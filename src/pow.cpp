// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <pow.h>

#include <arith_uint256.h>
#include <algorithm>
#include <chain.h>
#include <primitives/block.h>
#include <uint256.h>
#include <util/check.h>

// BTGS: LWMA difficulty adjustment.
static unsigned int CalculateNextWorkRequiredLWMA(
    const CBlockIndex* pindexLast,
    const Consensus::Params& params)
{
    constexpr int N = 60;
    const int64_t T = params.nPowTargetSpacing;
    const arith_uint256 powLimit = UintToArith256(params.powLimit);

    if (T <= 0 || pindexLast->nHeight < N) {
        return powLimit.GetCompact();
    }

    int64_t weightedSolvetime = 0;
    arith_uint256 sumTargets;
    const CBlockIndex* pindex = pindexLast;

    for (int i = N; i >= 1; --i) {
        if (pindex == nullptr || pindex->pprev == nullptr) {
            return powLimit.GetCompact();
        }

        int64_t solvetime =
            pindex->GetBlockTime() - pindex->pprev->GetBlockTime();
        solvetime = std::clamp(solvetime, -6 * T, 6 * T);
        weightedSolvetime += solvetime * i;

        arith_uint256 blockTarget;
        blockTarget.SetCompact(pindex->nBits);
        sumTargets += blockTarget;

        pindex = pindex->pprev;
    }

    const int64_t k = T * N * (N + 1) / 2;

    // Prevent zero or negative solve times from causing extreme difficulty changes.
    weightedSolvetime = std::max(weightedSolvetime, k / 10);

    arith_uint256 target = sumTargets;
    target /= N;
    target *= weightedSolvetime;
    target /= k;

    if (target > powLimit) {
        target = powLimit;
    }
    if (target == 0) {
        target = 1;
    }

    return target.GetCompact();
}

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    unsigned int nProofOfWorkLimit = UintToArith256(params.powLimit).GetCompact();
    unsigned int nMinDifficultyFloor = 0x1a06a090;

    const int nextHeight = pindexLast->nHeight + 1;
    if (nextHeight >= params.nPowLwmaActivationHeight) {
        return CalculateNextWorkRequiredLWMA(pindexLast, params);
    }

    if ((pindexLast->nHeight+1) % params.DifficultyAdjustmentInterval() != 0)
    {
        if (params.fPowAllowMinDifficultyBlocks)
        {
            if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
                return nProofOfWorkLimit;
            else
            {
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % params.DifficultyAdjustmentInterval() != 0 && pindex->nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->nBits;
            }
        }

        if (pindexLast->nHeight + 1 >= 2016) {
            if (pindexLast->nBits > nMinDifficultyFloor) {
                return nMinDifficultyFloor;
            }
        }
        return pindexLast->nBits;
    }

    int nHeightFirst = pindexLast->nHeight - (params.DifficultyAdjustmentInterval()-1);
    assert(nHeightFirst >= 0);
    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
    assert(pindexFirst);

    unsigned int nNewBits = CalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime(), params);

    if (pindexLast->nHeight + 1 >= 2016) {
        if (nNewBits > nMinDifficultyFloor) {
            return nMinDifficultyFloor;
        }
    }

    return nNewBits;
}

unsigned int CalculateNextWorkRequired(const CBlockIndex* pindexLast, int64_t nFirstBlockTime, const Consensus::Params& params)
{
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;

    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    if (nActualTimespan < params.nPowTargetTimespan/4)
        nActualTimespan = params.nPowTargetTimespan/4;
    if (nActualTimespan > params.nPowTargetTimespan*4)
        nActualTimespan = params.nPowTargetTimespan*4;

    const arith_uint256 bnPowLimit = UintToArith256(params.powLimit);
    arith_uint256 bnNew;

    if (params.enforce_BIP94) {
        int nHeightFirst = pindexLast->nHeight - (params.DifficultyAdjustmentInterval()-1);
        const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
        bnNew.SetCompact(pindexFirst->nBits);
    } else {
        bnNew.SetCompact(pindexLast->nBits);
    }

    bnNew *= nActualTimespan;
    bnNew /= params.nPowTargetTimespan;

    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    return bnNew.GetCompact();
}

bool PermittedDifficultyTransition(const Consensus::Params& params, int64_t height, uint32_t old_nbits, uint32_t new_nbits)
{
    if (params.fPowAllowMinDifficultyBlocks) return true;

    // LWMA permits per-block changes, but bound target changes during header sync.
    if (height >= params.nPowLwmaActivationHeight) {
        arith_uint256 old_target;
        arith_uint256 new_target;
        old_target.SetCompact(old_nbits);
        new_target.SetCompact(new_nbits);

        const arith_uint256 pow_limit = UintToArith256(params.powLimit);
        if (old_target == 0 || new_target == 0 ||
            old_target > pow_limit || new_target > pow_limit) {
            return false;
        }

        arith_uint256 maximum_target = old_target;
        maximum_target *= 10;
        if (maximum_target > pow_limit) maximum_target = pow_limit;
        if (new_target > maximum_target) return false;

        arith_uint256 minimum_target = old_target / 10;
        if (new_target < minimum_target) return false;

        return true;
    }

    if (height % params.DifficultyAdjustmentInterval() == 0) {
        int64_t smallest_timespan = params.nPowTargetTimespan/4;
        int64_t largest_timespan = params.nPowTargetTimespan*4;

        const arith_uint256 pow_limit = UintToArith256(params.powLimit);
        arith_uint256 observed_new_target;
        observed_new_target.SetCompact(new_nbits);

        arith_uint256 largest_difficulty_target;
        largest_difficulty_target.SetCompact(old_nbits);
        largest_difficulty_target *= largest_timespan;
        largest_difficulty_target /= params.nPowTargetTimespan;

        if (largest_difficulty_target > pow_limit) {
            largest_difficulty_target = pow_limit;
        }

        arith_uint256 maximum_new_target;
        maximum_new_target.SetCompact(largest_difficulty_target.GetCompact());
        if (height >= 2016 && new_nbits == 0x1a06a090) return true;

        if (maximum_new_target < observed_new_target) return false;

        arith_uint256 smallest_difficulty_target;
        smallest_difficulty_target.SetCompact(old_nbits);
        smallest_difficulty_target *= smallest_timespan;
        smallest_difficulty_target /= params.nPowTargetTimespan;

        if (smallest_difficulty_target > pow_limit) {
            smallest_difficulty_target = pow_limit;
        }

        arith_uint256 minimum_new_target;
        minimum_new_target.SetCompact(smallest_difficulty_target.GetCompact());
        if (minimum_new_target > observed_new_target) return false;
    } else if (old_nbits != new_nbits) {
        return false;
    }
    return true;
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params& params)
{
    if (EnableFuzzDeterminism()) return (hash.data()[31] & 0x80) == 0;
    return CheckProofOfWorkImpl(hash, nBits, params);
}

std::optional<arith_uint256> DeriveTarget(unsigned int nBits, const uint256 pow_limit)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(pow_limit))
        return {};

    return bnTarget;
}

bool CheckProofOfWorkImpl(uint256 hash, unsigned int nBits, const Consensus::Params& params)
{
    auto bnTarget{DeriveTarget(nBits, params.powLimit)};
    if (!bnTarget) return false;

    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}
