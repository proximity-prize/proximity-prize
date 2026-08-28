import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Exact interpolation profiles for the stacked 66.96 candidate

This module certifies the three ordinary differential-contact kernels used by
the bounded active-YZ recursive-GCD construction at `a = 182414`.  It reuses
the weighted-cutoff reduction proved for the 66.56 parameter certificate; only
the target-specific natural-number arithmetic is new here.

No GCD decomposition, residual ledger, or decoding claim is made in this
arithmetic module.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6696Research

open ContactInterpolation ContactRankKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182414
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨31, 21207, 9⟩
def profileB : Profile := ⟨60, 925, 18⟩
def profileC : Profile := ⟨34, 801717, 8⟩

namespace Profile

def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def characteristicCap (P : Profile) : ℕ :=
  (2 * P.slopeCap - 1) * P.weightedCap

def coefficients (P : Profile) : ℕ :=
  coefficientCount P.weightedCap w P.seedCap P.slopeCap

def localRank (P : Profile) : ℕ :=
  localRankBound P.multiplicity P.seedCap P.slopeCap

def totalRank (P : Profile) : ℕ := n * P.localRank
def nullity (P : Profile) : ℕ := P.coefficients - P.totalRank

end Profile

theorem base_values :
    errors = 79730 ∧ gap = 51343 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 21395775287865 := by
  change coefficientCount (31 * 182414) 131071 21207 9 = 21395775287865
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (31 * 182414) 131071 21207 9 44 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileA_localRank_exact : profileA.localRank = 81618405 := by
  change localRankBound 31 21207 9 = 81618405
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileA_values :
    profileA.weightedCap = 5654834 ∧ profileA.yCap = 43 ∧
      profileA.localRank = 81618405 ∧
      profileA.coefficients = 21395775287865 ∧
      profileA.nullity = 127545 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 6346526578730 := by
  change coefficientCount (60 * 182414) 131071 925 18 = 6346526578730
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (60 * 182414) 131071 925 18 84 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileB_localRank_exact : profileB.localRank = 24209914 := by
  change localRankBound 60 925 18 = 24209914
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileB_values :
    profileB.weightedCap = 10944840 ∧ profileB.yCap = 83 ∧
      profileB.localRank = 24209914 ∧
      profileB.coefficients = 6346526578730 ∧
      profileB.nullity = 42883114 := by
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    profileB_localRank_exact, profileB_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 911056821290568 := by
  change coefficientCount (34 * 182414) 131071 801717 8 = 911056821290568
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (34 * 182414) 131071 801717 8 48 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileC_localRank_exact : profileC.localRank = 3475405965 := by
  change localRankBound 34 801717 8 = 3475405965
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileC_values :
    profileC.weightedCap = 6202076 ∧ profileC.yCap = 47 ∧
      profileC.localRank = 3475405965 ∧
      profileC.coefficients = 911056821290568 ∧
      profileC.nullity = 1608 := by
  refine ⟨by norm_num [Profile.weightedCap, profileC, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileC, agreements, w],
    profileC_localRank_exact, profileC_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileC_coefficients_exact,
    profileC_localRank_exact]
  norm_num [n]

/-- Each of the three constraint maps has a nonzero kernel. -/
theorem interpolation_gates :
      profileA.totalRank < profileA.coefficients ∧
      profileB.totalRank < profileB.coefficients ∧
      profileC.totalRank < profileC.coefficients := by
  simp only [Profile.totalRank]
  rw [profileA_coefficients_exact, profileA_localRank_exact,
    profileB_coefficients_exact, profileB_localRank_exact,
    profileC_coefficients_exact, profileC_localRank_exact]
  norm_num [n]

/-- The ordinary derivative and coefficient arithmetic stays below the
challenge-field characteristic. -/
theorem characteristic_gates :
    profileA.characteristicCap < prime ∧
      (2 * profileA.slopeCap - 1) * profileA.seedCap < prime ∧
      profileA.slopeCap < prime ∧
    profileB.characteristicCap < prime ∧
      (2 * profileB.slopeCap - 1) * profileB.seedCap < prime ∧
      profileB.slopeCap < prime ∧
    profileC.characteristicCap < prime ∧
      (2 * profileC.slopeCap - 1) * profileC.seedCap < prime ∧
      profileC.slopeCap < prime := by
  norm_num [Profile.characteristicCap, Profile.weightedCap, profileA, profileB,
    profileC, agreements, prime]

/-- Coordinatewise caps inherited by the first GCD and the final common
divisor, respectively. -/
theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
        min profileA.seedCap profileB.seedCap,
        min profileA.slopeCap profileB.slopeCap) = (31, 925, 9) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (31, 925, 8) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6696Research
