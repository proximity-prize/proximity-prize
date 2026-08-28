import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Exact interpolation profiles for the stacked 66.70 candidate

This module certifies the three ordinary differential-contact kernels used by
the bounded active-YZ recursive-GCD construction at `a = 182668`.  It reuses
the weighted-cutoff reduction proved for the 66.56 parameter certificate; only
the target-specific natural-number arithmetic is new here.

No GCD decomposition, residual ledger, or decoding claim is made in this
arithmetic module.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

open ContactInterpolation ContactRankKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182668
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨27, 11937, 7⟩
def profileB : Profile := ⟨34, 1059, 9⟩
def profileC : Profile := ⟨54, 690, 16⟩

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
    errors = 79476 ∧ gap = 51597 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 7531085838988 := by
  change coefficientCount (27 * 182668) 131071 11937 7 = 7531085838988
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (27 * 182668) 131071 11937 7 38 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileA_localRank_exact : profileA.localRank = 28728812 := by
  change localRankBound 27 11937 7 = 28728812
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileA_values :
    profileA.weightedCap = 4932036 ∧ profileA.yCap = 37 ∧
      profileA.localRank = 28728812 ∧
      profileA.coefficients = 7531085838988 ∧
      profileA.nullity = 146060 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 1295785940615 := by
  change coefficientCount (34 * 182668) 131071 1059 9 = 1295785940615
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (34 * 182668) 131071 1059 9 48 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileB_localRank_exact : profileB.localRank = 4943015 := by
  change localRankBound 34 1059 9 = 4943015
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileB_values :
    profileB.weightedCap = 6210712 ∧ profileB.yCap = 47 ∧
      profileB.localRank = 4943015 ∧
      profileB.coefficients = 1295785940615 ∧
      profileB.nullity = 4216455 := by
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    profileB_localRank_exact, profileB_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 3438081196732 := by
  change coefficientCount (54 * 182668) 131071 690 16 = 3438081196732
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (54 * 182668) 131071 690 16 76 (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ]

theorem profileC_localRank_exact : profileC.localRank = 13115228 := by
  change localRankBound 54 690 16 = 13115228
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

theorem profileC_values :
    profileC.weightedCap = 9864072 ∧ profileC.yCap = 75 ∧
      profileC.localRank = 13115228 ∧
      profileC.coefficients = 3438081196732 ∧
      profileC.nullity = 2867900 := by
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
        min profileA.slopeCap profileB.slopeCap) = (27, 1059, 7) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (27, 690, 7) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedParameters6670Research.profileA_values
#print axioms ProximityPrize.SubmissionLower.ContactStackedParameters6670Research.profileB_values
#print axioms ProximityPrize.SubmissionLower.ContactStackedParameters6670Research.profileC_values
#print axioms ProximityPrize.SubmissionLower.ContactStackedParameters6670Research.interpolation_gates
#print axioms ProximityPrize.SubmissionLower.ContactStackedParameters6670Research.characteristic_gates
