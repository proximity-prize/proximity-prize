import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

/-!
# Exact interpolation profiles for the stacked 67.11 candidate

This module certifies the three joint-support differential-contact kernels
used by the bounded active-YZ recursive-GCD construction at `a = 182268`.
The counts use the existing tetrahedral `Y+R+Z` support APIs. A weighted
cutoff keeps the exact finite arithmetic certificates small.

No GCD decomposition, residual ledger, or decoding claim is made in this
arithmetic module.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182078
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The profiles are `(multiplicity, total Y+R+Z cap, slope cap)`.
`seedCap` retains its legacy name and bounds the full joint degree. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨50, 25000, 15⟩
def profileB : Profile := ⟨60, 3100, 18⟩
def profileC : Profile := ⟨50, 800000, 15⟩

namespace Profile

def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def totalCap (P : Profile) : ℕ := P.seedCap
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

theorem coefficientCount_eq_sum_range_of_weighted_cutoff
    (D w L s t : ℕ) (hD : D ≤ w * t) (ht : t ≤ L + 1) :
    coefficientCount D w L s =
      ∑ i ∈ Finset.range t,
        ∑ j ∈ Finset.range (s + 1),
          (L + 1 - i - j) * (D - w * i - (w - 1) * j) := by
  have hsplit : L + 1 = t + (L + 1 - t) := by omega
  unfold coefficientCount
  rw [hsplit, Finset.sum_range_add]
  have htail :
      (∑ x ∈ Finset.range (L + 1 - t),
        ∑ j ∈ Finset.range (s + 1),
          (t + (L + 1 - t) - (t + x) - j) *
            (D - w * (t + x) - (w - 1) * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hti : t ≤ t + i := by omega
    have hzero : D - w * (t + i) = 0 :=
      Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
    simp [hzero]
  rw [htail, add_zero]

theorem base_values :
    errors = 80066 ∧ gap = 51007 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 102709631462780 := by
  change coefficientCount (50 * 182078) 131071 25000 15 = 102709631462780
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (50 * 182078) 131071 25000 15 70 (by norm_num) (by norm_num)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 390672240 := by
  change localRankBound 50 25000 15 = 390672240
  decide

theorem profileA_values :
    profileA.weightedCap = 9103900 ∧ profileA.yCap = 69 ∧
      profileA.localRank = 390672240 ∧
      profileA.coefficients = 102709631462780 ∧
      profileA.nullity = 297247780220 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 21517463188355 := by
  change coefficientCount (60 * 182078) 131071 3100 18 = 21517463188355
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (60 * 182078) 131071 3100 18 84 (by norm_num) (by norm_num)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 81842728 := by
  change localRankBound 60 3100 18 = 81842728
  decide

theorem profileB_values :
    profileB.weightedCap = 10924680 ∧ profileB.yCap = 83 ∧
      profileB.localRank = 81842728 ∧
      profileB.coefficients = 21517463188355 ∧
      profileB.nullity = 62883099523 := by
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    profileB_localRank_exact, profileB_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 3290070328462780 := by
  change coefficientCount (50 * 182078) 131071 800000 15 = 3290070328462780
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (50 * 182078) 131071 800000 15 70 (by norm_num) (by norm_num)]
  decide

theorem profileC_localRank_exact : profileC.localRank = 12511672240 := by
  change localRankBound 50 800000 15 = 12511672240
  decide

theorem profileC_values :
    profileC.weightedCap = 9103900 ∧ profileC.yCap = 69 ∧
      profileC.localRank = 12511672240 ∧
      profileC.coefficients = 3290070328462780 ∧
      profileC.nullity = 10210520780220 := by
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
  rw [Profile.totalRank, Profile.totalRank, Profile.totalRank,
    profileA_coefficients_exact, profileA_localRank_exact,
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
  norm_num [Profile.characteristicCap, Profile.weightedCap, profileA, profileB, profileC,
    agreements, prime]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
