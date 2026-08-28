import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Exact interpolation profiles for the stacked 66.98 candidate
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

open ContactInterpolation ContactRankKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182397
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨60, 945, 18⟩
def profileB : Profile := ⟨35, 5000, 9⟩
def profileC : Profile := ⟨35, 500000, 9⟩

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
    errors = 79747 ∧ gap = 51326 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 6485848529250 := by
  change coefficientCount (60 * 182397) 131071 945 18 = 6485848529250
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (60 * 182397) 131071 945 18 84 (by norm_num) (by norm_num)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 24741517 := by
  change localRankBound 60 945 18 = 24741517
  decide

theorem profileA_values :
    profileA.weightedCap = 10943820 ∧ profileA.yCap = 83 ∧
      profileA.localRank = 24741517 ∧
      profileA.coefficients = 6485848529250 ∧
      profileA.nullity = 2928394 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    show profileA.localRank = 24741517 from profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 657404481079520 := by
  change coefficientCount (35 * 182397) 131071 5000 9 = 657404481079520
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (35 * 182397) 131071 5000 9 49 (by norm_num) (by norm_num)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 25078500 := by
  change localRankBound 35 5000 9 = 25078500
  decide

theorem profileB_values :
    profileB.weightedCap = 6383895 ∧ profileB.yCap = 48 ∧
      profileB.localRank = 25078500 ∧
      profileB.coefficients = 657404481079520 ∧
      profileB.nullity = 1202868880 := by
  have hcoeff : profileB.coefficients = 657404481079520 := by
    change coefficientCount (35 * 182397) 131071 5000 9 = 657404481079520
    rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
      (35 * 182397) 131071 5000 9 49 (by norm_num) (by norm_num)]
    decide
  have hrank : profileB.localRank = 25078500 := by
    change localRankBound 35 5000 9 = 25078500
    decide
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    hrank, hcoeff, ?_⟩
  rw [Profile.nullity, Profile.totalRank, hcoeff,
    show profileB.localRank = 25078500 from hrank]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 657404481079520 := by
  change coefficientCount (35 * 182397) 131071 500000 9 = 657404481079520
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (35 * 182397) 131071 500000 9 49 (by norm_num) (by norm_num)]
  decide

theorem profileC_localRank_exact : profileC.localRank = 2504956185 := by
  change localRankBound 35 500000 9 = 2504956185
  decide

theorem profileC_values :
    profileC.weightedCap = 6383895 ∧ profileC.yCap = 48 ∧
      profileC.localRank = 2504956185 ∧
      profileC.coefficients = 657404481079520 ∧
      profileC.nullity = 743821738880 := by
  have hcoeff : profileC.coefficients = 657404481079520 := by
    change coefficientCount (35 * 182397) 131071 500000 9 = 657404481079520
    rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
      (35 * 182397) 131071 500000 9 49 (by norm_num) (by norm_num)]
    decide
  have hrank : profileC.localRank = 2504956185 := by
    change localRankBound 35 500000 9 = 2504956185
    decide
  refine ⟨by norm_num [Profile.weightedCap, profileC, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileC, agreements, w],
    hrank, hcoeff, ?_⟩
  rw [Profile.nullity, Profile.totalRank, hcoeff,
    show profileC.localRank = 2504956185 from hrank]
  norm_num [n]

theorem profileA_interpolation_gate :
    profileA.totalRank < profileA.coefficients := by
  have h := profileA_values.2.2.2.2
  dsimp [Profile.nullity] at h
  omega

theorem profileB_interpolation_gate :
    profileB.totalRank < profileB.coefficients := by
  have h := profileB_values.2.2.2.2
  dsimp [Profile.nullity] at h
  omega

theorem profileC_interpolation_gate :
    profileC.totalRank < profileC.coefficients := by
  have h := profileC_values.2.2.2.2
  dsimp [Profile.nullity] at h
  omega

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

theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
        min profileA.seedCap profileB.seedCap,
        min profileA.slopeCap profileB.slopeCap) = (35, 945, 9) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (35, 945, 9) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
