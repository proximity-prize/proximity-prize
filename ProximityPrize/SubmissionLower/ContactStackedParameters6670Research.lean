import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Exact interpolation profiles for the stacked 67.18 candidate
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

open ContactInterpolation ContactRankKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182198
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨41, 20000, 12⟩
def profileB : Profile := ⟨60, 1300, 18⟩
def profileC : Profile := ⟨41, 800000, 12⟩

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
    errors = 79946 ∧ gap = 51127 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 45378365670326 := by
  change coefficientCount (41 * 182198) 131071 20000 12 = 45378365670326
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (41 * 182198) 131071 20000 12 58 (by norm_num) (by norm_num)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 172811639 := by
  change localRankBound 41 20000 12 = 172811639
  decide

theorem profileA_values :
    profileA.weightedCap = 7470118 ∧ profileA.yCap = 56 ∧
      profileA.localRank = 172811639 ∧
      profileA.coefficients = 45378365670326 ∧
      profileA.nullity = 76831376310 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    show profileA.localRank = 172811639 from profileA_localRank_exact]
  norm_num [n]

theorem profileB_values :
    profileB.weightedCap = 10931880 ∧ profileB.yCap = 83 ∧
      profileB.localRank = 34192039 ∧
      profileB.coefficients = 8963959385330 ∧
      profileB.nullity = 721513714 := by
  have hcoeff : profileB.coefficients = 8963959385330 := by
    change coefficientCount (60 * 182198) 131071 1300 18 = 8963959385330
    decide
  have hrank : profileB.localRank = 34192039 := by
    change localRankBound 60 1300 18 = 34192039
    decide
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    hrank, hcoeff, ?_⟩
  rw [Profile.nullity, Profile.totalRank, hcoeff,
    show profileB.localRank = 34192039 from hrank]
  norm_num [n]

theorem profileC_values :
    profileC.weightedCap = 7470118 ∧ profileC.yCap = 56 ∧
      profileC.localRank = 6915911639 ∧
      profileC.coefficients = 1816537803510326 ∧
      profileC.nullity = 3573062816310 := by
  have hcoeff : profileC.coefficients = 1816537803510326 := by
    change coefficientCount (41 * 182198) 131071 800000 12 = 1816537803510326
    rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
      (41 * 182198) 131071 800000 12 58 (by norm_num) (by norm_num)]
    decide
  have hrank : profileC.localRank = 6915911639 := by
    change localRankBound 41 800000 12 = 6915911639
    decide
  refine ⟨by norm_num [Profile.weightedCap, profileC, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileC, agreements, w],
    hrank, hcoeff, ?_⟩
  rw [Profile.nullity, Profile.totalRank, hcoeff,
    show profileC.localRank = 6915911639 from hrank]
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
  norm_num [Profile.characteristicCap, Profile.weightedCap, profileA,
    profileB, profileC, agreements, prime]

theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
        min profileA.seedCap profileB.seedCap,
        min profileA.slopeCap profileB.slopeCap) = (41, 1300, 12) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (41, 1300, 12) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
