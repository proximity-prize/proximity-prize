import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingParameters6719Research

open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagBezout6543Research
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def errors : ℕ := 79955
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def listBudget : ℕ := 700000000
def capacity : ℕ := prime ^ 6 / 2 ^ 128
def mcaBudget : ℕ := capacity - listBudget

structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨37, 22092, 10⟩
def profileB : Profile := ⟨71, 1006, 22⟩
def profileC : Profile := profileB
def profileMeet : Profile := ⟨37, 1006, 10⟩

namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def coefficients (P : Profile) : ℕ :=
  coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P : Profile) : ℕ :=
  localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P : Profile) : ℕ := n * P.localRank
def nullity (P : Profile) : ℕ := P.coefficients - P.totalRank
def characteristicCap (P : Profile) : ℕ :=
  (2 * P.slopeCap - 1) * P.weightedCap
end Profile

theorem base_values : agreements = 182189 ∧ gap = 51118 ∧
    capacity = 274980728111395087 ∧ mcaBudget = 274980727411395087 ∧
    mcaBudget + listBudget = capacity := by decide

theorem profileA_coefficients_exact : profileA.coefficients = 35204907336313 := by
  change coefficientCount (37 * 182189) 131071 22092 10 = 35204907336313
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (37 * 182189) 131071 22092 10 52 (by decide) (by decide)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 134296063 := by
  change localRankBound 37 22092 10 = 134296063
  decide

theorem profileB_coefficients_exact : profileB.coefficients = 11409396384694 := by
  change coefficientCount (71 * 182189) 131071 1006 22 = 11409396384694
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (71 * 182189) 131071 1006 22 99 (by decide) (by decide)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 43523176 := by
  change localRankBound 71 1006 22 = 43523176
  decide

theorem profile_values :
    profileA.weightedCap = 6740993 ∧ profileB.weightedCap = 12935419 ∧
    profileA.yCap = 51 ∧ profileB.yCap = 98 ∧
    profileA.nullity = 197241 ∧ profileB.nullity = 56935350 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rw [Profile.nullity, Profile.totalRank,
      profileA_coefficients_exact, profileA_localRank_exact]
    decide
  · rw [Profile.nullity, Profile.totalRank,
      profileB_coefficients_exact, profileB_localRank_exact]
    decide

theorem interpolation_gates :
    profileA.totalRank < profileA.coefficients ∧
    profileB.totalRank < profileB.coefficients ∧
    profileC.totalRank < profileC.coefficients := by
  simp only [profileC, Profile.totalRank]
  rw [profileA_coefficients_exact, profileA_localRank_exact,
    profileB_coefficients_exact, profileB_localRank_exact]
  decide

theorem characteristic_gates :
    profileA.characteristicCap < prime ∧
    (2 * profileA.slopeCap - 1) * profileA.seedCap < prime ∧
    profileA.slopeCap < prime ∧
    profileB.characteristicCap < prime ∧
    (2 * profileB.slopeCap - 1) * profileB.seedCap < prime ∧
    profileB.slopeCap < prime := by decide

theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
      min profileA.seedCap profileB.seedCap, min profileA.slopeCap profileB.slopeCap) =
        (profileMeet.multiplicity, profileMeet.seedCap, profileMeet.slopeCap) ∧
    (min profileMeet.multiplicity profileC.multiplicity,
      min profileMeet.seedCap profileC.seedCap, min profileMeet.slopeCap profileC.slopeCap) =
        (37, 1006, 10) := by decide

theorem middle_support_gates :
    profileA.weightedCap + profileA.slopeCap ≤ w * (profileA.yCap + 1) ∧
    profileB.weightedCap + profileB.slopeCap ≤ w * (profileB.yCap + 1) ∧
    profileA.multiplicity - 1 + profileA.slopeCap ≤ profileA.yCap ∧
    profileB.multiplicity - 1 + profileB.slopeCap ≤ profileB.yCap := by decide

def fixedFlag : FlagDegree := ⟨955, 41, 10⟩
def direction : FlagDegree := ⟨1910, 81, 19⟩
def q : ℕ := flagMixed fixedFlag direction direction
def ell : ℕ := flagMixed fixedFlag direction unitYZFlag
def u : ℕ := flagMixed fixedFlag unitYZFlag unitYZFlag
def zlin : ℕ := flagMixed fixedFlag direction unitZFlag
def zunit : ℕ := flagMixed fixedFlag unitYZFlag unitZFlag
def baseSaving : ℕ := 2679510
def polePenalty : ℕ := 2012
def qeff : ℕ := q - baseSaving + polePenalty
def E : ℕ := (n * gap * w + agreements - 1) / agreements
def U : ℕ := n - w

def primary : ℕ := qeff * E ^ 2 + 2 * (q + ell) * E * U +
  (q + 2 * ell + u) * U ^ 2
def zTail : ℕ := (errors + 1) * gap * (zlin * E + (zlin + zunit) * U)
def yzTail : ℕ := (errors + 1) * gap * (ell * E + (ell + u) * U)
def fixedRegularCost : ℕ := (primary + zTail + yzTail) / gap ^ 2 + 1

theorem flag_values : q = 10321024 ∧ qeff = 7643526 ∧ U = 131073 := by decide

def singularY (P : Profile) : ℕ := (P.characteristicCap - 1) / w
def singularZ (P : Profile) : ℕ := (2 * P.slopeCap - 1) * P.seedCap
def singularNumerator (P : Profile) : ℕ :=
  let y := singularY P
  let z := singularZ P
  U * ((1 + 2*w*y)*z + w*(2*y*z) + (2*w*z + 1)*y) +
    (errors + 1)*gap*y + 2*z*z*gap
def singularCeiling (P : Profile) : ℕ := singularNumerator P / gap + 1

def residualMixed (P Q : Profile) : Fin 3 → ℕ :=
  ![P.slopeCap*Q.seedCap + P.seedCap*Q.slopeCap,
    P.yCap*Q.seedCap + P.seedCap*Q.yCap,
    P.yCap*Q.slopeCap + P.slopeCap*Q.yCap]
def residualNumerator (P Q : Profile) : ℕ :=
  let c := residualMixed P Q
  U * (c 0*(1 + 2*w*max P.yCap Q.yCap) +
    c 1*(w*(2*max P.slopeCap Q.slopeCap - 1)) +
    c 2*(2*w*max P.seedCap Q.seedCap + 1)) + (errors + 1)*gap*c 2

def fixedSingularCost : ℕ := singularCeiling profileMeet
def firstResidualRegularCost : ℕ := residualNumerator profileA profileB / gap
def firstResidualSingularCeiling : ℕ := singularCeiling profileB
def secondResidualRegularCost : ℕ := residualNumerator profileMeet profileC / gap
def secondResidualSingularCeiling : ℕ := singularCeiling profileMeet
def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost + secondResidualSingularCeiling
def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem padded_incidence_values :
    E = 9640470642 ∧ ell = 39024 ∧ u = 10 ∧ zlin = 1779 ∧ zunit = 10 ∧
    primary = 710405354851629721993341378 ∧
    zTail = 70097904487874394315720 ∧
    yzTail = 1537661846658663289707120 ∧
    primary + zTail + yzTail = 712013114602776259677364218 := by decide

theorem residual_numerators_exact :
    residualNumerator profileA profileB = 4903299280254455268 ∧
    residualNumerator profileMeet profileC = 291796613575184412 := by decide

theorem six_cells_exact :
    fixedRegularCost = 272483548080414043 ∧
    fixedSingularCost = 37657607377307 ∧
    firstResidualRegularCost = 95921187844877 ∧
    firstResidualSingularCeiling = 370119108170621 ∧
    secondResidualRegularCost = 5708294799780 ∧
    secondResidualSingularCeiling = 37657607377307 := by decide

theorem total_and_slack_exact :
    totalCost = 273030611885983935 ∧
    mcaBudget - totalCost = 1950115525411152 ∧ totalCost < mcaBudget := by decide

theorem residual_characteristic_gates :
    residualMixed profileA profileB = ![496084, 2216322, 2102] ∧
    residualMixed profileMeet profileC = ![32192, 149894, 2102] ∧
    profileB.characteristicCap = 556223017 ∧ singularZ profileB = 43258 ∧
    singularY profileB = 4243 ∧ 2*singularY profileB*singularZ profileB < prime ∧
    profileMeet.characteristicCap = 128078867 ∧ singularZ profileMeet = 19114 ∧
    singularY profileMeet = 977 ∧ 2*singularY profileMeet*singularZ profileMeet < prime ∧
    (1 + w*(direction.yz + direction.all))*fixedFlag.all +
      (fixedFlag.yz + fixedFlag.all)*(w*direction.all) < prime := by decide

/-- . -/
theorem total_lt_mcaBudget (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total = firstResidual + secondResidual + fixed)
    (hfirst : firstResidual < firstResidualCeiling)
    (hsecond : secondResidual < secondResidualCeiling) (hfixed : fixed ≤ fixedCost) :
    total < mcaBudget := by
  have hsum : firstResidual + secondResidual + fixed < totalCost := by
    unfold totalCost
    omega
  rw [hpartition]
  exact hsum.trans total_and_slack_exact.2.2

end ProximityPrize.SubmissionLower.ContactMovingParameters6719Research
