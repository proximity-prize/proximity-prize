import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A0
import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.AJ
import ProximityPrize.SubmissionLower.AM
import ProximityPrize.SubmissionLower.B3
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BA
import ProximityPrize.SubmissionLower.BC
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.BO
import ProximityPrize.SubmissionLower.C2
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.C4
import ProximityPrize.SubmissionLower.C7
import ProximityPrize.SubmissionLower.D
import ProximityPrize.SubmissionLower.DH
import ProximityPrize.SubmissionLower.DV
import ProximityPrize.SubmissionLower.E8
import ProximityPrize.SubmissionLower.E9
import ProximityPrize.SubmissionLower.EA
import ProximityPrize.SubmissionLower.EC
import ProximityPrize.SubmissionLower.EQ
import ProximityPrize.SubmissionLower.F0
import ProximityPrize.SubmissionLower.FF
import ProximityPrize.SubmissionLower.FG
import ProximityPrize.SubmissionLower.FQ
import ProximityPrize.SubmissionLower.GC
import ProximityPrize.SubmissionLower.GE
import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.GI
import ProximityPrize.SubmissionLower.GL
import ProximityPrize.SubmissionLower.GM
import ProximityPrize.SubmissionLower.GY
import ProximityPrize.SubmissionLower.I6
import ProximityPrize.SubmissionLower.J4
import ProximityPrize.SubmissionLower.K3
import ProximityPrize.SubmissionLower.M1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.O
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.O8
import ProximityPrize.SubmissionLower.P1
import ProximityPrize.SubmissionLower.S
import ProximityPrize.SubmissionLower.U
import ProximityPrize.SubmissionLower.Z1
import ProximityPrize.SubmissionLower.Z8

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactRegularComponentCover
open ContactGenericSurface ContactIdentityResidualIterationResearch
open ContactProperCutSeedCount ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch
open ContactScalarCoordinateSeparator6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactTerminalAdaptiveProjection6600Research
open ContactRegularComponentYZPositivity6630Research
open ContactResidualStageDerivative6600Research
open ContactTerminalAdaptiveProjection6656Research
open ContactFirstTailCertificate6731Research
open ContactFirstTailProjection6731Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
theorem exists_firstTail_activeNestedData_of_caps
    (S:ResidualStage phi Gamma x pchar e flag w
      (ContactMovingAgreementCertificate6719Research.support a b s))
    (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
    (hflagChar:flag.yz+flag.all < pchar∧flag.all < pchar∧
      flag.zOnly+flag.yz+flag.all < pchar)
    (hmixed:(1+(w+1)*(2*(b+s+3)-2))*flag.all+
      (flag.yz+flag.all)*((2*(s+2)-1)*(w+1)) < pchar):
    ∃ (base:∀ C:RegularComponent Omega S.G
        (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
        SeparableLiteralCoordinate C.1),
      ∃ (hactive:∀ C:RegularComponent Omega S.G
          (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
          D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
            D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0),
        ∃ (hZ:∀ C:RegularComponent Omega S.G
            (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
            LiteralProjectionGate C 2),
          Nonempty (AdaptiveNestedProjectionDataActive base hactive
            (residualStage_pderiv_one_ne_zero_of_support S)):=by
  classical
  let T:=globalTailCut phi S.F (w+1)
  let H:=regularitySurface phi S.F
  let supp:=ContactMovingAgreementCertificate6719Research.support a b s
  have hsy:supp.s < supp.ys:=by
    change s+2 < b+s+3
    omega
  have hTflag:PolynomialInFlag (sharpResidualAgreementFlag supp (w+1)) T:=
    firstTail_in_sharp_flag S
  obtain ⟨hGY,hGS,hGZ⟩:=
    degree_bounds_of_polynomialInFlag S.flag_support
  obtain ⟨hTY,hTS,_⟩:=
    degree_bounds_of_polynomialInFlag hTflag
  have hTY':T.degreeOf 0 ≤ 1+(w+1)*(2*(b+s+3)-2):=by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys supp hsy (w+1)
  have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*(w+1):=by
    apply hTS.trans_eq
    simp only [sharpResidualAgreementFlag,sharpAgreementDirection,supp,
      ContactMovingAgreementCertificate6719Research.support]
  have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ:coordinateMixedDegree Omega S.G T 2 < pchar:=by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
  let choiceData:∀ C:RegularComponent Omega S.G T H,
      ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
    fun C↦regularComponent_exists_separableLiteralCoordinate6630
      phi S.F S.G T pchar S.G_dvd_surface S.irreducible_G hproper
      S.y_dependent hGdegree hmixedZ C
  let base:∀ C:RegularComponent Omega S.G T H,
      SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
  have hbaseIndex:∀ C:RegularComponent Omega S.G T H,
      (base C).index=0∨(base C).index=2:=by
    intro C
    exact (choiceData C).choose_spec
  have hactive:∀ C:RegularComponent Omega S.G T H,
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0:=by
    intro C
    have hb:=base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  have hZ:∀ C:RegularComponent Omega S.G T H,
      LiteralProjectionGate C 2:=by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      pchar S.G T S.irreducible_G
      (regularComponent_G_mem Omega S.G T H C)
      (regularComponent_T_mem Omega S.G T H C)
      hproper hGdegree hmixedZ
  exact ⟨base,hactive,hZ,
    exists_adaptiveNestedProjectionDataActive base hactive
      (residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
end
section

namespace ProximityPrize.SubmissionLower.ContactTwoTailParameters6735Research

open ProximityPrize.Benchmark
open ContactFlagBezout6543Research
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactMovingAgreementCertificate6719Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open scoped NNReal

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def score : ℕ := 6740
def errors : ℕ := 80161
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def radiusNumerator : ℕ := 128 * errors + 127
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

structure Profile where
  multiplicity : ℕ
  totalCap : ℕ
  slopeCap : ℕ
  middleCap : ℕ
  coefficients : ℕ
  rank : ℕ
  deriving DecidableEq

namespace Profile

def nullity (P : Profile) : ℕ := P.coefficients - n * P.rank
def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def totalRank (P : Profile) : ℕ := n * P.rank
def characteristicCap (P : Profile) : ℕ :=
  (2 * P.slopeCap - 1) * P.weightedCap

end Profile

def profileA : Profile :=
  ⟨43, 87761, 13, 59, 233463507880043, 890592605⟩
def profileB : Profile :=
  ⟨84, 1394, 26, 116, 26017826911362, 99249966⟩
def profileC : Profile :=
  ⟨45, 26176, 12, 62, 72651309055689, 277142749⟩
def finalMeet : Profile := ⟨43, 1394, 12, 59, 0, 0⟩

def supportProfile := support 1335 46 10
def fixedFlag : FlagDegree :=
  ⟨finalMeet.totalCap - finalMeet.middleCap,
    finalMeet.middleCap - finalMeet.slopeCap,
    finalMeet.slopeCap⟩
def direction : FlagDegree :=
  ⟨2 * fixedFlag.zOnly, 2 * fixedFlag.yz - 1, 2 * fixedFlag.all - 1⟩
def tailFlag (d : ℕ) : FlagDegree := unitYZFlag + (d + 1) • direction
def exactFirstTailFlag : FlagDegree := unitYZFlag + (w + 1) • direction
def rationalCoordinateFlag : FlagDegree := ⟨174983790, 6029406, 1310743⟩
def hybridCoordinateFlag : FlagDegree := ⟨174983790, 6094942, 1507351⟩
def movingFiberFlag : FlagDegree := ⟨1335, 47, 13⟩
def movingCutFlag : FlagDegree := ⟨174983790, 6160478, 1572887⟩

def hybridStageCost (flag : FlagDegree) : ℕ :=
  flagMixed flag exactFirstTailFlag hybridCoordinateFlag +
    (w + 1) * flagMixed flag movingFiberFlag movingCutFlag

def fixedRegularCost : ℕ := hybridStageCost fixedFlag
def fixedSingularCost : ℕ := 89129741434159
def firstResidualRegularCost : ℕ := 536839172882674
def firstResidualSingularCost : ℕ := 856170430068949
def secondResidualRegularCost : ℕ := 55442323120491
def secondResidualSingularCost : ℕ := 105276894357776
def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ :=
  firstResidualRegularCost + firstResidualSingularCost
def secondResidualCeiling : ℕ :=
  secondResidualRegularCost + secondResidualSingularCost
def totalCost : ℕ :=
  fixedRegularCost + fixedSingularCost +
    firstResidualRegularCost + firstResidualSingularCost +
    secondResidualRegularCost + secondResidualSingularCost

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 181983, 116, 26, 1394, 59, 13, 87761⟩
def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 181983, 59, 13, 1394, 62, 12, 26176⟩
def pivotB : TightParameters :=
  ⟨262144, 131071, 181983, 15286572, 1394, 26⟩
def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 181983, 7825269, 1394, 13⟩

def seedlessMultiplicity : ℕ := 44
def seedlessYTotalCap : ℕ := 61
def seedlessSlopeCap : ℕ := 12
def seedlessWeightedCap : ℕ := seedlessMultiplicity * agreements
def seedlessCapY : ℕ := 1 + 2 * w * seedlessYTotalCap
def seedlessCapR : ℕ := w * (2 * seedlessSlopeCap - 1)
def seedlessRegularListNumerator : ℕ :=
  (n - w) *
    (seedlessCapY * seedlessSlopeCap + seedlessCapR * seedlessYTotalCap)
def seedlessSingularListCap : ℕ :=
  (2 * seedlessSlopeCap - 1) * seedlessYTotalCap
def seedlessListNumerator : ℕ :=
  seedlessRegularListNumerator + seedlessSingularListCap * gap
def seedlessListCeiling : ℕ := seedlessListNumerator / gap + 1
def capacity : ℕ := prime ^ 6 / 2 ^ 128
def mcaBudget : ℕ := capacity - seedlessListCeiling
def slack : ℕ := mcaBudget - totalCost

abbrev scoreGate (e : ℕ) : Prop :=
  (radiusDenominator - (128 * e + 127)) ^ 12800 * 2 ^ score ≤
    radiusDenominator ^ 12800

theorem radius_row_exact :
    errors = 80161 ∧ agreements = 181983 ∧ gap = 50912 ∧
      radiusNumerator = 10260735 ∧ radiusDenominator = 33554432 := by
  decide

theorem radius_cell_exact : scoreGate errors ∧ ¬ scoreGate (errors - 1) := by
  decide

theorem profile_values :
    profileA.nullity = 34923 ∧ profileB.nullity = 43824258 ∧
      profileC.nullity = 261833 ∧
      finalMeet = ⟨43, 1394, 12, 59, 0, 0⟩ := by
  decide

theorem profileA_coefficients_exact :
    coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap =
      profileA.coefficients := by
  change coefficientCount (43 * 181983) 131071 87761 13 = 233463507880043
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (43 * 181983) 131071 87761 13 60 (by decide) (by decide)]
  decide

theorem profileB_coefficients_exact :
    coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap =
      profileB.coefficients := by
  change coefficientCount (84 * 181983) 131071 1394 26 = 26017826911362
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (84 * 181983) 131071 1394 26 117 (by decide) (by decide)]
  decide

theorem profileC_coefficients_exact :
    coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap =
      profileC.coefficients := by
  change coefficientCount (45 * 181983) 131071 26176 12 = 72651309055689
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (45 * 181983) 131071 26176 12 63 (by decide) (by decide)]
  decide

theorem profileA_rank_exact :
    localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap =
      profileA.rank := by
  decide

theorem profileB_rank_exact :
    localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap =
      profileB.rank := by
  decide

theorem profileC_rank_exact :
    localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap =
      profileC.rank := by
  decide

theorem interpolation_gates :
    profileA.totalRank < profileA.coefficients ∧
      profileB.totalRank < profileB.coefficients ∧
      profileC.totalRank < profileC.coefficients := by
  decide

theorem interpolation_gateA_exact :
    n * localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap := by
  rw [profileA_coefficients_exact, profileA_rank_exact]
  decide

theorem interpolation_gateB_exact :
    n * localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap <
      coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap := by
  rw [profileB_coefficients_exact, profileB_rank_exact]
  decide

theorem interpolation_gateC_exact :
    n * localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap := by
  rw [profileC_coefficients_exact, profileC_rank_exact]
  decide

theorem profile_gates :
    profileA.characteristicCap < prime ∧
      profileB.characteristicCap < prime ∧
      profileC.characteristicCap < prime ∧
      profileA.weightedCap + profileA.slopeCap ≤ w * (profileA.yCap + 1) ∧
      profileB.weightedCap + profileB.slopeCap ≤ w * (profileB.yCap + 1) ∧
      profileC.weightedCap + profileC.slopeCap ≤ w * (profileC.yCap + 1) ∧
      profileA.multiplicity - 1 + profileA.slopeCap ≤ profileA.yCap ∧
      profileB.multiplicity - 1 + profileB.slopeCap ≤ profileB.yCap ∧
      profileC.multiplicity - 1 + profileC.slopeCap ≤ profileC.yCap := by
  decide

theorem profile_small_gates :
    (2 * profileA.slopeCap - 1) * profileA.totalCap < prime ∧
      profileA.slopeCap < prime ∧
      (2 * profileB.slopeCap - 1) * profileB.totalCap < prime ∧
      profileB.slopeCap < prime ∧
      (2 * profileC.slopeCap - 1) * profileC.totalCap < prime ∧
      profileC.slopeCap < prime := by
  decide

theorem support_and_flag_values :
    supportProfile = support 1335 46 10 ∧
      fixedFlag = ⟨1335, 47, 12⟩ ∧ direction = ⟨2670, 93, 23⟩ ∧
      tailFlag (w + 1) = ⟨349964910, 12189790, 3014679⟩ ∧
      tailFlag (w + 2) = ⟨349967580, 12189883, 3014702⟩ := by
  decide

theorem fixed_flag_values :
    fixedFlag = ⟨1335, 47, 12⟩ ∧ direction = ⟨2670, 93, 23⟩ ∧
      tailFlag (w + 1) = ⟨349964910, 12189790, 3014679⟩ ∧
      tailFlag (w + 2) = ⟨349967580, 12189883, 3014702⟩ := by
  decide

theorem hybrid_flag_values :
    exactFirstTailFlag = ⟨349962240, 12189697, 3014656⟩ ∧
      rationalCoordinateFlag = ⟨174983790, 6029406, 1310743⟩ ∧
      hybridCoordinateFlag = ⟨174983790, 6094942, 1507351⟩ ∧
      movingFiberFlag = ⟨1335, 47, 13⟩ ∧
      movingCutFlag = ⟨174983790, 6160478, 1572887⟩ := by
  decide

theorem residual_formula_values :
    residualStageOne.regularCountCap = firstResidualRegularCost ∧
      pivotB.countCap + 1 = firstResidualSingularCost ∧
      residualStageTwo.regularCountCap = secondResidualRegularCost ∧
      pivotGcd12.countCap + 1 = secondResidualSingularCost := by
  decide

theorem six_cells_exact :
    fixedRegularCost = 263924776824012494 ∧
      fixedSingularCost = 89129741434159 ∧
      firstResidualRegularCost = 536839172882674 ∧
      firstResidualSingularCost = 856170430068949 ∧
      secondResidualRegularCost = 55442323120491 ∧
      secondResidualSingularCost = 105276894357776 := by
  decide

theorem seedless_numeric_values :
    seedlessWeightedCap = 8007252 ∧
      seedlessSingularListCap = 1403 ∧
      seedlessListNumerator = 49254757950073 ∧
      seedlessListCeiling = 967448892 := by
  decide

theorem budget_and_slack_exact :
    capacity = 274980728111395087 ∧
      totalCost = 265567635385876543 ∧
      mcaBudget = 274980727143946195 ∧
      slack = 9413091758069652 ∧ totalCost < mcaBudget := by
  decide

theorem cell_budget_strict :
    fixedCost + firstResidualCeiling + secondResidualCeiling < mcaBudget := by
  decide

end
end ProximityPrize.SubmissionLower.ContactTwoTailParameters6735Research
end
