import ProximityPrize.SubmissionLower.LocatorFixedStage
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.FQ

/- Tails use each original factor's padded
   support; the first flag and its sum budgets are never padded. -/
namespace ProximityPrize.SubmissionLower.LocatorFixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286
open RCN081 RCN135 RCN095
open RCN238 RCN243
open RCN222 RCN266
open RCN221
open RCN268 RCN140
open RCN275 RCN130
open RCN156 RCN159
open RCN234 RCN137
open RCN198 RCN263
open LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

def padA (p : FlagDegree) : ℕ := padT p - padY p
def padB (p : FlagDegree) : ℕ := padY p - padS p - 1
def padSlope (p : FlagDegree) : ℕ := padS p - 2

theorem pad_sums (p : FlagDegree) :
    padSlope p + 2 = padS p ∧
    padB p + padSlope p + 3 = padY p ∧
    padA p + padB p + padSlope p + 3 = padT p := by
  have hs : 2 ≤ padS p := le_max_right _ _
  have hy : padS p + 1 ≤ padY p := le_max_right _ _
  have ht : padY p ≤ padT p := le_max_right _ _
  dsimp [padA, padB, padSlope]
  omega

theorem exactTail6744_eq (p : FlagDegree) :
    exactTail6744 p = LocatorFixedStage.exactFirstTail
      (padA p) (padB p) (padSlope p) := by
  have hp := pad_sums p
  rw [exactTail6744_coordinates]
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [LocatorFixedStage.exactFirstTail,
    LocatorFixedStage.w, padA, padB, padSlope] <;> omega

theorem hybridTail6744_eq (p : FlagDegree) :
    hybridTail6744 p = LocatorFixedStage.hybridSecondTail
      (padA p) (padB p) (padSlope p) := by
  have hp := pad_sums p
  rw [hybridTail6744_coordinates]
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [LocatorFixedStage.hybridSecondTail, LocatorFixedStage.errors,
    padA, padB, padSlope] <;> omega

theorem movingFiber6744_eq (p : FlagDegree) :
    movingFiber6744 p = LocatorFixedStage.movingFiber
      (padA p) (padB p) (padSlope p) := by
  have hp := pad_sums p
  rw [movingFiber6744_coordinates]
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [LocatorFixedStage.movingFiber,
    RCN206.fiberFlag, padA, padB, padSlope] <;> omega

theorem movingCut6744_eq (p : FlagDegree) :
    movingCut6744 p = LocatorFixedStage.movingCut
      (padA p) (padB p) (padSlope p) := by
  have hp := pad_sums p
  rw [movingCut6744_coordinates]
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [LocatorFixedStage.movingCut,
    RCN198.center, RCN198.direction, RCN206.surfaceFlag, LocatorFixedStage.w,
    unitYZFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
    padA, padB, padSlope] <;> omega

theorem hybridCostAt6744_eq (q p : FlagDegree) :
    hybridCostAt6744 q p = LocatorFixedStage.hybridStageCost q
      (padA p) (padB p) (padSlope p) := by
  rw [hybridCostAt6744, LocatorFixedStage.hybridStageCost,
    exactTail6744_eq, hybridTail6744_eq, movingFiber6744_eq, movingCut6744_eq]
  rfl

theorem padded_tail_eq (p : FlagDegree) (d : ℕ) :
    reducedResidualAgreementFlag (RCN198.support (padA p) (padB p) (padSlope p)) d =
      paddedTail p d := by
  have hc := pad_sums p
  have hs : 2 ≤ padS p := le_max_right _ _
  simp only [reducedResidualAgreementFlag, reducedAgreementDirection,
    RCN198.support, hc.1, hc.2.1, hc.2.2, paddedTail]
  have he : 2 * padS p - 2 = 2 * (padS p - 1) := by omega
  rw [he]

theorem own_support (F : P4) :
    ResidualSupportData
      (RCN198.support (padA (originalCumulativeFlag F))
        (padB (originalCumulativeFlag F)) (padSlope (originalCumulativeFlag F))) F := by
  have hc := originalCumulativeFlag_cumulative F
  have hp := pad_sums (originalCumulativeFlag F)
  refine ⟨?_, ?_, ?_⟩
  · change wt residualSWeights F ≤ padSlope (originalCumulativeFlag F) + 2
    rw [hp.1, ← hc.1]
    exact le_max_left _ _
  · change wt residualYSWeights F ≤
      padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
    rw [hp.2.1, ← hc.2.1]
    exact le_max_left _ _
  · change wt residualTotalWeights F ≤ padA (originalCumulativeFlag F) +
      padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
    rw [hp.2.2, ← hc.2.2]
    exact le_max_left _ _

theorem own_box (F : P4) (D w L s : ℕ)
    (hbox : F ∈ RCN174.globalCoefficientBox K D w L s) :
    F ∈ RCN174.globalCoefficientBox K D w
      (padA (originalCumulativeFlag F) + padB (originalCumulativeFlag F) +
        padSlope (originalCumulativeFlag F) + 3)
      (padSlope (originalCumulativeFlag F) + 2) := by
  have hs := (own_support F).s_weight
  have ht := (own_support F).total_weight
  intro d hd
  have hds := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
  have hdt := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
  rw [weight_fin4] at hds hdt
  simp only [residualSWeights, residualTotalWeights, RCN198.support, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hds hdt
  exact ⟨by omega, hds, (hbox hd).2.2⟩

/-- Whole-polynomial support. The smaller Y bounds below concern individual
irreducible factors only. -/
def wholeSupport : ResidualSupportParameters :=
  ⟨13, 62, 1510, by decide, by decide, by decide, by decide⟩

theorem factor_support (Q : P4) (hQ : Q ≠ 0)
    (HQ : ResidualSupportData wholeSupport Q) (R : RegularIndex Q) :
    ResidualSupportData wholeSupport R.1 := by
  have hd := (RCN167.positiveRFactors_spec Q R.1 R.2).2.1
  exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩

theorem own_parameter_caps (p : FlagDegree)
    (hs : p.all ≤ 13) (hy : middle p ≤ 62) (ht : total p ≤ 1510) :
    padSlope p + 2 ≤ 13 ∧ padB p + padSlope p + 3 ≤ 62 ∧
      padA p + padB p + padSlope p + 3 ≤ 1510 := by
  have hp := pad_sums p
  have hps : padS p ≤ 13 := max_le hs (by decide)
  have hpy : padY p ≤ 62 := max_le hy (by omega)
  have hpt : padT p ≤ 1510 := max_le ht (by omega)
  rw [hp.1, hp.2.1, hp.2.2]
  exact ⟨hps, hpy, hpt⟩

theorem regular_factor_count
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K 8187435 131071 1510 13)
    (HQ : ResidualSupportData wholeSupport Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181943 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80201)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      hybridCost6744 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let p := regularCumulativeFlag Q R
  let a := padA p
  let b := padB p
  let s := padSlope p
  have hRdata := directFactor_data Q R.1 hQ 8187435 131071 1510 13 hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt (by decide)
  have hRbox := own_box R.1 8187435 131071 1510 13 hRdata.2.2
  have hRsupport := own_support R.1
  have hRwhole := factor_support Q hQ HQ R
  have hc := originalCumulativeFlag_cumulative R.1
  have hparam : s + 2 ≤ 13 ∧ b + s + 3 ≤ 62 ∧ a + b + s + 3 ≤ 1510 := by
    apply own_parameter_caps p
    · exact hRwhole.s_weight
    · simpa only [p, middle, regularCumulativeFlag, hc.2.1, wholeSupport] using
        hRwhole.ys_weight
    · simpa only [p, total, regularCumulativeFlag, hc.2.2, wholeSupport] using
        hRwhole.total_weight
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g : GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        hybridCostAt6744 (geometricCumulativeFlag K g) p := by
    let S0 := regularGeometricResidualStageOfSupport (RCN198.support a b s) Q selected Gamma
      (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
    have hnodes : S.nodes.card = 181943 + 80201 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g, 181943 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount := LocatorFixedStage.fixedStageBound a b s
      hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [geometricCumulativeFlag, a, b, s, hybridCostAt6744_eq] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card := hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        hybridCostAt6744 (geometricCumulativeFlag K g) p :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ hybridCost6744 p := by
      have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact LocatorFactorAggregate.sum_hybridCostAt6744_le
        (geometricCumulativeFlag K) p hb.1 hb.2.1 hb.2.2


/-- The sum ledger uses actual, unpadded first flags over every positive-R
irreducible factor.  The exceptional Y caps require no active-seed hypothesis. -/
theorem regular_sum_count
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K 8187435 131071 1510 13)
    (HQ : ResidualSupportData wholeSupport Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181943 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80201)
    (h10 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 10 →
      middle (regularCumulativeFlag Q R) ≤ 58)
    (h11 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 11 →
      middle (regularCumulativeFlag Q R) ≤ 54)
    (h12 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 12 →
      middle (regularCumulativeFlag Q R) ≤ 51)
    (h13 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 13 →
      middle (regularCumulativeFlag Q R) ≤ 46) :
    (∑ R : RegularIndex Q, (regularSeeds Q selected Gamma R).card) ≤
      250000000000000000 := by
  have hb := regularCumulativeFlag_budgets Q hQ HQ
  have hsSum : (∑ R : RegularIndex Q, (regularCumulativeFlag Q R).all) ≤ 13 :=
    hb.1
  have hySum : (∑ R : RegularIndex Q, middle (regularCumulativeFlag Q R)) ≤ 62 :=
    hb.2.1
  have htSum : (∑ R : RegularIndex Q, total (regularCumulativeFlag Q R)) ≤ 1510 :=
    hb.2.2
  have hs (R : RegularIndex Q) : (regularCumulativeFlag Q R).all ≤ 13 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)).trans hsSum
  have hy (R : RegularIndex Q) : middle (regularCumulativeFlag Q R) ≤ 62 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)).trans hySum
  have hcost := LocatorFactorAggregate.aggregate_6744 (regularCumulativeFlag Q)
    hs hy htSum h10 h11 h12 h13
  exact (Finset.sum_le_sum (fun R _ =>
    regular_factor_count Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R)).trans hcost

def profile : RCN276.Profile :=
  ⟨262144, 131071, 181943, 8187435, 1510, 13⟩

/-- Fixed-polynomial count for the 80201-error row. -/
theorem fixed_count_le
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K 8187435 131071 1510 13)
    (HQ : ResidualSupportData wholeSupport Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181943 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80201)
    (h10 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 10 →
      middle (regularCumulativeFlag Q R) ≤ 58)
    (h11 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 11 →
      middle (regularCumulativeFlag Q R) ≤ 54)
    (h12 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 12 →
      middle (regularCumulativeFlag Q R) ≤ 51)
    (h13 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 13 →
      middle (regularCumulativeFlag Q R) ≤ 46) :
    Gamma.card ≤ 250000000000000000 + LocatorArithmetic.fixedSingular.countCap := by
  have hg := LocatorArithmetic.fixed_singular_gates
  have hcover := RCN239.card_le_regular_sum_add_singular
    profile Q hQ hbox hg.s_pos hg.s_small hg.w_pos hg.kD
    hg.algebraic_pos hg.algebraic_small selected Gamma hsolution
  have hreg := regular_sum_count Q hQ hbox HQ selected Gamma u0 u1
    hdegree hagreement hno h10 h11 h12 h13
  have hsing := RCN292.TightParameters.singularSeeds_count_le_countCap
    LocatorArithmetic.fixedSingular Q hQ hbox
    hg.s_pos hg.s_small hg.w_pos hg.w_small hg.kD hg.algebraic_pos
    hg.implicit_small hg.algebraic_small hg.mixed_small hg.wa hg.an
    selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18)) = 262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [LocatorArithmetic.fixedSingular,
          RCN318.TightParameters.errors, LocatorArithmetic.n,
          LocatorArithmetic.w, LocatorArithmetic.agreements,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hreg hsing)

end
end ProximityPrize.SubmissionLower.LocatorFixed
