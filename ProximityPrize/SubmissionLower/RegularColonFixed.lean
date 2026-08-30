import ProximityPrize.SubmissionLower.RegularColonFixedStage
import ProximityPrize.SubmissionLower.RegularColonArithmetic
import ProximityPrize.SubmissionLower.FactorAggregate
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.FQ

/- Tails use each original factor's padded
   support; the first flag and its sum budgets are never padded. -/
namespace ProximityPrize.SubmissionLower.RegularColonFixed
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
open FactorAggregate
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
    (hbox : F ∈ globalCoefficientBox K D w L s) :
    F ∈ globalCoefficientBox K D w
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

def wholeSupport (T : ℕ) (hT : 56 ≤ T) : ResidualSupportParameters :=
  ⟨12, 56, T, by decide, by decide, hT, by decide⟩

theorem factor_support {T : ℕ} (hT : 56 ≤ T) (Q : P4) (hQ : Q ≠ 0)
    (HQ : ResidualSupportData (wholeSupport T hT) Q) (R : RegularIndex Q) :
    ResidualSupportData (wholeSupport T hT) R.1 := by
  have hd := (RCN167.positiveRFactors_spec Q R.1 R.2).2.1
  exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩

theorem own_parameter_caps (p : FlagDegree)
    (hs : p.all ≤ 12) (hy : middle p ≤ 56) (ht : total p ≤ 1282) :
    padSlope p + 2 ≤ 12 ∧ padB p + padSlope p + 3 ≤ 56 ∧
      padA p + padB p + padSlope p + 3 ≤ 1282 := by
  have hp := pad_sums p
  have hps : padS p ≤ 12 := max_le hs (by decide)
  have hpy : padY p ≤ 56 := max_le hy (by omega)
  have hpt : padT p ≤ 1282 := max_le ht (by omega)
  rw [hp.1, hp.2.1, hp.2.2]
  exact ⟨hps, hpy, hpt⟩

theorem regular_factor_count
    (T : ℕ) (hT : 56 ≤ T) (hTmax : T ≤ 1282)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K 7645344 131071 T 12)
    (HQ : ResidualSupportData (wholeSupport T hT) Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80112)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let p := regularCumulativeFlag Q R
  let a := padA p
  let b := padB p
  let s := padSlope p
  have hRdata := directFactor_data Q R.1 hQ 7645344 131071 T 12 hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt (by decide)
  have hRbox := own_box R.1 7645344 131071 T 12 hRdata.2.2
  have hRsupport := own_support R.1
  have hRwhole := factor_support hT Q hQ HQ R
  have hc := originalCumulativeFlag_cumulative R.1
  have hparam : s + 2 ≤ 12 ∧ b + s + 3 ≤ 56 ∧ a + b + s + 3 ≤ 1282 := by
    apply own_parameter_caps p
    · exact hRwhole.s_weight
    · simpa only [p, middle, regularCumulativeFlag, hc.2.1, wholeSupport] using
        hRwhole.ys_weight
    · simpa only [p, total, regularCumulativeFlag, hc.2.2] using
        hRwhole.total_weight.trans hTmax
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g : GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073) := by
    let S0 := regularGeometricResidualStageOfSupport (RCN198.support a b s) Q selected Gamma
      (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
    have hnodes : S.nodes.card = 182032 + 80112 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g, 182032 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount := RegularColonFixedStage.fixedStageBound a b s
      hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [RegularColonFixedStage.firstTail, RegularColonFixedStage.secondTail,
      RegularColonFixedStage.w, Nat.reduceAdd, geometricCumulativeFlag,
      a, b, s, padded_tail_eq] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card := hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073) := Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ paddedCost 131072 131073 p := by
      have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact FactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2

theorem regular_sum_count
    (T : ℕ) (hT : 56 ≤ T) (hTmax : T ≤ 1282)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K 7645344 131071 T 12)
    (HQ : ResidualSupportData (wholeSupport T hT) Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80112)
    (hfull : ∀ R : RegularIndex Q, (regularSeeds Q selected Gamma R).Nonempty →
      (regularCumulativeFlag Q R).all = 12 → middle (regularCumulativeFlag Q R) ≤ 53) :
    (∑ R : RegularIndex Q, (regularSeeds Q selected Gamma R).card) ≤
      paddedCost 131072 131073 (cap T 53 12) := by
  let active : Finset (RegularIndex Q) :=
    Finset.univ.filter (fun R => (regularSeeds Q selected Gamma R).Nonempty)
  let p : active → FlagDegree := fun R => regularCumulativeFlag Q R.1
  have hactive (R : active) : (regularSeeds Q selected Gamma R.1).Nonempty :=
    (Finset.mem_filter.mp R.2).2
  have hb := regularCumulativeFlag_budgets Q hQ HQ
  have hsum (f : RegularIndex Q → ℕ) : (∑ R : active, f R.1) ≤ ∑ R, f R := by
    conv_lhs => rw [Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ active)
  have hcost := FactorAggregate.aggregate_caps_bound T 131072 131073 hT p
    (fun R => regularCumulativeFlag_positive Q R.1)
    ((hsum (fun R => (regularCumulativeFlag Q R).all)).trans hb.1)
    ((hsum (fun R => middle (regularCumulativeFlag Q R))).trans hb.2.1)
    ((hsum (fun R => total (regularCumulativeFlag Q R))).trans hb.2.2)
    (fun R => hfull R.1 (hactive R))
  have hcount_eq : (∑ R : RegularIndex Q, (regularSeeds Q selected Gamma R).card) =
      ∑ R : active, (regularSeeds Q selected Gamma R.1).card := by
    rw [Finset.sum_coe_sort active
      (fun R : RegularIndex Q => (regularSeeds Q selected Gamma R).card)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro R hR hnot
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hnot (Finset.mem_filter.mpr ⟨hR, hne⟩)
  rw [hcount_eq]
  exact (Finset.sum_le_sum (fun R _ => regular_factor_count T hT hTmax Q hQ
    hbox HQ selected Gamma u0 u1 hdegree hagreement hno R.1)).trans hcost

def profile (T : ℕ) : RCN276.Profile :=
  ⟨262144, 131071, 182032, 7645344, T, 12⟩

theorem cost_eq (T : ℕ) (hT : T = 1280 ∨ T = 1282) :
    paddedCost 131072 131073 (cap T 53 12) =
      RegularColonArithmetic.fixedCost (T - 53) 40 10 := by
  rcases hT with rfl | rfl <;>
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, cap,
      RegularColonArithmetic.fixedCost, RegularColonArithmetic.w,
      RCN206.surfaceFlag,
      reducedResidualAgreementFlag, reducedAgreementDirection, RCN198.support, flagMixed]

theorem fixed_count_le
    (T : ℕ) (hT : T = 1280 ∨ T = 1282)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K 7645344 131071 T 12)
    (HQ : ResidualSupportData (wholeSupport T (by rcases hT with rfl | rfl <;> decide)) Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80112)
    (hfull : ∀ R : RegularIndex Q, (regularSeeds Q selected Gamma R).Nonempty →
      (regularCumulativeFlag Q R).all = 12 → middle (regularCumulativeFlag Q R) ≤ 53) :
    Gamma.card ≤ RegularColonArithmetic.fixedCost (T - 53) 40 10 +
      (RegularColonArithmetic.fixedSingular T).countCap := by
  have hTlo : 56 ≤ T := by rcases hT with rfl | rfl <;> decide
  have hThi : T ≤ 1282 := by rcases hT with rfl | rfl <;> decide
  have hcover := RCN239.card_le_regular_sum_add_singular
    (profile T) Q hQ hbox
    (by change 1 ≤ 12; decide) (by change 12 < 2130706433; decide)
    (by change 1 ≤ 131071; decide)
    (by change 131071 < 23 * 7645344; decide)
    (by change 1 ≤ 23 * T; omega)
    (by change 23 * T < 2130706433; omega) selected Gamma hsolution
  have hreg := regular_sum_count T hTlo hThi Q hQ hbox HQ selected Gamma u0 u1
    hdegree hagreement hno hfull
  rw [cost_eq T hT] at hreg
  have hsing := RCN292.TightParameters.singularSeeds_count_le_countCap
    (RegularColonArithmetic.fixedSingular T) Q hQ hbox
    (by change 1 ≤ 12; decide)
    (by change 12 < 2130706433; decide)
    (by change 1 ≤ 131071; decide)
    (by change 131071 < 2130706433; decide)
    (by change 131071 < 23 * 7645344; decide)
    (by change 1 ≤ 23 * T; omega)
    (by change (23 * 7645344 - 1) / 131071 < 2130706433; decide)
    (by change 23 * T < 2130706433; omega)
    (by
      rcases hT with rfl | rfl <;> decide)
    (by change 131071 < 182032; decide)
    (by change 182032 ≤ 262144; decide)
    selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18)) = 262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [RegularColonArithmetic.fixedSingular,
          RCN318.TightParameters.errors, RegularColonArithmetic.n,
          RegularColonArithmetic.w, RegularColonArithmetic.agreements,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hreg hsing)

end
end ProximityPrize.SubmissionLower.RegularColonFixed
