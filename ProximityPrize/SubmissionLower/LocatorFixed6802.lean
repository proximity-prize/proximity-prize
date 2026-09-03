/- The padded per-regular-factor bound, retuned to the 6802 A-kernel. -/
import ProximityPrize.SubmissionLower.Packed6801
import ProximityPrize.SubmissionLower.LocatorFixedStage6802

namespace ProximityPrize.SubmissionLower.LocatorFixed6802
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222
  RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234
  RCN137 RCN198 RCN263 LocatorFactorAggregate
open LocatorFixedStage6802
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
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

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
    reducedResidualAgreementFlag
      (RCN198.support (padA p) (padB p) (padSlope p)) d = paddedTail p d := by
  have hc := pad_sums p
  have hs : 2 ≤ padS p := le_max_right _ _
  simp only [reducedResidualAgreementFlag, reducedAgreementDirection,
    RCN198.support, hc.1, hc.2.1, hc.2.2, paddedTail]
  have he : 2 * padS p - 2 = 2 * (padS p - 1) := by omega
  rw [he]

theorem own_support (F : P4) :
    ResidualSupportData
      (RCN198.support (padA (originalCumulativeFlag F))
        (padB (originalCumulativeFlag F))
        (padSlope (originalCumulativeFlag F))) F := by
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

theorem factor_support {P : ResidualSupportParameters} (Q : P4) (hQ : Q ≠ 0)
    (HQ : ResidualSupportData P Q) (R : RegularIndex Q) :
    ResidualSupportData P R.1 := by
  have hd := (RCN167.positiveRFactors_spec Q R.1 R.2).2.1
  exact ⟨
    (weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩

theorem own_parameter_caps (p : FlagDegree)
    (hs : p.all ≤ 29) (hy : middle p ≤ 132) (ht : total p ≤ 6403) :
    padSlope p + 2 ≤ 29 ∧ padB p + padSlope p + 3 ≤ 132 ∧
      padA p + padB p + padSlope p + 3 ≤ 6403 := by
  have hp := pad_sums p
  have hps : padS p ≤ 29 := max_le hs (by decide)
  have hpy : padY p ≤ 132 := max_le hy (by omega)
  have hpt : padT p ≤ 6403 := max_le ht (by omega)
  rw [hp.1, hp.2.1, hp.2.2]
  exact ⟨hps, hpy, hpt⟩

theorem regular_factor_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 17411808)
    (hS : P.s ≤ 29) (hY : P.ys ≤ 132) (hT : P.total ≤ 6403)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let p := regularCumulativeFlag Q R
  let a := padA p
  let b := padB p
  let s := padSlope p
  have hRdata := directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox := own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport := own_support R.1
  have hRwhole := factor_support Q hQ HQ R
  have hc := originalCumulativeFlag_cumulative R.1
  have hparam : s + 2 ≤ 29 ∧ b + s + 3 ≤ 132 ∧
      a + b + s + 3 ≤ 6403 := by
    apply own_parameter_caps p
    · exact hRwhole.s_weight.trans hS
    · simpa only [p, middle, regularCumulativeFlag, hc.2.1] using
        hRwhole.ys_weight.trans hY
    · simpa only [p, total, regularCumulativeFlag, hc.2.2] using
        hRwhole.total_weight.trans hT
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
    let S0 := regularGeometricResidualStageOfSupport
      (RCN198.support a b s) Q selected Gamma (Finset.univ : Finset I)
      IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected _ g).trans
        (regularSeeds_subset Q selected Gamma R)
    have hnodes : S.nodes.card = 181373 + 80771 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        181373 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount := LocatorFixedStage6802.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [LocatorFixedStage6802.firstTail,
      LocatorFixedStage6802.secondTail, LocatorFixedStage6802.w, Nat.reduceAdd,
      geometricCumulativeFlag, a, b, s, padded_tail_eq] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card := hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073) := Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ paddedCost 131072 131073 p := by
      have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2

end
end ProximityPrize.SubmissionLower.LocatorFixed6802
