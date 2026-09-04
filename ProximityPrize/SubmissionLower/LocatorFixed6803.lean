import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorFixedStage6803

/-!
# Ordinary per-factor fixed bound for the 68.03 row

This is the minimal consumer of `LocatorFixedStage6803`: the padded half of
the C2 own-bound, with agreement `181363` and the narrow A box widened to
middle `135` and total `6676`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixed6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN135 RCN137 RCN140 RCN156 RCN159 RCN174 RCN198
  RCN221 RCN222 RCN234 RCN238 RCN243 RCN263 RCN266 RCN268 RCN275 RCN286
  RCN319
open LocatorFactorAggregate LocatorFixed

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

theorem own_parameter_caps (p : FlagDegree)
    (hs : p.all ≤ 29) (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    padSlope p + 2 ≤ 29 ∧ padB p + padSlope p + 3 ≤ 135 ∧
      padA p + padB p + padSlope p + 3 ≤ 6676 := by
  have hp := pad_sums p
  have hps : padS p ≤ 29 := max_le hs (by decide)
  have hpy : padY p ≤ 135 := max_le hy (by omega)
  have hpt : padT p ≤ 6676 := max_le ht (by omega)
  rw [hp.1, hp.2.1, hp.2.2]
  exact ⟨hps, hpy, hpt⟩

theorem regular_factor_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 17773574)
    (hS : P.s ≤ 29) (hY : P.ys ≤ 135) (hT : P.total ≤ 6676)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) 2130706433 :=
    genericField_charP K 2130706433
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
  have hparam : s + 2 ≤ 29 ∧ b + s + 3 ≤ 135 ∧
      a + b + s + 3 ≤ 6676 := by
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
      (geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g).card ≤
      flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
        (paddedTail p 131073) := by
    let S0 := regularGeometricResidualStageOfSupport
      (RCN198.support a b s) Q selected Gamma
      (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S := reflagResidualStage S0
      (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected _ g).trans
        (regularSeeds_subset Q selected Gamma R)
    have hnodes : S.nodes.card = 181363 + 80781 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        181363 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using
        hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1
      hRdata.1.ne_zero hRsupport g
    have hcount := LocatorFixedStage6803.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2
      S hnodes hag hRbox hf
    simpa only [LocatorFixedStage6803.firstTail,
      LocatorFixedStage6803.secondTail, LocatorFixedStage6803.w,
      Nat.reduceAdd, geometricCumulativeFlag, a, b, s, padded_tail_eq] using
      hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card := hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073) :=
      Finset.sum_le_sum (fun g _ ↦ hstage g)
    _ ≤ paddedCost 131072 131073 p := by
      have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2

end

end ProximityPrize.SubmissionLower.LocatorFixed6803
