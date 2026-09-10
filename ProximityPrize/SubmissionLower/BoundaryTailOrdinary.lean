import ProximityPrize.SubmissionLower.BoundaryTailOrdinaryLow
import ProximityPrize.SubmissionLower.BoundaryTailOrdinaryHigh
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailOrdinary
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 LocatorFactorAggregate
open LocatorHybridCostC2 LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def padA (p:FlagDegree):ℕ:=padT p - padY p
def padB (p:FlagDegree):ℕ:=padY p - padS p - 1
def padSlope (p:FlagDegree):ℕ:=padS p - 2
theorem pad_sums (p:FlagDegree) :
    padSlope p + 2=padS p ∧
    padB p + padSlope p + 3=padY p ∧
    padA p + padB p + padSlope p + 3=padT p:=by
  have hs:2 ≤ padS p:=le_max_right _ _
  have hy:padS p + 1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  dsimp [padA,padB,padSlope]
  omega
theorem padded_tail_eq (p:FlagDegree) (d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support (padA p) (padB p) (padSlope p)) d=
      paddedTail p d:=by
  have hc:=pad_sums p
  have hs:2 ≤ padS p:=le_max_right _ _
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,
    RCN198.support,hc.1,hc.2.1,hc.2.2,paddedTail]
  have he:2 * padS p - 2=2 * (padS p - 1):=by omega
  rw [he]
theorem own_support (F:P4) :
    ResidualSupportData
      (RCN198.support (padA (originalCumulativeFlag F))
        (padB (originalCumulativeFlag F)) (padSlope (originalCumulativeFlag F))) F:=by
  have hc:=originalCumulativeFlag_cumulative F
  have hp:=pad_sums (originalCumulativeFlag F)
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
theorem own_box (F:P4) (D w L s:ℕ)
    (hbox:F ∈ RCN174.globalCoefficientBox K D w L s) :
    F ∈ RCN174.globalCoefficientBox K D w
      (padA (originalCumulativeFlag F) + padB (originalCumulativeFlag F) +
        padSlope (originalCumulativeFlag F) + 3)
      (padSlope (originalCumulativeFlag F) + 2):=by
  have hs:=(own_support F).s_weight
  have ht:=(own_support F).total_weight
  intro d hd
  have hds:=(MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
  have hdt:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
  rw [weight_fin4] at hds hdt
  simp only [residualSWeights,residualTotalWeights,RCN198.support,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at hds hdt
  exact ⟨by omega,hds, (hbox hd).2.2⟩
theorem factor_support {P:ResidualSupportParameters} (Q:P4) (hQ:Q ≠ 0)
    (HQ:ResidualSupportData P Q) (R:RegularIndex Q) :
    ResidualSupportData P R.1:=by
  have hd:=(RCN167.positiveRFactors_spec Q R.1 R.2).2.1
  exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩
theorem own_parameter_caps (p:FlagDegree)
    (hs:p.all ≤ 30) (hy:middle p ≤ 139) (ht:total p ≤ 7199) :
    padSlope p + 2 ≤ 30 ∧ padB p + padSlope p + 3 ≤ 139 ∧
      padA p + padB p + padSlope p + 3 ≤ 7199:=by
  have hp:=pad_sums p
  have hps:padS p ≤ 30:=max_le hs (by decide)
  have hpy:padY p ≤ 139:=max_le hy (by omega)
  have hpt:padT p ≤ 7199:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem regular_factor_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D < 2130706433)
    (hS:P.s ≤ 30) (hY:P.ys ≤ 139) (hT:P.total ≤ 7199)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181343 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80801)
    (R:RegularIndex Q)
    (hhyb : ¬ HybridAppliesC2 (regularCumulativeFlag Q R)) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R):=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  let p:=regularCumulativeFlag Q R
  let a:=padA p
  let b:=padB p
  let s:=padSlope p
  have hlow := BoundaryTailPaddedIdentity.low_pad_parameters p hhyb
  have hRdata:=directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < 2130706433:=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox:=own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:=own_support R.1
  have hRwhole:=factor_support Q hQ HQ R
  have hc:=originalCumulativeFlag_cumulative R.1
  have hparam:s + 2 ≤ 30 ∧ b + s + 3 ≤ 139 ∧ a + b + s + 3 ≤ 7199:=by
    apply own_parameter_caps p
    · exact hRwhole.s_weight.trans hS
    · simpa only [p,middle,regularCumulativeFlag,hc.2.1] using
        hRwhole.ys_weight.trans hY
    · simpa only [p,total,regularCumulativeFlag,hc.2.2] using
        hRwhole.total_weight.trans hT
  have hsolutions:∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073):=by
    let S0:=regularGeometricResidualStageOfSupport (RCN198.support a b s) Q selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S:=reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub:geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
    have hnodes:S.nodes.card=181343 + 80801:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181343 ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,S0,ResidualStage.agreementFiber,ResidualStage.Agrees,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf:=geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount:=BoundaryTailOrdinaryLow.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 hlow S hnodes hag hRbox hf
    simpa only [BoundaryTailOrdinaryLow.firstTail,BoundaryTailOrdinaryLow.secondTail,
      BoundaryTailOrdinaryLow.w,Nat.reduceAdd,geometricCumulativeFlag,
      a,b,s,padded_tail_eq] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
          (paddedTail p 131073):=Finset.sum_le_sum (fun g _=> hstage g)
    _ ≤ paddedCost 131072 131073 p:=by
      have hb:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2

/-- The high-cell alternative, with all geometric factors charged against
the original factor's same three cumulative degree budgets. -/
theorem regular_factor_count_high
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D < 2130706433)
    (hS : P.s ≤ 30) (hY : P.ys ≤ 139) (hT : P.total ≤ 7199)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181343 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80801)
    (R : RegularIndex Q)
    (hhyb : HybridAppliesC2 (regularCumulativeFlag Q R)) :
    (regularSeeds Q selected Gamma R).card ≤
      BoundaryTailOrdinaryHigh.bound (regularCumulativeFlag Q R)
        (total (regularCumulativeFlag Q R)) (middle (regularCumulativeFlag Q R))
        (regularCumulativeFlag Q R).all := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  set p := regularCumulativeFlag Q R with hp
  have hRdata := directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox0 : R.1 ∈ RCN174.globalCoefficientBox K D 131071
      (padA p+padB p+padSlope p+3) (padSlope p+2) :=
    own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport : ResidualSupportData
      (RCN198.support (padA p) (padB p) (padSlope p)) R.1 := own_support R.1
  have hRwhole := factor_support Q hQ HQ R
  have hc := originalCumulativeFlag_cumulative R.1
  have hps := pad_sums p
  have hRbox : R.1 ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p) := by
    rw [← hps.2.2, ← hps.1]
    exact hRbox0
  have h1 : p.all ≤ 30 := hRwhole.s_weight.trans hS
  have h2 : middle p ≤ 139 := by
    simpa only [hp, middle, regularCumulativeFlag, hc.2.1] using
      hRwhole.ys_weight.trans hY
  have h3 : total p ≤ 7199 := by
    simpa only [hp, total, regularCumulativeFlag, hc.2.2] using
      hRwhole.total_weight.trans hT
  have hpS : padS p ≤ 30 := max_le h1 (by decide)
  have hpY : padY p ≤ 139 := max_le h2 (by omega)
  have hpT : padT p ≤ 7199 := max_le h3 (by omega)
  have hp3 : 3 ≤ p.all := hhyb.1
  have hpSeq : padS p = p.all := max_eq_left (by omega : 2 ≤ p.all)
  have hpYeq : padY p = middle p :=
    max_eq_left (by rw [hpSeq]; exact hhyb.2.trans' (by omega))
  have hpTeq : padT p = total p := by
    unfold padT
    rw [hpYeq]
    exact max_eq_left (by dsimp [total, middle]; omega)
  have hpS3 : 3 ≤ padS p := by rw [hpSeq]; exact hhyb.1
  have hhyb' : padS p+2 ≤ padY p := by rw [hpSeq, hpYeq]; exact hhyb.2
  have hpyt : padY p ≤ padT p := le_max_right _ _
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g : GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        BoundaryTailOrdinaryHigh.bound (geometricCumulativeFlag K g)
          (padT p) (padY p) (padS p) := by
    let S0 := regularGeometricResidualStageOfSupport
      (RCN198.support (padA p) (padB p) (padSlope p)) Q selected Gamma
      (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub : geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
      (geometricSeeds_subset K R.1 selected _ g).trans
        (regularSeeds_subset Q selected Gamma R)
    have hnodes : S.nodes.card = 181343+80801 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        181343 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hf1 : (geometricCumulativeFlag K g).all ≤ padSlope p+2 := hf.1
    have hf2 : (geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ padB p+padSlope p+3 := hf.2.1
    have hf3 : (geometricCumulativeFlag K g).zOnly+
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤
          padA p+padB p+padSlope p+3 := hf.2.2
    have hf' : (geometricCumulativeFlag K g).all ≤ padS p ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ padY p ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
          (geometricCumulativeFlag K g).all ≤ padT p := by
      refine ⟨?_, ?_, ?_⟩ <;> omega
    have hcount := BoundaryTailOrdinaryHigh.stage_card_le D (padT p) (padY p) (padS p)
      hDlow hDhigh hpS3 hhyb' hpyt hpS hpY hpT S hnodes hag hRbox hf'
    simpa only [geometricCumulativeFlag] using hcount
  have hsum :
      (∑ g : GeometricFactor K R.1,
        BoundaryTailOrdinaryHigh.bound (geometricCumulativeFlag K g)
          (padT p) (padY p) (padS p)) ≤
        BoundaryTailOrdinaryHigh.bound p (padT p) (padY p) (padS p) := by
    have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
    unfold BoundaryTailOrdinaryHigh.bound
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
        hb.1 hb.2.1 hb.2.2)
      (Nat.mul_le_mul_left 65539
        (LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
          hb.1 hb.2.1 hb.2.2))
  have hcount := hcover.trans ((Finset.sum_le_sum (fun g _ => hstage g)).trans hsum)
  rwa [hpTeq, hpYeq, hpSeq] at hcount

/-- Numerical raw cost used by the 68.05 ordinary-domain envelope. -/
def rawCost (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then
    BoundaryTailOrdinaryHigh.bound p (total p) (middle p) p.all
  else paddedCost 131072 131073 p

/-- The concrete per-factor estimate for every ordinary-domain cell. -/
theorem regular_factor_count_raw
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D < 2130706433)
    (hS : P.s ≤ 30) (hY : P.ys ≤ 139) (hT : P.total ≤ 7199)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181343 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80801)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤ rawCost (regularCumulativeFlag Q R) := by
  unfold rawCost
  split_ifs with hhyb
  · exact regular_factor_count_high D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb
  · exact regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb

end

end ProximityPrize.SubmissionLower.BoundaryTailOrdinary
