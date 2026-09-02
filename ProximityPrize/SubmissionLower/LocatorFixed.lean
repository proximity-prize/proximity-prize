import ProximityPrize.SubmissionLower.LocatorFixedStage
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.FQ
namespace ProximityPrize.SubmissionLower.LocatorFixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 LocatorFactorAggregate
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
    (hs:p.all ≤ 20) (hy:middle p ≤ 93) (ht:total p ≤ 3321) :
    padSlope p + 2 ≤ 20 ∧ padB p + padSlope p + 3 ≤ 93 ∧
      padA p + padB p + padSlope p + 3 ≤ 3321:=by
  have hp:=pad_sums p
  have hps:padS p ≤ 20:=max_le hs (by decide)
  have hpy:padY p ≤ 93:=max_le hy (by omega)
  have hpt:padT p ≤ 3321:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem regular_factor_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hS:P.s ≤ 20) (hY:P.ys ≤ 93) (hT:P.total ≤ 3321)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565)
    (R:RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag Q R):=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  let p:=regularCumulativeFlag Q R
  let a:=padA p
  let b:=padB p
  let s:=padSlope p
  have hRdata:=directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < 2130706433:=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox:=own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:=own_support R.1
  have hRwhole:=factor_support Q hQ HQ R
  have hc:=originalCumulativeFlag_cumulative R.1
  have hparam:s + 2 ≤ 20 ∧ b + s + 3 ≤ 93 ∧ a + b + s + 3 ≤ 3321:=by
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
    have hnodes:S.nodes.card=181579 + 80565:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181579 ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,S0,ResidualStage.agreementFiber,ResidualStage.Agrees,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf:=geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount:=LocatorFixedStage.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [LocatorFixedStage.firstTail,LocatorFixedStage.secondTail,
      LocatorFixedStage.w,Nat.reduceAdd,geometricCumulativeFlag,
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
def regularCost (T YS S:ℕ):ℕ:=
  paddedCost 131072 131073 (cap T YS S)
theorem regular_sum_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hS:P.s ≤ 20) (hY:P.ys ≤ 93) (hT:P.total ≤ 3321)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565) :
    (∑ R:RegularIndex Q, (regularSeeds Q selected Gamma R).card) ≤
      regularCost P.total P.ys P.s:=by
  have hb:=regularCumulativeFlag_budgets Q hQ HQ
  have hc:=cap_cumulative P.total P.ys P.s P.s_le_ys P.ys_le_total
  have hcost:=merge_padded_costs 131072 131073 (regularCumulativeFlag Q)
    (cap P.total P.ys P.s)
    (by simpa only [hc.1] using hb.1)
    (by rw [hc.2.1]; simpa only [middle] using hb.2.1)
    (by rw [hc.2.2]; simpa only [total] using hb.2.2)
  exact (Finset.sum_le_sum (fun R _=>
    regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R)).trans hcost
def profile (D T S:ℕ):RCN276.Profile:=
  ⟨262144,131071,181579,D,T,S⟩
def singularProfile (D T S:ℕ):RCN318.TightParameters:=
  ⟨262144,131071,181579,D,T,S⟩
def equationCost (D T YS S:ℕ):ℕ:=
  regularCost T YS S + (singularProfile D T S).countCap
structure SingularGates (P:RCN318.TightParameters):Prop where
  s_pos:1 ≤ P.s
  s_small:P.s < 2130706433
  w_pos:1 ≤ P.w
  w_small:P.w < 2130706433
  kD:P.w < P.kappa * P.D
  algebraic_pos:1 ≤ P.algebraicCap
  implicit_small:P.implicitYCap < 2130706433
  algebraic_small:P.algebraicCap < 2130706433
  mixed_small:2 * P.implicitYCap * P.algebraicCap < 2130706433
  wa:P.w < P.a
  an:P.a ≤ P.n
theorem singular_gates (D T S:ℕ)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hTpos:1 ≤ T) (hT:T ≤ 3321)
    (hSpos:1 ≤ S) (hS:S ≤ 20) :
    SingularGates (singularProfile D T S):=by
  have hkpos:1 ≤ 2*S-1:=by omega
  have hk:2*S-1 ≤ 39:=by omega
  have hDle:D ≤ (2*S-1)*D:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right D hkpos
  have hnum:(2*S-1)*D-1 ≤ 474492056:=by
    have hp:=Nat.mul_le_mul hk hDhigh
    norm_num at hp
    omega
  have hiy:((2*S-1)*D-1)/131071 ≤ 3620:=
    (Nat.div_le_div_right hnum).trans (by decide)
  have halgpos:1 ≤ (2*S-1)*T:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hkpos hTpos
  have halg:(2*S-1)*T ≤ 126048:=by
    have hp:=Nat.mul_le_mul hk hT
    norm_num at hp
    exact hp
  have hmix_le:2*(((2*S-1)*D-1)/131071)*((2*S-1)*T) ≤ 912587520:=
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hiy) halg).trans (by decide)
  have hmix:2*(((2*S-1)*D-1)/131071)*((2*S-1)*T) < 2130706433:=
    hmix_le.trans_lt (by decide)
  refine ⟨hSpos, ?_,by change 1 ≤ 131071; decide,
    by change 131071 < 2130706433; decide, ?_,halgpos, ?_, ?_,hmix,
    by change 131071 < 181579; decide,by change 181579 ≤ 262144; decide⟩
  · exact hS.trans_lt (by decide)
  · change 131071 < (2*S-1)*D
    omega
  · exact hiy.trans_lt (by decide)
  · exact halg.trans_lt (by decide)
theorem fixed_count_le
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hS:P.s ≤ 20) (hY:P.ys ≤ 93) (hT:P.total ≤ 3321)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma Q=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565) :
    Gamma.card ≤ equationCost D P.total P.ys P.s:=by
  have hg:=singular_gates D P.total P.s hDlow hDhigh
    (P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)) hT P.one_le_s hS
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (profile D P.total P.s) Q hQ hbox hg.s_pos hg.s_small hg.w_pos hg.kD
    hg.algebraic_pos hg.algebraic_small selected Gamma hsolution
  have hreg:=regular_sum_count D P hDlow hDhigh hS hY hT
    Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno
  have hsing:=RCN292.TightParameters.singularSeeds_count_le_countCap
    (singularProfile D P.total P.s) Q hQ hbox
    hg.s_pos hg.s_small hg.w_pos hg.w_small hg.kD hg.algebraic_pos
    hg.implicit_small hg.algebraic_small hg.mixed_small hg.wa hg.an
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18)) =262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [singularProfile,RCN318.TightParameters.errors,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hreg hsing)
end
end ProximityPrize.SubmissionLower.LocatorFixed
