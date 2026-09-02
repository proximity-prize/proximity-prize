import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorHybridIdentity
import ProximityPrize.SubmissionLower.LocatorHybridTailProvider

/-!
# Hybrid second-surface bound for a regular factor

When the padded cumulative flag `p` of a regular factor satisfies
`2 ≤ p.all ∧ p.all + 2 ≤ middle p`, the factor's seeds are bounded by
`hybridCost p` instead of the padded two-tail cost.  The identity branch is
dominated through `identity_le_hybrid`; the proper-first-tail branch uses a
`HybridTailMultiplicityProvider` on the cell `(padT p, padY p, padS p)`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedHybrid
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open LocatorFactorAggregate LocatorHybridCost LocatorHybridIdentity LocatorHybridCells
  LocatorHybridTailProvider LocatorFixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem flagDegree_ext {f g:FlagDegree} (h1:f.zOnly=g.zOnly) (h2:f.yz=g.yz)
    (h3:f.all=g.all) : f=g:=by
  cases f; cases g
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  rfl

theorem cellSupport_eq (p:FlagDegree) :
    cellSupport (padT p) (padY p) (padS p)=
      RCN198.support (padA p) (padB p) (padSlope p):=rfl

theorem cellSupport_fields (p:FlagDegree) :
    (cellSupport (padT p) (padY p) (padS p)).s=padS p ∧
    (cellSupport (padT p) (padY p) (padS p)).ys=padY p ∧
    (cellSupport (padT p) (padY p) (padS p)).total=padT p:=by
  have h:=pad_sums p
  simp only [cellSupport_eq,RCN198.support]
  exact ⟨h.1,h.2.1,h.2.2⟩

theorem cell_tails_eq (p:FlagDegree) :
    cellSharpTail (padT p) (padY p) (padS p)=sharpTail p ∧
    cellHybridCoordinate (padT p) (padY p) (padS p)=hybridCoordinate p ∧
    cellMovingFiber (padT p) (padY p) (padS p)=movingFiber p ∧
    cellMovingCut (padT p) (padY p) (padS p)=movingCut p:=by
  have hf:=cellSupport_fields p
  have hb:=pad_bounds p
  refine ⟨?_,?_,?_,?_⟩
  · apply flagDegree_ext <;>
      simp only [cellSharpTail,sharpResidualAgreementFlag,sharpAgreementDirection,
        hf.1,hf.2.1,hf.2.2,sharpTail,RCN327.w,Nat.reduceAdd]
  · apply flagDegree_ext <;>
      simp only [cellHybridCoordinate,cellRational,cellDirection,RCN206.directionFlag,
        cellA,cellB,cellS,hybridCoordinate,rationalFlag,add_zOnly,add_yz,add_all,
        RCN327.w,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingFiber,RCN206.fiberFlag,cellA,cellB,cellS,movingFiber] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingCut,cellRational,cellDirection,RCN206.directionFlag,
        cellA,cellB,cellS,movingCut,rationalFlag,add_zOnly,add_yz,add_all,
        RCN327.w,Nat.reduceAdd,Nat.reduceMul] <;> omega

/-- The hybrid Bezout bound of a stage with flag `flag` on the padded cell of `p`. -/
def hybridBound (flag p:FlagDegree):ℕ:=
  flagMixed flag (sharpTail p) (hybridCoordinate p) +
    131072 * flagMixed flag (movingFiber p) (movingCut p)

theorem hybridBound_eq_abs (flag p:FlagDegree) :
    hybridBound flag p=hybridCostABS flag (padA p) (padB p) (padSlope p):=
  hybridCost_eq_abs p flag

/-- The proper-first-tail obligation: a hybrid provider on the cell of `p`. -/
def ProviderHyp (D:ℕ) (p:FlagDegree):Prop:=
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  ∀ {Gamma:Finset K} {flag:FlagDegree}
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80565 flag 131071 (cellSupport (padT p) (padY p) (padS p))),
    S.nodes.card=181579 + 80565 →
    (∀ gamma ∈ Gamma,181579 ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p) →
    (flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) →
    ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1) →
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1:=cellSharpTail (padT p) (padY p) (padS p))
      (tailFlag2:=cellHybridCoordinate (padT p) (padY p) (padS p)) S
      (flagMixed flag (cellSharpTail (padT p) (padY p) (padS p))
          (cellHybridCoordinate (padT p) (padY p) (padS p)) +
        (RCN327.w + 1) * flagMixed flag (cellMovingFiber (padT p) (padY p) (padS p))
          (cellMovingCut (padT p) (padY p) (padS p))))

/-- The realization: providers exist on every admissible hybrid cell. -/
def Realization (D:ℕ):Prop:=
  ∀ p:FlagDegree,padS p ≤ 20 → padY p ≤ 92 → padT p ≤ 3319 → padS p + 2 ≤ padY p →
    ProviderHyp D p

theorem hybridStageBound (D:ℕ) (p:FlagDegree)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hS:padS p ≤ 20) (hY:padY p ≤ 92) (hT:padT p ≤ 3319)
    (hhyb:padS p + 2 ≤ padY p)
    (hprov:ProviderHyp D p)
    {Gamma:Finset K} {flag:FlagDegree}
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80565 flag 131071 (cellSupport (padT p) (padY p) (padS p)))
    (hnodes:S.nodes.card=181579 + 80565)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤ (S.agreementFiber gamma).card)
    (hbox:S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p))
    (hflag:flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) :
    Gamma.card ≤ hybridBound flag p:=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  have hps:=pad_sums p
  have hS':padSlope p + 2 ≤ 20:=by omega
  have hY':padB p + padSlope p + 3 ≤ 92:=by omega
  have hT':padA p + padB p + padSlope p + 3 ≤ 3319:=by omega
  have hb1:1 ≤ padB p:=by omega
  have hDchar:D < 2130706433:=by omega
  have hflag':flag.all ≤ padSlope p + 2 ∧
      flag.yz + flag.all ≤ padB p + padSlope p + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ padA p + padB p + padSlope p + 3:=by
    refine ⟨?_,?_,?_⟩ <;> omega
  have hflagChar:=LocatorFixedStage.flag_characteristic (padA p) (padB p) (padSlope p)
    flag hS' hY' hT' hflag'
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (RCN327.w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (RCN327.w + 1) S.G).mp hTail
    have hbox':S.F ∈ RCN174.globalCoefficientBox K D 131071
        (padA p + padB p + padSlope p + 3) (padSlope p + 2):=by
      rw [hps.2.2,hps.1]; exact hbox
    have hprovider:=actual_identityCurveCountProvider
      (a:=padA p) (b:=padB p) (s:=padSlope p) S 181579 hnodes hagreement
      (by norm_num) hTailNumerator D (padA p + padB p + padSlope p + 3) (padSlope p + 2)
      (by norm_num) hDlow hDchar hbox' hflagChar
      (LocatorFixedStage.identity_mixed_gate (padB p) (padSlope p) flag hS' hY'
        hflag'.1 hflag'.2.1)
    have hpositive:1 ≤ identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=by
      apply LocatorFixedStage.identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S 181579
      (identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071) hprovider hagreement
      (by norm_num) (by rw [hnodes]; norm_num) hpositive
    have hscaled:Gamma.card * 50508 ≤
        50508 * hybridCostABS flag (padA p) (padB p) (padSlope p):=by
      calc
        Gamma.card * 50508=Gamma.card * (181579 - 131071):=rfl
        _ ≤ (S.nodes.card - 131071) * (80565 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=hinc
        _= (262144 - 131071) * (80565 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071:=by
          rw [hnodes]
        _ ≤ 50508 * hybridCostABS flag (padA p) (padB p) (padSlope p):=
          identity_le_hybrid flag (padA p) (padB p) (padSlope p) hb1
    rw [hybridBound_eq_abs]
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num:0 < 50508)
    simpa only [Nat.mul_comm] using hscaled
  · obtain ⟨P⟩:=hprov S hnodes hagreement hbox hflag hTail
    have h:=stage_card_le_divisorBound S P
    have hct:=cell_tails_eq p
    rw [hct.1,hct.2.1,hct.2.2.1,hct.2.2.2] at h
    simpa only [hybridBound,RCN327.w,Nat.reduceAdd] using h

theorem regular_factor_count_hybrid
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 12347372)
    (hS:P.s ≤ 20) (hY:P.ys ≤ 92) (hT:P.total ≤ 3319)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565)
    (R:RegularIndex Q)
    (hhyb:HybridApplies (regularCumulativeFlag Q R))
    (hreal:Realization D) :
    (regularSeeds Q selected Gamma R).card ≤ hybridCost (regularCumulativeFlag Q R):=by
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  set p:=regularCumulativeFlag Q R with hp
  have hRdata:=directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < 2130706433:=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox0:R.1 ∈ RCN174.globalCoefficientBox K D 131071
      (padA p + padB p + padSlope p + 3) (padSlope p + 2):=
    own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:ResidualSupportData (RCN198.support (padA p) (padB p) (padSlope p)) R.1:=
    own_support R.1
  have hRwhole:=factor_support Q hQ HQ R
  have hc:=originalCumulativeFlag_cumulative R.1
  have hps:=pad_sums p
  have hRbox:R.1 ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p):=by
    rw [← hps.2.2,← hps.1]; exact hRbox0
  have h1:p.all ≤ 20:=hRwhole.s_weight.trans hS
  have h2:middle p ≤ 92:=by
    simpa only [hp,middle,regularCumulativeFlag,hc.2.1] using hRwhole.ys_weight.trans hY
  have h3:total p ≤ 3319:=by
    simpa only [hp,total,regularCumulativeFlag,hc.2.2] using hRwhole.total_weight.trans hT
  have hpS:padS p ≤ 20:=max_le h1 (by decide)
  have hpY:padY p ≤ 92:=max_le h2 (by omega)
  have hpT:padT p ≤ 3319:=max_le h3 (by omega)
  have hpSeq:padS p=p.all:=max_eq_left hhyb.1
  have hpYeq:padY p=middle p:=max_eq_left (by rw [hpSeq]; exact hhyb.2.trans' (by omega))
  have hhyb':padS p + 2 ≤ padY p:=by rw [hpSeq,hpYeq]; exact hhyb.2
  have hprov:ProviderHyp D p:=hreal p hpS hpY hpT hhyb'
  have hsolutions:∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        hybridBound (geometricCumulativeFlag K g) p:=by
    let S0:=regularGeometricResidualStageOfSupport
      (RCN198.support (padA p) (padB p) (padSlope p)) Q selected Gamma
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
    have hf1:(geometricCumulativeFlag K g).all ≤ padSlope p + 2:=hf.1
    have hf2:(geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤
        padB p + padSlope p + 3:=hf.2.1
    have hf3:(geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all ≤ padA p + padB p + padSlope p + 3:=hf.2.2
    have hf':(geometricCumulativeFlag K g).all ≤ padS p ∧
        (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤ padY p ∧
        (geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
          (geometricCumulativeFlag K g).all ≤ padT p:=by
      refine ⟨?_,?_,?_⟩ <;> omega
    have hcount:=hybridStageBound D p hDlow hDhigh hpS hpY hpT hhyb' hprov
      (S:=S) hnodes hag hRbox hf'
    simpa only [geometricCumulativeFlag] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        hybridBound (geometricCumulativeFlag K g) p:=Finset.sum_le_sum (fun g _=> hstage g)
    _ ≤ hybridCost p:=by
      have hb:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact merge_hybrid_costs (geometricCumulativeFlag K) p hb.1 hb.2.1 hb.2.2

end
end ProximityPrize.SubmissionLower.LocatorFixedHybrid
