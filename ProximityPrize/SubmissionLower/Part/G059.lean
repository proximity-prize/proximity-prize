import ProximityPrize.SubmissionLower.Part.G058


section Compact_C2Geometry80788
/-! C2 geometric ingredients retuned to error 80788.
Adapted from the promoted submission. These are not a protocol claim. -/
set_option Elab.async false

section Adapted_LocatorFixedStage
namespace ProximityPrize.SubmissionLower.Lower80788.FixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80788
def agreements:ℕ:=181356
def gap:ℕ:=50285
def prime:ℕ:=2130706433
def weightedCap:ℕ:=17954244
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
    identityCurveDegree flag a b s w=
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
def identitySlackZ (b s:ℕ):ℕ:=
  6202885228582427 +
    11046436110012848 * s +
    6911170502983680 * b +
    3455585251491840 * s ^ 2 +
    6911170502983680 * b * s
def identitySlackYZ (a b s:ℕ):ℕ:=
  2038988338766684 +
    8270504850135686 * s +
    6911170502983680 * b +
    6911170502983680 * a +
    3455585251491840 * s ^ 2 +
    6911170502983680 * b * s +
    6911170502983680 * a * s
def identitySlackAll (a b s:ℕ):ℕ:=
  2718647515841103 +
    8270504850135686 * s +
    8270504850135686 * b +
    11046436110012848 * a +
    3455585251491840 * s ^ 2 +
    6911170502983680 * b * s +
    3455585251491840 * b ^ 2 +
    6911170502983680 * a * s +
    6911170502983680 * a * b
def identitySlack (flag:FlagDegree) (a b s:ℕ):ℕ:=
  flag.zOnly * identitySlackZ b s + flag.yz * identitySlackYZ a b s +
    flag.all * identitySlackAll a b s
theorem identity_budget_exact (flag:FlagDegree) (a b s:ℕ) :
    gap * flagMixed flag (firstTail a b s) (secondTail a b s) =
      (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
        identitySlack flag a b s:=by
  rw [identityDegree_linear]
  norm_num [firstTail,secondTail,tail_support_formula,w,n,errors,gap,
    identitySlack,identitySlackZ,identitySlackYZ,identitySlackAll,flagMixed] <;>
    ring
theorem identity_budget (flag:FlagDegree) (a b s:ℕ) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
theorem tangent_gate (a b s:ℕ) :
    errors + 1 ≤ (secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
    have h:=Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 30) (hY:b + s + 3 ≤ 136) (hT:a + b + s + 3 ≤ 6837)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 30) (hY:b + s + 3 ≤ 136)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 270:=by omega
  have hs:2 * (s + 2) - 1 ≤ 59:=by omega
  have hfS:flag.all ≤ 30:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 136:=hfy.trans hY
  calc
    _ ≤ (1 + w * 270) * 30 + 136 * (59 * w) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _ < prime:=by norm_num [w,prime]
theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 30) (hY:b + s + 3 ≤ 136)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 270:=by omega
  have hs:2 * (s + 2) - 2 ≤ 58:=by omega
  have hfS:flag.all ≤ 30:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 136:=hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 270) * 30 + 136 * (58 * (w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
    _ < prime:=by norm_num [w,prime]
def FixedStageBound (D a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements + errors →
    (∀ gamma ∈ Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (D a b s:ℕ)
    (hDlow:w + 1 ≤ D) (hDhigh:D ≤ weightedCap)
    (hS:s + 2 ≤ 30) (hY:b + s + 3 ≤ 136) (hT:a + b + s + 3 ≤ 6837) :
    FixedStageBound D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D < prime:=hDhigh.trans_lt (by norm_num [weightedCap,prime])
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider:=actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
      apply identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes] <;> norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card * gap=Gamma.card * (agreements - w):=rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            identityCurveDegree flag a b s w:=hinc
        _= (n - w) * (errors + 1) * identityCurveDegree flag a b s w:=by
          rw [hnodes] <;> norm_num [n,agreements,errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          identity_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some
end
end ProximityPrize.SubmissionLower.Lower80788.FixedStage

end Adapted_LocatorFixedStage

section Adapted_LocatorFixed
namespace ProximityPrize.SubmissionLower.Lower80788.Fixed
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
    (hs:p.all ≤ 30) (hy:middle p ≤ 136) (ht:total p ≤ 6837) :
    padSlope p + 2 ≤ 30 ∧ padB p + padSlope p + 3 ≤ 136 ∧
      padA p + padB p + padSlope p + 3 ≤ 6837:=by
  have hp:=pad_sums p
  have hps:padS p ≤ 30:=max_le hs (by decide)
  have hpy:padY p ≤ 136:=max_le hy (by omega)
  have hpt:padT p ≤ 6837:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem regular_factor_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 17954244)
    (hS:P.s ≤ 30) (hY:P.ys ≤ 136) (hT:P.total ≤ 6837)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181356 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80788)
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
  have hparam:s + 2 ≤ 30 ∧ b + s + 3 ≤ 136 ∧ a + b + s + 3 ≤ 6837:=by
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
    have hnodes:S.nodes.card=181356 + 80788:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181356 ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,S0,ResidualStage.agreementFiber,ResidualStage.Agrees,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf:=geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hcount:=Lower80788.FixedStage.fixedStageBound D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
    simpa only [Lower80788.FixedStage.firstTail,Lower80788.FixedStage.secondTail,
      Lower80788.FixedStage.w,Nat.reduceAdd,geometricCumulativeFlag,
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

end
end ProximityPrize.SubmissionLower.Lower80788.Fixed

end Adapted_LocatorFixed

section Adapted_LocatorHybridIdentityC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

open RCN095 RCN146 RCN203 RCN206 LocatorFactorAggregate LocatorHybridCost
open LocatorHybridCostC1 LocatorHybridCostC2 RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! ### Row constants for 6800 -/

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80788
def agreements : ℕ := 181356
def gap : ℕ := 50285

theorem row_arithmetic : n - errors = agreements ∧ agreements - w = gap := by
  refine ⟨?_, ?_⟩ <;> norm_num [n, errors, agreements, w, gap]

/-- Local restatement of `Lower80788.FixedStage.identityDegree_linear`. -/
theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simp only [identityCurveDegree, paddedCut,
    RCN206.centreFlag, RCN206.directionFlag,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all, w]
  ring

/-! ### Subtraction-free C2 tails in the support coordinates `a, b, s` -/

/-- The reduced first tail at `w + 1 = 131072`. -/
def reducedABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 2) * 131072, (2 * s + 2) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩

def hybridCostABSC2 (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (reducedABS a b s) (rationalABS a b s) +
    131076 * flagMixed flag (mfibABS a b s) (mcutABS a b s)

theorem tails_eqC2 (p : FlagDegree) :
    reducedTail p = reducedABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    hybridCoordinateC1 p =
      rationalABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingFiber p = mfibABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingCut p = mcutABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := pad_bounds p
  generalize hS : padS p = sP at h ⊢
  generalize hY : padY p = yP at h ⊢
  generalize hT : padT p = tP at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : 2 * (yP - sP) = 2 * (yP - sP - 1) + 2 := by omega
    have e2 : 2 * (sP - 1) = 2 * (sP - 2) + 2 := by omega
    simp only [reducedTail, paddedTail, reducedABS, hS, hY, hT, e1, e2]
  · simp only [hybridCoordinateC1, rationalFlag, rationalABS, hS, hY, hT]
  · have e1 : yP - sP = yP - sP - 1 + 1 := by omega
    have e2 : sP + 1 = sP - 2 + 3 := by omega
    simp only [movingFiber, mfibABS, hS, hY, hT, FlagDegree.mk.injEq]
    exact ⟨trivial, e1, e2⟩
  · simp only [movingCut, rationalFlag, mcutABS, rationalABS, hS, hY, hT]

theorem hybridCostC2_eq_abs (p : FlagDegree) (flag : FlagDegree) :
    flagMixed flag (reducedTail p) (hybridCoordinateC1 p) +
        131076 * flagMixed flag (movingFiber p) (movingCut p) =
      hybridCostABSC2 flag (padT p - padY p) (padY p - padS p - 1)
        (padS p - 2) := by
  have h := tails_eqC2 p
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  rfl

/-! ### Slack polynomials for `errors = 80788` (regenerated for the C2 cost) -/

def hybridSlackZC2 (b s : ℕ) : ℕ :=
  11386889252075652 +
    11910721292680868 * s +
    6047485102497620 * b +
    2591735075709800 * s ^ 2 +
    5183470151419600 * b * s

def hybridSlackYZC2 (a b s : ℕ) : ℕ :=
  7222992362259909 +
    9134790032803706 * s +
    6047485102497620 * b +
    6047485102497620 * a +
    2591735075709800 * s ^ 2 +
    5183470151419600 * b * s +
    5183470151419600 * a * s

def hybridSlackAllC2 (a b s : ℕ) : ℕ :=
  5806565410441329 +
    9134790032803706 * s +
    9134790032803706 * b +
    11910721292680868 * a +
    2591735075709800 * s ^ 2 +
    5183470151419600 * b * s +
    2591735075709800 * b ^ 2 +
    5183470151419600 * a * s +
    5183470151419600 * a * b

def hybridSlackC2 (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * hybridSlackZC2 b s + flag.yz * hybridSlackYZC2 a b s +
    flag.all * hybridSlackAllC2 a b s

theorem hybrid_identity_exactC2 (flag : FlagDegree) (a b s : ℕ) :
    gap * hybridCostABSC2 flag a (b + 1) s =
      (n - w) * (errors + 1) * identityCurveDegree flag a (b + 1) s w +
        hybridSlackC2 flag a b s := by
  rw [identityDegree_linear]
  norm_num [hybridCostABSC2, reducedABS, rationalABS, mfibABS, mcutABS,
    w, n, errors, gap, hybridSlackC2, hybridSlackZC2, hybridSlackYZC2,
    hybridSlackAllC2, flagMixed, add_zOnly, add_yz, add_all]
  ring

theorem identity_le_hybridC2 (flag : FlagDegree) (a b s : ℕ) (hb : 1 ≤ b) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * hybridCostABSC2 flag a b s := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [hybrid_identity_exactC2]
  exact Nat.le_add_right _ _

end ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

end Adapted_LocatorHybridIdentityC2

section Adapted_LocatorHybridGatesC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2
open RCN095 LocatorHybridCells LocatorHybridCellsC1

/-- Provider gate for the REDUCED first tail (`2 * (s + 2) - 2`). -/
theorem reduced_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 30) (hY : b + s + 3 ≤ 136)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 270 := by omega
  have hs : 2 * (s + 2) - 2 ≤ 58 := by omega
  have hfS : flag.all ≤ 30 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 136 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 270) * 30 + 136 * (58 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

/-- Provider gate for the SHARP first tail, kept for the C1 comparison. -/
theorem sharp_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 30) (hY : b + s + 3 ≤ 136)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 270 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 59 := by omega
  have hfS : flag.all ≤ 30 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 136 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 270) * 30 + 136 * (59 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

theorem product_gateC2 (a b s : ℕ) (flag : FlagDegree)
    (hT : a + b + s + 3 ≤ 6837)
    (hft : flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < 2130706433 := by
  have h1 : flag.zOnly + flag.yz + flag.all ≤ 6837 := hft.trans hT
  have h2 : a + b + s + 4 ≤ 6838 := by omega
  calc
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) ≤ 2 * 6837 * 6838 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433 := by norm_num

/-- The single coordinate gate at `errors = 80788`. -/
theorem rational_gateC2 (t y r : ℕ) (hb : r + 2 ≤ y) :
    80788 + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  hybridC1Gate_of_le t y r 80788 hb (by norm_num)

theorem flag_characteristicC2 (a b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 30) (hY : b + s + 3 ≤ 136) (hT : a + b + s + 3 ≤ 6837)
    (hflag : flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
  omega

/-- `Lower80788.FixedStage.identity_mixed_gate` at the 6800 caps (uses `w`, not `w+1`). -/
theorem identity_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 30) (hY : b + s + 3 ≤ 136)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + RCN327.w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * RCN327.w) < 2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 270 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 59 := by omega
  have hfS : flag.all ≤ 30 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 136 := hfy.trans hY
  calc
    _ ≤ (1 + RCN327.w * 270) * 30 + 136 * (59 * RCN327.w) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left RCN327.w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right RCN327.w hs))
    _ < 2130706433 := by norm_num [RCN327.w]

end ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2

end Adapted_LocatorHybridGatesC2

section Adapted_LocatorFixedHybridC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open Lower80788.HybridIdentityC2 LocatorHybridCells LocatorHybridCellsC1
open LocatorHybridTailProvider LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
open Lower80788.HybridGatesC2 Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem flagDegree_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  rfl

theorem cellSupport_eq (p : FlagDegree) :
    cellSupport (padT p) (padY p) (padS p) =
      RCN198.support (padA p) (padB p) (padSlope p) := rfl

theorem cellSupport_fields (p : FlagDegree) :
    (cellSupport (padT p) (padY p) (padS p)).s = padS p ∧
    (cellSupport (padT p) (padY p) (padS p)).ys = padY p ∧
    (cellSupport (padT p) (padY p) (padS p)).total = padT p := by
  have h := pad_sums p
  simp only [cellSupport_eq, RCN198.support]
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem cell_tails_eqC2 (p : FlagDegree) :
    cellFirstTail (padT p) (padY p) (padS p) = reducedTail p ∧
    cellHybridCoordinateC1 (padT p) (padY p) (padS p) = hybridCoordinateC1 p ∧
    cellMovingFiber (padT p) (padY p) (padS p) = movingFiber p ∧
    cellMovingCut (padT p) (padY p) (padS p) = movingCut p := by
  have hf := cellSupport_fields p
  have hb := pad_bounds p
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply flagDegree_ext <;>
      simp only [cellFirstTail, reducedResidualAgreementFlag,
        reducedAgreementDirection, hf.1, hf.2.1, hf.2.2, reducedTail,
        paddedTail, RCN327.w, Nat.reduceAdd] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellHybridCoordinateC1, cellRational, cellDirection,
        RCN206.directionFlag, cellA, cellB, cellS, hybridCoordinateC1,
        rationalFlag, RCN327.w, Nat.reduceAdd, Nat.reduceMul] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingFiber, RCN206.fiberFlag, cellA, cellB, cellS,
        movingFiber] <;> omega
  · apply flagDegree_ext <;>
      simp only [cellMovingCut, cellRational, cellDirection,
        RCN206.directionFlag, cellA, cellB, cellS, movingCut, rationalFlag,
        add_zOnly, add_yz, add_all, RCN327.w, Nat.reduceAdd,
        Nat.reduceMul] <;> omega

/-- The C2 hybrid Bezout bound of a stage with flag `flag` on the padded cell. -/
def hybridBoundC2 (flag p : FlagDegree) : ℕ :=
  flagMixed flag (reducedTail p) (hybridCoordinateC1 p) +
    131076 * flagMixed flag (movingFiber p) (movingCut p)

theorem hybridBoundC2_eq_abs (flag p : FlagDegree) :
    hybridBoundC2 flag p =
      hybridCostABSC2 flag (padA p) (padB p) (padSlope p) :=
  hybridCostC2_eq_abs p flag

/-- The proper-first-tail obligation: a C2 hybrid provider on the cell of `p`. -/
def ProviderHypC2 (D : ℕ) (p : FlagDegree) : Prop :=
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  ∀ {Gamma : Finset K} {flag : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80788 flag 131071 (cellSupport (padT p) (padY p) (padS p))),
    S.nodes.card = 181356 + 80788 →
    (∀ gamma ∈ Gamma, 181356 ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p) →
    (flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) →
    ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1) →
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellFirstTail (padT p) (padY p) (padS p))
      (tailFlag2 := cellHybridCoordinateC1 (padT p) (padY p) (padS p)) S
      (flagMixed flag (cellFirstTail (padT p) (padY p) (padS p))
          (cellHybridCoordinateC1 (padT p) (padY p) (padS p)) +
        (RCN327.w + 5) *
          flagMixed flag (cellMovingFiber (padT p) (padY p) (padS p))
            (cellMovingCut (padT p) (padY p) (padS p))))

/-- The realization: C2 providers exist on every admissible hybrid cell.  Note
the extra `3 ≤ padS p`, the C2 branch condition. -/
def RealizationC2 (D : ℕ) : Prop :=
  ∀ p : FlagDegree, padS p ≤ 30 → padY p ≤ 136 → padT p ≤ 6837 →
    3 ≤ padS p → padS p + 2 ≤ padY p → ProviderHypC2 D p

theorem hybridStageBoundC2 (D : ℕ) (p : FlagDegree)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 17954244)
    (hS : padS p ≤ 30) (hY : padY p ≤ 136) (hT : padT p ≤ 6837)
    (hS3 : 3 ≤ padS p) (hhyb : padS p + 2 ≤ padY p)
    (hprov : ProviderHypC2 D p)
    {Gamma : Finset K} {flag : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      2130706433 80788 flag 131071 (cellSupport (padT p) (padY p) (padS p)))
    (hnodes : S.nodes.card = 181356 + 80788)
    (hagreement : ∀ gamma ∈ Gamma, 181356 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p))
    (hflag : flag.all ≤ padS p ∧ flag.yz + flag.all ≤ padY p ∧
      flag.zOnly + flag.yz + flag.all ≤ padT p) :
    Gamma.card ≤ hybridBoundC2 flag p := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  have hps := pad_sums p
  have hS' : padSlope p + 2 ≤ 30 := by omega
  have hY' : padB p + padSlope p + 3 ≤ 136 := by omega
  have hT' : padA p + padB p + padSlope p + 3 ≤ 6837 := by omega
  have hb1 : 1 ≤ padB p := by omega
  have hDchar : D < 2130706433 := by omega
  have hflag' : flag.all ≤ padSlope p + 2 ∧
      flag.yz + flag.all ≤ padB p + padSlope p + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ padA p + padB p + padSlope p + 3 := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hflagChar := flag_characteristicC2 (padA p) (padB p) (padSlope p)
    flag hS' hY' hT' hflag'
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (RCN327.w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (RCN327.w + 1) S.G).mp hTail
    have hbox' : S.F ∈ RCN174.globalCoefficientBox K D 131071
        (padA p + padB p + padSlope p + 3) (padSlope p + 2) := by
      rw [hps.2.2, hps.1]; exact hbox
    have hprovider := actual_identityCurveCountProvider
      (a := padA p) (b := padB p) (s := padSlope p) S 181356 hnodes hagreement
      (by norm_num) hTailNumerator D (padA p + padB p + padSlope p + 3)
      (padSlope p + 2)
      (by norm_num) hDlow hDchar hbox' hflagChar
      (identity_mixed_gateC2 (padB p) (padSlope p) flag hS' hY'
        hflag'.1 hflag'.2.1)
    have hpositive : 1 ≤ identityCurveDegree flag (padA p) (padB p)
        (padSlope p) 131071 := by
      apply Lower80788.FixedStage.identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181356
      (identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071)
      hprovider hagreement
      (by norm_num) (by rw [hnodes]; norm_num) hpositive
    have hscaled : Gamma.card * 50285 ≤
        50285 * hybridCostABSC2 flag (padA p) (padB p) (padSlope p) := by
      calc
        Gamma.card * 50285 = Gamma.card * (181356 - 131071) := rfl
        _ ≤ (S.nodes.card - 131071) * (80788 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071 :=
          hinc
        _ = (262144 - 131071) * (80788 + 1) *
            identityCurveDegree flag (padA p) (padB p) (padSlope p) 131071 := by
          rw [hnodes]
        _ ≤ 50285 * hybridCostABSC2 flag (padA p) (padB p) (padSlope p) :=
          identity_le_hybridC2 flag (padA p) (padB p) (padSlope p) hb1
    rw [hybridBoundC2_eq_abs]
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num : 0 < 50285)
    simpa only [Nat.mul_comm] using hscaled
  · obtain ⟨P⟩ := hprov S hnodes hagreement hbox hflag hTail
    have h := stage_card_le_divisorBound S P
    have hct := cell_tails_eqC2 p
    rw [hct.1, hct.2.1, hct.2.2.1, hct.2.2.2] at h
    simpa only [hybridBoundC2, RCN327.w, Nat.reduceAdd] using h

theorem regular_factor_count_hybridC2
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 17954244)
    (hS : P.s ≤ 30) (hY : P.ys ≤ 136) (hT : P.total ≤ 6837)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181356 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80788)
    (R : RegularIndex Q)
    (hhyb : HybridAppliesC2 (regularCumulativeFlag Q R))
    (hreal : RealizationC2 D) :
    (regularSeeds Q selected Gamma R).card ≤
      hybridCostC2 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  set p := regularCumulativeFlag Q R with hp
  have hRdata := directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
    (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox0 : R.1 ∈ RCN174.globalCoefficientBox K D 131071
      (padA p + padB p + padSlope p + 3) (padSlope p + 2) :=
    own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport : ResidualSupportData
      (RCN198.support (padA p) (padB p) (padSlope p)) R.1 :=
    own_support R.1
  have hRwhole := factor_support Q hQ HQ R
  have hc := originalCumulativeFlag_cumulative R.1
  have hps := pad_sums p
  have hRbox : R.1 ∈ RCN174.globalCoefficientBox K D 131071 (padT p) (padS p) := by
    rw [← hps.2.2, ← hps.1]; exact hRbox0
  have h1 : p.all ≤ 30 := hRwhole.s_weight.trans hS
  have h2 : middle p ≤ 136 := by
    simpa only [hp, middle, regularCumulativeFlag, hc.2.1] using
      hRwhole.ys_weight.trans hY
  have h3 : total p ≤ 6837 := by
    simpa only [hp, total, regularCumulativeFlag, hc.2.2] using
      hRwhole.total_weight.trans hT
  have hpS : padS p ≤ 30 := max_le h1 (by decide)
  have hpY : padY p ≤ 136 := max_le h2 (by omega)
  have hpT : padT p ≤ 6837 := max_le h3 (by omega)
  have hp3 : 3 ≤ p.all := hhyb.1
  have hpSeq : padS p = p.all := max_eq_left (by omega : 2 ≤ p.all)
  have hpYeq : padY p = middle p :=
    max_eq_left (by rw [hpSeq]; exact hhyb.2.trans' (by omega))
  have hpS3 : 3 ≤ padS p := by rw [hpSeq]; exact hhyb.1
  have hhyb' : padS p + 2 ≤ padY p := by rw [hpSeq, hpYeq]; exact hhyb.2
  have hprov : ProviderHypC2 D p := hreal p hpS hpY hpT hpS3 hhyb'
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g : GeometricFactor K R.1) :
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        hybridBoundC2 (geometricCumulativeFlag K g) p := by
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
    have hnodes : S.nodes.card = 181356 + 80788 := by
      change (Finset.univ : Finset I).card = _
      norm_num [I, IRSProfile.Index]
    have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        181356 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
    have hf1 : (geometricCumulativeFlag K g).all ≤ padSlope p + 2 := hf.1
    have hf2 : (geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all ≤ padB p + padSlope p + 3 := hf.2.1
    have hf3 : (geometricCumulativeFlag K g).zOnly +
        (geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all ≤
          padA p + padB p + padSlope p + 3 := hf.2.2
    have hf' : (geometricCumulativeFlag K g).all ≤ padS p ∧
        (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤
          padY p ∧
        (geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
          (geometricCumulativeFlag K g).all ≤ padT p := by
      refine ⟨?_, ?_, ?_⟩ <;> omega
    have hcount := hybridStageBoundC2 D p hDlow hDhigh hpS hpY hpT hpS3 hhyb'
      hprov (S := S) hnodes hag hRbox hf'
    simpa only [geometricCumulativeFlag] using hcount
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card :=
      hcover
    _ ≤ ∑ g : GeometricFactor K R.1,
        hybridBoundC2 (geometricCumulativeFlag K g) p :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ hybridCostC2 p := by
      have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact merge_hybrid_costsC2 (geometricCumulativeFlag K) p hb.1 hb.2.1 hb.2.2

end
end ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2

end Adapted_LocatorFixedHybridC2

section Adapted_LocatorHybridRealizeC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
open LocatorHybridTailRealizationC2 Lower80788.HybridGatesC2
open Lower80788.Fixed Lower80788.FixedHybridC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem realizationC2 : RealizationC2 17954244 := by
  intro p hS hY hT hS3 hhyb
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  unfold ProviderHypC2
  intro Gamma flag S hnodes hagreement hbox hflag hTail
  have hps := pad_sums p
  have hpb := pad_bounds p
  have hyt : padY p ≤ padT p := hpb.2.2
  have hflagChar : flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hmixedRed := reduced_mixed_gateC2 (padB p) (padSlope p) flag
    (by omega) (by omega) (by omega) (by omega)
  have hmix := product_gateC2 (padA p) (padB p) (padSlope p) flag
    (by omega) (by omega)
  have hrat := rational_gateC2 (padT p) (padY p) (padS p) hhyb
  have htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (RCN327.w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80788 + 1) *
            (reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
    intro C hall
    exact tangent_component_card_le S C hTail
      (reducedBaseOrd S hTail hflagChar hmixedRed C)
      181356 17954244 (padT p) (padS p) hnodes hagreement
      (by norm_num [RCN327.w]) (by norm_num [RCN327.w])
      (by norm_num [RCN327.w]) (by norm_num)
      hbox (reducedBudgetFamily S hTail hflagChar hmixedRed)
      (reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C) hall
      (reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
  exact exists_hybridTailMultiplicityProviderC2_realized hS3 hhyb hyt S hTail
    hflagChar hmixedRed hmix hrat htangent

end
end ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2

end Adapted_LocatorHybridRealizeC2

section Adapted_LocatorFixedOwnBoundC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open LocatorFactorAggregate LocatorHybridCostC2 Lower80788.Fixed Lower80788.FixedHybridC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

/-- Both per-factor bounds: padded always, C2 hybrid when it applies. -/
theorem regular_factor_own_bound
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 17954244)
    (hS:P.s ≤ 30) (hY:P.ys ≤ 136) (hT:P.total ≤ 6837)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181356 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80788)
    (R:RegularIndex Q) (hreal:RealizationC2 D) :
    OwnBoundC2 (regularSeeds Q selected Gamma R).card (regularCumulativeFlag Q R):=
  ⟨regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R,
    fun hhyb=> regular_factor_count_hybridC2 D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb hreal⟩
end
end ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2

end Adapted_LocatorFixedOwnBoundC2

end Compact_C2Geometry80788
