import ProximityPrize.SubmissionLower.LocatorReplacementReceiptB6765

section Bundled510
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem receipt (c:Cell):Receipt c:=by
  rcases c with ⟨ri,y,b⟩
  fin_cases ri
  · exact receipt_r01_full y b
  · exact receipt_r02_full y b
  · exact receipt_r03_full y b
  · exact receipt_r04_full y b
  · exact receipt_r05_full y b
  · exact receipt_r06_full y b
  · exact receipt_r07_full y b
  · exact receipt_r08_full y b
  · exact receipt_r09_full y b
  · exact receipt_r10_full y b
  · exact receipt_r11_full y b
  · exact receipt_r12_full y b
  · exact receipt_r13_full y b
  · exact receipt_r14_full y b
  · exact receipt_r15_full y b
  · exact receipt_r16_full y b
  · exact receipt_r17_full y b

theorem chosenCost_with_rest (c:Cell) (hv:Valid c) (hnr:¬noBadFits c):
    chosenCost c+exactRest c≤271826427410824381:=by
  have routes:ordinaryFits c∨sourceFits c∨sourceFits126 c∨sourceFitsX c:=
    (receipt c hv).resolve_left hnr
  by_cases ho:ordinaryFits c
  · rw [chosenCost,if_pos ho]
    exact ho
  · have hsources:=routes.resolve_left ho
    by_cases h93:sourceFits c
    · rw [chosenCost,if_neg ho,if_pos h93]
      exact h93.2.2.2.2.2.2.2.2
    · rw [chosenCost,if_neg ho,if_neg h93]
      rcases hsources.resolve_left h93 with h126|hX
      · exact h126.2.2.2.2.2.2.2.2
      · exact hX.2.2.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt
end Bundled510

section Bundled511
namespace ProximityPrize.SubmissionLower.LocatorResidual
open scoped Classical
open LocatorArithmetic RCN174 RCN319 RCN260 RCN318 RCN238 RCN243 RCN052 RCN303 RCN259 RCN180 RCN156 RCN234
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
structure Gates:Prop where
  kD:w < residualSingular.kappa * residualSingular.D
  algebraic_pos:1 ≤ residualSingular.algebraicCap
  implicit_small:residualSingular.implicitYCap < 2130706433
  algebraic_small:residualSingular.algebraicCap < 2130706433
  mixed_small:2 * residualSingular.implicitYCap *
    residualSingular.algebraicCap < 2130706433
  qY:(residualSingular.D - 1) / w ≤ residualStage.leftY
  leftZ_small:residualStage.leftZ < 2130706433
  mixedY_small:residualStage.mixedCost.y < 2130706433
  mixedR_small:residualStage.mixedCost.r < 2130706433
  mixedZ_small:residualStage.mixedCost.z < 2130706433
theorem gates:Gates:=by
  exact ⟨residual_singular_gates.kD,
    residual_singular_gates.algebraic_pos,
    residual_singular_gates.implicit_small,
    residual_singular_gates.algebraic_small,
    residual_singular_gates.mixed_small,
    residual_gates.qY,residual_gates.leftZ_small,
    residual_gates.mixedY_small,residual_gates.mixedR_small,
    residual_gates.mixedZ_small⟩
theorem residual_count_lt
    (valid:Gates)
    (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0) (hrel:IsRelPrime Q T)
    (hbox:Q ∈ globalCoefficientBox K weightedB w LB 28)
    (hTcaps:T.degreeOf 1 ≤ 174 ∧ T.degreeOf 2 ≤ 39 ∧ T.degreeOf 3 ≤ LA)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma Q=0)
    (hTsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma T=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < residualStage.regularCountCap +
      residualSingular.countCap + 1:=by
  classical
  apply asymmetric_stage_count_lt_of_regular_factors
    residualStage residualSingular Q T hQ 2130706433
    (by change 1 ≤ 28; decide) (by change 28 < 2130706433; decide)
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide) valid.kD
    valid.algebraic_pos valid.implicit_small valid.algebraic_small valid.mixed_small
    (by change 131071 < 181707; decide) (by change 181707 ≤ 262144; decide)
    hbox (by norm_num only [residualStage,UnequalParameters.gap,agreements,w])
    (by simp only [residualSingular,residualStage,TightParameters.gap,
      UnequalParameters.gap])
    valid.qY (by change 28 ≤ 28; decide) (by exact Nat.le_refl _)
    selected seeds nodes x u0 u1 hinj hnodes hdegree hQsolution hTsolution hagreement
    (by simpa only [residualSingular,TightParameters.errors] using hno)
  exact all_regularPairSeeds_bound residualStage Q T hQ hrel
    weightedB w LB 28 2130706433 hbox (by decide)
    valid.qY (by change 28 ≤ 28; decide) (by exact Nat.le_refl _)
    hTcaps.1 hTcaps.2.1 hTcaps.2.2 (by change 1 ≤ 28; decide)
    (by change 127 < 2130706433; decide) (by change 28 < 2130706433; decide)
    valid.leftZ_small valid.mixedY_small valid.mixedR_small valid.mixedZ_small
    selected seeds nodes x u0 u1 hinj hnodes
    (by change 1 ≤ 131071; decide) (by change 131071 < 2130706433; decide)
    (by change 131071 < 181707; decide) (by change 181707 ≤ 262144; decide)
    hdegree hagreement
    (by simpa only [residualStage,UnequalParameters.errors] using hno)
theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedC w LA 39)
    (hboxB:QB ∈ RCN100.globalCoefficientBox K weightedB w LB 28)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hA:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QA=0)
    (hB:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QB=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    (LocatorCover.residual
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      seeds QA QB).card < residualStage.regularCountCap +
        residualSingular.countCap + 1:=by
  classical
  let phi:=fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:=LocatorCover.residual phi seeds QA QB
  let H:=gcd12 QA QB
  let Q:=quotientB QA QB
  let T:=quotientA QA QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left hQA
  have hQeq:QB=H * Q:=b_eq_gcd12_mul_quotientB QA QB
  have hTeq:QA=H * T:=a_eq_gcd12_mul_quotientA QA QB
  have hQ:Q ≠ 0:=by
    intro hz
    exact hQB (by rw [hQeq,hz,mul_zero])
  have hT:T ≠ 0:=by
    intro hz
    exact hQA (by rw [hTeq,hz,mul_zero])
  have hQflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QB H Q weightedB w LB 28 0 0 0 hQB hH hQ hboxB hQeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hTflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T weightedC w LA 39 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB 28:=
    RCN101.flag_box_to_ordinary K
      weightedB w LB 28 Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox:T ∈ globalCoefficientBox K weightedC w LA 39:=
    RCN101.flag_box_to_ordinary K
      weightedC w LA 39 T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedC w LA 39 (by decide) hTbox
  rw [show (weightedC - 1) / w=174 by decide] at hTcaps
  have hsub:Delta ⊆ seeds:=by
    intro gamma hg
    have hm:gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0:=by
      simpa only [Delta,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma:K) (hg:gamma ∈ Delta) :
      specialization K (selected gamma) gamma T=0 ∧
      specialization K (selected gamma) gamma Q=0:=
    LocatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  exact residual_count_lt gates Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
end
end ProximityPrize.SubmissionLower.LocatorResidual
end Bundled511

section Bundled512
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
theorem kernelAmbient_nullity:
    coefficientCount 22895082 131071 52091 39 -
      262144 * localRankBound 126 52091 39=18013574373850:=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
end Bundled512

section Bundled513
namespace ProximityPrize.SubmissionLower.LocatorSelection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
section GenericCoefficients
variable {E V:Type*} [Field E] [AddCommGroup V] [Module E V]
def polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) :
    V →ₗ[E] (CoefficientIndex D w L s → E) :=
  LinearMap.pi (fun c=> (MvPolynomial.lcoeff E (columnExponent c)).comp f)
@[simp] theorem polynomialCoefficientsLinear_apply (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (c:CoefficientIndex D w L s) :
    polynomialCoefficientsLinear D w L s f v c=
      MvPolynomial.coeff (columnExponent c) (f v):=by
  simp only [polynomialCoefficientsLinear,LinearMap.pi_apply,
    LinearMap.comp_apply,MvPolynomial.lcoeff_apply]
theorem reconstruct_polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (hbox:f v ∈ globalCoefficientBox E D w L s) :
    reconstruct E D w L s (polynomialCoefficientsLinear D w L s f v) =f v:=by
  let Q:globalCoefficientBox E D w L s:=⟨f v,hbox⟩
  have he:polynomialCoefficientsLinear D w L s f v=encodeBox Q:=by
    funext c
    exact polynomialCoefficientsLinear_apply D w L s f v c
  rw [he]
  exact reconstruct_encodeBox Q
theorem reconstruct_add_generic (D w L s:ℕ)
    (a b:CoefficientIndex D w L s → E) :
    reconstruct E D w L s (a + b) =
      reconstruct E D w L s a + reconstruct E D w L s b:=
  (reconstructLinear (K:=E) D w L s).map_add a b
end GenericCoefficients
section GenericJoin
variable {E U V:Type*} [Field E]
 [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
def joinLinear (A:Submodule E U) (f:V →ₗ[E] U):(A × V) →ₗ[E] U:=
  A.subtype.comp (LinearMap.fst E A V) + f.comp (LinearMap.snd E A V)
@[simp] theorem joinLinear_apply (A:Submodule E U) (f:V →ₗ[E] U)
    (v:A × V):joinLinear A f v=v.1.1 + f v.2:=by
  simp only [joinLinear,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,Submodule.subtype_apply]
variable {LeftRest RightRest:Type*} [AddCommGroup LeftRest] [Module E LeftRest]
 [AddCommGroup RightRest] [Module E RightRest]
def tripleLinear (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U) :
    (V × (LeftRest × RightRest)) →ₗ[E] U:=
  f.comp (LinearMap.fst E V (LeftRest × RightRest)) +
    g.comp ((LinearMap.fst E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest))) +
    h.comp ((LinearMap.snd E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest)))
@[simp] theorem tripleLinear_apply
    (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U)
    (v:V × (LeftRest × RightRest)) :
    tripleLinear f g h v=f v.1 + g v.2.1 + h v.2.2:=by
  simp only [tripleLinear,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply]
end GenericJoin
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid P4:=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 10539006 131071 52091 17 58 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 16898751 131071 52091 28 93 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 22895082 131071 52091 39 126 IRSProfile.domain u0 u1
abbrev TKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20532891 131071 2413 35 113 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 16717044 131071 2558 28 92 IRSProfile.domain u0 u1
abbrev Ambient:=CoefficientIndex 22895082 131071 52091 39 → K
theorem gateC:Fintype.card I * localRankBound 126 52091 39 <
    coefficientCount 22895082 131071 52091 39:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorSourceArithmetic.kernelAmbient_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 92 2558 28 <
    coefficientCount 16717044 131071 2558 28:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem aBox_le_cBox:globalCoefficientBox K 10539006 131071 52091 17 ≤
    globalCoefficientBox K 22895082 131071 52091 39:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedA (u0 u1:I → K):AKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 10539006 131071 52091 17 58
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedA (u0 u1:I → K) (v:AKernel u0 u1) :
    reconstruct K 22895082 131071 52091 39 (embedA u0 u1 v) =
      reconstruct K 10539006 131071 52091 17 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 10539006 131071 52091 17 58
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 22895082 131071 52091 39:=by
    rw [kernelReconstructLinear_apply]
    exact aBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 10539006 131071 52091 17 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 10539006 131071 52091 17 58
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedA,kernelReconstructLinear_apply] using h
theorem auxBox_le_cBox:globalCoefficientBox K 16898751 131071 52091 28 ≤
    globalCoefficientBox K 22895082 131071 52091 39:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedAux (u0 u1:I → K):AuxKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 16898751 131071 52091 28 93
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedAux (u0 u1:I → K) (v:AuxKernel u0 u1) :
    reconstruct K 22895082 131071 52091 39 (embedAux u0 u1 v) =
      reconstruct K 16898751 131071 52091 28 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 16898751 131071 52091 28 93
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 22895082 131071 52091 39:=by
    rw [kernelReconstructLinear_apply]
    exact auxBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 16898751 131071 52091 28 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 16898751 131071 52091 28 93
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedAux,kernelReconstructLinear_apply] using h
theorem tBox_le_cBox:globalCoefficientBox K 20532891 131071 2413 35 ≤
    globalCoefficientBox K 22895082 131071 52091 39:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩
def embedT (u0 u1:I → K):TKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 20532891 131071 2413 35 113
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedT (u0 u1:I → K) (v:TKernel u0 u1) :
    reconstruct K 22895082 131071 52091 39 (embedT u0 u1 v) =
      reconstruct K 20532891 131071 2413 35 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 20532891 131071 2413 35 113
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 22895082 131071 52091 39:=by
    rw [kernelReconstructLinear_apply]
    exact tBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 20532891 131071 2413 35 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 22895082 131071 52091 39
    (kernelReconstructLinear (K:=K) 20532891 131071 2413 35 113
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedT,kernelReconstructLinear_apply] using h
def joinedMap (u0 u1:I → K) :
    (CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TKernel u0 u1))) →ₗ[K]
      Ambient:=
  joinLinear (CKernel u0 u1)
    (tripleLinear (embedA u0 u1) (embedAux u0 u1) (embedT u0 u1))
abbrev JoinedKernel (u0 u1:I → K):=LinearMap.range (joinedMap u0 u1)
@[simp] theorem joinedMap_apply (u0 u1:I → K)
    (v:CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TKernel u0 u1))) :
    joinedMap u0 u1 v=
      v.1.1 + (embedA u0 u1 v.2.1 + embedAux u0 u1 v.2.2.1 +
        embedT u0 u1 v.2.2.2):=by
  simp only [joinedMap,joinLinear_apply,tripleLinear_apply]
theorem reconstruct_joinedMap (u0 u1:I → K)
    (v:CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TKernel u0 u1))) :
    reconstruct K 22895082 131071 52091 39 (joinedMap u0 u1 v) =
      reconstruct K 22895082 131071 52091 39 v.1.1 +
        (reconstruct K 10539006 131071 52091 17 v.2.1.1 +
          reconstruct K 16898751 131071 52091 28 v.2.2.1.1 +
          reconstruct K 20532891 131071 2413 35 v.2.2.2.1):=by
  rw [joinedMap_apply,reconstruct_add_generic,reconstruct_add_generic,
    reconstruct_add_generic,reconstruct_embedA,reconstruct_embedAux,
    reconstruct_embedT]
def includeC (u0 u1:I → K) (v:CKernel u0 u1):JoinedKernel u0 u1:=
  ⟨v.1, ⟨(v, (0, (0,0))),by
    simp only [joinedMap_apply,map_zero,zero_add,add_zero]⟩⟩
def includeA (u0 u1:I → K) (v:AKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedA u0 u1 v, ⟨(0, (v, (0,0))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeAux (u0 u1:I → K) (v:AuxKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedAux u0 u1 v, ⟨(0, (0, (v,0))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeT (u0 u1:I → K) (v:TKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedT u0 u1 v, ⟨(0, (0, (0,v))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
theorem joined_universal (u0 u1:I → K) (v:JoinedKernel u0 u1)
    (gamma:K) (P:Polynomial K) (points:Finset I)
    (hP:P.natDegree ≤ 131071) (hcard:181707 ≤ points.card)
    (hvalues:∀ i ∈ points,
      P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (reconstruct K 22895082 131071 52091 39 v.1) =0:=by
  obtain ⟨z,hz⟩:=v.2
  rw [← hz,reconstruct_joinedMap,map_add,map_add,map_add]
  have hc:=specialization_eq_zero_of_agreements K
    22895082 131071 52091 39 126 181707 IRSProfile.domain u0 u1
    z.1.1 z.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have ha:=specialization_eq_zero_of_agreements K
    10539006 131071 52091 17 58 181707 IRSProfile.domain u0 u1
    z.2.1.1 z.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have haux:=specialization_eq_zero_of_agreements K
    16898751 131071 52091 28 93 181707 IRSProfile.domain u0 u1
    z.2.2.1.1 z.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have hthin:=specialization_eq_zero_of_agreements K
    20532891 131071 2413 35 113 181707 IRSProfile.domain u0 u1
    z.2.2.2.1 z.2.2.2.2 (by decide) (by decide) P gamma points hP hcard hvalues
  rw [specialization_eq_ordinary] at ha haux hc hthin
  rw [hc,ha,haux,hthin,zero_add,zero_add,zero_add]
private theorem gcd_mul_right_plain_associated
    (P H q:P4) (hc:IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
    have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
    have hcop:IsRelPrime (gcd P (H * q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
    (H q P:P4) (hc:IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
    have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
    have hcop:IsRelPrime (gcd (H * q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)
structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ globalCoefficientBox K 22895082 131071 52091 39
  QB_flag:QB ∈ globalCoefficientBox K 16717044 131071 2558 28
  common_divides_A:∀ v:AKernel u0 u1,
    gcd QA QB ∣ reconstruct K 10539006 131071 52091 17 v.1
  common_divides_Aux:∀ v:AuxKernel u0 u1,
    gcd QA QB ∣ reconstruct K 16898751 131071 52091 28 v.1
  common_divides_C:∀ v:CKernel u0 u1,
    gcd QA QB ∣ reconstruct K 22895082 131071 52091 39 v.1
  common_divides_T:∀ v:TKernel u0 u1,
    gcd QA QB ∣ reconstruct K 20532891 131071 2413 35 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 16717044 131071 2558 28 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181707 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaC,htC,hkC⟩:=exists_nonzero_kernel_array (I:=I)
    K 22895082 131071 52091 39 126 IRSProfile.domain u0 u1 gateC
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 16717044 131071 2558 28 92 IRSProfile.domain u0 u1 gateB
  let c0:CKernel u0 u1:=⟨thetaC,LinearMap.mem_ker.mpr hkC⟩
  let vC0:JoinedKernel u0 u1:=includeC u0 u1 c0
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (JoinedKernel u0 u1):=⟨⟨vC0,0,by
    intro h
    exact htC (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bA:=Module.Free.chooseBasis K (JoinedKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)) :=
    Module.Finite.finite_basis bA
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)):=bA.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HA:=commonGCD (JoinedKernel u0 u1) bA
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHA:HA ≠ 0:=commonGCD_ne_zero (JoinedKernel u0 u1) bA
  have hHB:HB ≠ 0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB ∈ globalCoefficientBox K 16717044 131071 2558 28:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 16717044 2558 28
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (JoinedKernel u0 u1) bA hHA HB hHB hcardHB
  let qA:=commonQuotientLinear (JoinedKernel u0 u1) bA hHA vA
  let QA:=submoduleReconstructLinear (JoinedKernel u0 u1) vA
  have hQAeq:QA=HA * qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (JoinedKernel u0 u1)) HA
    (commonDivisorProof (JoinedKernel u0 u1) bA) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (JoinedKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ globalCoefficientBox K 22895082 131071 52091 39:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 22895082 131071 52091 39 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 22895082 52091 39
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB:=submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq:QB=HB * qB:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB:QB ≠ 0:=by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB ∈ globalCoefficientBox K 16717044 131071 2558 28:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 16717044 131071 2558 28 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HA HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HA qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHA:gcd QA QB ∣ HA:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HA HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HA HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_A:=?_,common_divides_Aux:=?_,common_divides_C:=?_
    common_divides_T:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeA u0 u1 v))
    change gcd QA QB ∣ reconstruct K 22895082 131071 52091 39 (embedA u0 u1 v) at h
    simpa only [reconstruct_embedA] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeAux u0 u1 v))
    change gcd QA QB ∣ reconstruct K 22895082 131071 52091 39 (embedAux u0 u1 v) at h
    simpa only [reconstruct_embedAux] using h
  · intro v
    exact hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeC u0 u1 v))
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeT u0 u1 v))
    change gcd QA QB ∣ reconstruct K 22895082 131071 52091 39 (embedT u0 u1 v) at h
    simpa only [reconstruct_embedT] using h
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact joined_universal u0 u1 vA gamma P points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        16717044 131071 2558 28 92 181707 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.LocatorSelection
end Bundled513

section Bundled514
namespace ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
open RCN100 RCN119 RCN101 RCN122 RCN180
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
section Generic
variable {E J:Type*} [Field E] [Fintype J]
local instance:DecidableEq E:=Classical.decEq E
theorem globalCoefficientBox_mono_total {D w L Lmax s:ℕ} (hL:L ≤ Lmax) :
    globalCoefficientBox E D w L s ≤ globalCoefficientBox E D w Lmax s:=by
  intro P hP d hd
  exact ⟨(hP hd).1.trans hL, (hP hd).2⟩
def zeroExtendTotal {D w L Lmax s:ℕ} (_hL:L ≤ Lmax) :
    (CoefficientIndex D w L s → E) →ₗ[E] (CoefficientIndex D w Lmax s → E) :=
  LocatorSelection.polynomialCoefficientsLinear D w Lmax s
    (reconstructLinear (K:=E) D w L s)
@[simp] theorem zeroExtendTotal_apply {D w L Lmax s:ℕ} (hL:L ≤ Lmax)
    (a:CoefficientIndex D w L s → E) (c:CoefficientIndex D w Lmax s) :
    zeroExtendTotal (E:=E) hL a c=
      MvPolynomial.coeff (columnExponent c) (reconstruct E D w L s a) :=
  LocatorSelection.polynomialCoefficientsLinear_apply D w Lmax s
    (reconstructLinear (K:=E) D w L s) a c
@[simp] theorem reconstruct_zeroExtendTotal {D w L Lmax s:ℕ} (hL:L ≤ Lmax)
    (a:CoefficientIndex D w L s → E) :
    reconstruct E D w Lmax s (zeroExtendTotal (E:=E) hL a) =
      reconstruct E D w L s a:=by
  apply LocatorSelection.reconstruct_polynomialCoefficientsLinear
    D w Lmax s (reconstructLinear (K:=E) D w L s) a
  exact globalCoefficientBox_mono_total hL
    (reconstruct_mem_globalCoefficientBox E D w L s a)
theorem zeroExtendTotal_mem_constraintKernel
    {D w L Lmax s m:ℕ} (hL:L ≤ Lmax) (nodes u0 u1:J → E)
    (a:CoefficientIndex D w L s → E)
    (ha:a ∈ LinearMap.ker (constraintMap E D w L s m nodes u0 u1)) :
    zeroExtendTotal (E:=E) hL a ∈
      LinearMap.ker (constraintMap E D w Lmax s m nodes u0 u1):=by
  rw [LinearMap.mem_ker]
  funext i r
  apply Subtype.ext
  change contactJet E (m - r.val)
    ((extractBlock E D w Lmax s (nodes i) (u0 i) (u1 i) r.val
      (zeroExtendTotal (E:=E) hL a)):RCN119.Poly E) =0
  rw [← translation_reconstruct_coeff,reconstruct_zeroExtendTotal,
    translation_reconstruct_coeff]
  exact block_equations_of_mem_ker E D w L s m nodes u0 u1 a ha i r
def zeroExtendConstraintKernel {D w L Lmax s m:ℕ} (hL:L ≤ Lmax)
    (nodes u0 u1:J → E) :
    ConstraintKernel (K:=E) D w L s m nodes u0 u1 →ₗ[E]
      ConstraintKernel (K:=E) D w Lmax s m nodes u0 u1:=
  LinearMap.codRestrict
    (ConstraintKernel (K:=E) D w Lmax s m nodes u0 u1)
    ((zeroExtendTotal (E:=E) hL).comp
      (ConstraintKernel (K:=E) D w L s m nodes u0 u1).subtype)
    (fun a=> zeroExtendTotal_mem_constraintKernel hL nodes u0 u1 a.1 a.2)
@[simp] theorem zeroExtendConstraintKernel_coe {D w L Lmax s m:ℕ}
    (hL:L ≤ Lmax) (nodes u0 u1:J → E)
    (a:ConstraintKernel (K:=E) D w L s m nodes u0 u1) :
    (zeroExtendConstraintKernel hL nodes u0 u1 a).1=
      zeroExtendTotal (E:=E) hL a.1:=rfl
@[simp] theorem reconstruct_zeroExtendConstraintKernel {D w L Lmax s m:ℕ}
    (hL:L ≤ Lmax) (nodes u0 u1:J → E)
    (a:ConstraintKernel (K:=E) D w L s m nodes u0 u1) :
    reconstruct E D w Lmax s (zeroExtendConstraintKernel hL nodes u0 u1 a).1=
      reconstruct E D w L s a.1:=
  reconstruct_zeroExtendTotal hL a.1
theorem full_kernel_divisor_small {D w L Lmax s m:ℕ} (hL:L ≤ Lmax)
    (nodes u0 u1:J → E) (F:MvPolynomial (Fin 4) E)
    (hdiv:∀ a:ConstraintKernel (K:=E) D w Lmax s m nodes u0 u1,
      F ∣ reconstruct E D w Lmax s a.1) :
    ∀ a:ConstraintKernel (K:=E) D w L s m nodes u0 u1,
      F ∣ reconstruct E D w L s a.1:=by
  intro a
  have h:=hdiv (zeroExtendConstraintKernel hL nodes u0 u1 a)
  simpa only [reconstruct_zeroExtendConstraintKernel] using h
end Generic
section Selected
open ProximityPrize.Benchmark
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_divides_A93_small {u0 u1:I → K}
    (S:LocatorSelection.SelectedPair u0 u1) (L:ℕ) (hL:L ≤ 52091) :
    ∀ a:ConstraintKernel (K:=K) 16898751 131071 L 28 93
      IRSProfile.domain u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 16898751 131071 L 28 a.1:=by
  exact full_kernel_divisor_small (E:=K) (Lmax:=52091) hL
    IRSProfile.domain u0 u1 (gcd S.QA S.QB) S.common_divides_Aux
theorem common_divides_A126_small {u0 u1:I → K}
    (S:LocatorSelection.SelectedPair u0 u1) (L:ℕ) (hL:L ≤ 52091) :
    ∀ a:ConstraintKernel (K:=K) 22895082 131071 L 39 126
      IRSProfile.domain u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 22895082 131071 L 39 a.1:=by
  exact full_kernel_divisor_small (E:=K) (Lmax:=52091) hL
    IRSProfile.domain u0 u1 (gcd S.QA S.QB) S.common_divides_C
end Selected
end
end ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
end Bundled514

section Bundled515
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 2411:=
  LocatorCaps.common_T_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_T
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 78:=
  LocatorCaps.common_A_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 17:=
  LocatorCaps.common_A_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
end Bundled515

section Bundled516
namespace ProximityPrize.SubmissionLower.RCN202
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084 RCN095 RCN341 RCN037 RCN076
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" => MvPolynomial (Fin 3) K
local notation "PE" => MvPolynomial (Fin 3) E
def rationalVariable (K:Type) [Field K]:RatFunc K:=
 algebraMap (Polynomial K) (RatFunc K) Polynomial.X
theorem eliminated_not_mem_nonpoint
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U)
   (D:Ideal PE) [D.IsPrime]
   (hnonpoint:∀ v:Fin 3 → E,D≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hF:scalarPolynomialMap K E F∈D)
   (hN:movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∈D)
   (hH:scalarPolynomialMap K E H∉D) (hU:scalarPolynomialMap K E U∉D)
   (hbelow:D.comap (scalarPolynomialMap K E) ≤ C.1):
   eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∉D:=by
 intro hA
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let evD:=coordinateEvaluation E D
 let ev:=evD.toRingHom.comp mu
 have hTor:mu (filteredCut k B H G)∈D:=by
   rw [map_filteredCut]
   exact original_mem_of_eliminated_mem D k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hA hU
 have hcut:cutIdeal K F (filteredCut k B H G) ≤ D.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact hF
   · exact hTor
 have hmin:=(mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (regularComponent_mem K _ _ _ C)
 have hcontract:D.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     coordinateEvaluation_ker E D]
   exact hcontract
 let phi:=coordinateFieldMap C.1 ev hker
 have hphi (A:Poly):phi (coordinateEvaluation K C.1 A)=ev A:=
   coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):phi (algebraMap K (CoordinateField K C.1) c)=
     algebraMap E (CoordinateField E D) (algebraMap K E c):=by
   simpa [ev,mu,scalarPolynomialMap] using hphi (MvPolynomial.C c)
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [coordinateEvaluation_ker E D] at this
   exact hH this
 have hNzero:evD (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   apply RingHom.mem_ker.mp
   change _∈RingHom.ker (coordinateEvaluation E D).toRingHom
   rwa [coordinateEvaluation_ker E D]
 have hrel:ev H*(algebraMap E (CoordinateField E D) t-ev Q)=ev U*ev G:=by
   have hconst:evD (MvPolynomial.C t)=algebraMap E (CoordinateField E D) t:=evD.commutes t
   apply sub_eq_zero.mp
   simpa only [movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=algebraMap E (CoordinateField E D) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (CoordinateField E D) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd];ring
 have hdiag:(algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)=
     phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1)):=by
   apply IsFractionRing.ringHom_ext (A:=Polynomial K)
   intro p
   have hp:((algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)).comp
       (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1))).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
     apply Polynomial.ringHom_ext
     · intro c
       change algebraMap E (CoordinateField E D)
         (algebraMap (RatFunc K) E (algebraMap K (RatFunc K) c))=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (algebraMap K (RatFunc K) c))
       rw [←IsScalarTower.algebraMap_apply K (RatFunc K) E,
         ←IsScalarTower.algebraMap_apply K (RatFunc K) (CoordinateField K C.1),hscalar]
     · change algebraMap E (CoordinateField E D) t=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K))
       rw [hj];exact hjmap.symm
   exact RingHom.congr_fun hp p
 have halg:∀ i,IsAlgebraic E (coordinate E D i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (algebraMap (RatFunc K) E) phi hdiag
     (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic E D halg
 exact hnonpoint v hv
theorem embedding_point_certificate
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U) (hU:U∉C.1)
   (f:CoordinateField K C.1 →ₐ[RatFunc K] E):
   let mu:=scalarPolynomialMap K E
   let t:=algebraMap (RatFunc K) E (rationalVariable K)
   let v:=embeddingPoint C.1 (f.restrictScalars K)
   let N:=movingEquation (mu H) (mu G) (mu Q) (mu U) t
   let A:=eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t
   MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v (mu H*mu U)≠0∧
     IsolatedPoint (mu F) N A v:=by
 dsimp only
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let v:=embeddingPoint C.1 (f.restrictScalars K)
 let ev:=MvPolynomial.eval v
 have hev (A:Poly):ev (mu A)=f (coordinateEvaluation K C.1 A):=by
   have h:=AlgHom.congr_fun (embeddingPoint_aeval C.1 (f.restrictScalars K)) A
   change MvPolynomial.eval v (MvPolynomial.map (algebraMap K E) A)=_
   rw [MvPolynomial.eval_map]
   exact h
 have hz (A:Poly) (hA:A∈C.1):ev (mu A)=0:=by
   rw [hev]
   have ha:coordinateEvaluation K C.1 A=0:=by
     apply RingHom.mem_ker.mp
     change A∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
     rwa [coordinateEvaluation_ker K C.1]
   rw [ha,map_zero]
 have hne (A:Poly) (hA:A∉C.1):ev (mu A)≠0:=by
   rw [hev]
   exact fun h↦hA (by
     rw [←coordinateEvaluation_ker K C.1]
     exact (map_eq_zero_iff f f.injective).mp h)
 have hHne:=hne H (regularComponent_H_not_mem K _ _ _ C)
 have hUne:=hne U hU
 have hjval:ev (mu Q)+ev (mu U)*ev (mu G)/ev (mu H)=t:=by
   simp only [hev]
   have h:=f.commutes (rationalVariable K)
   rw [hj] at h
   simpa only [movingValue,map_add,map_div₀,map_mul] using h
 have hN:ev (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   have hevC:ev (MvPolynomial.C t)=t:=by simp [ev]
   simp only [movingEquation,map_sub,map_mul,hevC]
   have h:=(div_eq_iff hHne).mp (show ev (mu U)*ev (mu G)/ev (mu H)=t-ev (mu Q) by
     linear_combination hjval)
   linear_combination-h
 have hA:ev (eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t)=0:=by
   apply (eliminatedCut_zero_iff ev k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hHne hUne).mpr
   rw [←map_filteredCut]
   exact hz _ (regularComponent_T_mem K _ _ _ C)
 refine ⟨hz F (regularComponent_G_mem K _ _ _ C),hN,hA,?_,?_⟩
 · simpa only [map_mul] using mul_ne_zero hHne hUne
 · intro D hD hn hp hDF hDN
   letI:=hD
   apply eliminated_not_mem_nonpoint F H G Q U k B C hj D hn hDF hDN
   · exact fun h↦hHne (hp h)
   · exact fun h↦hUne (hp h)
   · exact comap_le_of_embedding_point C.1 (f.restrictScalars K) D hp
abbrev fiberEquation (H G Q U:Poly):PE:=
 movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
abbrev fiberCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly):PE:=
 eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
theorem sum_moving_degrees_le
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1)]
   (hj:∀ C:RegularComponent K F (filteredCut k B H G) H,
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U)
   (hU:∀ C:RegularComponent K F (filteredCut k B H G) H,U∉C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p q r:FlagDegree) (hFp:PolynomialInFlag p F)
   (hNq:PolynomialInFlag q (fiberEquation (E:=E) H G Q U))
   (hAr:PolynomialInFlag r (fiberCut (E:=E) k B Q U))
   (c:ℕ) [CharP E c] (hdeg:p.zOnly+p.yz+p.all < c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c):
   (∑ C:RegularComponent K F (filteredCut k B H G) H,
     Module.finrank (RatFunc K) (CoordinateField K C.1)) ≤ flagMixed p q r:=by
 classical
 let mu:=scalarPolynomialMap K E
 let N:=fiberEquation (E:=E) H G Q U
 let A:=fiberCut (E:=E) k B Q U
 let R:=mu H*mu U
 let P:=fun C:RegularComponent K F (filteredCut k B H G) H↦C.1
 let points:=genericFiberPoints (B:=RatFunc K) (L:=E) P
 have hc:∀ v∈points,MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v R≠0∧IsolatedPoint (mu F) N A v:=by
   intro v hv
   obtain ⟨⟨C,f⟩,_,rfl⟩:=Finset.mem_image.mp hv
   exact embedding_point_certificate F H G Q U k B C (hj C) (hU C) f
 have hinj:Function.Injective mu:=
   MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
 have hMF:mu F≠0:=fun h↦hF (hinj (h.trans (map_zero mu).symm))
 have hMFp:=inFlag_map (algebraMap K E) hFp
 obtain ⟨base,hY,hZ⟩:=exists_small_projection_data (mu F) N R hMF p q hMFp hNq c hdeg hmix
 rw [←genericFiberPoints_card (B:=RatFunc K) (L:=E) P Subtype.val_injective]
 apply isolated_points_card_le (mu F) N A R p q r hMF
   hMFp hNq hAr base hY hZ points
 · intro v hv
   have hv:=hc v hv
   apply exists_active_factor_of_isolated (mu F) N A R hMF v hv.1 hv.2.2.1 hv.2.2.2.1
   · have hH:MvPolynomial.eval v (mu H)≠0:=
       (mul_ne_zero_iff.mp (by simpa only [R,map_mul] using hv.2.2.2.1)).1
     exact map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval v) (mu F) (mu H)
       (scalar_derivative_span F H hderiv) hv.1 hH
   · exact hv.2.2.2.2
 · exact fun v hv↦(hc v hv).2.1
 · exact fun v hv↦(hc v hv).2.2.1
 · exact fun v hv↦(hc v hv).2.2.2.1
 · intro g C v hv hp
   have hCF:=C.1.mem_of_dvd (activeFactors_spec (mu F) N g).2.1
     (regularComponent_G_mem E g.1 N R C)
   exact (hc v hv).2.2.2.2 C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
     hp hCF (regularComponent_T_mem E g.1 N R C)
theorem fiber_small_flags (a b s k:ℕ) (C:FlagDegree)
   (H G Q U:Poly) (B:Fin (k+1) → Poly) (c:Fin (k+1) → FlagDegree)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H) (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q) (hU:PolynomialInFlag unitYZFlag U)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (fiberEquation (E:=E) H G Q U)∧
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (fiberCut (E:=E) k B Q U):=by
 constructor
 · exact movingEquation_inFlag a b s _ _ _ _ _
     (inFlag_map (algebraMap K E) hH) (inFlag_map (algebraMap K E) hG)
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU)
 · exact eliminatedCut_small_flag a b s k C _ _ _ _ c
     (fun j↦inFlag_map (algebraMap K E) (hB j))
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU) hc
end
end ProximityPrize.SubmissionLower.RCN202
end Bundled516

section Bundled517
namespace ProximityPrize.SubmissionLower.RCN209
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN022 RCN207 RCN208 RCN064 RCN202 RCN095 RCN187
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem exists_separable_moving_coordinates (F A H G:Poly)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ (Q U:Poly) (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1)),
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
           movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=WithZero.exp
           (max (poleOrder v.val (coordinate K C.1 0)) (poleOrder v.val (coordinate K C.1 2)))):=by
 obtain ⟨Q,U,hQ,hU,h⟩:=exists_common_original_projection F A H G base
 have gate (C:RegularComponent K F A H):=moving_projection_gate (base C) H G Q U (h C).2.1
 let J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1):=
   fun C↦{
     embedding:=elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) (gate C).choose
     finite:=(gate C).choose_spec.1
     separable:=(gate C).choose_spec.2.1}
 have hv (C:RegularComponent K F A H):
     SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U:=
   elementEmbedding_variable K (CoordinateField K C.1) _ (gate C).choose
 refine ⟨Q,U,J,hQ,hU,fun C↦⟨(h C).1,hv C,?_,(h C).2.2.2⟩⟩
 intro v
 rw [hv C]
 exact (h C).2.2.1 v
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_projection_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p:FlagDegree) (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ J:∀ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate K (CoordinateField K C.1),
     (∀ (C:RegularComponent K F (filteredCut k B H G) H)
         (v:Place K (CoordinateField K C.1)),
       poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
         movingPoleTarget C.1 H G v)∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate.degree K (CoordinateField K C.1) (J C)) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 classical
 obtain ⟨Q,U,J,hQ,hU,hJ⟩:=exists_separable_moving_coordinates F (filteredCut k B H G) H G base
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).embedding.toRingHom.toAlgebra
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1):=fun C↦
       IsScalarTower.of_algebraMap_eq fun a↦((J C).embedding.commutes a).symm
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).finite
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).separable
 have hj (C:RegularComponent K F (filteredCut k B H G) H):
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U:=
   (hJ C).2.1
 have hdeg:p.zOnly+p.yz+p.all < pchar:=by
   nlinarith
 obtain ⟨hN,hA⟩:=fiber_small_flags (E:=E) a b s k C0 H G Q U B c hH hG hQ hU hB hc
 have hcount:=sum_moving_degrees_le (E:=E) F H G Q U k B hj (fun C↦(hJ C).1)
   hF hderiv p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree))
   hFp hN hA pchar hdeg hmix
 refine ⟨J,fun C v↦(hJ C).2.2.1 v,?_⟩
 simpa only [SeparableCoordinate.degree] using hcount
end
end ProximityPrize.SubmissionLower.RCN209
end Bundled517

section Bundled518
namespace ProximityPrize.SubmissionLower.RCN200
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN046 RCN095 RCN295 RCN187 RCN207 RCN064 RCN209 RCN199
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
def budgetOfProjections (F A H G:Poly)
   {base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (unit:AdaptiveUnitProjectionFamily base p q)
   (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1))
   (hJ:∀ (C:RegularComponent K F A H) (v:Place K (CoordinateField K C.1)),
     poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
       movingPoleTarget C.1 H G v) (C:RegularComponent K F A H):
   MovingPoleBudget C.1 H G where
 zCost:=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)
 yzCost:=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)
 allCost:=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C)
 movingCost:=SeparableCoordinate.degree K (CoordinateField K C.1) (J C)
 zPole:=unit.toAdaptiveUnitPoleBudget.zPole C
 yzPole:=unit.toAdaptiveUnitPoleBudget.yzPole C
 allPole:=unit.toAdaptiveUnitPoleBudget.allPole C
 movingPole:=by
   intro W
   calc
     (∑ v∈W,movingPoleTarget C.1 H G v)=
         ∑ v∈W,RCN346.poleOrder K (CoordinateField K C.1) v
           (SeparableCoordinate.value K (CoordinateField K C.1) (J C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact (hJ C v).symm
     _ ≤ (SeparableCoordinate.degree K (CoordinateField K C.1) (J C):ℤ):=
       SeparableCoordinate.finite_sum_pole_le_degree K (CoordinateField K C.1) (J C) W
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_pole_budget_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (p firstCutFlag:FlagDegree) (unit:AdaptiveUnitProjectionFamily base p firstCutFlag)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ budget:∀ C:RegularComponent K F (filteredCut k B H G) H,MovingPoleBudget C.1 H G,
     (∀ C,(budget C).zCost=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)∧
       (budget C).yzCost=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)∧
       (budget C).allCost=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).zCost) ≤
       flagMixed p firstCutFlag unitZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).yzCost) ≤
       flagMixed p firstCutFlag unitYZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).allCost) ≤
       flagMixed p firstCutFlag unitAllFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).movingCost) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 obtain ⟨J,hJ,hdegree⟩:=exists_moving_projection_family (E:=E) F H G k B base
   hF hderiv p hFp a b s C0 hH hG c hB hc pchar hmix
 refine ⟨budgetOfProjections F (filteredCut k B H G) H G unit J hJ,?_,?_,?_,?_,?_⟩
 · exact fun C↦⟨rfl,rfl,rfl⟩
 · exact unit.sum_zDegree_le
 · exact unit.sum_yzDegree_le
 · exact unit.sum_allDegree_le
 · exact hdegree
end
end ProximityPrize.SubmissionLower.RCN200
end Bundled518

section Bundled519
namespace ProximityPrize.SubmissionLower.RCN203
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN201 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
def paddedCut (a b s d:ℕ):FlagDegree:=
 RCN206.centreFlag a b s+
   d • RCN206.directionFlag a b s
theorem mixed_add_second (p q r t:FlagDegree):
   flagMixed p (q+r) t=flagMixed p q t+flagMixed p r t:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all]
 ring
theorem mixed_affine_third (p q C R:FlagDegree) (k:ℕ):
   flagMixed p q (C+k • R)=flagMixed p q C+k*flagMixed p q R:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
theorem mixed_sharp_le_padded (a b s d:ℕ) (p r:FlagDegree):
   flagMixed p (sharpResidualAgreementFlag (support a b s) d) r ≤
     flagMixed p (paddedCut a b s d) r:=by
 have he:paddedCut a b s d=
     sharpResidualAgreementFlag (support a b s) d+direction a b s:=by
   rw [sharp_flag_eq]
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp [paddedCut,RCN206.centreFlag,
     RCN206.directionFlag,direction,unitYZFlag] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
theorem exists_actual_cut_budgets
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Ω) (a b s d:ℕ) (xI u0 u1:K)
   (hT:T=agreementPolynomial φ F d xI u0 u1)
   (hF:ResidualSupportData (support a b s) F) (flag:FlagDegree)
   (hG:G≠0) (hdiv:G∣surfaceMap φ F) (hGflag:PolynomialInFlag flag G)
   (base:∀ C:RegularComponent Ω G T (regularitySurface φ F),SeparableLiteralCoordinate C.1)
   (unit:AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) d))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar):
   ∃ budget:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
     (∀ C,(budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C∧
       (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C∧
       (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C)∧
     (∑ C,(budget C).zCost) ≤ flagMixed flag (paddedCut a b s d) unitZFlag∧
     (∑ C,(budget C).yzCost) ≤ flagMixed flag (paddedCut a b s d) unitYZFlag∧
     (∑ C,(budget C).allCost) ≤ flagMixed flag (paddedCut a b s d) unitAllFlag∧
     (∑ C,(budget C).movingCost) ≤ flagMixed flag
       (RCN206.fiberFlag a b s)
       (center a b s+d • RCN206.surfaceFlag a b s):=by
 classical
 obtain ⟨coeffs,cflags,heq,hcoeff,hclass,_⟩:=exists_actual_agreement_certificate
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight d xI u0 u1
 obtain ⟨hHflag,hGcontact⟩:=surfaceMap_HG_flags
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
 have hderiv:regularitySurface φ F∈
     Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set (MvPolynomial (Fin 3) Ω)):=by
   rw [regularitySurface, ←RCN267.surfaceMap_pderiv_R]
   exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
 have hT':T=filteredCut (d-1) coeffs (surfaceMap φ (polyH K F))
     (surfaceMap φ (polyG K F)):=hT.trans heq
 clear hT
 subst T
 obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=exists_moving_pole_budget_family (E:=E)
   G (regularitySurface φ F) (surfaceMap φ (polyG K F)) (d-1) coeffs
   base flag (sharpResidualAgreementFlag (support a b s) d) unit hG hderiv hGflag
   a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
   (by convert hmix using 1 <;> ring)
 refine ⟨budget,hcost,hz.trans (mixed_sharp_le_padded a b s d flag unitZFlag),
   hyz.trans (mixed_sharp_le_padded a b s d flag unitYZFlag),
   ha.trans (mixed_sharp_le_padded a b s d flag unitAllFlag),hm.trans ?_⟩
 rw [mixed_affine_third,mixed_affine_third]
 exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le d 1)) _
end
end ProximityPrize.SubmissionLower.RCN203
end Bundled519

section Bundled520
namespace ProximityPrize.SubmissionLower.RCN085
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
theorem exists_firstTail_cut_budgets
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Ω) (a b s w:ℕ) (hw:1 ≤ w)
   (hT:T=globalTailCut φ F (w+1))
   (hF:ResidualSupportData (support a b s) F) (flag:FlagDegree)
   (hG:G≠0) (hdiv:G∣surfaceMap φ F) (hGflag:PolynomialInFlag flag G)
   (base:∀ C:RegularComponent Ω G T (regularitySurface φ F),SeparableLiteralCoordinate C.1)
   (unit:AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) (w+1)))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar):
   ∃ budget:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
     (∀ C,(budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C∧
       (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C∧
       (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C)∧
     (∑ C,(budget C).zCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitZFlag∧
     (∑ C,(budget C).yzCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitYZFlag∧
     (∑ C,(budget C).allCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitAllFlag∧
     (∑ C,(budget C).movingCost) ≤ flagMixed flag
       (RCN206.fiberFlag a b s)
       (center a b s+(w+1) • RCN206.surfaceFlag a b s):=by
 classical
 obtain ⟨coeffs,cflags,heq,hcoeff,hclass⟩:=globalTailCut_certificate
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
 obtain ⟨hHflag,hGcontact⟩:=surfaceMap_HG_flags
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
 have hderiv:regularitySurface φ F∈
     Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set (MvPolynomial (Fin 3) Ω)):=by
   rw [regularitySurface, ←RCN267.surfaceMap_pderiv_R]
   exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
 have hT':T=filteredCut w coeffs (surfaceMap φ (polyH K F))
     (surfaceMap φ (polyG K F)):=hT.trans heq
 clear hT
 subst T
 obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=exists_moving_pole_budget_family (E:=E)
   G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
   base flag (sharpResidualAgreementFlag (support a b s) (w+1)) unit hG hderiv hGflag
   a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
   (by convert hmix using 1 <;> ring)
 refine ⟨budget,hcost,hz.trans (mixed_sharp_le_padded a b s (w+1) flag unitZFlag),
   hyz.trans (mixed_sharp_le_padded a b s (w+1) flag unitYZFlag),
   ha.trans (mixed_sharp_le_padded a b s (w+1) flag unitAllFlag),hm.trans ?_⟩
 rw [mixed_affine_third,mixed_affine_third]
 exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _
end
end ProximityPrize.SubmissionLower.RCN085
end Bundled520

section Bundled521
namespace ProximityPrize.SubmissionLower.RCN088
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN086
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem firstTail_in_sharp_flag
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s)):
   PolynomialInFlag
     (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))
     (globalTailCut phi S.F (w+1)):=by
 let Hsupport:ResidualSupportData
     (RCN198.support a b s) S.F:=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 exact globalTailCut_in_sharp_flag phi a b s S.F
   Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight (w+1)
theorem exists_firstTail_projection
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s))
   (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
   (hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega S.G (globalTailCut phi S.F (w+1)) 2 < pchar):
   ∃ base:∀ C:RegularComponent Omega S.G
       (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))):=by
 classical
 let T:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 have hTflag:=firstTail_in_sharp_flag S
 let choiceData:∀ C:RegularComponent Omega S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G T pchar S.G_dvd_surface
     S.irreducible_G hproper S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G T H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0)≠0∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega S.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G T S.irreducible_G
     (regularComponent_G_mem Omega S.G T H C)
     (regularComponent_T_mem Omega S.G T H C)
     hproper hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))
   base hactive hZ (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 hGflag)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (RCN198.support a b s) (w+1)) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem exists_firstTail_projection_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s))
   (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
   (hflagChar:flag.yz+flag.all < pchar∧flag.all < pchar∧
     flag.zOnly+flag.yz+flag.all < pchar)
   (hmixed:(1+(w+1)*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*(w+1)) < pchar):
   ∃ base:∀ C:RegularComponent Omega S.G
       (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))):=by
 let T:=globalTailCut phi S.F (w+1)
 let supp:=RCN198.support a b s
 have hsy:supp.s < supp.ys:=by
   change s+2 < b+s+3
   omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag supp (w+1)) T:=
   firstTail_in_sharp_flag S
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+(w+1)*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys supp hsy (w+1)
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*(w+1):=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,supp,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Omega S.G T 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 exact exists_firstTail_projection S hproper hGdegree hmixZ
end
end ProximityPrize.SubmissionLower.RCN088
end Bundled521

section Bundled522
namespace ProximityPrize.SubmissionLower.RCN049
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem exists_agreement_projection_of_caps
   (S:ResidualStage φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   ∃ base:∀ C:RegularComponent Ω S.G
       (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=agreementPolynomial φ S.F w x0 u0 u1
 let H:=regularitySurface φ S.F
 have hsy:s+2 < b+s+3:=by omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=φ)
     ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
     w (fun j:ℕ => (j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+w*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys (support a b s) hsy w
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*w:=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Ω S.G T 2<p:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C => regularComponent_exists_separableLiteralCoordinate6630
     φ S.F S.G T p S.G_dvd_surface S.irreducible_G hproper
     S.y_dependent hGdegree hmixZ C
 let base:∀ C:RegularComponent Ω S.G T H,
     SeparableLiteralCoordinate C.1:=fun C => (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Ω S.G T H,
     D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Ω S.G T H,LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Ω C.1 2 htr
     p S.G T S.irreducible_G
     (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C)
     hproper hGdegree hmixZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.RCN049
end Bundled522

section Bundled523
namespace ProximityPrize.SubmissionLower.RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
def identityCurveDegree (flag:FlagDegree) (a b s w:ℕ):ℕ:=
 flagMixed flag (paddedCut a b s (w+1)) unitZFlag+
   flagMixed flag (paddedCut a b s (w+1)) unitYZFlag
theorem mixed_padded_le_succ (flag:FlagDegree) (a b s d:ℕ) (r:FlagDegree):
   flagMixed flag (paddedCut a b s d) r ≤
     flagMixed flag (paddedCut a b s (d+1)) r:=by
 have he:paddedCut a b s (d+1)=paddedCut a b s d+
     RCN206.directionFlag a b s:=by
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp only [paddedCut,
     RCN206.centreFlag,
     RCN206.directionFlag,
     add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
variable {Γ:Finset K} {x:I → K} {p e a b s:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ}
theorem actual_identityCurveCountProvider
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀ γ∈Γ,agreements≤(S.agreementFiber γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   IdentityCurveCountProvider S (identityCurveDegree flag a b s w):=by
 classical
 unfold IdentityCurveCountProvider
 intro i hi
 dsimp only
 intro hproper
 let T:=agreementPolynomial (polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ => S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=exists_agreement_projection_of_caps S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RegularComponent (Ω K) S.G T (regularitySurface (polynomialEmbedding K) S.F)→ℕ:=
   fun C => U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=componentSeeds (Ω K) S.G T
     (regularitySurface (polynomialEmbedding K) S.F) Gi
     (selectedPoint (polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=componentSeeds_subset (Ω K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀ W:Finset (RCN346.Place (Ω K)
       (CoordinateField (Ω K) C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag))≤
       (coordinateDegree (Ω K) (CoordinateField (Ω K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (Ω K)
           (CoordinateField (Ω K) C.1) v
           (coordinateValue (Ω K) (CoordinateField (Ω K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _ ≤ _:=finite_sum_coordinate_pole_le_degree (Ω K)
         (CoordinateField (Ω K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=coefficientPoleProfile_of_regular_agreement_curve
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toPrimeFlagBudgetFamily.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
       (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
       (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ) ≤
         ((U.family.toPrimeFlagBudgetFamily.zCost C+
           U.family.toPrimeFlagBudgetFamily.yzCost C:ℕ):ℤ)
       norm_cast
       omega)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (polynomialEmbedding K) S.F rfl S.G_dvd_surface C
   apply prime_curve_card_le_of_coefficientPoleProfile
     (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
     (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.characteristic_bound hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact componentSeeds_on_prime (Ω K) S.G T
       (regularitySurface (polynomialEmbedding K) S.F) Gi
       (selectedPoint (polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
       hagreement γ hΓ
   · exact noLargeSelectedPencil_mono S.selected Γ Gc w e hGcΓ S.no_large_pencil
 · have hz:=U.family.sum_zDegree_le
   have hyz:=U.family.sum_yzDegree_le
   change (∑ C,U.family.toPrimeFlagBudgetFamily.zCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toPrimeFlagBudgetFamily.yzCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (mixed_padded_le_succ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (mixed_padded_le_succ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C)) ≤ identityCurveDegree flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end ProximityPrize.SubmissionLower.RCN146
end Bundled523

section Bundled524
namespace ProximityPrize.SubmissionLower.RCN090
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_projection_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (reducedResidualAgreementFlag (support a b s) (w + 1))):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T,Tred,sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY,hGS,hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY,hTS,_hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (reducedResidualAgreementFlag supp (w + 1)) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproperRed
   ((support_subset_flagSupport_iff flag S.G).2 hGflag)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag supp (w + 1)) Tred).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY, hTS, _hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 have hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.RCN090
end Bundled524

section Bundled525
namespace ProximityPrize.SubmissionLower.RCN254
open RCN135 RCN136 RCN086 RCN244 RCN245 RCN249 RCN112 RCN103 RCN113 RCN093 RCN095 RCN011
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   stageFamilyResultant S A F≠0:=by
 change flagPlaneResultant F.lam F.mu F.nu F.order S.G
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))≠0
 exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
   (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.RCN254
end Bundled525

section Bundled526
namespace ProximityPrize.SubmissionLower.RCN250
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN245 RCN249 RCN251 RCN254 RCN102 RCN106 RCN107 RCN109 RCN120 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
def StageFamilySurfaceModNonzero
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):Prop:=
 (indexedFiberSurface W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
     (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0
@[simp] theorem stageFamilySurfaceModNonzero_eq
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W ↔
     (indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
         (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0:=Iff.rfl
theorem properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
   (hPbar:StageFamilySurfaceModNonzero S F W):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=by
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 let tail:=stageTailPlane S F.lam F.mu F.nu F.order
 letI:(Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime:=
   stageFamily_surfacePrime S F W
 have hpower:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   F.component F.injective F.lam F.mu F.nu F.order F.ht F.finite F.generates
     W.q W.irreducible W.monic surface tail surface.natDegree tail.natDegree
     (fun a => stageFamily_surface_mem S F W a)
     (fun a => stageFamily_bar_ne S F W hfirstProper a)
     (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
       (F.component a.1))
     (fun a => stageFamily_tail_mem S F W hfirstProper a)
     Polynomial.natDegree_map_le Polynomial.natDegree_map_le
     (stageFamily_resultant_ne S hfirstProper F W) hPbar
 simpa only [stageFamilyGroupedExponent_eq,stageFamilyResultant] using hpower
end
end ProximityPrize.SubmissionLower.RCN250
end Bundled526

section Bundled527
namespace ProximityPrize.SubmissionLower.RCN255
open RCN135 RCN136 RCN244 RCN249 RCN245 RCN106 RCN103 RCN093 RCN095 RCN125 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem planeSurface_map_adjoinRoot_ne_zero
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega) (hirr:Irreducible surface)
   (hpositive:0 < surface.natDegree):
   surface.map (AdjoinRoot.mk q)≠0:=by
 letI:Fact (Irreducible q):=⟨hq⟩
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap (RatFunc Omega) (AdjoinRoot q))
       (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
 have hs:=RCN360.bimap_specialization_ne_zero
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.bimap_specialization,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
def StageFamilySurfaceSpecializationNonzero
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):Prop:=
 (stageSurfacePlane S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem stageFamily_surface_specialization_ne
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
   StageFamilySurfaceSpecializationNonzero S F q:=by
 change (planeMap (GenericField K) F.order
   (flagAlgHom F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
 exact planeSurface_map_adjoinRoot_ne_zero q hq
   (planeMap (GenericField K) F.order (flagAlgHom F.lam F.mu F.nu S.G))
   (transformedSurface_irreducible F.lam F.mu F.nu F.order S.irreducible_G
     (F.component a.1) (F.ht a.1)) F.positive
end
end ProximityPrize.SubmissionLower.RCN255
end Bundled527

section Bundled528
namespace ProximityPrize.SubmissionLower.RCN252
open RCN135 RCN136 RCN074 RCN244 RCN249 RCN245 RCN106 RCN107 RCN108 RCN103 RCN102 RCN195 RCN255 RCN250 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W:=by
 rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 have hspecial:=stageFamily_surface_specialization_ne S F q hq
   (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
 change surface.map (AdjoinRoot.mk q)≠0 at hspecial
 change (indexedFiberSurface q hq surface).map
   (IsLocalRing.residue (FiberCoefficient q hq))≠0
 subst q
 exact localized_surface_residue_ne_zero (GenericField K)
   (CoordinateField (GenericField K) (F.component a).1) F.order
   (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
   (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.RCN252
end Bundled528

section Bundled529
namespace ProximityPrize.SubmissionLower.RCN253
open RCN135 RCN086 RCN244 RCN249 RCN250 RCN252 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem properStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=
 properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
   (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.RCN253
end Bundled529

section Bundled530
namespace ProximityPrize.SubmissionLower.RCN336
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN066 RCN338
noncomputable section
set_option autoImplicit false
variable {Omega Seed:Type} [Field Omega]
 {G T T' T2 H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
theorem component_secondTail_card_le_mod
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H)
     surfaceFlag firstTailFlag)
   (C:RegularComponent Omega G T H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlagMod C.1 secondTailFlag T2)
   (hproper:T2 ∉ C.1)
   (hzero:∀ gamma ∈ componentSeeds Omega G T H S point C,
     MvPolynomial.aeval (point gamma) T2 = 0) :
   (componentSeeds Omega G T H S point C).card ≤
     B.weightedCost secondTailFlag C:=by
 classical
 let component:=componentSeeds Omega G T H S point C
 let points:=component.image point
 have hpointsPrime:∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T H S point C gamma hgamma
 have hpointsZero:∀ v ∈ points,MvPolynomial.aeval v T2 = 0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound :=
   RCN066.PrimeFlagZeroBudget.zero_le_congr
     (B.primeBudget C) secondTailFlag T2 hT2flag hproper
     points hpointsPrime hpointsZero
 have hcard:points.card = component.card :=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
def transportedMultiplicity
   (h:G ∣ T - T')
   (multiplicity:RegularComponent Omega G T H → ℕ) :
   RegularComponent Omega G T' H → ℕ :=
 fun C => multiplicity ((regularComponentEquiv h).symm C)
theorem weightedCertificate_of_congruentCut
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H)
     surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B
     (transportedMultiplicity h multiplicity)) :
   RegularComponentWeightedInertiaResultantCertificate
     (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
 z:=by
   have hz:=C.z
   dsimp only [transportedMultiplicity] at hz
   rw [← (regularComponentEquiv h).sum_comp] at hz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hz
 yz:=by
   have hyz:=C.yz
   dsimp only [transportedMultiplicity] at hyz
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hyz
 all:=by
   have hall:=C.all
   dsimp only [transportedMultiplicity] at hall
   rw [← (regularComponentEquiv h).sum_comp] at hall
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.RCN336
end Bundled530

section Bundled531
namespace ProximityPrize.SubmissionLower.RCN333
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN249 RCN251 RCN252 RCN255 RCN250 RCN247 RCN245 RCN106 RCN107 RCN108 RCN102 RCN103 RCN109 RCN112 RCN113 RCN264 RCN120 RCN243 RCN111 RCN093 RCN095 RCN125 RCN066 RCN336 RCN226 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem finiteDimensional_coordinateField_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega Q):=by
 subst Q
 exact hfinite
theorem flagGenerators_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hgen:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 1))} :
         Set (CoordinateField Omega P)) = ⊤) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 2)),
       flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 1))} :
       Set (CoordinateField Omega Q)) = ⊤:=by
 subst Q
 exact hgen
theorem indexedComponentFactor_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   projectedFactor Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   projectedFactor Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem relationKernel_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   relationKernel Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   relationKernel Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem flagPlaneMap_mem_relation
   {Omega:Type} [Field Omega]
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A:MvPolynomial (Fin 3) Omega} (hA:A ∈ P) :
   flagPlaneMap Omega lam mu nu order A ∈
     relationKernel Omega (CoordinateField Omega P) order
       (flagEvaluation Omega P lam mu nu) ht:=by
 change planeEvaluation Omega (CoordinateField Omega P) order
   (flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom lam mu nu A)) = 0
 rw [← RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation Omega P lam mu nu (flagAlgHom lam mu nu A) = 0
 rw [flagEvaluation_flag]
 change A ∈ RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rw [coordinateEvaluation_ker]
 exact hA
theorem ideal_mem_right_of_sub_mem
   {R:Type} [CommRing R] (P:Ideal R) {A B:R}
   (hA:A ∈ P) (hAB:A - B ∈ P):B ∈ P:=by
 have h:=P.sub_mem hA hAB
 simpa only [sub_sub_cancel] using h
@[simp] theorem flagPlaneMap_apply
   {Omega:Type} [Field Omega] (lam mu nu:Omega)
   (order:Fin 3 ≃ Fin 3) (A:MvPolynomial (Fin 3) Omega) :
   flagPlaneMap Omega lam mu nu order A =
     planeMap Omega order (flagAlgHom lam mu nu A):=rfl
theorem reducedStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1) - Tred)
   {A:Type} [Fintype A]
   (component:A → RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F))
   (hcomponent:Function.Injective component)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (component a).1)) = ⊤)
   (positive:0 < (stageSurfacePlane S lam mu nu order).natDegree)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (hqMonic:q.Monic)
   (a0:IndexedFactorFiber component lam mu nu order ht q) :
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) *
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1) ∣
     flagPlaneResultant lam mu nu order S.G Tred:=by
 let e:=regularComponentEquiv
   (H:=regularitySurface (polynomialEmbedding K) S.F) hd
 let oldComponent:A → StageComponent S:=fun a => e.symm (component a)
 have oldComponent_val (a:A):(oldComponent a).1 = (component a).1 :=
   regularComponentEquiv_symm_val hd (component a)
 have holdInjective:Function.Injective oldComponent :=
   e.symm.injective.comp hcomponent
 have htold:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
       (MvPolynomial.X (order 0))):=by
   intro a
   rw [oldComponent_val a]
   exact ht a
 have hfiniteold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (oldComponent a).1):=by
   intro a
   exact finiteDimensional_coordinateField_congr
     (oldComponent_val a).symm lam mu nu order (ht a) (htold a) (hfinite a)
 have hgenold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (oldComponent a).1)) = ⊤:=by
   intro a
   exact flagGenerators_congr (oldComponent_val a).symm lam mu nu order
     (ht a) (htold a) (hgen a)
 let surface:=stageSurfacePlane S lam mu nu order
 let oldTail:=stageTailPlane S lam mu nu order
 let redTail:=flagPlaneMap (GenericField K) lam mu nu order Tred
 letI:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime:=by
   exact indexedFiberSurface_span_isPrime component lam mu nu order ht
     S.irreducible_G q hq a0
 have hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   change flagPlaneMap (GenericField K) lam mu nu order S.G ∈ _
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_G_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hfirstProper
   have hsum:=hd.add hr
   simpa only [sub_add_cancel] using hsum
 have hredTailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     redTail ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_T_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperLocal:indexedFiberTail q hq redTail ∉
     Ideal.span {indexedFiberSurface q hq surface}:=by
   exact indexedFiberTail_not_mem_surface component lam mu nu order ht
     S.irreducible_G hproperRed q hq a0
 have hbar:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥:=by
   intro a
   exact indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq
     surface redTail hredTailRoot hproperLocal a
 have hplaneDvd:surface ∣ oldTail-redTail:=by
   simpa only [surface,oldTail,redTail,stageSurfacePlane,stageTailPlane,
     map_sub] using map_dvd (flagPlaneMap (GenericField K) lam mu nu order) hd
 have htail:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberTail q hq redTail ∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a ^
           transportedMultiplicity hd
             (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
             (component a.1):=by
   intro a
   let Q:=Ideal.span {indexedFiberSurface q hq surface} ⊔
     indexedFiberRelation component lam mu nu order ht q hq a ^
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1)
   have hfactorOld:q =
       indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a.1:=a.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a.1).symm
           lam mu nu order (ht a.1) (htold a.1)
   let aold:IndexedFactorFiber oldComponent lam mu nu order htold q :=
     ⟨a.1,hfactorOld⟩
   have hold:=indexedFiberTail_mem_primary S hfirstProper oldComponent
     lam mu nu order htold hfiniteold hgenold q hq aold
   have aold_val:aold.1 = a.1:=rfl
   have hcomponentVal:(oldComponent aold.1).1 = (component a.1).1:=by
     rw [aold_val,oldComponent_val]
   have hrel:indexedFiberRelation oldComponent lam mu nu order htold q hq aold =
       indexedFiberRelation component lam mu nu order ht q hq a:=by
     unfold indexedFiberRelation
     exact congrArg (Ideal.map (fiberLocalizePlane q hq))
       (relationKernel_congr hcomponentVal lam mu nu order
         (htold aold.1) (ht a.1))
   have hmult:localMultiplicity S
       (canonicalLocalDVRFamily S hfirstProper) (oldComponent aold.1) =
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1):=by
     change localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component aold.1)) =
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component a.1))
     rw [aold_val]
   rw [hrel,hmult] at hold
   have holdQ:indexedFiberTail q hq oldTail ∈ Q:=by
     simpa only [oldTail,surface,Q] using hold
   have hfiberDvd:indexedFiberSurface q hq surface ∣
       indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail:=by
     simpa only [indexedFiberSurface,indexedFiberTail,map_sub] using
       map_dvd (fiberLocalizePlane q hq) hplaneDvd
   have hdiff:indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail ∈ Q :=
     (show Ideal.span {indexedFiberSurface q hq surface} ≤ Q from le_sup_left)
       (Ideal.mem_span_singleton.mpr hfiberDvd)
   exact ideal_mem_right_of_sub_mem Q
     (A:=indexedFiberTail q hq oldTail)
     (B:=indexedFiberTail q hq redTail) holdQ hdiff
 have hresultant0:=flagPlaneResultant_ne lam mu nu order
   S.irreducible_G hproperRed (component a0.1) (ht a0.1) positive
 have hresultant:Polynomial.resultant surface redTail surface.natDegree
     redTail.natDegree ≠ 0:=by
   simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
     flagPlaneMap_apply] using hresultant0
 have hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0:=by
   have hfactorA0old:q =
       indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a0.1:=a0.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a0.1).symm
           lam mu nu order (ht a0.1) (htold a0.1)
   let F:StageIndexedFlagFamily S A:={
     component:=oldComponent
     injective:=holdInjective
     lam:=lam
     mu:=mu
     nu:=nu
     order:=order
     ht:=htold
     finite:=hfiniteold
     generates:=hgenold
     positive:=positive }
   let a0old:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q :=
     ⟨a0.1,hfactorA0old⟩
   let W:StageIndexedFactor S A F :=
     { q:=q, irreducible:=hq, monic:=hqMonic, witness:=a0old }
   have hPbar0:=stageFamily_surface_mod_ne S F W
   change (indexedFiberSurface q hq
     (stageSurfacePlane S lam mu nu order)).map
       (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 at hPbar0
   simpa only [surface] using hPbar0
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   component hcomponent lam mu nu order ht hfinite hgen q hq hqMonic
   surface redTail surface.natDegree redTail.natDegree hsurface hbar
   (fun a => transportedMultiplicity hd
     (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
     (component a.1)) htail Polynomial.natDegree_map_le
       Polynomial.natDegree_map_le hresultant hPbar
 simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
   flagPlaneMap_apply] using hpow
end
end ProximityPrize.SubmissionLower.RCN333
end Bundled531

section Bundled532
namespace ProximityPrize.SubmissionLower.RCN331
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN243 RCN264 RCN095 RCN066 RCN336 RCN333 RCN029 RCN031 RCN037 RCN038 RCN341 RCN117 RCN125 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem reducedStage_activeFixedPowers
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1) - Tred)
   (base:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 0) ≠ 0 ∨
       KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 2) ≠ 0)
   (hZ:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G ≠ 0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv) :
   ActiveNestedFixedPowers base hactive hZ hSderiv D
     (transportedMultiplicity hd
       (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))):=by
 refine { z:=?_, u:=?_, v:=?_ }
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (activeNestedZComponent (G:=S.G) (T:=Tred)
       (H:=regularitySurface (polynomialEmbedding K) S.F))
     activeNestedZComponent_injective D.lam D.mu (D.mu * D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D)
     (activeNestedZFinite base hactive hZ hSderiv D)
     (activeNestedZGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D)
     (activeNestedUFinite base hactive hSderiv D)
     (activeNestedUGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D)
     (activeNestedVFinite base hactive hSderiv D)
     (activeNestedVGenerates base hactive hSderiv D)
     (flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional)
     q hq hqMonic a0
end
end ProximityPrize.SubmissionLower.RCN331
end Bundled532

section Bundled533
namespace ProximityPrize.SubmissionLower.RCN334
open scoped Classical BigOperators
open RCN135 RCN136 RCN319 RCN174 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN090 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN037 RCN038 RCN042 RCN341 RCN312 RCN339 RCN330 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
 {tightSupport:ResidualSupportParameters}
def loosenStageGeneral
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport) :
   Stage K I Gamma x p flag stageErrorCap tightSupport:=S
theorem loosenStageGeneral_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStageGeneral S)
     (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStageGeneral S) hfirstProper
def loosenStage
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total) :
   Stage K I Gamma x p flag stageErrorCap fixedSupport :=
 { S with
   surface_s_weight:=S.surface_s_weight.trans hs
   surface_ys_weight:=S.surface_ys_weight.trans hys
   surface_total_weight:=S.surface_total_weight.trans htotal }
theorem loosenStage_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStage S hs hys htotal)
     (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStage S hs hys htotal) hfirstProper
theorem laterTail_in_reduced_delay_secondFlag
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (C:FirstTailComponent S) (delay:ℕ) (hdelay:1 ≤ delay) :
   PolynomialInFlagMod C.1
     (delay • reducedResidualAgreementFlag tightSupport (w + 2))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
 let d:=w + 1 + delay
 let Tred:=reducedGlobalTailCut (polynomialEmbedding K) tightSupport S.F d
 let Hsupport:ResidualSupportData tightSupport S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hred:PolynomialInFlag (reducedResidualAgreementFlag tightSupport d) Tred :=
   reducedGlobalTailCut_in_flag (polynomialEmbedding K) tightSupport Hsupport d
 have hflag:PolynomialInFlag
     (delay • reducedResidualAgreementFlag tightSupport (w + 2)) Tred:=by
   have hscale:d ≤ delay * (w + 2):=by
     dsimp only [d]
     norm_num [w]
     omega
   have hallFlag:(reducedResidualAgreementFlag tightSupport d).all ≤
       (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     simp only [reducedResidualAgreementFlag, reducedAgreementDirection, nsmul_all]
     calc
       (2 * tightSupport.s - 2) * d ≤
           (2 * tightSupport.s - 2) * (delay * (w + 2)) :=
         Nat.mul_le_mul_left _ hscale
       _ = delay * ((2 * tightSupport.s - 2) * (w + 2)):=by ring
   have hysFlag :
       (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_ys]
     simp only [nsmul_yz, nsmul_all]
     rw [← Nat.mul_add]
     rw [reducedResidualAgreementFlag_ys]
     calc
       1 + d * (2 * tightSupport.ys - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.ys - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.ys - 2)):=by ring
   have htotalFlag :
       (reducedResidualAgreementFlag tightSupport d).zOnly +
           (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).zOnly +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_total]
     simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
     rw [← Nat.mul_add, ← Nat.mul_add]
     rw [reducedResidualAgreementFlag_total]
     calc
       1 + d * (2 * tightSupport.total - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.total - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.total - 2)):=by ring
   intro exponent hexponent
   have h:=hred exponent hexponent
   exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag, h.2.2.trans htotalFlag⟩
 refine ⟨Tred, hflag, ?_⟩
 have hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) tightSupport S.F d)
 exact C.1.mem_of_dvd hd
   (regularComponent_G_mem (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) C)
theorem loosenStage_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStage S hs hys htotal)
         (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
structure ReducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) where
 base:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   SeparableLiteralCoordinate C.1
 hactive:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0 ∨
     KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F), LiteralProjectionGate C 2
 data:AdaptiveNestedProjectionDataActive base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, ⟨D⟩⟩ :=
   exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 exact ⟨⟨base, hactive, hZ, D⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
theorem loosenStageGeneral_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStageGeneral S)
         (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
end
end ProximityPrize.SubmissionLower.RCN334
end Bundled533

section Bundled534
namespace ProximityPrize.SubmissionLower.RCN332
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
def reducedFirstCut
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):MvPolynomial (Fin 3) (GenericField K) :=
 reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1)
theorem ordinary_sub_reducedFirstCut_dvd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
     reducedFirstCut S :=
 S.G_dvd_surface.trans
   (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) (support a b s)
     S.F (w + 1))
theorem reducedFirstCut_proper
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ¬ S.G ∣ reducedFirstCut S:=by
 intro hr
 apply hfirstProper
 have h:=(ordinary_sub_reducedFirstCut_dvd S).add hr
 simpa only [reducedFirstCut, sub_add_cancel] using h
theorem reducedFirstCut_in_flag
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   PolynomialInFlag (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S):=by
 exact reducedGlobalTailCut_in_flag (polynomialEmbedding K) (support a b s)
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩ (w + 1)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedMultiplicity
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
theorem reducedFixedPowers
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStage S hs hys htotal)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultants
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicity S hs hys htotal hfirstProper))
   (reducedFixedPowers S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBudgetFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
theorem transportedWeightedResultants
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicity S hs hys htotal hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicity S hs hys htotal hfirstProper)
   (reducedWeightedResultants S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S):SeparableLiteralCoordinate C.1:=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=ordinary_sub_reducedFirstCut_dvd S
 let C':=regularComponentEquiv hd C
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj:U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq:regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C':=by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
noncomputable def reducedMultiplicityGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)
theorem transportedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.RCN332
end Bundled534

section Bundled535
namespace ProximityPrize.SubmissionLower.RCN335
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_delayedTailMultiplicityProvider_of_reducedGeneral
   {a b s:ℕ}
   (agreementCap:ℕ)
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreementCap + stageErrorCap)
   (hagreement:∀ gamma ∈ Gamma, agreementCap ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreementCap)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:stageErrorCap + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 classical
 let supp:=support a b s
 let S0:=loosenStageGeneral S
 let T:=globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let secondFlag:=reducedResidualAgreementFlag supp (w + 2)
 let B:=reducedBudgetFamily S hfirstProper hflagChar hmixed
 let multiplicity:=reducedMultiplicityGeneral S hfirstProper
 have hone:∀ C, 1 ≤ multiplicity C:=by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T H Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     agreementCap bound seedCap slopeCap hnodes hagreement
     hwa (by norm_num [w])
     hshort hchar hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have branchBound (C:FirstTailComponent S) :
     ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
         globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 ∧
         (componentSeeds (GenericField K) S.G T H Gamma
           (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
             multiplicity C * B.weightedCost secondFlag C) ∨
       (∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1)):=by
   have dichotomy:=local_order_tail_dichotomy S0
     (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
   rcases dichotomy.2 with hproper | htangent
   · left
     obtain ⟨delay, hdelay, hdelayMu, htail⟩:=hproper
     have hzero:∀ gamma ∈ componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C,
         MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
           (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0:=by
       intro gamma hgamma
       have hGamma:=componentSeeds_subset (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
       exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected
         gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
         (S.solution gamma hGamma) (by omega)
     have hcount:=component_secondTail_card_le_mod B C Gamma
       (selectedPoint (polynomialEmbedding K) S.selected)
       (selectedPoint_injective (polynomialEmbedding K) S.selected)
       (laterTail_in_reduced_delay_secondFlag S C delay hdelay) htail hzero
     have hscale:B.weightedCost (delay • secondFlag) C =
         delay * B.weightedCost secondFlag C:=by
       simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
         nsmul_all]
       ring
     rw [hscale] at hcount
     exact ⟨delay, hdelay, hdelayMu, htail,
       hcount.trans (Nat.mul_le_mul_right (B.weightedCost secondFlag C) hdelayMu)⟩
   · exact Or.inr htangent
 have providerDichotomy :=
   loosenStageGeneral_dichotomy_with_tangent S hfirstProper B tangentCount
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=fun C => multiplicity C * B.weightedCost secondFlag C
   one_le_multiplicity:=hone
   tangentYZGate:=htangentGate
   cost_le:=fun _ => le_rfl
   divisor_le :=
     (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixed).divisor_le
       B multiplicity
   componentBound:=?_
   dichotomy:=providerDichotomy }⟩
 intro C
 rcases branchBound C with hproper | htangent
 · obtain ⟨_delay, _hdelay, _hdelayMu, _htail, hcount⟩:=hproper
   exact hcount
 · calc
     (componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=tangentCount C htangent
     _ ≤ B.weightedCost secondFlag C :=
       yzCost_mul_le_weightedCost B secondFlag C (stageErrorCap + 1) htangentGate
     _ = 1 * B.weightedCost secondFlag C:=by simp
     _ ≤ multiplicity C * B.weightedCost secondFlag C :=
       Nat.mul_le_mul_right (B.weightedCost secondFlag C) (hone C)
theorem exists_delayedTailMultiplicityProvider_of_reduced
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreements + errors)
   (hagreement:∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:errors + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 exact exists_delayedTailMultiplicityProvider_of_reducedGeneral agreements S
   hfirstProper hflagChar hmixed bound seedCap slopeCap hnodes hagreement
   (by norm_num [agreements, errors, n, w]) hshort hchar hbox htangentGate
end
end ProximityPrize.SubmissionLower.RCN335
end Bundled535

section Bundled536
namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80437
def agreements:ℕ:=181707
def gap:ℕ:=50636
def prime:ℕ:=2130706433
def weightedCap:ℕ:=10539006
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
  6293338251975926 + 6959411943702528 * b + 11154979627669292 * s +
    3479705971851264 * s ^ 2 + 6959411943702528 * b * s
def identitySlackYZ (a b s:ℕ):ℕ:=
  2147532040449620 + 6959411943702528 * a + 6959411943702528 * b +
    8391108819985088 * s + 3479705971851264 * s ^ 2 +
    6959411943702528 * a * s + 6959411943702528 * b * s
def identitySlackAll (a b s:ℕ):ℕ:=
  2863372666115808 + 11154979627669292 * a + 8391108819985088 * b +
    3479705971851264 * b ^ 2 + 8391108819985088 * s +
    3479705971851264 * s ^ 2 + 6959411943702528 * a * b +
    6959411943702528 * a * s + 6959411943702528 * b * s
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
    (hS:s + 2 ≤ 17) (hY:b + s + 3 ≤ 78) (hT:a + b + s + 3 ≤ 2411)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 17) (hY:b + s + 3 ≤ 78)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 154:=by omega
  have hs:2 * (s + 2) - 1 ≤ 33:=by omega
  have hfS:flag.all ≤ 17:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 78:=hfy.trans hY
  calc
    _ ≤ (1 + w * 154) * 17 + 78 * (33 * w) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _ < prime:=by norm_num [w,prime]
theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 17) (hY:b + s + 3 ≤ 78)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 154:=by omega
  have hs:2 * (s + 2) - 2 ≤ 32:=by omega
  have hfS:flag.all ≤ 17:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 78:=hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 154) * 17 + 78 * (32 * (w + 1)) :=
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
    (hS:s + 2 ≤ 17) (hY:b + s + 3 ≤ 78) (hT:a + b + s + 3 ≤ 2411) :
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
end ProximityPrize.SubmissionLower.LocatorFixedStage
end Bundled536

section Bundled537
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
    (hs:p.all ≤ 17) (hy:middle p ≤ 78) (ht:total p ≤ 2411) :
    padSlope p + 2 ≤ 17 ∧ padB p + padSlope p + 3 ≤ 78 ∧
      padA p + padB p + padSlope p + 3 ≤ 2411:=by
  have hp:=pad_sums p
  have hps:padS p ≤ 17:=max_le hs (by decide)
  have hpy:padY p ≤ 78:=max_le hy (by omega)
  have hpt:padT p ≤ 2411:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem regular_factor_count
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 10539006)
    (hS:P.s ≤ 17) (hY:P.ys ≤ 78) (hT:P.total ≤ 2411)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
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
  have hparam:s + 2 ≤ 17 ∧ b + s + 3 ≤ 78 ∧ a + b + s + 3 ≤ 2411:=by
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
    have hnodes:S.nodes.card=181707 + 80437:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀ gamma ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,181707 ≤ (S.agreementFiber gamma).card:=by
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
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 10539006)
    (hS:P.s ≤ 17) (hY:P.ys ≤ 78) (hT:P.total ≤ 2411)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437) :
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
  ⟨262144,131071,181707,D,T,S⟩
def singularProfile (D T S:ℕ):RCN318.TightParameters:=
  ⟨262144,131071,181707,D,T,S⟩
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
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 10539006)
    (hTpos:1 ≤ T) (hT:T ≤ 2411)
    (hSpos:1 ≤ S) (hS:S ≤ 17) :
    SingularGates (singularProfile D T S):=by
  have hkpos:1 ≤ 2*S-1:=by omega
  have hk:2*S-1 ≤ 33:=by omega
  have hDle:D ≤ (2*S-1)*D:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right D hkpos
  have hnum:(2*S-1)*D-1 ≤ 347787197:=by
    have hp:=Nat.mul_le_mul hk hDhigh
    norm_num at hp
    omega
  have hiy:((2*S-1)*D-1)/131071 ≤ 2653:=
    (Nat.div_le_div_right hnum).trans (by decide)
  have halgpos:1 ≤ (2*S-1)*T:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hkpos hTpos
  have halg:(2*S-1)*T ≤ 79563:=by
    have hp:=Nat.mul_le_mul hk hT
    norm_num at hp
    exact hp
  have hmix_le:2*(((2*S-1)*D-1)/131071)*((2*S-1)*T) ≤ 422161278:=
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hiy) halg).trans (by decide)
  have hmix:2*(((2*S-1)*D-1)/131071)*((2*S-1)*T) < 2130706433:=
    hmix_le.trans_lt (by decide)
  refine ⟨hSpos, ?_,by change 1 ≤ 131071; decide,
    by change 131071 < 2130706433; decide, ?_,halgpos, ?_, ?_,hmix,
    by change 131071 < 181707; decide,by change 181707 ≤ 262144; decide⟩
  · exact hS.trans_lt (by decide)
  · change 131071 < (2*S-1)*D
    omega
  · exact hiy.trans_lt (by decide)
  · exact halg.trans_lt (by decide)
theorem fixed_count_le
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 10539006)
    (hS:P.s ≤ 17) (hY:P.ys ≤ 78) (hT:P.total ≤ 2411)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma Q=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437) :
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
end Bundled537

section Bundled538
namespace ProximityPrize.SubmissionLower.LocatorFixedConsumer
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN275 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
def wholeSupport:ResidualSupportParameters:=
  ⟨17,78,2411,by decide,by decide,by decide,by decide⟩
theorem singularProfile_eq:
    LocatorFixed.singularProfile 10539006 2411 17=LocatorArithmetic.fixedSingular:=rfl
theorem regular_sum_count
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 10539006 131071 2411 17)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.Bad 2411 131072 131073
      271826427410824381 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hcell:∀ R,LocatorFactorReplacement.Bad 2411 131072 131073
      271826427410824381 (regularCumulativeFlag H R) →
      LocatorFactorReplacement.cellCost 2411 78 17 131072 131073
        (regularCumulativeFlag H R) (qCost R) ≤ 271826427410824381) :
    (∑ R:RegularIndex H, (regularSeeds H selected Gamma R).card) ≤
      271826427410824381:=by
  have hb:=regularCumulativeFlag_budgets H hH hSupport
  have hs:(∑ R:RegularIndex H, (regularCumulativeFlag H R).all) ≤ 17:=by
    simpa only [wholeSupport] using hb.1
  have hy:(∑ R:RegularIndex H,middle (regularCumulativeFlag H R)) ≤ 78:=by
    simpa only [wholeSupport,middle] using hb.2.1
  have ht:(∑ R:RegularIndex H,total (regularCumulativeFlag H R)) ≤ 2411:=by
    simpa only [wholeSupport,total] using hb.2.2
  have hstage (R:RegularIndex H) :
      (regularSeeds H selected Gamma R).card ≤
        paddedCost 131072 131073 (regularCumulativeFlag H R) :=
    LocatorFixed.regular_factor_count 10539006 wholeSupport
      (by decide) (by decide) (by decide) (by decide) (by decide)
      H hH hbox hSupport selected Gamma u0 u1 hdegree hagreement hno R
  have hzero (R:RegularIndex H) (hz:(regularCumulativeFlag H R).all=0) :
      (regularSeeds H selected Gamma R).card=0:=by
    have hpos:=regularCumulativeFlag_positive H R
    omega
  exact LocatorFactorReplacement.aggregate_of_bad_cells (regularCumulativeFlag H)
    (fun R=> (regularSeeds H selected Gamma R).card) qCost
    2411 78 17 131072 131073 271826427410824381 (by decide)
    hs hy ht hstage hzero hqCost hcell
theorem fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 10539006 131071 2411 17)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437)
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.Bad 2411 131072 131073
      271826427410824381 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hcell:∀ R,LocatorFactorReplacement.Bad 2411 131072 131073
      271826427410824381 (regularCumulativeFlag H R) →
      LocatorFactorReplacement.cellCost 2411 78 17 131072 131073
        (regularCumulativeFlag H R) (qCost R) ≤ 271826427410824381) :
    Gamma.card ≤ 271826427410824381 + LocatorArithmetic.fixedSingular.countCap:=by
  have hg:=LocatorFixed.singular_gates 10539006 2411 17
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 10539006 2411 17) H hH hbox
    hg.s_pos hg.s_small hg.w_pos hg.kD hg.algebraic_pos hg.algebraic_small
    selected Gamma hsolution
  have hreg:=regular_sum_count H hH hbox hSupport selected Gamma u0 u1
    hdegree hagreement hno qCost hqCost hcell
  have hsing:=RCN292.TightParameters.singularSeeds_count_le_countCap
    (LocatorFixed.singularProfile 10539006 2411 17) H hH hbox
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
        simpa only [LocatorFixed.singularProfile,RCN318.TightParameters.errors,
          Nat.reduceSub] using hno)
  have htotal:=hcover.trans (Nat.add_le_add hreg hsing)
  simpa only [singularProfile_eq] using htotal
end
end ProximityPrize.SubmissionLower.LocatorFixedConsumer
end Bundled538

section Bundled539
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN081 RCN095 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259
open RCN319 RCN266 RCN130 RCN140
open LocatorSelection LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
private abbrev regularBound:ℕ:=271826427410824381

theorem gcd_fixed_count_le
    (u0 u1:I→K) (S:SelectedPair u0 u1)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181707≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card≤
      regularBound+LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K→P4→+*Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H≠0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagA:H∈RCN100.globalCoefficientBox K 10539006 131071 52091 17:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
    10539006 131071 52091 17 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H≤2411:=S.common_total_le
  have hYS:wt residualYSWeights H≤78:=S.common_ys_le
  have hS:wt residualSWeights H≤17:=S.common_slope_le
  have hflag:H∈RCN100.globalCoefficientBox K 10539006 131071 2411 17:=
    (mem_flagGlobalCoefficientBox_iff H 10539006 131071 2411 17 (by decide)).mpr
      ⟨hT,hS,hHcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 10539006 131071 2411 17 H hflag
  have hsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta⊆Gamma:=by
    intro gamma hg
    exact (by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg:
        gamma∈Gamma∧phi gamma (gcd12 S.QA S.QB)=0).1
  have hsolution:∀ gamma∈Delta,specialization K (selected gamma) gamma H=0:=
    fun gamma hg=>LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma∈Delta,(selected gamma).natDegree≤131071:=
    fun gamma hg=>hdegree gamma (hsub hg)
  have hagreementD:∀ gamma∈Delta,181707≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80437:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80437 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H):
      (p F).all≤17∧middle (p F)≤78∧total (p F)≤2411:=by
    have hf:=LocatorFixed.factor_support H hH hsupport F
    have hc:=originalCumulativeFlag_cumulative F.1
    exact ⟨by simpa only [p,regularCumulativeFlag,hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight,
      by simpa only [p,regularCumulativeFlag,middle,hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight,
      by simpa only [p,regularCumulativeFlag,total,hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight⟩
  have hfpos (F:RegularIndex H):1≤(p F).all:=by
    have hp:=regularCumulativeFlag_positive H F
    change 1≤(regularCumulativeFlag H F).all
    omega
  let qCost:RegularIndex H→ℕ:=fun F=>
    chosenCost (cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2)
  have hqCost (F:RegularIndex H)
      (hbad:Bad 2411 131072 131073 regularBound (p F)):
      (regularSeeds H selected Delta F).card≤qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=cellOf_bounds (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=cellOf_valid (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hnone:¬noBadFits c:=by
      intro hn
      have hmono:=paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc)
      have hscaled:=Nat.mul_le_mul_left 2411 hmono
      have hright:=Nat.mul_le_mul_left regularBound hc.tlo_le
      have hle:2411*paddedCost 131072 131073 (p F)≤
          regularBound*total (p F):=(hscaled.trans hn).trans hright
      exact (Nat.not_lt_of_ge hle) hbad
    have routes:ordinaryFits c∨sourceFits c∨sourceFits126 c∨sourceFitsX c:=
      (receipt c hv).resolve_left hnone
    by_cases ho:ordinaryFits c
    · have hown:=LocatorFixed.regular_factor_count 10539006
        LocatorFixedConsumer.wholeSupport (by decide) (by decide)
        (by decide) (by decide) (by decide)
        H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
      have hle:=hown.trans
        (paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc))
      simpa only [qCost,c,chosenCost,if_pos ho] using hle
    · have hf:=RCN167.positiveRFactors_spec H F.1 F.2
      have hHcontact:wt (contactWeights 131071) H<10539006:=by omega
      have hcontact:wt (contactWeights 131071) F.1<10539006:=
        (weightedTotalDegree_le_of_dvd (contactWeights 131071)
          F.1 H hf.2.1 hH).trans_lt hHcontact
      have hsources:=routes.resolve_left ho
      by_cases h93:sourceFits c
      · have hdiv93:∀ L,L≤52091→∀ v:RCN180.ConstraintKernel (K:=K)
            16898751 131071 L 28 93 IRSProfile.domain u0 u1,
            F.1∣RCN100.reconstruct K 16898751 131071 L 28 v.1:=by
          intro L hL v
          exact hf.2.1.trans
            (LocatorAuxiliarySelection.common_divides_A93_small S L hL v)
        have hs:=LocatorQuotientReplacement.regularSeeds_count_le_source93
          u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
          hdiv93 hcontact c hc h93
        simpa only [qCost,c,chosenCost,if_neg ho,if_pos h93] using hs
      · have h126:=hsources.resolve_left h93
        have hdiv126:∀ L,L≤52091→∀ v:RCN180.ConstraintKernel (K:=K)
            22895082 131071 L 39 126 IRSProfile.domain u0 u1,
            F.1∣RCN100.reconstruct K 22895082 131071 L 39 v.1:=by
          intro L hL v
          exact hf.2.1.trans
            (LocatorAuxiliarySelection.common_divides_A126_small S L hL v)
        by_cases hs126:sourceFits126 c
        · have hs:=LocatorQuotientReplacement.regularSeeds_count_le_source126
            u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
            hdiv126 hcontact c hc hs126
          simpa only [qCost,c,chosenCost,if_neg ho,if_neg h93] using hs
        · have hX:=h126.resolve_left hs126
          have hs:=LocatorQuotientReplacement.regularSeeds_count_le_sourceX
            u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
            hdiv126 hcontact c hc hX
          simpa only [qCost,c,chosenCost,if_neg ho,if_neg h93] using hs
  have hcell (F:RegularIndex H)
      (hbad:Bad 2411 131072 131073 regularBound (p F)):
      cellCost 2411 78 17 131072 131073 (p F) (qCost F)≤regularBound:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=cellOf_bounds (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=cellOf_valid (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hnone:¬noBadFits c:=by
      intro hn
      have hmono:=paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc)
      have hscaled:=Nat.mul_le_mul_left 2411 hmono
      have hright:=Nat.mul_le_mul_left regularBound hc.tlo_le
      exact (Nat.not_lt_of_ge ((hscaled.trans hn).trans hright)) hbad
    exact cellCost_le_of_cell_bound (p F) c (qCost F) hc
      (by simpa only [qCost,c,exactRest] using chosenCost_with_rest c hv hnone)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
end Bundled539

section Bundled540
namespace ProximityPrize.SubmissionLower.LocatorClosure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238 RCN259 RCN156 RCN234 LocatorSelection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
theorem selected_pair_count
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (seeds:Finset K)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ seeds,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds 131071 80437) :
    seeds.card < LocatorArithmetic.budget:=by
  have hnoResidual:NoLargeSelectedPencil selected seeds LocatorArithmetic.w
      (LocatorArithmetic.n - LocatorArithmetic.agreements):=by
    simpa only [LocatorArithmetic.w,LocatorArithmetic.n,
      LocatorArithmetic.agreements,Nat.reduceSub] using hno
  let phi:=fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  have hparents (gamma:K) (hg:gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA=0 ∧
      specialization K (selected gamma) gamma S.QB=0:=by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi=> (Finset.mem_filter.mp hi).2)
  have hnodes:(Finset.univ:Finset I).card=LocatorArithmetic.n:=by
    norm_num [I,IRSProfile.Index,LocatorArithmetic.n]
  have hfixed:=LocatorFixedBridge.gcd_fixed_count_le u0 u1 S
    selected seeds hdegree hagreement hno
  change (LocatorCover.fixed
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      seeds S.QA S.QB).card ≤
    271826427410824381 + LocatorArithmetic.fixedSingular.countCap at hfixed
  have hresidual:=LocatorResidual.gcd_residual_count_lt
    S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag
    selected seeds (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hnodes hdegree
    (fun gamma hg=> (hparents gamma hg).1)
    (fun gamma hg=> (hparents gamma hg).2) hagreement hnoResidual
  have hpartition:=LocatorCover.partition_card phi seeds S.QA S.QB
  dsimp only [phi] at hpartition
  have hledger:=LocatorArithmetic.ledger_lt
  unfold LocatorArithmetic.ledger LocatorArithmetic.fixedRegularCap at hledger
  omega
theorem selectedNoLargePencilBound6768:
    SelectedNoLargePencilBound IRSProfile.domain 131071 80437
      LocatorArithmetic.budget:=by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩:=exists_selected_pair (U 0) (U 1)
  have hA:∀ gamma ∈ seeds,181707 ≤ (A gamma).card:=by
    intro gamma hg
    have hc:=hcard gamma hg
    simpa [I,IRSProfile.Index] using hc
  have hagreement:∀ gamma ∈ seeds,181707 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =U 0 i + gamma * U 1 i)).card:=by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvalues gamma hg i hi⟩
  have hno':NoLargeSelectedPencil selected seeds 131071 80437:=by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt (selected_pair_count (U 0) (U 1) S selected seeds
    hdegree hagreement hno')
theorem alignmentBound6768:
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol.errors LocatorProtocol.mcaBudget:=by
  have h:=alignmentBound_of_selected_count IRSProfile.domain 131071 80437
    LocatorArithmetic.budget selectedNoLargePencilBound6768
  simpa [IRSProfile.baseCode,IRSProfile.baseDimension,
    LocatorArithmetic.budget,LocatorProtocol.errors,
    LocatorProtocol.mcaBudget] using h
theorem protocolClaim6768:ProtocolClaim 6768 10296009 33554432:=
  LocatorProtocol.protocolClaim6768_of_alignment alignmentBound6768
end
end ProximityPrize.SubmissionLower.LocatorClosure
end Bundled540

section Bundled541
namespace ProximityPrize.Benchmark
theorem candidate:ProtocolClaim 6768 10296009 33554432:=
 ProximityPrize.SubmissionLower.LocatorClosure.protocolClaim6768
end ProximityPrize.Benchmark
end Bundled541

