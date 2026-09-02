import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSelection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
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
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 26320400 131071 3923 45 145 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 14521600 131071 16000 23 80 IRSProfile.domain u0 u1
theorem gateTCap:Fintype.card I * localRankBound 145 3923 45 <
    coefficientCount 26320400 131071 3923 45:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 80 16000 23 <
    coefficientCount 14521600 131071 16000 23:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
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
/-- The selected pair: `QA` is drawn from the total-cap kernel (the smallest
box), `QB` from the B kernel.  Their gcd divides every reconstruction of both
kernels; divisibility of the other source kernels is decided factor by factor
in the fixed stage. -/
structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ globalCoefficientBox K 26320400 131071 3923 45
  QB_flag:QB ∈ globalCoefficientBox K 14521600 131071 16000 23
  common_divides_TCap:∀ v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 26320400 131071 3923 45 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 14521600 131071 16000 23 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181520 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaT,htT,hkT⟩:=exists_nonzero_kernel_array (I:=I)
    K 26320400 131071 3923 45 145 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 14521600 131071 16000 23 80 IRSProfile.domain u0 u1 gateB
  let vT0:TCapKernel u0 u1:=⟨thetaT,LinearMap.mem_ker.mpr hkT⟩
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (TCapKernel u0 u1):=⟨⟨vT0,0,by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT:=Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Module.Finite.finite_basis bT
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=bT.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HT:=commonGCD (TCapKernel u0 u1) bT
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHT:HT ≠ 0:=commonGCD_ne_zero (TCapKernel u0 u1) bT
  have hHB:HB ≠ 0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB ∈ globalCoefficientBox K 14521600 131071 16000 23:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 14521600 16000 23
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA:=commonQuotientLinear (TCapKernel u0 u1) bT hHT vA
  let QA:=submoduleReconstructLinear (TCapKernel u0 u1) vA
  have hQAeq:QA=HT * qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (TCapKernel u0 u1)) HT
    (commonDivisorProof (TCapKernel u0 u1) bT) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (TCapKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ globalCoefficientBox K 26320400 131071 3923 45:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 26320400 131071 3923 45 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 26320400 3923 45
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
  have hQBbox:QB ∈ globalCoefficientBox K 14521600 131071 16000 23:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 14521600 131071 16000 23 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HT HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HT qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHT:gcd QA QB ∣ HT:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_TCap:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    exact hHHT.trans (commonGCD_dvd (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        26320400 131071 3923 45 145 181520 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide) (by decide) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        14521600 131071 16000 23 80 181520 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.LocatorSelection
