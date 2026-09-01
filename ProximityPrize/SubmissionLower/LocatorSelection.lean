import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.LocatorSourceArithmetic
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
  ConstraintKernel (K:=K) 11624192 131071 169536 19 64 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 13077216 131071 169536 21 72 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 39050020 131071 169536 63 215 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 22885128 131071 2919 39 126 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 13985356 131071 4893 23 77 IRSProfile.domain u0 u1
abbrev Ambient:=CoefficientIndex 39050020 131071 169536 63 → K
theorem gateC:Fintype.card I * localRankBound 215 169536 63 <
    coefficientCount 39050020 131071 169536 63:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorSourceArithmetic.kernelAmbient_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 77 4893 23 <
    coefficientCount 13985356 131071 4893 23:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem aBox_le_cBox:globalCoefficientBox K 11624192 131071 169536 19 ≤
    globalCoefficientBox K 39050020 131071 169536 63:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedA (u0 u1:I → K):AKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 11624192 131071 169536 19 64
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedA (u0 u1:I → K) (v:AKernel u0 u1) :
    reconstruct K 39050020 131071 169536 63 (embedA u0 u1 v) =
      reconstruct K 11624192 131071 169536 19 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 11624192 131071 169536 19 64
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 39050020 131071 169536 63:=by
    rw [kernelReconstructLinear_apply]
    exact aBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 11624192 131071 169536 19 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 11624192 131071 169536 19 64
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedA,kernelReconstructLinear_apply] using h
theorem auxBox_le_cBox:globalCoefficientBox K 13077216 131071 169536 21 ≤
    globalCoefficientBox K 39050020 131071 169536 63:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht,hs.trans (by decide),hc.trans_le (by decide)⟩
def embedAux (u0 u1:I → K):AuxKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 13077216 131071 169536 21 72
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedAux (u0 u1:I → K) (v:AuxKernel u0 u1) :
    reconstruct K 39050020 131071 169536 63 (embedAux u0 u1 v) =
      reconstruct K 13077216 131071 169536 21 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 13077216 131071 169536 21 72
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 39050020 131071 169536 63:=by
    rw [kernelReconstructLinear_apply]
    exact auxBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 13077216 131071 169536 21 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 13077216 131071 169536 21 72
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedAux,kernelReconstructLinear_apply] using h
theorem tcapBox_le_cBox:globalCoefficientBox K 22885128 131071 2919 39 ≤
    globalCoefficientBox K 39050020 131071 169536 63:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩
def embedTCap (u0 u1:I → K):TCapKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 22885128 131071 2919 39 126
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedTCap (u0 u1:I → K) (v:TCapKernel u0 u1) :
    reconstruct K 39050020 131071 169536 63 (embedTCap u0 u1 v) =
      reconstruct K 22885128 131071 2919 39 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 22885128 131071 2919 39 126
      IRSProfile.domain u0 u1 v ∈ globalCoefficientBox K 39050020 131071 169536 63:=by
    rw [kernelReconstructLinear_apply]
    exact tcapBox_le_cBox (reconstruct_mem_globalCoefficientBox
      K 22885128 131071 2919 39 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 39050020 131071 169536 63
    (kernelReconstructLinear (K:=K) 22885128 131071 2919 39 126
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedTCap,kernelReconstructLinear_apply] using h
def joinedMap (u0 u1:I → K) :
    (CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TCapKernel u0 u1))) →ₗ[K]
      Ambient:=
  joinLinear (CKernel u0 u1)
    (tripleLinear (embedA u0 u1) (embedAux u0 u1) (embedTCap u0 u1))
abbrev JoinedKernel (u0 u1:I → K):=LinearMap.range (joinedMap u0 u1)
@[simp] theorem joinedMap_apply (u0 u1:I → K)
    (v:CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TCapKernel u0 u1))) :
    joinedMap u0 u1 v=
      v.1.1 + (embedA u0 u1 v.2.1 + embedAux u0 u1 v.2.2.1 +
        embedTCap u0 u1 v.2.2.2):=by
  simp only [joinedMap,joinLinear_apply,tripleLinear_apply]
theorem reconstruct_joinedMap (u0 u1:I → K)
    (v:CKernel u0 u1 × (AKernel u0 u1 × (AuxKernel u0 u1 × TCapKernel u0 u1))) :
    reconstruct K 39050020 131071 169536 63 (joinedMap u0 u1 v) =
      reconstruct K 39050020 131071 169536 63 v.1.1 +
        (reconstruct K 11624192 131071 169536 19 v.2.1.1 +
          reconstruct K 13077216 131071 169536 21 v.2.2.1.1 +
          reconstruct K 22885128 131071 2919 39 v.2.2.2.1):=by
  rw [joinedMap_apply,reconstruct_add_generic,reconstruct_add_generic,
    reconstruct_add_generic,reconstruct_embedA,reconstruct_embedAux,
    reconstruct_embedTCap]
def includeC (u0 u1:I → K) (v:CKernel u0 u1):JoinedKernel u0 u1:=
  ⟨v.1, ⟨(v, (0, (0,0))),by
    simp only [joinedMap_apply,map_zero,zero_add,add_zero]⟩⟩
def includeA (u0 u1:I → K) (v:AKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedA u0 u1 v, ⟨(0, (v, (0,0))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeAux (u0 u1:I → K) (v:AuxKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedAux u0 u1 v, ⟨(0, (0, (v,0))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeTCap (u0 u1:I → K) (v:TCapKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedTCap u0 u1 v, ⟨(0, (0, (0,v))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
theorem joined_universal (u0 u1:I → K) (v:JoinedKernel u0 u1)
    (gamma:K) (P:Polynomial K) (points:Finset I)
    (hP:P.natDegree ≤ 131071) (hcard:181628 ≤ points.card)
    (hvalues:∀ i ∈ points,
      P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (reconstruct K 39050020 131071 169536 63 v.1) =0:=by
  obtain ⟨z,hz⟩:=v.2
  rw [← hz,reconstruct_joinedMap,map_add,map_add,map_add]
  have hc:=specialization_eq_zero_of_agreements K
    39050020 131071 169536 63 215 181628 IRSProfile.domain u0 u1
    z.1.1 z.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have ha:=specialization_eq_zero_of_agreements K
    11624192 131071 169536 19 64 181628 IRSProfile.domain u0 u1
    z.2.1.1 z.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have haux:=specialization_eq_zero_of_agreements K
    13077216 131071 169536 21 72 181628 IRSProfile.domain u0 u1
    z.2.2.1.1 z.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have htcap:=specialization_eq_zero_of_agreements K
    22885128 131071 2919 39 126 181628 IRSProfile.domain u0 u1
    z.2.2.2.1 z.2.2.2.2 (by decide) (by decide) P gamma points hP hcard hvalues
  rw [specialization_eq_ordinary] at ha haux hc htcap
  rw [hc,ha,haux,htcap,zero_add,zero_add,zero_add]
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
  QA_flag:QA ∈ globalCoefficientBox K 39050020 131071 169536 63
  QB_flag:QB ∈ globalCoefficientBox K 13985356 131071 4893 23
  common_divides_A:∀ v:AKernel u0 u1,
    gcd QA QB ∣ reconstruct K 11624192 131071 169536 19 v.1
  common_divides_Aux:∀ v:AuxKernel u0 u1,
    gcd QA QB ∣ reconstruct K 13077216 131071 169536 21 v.1
  common_divides_C:∀ v:CKernel u0 u1,
    gcd QA QB ∣ reconstruct K 39050020 131071 169536 63 v.1
  common_divides_TCap:∀ v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 22885128 131071 2919 39 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 13985356 131071 4893 23 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181628 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaC,htC,hkC⟩:=exists_nonzero_kernel_array (I:=I)
    K 39050020 131071 169536 63 215 IRSProfile.domain u0 u1 gateC
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 13985356 131071 4893 23 77 IRSProfile.domain u0 u1 gateB
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
  have hHBbox:HB ∈ globalCoefficientBox K 13985356 131071 4893 23:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 13985356 4893 23
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
  have hQAbox:QA ∈ globalCoefficientBox K 39050020 131071 169536 63:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 39050020 131071 169536 63 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 39050020 169536 63
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
  have hQBbox:QB ∈ globalCoefficientBox K 13985356 131071 4893 23:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 13985356 131071 4893 23 vB.1
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
    common_divides_TCap:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeA u0 u1 v))
    change gcd QA QB ∣ reconstruct K 39050020 131071 169536 63 (embedA u0 u1 v) at h
    simpa only [reconstruct_embedA] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeAux u0 u1 v))
    change gcd QA QB ∣ reconstruct K 39050020 131071 169536 63 (embedAux u0 u1 v) at h
    simpa only [reconstruct_embedAux] using h
  · intro v
    exact hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeC u0 u1 v))
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeTCap u0 u1 v))
    change gcd QA QB ∣ reconstruct K 39050020 131071 169536 63 (embedTCap u0 u1 v) at h
    simpa only [reconstruct_embedTCap] using h
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
        13985356 131071 4893 23 77 181628 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.LocatorSelection
