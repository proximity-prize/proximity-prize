import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.LocatorArithmetic


namespace ProximityPrize.SubmissionLower.LocatorSelection
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000


section GenericCoefficients
variable {E V:Type*} [Field E] [AddCommGroup V] [Module E V]

def polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E):
    V →ₗ[E] (CoefficientIndex D w L s → E):=
  LinearMap.pi (fun c=>(MvPolynomial.lcoeff E (columnExponent c)).comp f)

@[simp] theorem polynomialCoefficientsLinear_apply (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (c:CoefficientIndex D w L s):
    polynomialCoefficientsLinear D w L s f v c=
      MvPolynomial.coeff (columnExponent c) (f v):=by
  simp only [polynomialCoefficientsLinear,LinearMap.pi_apply,
    LinearMap.comp_apply,MvPolynomial.lcoeff_apply]

theorem reconstruct_polynomialCoefficientsLinear (D w L s:ℕ)
    (f:V →ₗ[E] MvPolynomial (Fin 4) E) (v:V)
    (hbox:f v∈globalCoefficientBox E D w L s):
    reconstruct E D w L s (polynomialCoefficientsLinear D w L s f v)=f v:=by
  let Q:globalCoefficientBox E D w L s:=⟨f v,hbox⟩
  have he:polynomialCoefficientsLinear D w L s f v=encodeBox Q:=by
    funext c
    exact polynomialCoefficientsLinear_apply D w L s f v c
  rw [he]
  exact reconstruct_encodeBox Q

theorem reconstruct_add_generic (D w L s:ℕ)
    (a b:CoefficientIndex D w L s → E):
    reconstruct E D w L s (a+b)=
      reconstruct E D w L s a+reconstruct E D w L s b:=
  (reconstructLinear (K:=E) D w L s).map_add a b

end GenericCoefficients

section GenericJoin
variable {E U V:Type*} [Field E]
variable [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]

def joinLinear (A:Submodule E U) (f:V →ₗ[E] U):(A × V) →ₗ[E] U:=
  A.subtype.comp (LinearMap.fst E A V)+f.comp (LinearMap.snd E A V)

@[simp] theorem joinLinear_apply (A:Submodule E U) (f:V →ₗ[E] U)
    (v:A × V):joinLinear A f v=v.1.1+f v.2:=by
  simp only [joinLinear,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,Submodule.subtype_apply]


variable {LeftRest RightRest:Type*} [AddCommGroup LeftRest] [Module E LeftRest]
variable [AddCommGroup RightRest] [Module E RightRest]

def tripleLinear (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U):
    (V × (LeftRest × RightRest)) →ₗ[E] U:=
  f.comp (LinearMap.fst E V (LeftRest × RightRest))+
    g.comp ((LinearMap.fst E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest)))+
    h.comp ((LinearMap.snd E LeftRest RightRest).comp
      (LinearMap.snd E V (LeftRest × RightRest)))

@[simp] theorem tripleLinear_apply
    (f:V →ₗ[E] U) (g:LeftRest →ₗ[E] U) (h:RightRest →ₗ[E] U)
    (v:V × (LeftRest × RightRest)):
    tripleLinear f g h v=f v.1+g v.2.1+h v.2.2:=by
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

abbrev AKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 16193817 131071 100000 27 89 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 13464522 131071 98880 21 74 IRSProfile.domain u0 u1
abbrev Aux23Kernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 14738193 131071 70548 23 81 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 8187885 131071 62248 13 45 IRSProfile.domain u0 u1
abbrev ThinKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 14738193 131071 62316 24 81 IRSProfile.domain u0 u1
abbrev TradeKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 16193817 131071 2748 27 89 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 15829911 131071 1471 27 87 IRSProfile.domain u0 u1
abbrev Ambient:=CoefficientIndex 16193817 131071 100000 27 → K

theorem gateA:Fintype.card I*localRankBound 89 100000 27<
    coefficientCount 16193817 131071 100000 27:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateB:Fintype.card I*localRankBound 87 1471 27<
    coefficientCount 15829911 131071 1471 27:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega

theorem auxBox_le_aBox:globalCoefficientBox K 13464522 131071 98880 21≤
    globalCoefficientBox K 16193817 131071 100000 27:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩

def embedAux (u0 u1:I → K):AuxKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 13464522 131071 98880 21 74
      IRSProfile.domain u0 u1)

@[simp] theorem reconstruct_embedAux (u0 u1:I → K) (v:AuxKernel u0 u1):
    reconstruct K 16193817 131071 100000 27 (embedAux u0 u1 v)=
      reconstruct K 13464522 131071 98880 21 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 13464522 131071 98880 21 74
      IRSProfile.domain u0 u1 v∈globalCoefficientBox K 16193817 131071 100000 27:=by
    rw [kernelReconstructLinear_apply]
    exact auxBox_le_aBox (reconstruct_mem_globalCoefficientBox
      K 13464522 131071 98880 21 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 13464522 131071 98880 21 74
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedAux,kernelReconstructLinear_apply] using h

theorem aux23Box_le_aBox:globalCoefficientBox K 14738193 131071 70548 23≤
    globalCoefficientBox K 16193817 131071 100000 27:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩
def embedAux23 (u0 u1:I → K):Aux23Kernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 14738193 131071 70548 23 81
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedAux23 (u0 u1:I → K) (v:Aux23Kernel u0 u1):
    reconstruct K 16193817 131071 100000 27 (embedAux23 u0 u1 v)=
      reconstruct K 14738193 131071 70548 23 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 14738193 131071 70548 23 81
      IRSProfile.domain u0 u1 v∈globalCoefficientBox K 16193817 131071 100000 27:=by
    rw [kernelReconstructLinear_apply]
    exact aux23Box_le_aBox (reconstruct_mem_globalCoefficientBox
      K 14738193 131071 70548 23 v.1)
  simpa only [embedAux23,kernelReconstructLinear_apply] using
    reconstruct_polynomialCoefficientsLinear 16193817 131071 100000 27
      (kernelReconstructLinear (K:=K) 14738193 131071 70548 23 81
        IRSProfile.domain u0 u1) v hbox

theorem cBox_le_aBox:globalCoefficientBox K 8187885 131071 62248 13≤
    globalCoefficientBox K 16193817 131071 100000 27:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩

def embedC (u0 u1:I → K):CKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 8187885 131071 62248 13 45
      IRSProfile.domain u0 u1)

@[simp] theorem reconstruct_embedC (u0 u1:I → K) (v:CKernel u0 u1):
    reconstruct K 16193817 131071 100000 27 (embedC u0 u1 v)=
      reconstruct K 8187885 131071 62248 13 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 8187885 131071 62248 13 45
      IRSProfile.domain u0 u1 v∈globalCoefficientBox K 16193817 131071 100000 27:=by
    rw [kernelReconstructLinear_apply]
    exact cBox_le_aBox (reconstruct_mem_globalCoefficientBox
      K 8187885 131071 62248 13 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 8187885 131071 62248 13 45
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedC,kernelReconstructLinear_apply] using h

theorem thinBox_le_aBox:globalCoefficientBox K 14738193 131071 62316 24≤
    globalCoefficientBox K 16193817 131071 100000 27:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs.trans (by decide),hc.trans_le (by decide)⟩

def embedThin (u0 u1:I → K):ThinKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 14738193 131071 62316 24 81
      IRSProfile.domain u0 u1)

@[simp] theorem reconstruct_embedThin (u0 u1:I → K) (v:ThinKernel u0 u1):
    reconstruct K 16193817 131071 100000 27 (embedThin u0 u1 v)=
      reconstruct K 14738193 131071 62316 24 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 14738193 131071 62316 24 81
      IRSProfile.domain u0 u1 v∈globalCoefficientBox K 16193817 131071 100000 27:=by
    rw [kernelReconstructLinear_apply]
    exact thinBox_le_aBox (reconstruct_mem_globalCoefficientBox
      K 14738193 131071 62316 24 v.1)
  have h:=reconstruct_polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 14738193 131071 62316 24 81
      IRSProfile.domain u0 u1) v hbox
  simpa only [embedThin,kernelReconstructLinear_apply] using h

theorem tradeBox_le_aBox:globalCoefficientBox K 16193817 131071 2748 27≤
    globalCoefficientBox K 16193817 131071 100000 27:=by
  intro Q hQ d hd
  obtain ⟨ht,hs,hc⟩:=hQ hd
  exact ⟨ht.trans (by decide),hs,hc⟩
def embedTrade (u0 u1:I → K):TradeKernel u0 u1 →ₗ[K] Ambient:=
  polynomialCoefficientsLinear 16193817 131071 100000 27
    (kernelReconstructLinear (K:=K) 16193817 131071 2748 27 89
      IRSProfile.domain u0 u1)
@[simp] theorem reconstruct_embedTrade (u0 u1:I → K) (v:TradeKernel u0 u1):
    reconstruct K 16193817 131071 100000 27 (embedTrade u0 u1 v)=
      reconstruct K 16193817 131071 2748 27 v.1:=by
  have hbox:kernelReconstructLinear (K:=K) 16193817 131071 2748 27 89
      IRSProfile.domain u0 u1 v∈globalCoefficientBox K 16193817 131071 100000 27:=by
    rw [kernelReconstructLinear_apply]
    exact tradeBox_le_aBox (reconstruct_mem_globalCoefficientBox
      K 16193817 131071 2748 27 v.1)
  simpa only [embedTrade,kernelReconstructLinear_apply] using
    reconstruct_polynomialCoefficientsLinear 16193817 131071 100000 27
      (kernelReconstructLinear (K:=K) 16193817 131071 2748 27 89
        IRSProfile.domain u0 u1) v hbox

abbrev Rest (u0 u1:I → K):=CKernel u0 u1×(ThinKernel u0 u1×TradeKernel u0 u1)
def restMap (u0 u1:I → K):Rest u0 u1→ₗ[K] Ambient:=
  tripleLinear (embedC u0 u1) (embedThin u0 u1) (embedTrade u0 u1)
abbrev AuxRest (u0 u1:I → K):=AuxKernel u0 u1×(Aux23Kernel u0 u1×Rest u0 u1)
def auxMap (u0 u1:I → K):AuxRest u0 u1→ₗ[K] Ambient:=
  tripleLinear (embedAux u0 u1) (embedAux23 u0 u1) (restMap u0 u1)
def joinedMap (u0 u1:I → K):(AKernel u0 u1×AuxRest u0 u1)→ₗ[K] Ambient:=
  joinLinear (AKernel u0 u1) (auxMap u0 u1)
abbrev JoinedKernel (u0 u1:I → K):=LinearMap.range (joinedMap u0 u1)

@[simp] theorem restMap_apply (u0 u1:I → K) (v:Rest u0 u1):
    restMap u0 u1 v=embedC u0 u1 v.1+embedThin u0 u1 v.2.1+
      embedTrade u0 u1 v.2.2:=by simp [restMap,tripleLinear_apply]
@[simp] theorem auxMap_apply (u0 u1:I → K) (v:AuxRest u0 u1):
    auxMap u0 u1 v=embedAux u0 u1 v.1+embedAux23 u0 u1 v.2.1+
      restMap u0 u1 v.2.2:=by simp [auxMap,tripleLinear_apply]
@[simp] theorem joinedMap_apply (u0 u1:I → K)
    (v:AKernel u0 u1×AuxRest u0 u1):
    joinedMap u0 u1 v=v.1.1+(embedAux u0 u1 v.2.1+
      embedAux23 u0 u1 v.2.2.1+(embedC u0 u1 v.2.2.2.1+
        embedThin u0 u1 v.2.2.2.2.1+embedTrade u0 u1 v.2.2.2.2.2)):=by
  simp only [joinedMap,joinLinear_apply,auxMap_apply,restMap_apply]

theorem reconstruct_joinedMap (u0 u1:I → K)
    (v:AKernel u0 u1×AuxRest u0 u1):
    reconstruct K 16193817 131071 100000 27 (joinedMap u0 u1 v)=
      reconstruct K 16193817 131071 100000 27 v.1.1+
        (reconstruct K 13464522 131071 98880 21 v.2.1.1+
          reconstruct K 14738193 131071 70548 23 v.2.2.1.1+
          (reconstruct K 8187885 131071 62248 13 v.2.2.2.1.1+
          reconstruct K 14738193 131071 62316 24 v.2.2.2.2.1.1+
          reconstruct K 16193817 131071 2748 27 v.2.2.2.2.2.1)):=by
  rw [joinedMap_apply,reconstruct_add_generic,reconstruct_add_generic,
    reconstruct_add_generic,reconstruct_add_generic,reconstruct_add_generic,
    reconstruct_embedAux,reconstruct_embedAux23,reconstruct_embedC,
    reconstruct_embedThin,reconstruct_embedTrade]

def includeA (u0 u1:I → K) (v:AKernel u0 u1):JoinedKernel u0 u1:=
  ⟨v.1,⟨(v,(0,(0,(0,(0,0))))),by
    simp only [joinedMap_apply,map_zero,zero_add,add_zero]⟩⟩
def includeAux (u0 u1:I → K) (v:AuxKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedAux u0 u1 v,⟨(0,(v,(0,(0,(0,0))))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeAux23 (u0 u1:I → K) (v:Aux23Kernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedAux23 u0 u1 v,⟨(0,(0,(v,(0,(0,0))))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeC (u0 u1:I → K) (v:CKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedC u0 u1 v,⟨(0,(0,(0,(v,(0,0))))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeThin (u0 u1:I → K) (v:ThinKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedThin u0 u1 v,⟨(0,(0,(0,(0,(v,0))))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩
def includeTrade (u0 u1:I → K) (v:TradeKernel u0 u1):JoinedKernel u0 u1:=
  ⟨embedTrade u0 u1 v,⟨(0,(0,(0,(0,(0,v))))),by
    simp only [joinedMap_apply,ZeroMemClass.coe_zero,map_zero,zero_add,add_zero]⟩⟩

theorem joined_universal (u0 u1:I → K) (v:JoinedKernel u0 u1)
    (gamma:K) (P:Polynomial K) (points:Finset I)
    (hP:P.natDegree≤131071) (hcard:181953≤points.card)
    (hvalues:∀ i∈points,
      P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i):
    RCN319.specialization K P gamma
      (reconstruct K 16193817 131071 100000 27 v.1)=0:=by
  obtain ⟨z,hz⟩:=v.2
  rw [← hz,reconstruct_joinedMap,map_add,map_add,map_add,map_add,map_add]
  have ha:=specialization_eq_zero_of_agreements K
    16193817 131071 100000 27 89 181953 IRSProfile.domain u0 u1
    z.1.1 z.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have haux:=specialization_eq_zero_of_agreements K
    13464522 131071 98880 21 74 181953 IRSProfile.domain u0 u1
    z.2.1.1 z.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have haux23:=specialization_eq_zero_of_agreements K
    14738193 131071 70548 23 81 181953 IRSProfile.domain u0 u1
    z.2.2.1.1 z.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have hc:=specialization_eq_zero_of_agreements K
    8187885 131071 62248 13 45 181953 IRSProfile.domain u0 u1
    z.2.2.2.1.1 z.2.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have hthin:=specialization_eq_zero_of_agreements K
    14738193 131071 62316 24 81 181953 IRSProfile.domain u0 u1
    z.2.2.2.2.1.1 z.2.2.2.2.1.2 (by decide) (by decide) P gamma points hP hcard hvalues
  have htrade:=specialization_eq_zero_of_agreements K
    16193817 131071 2748 27 89 181953 IRSProfile.domain u0 u1
    z.2.2.2.2.2.1 z.2.2.2.2.2.2 (by decide) (by decide) P gamma points hP hcard hvalues
  rw [specialization_eq_ordinary] at ha haux haux23 hc hthin htrade
  simp only [ha,haux,haux23,hc,hthin,htrade,zero_add,add_zero]

private theorem gcd_mul_right_plain_associated
    (P H q:P4) (hc:IsRelPrime q P):
    Associated (gcd P (H*q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H*q)∣P:=gcd_dvd_left P (H*q)
    have hright:gcd P (H*q)∣H*q:=gcd_dvd_right P (H*q)
    have hcop:IsRelPrime (gcd P (H*q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
    (H q P:P4) (hc:IsRelPrime q P):
    Associated (gcd (H*q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H*q) P∣H*q:=gcd_dvd_left (H*q) P
    have hright:gcd (H*q) P∣P:=gcd_dvd_right (H*q) P
    have hcop:IsRelPrime (gcd (H*q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)

structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA≠0
  QB_ne:QB≠0
  QA_flag:QA∈globalCoefficientBox K 16193817 131071 100000 27
  QB_flag:QB∈globalCoefficientBox K 15829911 131071 1471 27
  common_divides_A:∀ v:AKernel u0 u1,
    gcd QA QB∣reconstruct K 16193817 131071 100000 27 v.1
  common_divides_Aux:∀ v:AuxKernel u0 u1,
    gcd QA QB∣reconstruct K 13464522 131071 98880 21 v.1
  common_divides_Aux23:∀ v:Aux23Kernel u0 u1,
    gcd QA QB∣reconstruct K 14738193 131071 70548 23 v.1
  common_divides_C:∀ v:CKernel u0 u1,
    gcd QA QB∣reconstruct K 8187885 131071 62248 13 v.1
  common_divides_Thin:∀ v:ThinKernel u0 u1,
    gcd QA QB∣reconstruct K 14738193 131071 62316 24 v.1
  common_divides_Trade:∀ v:TradeKernel u0 u1,
    gcd QA QB∣reconstruct K 16193817 131071 2748 27 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB∣reconstruct K 15829911 131071 1471 27 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree≤131071 → 181953≤points.card →
      (∀ i∈points,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0

theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaA,htA,hkA⟩:=exists_nonzero_kernel_array (I:=I)
    K 16193817 131071 100000 27 89 IRSProfile.domain u0 u1 gateA
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 15829911 131071 1471 27 87 IRSProfile.domain u0 u1 gateB
  let a0:AKernel u0 u1:=⟨thetaA,LinearMap.mem_ker.mpr hkA⟩
  let vA0:JoinedKernel u0 u1:=includeA u0 u1 a0
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (JoinedKernel u0 u1):=⟨⟨vA0,0,by
    intro h
    exact htA (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bA:=Module.Free.chooseBasis K (JoinedKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)):=
    Module.Finite.finite_basis bA
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (JoinedKernel u0 u1)):=bA.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HA:=commonGCD (JoinedKernel u0 u1) bA
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHA:HA≠0:=commonGCD_ne_zero (JoinedKernel u0 u1) bA
  have hHB:HB≠0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB∈globalCoefficientBox K 15829911 131071 1471 27:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card<ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 15829911 1471 27
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (JoinedKernel u0 u1) bA hHA HB hHB hcardHB
  let qA:=commonQuotientLinear (JoinedKernel u0 u1) bA hHA vA
  let QA:=submoduleReconstructLinear (JoinedKernel u0 u1) vA
  have hQAeq:QA=HA*qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (JoinedKernel u0 u1)) HA
    (commonDivisorProof (JoinedKernel u0 u1) bA) vA
  have hQA:QA≠0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (JoinedKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA∈globalCoefficientBox K 16193817 131071 100000 27:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 16193817 131071 100000 27 vA.1
  have hcardQA:(normalizedFactorSet QA).card<ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 16193817 100000 27
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB:=submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq:QB=HB*qB:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB:QB≠0:=by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB∈globalCoefficientBox K 15829911 131071 1471 27:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 15829911 131071 1471 27 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HA HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HA qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHA:gcd QA QB∣HA:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HA HB)
  have hHHB:gcd QA QB∣HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HA HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_A:=?_,common_divides_Aux:=?_,common_divides_Aux23:=?_
    common_divides_C:=?_,common_divides_Thin:=?_,common_divides_Trade:=?_
    common_divides_B:=?_
    universal_vanishing:=?_ }⟩
  · intro v
    exact hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeA u0 u1 v))
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeAux u0 u1 v))
    change gcd QA QB∣reconstruct K 16193817 131071 100000 27 (embedAux u0 u1 v) at h
    simpa only [reconstruct_embedAux] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeAux23 u0 u1 v))
    change gcd QA QB∣reconstruct K 16193817 131071 100000 27 (embedAux23 u0 u1 v) at h
    simpa only [reconstruct_embedAux23] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeC u0 u1 v))
    change gcd QA QB∣reconstruct K 16193817 131071 100000 27 (embedC u0 u1 v) at h
    simpa only [reconstruct_embedC] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeThin u0 u1 v))
    change gcd QA QB∣reconstruct K 16193817 131071 100000 27 (embedThin u0 u1 v) at h
    simpa only [reconstruct_embedThin] using h
  · intro v
    have h:=hHHA.trans (commonGCD_dvd (JoinedKernel u0 u1) bA (includeTrade u0 u1 v))
    change gcd QA QB∣reconstruct K 16193817 131071 100000 27 (embedTrade u0 u1 v) at h
    simpa only [reconstruct_embedTrade] using h
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
        15829911 131071 1471 27 87 181953 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues

end
end ProximityPrize.SubmissionLower.LocatorSelection
