import ProximityPrize.SubmissionLower.R6966ProofGlobalPrimitive
import ProximityPrize.SubmissionLower.R6966ProofFixedNodeRows
import Mathlib.Algebra.MvPolynomial.Equiv

set_option Elab.async false

-- merged module R6966ProofPhysicalPrimitiveCoeffs
section Merged_R6966ProofPhysicalPrimitiveCoeffs

namespace Research6966.PhysicalPrimitiveCoeffs
open Polynomial Finset
open K1_14 (L FX Jet Seeds)
open K1_14_1 (SeedPoly Source RawSource jetConstant)
open K1_14_1_4 (doubleMap centerBase evalRaw)
open GlobalPrimitive (Clears)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 24
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

abbrev R:=SeedPoly[X]
abbrev k:=K1_14_1.SeedField
def rawCoeff : R→+*k[X]:=mapRingHom (algebraMap SeedPoly k)
def phys : L[X]→+*R:=mapRingHom MvPolynomial.C
def seeds : SeedPoly→+*R:=C

theorem physical_only (P:L[X]) : centerBase (phys P)=MvPolynomial.C (algebraMap L[X] FX P) := by
  have eq:centerBase.comp phys=MvPolynomial.C.comp (algebraMap L[X] FX) := by
    apply Polynomial.ringHom_ext
    · intro c
      change centerBase ((C c).map MvPolynomial.C)=_
      rw [Polynomial.map_C]
      simp only [centerBase,coe_eval₂RingHom,eval₂_C,RingHom.comp_apply]
      change MvPolynomial.map (algebraMap L FX) (MvPolynomial.C c)=_
      rw [MvPolynomial.map_C];rfl
    · change centerBase (Polynomial.X.map MvPolynomial.C)=_
      rw [Polynomial.map_X];simp only [centerBase,coe_eval₂RingHom,eval₂_X,RingHom.comp_apply]
  exact RingHom.congr_fun eq P

theorem seed_only (i:Fin 2) : centerBase (seeds (MvPolynomial.X i))=MvPolynomial.X i := by
  change (eval₂RingHom _ _ (C (MvPolynomial.X i)):Seeds)=_
  rw [coe_eval₂RingHom,eval₂_C]
  exact MvPolynomial.map_X _ _

theorem native_clears : Clears centerBase := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c=>
    obtain ⟨n,d,nd,id⟩:=IsFractionRing.div_surjective L[X] c
    have nz:algebraMap L[X] FX d≠0:=(map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (nonZeroDivisors.ne_zero nd)
    refine ⟨phys n,phys d,physical_only d ▸ nz.isUnit.map MvPolynomial.C,?_⟩
    rw [physical_only,physical_only,←map_mul MvPolynomial.C]
    apply congrArg MvPolynomial.C
    rw [←id,mul_comm,div_mul_cancel₀ _ nz]
  | add A B ha hb=>
    obtain ⟨a,d,du,first⟩:=ha
    obtain ⟨b,e,eu,second⟩:=hb
    refine ⟨e*a+d*b,d*e,(map_mul centerBase _ _) ▸ du.mul eu,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,first,second];ring
  | mul_X P i ih=>
    obtain ⟨p,d,du,eq⟩:=ih
    exact ⟨p*seeds (MvPolynomial.X i),d,du,by rw [map_mul,eq,seed_only,mul_assoc]⟩

theorem raw_clears : Clears rawCoeff :=
  GlobalPrimitive.lift_clear _ (GlobalPrimitive.clear_localization (nonZeroDivisors SeedPoly))

theorem global_native {N:Jet} (prime:Prime N) :
    ∃ P:Source,Prime P ∧ Associated (doubleMap centerBase P) N :=
  GlobalPrimitive.global_prime (doubleMap centerBase)
    (map_injective _ (map_injective _ PadeRawField.center_injective))
    (GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ native_clears)) prime

theorem global_raw {N:RawSource} (prime:Prime N) :
    ∃ P:Source,Prime P ∧ Associated (doubleMap rawCoeff P) N :=
  GlobalPrimitive.global_prime (doubleMap rawCoeff)
    (map_injective _ (map_injective _ (map_injective _ (IsFractionRing.injective SeedPoly k))))
    (GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ raw_clears)) prime

/-- Transpose the abscissa and the two seeds. This permits specialization at
a fixed physical coordinate without evaluating any rational coefficients. -/
def transpose : R≃ₐ[L]MvPolynomial (Fin 2) L[X] :=
  (MvPolynomial.optionEquivLeft L (Fin 2)).symm.trans (MvPolynomial.optionEquivRight L (Fin 2))

theorem transpose_agrees (P:R) :
    MvPolynomial.map (algebraMap L[X] FX) (transpose P)=centerBase P := by
  have eq:(MvPolynomial.map (algebraMap L[X] FX)).comp transpose.toRingHom=centerBase := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        have calc₀:(MvPolynomial.optionEquivLeft L (Fin 2)).symm (C (MvPolynomial.C c))=MvPolynomial.C c :=
          (MvPolynomial.optionEquivLeft L (Fin 2)).symm_apply_eq.mpr (MvPolynomial.optionEquivLeft_C L _ c).symm
        change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.C c))))=_
        rw [calc₀,MvPolynomial.optionEquivRight_C,MvPolynomial.map_C]
        change _=centerBase (C (MvPolynomial.C c))
        exact (physical_only (C c)).symm.trans (congrArg centerBase (Polynomial.map_C ..))
      · intro i
        change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.X i))))=_
        rw [MvPolynomial.optionEquivLeft_symm_C_X,MvPolynomial.optionEquivRight_X_some,MvPolynomial.map_X]
        exact (seed_only i).symm
    · change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm Polynomial.X))=_
      rw [MvPolynomial.optionEquivLeft_symm_X,MvPolynomial.optionEquivRight_X_none,MvPolynomial.map_C]
      simp only [centerBase,coe_eval₂RingHom,eval₂_X]
  exact RingHom.congr_fun eq P

end
end Research6966.PhysicalPrimitiveCoeffs

end Merged_R6966ProofPhysicalPrimitiveCoeffs

-- merged module R6966ProofRegularPhysicalChart
section Merged_R6966ProofRegularPhysicalChart

namespace Research6966.RegularPhysicalChart
open Polynomial
open K1_14_1 (jetConstant)
open K1_14_1_4 (substitute doubleMap)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 650000
variable {R:Type*} [CommRing R]

abbrev yVar (R:Type*) [CommRing R] : R[X][X]:=C (Polynomial.X:R[X])
abbrev vVar (R:Type*) [CommRing R] : R[X][X]:=Polynomial.X

def transform (a b u d:R) : R[X][X]→+*R[X][X] :=
  substitute (RingHom.id R) (jetConstant a*yVar R+jetConstant b)
    (jetConstant a*vVar R+jetConstant u*yVar R+jetConstant d)

private theorem onC (a b u d c:R) : transform a b u d (jetConstant c)=jetConstant c := by
  simp [transform,substitute,jetConstant]
private theorem onY (a b u d:R) : transform a b u d (yVar R)=jetConstant a*yVar R+jetConstant b := by
  simp [transform,substitute,yVar]
private theorem onV (a b u d:R) : transform a b u d (vVar R)=jetConstant a*vVar R+jetConstant u*yVar R+jetConstant d := by
  simp [transform,substitute,vVar]

private theorem ext {S:Type*} [CommRing S] {f g:R[X][X]→+*S} (c:∀ r,f (jetConstant r)=g (jetConstant r))
    (y:f (yVar R)=g (yVar R)) (v:f (vVar R)=g (vVar R)) : f=g :=
  Polynomial.ringHom_ext' (Polynomial.ringHom_ext c y) v

theorem comp (a b u d s t v j:R) : (transform a b u d).comp (transform s t v j) =
    transform (s*a) (s*b+t) (s*u+v*a) (s*d+v*b+j) := by
  apply ext
  · intro c;simp only [RingHom.comp_apply,onC]
  · simp only [RingHom.comp_apply,onY,map_add,map_mul,onC,onY]
    ring
  · simp only [RingHom.comp_apply,onV,map_add,map_mul,onC,onV,onY]
    ring

private theorem identity : transform (1:R) 0 0 0=RingHom.id _ := by
  apply ext
  · intro c;rw [onC];rfl
  · rw [onY];simp
  · rw [onV];simp

theorem bijective (a:Rˣ) (b u d:R) : Function.Bijective (transform (↑a:R) b u d) := by
  let s:R:=↑a⁻¹
  let p:R:=↑a
  have ps:p*s=1:=Units.mul_inv a
  have sp:s*p=1:=Units.inv_mul a
  let inv:=transform s (-s*b) (-s^2*u) (s^2*u*b-s*d)
  have li:inv.comp (transform p b u d)=RingHom.id _ := by
    dsimp only [inv];rw [comp,ps]
    have db:p*(-s*b)+b=0:=by linear_combination -b*ps
    have uv:p*(-s^2*u)+u*s=0:=by linear_combination -(s*u)*ps
    have dt:p*(s^2*u*b-s*d)+u*(-s*b)+d=0:=by linear_combination (s*u*b-d)*ps
    rw [db,uv,dt,identity]
  have ri:(transform p b u d).comp inv=RingHom.id _ := by
    dsimp only [inv];rw [comp,sp]
    have db:s*b+-s*b=0:=by ring
    have uv:s*u+-s^2*u*p=0:=by linear_combination -(s*u)*sp
    have dt:s*d+-s^2*u*b+(s^2*u*b-s*d)=0:=by ring
    rw [db,uv,dt,identity]
  exact ⟨(show Function.LeftInverse inv (transform p b u d) from RingHom.congr_fun li).injective,
    (show Function.RightInverse inv (transform p b u d) from RingHom.congr_fun ri).surjective⟩

theorem maps {S:Type*} [CommRing S] (f:R→+*S) (a b u d:R) :
    (doubleMap f).comp (transform a b u d)=
    (transform (f a) (f b) (f u) (f d)).comp (doubleMap f) := by
  have c (v:R):doubleMap f (jetConstant v)=jetConstant (f v):=by simp [doubleMap,jetConstant]
  have y:doubleMap f (yVar R)=yVar S:=by simp [doubleMap,yVar]
  have v:doubleMap f (vVar R)=vVar S:=by simp [doubleMap,vVar]
  apply ext
  · intro j;simp only [RingHom.comp_apply,onC,c]
  · simp only [RingHom.comp_apply,onY,y,map_add,map_mul,c]
  · simp only [RingHom.comp_apply,onV,v,y,map_add,map_mul,c,onV]

theorem comparison {S F:Type*} [IsDomain R] [CommRing S] [IsDomain S] [Field F]
    (inc:R→+*S) (inj:Function.Injective inc) (localizes:GlobalPrimitive.Clears inc)
    (gen:S→+*F) (faithful:Function.Injective gen) (clears:GlobalPrimitive.Clears gen)
    (a:Sˣ) (b u d:S) {P Q:R[X][X]} (pp:Prime P) (qp:Prime Q) (pSlope:0<P.natDegree) (qSlope:0<Q.natDegree)
    (generic:Associated (doubleMap gen (transform (↑a:S) b u d (doubleMap inc P)))
      (doubleMap gen (doubleMap inc Q))) :
    ∃ c:S,IsUnit c ∧ transform (↑a:S) b u d (doubleMap inc P)=jetConstant c*doubleMap inc Q := by
  let φ:=doubleMap inc
  have ij:Function.Injective φ:=map_injective _ (map_injective _ inj)
  have cl:GlobalPrimitive.Clears φ:=GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ localizes)
  have degree (g:R[X][X]):(φ g).natDegree=g.natDegree:=natDegree_map_eq_of_injective (map_injective _ inj) _
  have pprime:=GlobalPrimitive.prime_image φ ij cl pp (fun unit=>pSlope.ne' ((degree P).symm.trans (natDegree_eq_zero_of_isUnit unit)))
  have qprime:=GlobalPrimitive.prime_image φ ij cl qp (fun unit=>qSlope.ne' ((degree Q).symm.trans (natDegree_eq_zero_of_isUnit unit)))
  let eqv:=RingEquiv.ofBijective (transform (↑a:S) b u d) (bijective a b u d)
  have ir:Irreducible (eqv (φ P)):=(MulEquiv.irreducible_iff eqv).mpr pprime.irreducible
  have pos:0<(φ Q).natDegree:=(degree Q) ▸ qSlope
  have divides:φ Q∣eqv (φ P):=GlobalPrimitive.descend_jet gen faithful clears qprime pos generic.symm.dvd
  obtain ⟨scalar,assoc⟩:=qprime.irreducible.associated_of_dvd ir divides
  obtain ⟨c,unit,id⟩:=GlobalPrimitive.unit_constant scalar.isUnit
  exact ⟨c,unit,assoc.symm.trans (id ▸ mul_comm _ _)⟩

end
end Research6966.RegularPhysicalChart

end Merged_R6966ProofRegularPhysicalChart
