import ProximityPrize.SubmissionLower.R6960NormalizedFiber
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Algebra
open scoped Polynomial TensorProduct

variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]

local instance fibreRing (z : k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)

/-- The `(Polynomial k)` action on the actual quotient of the surface normalization. -/
scoped instance fibreAlgebra (z : k) : Algebra (Polynomial k) (Fiber E z) :=
  @RingHom.toAlgebra (Polynomial k) (Fiber E z) _ (fibreRing (E:=E) z).toCommSemiring (baseMap E z)

/-- Specialize only the scalar coordinate in the original polynomial plane. -/
def fibreBase (z : k) : Plane k→+*(Polynomial k) := evalRingHom (C z)

def genericFibreBase (z : k) : Plane k→+*FractionRing (Polynomial k) :=
  (algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp (fibreBase z)

/-- Taking the scalar fibre of the actual plane normalization is the
same as base-changing its original order by the scalar-coordinate map. -/
def fibreAsTensor (z : k) :
    let : Algebra (Plane k) (Polynomial k) := (fibreBase z).toAlgebra
    { e : Fiber E z ≃ₐ[(Polynomial k)] ((Polynomial k)⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (quotientMap E z x)=(1:(Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let B := Order k E
  let : CommRing B := @Subalgebra.toCommRing A E _ _ (inferInstance : Algebra A E) B
  let : Algebra A R := (fibreBase z).toAlgebra
  let : IsScalarTower A A R := IsScalarTower.of_algebraMap_eq (R:=A) (S:=A) (A:=R) fun a=>by
    change algebraMap A R a=algebraMap A R (algebraMap A A a)
    rw [Algebra.algebraMap_self,RingHom.id_apply]
  let I : Ideal A := Ideal.span {Polynomial.X-C (C z)}
  let : CommRing (A ⧸ I) := Ideal.Quotient.commRing I
  let j := algebraMap A B
  have slice : sliceIdeal E z=I.map j := by
    unfold I sliceIdeal
    rw [Ideal.map_span,Set.image_singleton]
  let eq : Fiber E z ≃+* (B ⧸ I.map j) := Ideal.quotEquivOfEq slice
  let Q := Polynomial.quotientSpanXSubCAlgEquiv (C z)
  let base : (A ⧸ I) ≃ₐ[A] R := {
    Q.toRingEquiv with
    commutes' := fun a=>by
      change Q (Ideal.Quotient.mk I a)=a.eval (C z)
      exact Polynomial.quotientSpanXSubCAlgEquiv_mk (C z) a }
  let tensor := Algebra.TensorProduct.congr base (AlgEquiv.refl (R:=A) (A₁:=B))
  let ring : Fiber E z ≃+* (R⊗[A] B) := eq.trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv.trans tensor.toRingEquiv)
  have apply_q (x : B) : ring (quotientMap E z x)=(1:R) ⊗ₜ[A] x := by
    change tensor ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
      (eq (Ideal.Quotient.mk (sliceIdeal E z) x)))=_
    rw [show eq (Ideal.Quotient.mk (sliceIdeal E z) x)=Ideal.Quotient.mk (I.map j) x from
      Ideal.quotEquivOfEq_mk slice x,Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (base 1) ⊗ₜ[A] x=_
    rw [map_one]
  let e : Fiber E z ≃ₐ[R] (R⊗[A] B) := { ring with
    commutes' := fun c=>by
      change ring (quotientMap E z (j (C c)))=c ⊗ₜ[A] (1:B)
      rw [apply_q,Algebra.algebraMap_eq_smul_one,TensorProduct.tmul_smul]
      change ((C c : A) • (1:R)) ⊗ₜ[A] (1:B)=_
      have h : (C c : A) • (1:R)=c := by
        rw [Algebra.smul_def,mul_one]
        change (C c).eval (C z)=c
        exact eval_C
      rw [h] }
  exact ⟨e,apply_q⟩

/-- The generic abscissa of the actual specialized surface order, with
the same reduction map from original integral elements. -/
def genericFibreAsTensor (z : k) :
    let : Algebra (Plane k) (FractionRing (Polynomial k)) := (genericFibreBase z).toAlgebra
    { e : ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z) ≃ₐ[FractionRing (Polynomial k)]
        ((FractionRing (Polynomial k))⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (1 ⊗ₜ[(Polynomial k)] quotientMap E z x)=(1:FractionRing (Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let K := FractionRing R
  let B := Order k E
  let : Algebra A R := (fibreBase z).toAlgebra
  let : Algebra A K := (genericFibreBase z).toAlgebra
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : SMul A K := (inferInstance : Algebra A K).toSMul
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=K) fun _=>rfl
  let v := fibreAsTensor (E:=E) z
  let c := Algebra.TensorProduct.congr (AlgEquiv.refl (R:=K) (A₁:=K)) v.val
  let d := Algebra.TensorProduct.cancelBaseChange A R K K B
  refine ⟨c.trans d,fun x=>?_⟩
  change d (1 ⊗ₜ[R] v.val (quotientMap E z x))=_
  rw [v.property,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]

#print axioms fibreAsTensor
#print axioms genericFibreAsTensor
end
end Lower6960.CollisionMarked
