import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedFibreQuotient
open Algebra
open scoped TensorProduct
variable {k A S : Type*} [Field k] [CommRing A] [CommRing S]
  [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]

/-- Specializing the finite algebra at a scalar-valued point is its quotient by
the extended point ideal, with the original scalar action on that quotient. -/
def atPoint (φ : A →ₐ[k] k) :
    letI := φ.toRingHom.toAlgebra
    (S ⧸ (RingHom.ker φ.toRingHom).map (algebraMap A S)) ≃ₐ[k] (k ⊗[A] S) := by
  letI := φ.toRingHom.toAlgebra
  let I:=RingHom.ker φ.toRingHom
  have sur : Function.Surjective φ.toRingHom := fun x=>⟨algebraMap k A x,φ.commutes x⟩
  let e : (A ⧸ I) ≃ₐ[A] k :=
    { __ := φ.toRingHom.quotientKerEquivOfSurjective sur
      commutes' := fun x=>φ.toRingHom.quotientKerEquivOfSurjective_apply_mk sur x }
  let tensor := Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=A) (A₁:=S))
  let result := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toRingEquiv.trans tensor.toRingEquiv
  refine { __ := result, commutes' := fun c=>?_ }
  change result ((Ideal.Quotient.mk _) (algebraMap k S c))=_
  change tensor (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I (Ideal.Quotient.mk _ (algebraMap k S c)))=_
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  change e 1 ⊗ₜ[A] (algebraMap k S c)=_
  rw [map_one]
  rw [IsScalarTower.algebraMap_apply k A S]
  change (1:k) ⊗ₜ[A] (algebraMap A S (algebraMap k A c))=c ⊗ₜ[A] (1:S)
  rw [Algebra.algebraMap_eq_smul_one,TensorProduct.tmul_smul]
  change (φ (algebraMap k A c) * 1) ⊗ₜ[A] (1:S)=_
  rw [φ.commutes,mul_one]
  rfl

#print axioms atPoint
end Lower6960.RetainedFibreQuotient
