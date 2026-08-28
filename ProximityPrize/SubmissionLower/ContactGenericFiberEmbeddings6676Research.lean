import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveCoordinateField

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactGenericFiberEmbeddings6676Research

open scoped BigOperators
open ActualCurveCoordinateField

noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]

def embeddingPoint (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] L) : Fin 3 → L :=
  fun i => f (coordinate K P i)

theorem embeddingPoint_aeval (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] L) :
    MvPolynomial.aeval (embeddingPoint P f) =
      f.comp (coordinateEvaluation K P) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, embeddingPoint, coordinate]

theorem embeddingPoint_kernel (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] L) :
    RingHom.ker (MvPolynomial.aeval (embeddingPoint P f)).toRingHom = P := by
  rw [embeddingPoint_aeval]
  change RingHom.ker (f.toRingHom.comp
    (coordinateEvaluation K P).toRingHom) = P
  rw [RingHom.ker_comp_of_injective _ f.injective, coordinateEvaluation_ker]

theorem embeddingPoint_injective (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] :
    Function.Injective (embeddingPoint (L := L) P) := by
  intro f g hfg
  have he : f.comp (coordinateEvaluation K P) =
      g.comp (coordinateEvaluation K P) := by
    rw [← embeddingPoint_aeval, ← embeddingPoint_aeval, hfg]
  apply IsLocalization.algHom_ext (nonZeroDivisors (CoordinateRing K P))
  apply AlgHom.ext
  intro a
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact AlgHom.congr_fun he A

variable {I : Type} (P : I → Ideal (MvPolynomial (Fin 3) K))
variable [∀ i, (P i).IsPrime]

def familyEmbeddingPoint
    (z : Σ i, CoordinateField K (P i) →ₐ[K] L) : Fin 3 → L :=
  embeddingPoint (P z.1) z.2

theorem familyEmbeddingPoint_injective (hP : Function.Injective P) :
    Function.Injective (familyEmbeddingPoint (L := L) P) := by
  rintro ⟨i, f⟩ ⟨j, g⟩ hfg
  have hij : P i = P j := by
    rw [← embeddingPoint_kernel (P i) f,
      ← embeddingPoint_kernel (P j) g]
    exact congrArg (fun v : Fin 3 → L =>
      RingHom.ker (MvPolynomial.aeval v).toRingHom) hfg
  obtain rfl := hP hij
  have hf : f = g := embeddingPoint_injective (P i) hfg
  cases hf
  rfl

section CommonBase

variable {B : Type} [Field B] [Algebra K B] [Algebra B L]
variable [IsScalarTower K B L]
variable [∀ i, Algebra B (CoordinateField K (P i))]
variable [∀ i, IsScalarTower K B (CoordinateField K (P i))]

def commonBaseEmbeddingPoint
    (z : Σ i, CoordinateField K (P i) →ₐ[B] L) : Fin 3 → L :=
  embeddingPoint (P z.1) (z.2.restrictScalars K)

theorem commonBaseEmbeddingPoint_injective (hP : Function.Injective P) :
    Function.Injective (commonBaseEmbeddingPoint (B := B) (L := L) P) := by
  rintro ⟨i, f⟩ ⟨j, g⟩ hfg
  have hij : P i = P j := by
    rw [← embeddingPoint_kernel (P i) (f.restrictScalars K),
      ← embeddingPoint_kernel (P j) (g.restrictScalars K)]
    exact congrArg (fun v : Fin 3 → L =>
      RingHom.ker (MvPolynomial.aeval v).toRingHom) hfg
  obtain rfl := hP hij
  have hr : f.restrictScalars K = g.restrictScalars K :=
    embeddingPoint_injective (P i) hfg
  have hf : f = g := by
    apply AlgHom.ext
    intro a
    exact AlgHom.congr_fun hr a
  cases hf
  rfl

variable [Fintype I] [IsAlgClosed L]
variable [∀ i, FiniteDimensional B (CoordinateField K (P i))]
variable [∀ i, Algebra.IsSeparable B (CoordinateField K (P i))]

def genericFiberPoints : Finset (Fin 3 → L) := by
  classical
  exact Finset.univ.image (commonBaseEmbeddingPoint (B := B) (L := L) P)

theorem genericFiberPoints_card (hP : Function.Injective P) :
    (genericFiberPoints (B := B) (L := L) P).card =
      ∑ i, Module.finrank B (CoordinateField K (P i)) := by
  classical
  rw [genericFiberPoints,
    Finset.card_image_of_injective _ (commonBaseEmbeddingPoint_injective P hP)]
  simp only [Finset.card_univ, Fintype.card_sigma, AlgHom.card]

end CommonBase
end
end ProximityPrize.SubmissionLower.ContactGenericFiberEmbeddings6676Research
