import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DifferentialTaylorHom



/-!
# A concrete differential ring for the regular contact equation

Model label: gpt-5.

Adjoin a fifth polynomial variable U and impose F=0 and H*U=1, where
H=partial_R F. The polynomial vector field preserves this actual ideal.
It therefore descends to a derivation on the quotient, to which the already
proved finite Taylor homomorphism applies. No localization API, integrality
assertion, or assumed differential-ring structure is used.

This module does not supply the mixed curve count or the rational numerator
degree bounds and is not a complete alignment or submission theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactDifferentialRing

open DifferentialTaylorCoefficients

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section StableIdeals

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem derivation_preserves_span
    (D : Derivation K A A) (generators : Set A)
    (hgenerators : ∀ x ∈ generators, D x ∈ Ideal.span generators) :
    ∀ x ∈ Ideal.span generators, D x ∈ Ideal.span generators := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgenerators x hx
  | zero => simpa only [map_zero] using (Ideal.span generators).zero_mem
  | add x y hx hy hDx hDy =>
    simpa only [map_add] using (Ideal.span generators).add_mem hDx hDy
  | smul c x hx hDx =>
    change D (c * x) ∈ Ideal.span generators
    rw [leibniz_product]
    exact (Ideal.span generators).add_mem
      ((Ideal.span generators).mul_mem_left (D c) hx)
      ((Ideal.span generators).mul_mem_left c hDx)

noncomputable def quotientDerivation
    (D : Derivation K A A) (I : Ideal A)
    (hstable : ∀ x ∈ I, D x ∈ I) :
    Derivation K (A ⧸ I) (A ⧸ I) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K I)
    (d := D) (fun x hx => by
      change Ideal.Quotient.mk I (D x) = 0
      change Ideal.Quotient.mk I x = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (hstable x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))

theorem quotientDerivation_mk
    (D : Derivation K A A) (I : Ideal A)
    (hstable : ∀ x ∈ I, D x ∈ I) (x : A) :
    quotientDerivation D I hstable (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (D x) := by
  unfold quotientDerivation
  exact Derivation.liftOfSurjective_apply _ _ x

end StableIdeals

section PolynomialVectorField

variable (K : Type*) [CommRing K]

abbrev Poly4 := MvPolynomial (Fin 4) K
abbrev Poly5 := MvPolynomial (Fin 5) K

noncomputable def liftFour (F : Poly4 K) : Poly5 K :=
  MvPolynomial.rename Fin.castSucc F

theorem partial_extra_liftFour (F : Poly4 K) :
    MvPolynomial.pderiv (4 : Fin 5) (liftFour K F) = 0 := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftFour]
  | add F G hF hG =>
    dsimp only [liftFour] at hF hG
    change MvPolynomial.pderiv (4 : Fin 5)
      (MvPolynomial.rename Fin.castSucc (F + G)) = 0
    rw [map_add, map_add, hF, hG, add_zero]
  | mul_X F i hF =>
    dsimp only [liftFour] at hF
    have hne : (i.castSucc : Fin 5) ≠ 4 := by
      intro h
      have hv : i.val = 4 := congrArg Fin.val h
      have hi := i.isLt
      omega
    change MvPolynomial.pderiv (4 : Fin 5)
      (MvPolynomial.rename Fin.castSucc (F * MvPolynomial.X i)) = 0
    rw [map_mul, MvPolynomial.rename_X, leibniz_product, hF,
      MvPolynomial.pderiv_X_of_ne hne, zero_mul, mul_zero, add_zero]

theorem partial_liftFour (F : Poly4 K) (i : Fin 4) :
    MvPolynomial.pderiv i.castSucc (liftFour K F) =
      liftFour K (MvPolynomial.pderiv i F) := by
  have hinj : Function.Injective (Fin.castSucc : Fin 4 → Fin 5) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin 5 => x.val) hij
  exact MvPolynomial.pderiv_rename hinj i F

noncomputable def inverseRelation (H : Poly5 K) : Poly5 K :=
  H * MvPolynomial.X (4 : Fin 5) - 1

noncomputable def inverseDerivative (G H : Poly5 K) : Poly5 K :=
  MvPolynomial.pderiv (0 : Fin 5) H +
    MvPolynomial.X (2 : Fin 5) * MvPolynomial.pderiv (1 : Fin 5) H +
    G * MvPolynomial.X (4 : Fin 5) * MvPolynomial.pderiv (2 : Fin 5) H

noncomputable def inverseVectorField (G H : Poly5 K) :
    Derivation K (Poly5 K) (Poly5 K) :=
  (MvPolynomial.pderiv (0 : Fin 5) : Derivation K (Poly5 K) (Poly5 K)) +
    (MvPolynomial.X (2 : Fin 5) : Poly5 K) • MvPolynomial.pderiv (1 : Fin 5) +
    (G * MvPolynomial.X (4 : Fin 5)) • MvPolynomial.pderiv (2 : Fin 5) -
    ((MvPolynomial.X (4 : Fin 5)) ^ 2 * inverseDerivative K G H) •
      MvPolynomial.pderiv (4 : Fin 5)

theorem inverseVectorField_apply (G H P : Poly5 K) :
    inverseVectorField K G H P =
      MvPolynomial.pderiv (0 : Fin 5) P +
        MvPolynomial.X (2 : Fin 5) * MvPolynomial.pderiv (1 : Fin 5) P +
        G * MvPolynomial.X (4 : Fin 5) * MvPolynomial.pderiv (2 : Fin 5) P -
        ((MvPolynomial.X (4 : Fin 5)) ^ 2 * inverseDerivative K G H) *
          MvPolynomial.pderiv (4 : Fin 5) P := by
  simp only [inverseVectorField, Derivation.add_apply, Derivation.sub_apply,
    Derivation.smul_apply, smul_eq_mul]

theorem inverseVectorField_X (G H : Poly5 K) :
    inverseVectorField K G H (MvPolynomial.X (0 : Fin 5)) = 1 := by
  simp [inverseVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply]

theorem inverseVectorField_Y (G H : Poly5 K) :
    inverseVectorField K G H (MvPolynomial.X (1 : Fin 5)) =
      MvPolynomial.X (2 : Fin 5) := by
  simp [inverseVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply]

theorem inverseVectorField_R (G H : Poly5 K) :
    inverseVectorField K G H (MvPolynomial.X (2 : Fin 5)) =
      G * MvPolynomial.X (4 : Fin 5) := by
  simp [inverseVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply]

theorem inverseVectorField_Z (G H : Poly5 K) :
    inverseVectorField K G H (MvPolynomial.X (3 : Fin 5)) = 0 := by
  simp [inverseVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply]

theorem inverseVectorField_U (G H : Poly5 K) :
    inverseVectorField K G H (MvPolynomial.X (4 : Fin 5)) =
      -((MvPolynomial.X (4 : Fin 5)) ^ 2 * inverseDerivative K G H) := by
  simp [inverseVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply]

theorem inverseVectorField_H (G H : Poly5 K)
    (hH : MvPolynomial.pderiv (4 : Fin 5) H = 0) :
    inverseVectorField K G H H = inverseDerivative K G H := by
  rw [inverseVectorField_apply, hH, mul_zero, sub_zero]
  rfl

theorem inverseVectorField_inverseRelation (G H : Poly5 K)
    (hH : MvPolynomial.pderiv (4 : Fin 5) H = 0) :
    inverseVectorField K G H (inverseRelation K H) =
      -(inverseDerivative K G H * MvPolynomial.X (4 : Fin 5)) *
        inverseRelation K H := by
  rw [inverseRelation, map_sub, (inverseVectorField K G H).map_one_eq_zero,
    sub_zero, leibniz_product, inverseVectorField_H K G H hH, inverseVectorField_U]
  ring

noncomputable def contactH (F : Poly4 K) : Poly5 K :=
  MvPolynomial.pderiv (2 : Fin 5) (liftFour K F)

noncomputable def contactG (F : Poly4 K) : Poly5 K :=
  -(MvPolynomial.pderiv (0 : Fin 5) (liftFour K F) +
      MvPolynomial.X (2 : Fin 5) * MvPolynomial.pderiv (1 : Fin 5) (liftFour K F))

noncomputable def contactVectorField (F : Poly4 K) :
    Derivation K (Poly5 K) (Poly5 K) :=
  inverseVectorField K (contactG K F) (contactH K F)

theorem partial_extra_contactH (F : Poly4 K) :
    MvPolynomial.pderiv (4 : Fin 5) (contactH K F) = 0 := by
  have h := partial_liftFour K F (2 : Fin 4)
  change contactH K F = liftFour K (MvPolynomial.pderiv (2 : Fin 4) F) at h
  rw [h]
  exact partial_extra_liftFour K _

theorem contactVectorField_F (F : Poly4 K) :
    contactVectorField K F (liftFour K F) =
      contactG K F * inverseRelation K (contactH K F) := by
  rw [contactVectorField, inverseVectorField_apply, partial_extra_liftFour,
    mul_zero, sub_zero]
  unfold contactG contactH inverseRelation
  ring

noncomputable def contactIdeal (F : Poly4 K) : Ideal (Poly5 K) :=
  Ideal.span ({liftFour K F, inverseRelation K (contactH K F)} : Set (Poly5 K))

theorem contactIdeal_stable (F : Poly4 K) :
    ∀ P ∈ contactIdeal K F, contactVectorField K F P ∈ contactIdeal K F := by
  apply derivation_preserves_span
  intro P hP
  have hrel : inverseRelation K (contactH K F) ∈ contactIdeal K F :=
    Ideal.subset_span (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · rw [contactVectorField_F]
    exact (contactIdeal K F).mul_mem_left _ hrel
  · rw [contactVectorField,
      inverseVectorField_inverseRelation K _ _ (partial_extra_contactH K F)]
    exact (contactIdeal K F).mul_mem_left _ hrel

abbrev ContactRing (F : Poly4 K) := Poly5 K ⧸ contactIdeal K F

noncomputable def contactDerivation (F : Poly4 K) :
    Derivation K (ContactRing K F) (ContactRing K F) :=
  quotientDerivation (contactVectorField K F) (contactIdeal K F) (contactIdeal_stable K F)

theorem contactDerivation_mk (F : Poly4 K) (P : Poly5 K) :
    contactDerivation K F (Ideal.Quotient.mk (contactIdeal K F) P) =
      Ideal.Quotient.mk (contactIdeal K F) (contactVectorField K F P) :=
  quotientDerivation_mk _ _ _ P

theorem contactRing_relation (F : Poly4 K) :
    Ideal.Quotient.mk (contactIdeal K F) (liftFour K F) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

theorem contactRing_inverse (F : Poly4 K) :
    Ideal.Quotient.mk (contactIdeal K F) (contactH K F) *
      Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4 : Fin 5)) = 1 := by
  have hrel : Ideal.Quotient.mk (contactIdeal K F)
      (inverseRelation K (contactH K F)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [inverseRelation, map_sub, map_mul, map_one, sub_eq_zero] using hrel

end PolynomialVectorField

end ProximityPrize.SubmissionLower.ContactDifferentialRing

#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.derivation_preserves_span
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.quotientDerivation_mk
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.partial_extra_liftFour
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.contactVectorField_F
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.contactIdeal_stable
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.contactDerivation_mk
#print axioms ProximityPrize.SubmissionLower.ContactDifferentialRing.contactRing_inverse
