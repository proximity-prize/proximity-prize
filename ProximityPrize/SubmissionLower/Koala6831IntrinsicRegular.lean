import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN077 RCN347

noncomputable section

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K]

private def liftedSeparant (F : Carrier K) : Poly5 K :=
  liftFour K (implicitRegularity F)

private def horizontalField (F : Carrier K) : Derivation K (Poly5 K) (Poly5 K) :=
  pderiv 0 - ((MvPolynomial.X (4 : Fin 5)) * liftFour K (pderiv 0 F)) • pderiv 1

private def regularField (F : Carrier K) : Derivation K (Poly5 K) (Poly5 K) :=
  horizontalField F -
    ((MvPolynomial.X (4 : Fin 5)) ^ 2 * horizontalField F (liftedSeparant F)) • pderiv 4

private theorem horizontalField_apply (F : Carrier K) (P : Poly5 K) :
    horizontalField F P =
      pderiv 0 P - MvPolynomial.X (4 : Fin 5) * liftFour K (pderiv 0 F) * pderiv 1 P := by
  simp only [horizontalField, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

private theorem regularField_apply (F : Carrier K) (P : Poly5 K) :
    regularField F P =
      horizontalField F P -
        MvPolynomial.X (4 : Fin 5) ^ 2 * horizontalField F (liftedSeparant F) * pderiv 4 P := by
  simp only [regularField, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

private theorem regularField_F (F : Carrier K) :
    regularField F (liftFour K F) = -liftFour K (pderiv 0 F) *
      inverseRelation K (liftedSeparant F) := by
  rw [regularField_apply, partial_extra_liftFour, mul_zero, sub_zero, horizontalField_apply]
  have hx := partial_liftFour K F 0
  have hy := partial_liftFour K F 1
  change pderiv (0 : Fin 5) (liftFour K F) = _ at hx
  change pderiv (1 : Fin 5) (liftFour K F) = _ at hy
  rw [hx, hy]
  unfold inverseRelation liftedSeparant implicitRegularity
  ring

private theorem regularField_inverseRelation (F : Carrier K) :
    regularField F (inverseRelation K (liftedSeparant F)) =
      -(horizontalField F (liftedSeparant F) * MvPolynomial.X (4 : Fin 5)) *
        inverseRelation K (liftedSeparant F) := by
  have hs : regularField F (liftedSeparant F) = horizontalField F (liftedSeparant F) := by
    rw [regularField_apply, liftedSeparant, partial_extra_liftFour, mul_zero, sub_zero]
  have hu : regularField F (MvPolynomial.X (4 : Fin 5)) =
      -(MvPolynomial.X (4 : Fin 5) ^ 2 * horizontalField F (liftedSeparant F)) := by
    rw [regularField_apply, horizontalField_apply]
    simp [MvPolynomial.pderiv_X]
  unfold inverseRelation
  rw [map_sub, (regularField F).map_one_eq_zero, sub_zero, leibniz_product, hs, hu]
  ring

def regularIdeal (F : Carrier K) : Ideal (Poly5 K) :=
  Ideal.span ({liftFour K F, inverseRelation K (liftedSeparant F)} : Set (Poly5 K))

private theorem regularIdeal_stable (F : Carrier K) :
    ∀ P ∈ regularIdeal F, regularField F P ∈ regularIdeal F := by
  apply derivation_preserves_span
  intro P hP
  have hrel : inverseRelation K (liftedSeparant F) ∈ regularIdeal F :=
    Ideal.subset_span (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · rw [regularField_F]
    exact (regularIdeal F).mul_mem_left _ hrel
  · rw [regularField_inverseRelation]
    exact (regularIdeal F).mul_mem_left _ hrel

abbrev RegularCarrier (F : Carrier K) := Poly5 K ⧸ regularIdeal F

def regularDerivation (F : Carrier K) :
    Derivation K (RegularCarrier F) (RegularCarrier F) :=
  quotientDerivation (regularField F) (regularIdeal F) (regularIdeal_stable F)

def regularImage (F : Carrier K) : Carrier K →+* RegularCarrier F :=
  (Ideal.Quotient.mk (regularIdeal F)).comp (MvPolynomial.rename Fin.castSucc).toRingHom

def reciprocal (F : Carrier K) : RegularCarrier F :=
  Ideal.Quotient.mk (regularIdeal F) (MvPolynomial.X (4 : Fin 5))

theorem regularImage_carrier_zero (F : Carrier K) : regularImage F F = 0 := by
  change Ideal.Quotient.mk (regularIdeal F) (liftFour K F) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem regularImage_separant_mul_reciprocal (F : Carrier K) :
    regularImage F (implicitRegularity F) * reciprocal F = 1 := by
  have hrel : Ideal.Quotient.mk (regularIdeal F) (inverseRelation K (liftedSeparant F)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [inverseRelation, liftedSeparant, map_sub, map_mul, map_one, sub_eq_zero,
    regularImage, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    liftFour, reciprocal] using hrel

theorem regularDerivation_image (F Q : Carrier K) :
    regularDerivation F (regularImage F Q) =
      regularImage F (pderiv 0 Q) -
        reciprocal F * regularImage F (pderiv 0 F) * regularImage F (pderiv 1 Q) := by
  change quotientDerivation (regularField F) (regularIdeal F) (regularIdeal_stable F)
    (Ideal.Quotient.mk (regularIdeal F) (liftFour K Q)) = _
  rw [quotientDerivation_mk, regularField_apply, partial_extra_liftFour, mul_zero, sub_zero,
    horizontalField_apply]
  have hx := partial_liftFour K Q 0
  have hy := partial_liftFour K Q 1
  change pderiv (0 : Fin 5) (liftFour K Q) = _ at hx
  change pderiv (1 : Fin 5) (liftFour K Q) = _ at hy
  rw [hx, hy, map_sub, map_mul, map_mul]
  rfl

theorem regularDerivation_X (F : Carrier K) :
    regularDerivation F (regularImage F (MvPolynomial.X 0)) = 1 := by
  simp [regularDerivation_image, MvPolynomial.pderiv_X]

theorem regularDerivation_seeds (F : Carrier K) :
    regularDerivation F (regularImage F (MvPolynomial.X 2)) = 0 ∧
    regularDerivation F (regularImage F (MvPolynomial.X 3)) = 0 := by
  simp [regularDerivation_image, MvPolynomial.pderiv_X]

theorem regularImage_clearedImplicit (F Q : Carrier K) :
    regularImage F (clearedImplicit F Q) =
      regularImage F (implicitRegularity F) * regularDerivation F (regularImage F Q) := by
  rw [clearedImplicit, map_sub, map_mul, map_mul, regularDerivation_image,
    mul_sub, ← mul_assoc, ← mul_assoc, regularImage_separant_mul_reciprocal, one_mul]

private theorem quotient_derivation_step {A : Type*} [CommRing A] [Algebra K A]
    (D : Derivation K A A) (S U : A) (k : ℕ) :
    S ^ 2 * D (S ^ (k + 1) * U) -
      ((k + 1 : ℕ) : A) * (S ^ (k + 1) * U) * (S * D S) =
    S ^ (k + 3) * D U := by
  rw [RCN324.derivation_pow_mul D S U (k + 1) (by omega), Nat.add_sub_cancel]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem regularImage_tailNumerator (F : Carrier K) (j : ℕ) :
    regularImage F (tailNumerator F j) =
      (regularImage F (implicitRegularity F)) ^ (2 * j + 1) *
        ((regularDerivation F : RegularCarrier F → RegularCarrier F)^[j + 1])
          (regularImage F (MvPolynomial.X 1)) := by
  induction j with
  | zero =>
      simp only [tailNumerator, map_neg, Nat.mul_zero, Nat.zero_add, pow_one,
        Function.iterate_one, regularDerivation_image]
      rw [MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 4) ≠ 0), MvPolynomial.pderiv_X_self]
      simp only [map_zero, map_one, mul_one, zero_sub]
      linear_combination regularImage F (pderiv 0 F) * regularImage_separant_mul_reciprocal F
  | succ j ih =>
      rw [tailNumerator]
      simp only [map_sub, map_mul, map_natCast, regularImage_clearedImplicit, ih]
      let D := regularDerivation F
      let S := regularImage F (implicitRegularity F)
      let Q := regularImage F (MvPolynomial.X 1)
      have hiter : (D : RegularCarrier F → RegularCarrier F)^[j + 1 + 1] Q =
          D ((D : RegularCarrier F → RegularCarrier F)^[j + 1] Q) :=
        Function.iterate_succ_apply' D (j + 1) Q
      change
        S * (S * D (S ^ (2 * j + 1) *
          ((D : RegularCarrier F → RegularCarrier F)^[j + 1]) Q)) -
          ((2 * j + 1 : ℕ) : RegularCarrier F) *
            (S ^ (2 * j + 1) * ((D : RegularCarrier F → RegularCarrier F)^[j + 1]) Q) *
            (S * D S) =
          S ^ (2 * (j + 1) + 1) * ((D : RegularCarrier F → RegularCarrier F)^[j + 1 + 1]) Q
      rw [hiter, show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
      have hstep := quotient_derivation_step D S
        (((D : RegularCarrier F → RegularCarrier F)^[j + 1]) Q) (2 * j)
      rw [pow_two, mul_assoc] at hstep
      exact hstep


end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
