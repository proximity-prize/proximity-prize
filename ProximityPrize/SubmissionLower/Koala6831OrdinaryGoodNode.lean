import ProximityPrize.SubmissionLower.Koala6831PrimitiveLift
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open MvPolynomial Koala6831Ordinary
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private theorem atCenteredXZero_monomial (d : Fin 5 →₀ ℕ) (a : K) :
    atCenteredXZero (MvPolynomial.monomial d a) =
      if d 0 = 0 then MvPolynomial.monomial d a else 0 := by
  classical
  have constant : atCenteredXZero (C a : Koala6831Ordinary.Poly K) = C a := by simp [atCenteredXZero]
  have var (i : Fin 5) : atCenteredXZero (X i : Koala6831Ordinary.Poly K) = if i = 0 then 0 else X i := by
    fin_cases i <;> simp [atCenteredXZero]
  have idx₁ : (0 : Fin 4).succ = (1 : Fin 5) := by decide
  have idx₂ : (0 : Fin 3).succ.succ = (2 : Fin 5) := by decide
  have idx₃ : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
  have idx₄ : (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) := by decide
  simp only [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_pow, constant,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, idx₁, idx₂, idx₃, idx₄, var]
  by_cases zero : d 0 = 0
  · simp [zero]
  · simp [zero, zero_pow]

theorem atCenteredXZero_coeff (P : Koala6831Ordinary.Poly K) (d : Fin 5 →₀ ℕ) :
    (atCenteredXZero P).coeff d = if d 0 = 0 then P.coeff d else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      rw [atCenteredXZero_monomial]
      by_cases ed : e = d
      · subst e
        split_ifs <;> simp
      · by_cases he : e 0 = 0 <;> by_cases hd : d 0 = 0 <;> simp [he, hd, coeff_monomial, ed]
  | add P Q hP hQ =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
      split_ifs <;> simp

private def seedCoordinates : Fin 2 → Fin 5 := ![3, 4]

private theorem seedCoordinates_injective : Function.Injective seedCoordinates := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [seedCoordinates] at h)

private theorem seedWord_support_at_contact (U : SeedRing K) {d : Fin 5 →₀ ℕ}
    (hd : d ∈ (liftSeedWord U).support) (i : Fin 5) (hi : i = 0 ∨ i = 1 ∨ i = 2) : d i = 0 := by
  classical
  change d ∈ (MvPolynomial.rename seedCoordinates U).support at hd
  rw [MvPolynomial.support_rename_of_injective seedCoordinates_injective] at hd
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
  have no_image : i ∉ Set.range seedCoordinates := by
    rintro ⟨j, hj⟩
    fin_cases j <;> rcases hi with rfl | rfl | rfl <;> simp [seedCoordinates] at hj
  exact Finsupp.mapDomain_of_notMem_range e i no_image

private theorem seedWord_isWeightedHomogeneous (U : SeedRing K) :
    (liftSeedWord U).IsWeightedHomogeneous germWeights 0 := by
  intro d hd
  have support := MvPolynomial.mem_support_iff.mpr hd
  rw [germ_weight, seedWord_support_at_contact U support 0 (Or.inl rfl),
    seedWord_support_at_contact U support 1 (Or.inr (Or.inl rfl)),
    seedWord_support_at_contact U support 2 (Or.inr (Or.inr rfl))]

private theorem seedWord_deriv_zero (U : SeedRing K) (i : Fin 5) (hi : i = 1 ∨ i = 2) :
    pderiv i (liftSeedWord U) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro mem
  obtain ⟨d, hd, active⟩ := (mem_vars_iff_mem_support i).mp mem
  exact (Finsupp.mem_support_iff.mp active) (seedWord_support_at_contact U hd i (Or.inr hi))

private theorem linear_seed_row_nonzero (U V : SeedRing K) (active : U ≠ 0 ∨ V ≠ 0) :
    liftSeedWord U * X 1 + liftSeedWord V * X 2 ≠ 0 := by
  intro zero
  rcases active with hU | hV
  · apply hU
    apply liftSeedWord_injective (K := K)
    have h := congrArg (fun P : Koala6831Ordinary.Poly K => pderiv 1 P) zero
    simp only [map_add, map_zero, pderiv_mul, seedWord_deriv_zero U 1 (Or.inl rfl),
      seedWord_deriv_zero V 1 (Or.inl rfl), pderiv_X_self, pderiv_X_of_ne (by decide : (2 : Fin 5) ≠ 1),
      zero_mul, mul_zero, zero_add, add_zero, mul_one] at h
    simpa only [map_zero] using h
  · apply hV
    apply liftSeedWord_injective (K := K)
    have h := congrArg (fun P : Koala6831Ordinary.Poly K => pderiv 2 P) zero
    simp only [map_add, map_zero, pderiv_mul, seedWord_deriv_zero U 2 (Or.inr rfl),
      seedWord_deriv_zero V 2 (Or.inr rfl), pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 5) ≠ 2),
      zero_mul, mul_zero, zero_add, add_zero, mul_one] at h
    simpa only [map_zero] using h

theorem primitiveRowLift_germ_order_one (q : SymbolicRow (SeedRing K)) (primitive : IsPrimitiveRow q)
    (x u₀ v₀ u₁ v₁ : K)
    (good : q.atNode (MvPolynomial.C x) (MvPolynomial.C u₀ + MvPolynomial.X 0 * MvPolynomial.C v₀)
      (MvPolynomial.C u₁ + MvPolynomial.X 1 * MvPolynomial.C v₁) = 0) :
    (weightLift germWeights
      (Koala6831Quotient.centerAtNode x u₀ v₀ u₁ v₁ (primitiveRowLift q))).natTrailingDegree = 1 := by
  classical
  let P := Koala6831Quotient.centerAtNode x u₀ v₀ u₁ v₁ (primitiveRowLift q)
  let U := q.first.eval (MvPolynomial.C x)
  let V := q.second.eval (MvPolynomial.C x)
  have linear : atCenteredXZero P = liftSeedWord U * X 1 + liftSeedWord V * X 2 :=
    centered_primitive_row_at_x_zero x u₀ v₀ u₁ v₁ q good
  have linear_ne : atCenteredXZero P ≠ 0 := by
    rw [linear]
    exact linear_seed_row_nonzero U V (primitive_active_at_good_node q primitive x _ _ good)
  have linear_homogeneous : (atCenteredXZero P).IsWeightedHomogeneous germWeights 1 := by
    rw [linear]
    have one₀ : (X 1 : Koala6831Ordinary.Poly K).IsWeightedHomogeneous germWeights 1 :=
      MvPolynomial.isWeightedHomogeneous_X K germWeights 1
    have one₁ : (X 2 : Koala6831Ordinary.Poly K).IsWeightedHomogeneous germWeights 1 :=
      MvPolynomial.isWeightedHomogeneous_X K germWeights 2
    exact ((seedWord_isWeightedHomogeneous U).mul one₀).add
      ((seedWord_isWeightedHomogeneous V).mul one₁)
  change (weightLift germWeights P).natTrailingDegree = 1
  apply germ_order_one_of_components
  · ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with zero_weight
    · have no_x : d 0 = 0 := by
        rw [germ_weight] at zero_weight
        omega
      have erased_zero : (atCenteredXZero P).coeff d = 0 := by
        by_contra kept
        have one_weight := linear_homogeneous kept
        omega
      change P.coeff d = 0
      simpa only [atCenteredXZero_coeff, ite_eq_left no_x] using erased_zero
    · simp
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr linear_ne
    have erased_coefficient := MvPolynomial.mem_support_iff.mp hd
    have one_weight := linear_homogeneous erased_coefficient
    rw [atCenteredXZero_coeff] at erased_coefficient
    split_ifs at erased_coefficient
    · intro zero
      have h := congrArg (fun Q : Koala6831Ordinary.Poly K => Q.coeff d) zero
      rw [coeff_weightedHomogeneousComponent, ite_eq_left one_weight] at h
      exact erased_coefficient (by simpa using h)
    · exact (erased_coefficient rfl).elim

end

end ProximityPrize.SubmissionLower.Koala6831Comparison
