import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors



namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

abbrev Poly (K : Type*) [CommSemiring K] := MvPolynomial (Fin 5) K
abbrev weightDegree (w : Fin 5 → ℕ) (P : Poly K) : ℕ := P.weightedTotalDegree w

def weightLift (w : Fin 5 → ℕ) : Poly K →+* Polynomial (Poly K) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

theorem weight_five (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) :
    Finsupp.weight w d = d 0 * w 0 + d 1 * w 1 + d 2 * w 2 + d 3 * w 3 + d 4 * w 4 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_succ, Nat.mul_comm, Nat.add_assoc]

private theorem lift_monomial (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (a : K) :
    weightLift w (MvPolynomial.monomial d a) =
      Polynomial.C (MvPolynomial.monomial d a) * Polynomial.X ^ Finsupp.weight w d := by
  rw [weightLift, eval₂Hom_monomial, Finsupp.prod_pow]
  simp only [RingHom.comp_apply, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [← Polynomial.C_pow]
  rw [← map_prod Polynomial.C, ← mul_assoc, ← map_mul Polynomial.C]
  congr 2
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  · rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [Nat.mul_comm]

theorem weightLift_coeff (w : Fin 5 → ℕ) (P : Poly K) (n : ℕ) :
    (weightLift w P).coeff n = weightedHomogeneousComponent w n P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      rw [lift_monomial, Polynomial.coeff_C_mul_X_pow]
      ext e
      rw [coeff_weightedHomogeneousComponent]
      by_cases h : d = e
      · subst e
        by_cases hn : n = Finsupp.weight w d <;> simp [hn, eq_comm]
      · by_cases hn : n = Finsupp.weight w d
        · simp [hn, coeff_monomial, h]
        · simp [hn, coeff_monomial, h]
  | add P Q hP hQ => simp only [map_add, Polynomial.coeff_add, hP, hQ]

theorem weightLift_natDegree (w : Fin 5 → ℕ) (P : Poly K) :
    (weightLift w P).natDegree = weightDegree w P := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    rw [weightLift_coeff]
    exact weightedHomogeneousComponent_eq_zero _ _ hd
  · apply Finset.sup_le
    intro d hd
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hc := congrArg (fun R : Poly K => R.coeff d) hz
    rw [weightLift_coeff, coeff_weightedHomogeneousComponent, ite_eq_left rfl] at hc
    exact (mem_support_iff.mp hd) (by simpa using hc)

theorem weightLift_ne_zero (w : Fin 5 → ℕ) {P : Poly K} (hP : P ≠ 0) :
    weightLift w P ≠ 0 := by
  obtain ⟨d, hd⟩ := support_nonempty.mpr hP
  intro hz
  have hc := congrArg (fun R : Polynomial (Poly K) => (R.coeff (Finsupp.weight w d)).coeff d) hz
  rw [weightLift_coeff, coeff_weightedHomogeneousComponent, ite_eq_left rfl,
    Polynomial.coeff_zero] at hc
  exact (mem_support_iff.mp hd) (by simpa using hc)

theorem weight_mul_eq (w : Fin 5 → ℕ) {P Q : Poly K} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    weightDegree w (P * Q) = weightDegree w P + weightDegree w Q := by
  simp only [← weightLift_natDegree, map_mul,
    Polynomial.natDegree_mul (weightLift_ne_zero w hP) (weightLift_ne_zero w hQ)]

theorem weight_mul_le (w : Fin 5 → ℕ) (P Q : Poly K) :
    weightDegree w (P * Q) ≤ weightDegree w P + weightDegree w Q := by
  simpa only [← weightLift_natDegree, map_mul] using
    Polynomial.natDegree_mul_le (p := weightLift w P) (q := weightLift w Q)

theorem weight_add_le (w : Fin 5 → ℕ) (P Q : Poly K) :
    weightDegree w (P + Q) ≤ max (weightDegree w P) (weightDegree w Q) := by
  simpa only [← weightLift_natDegree, map_add] using
    Polynomial.natDegree_add_le (weightLift w P) (weightLift w Q)

theorem weight_C (w : Fin 5 → ℕ) (a : K) : weightDegree w (MvPolynomial.C a) = 0 := by
  simp [weightedTotalDegree]

theorem weight_X (w : Fin 5 → ℕ) (i : Fin 5) :
    weightDegree w (MvPolynomial.X i : Poly K) = w i := by
  simp [weightedTotalDegree, support_X, Finsupp.weight_single]

theorem weight_eval_le (v w : Fin 5 → ℕ) (f : Fin 5 → Poly K) (P : Poly K)
    (himage : ∀ i, weightDegree w (f i) ≤ v i) :
    weightDegree w (MvPolynomial.aeval f P) ≤ weightDegree v P := by
  classical
  have monomial_bound (d : Fin 5 →₀ ℕ) (a : K) :
      weightDegree w (MvPolynomial.aeval f (MvPolynomial.monomial d a)) ≤ Finsupp.weight v d := by
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_pow, ← weightLift_natDegree,
      map_mul, map_prod]
    apply (Polynomial.natDegree_mul_le).trans
    rw [show (algebraMap K (Poly K)) a = MvPolynomial.C a from rfl, weightLift_natDegree, weight_C, zero_add]
    apply (Polynomial.natDegree_prod_le _ _).trans
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    apply Finset.sum_le_sum
    intro i _
    simpa only [map_pow, weightLift_natDegree, smul_eq_mul] using
      Polynomial.natDegree_pow_le_of_le (d i) ((weightLift_natDegree w (f i)).le.trans (himage i))
  rw [← weightLift_natDegree]
  conv_lhs => rw [MvPolynomial.as_sum P, map_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [weightLift_natDegree]
  exact (monomial_bound d (P.coeff d)).trans (le_weightedTotalDegree v hd)

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary
