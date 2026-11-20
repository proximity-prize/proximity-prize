import Mathlib.Algebra.MvPolynomial.Equiv
import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermHomogeneous


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial
open scoped BigOperators Classical

noncomputable section
set_option autoImplicit false

variable {R B : Type*} [CommRing R] [CommRing B]

theorem homogeneousEval_degreeOf_le {ι : Type*} (φ : R →+* MvPolynomial ι B)
    (Q : Polynomial R) (u : ℕ) (N D : MvPolynomial ι B) (i : ι) (cap : ℕ)
    (h : ∀ j ∈ Q.support, (φ (Q.coeff j)).degreeOf i +
      j*N.degreeOf i + (u-j)*D.degreeOf i ≤ cap) :
    (homogeneousEval φ Q u N D).degreeOf i ≤ cap := by
  classical
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j hj
  have h₁ := MvPolynomial.degreeOf_mul_le i (φ (Q.coeff j) * N^j) (D^(u-j))
  have h₂ := MvPolynomial.degreeOf_mul_le i (φ (Q.coeff j)) (N^j)
  exact h₁.trans ((Nat.add_le_add
    (h₂.trans (Nat.add_le_add_left (MvPolynomial.degreeOf_pow_le i N j) _))
    (MvPolynomial.degreeOf_pow_le i D (u-j))).trans (h j hj))

theorem homogeneousEval_totalDegree_le {ι : Type*} (φ : R →+* MvPolynomial ι B)
    (Q : Polynomial R) (u : ℕ) (N D : MvPolynomial ι B) (cap : ℕ)
    (h : ∀ j ∈ Q.support, (φ (Q.coeff j)).totalDegree +
      j*N.totalDegree + (u-j)*D.totalDegree ≤ cap) :
    (homogeneousEval φ Q u N D).totalDegree ≤ cap := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have h₁ := MvPolynomial.totalDegree_mul (φ (Q.coeff j) * N^j) (D^(u-j))
  have h₂ := MvPolynomial.totalDegree_mul (φ (Q.coeff j)) (N^j)
  have hN : (N^j).totalDegree ≤ j*N.totalDegree := by
    simpa only [Nat.mul_comm] using MvPolynomial.totalDegree_pow N j
  have hD : (D^(u-j)).totalDegree ≤ (u-j)*D.totalDegree := by
    simpa only [Nat.mul_comm] using MvPolynomial.totalDegree_pow D (u-j)
  exact h₁.trans ((Nat.add_le_add (h₂.trans (Nat.add_le_add_left hN _)) hD).trans (h j hj))

theorem totalDegree_coeff_pack_le (P : MvPolynomial (Fin 2) R) (j v : ℕ) (h : P.totalDegree ≤ v) :
    ((MvPolynomial.finSuccEquiv R 1 P).coeff j).totalDegree ≤ v-j := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  have H := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_coeff_finSuccEquiv.mp he)
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ] at H
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ] at H
  exact Nat.le_sub_of_add_le ((Nat.add_comm _ _).le.trans (H.trans h))

def coeffLayer (n : ℕ) (P : MvPolynomial (Fin 2) (Polynomial B)) : MvPolynomial (Fin 2) B :=
  ∑ e ∈ P.support, MvPolynomial.monomial e ((P.coeff e).coeff n)

theorem coeff_coeffLayer (n : ℕ) (P : MvPolynomial (Fin 2) (Polynomial B)) (e : Fin 2 →₀ ℕ) :
    (coeffLayer n P).coeff e = (P.coeff e).coeff n := by
  classical
  simp only [coeffLayer, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hne
    simp [hne]
  · intro he
    rw [MvPolynomial.notMem_support_iff.mp he]
    simp

theorem support_coeffLayer_subset (n : ℕ) (P : MvPolynomial (Fin 2) (Polynomial B)) :
    (coeffLayer n P).support ⊆ P.support := by
  intro e he
  rw [MvPolynomial.mem_support_iff, coeff_coeffLayer] at he
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact he (by rw [hz, Polynomial.coeff_zero])

theorem exists_firstCoeffLayer (P : MvPolynomial (Fin 2) (Polynomial B)) (hP : P ≠ 0) :
    ∃ n, coeffLayer n P ≠ 0 ∧ ∀ m < n, coeffLayer m P = 0 := by
  classical
  have hExists : ∃ n, coeffLayer n P ≠ 0 := by
    by_contra! h
    apply hP
    ext e n
    have hh := congrArg (fun J : MvPolynomial (Fin 2) B => J.coeff e) (h n)
    change (P.coeff e).coeff n = 0
    simpa [coeff_coeffLayer] using hh
  exact ⟨Nat.find hExists, Nat.find_spec hExists, fun m hm => not_ne_iff.mp (Nat.find_min hExists hm)⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
