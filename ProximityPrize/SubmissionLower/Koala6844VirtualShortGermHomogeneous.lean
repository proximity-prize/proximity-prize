import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial
open scoped BigOperators Classical

noncomputable section
set_option autoImplicit false

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

def homogeneousEval (φ : R →+* S) (Q : Polynomial R) (u : ℕ) (num den : S) : S :=
  ∑ j ∈ Q.support, φ (Q.coeff j) * num^j * den^(u-j)

theorem map_homogeneousEval (φ : R →+* S) (ψ : S →+* T) (Q : Polynomial R)
    (u : ℕ) (num den : S) :
    ψ (homogeneousEval φ Q u num den) =
      homogeneousEval (ψ.comp φ) Q u (ψ num) (ψ den) := by
  simp [homogeneousEval]

theorem homogeneousEval_eq_mul_eval₂ (φ : R →+* S) (Q : Polynomial R)
    (u : ℕ) (hu : Q.natDegree ≤ u) (num den v : S) (hn : num = den*v) :
    homogeneousEval φ Q u num den = den^u * Q.eval₂ φ v := by
  rw [homogeneousEval, Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hju := (Polynomial.le_natDegree_of_mem_supp j hj).trans hu
  have hp : den^u = den^j * den^(u-j) := by rw [← pow_add, Nat.add_sub_of_le hju]
  rw [hn, mul_pow, hp]
  ring

theorem homogeneousEval_affine_ne_zero {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hφ : Function.Injective φ) (Q : Polynomial A) (hQ : Q ≠ 0)
    (a b d : B) (ha : a ≠ 0) :
    homogeneousEval (Polynomial.C.comp φ) Q Q.natDegree
      (Polynomial.C a * Polynomial.X + Polynomial.C b) (Polynomial.C d) ≠ 0 := by
  let L : Polynomial B := Polynomial.C a * Polynomial.X + Polynomial.C b
  have hL : L.natDegree = 1 := by
    rw [show L = Polynomial.C a * Polynomial.X + Polynomial.C b from rfl,
      Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul (by simp [ha]), Polynomial.natDegree_X]
  have hLc : L.leadingCoeff = a := by
    rw [Polynomial.leadingCoeff, hL]
    simp [L]
  let u := Q.natDegree
  have hcoeff : (homogeneousEval (Polynomial.C.comp φ) Q u L (Polynomial.C d)).coeff u =
      φ Q.leadingCoeff * a^u := by
    rw [homogeneousEval, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single u]
    · have hd : (L^u).natDegree = u := by simp [Polynomial.natDegree_pow, hL]
      have hc : (L^u).coeff u = a^u := by
        calc
          _ = (L^u).coeff (L^u).natDegree := congrArg ((L^u).coeff) hd.symm
          _ = _ := by rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow, hLc]
      simp only [RingHom.comp_apply, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_C_mul,
        hc, u, Polynomial.coeff_natDegree]
    · intro j hj hne
      have hjlt : j < u :=
        lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp j hj) hne
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have le₁ := Polynomial.natDegree_mul_le
        (p := Polynomial.C (φ (Q.coeff j)) * L^j) (q := Polynomial.C d ^ (u-j))
      have le₂ := Polynomial.natDegree_mul_le
        (p := Polynomial.C (φ (Q.coeff j))) (q := L^j)
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_C, hL,
        mul_zero, mul_one, add_zero, zero_add] at le₁ le₂
      exact (le₁.trans le₂).trans_lt hjlt
    · intro h
      exact False.elim (h (Polynomial.natDegree_mem_support_of_nonzero hQ))
  intro hz
  rw [hz, Polynomial.coeff_zero] at hcoeff
  exact (mul_ne_zero (fun h => (Polynomial.leadingCoeff_ne_zero.mpr hQ)
    (hφ (h.trans (map_zero φ).symm))) (pow_ne_zero _ ha)) hcoeff.symm

theorem homogeneousEval_at_pole {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (Q : Polynomial A) (hQ : Q ≠ 0) (n : B) :
    homogeneousEval φ Q Q.natDegree n 0 = φ Q.leadingCoeff * n^Q.natDegree := by
  rw [homogeneousEval, Finset.sum_eq_single Q.natDegree]
  · simp only [Polynomial.coeff_natDegree, Nat.sub_self, pow_zero, mul_one]
  · intro j hj hne
    have hjlt := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp j hj) hne
    simp [zero_pow (Nat.sub_ne_zero_of_lt hjlt)]
  · intro h
    exact False.elim (h (Polynomial.natDegree_mem_support_of_nonzero hQ))

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
