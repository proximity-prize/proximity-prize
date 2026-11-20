import Mathlib.Algebra.MvPolynomial.CommRing
import ProximityPrize.SubmissionLower.Koala6844VirtualHighGlobalContacts


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

def ordinaryEquation (u : K) : GermCarrier K :=
  Polynomial.C (MvPolynomial.X (0 : Fin 3) - MvPolynomial.C u)


private def ordinaryWidth : Fin 3 → ℕ := ![1,0,0]

private theorem ordinary_coeff_degree_le (u : K) (n : ℕ) (j : Fin 3) :
    ((ordinaryEquation u).coeff n).degreeOf j ≤ ordinaryWidth j := by
  classical
  by_cases h : n = 0
  · subst n
    rw [ordinaryEquation, Polynomial.coeff_C_zero]
    apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    fin_cases j <;> simp [ordinaryWidth, MvPolynomial.degreeOf_X]
  · simp [ordinaryEquation, Polynomial.coeff_C, h]

private theorem ordinary_coeff_zero_ne (u : K) : (ordinaryEquation u).coeff 0 ≠ 0 := by
  rw [ordinaryEquation, Polynomial.coeff_C_zero]
  intro hz
  have hc := congrArg (fun P : SeedValue K => P.coeff (Finsupp.single (0 : Fin 3) 1)) hz
  have hs : (Finsupp.single (0 : Fin 3) (1 : ℕ)) ≠ 0 :=
    fun e => by simpa using congrArg (fun f : Fin 3 →₀ ℕ => f 0) e
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_C, Ne.symm hs] at hc

private theorem twice_ordinary_order_sum (m : ℕ) :
    2 * (∑ i : Fin m, (m - (i : ℕ))) = m * (m+1) := by
  rw [Fin.sum_univ_eq_sum_range]
  have hsum : (∑ i ∈ Finset.range m, (m-i)) = ∑ j ∈ Finset.range m, (j+1) := by
    rw [← Finset.sum_range_reflect (fun j : ℕ => j+1) m]
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_range.mp hj
    omega
  rw [hsum]
  clear hsum
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem ordinary_quotient_rank_two_le (m y b c : ℕ) (hm : m ≤ y) (a u : K) :
    2 * Module.finrank K
      (RectangleJet (K := K) (1*m) (sourceRectangle y b c) ⧸
        virtualContactSpace (K := K) (1*m) 1 m
          (Polynomial.taylor (MvPolynomial.C a) (ordinaryEquation u)) (sourceRectangle y b c))
      ≤ m*(m+1)*(b+1)*(c+1) := by
  have hqt : Polynomial.taylor (MvPolynomial.C a) (ordinaryEquation u) = ordinaryEquation u := by
    simp [ordinaryEquation]
  rw [hqt, one_mul]
  let order (i : Fin m) := m - (i : ℕ)
  have valid (i : Fin m) : order i ≤ m ∧ 1 * (m - order i) ≤ (i : ℕ) := by
    dsimp [order]
    omega
  have cap (i : Fin m) (j : Fin 3) :
      order i * ordinaryWidth j ≤ sourceRectangle y b c j := by
    have hv := (valid i).1.trans hm
    fin_cases j
    · simpa [sourceRectangle, ordinaryWidth] using hv
    · simp [sourceRectangle, ordinaryWidth]
    · simp [sourceRectangle, ordinaryWidth]
  have rank := quotient_rank_le m 1 m (sourceRectangle y b c) ordinaryWidth
    (ordinaryEquation u) (ordinary_coeff_zero_ne u) order valid cap (ordinary_coeff_degree_le u)
  have full : (∏ j : Fin 3, (sourceRectangle y b c j + 1)) = (y+1)*(b+1)*(c+1) := by
    simp [sourceRectangle, Fin.prod_univ_three]
  have reduced (i : Fin m) :
      (∏ j : Fin 3, (sourceRectangle y b c j - order i * ordinaryWidth j + 1)) =
        (y-order i+1)*(b+1)*(c+1) := by
    simp [sourceRectangle, ordinaryWidth, Fin.prod_univ_three]
  simp only [full, reduced] at rank
  let big := (y+1)*(b+1)*(c+1)
  let small (i : Fin m) := (y-order i+1)*(b+1)*(c+1)
  change _ ≤ m*big - ∑ i : Fin m, small i at rank
  have hdiff (i : Fin m) : big-small i = order i*(b+1)*(c+1) := by
    have h := (valid i).1.trans hm
    simp only [big, small, ← Nat.sub_mul]
    have he : y+1-(y-order i+1) = order i := by omega
    rw [he]
  have hsum : m*big - ∑ i : Fin m, small i = ∑ i : Fin m, (big-small i) := by
    have hconst : m*big = ∑ _i : Fin m, big := by simp [Finset.sum_const]
    rw [hconst]
    symm
    apply Finset.sum_tsub_distrib
    intro i _
    change (y-order i+1)*(b+1)*(c+1) ≤ (y+1)*(b+1)*(c+1)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  rw [hsum] at rank
  simp only [hdiff, ← Finset.sum_mul] at rank
  calc
    _ ≤ 2 * ((∑ i : Fin m, (m - (i : ℕ))) * (b+1) * (c+1)) :=
      Nat.mul_le_mul_left _ rank
    _ = (2 * ∑ i : Fin m, (m - (i : ℕ))) * (b+1) * (c+1) := by ring
    _ = _ := by rw [twice_ordinary_order_sum]

structure LocalContact (K : Type) [Field K] where
  center : K
  length : ℕ
  multiplicity : ℕ
  relation : GermCarrier K

abbrev LocalContact.target (C : LocalContact K) (y b c : ℕ) :=
  RectangleJet (K := K) (C.length*C.multiplicity) (sourceRectangle y b c) ⧸
    virtualContactSpace (K := K) (C.length*C.multiplicity) C.length C.multiplicity
      (Polynomial.taylor (MvPolynomial.C C.center) C.relation) (sourceRectangle y b c)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
