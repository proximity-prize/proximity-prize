import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.RingTheory.Valuation.Basic


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Polynomial BigOperators

noncomputable section

variable {E Γ₀ : Type*} [CommRing E] [LinearOrderedCommGroupWithZero Γ₀]

def gaussMaximum (v : Valuation E Γ₀) (P : E[X]) : Γ₀ :=
  P.support.sup fun n ↦ v (P.coeff n)

@[simp] theorem gaussMaximum_zero (v : Valuation E Γ₀) : gaussMaximum v 0 = 0 := by
  simp [gaussMaximum, bot_eq_zero]

@[simp] theorem gaussMaximum_C (v : Valuation E Γ₀) (a : E) :
    gaussMaximum v (Polynomial.C a) = v a := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [gaussMaximum, Polynomial.support_C ha]

theorem coefficient_le_gaussMaximum (v : Valuation E Γ₀) (P : E[X]) (n : ℕ) :
    v (P.coeff n) ≤ gaussMaximum v P := by
  by_cases hn : n ∈ P.support
  · exact Finset.le_sup (f := fun j ↦ v (P.coeff j)) hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
    exact zero_le

theorem gaussMaximum_le_iff (v : Valuation E Γ₀) (P : E[X]) (B : Γ₀) :
    gaussMaximum v P ≤ B ↔ ∀ n, v (P.coeff n) ≤ B :=
  ⟨fun h n ↦ (coefficient_le_gaussMaximum v P n).trans h,
    fun h ↦ Finset.sup_le fun n _ ↦ h n⟩

private theorem exists_first_maximum (v : Valuation E Γ₀) (P : E[X])
    (hP : gaussMaximum v P ≠ 0) :
    ∃ i, v (P.coeff i) = gaussMaximum v P ∧
      ∀ j < i, v (P.coeff j) < gaussMaximum v P := by
  classical
  have hnonempty : P.support.Nonempty := Polynomial.support_nonempty.mpr (by
    intro hz
    apply hP
    simp [hz])
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup P.support hnonempty (fun n ↦ v (P.coeff n))
  have he : ∃ i, v (P.coeff i) = gaussMaximum v P := ⟨j, hj.symm⟩
  refine ⟨Nat.find he, Nat.find_spec he, fun k hk ↦ ?_⟩
  apply lt_of_le_of_ne (coefficient_le_gaussMaximum v P k)
  exact fun eq ↦ (Nat.not_le_of_gt hk) (Nat.find_min' he eq)

private theorem gaussMaximum_mul_le (v : Valuation E Γ₀) (P Q : E[X]) :
    gaussMaximum v (P * Q) ≤ gaussMaximum v P * gaussMaximum v Q := by
  apply (gaussMaximum_le_iff _ _ _).mpr
  intro n
  rw [Polynomial.coeff_mul]
  apply v.map_sum_le
  intro i _
  rw [map_mul]
  exact mul_le_mul (coefficient_le_gaussMaximum v P i.1) (coefficient_le_gaussMaximum v Q i.2)
    zero_le zero_le

theorem gaussMaximum_mul (v : Valuation E Γ₀) (P Q : E[X]) :
    gaussMaximum v (P * Q) = gaussMaximum v P * gaussMaximum v Q := by
  apply le_antisymm (gaussMaximum_mul_le v P Q)
  by_cases hP : gaussMaximum v P = 0
  · simp [hP]
  by_cases hQ : gaussMaximum v Q = 0
  · simp [hQ]
  obtain ⟨i, hi, hi'⟩ := exists_first_maximum v P hP
  obtain ⟨j, hj, hj'⟩ := exists_first_maximum v Q hQ
  let s := Finset.antidiagonal (i + j)
  let f (k : ℕ × ℕ) := P.coeff k.1 * Q.coeff k.2
  have hmem : (i, j) ∈ s := by simp [s]
  have hsmall : ∀ k ∈ s \ {(i, j)}, v (f k) < v (f (i, j)) := by
    intro k hk
    obtain ⟨hks, hne⟩ := Finset.mem_sdiff.mp hk
    have hsum := Finset.mem_antidiagonal.mp hks
    have hne' : k ≠ (i, j) := by simpa only [Finset.mem_singleton] using hne
    have hearly : k.1 < i ∨ k.2 < j := by
      by_contra! hn
      exact hne' (Prod.ext (by omega) (by omega))
    change v (P.coeff k.1 * Q.coeff k.2) < v (P.coeff i * Q.coeff j)
    simp only [map_mul, hi, hj]
    rcases hearly with h | h
    · exact (mul_le_mul_of_nonneg_left (coefficient_le_gaussMaximum v Q k.2) zero_le).trans_lt
        (mul_lt_mul_of_pos_right (hi' k.1 h) (zero_lt_iff.mpr hQ))
    · exact (mul_le_mul_of_nonneg_right (coefficient_le_gaussMaximum v P k.1) zero_le).trans_lt
        (mul_lt_mul_of_pos_left (hj' k.2 h) (zero_lt_iff.mpr hP))
  have hlarge := v.map_sum_eq_of_lt hmem hsmall
  have he : v ((P * Q).coeff (i + j)) = gaussMaximum v P * gaussMaximum v Q := by
    rw [Polynomial.coeff_mul]
    exact hlarge.trans (by simp [f, map_mul, hi, hj])
  rw [← he]
  exact coefficient_le_gaussMaximum v (P * Q) _

def gaussValuation (v : Valuation E Γ₀) : Valuation E[X] Γ₀ where
  toFun := gaussMaximum v
  map_zero' := gaussMaximum_zero v
  map_one' := by simpa only [map_one, gaussMaximum_C] using (gaussMaximum_C v (1 : E))
  map_mul' := gaussMaximum_mul v
  map_add_le_max' P Q := by
    apply (gaussMaximum_le_iff _ _ _).mpr
    intro n
    rw [Polynomial.coeff_add]
    exact (v.map_add _ _).trans (max_le_max (coefficient_le_gaussMaximum v P n)
      (coefficient_le_gaussMaximum v Q n))

@[simp] theorem gaussValuation_apply (v : Valuation E Γ₀) (P : E[X]) :
    gaussValuation v P = gaussMaximum v P := rfl

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
