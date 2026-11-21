import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace SplitCut

open Polynomial

/-- Polynomial nullspace compression. Rows may have degree `D`. With `m`
    independent rows it suffices to enforce all their coefficients below `p`.
    The vector returned has enough space left for substitution of the scalar
    polynomial, whose Y-powers consume at most `D` abscissa degrees. -/
theorem compress_rows {F : Type*} [Field F] (n m p D : ℕ) (hD : D < p)
    (hdim : m*p < n*(p-D)) (A : Fin m → Fin n → F[X])
    (hA : ∀ i j, (A i j).natDegree ≤ D) :
    ∃ w : Fin n → degreeLT F (p-D), w ≠ 0 ∧
      ∀ i, ∑ j, A i j * (w j : F[X]) = 0 := by
  classical
  have hs (w : Fin n → degreeLT F (p-D)) (i : Fin m) :
      (∑ j, A i j * (w j : F[X])) ∈ degreeLT F p := by
    apply Submodule.sum_mem
    intro j _
    by_cases hw : (w j : F[X]) = 0
    · simp [hw]
    by_cases ha : A i j = 0
    · simp [ha]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero ha hw)).mp
    have h := (natDegree_lt_iff_degree_lt hw).mpr
      (mem_degreeLT.mp (w j).property)
    have := natDegree_mul_le (p := A i j) (q := (w j : F[X]))
    have := hA i j
    omega
  let M : (Fin n → degreeLT F (p-D)) →ₗ[F] (Fin m → degreeLT F p) :=
    { toFun := fun w i => ⟨∑ j, A i j * (w j : F[X]), hs w i⟩
      map_add' := by
        intro w z
        funext i
        apply Subtype.ext
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext i
        apply Subtype.ext
        simp [Finset.smul_sum] }
  have hd (a b : ℕ) : Module.finrank F (Fin a → degreeLT F b) = a*b := by
    simp [Module.finrank_pi_fintype, (degreeLTEquiv F b).finrank_eq]
  have hni : ¬ Function.Injective M := fun hi => hdim.not_ge
    (by simpa only [hd] using LinearMap.finrank_le_finrank_of_injective hi)
  rw [LinearMap.ker_eq_bot.symm] at hni
  obtain ⟨w, hw, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hni
  refine ⟨w, hn, fun i => ?_⟩
  exact congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hw) i)

/-- The referee's compression guard yields strict surplus for the polynomial
    nullspace after accounting for the known independent multiples. -/
theorem compression_guard {n k p D m : ℕ} (hk : k ≤ n) (hD : D ≤ p)
    (hm : m ≤ n-k) (hg : n*D < k*p) : m*p < n*(p-D) := by
  calc
    m*p ≤ (n-k)*p := Nat.mul_le_mul_right p hm
    _ < n*(p-D) := by
      zify [hk, hD] at hg ⊢
      nlinarith

end SplitCut

