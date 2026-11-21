import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.KoalaOpenChart

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace SplitCut

open Polynomial

/-- After compression, a polynomial relation over the differential constants can
    be evaluated at an independent abscissa. -/
theorem fresh_identity {C E : Type*} [Field C] [Field E] [Algebra C E]
    (p : ℕ) [CharP C p] (D : Derivation C E E) (x : E) (hx : D x = 1)
    (P : C[X]) (hp : P.natDegree < p) (hz : aeval x P = 0) : P = 0 := by
  by_cases h : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h] at hz ⊢
    simpa using (algebraMap C E).injective (by simpa using hz :
      algebraMap C E (P.coeff 0) = algebraMap C E 0)
  · have hd : aeval x P.derivative = 0 := by
      have e := D.map_aeval P x
      simpa [hz, hx] using e.symm
    have lt := natDegree_derivative_lt h
    have hd0 := fresh_identity p D x hx P.derivative (lt.trans hp) hd
    have ce := congrArg (fun Q : C[X] => Q.coeff (P.natDegree - 1)) hd0
    have hh : P.natDegree - 1 + 1 = P.natDegree := by omega
    simp only [coeff_derivative, hh, coeff_natDegree, coeff_zero] at ce
    have hhC : ((P.natDegree-1 : ℕ) : C) + 1 = (P.natDegree : C) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast (R := C)) hh
    rw [hhC] at ce
    have hn : (P.natDegree : C) ≠ 0 := by
      intro hn
      have hdv := (CharP.cast_eq_zero_iff C p P.natDegree).mp hn
      exact hp.not_ge (Nat.le_of_dvd (by omega) hdv)
    rcases mul_eq_zero.mp ce with h₁ | h₂
    · exact leadingCoeff_eq_zero.mp h₁
    · exact (hn h₂).elim
termination_by P.natDegree

/-- The opposite-axis terms in the seed-plane intersection are the row sums
    of the Sylvester determinant. -/
theorem seed_resultant {F : Type*} [Field F] (P Q : F[X][X])
    (a b c d : ℕ) (hp : P.natDegree ≤ a) (hq : Q.natDegree ≤ c)
    (hpc : ∀ i, (P.coeff i).natDegree ≤ b) (hqc : ∀ i, (Q.coeff i).natDegree ≤ d) :
    (P.resultant Q).natDegree ≤ a*d+c*b := by
  exact (natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree b d hpc hqc).trans
    (by simpa [add_comm] using Nat.add_le_add (Nat.mul_le_mul_right d hp) (Nat.mul_le_mul_right b hq))

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

abbrev Profile := ℚ → ℚ → ℚ → ℚ → ℚ

/-- Nef abscissa of the Hirzebruch surface, velocity, and the two seed lines. -/
def ambient (h t u v : ℚ) : ℚ := (t+1)*(h+t+1)*(u+1)*(v+1)

def cut (a b c d : ℚ) (P : Profile) (h t u v : ℚ) : ℚ :=
  P h t u v - P (h-a) (t-b) (u-c) (v-d)

/-- The mixed multiplicity of a root equation, its tangent, and two successive
    Taylor sections in the four-graded Hilbert polynomial. -/
theorem mixed_cut (e v₀ v₁ a b c₀ c₁ x y z₀ z₁ h t u w : ℚ) :
    cut (x-2*y) y z₀ z₁
      (cut (a-2*b) b c₀ c₁ (cut (e-2) 1 v₀ v₁ (cut e 0 v₀ v₁ ambient))) h t u w =
      e*(c₀*z₁+c₁*z₀) +
      (v₀*c₁+v₁*c₀)*((2*e-2)*y+x) + (v₀*z₁+v₁*z₀)*((2*e-2)*b+a) +
      2*v₀*v₁*((a-2*b)*y+x*b) := by
  unfold cut ambient
  ring

/-- With fixed side sum, moving area from the shorter side to the longer side
    decreases the remaining lattice-point count. -/
theorem outward_product (L S d : ℕ) (h : S ≤ L) : (L+d)*(S-d) ≤ L*S := by
  by_cases hd : d ≤ S
  · zify [hd] at h ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (Int.natCast_nonneg d),
      sq_nonneg (d : ℤ)]
  · simp [Nat.sub_eq_zero_of_le (by omega : S ≤ d)]

theorem balanced_product {u v l r : ℤ} (hs : u+v=l+r) (h₀ : l≤r) (h₁ : r≤l+1) :
    u*v ≤ l*r := by
  have hv : v = l+r-u := by omega
  subst v
  by_cases h : u ≤ l
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (h.trans h₀))]
  · have h' : r ≤ u := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (sub_nonneg.mpr (h₀.trans h'))]

end SplitCut

#print axioms SplitCut.fresh_identity
#print axioms SplitCut.seed_resultant
#print axioms SplitCut.compress_rows
#print axioms SplitCut.compression_guard
#print axioms SplitCut.mixed_cut
#print axioms SplitCut.outward_product
#print axioms SplitCut.balanced_product
