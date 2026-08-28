import ProximityPrize.SubmissionLower.BCHKSLinearFactorDirect

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A nonzero linear polynomial over a field has at most one root. -/
theorem linear_root_unique_of_natDegree_eq_one
    (H : F[X]) (a b : F) (hdeg : H.natDegree = 1)
    (ha : H.eval a = 0) (hb : H.eval b = 0) : a = b := by
  have hshape : H = Polynomial.C (H.coeff 0) +
      Polynomial.C (H.coeff 1) * Polynomial.X := by
    ext n
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · have hn : H.natDegree < n.succ.succ := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
      simp
  have hne : H ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hc : H.coeff 1 ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  rw [hshape] at ha hb
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X] at ha hb
  apply (mul_left_cancel₀ hc)
  linear_combination ha - hb

variable [Fintype F]

/-- Final assembly for the degree-one branch.  The auxiliary polynomial `H z x`
records the specialization in the `Y` coordinate at `(z,x)`.  Its two roots
are the selected value `P z` and the affine candidate forced by `Q x = 0`;
linearity therefore supplies exactly the root-uniqueness input required by
`bchksLinearFactorDirect`. -/
theorem bchksLinearBranchFinal
    [DecidableEq F] (k DZ : ℕ) (T A : Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F) (Q : F → F[X])
    (H : F → F → F[X])
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ k)
    (hAcard : k + 1 ≤ A.card) (hkF : k < Fintype.card F)
    (Fib : {x // x ∈ A} → Finset F)
    (hFibT : ∀ x, Fib x ⊆ T)
    (hFibcard : ∀ x, DZ < (Fib x).card)
    (hQdeg : ∀ x ∈ A, (Q x).natDegree ≤ DZ)
    (hQzero : ∀ x : {x // x ∈ A}, ∀ z ∈ Fib x,
      (Q x).eval z = 0)
    (hHdeg : ∀ z ∈ T, ∀ x ∈ A, (H z x).natDegree = 1)
    (hPzero : ∀ z ∈ T, ∀ x ∈ A,
      (H z x).eval ((P z).eval x) = 0)
    (hQroot : ∀ z ∈ T, ∀ x ∈ A, Q x = 0 →
      (H z x).eval (U₀ x + z * U₁ x) = 0) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ T, P z = p₀ + Polynomial.C z * p₁ := by
  apply bchksLinearFactorDirect k DZ T A P U₀ U₁ Q hPdeg hAcard hkF
    Fib hFibT hFibcard hQdeg hQzero
  intro z hz x hx hQ
  exact linear_root_unique_of_natDegree_eq_one (H z x)
    ((P z).eval x) (U₀ x + z * U₁ x) (hHdeg z hz x hx)
    (hPzero z hz x hx) (hQroot z hz x hx hQ)

end ProximityPrize.SubmissionLower
