import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 1000000

/-- Lagrange interpolation on exactly `k+1` nodes has degree at most `k`. -/
theorem core_lagrange_natDegree_le
    {F : Type} [Field F] [DecidableEq F]
    (E : Finset F) (U : F → F) (k : ℕ) (hcard : E.card = k + 1) :
    (Lagrange.interpolate E id U).natDegree ≤ k := by
  classical
  let p := Lagrange.interpolate E id U
  change p.natDegree ≤ k
  by_cases hp : p = 0
  · simp [hp]
  · have hd : p.degree < (E.card : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt U (Set.injOn_id (↑E : Set F))
    have hn : p.natDegree < E.card :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hd
    simpa [hcard] using hn

/-- A polynomial of degree at most `DZ` with more than `DZ` distinct selected
roots is zero. -/
theorem selected_polynomial_eq_zero
    {F : Type} [Field F] [DecidableEq F] (DZ : ℕ)
    (Q : F[X]) (S : Finset F) (hdeg : Q.natDegree ≤ DZ)
    (hcard : DZ < S.card) (hzero : ∀ z ∈ S, Q.eval z = 0) : Q = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    Q (ι := {z // z ∈ S}) (f := fun z => (z : F))
  · exact Subtype.val_injective
  · intro z
    exact hzero z z.property
  · simpa [Fintype.card_coe] using hdeg.trans_lt hcard

/-- A nonzero linear polynomial over a field has at most one root. -/
theorem core_linear_root_unique
    {F : Type} [Field F] (H : F[X]) (a b : F)
    (hdeg : H.natDegree = 1) (ha : H.eval a = 0) (hb : H.eval b = 0) : a = b := by
  have hshape : H = Polynomial.C (H.coeff 0) +
      Polynomial.C (H.coeff 1) * Polynomial.X := by
    ext n
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have hne : H ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hc : H.coeff 1 ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  rw [hshape] at ha hb
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X] at ha hb
  apply mul_left_cancel₀ hc
  linear_combination ha - hb

/-- Elementary selected-root scheme: large fibers force every `Q x` to
vanish; uniqueness of a linear root identifies the selected values with an
affine function of `z`; interpolation and polynomial extensionality give a
single affine line of polynomials. -/
theorem bchksLinearSelectedCore
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (k DZ : ℕ) (T A : Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F) (Q : F → F[X])
    (H : F → F → F[X])
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ k)
    (hAcard : k + 1 ≤ A.card)
    (Fib : {x // x ∈ A} → Finset F)
    (hFibcard : ∀ x, DZ < (Fib x).card)
    (hQdeg : ∀ x ∈ A, (Q x).natDegree ≤ DZ)
    (hQzero : ∀ x : {x // x ∈ A}, ∀ z ∈ Fib x, (Q x).eval z = 0)
    (hHdeg : ∀ z ∈ T, ∀ x ∈ A, (H z x).natDegree = 1)
    (hPzero : ∀ z ∈ T, ∀ x ∈ A, (H z x).eval ((P z).eval x) = 0)
    (hQroot : ∀ z ∈ T, ∀ x ∈ A, Q x = 0 →
      (H z x).eval (U₀ x + z * U₁ x) = 0) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ T, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  have hQ : ∀ x ∈ A, Q x = 0 := by
    intro x hx
    exact selected_polynomial_eq_zero DZ (Q x) (Fib ⟨x, hx⟩)
      (hQdeg x hx) (hFibcard ⟨x, hx⟩) (fun z hz => hQzero ⟨x, hx⟩ z hz)
  obtain ⟨E, hEA, hEcard⟩ := Finset.exists_subset_card_eq hAcard
  let p₀ : F[X] := Lagrange.interpolate E id U₀
  let p₁ : F[X] := Lagrange.interpolate E id U₁
  have hp₀ : p₀.natDegree ≤ k := core_lagrange_natDegree_le E U₀ k hEcard
  have hp₁ : p₁.natDegree ≤ k := core_lagrange_natDegree_le E U₁ k hEcard
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z hz
  let q := p₀ + Polynomial.C z * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : {x // x ∈ E} => (x : F)) Subtype.val_injective
  · intro x
    have h0 : p₀.eval (x : F) = U₀ x :=
      Lagrange.eval_interpolate_at_node U₀ (Set.injOn_id (↑E : Set F)) x.property
    have h1 : p₁.eval (x : F) = U₁ x :=
      Lagrange.eval_interpolate_at_node U₁ (Set.injOn_id (↑E : Set F)) x.property
    rw [core_linear_root_unique (H z x) ((P z).eval x)
      (U₀ x + z * U₁ x) (hHdeg z hz x (hEA x.property))
      (hPzero z hz x (hEA x.property))
      (hQroot z hz x (hEA x.property) (hQ x (hEA x.property)))]
    simp [q, h0, h1]
  · have hq : q.natDegree ≤ k :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    rw [Fintype.card_coe, hEcard]
    exact max_lt ((hPdeg z hz).trans_lt (Nat.lt_succ_self k))
      (hq.trans_lt (Nat.lt_succ_self k))

end ProximityPrize.SubmissionLower
