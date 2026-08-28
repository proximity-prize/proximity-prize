import ProximityPrize.SubmissionLower.BCHKSInitialValueAffine

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F] [Fintype F]

/-- Direct alignment for a linear branch.  `Q x` is the polynomial in the
parameter obtained after putting `X=x` and `Y=U₀(x)+Z*U₁(x)` in the selected
factor.  The last hypothesis is precisely the simple-linear-root consequence:
a second root of the specialization is equal to the first one.  Keeping this
statement separate makes the lemma usable without any Hensel weights. -/
theorem bchksLinearFactorDirect
    [DecidableEq F] (k DZ : ℕ) (T A : Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F) (Q : F → F[X])
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ k)
    (hAcard : k + 1 ≤ A.card) (hkF : k < Fintype.card F)
    (Fib : {x // x ∈ A} → Finset F)
    (hFibT : ∀ x, Fib x ⊆ T)
    (hFibcard : ∀ x, DZ < (Fib x).card)
    (hQdeg : ∀ x ∈ A, (Q x).natDegree ≤ DZ)
    (hQzero : ∀ x : {x // x ∈ A}, ∀ z ∈ Fib x,
      (Q x).eval z = 0)
    (hrootUnique : ∀ z ∈ T, ∀ x ∈ A,
      (Q x = 0) → (P z).eval x = U₀ x + z * U₁ x) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ T, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  have hQ : ∀ x ∈ A, Q x = 0 := by
    intro x hx
    let E := Fib ⟨x, hx⟩
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Q x) (ι := {z // z ∈ E}) (f := fun z => (z:F))
    · exact Subtype.val_injective
    · intro z
      exact hQzero ⟨x, hx⟩ z z.property
    · simpa [Fintype.card_coe] using
        (hQdeg x hx).trans_lt (hFibcard ⟨x, hx⟩)
  obtain ⟨E, hEA, hEcard⟩ := Finset.exists_subset_card_eq hAcard
  let p₀ : F[X] := Lagrange.interpolate E id U₀
  let p₁ : F[X] := Lagrange.interpolate E id U₁
  have hp₀ : p₀.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₀ k hEcard
  have hp₁ : p₁.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₁ k hEcard
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z hz
  let q := p₀ + Polynomial.C z * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : {x // x ∈ E} => (x : F)) Subtype.val_injective
  · intro x
    have h0 : p₀.eval (x:F) = U₀ x :=
      Lagrange.eval_interpolate_at_node U₀ (Set.injOn_id (↑E : Set F)) x.property
    have h1 : p₁.eval (x:F) = U₁ x :=
      Lagrange.eval_interpolate_at_node U₁ (Set.injOn_id (↑E : Set F)) x.property
    rw [hrootUnique z hz x (hEA x.property) (hQ x (hEA x.property))]
    simp [q, h0, h1]
  · have hq : q.natDegree ≤ k :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z hz).trans_lt (by simpa [Fintype.card_coe, hEcard]))
      (hq.trans_lt (by simpa [Fintype.card_coe, hEcard]))

end ProximityPrize.SubmissionLower
