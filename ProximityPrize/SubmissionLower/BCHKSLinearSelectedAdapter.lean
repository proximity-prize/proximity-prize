import ProximityPrize.SubmissionLower.BCHKSLinearSelectedCore
import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Put `Z=z` and `X=x` in a polynomial in `F[Z][X][Y]`, leaving `Y`. -/
noncomputable def linearHSpecialization {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (z x : F) : F[X] :=
  R.map ((Polynomial.evalRingHom x).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)))

/-- Put `X=x` and the symbolic affine value `Y=U₀(x)+Z U₁(x)` in `R`.
The result is a polynomial in `Z`. -/
noncomputable def linearQSpecialization {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (U₀ U₁ : F → F) (x : F) : F[X] :=
  Polynomial.eval (Polynomial.C (U₀ x) + Polynomial.X * Polynomial.C (U₁ x))
    (triSpecializeX R x)

/-- Adapter from a selected trivariate linear factor to the elementary core.
The leading-coefficient exceptional set is explicit: this is useful because
its cardinality is normally discharged by the usual roots bound. -/
theorem bchksLinearSelectedAdapter
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (k DZ errors : ℕ) (R : Polynomial (Polynomial (Polynomial F))) (T Bad : Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F) (Arow : F → Finset F)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ k)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hagree : ∀ z ∈ T, ∀ x ∈ Arow z,
      (P z).eval x = U₀ x + z * U₁ x)
    (hrow : ∀ z ∈ T, Fintype.card F - errors ≤ (Arow z).card)
    (hTcard : (errors + 1) + Bad.card < T.card)
    (hcount : (Fintype.card F - errors - k) * (T.card - Bad.card) >
      (Fintype.card F - k) * DZ)
    (hQdeg : ∀ x, (linearQSpecialization R U₀ U₁ x).natDegree ≤ DZ)
    (hHdeg : ∀ z ∈ T, z ∉ Bad → ∀ x,
      (linearHSpecialization R z x).natDegree = 1)
    (hstageP : ∀ z x,
      (linearHSpecialization R z x).eval ((P z).eval x) =
        (triEval R z (P z)).eval x)
    (hstageQ : ∀ z x,
      (linearQSpecialization R U₀ U₁ x).eval z =
        (linearHSpecialization R z x).eval (U₀ x + z * U₁ x)) :
    ∃ Tgood : Finset F, Tgood ⊆ T ∧ errors + 1 < Tgood.card ∧
      ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
        ∀ z ∈ Tgood, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let Tgood := T.filter fun z => z ∉ Bad
  have hTgood_sub : Tgood ⊆ T := Finset.filter_subset _ _
  have hTgood_card : errors + 1 < Tgood.card := by
    have hs : (T.filter fun z => z ∈ Bad).card ≤ Bad.card :=
      Finset.card_le_card (by intro z hz; exact (Finset.mem_filter.mp hz).2)
    have hp := Finset.filter_card_add_filter_neg_card_eq_card
      (s := T) (p := fun z => z ∉ Bad)
    simp only [not_not] at hp
    dsimp [Tgood]
    omega
  let A : Finset F := Finset.univ.filter fun x =>
    DZ < (Tgood.filter fun z => x ∈ Arow z).card
  have hAcard : k + 1 ≤ A.card := by
    apply many_large_fibers Tgood Arow (Fintype.card F) errors k DZ rfl
    · intro z hz
      exact hrow z (hTgood_sub hz)
    · have hs : (T.filter fun z => z ∈ Bad).card ≤ Bad.card :=
        Finset.card_le_card (by intro z hz; exact (Finset.mem_filter.mp hz).2)
      have hp := Finset.filter_card_add_filter_neg_card_eq_card
        (s := T) (p := fun z => z ∉ Bad)
      simp only [not_not] at hp
      have hlower : T.card - Bad.card ≤ Tgood.card := by
        dsimp [Tgood]
        omega
      exact lt_of_lt_of_le hcount (Nat.mul_le_mul_left _ hlower)
  let Fib : {x // x ∈ A} → Finset F := fun x =>
    Tgood.filter fun z => (x : F) ∈ Arow z
  have hcore := bchksLinearSelectedCore k DZ Tgood A P U₀ U₁
    (linearQSpecialization R U₀ U₁) (linearHSpecialization R)
    (fun z hz => hPdeg z (hTgood_sub hz)) hAcard Fib
    (by intro x; exact (Finset.mem_filter.mp x.property).2)
    (by intro x hx; exact hQdeg (x : F))
    (by
      intro x z hz
      have hzgood := (Finset.mem_filter.mp hz).1
      have hzrow := (Finset.mem_filter.mp hz).2
      rw [hstageQ, ← hagree z (hTgood_sub hzgood) x hzrow, hstageP,
        hvan z (hTgood_sub hzgood)]
      simp)
    (by
      intro z hz x hx
      exact hHdeg z (hTgood_sub hz) (Finset.mem_filter.mp hz).2 x)
    (by
      intro z hz x hx
      rw [hstageP, hvan z (hTgood_sub hz)]
      simp)
    (by intro z hz x hx hQ; rw [← hstageQ, hQ]; simp)
  exact ⟨Tgood, hTgood_sub, hTgood_card, hcore⟩

end ProximityPrize.SubmissionLower
