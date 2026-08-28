import ProximityPrize.SubmissionLower.BCHKSLinearSelectedAdapter

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Final degree-one adapter with a single resultant obstruction.  Algebraic
applications take `Res` to be the resultant in `X` of the two `Y`-coefficients
of the selected factor.  Thus `hregular` is precisely the standard statement
that, away from the roots of that resultant, the specialized leading
coefficient is a unit and the specialization still has `Y`-degree one. -/
theorem bchksLinearDegreeOneFinal
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (k DZ errors badCap : ℕ)
    (R : Polynomial (Polynomial (Polynomial F)))
    (Res : F[X]) (T : Finset F)
    (P : F → F[X]) (U₀ U₁ : F → F) (Arow : F → Finset F)
    (hRes : Res ≠ 0)
    (hResdeg : Res.natDegree ≤ badCap)
    (hregular : ∀ z ∈ T, Res.eval z ≠ 0 → ∀ x,
      (linearHSpecialization R z x).natDegree = 1)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ k)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hagree : ∀ z ∈ T, ∀ x ∈ Arow z,
      (P z).eval x = U₀ x + z * U₁ x)
    (hrow : ∀ z ∈ T, Fintype.card F - errors ≤ (Arow z).card)
    (hTcard : (errors + 1) + badCap < T.card)
    (hcount : (Fintype.card F - errors - k) * (T.card - badCap) >
      (Fintype.card F - k) * DZ)
    (hQdeg : ∀ x, (linearQSpecialization R U₀ U₁ x).natDegree ≤ DZ)
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
  let Bad : Finset F := Res.roots.toFinset
  have hBad : Bad.card ≤ badCap := by
    calc
      Bad.card ≤ Res.roots.card := Multiset.toFinset_card_le _
      _ ≤ Res.natDegree := Polynomial.card_roots' Res
      _ ≤ badCap := hResdeg
  apply bchksLinearSelectedAdapter k DZ errors R T Bad P U₀ U₁ Arow
    hPdeg hvan hagree hrow
  · omega
  · have hsub : T.card - badCap ≤ T.card - Bad.card :=
      Nat.sub_le_sub_left hBad T.card
    exact lt_of_lt_of_le hcount (Nat.mul_le_mul_left _ hsub)
  · exact hQdeg
  · intro z hzT hzBad x
    apply hregular z hzT
    intro heval
    have : z ∈ Bad := by
      dsimp [Bad]
      simp only [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hRes).2 heval
    exact hzBad this
  · exact hstageP
  · exact hstageQ

end ProximityPrize.SubmissionLower
