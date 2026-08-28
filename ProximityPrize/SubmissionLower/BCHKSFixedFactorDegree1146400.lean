import ProximityPrize.SubmissionLower.BCHKSFixedFactorPolynomialAlignment6400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

open FixedFactorCover6400
open FixedFactorPolynomialAlignment6400

/-- Complete closure for an already-selected score-64 irreducible factor of
positive outer degree at most 114, using the one-factor universal-numerator
ledger uniformly in every positive degree. -/
theorem fixed_factor_degree_le_114_alignment_6400
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↑S → Polynomial IRSProfile.Field)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hDcap : D ≤ 1898945373)
    (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424)
    (hPdeg : ∀ z : ↑S, (P z).natDegree ≤ 131071)
    (hAcard : ∀ z : ↑S, 185364 ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + z.1 * U 1 i)
    (hRroot : ∀ z : ↑S, triEval R z.1 (P z) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ p₀ p₁ : IRSProfile.Field[X], ∃ T : Finset IRSProfile.Field,
      ∃ hTsub : T ⊆ S, bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTsub hz⟩ = p₀ + Polynomial.C z * p₁ := by
  exact fixed_factor_polynomial_alignment_6400 U S A P R hR hpos hd
    D hDcap hYZ hweighted hPdeg hAcard hagree hRroot hS

end ProximityPrize.SubmissionLower
