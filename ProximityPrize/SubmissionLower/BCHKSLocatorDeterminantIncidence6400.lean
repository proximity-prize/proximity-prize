import ProximityPrize.SubmissionLower.BCHKSLocatorRootPins6400
import ProximityPrize.SubmissionLower.BCHKSFixedObstructionIncidence6400

/-!
# Incidence from a rank-two locator determinant to a fixed container

Two parameter-dependent multiplier relations give a determinant obstruction
at every actual error coordinate.  Once the already-certified score-63.99
slopes are removed, every remaining error support has at least `76771`
coordinates.  This module checks that even twice the full locator diagonal
degree is cheap enough to force `49622` coordinate obstructions to vanish
identically in the challenge parameter.  That is exactly the container size
consumed by `BCHKSLocatorContainerAlignment6400`.
-/

namespace ProximityPrize.SubmissionLower

set_option autoImplicit false

open Polynomial

variable {F : Type} [Field F]

/-- A deliberately conservative parameter-degree allowance for the
determinant of two locator multiplier relations. -/
abbrev score6400PairDetParameterCap : ℕ := 2 * 47917457026029

/-- Exact incidence margin after reserving the entire accepted score-63.99
numerator. -/
theorem score6400_pairDet_container_incidence_numeric
    (tcard : ℕ) (ht : 174972148031419760 < tcard) :
    262144 * score6400PairDetParameterCap <
      (76771 - 49621) * tcard := by
  norm_num [score6400PairDetParameterCap] at ht ⊢
  nlinarith

/-- Two semilinear multiplier relations annihilate the error through their
alternating determinant.  At a genuine error coordinate the determinant
itself must therefore vanish. -/
theorem pairDet_mul_error_eq_zero
    (A₀ B₀ A₁ B₁ e ep : F)
    (h₀ : A₀ * e + B₀ * ep = 0)
    (h₁ : A₁ * e + B₁ * ep = 0) :
    (A₀ * B₁ - A₁ * B₀) * e = 0 := by
  linear_combination B₁ * h₀ - B₀ * h₁

theorem pairDet_eq_zero_of_error_ne_zero
    (A₀ B₀ A₁ B₁ e ep : F)
    (he : e ≠ 0)
    (h₀ : A₀ * e + B₀ * ep = 0)
    (h₁ : A₁ * e + B₁ * ep = 0) :
    A₀ * B₁ - A₁ * B₀ = 0 := by
  exact (mul_eq_zero.mp
    (pairDet_mul_error_eq_zero A₀ B₀ A₁ B₁ e ep h₀ h₁)).resolve_right he

/-- Coordinate form of the rank-two determinant incidence step with an
explicit parameter-degree budget.  `E z` is the actual error support and
`G i` is the determinant obstruction after specializing the evaluation
coordinate `i`, leaving a univariate polynomial in the challenge. -/
theorem score6400_pairDet_gives_fixed_container_of_cap
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (E : F → Finset I) (G : I → F[X])
    (parameterCap : ℕ)
    (hn : Fintype.card I = 262144)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ parameterCap)
    (hincidence : 262144 * parameterCap <
      (76771 - 49621) * T.card) :
    49622 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  obtain ⟨z, hzT, hzlarge⟩ :=
    exists_many_zero_obstruction_agreements
      T E G 262144 76771 49621 parameterCap
      hn hEcard (fun z hz i hi => Or.inr (hroot z hz i hi)) hdegree
      hincidence
  have hsub : (E z).filter (fun i => G i = 0) ⊆
      Finset.univ.filter fun i : I => G i = 0 := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  exact hzlarge.trans (Finset.card_le_card hsub)

/-- The original twice-diagonal-degree specialization of the generic
incidence theorem. -/
theorem score6400_pairDet_gives_fixed_container
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq F]
    (T : Finset F) (E : F → Finset I) (G : I → F[X])
    (hn : Fintype.card I = 262144)
    (hT : 174972148031419760 < T.card)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ score6400PairDetParameterCap) :
    49622 ≤ (Finset.univ.filter fun i : I => G i = 0).card := by
  exact score6400_pairDet_gives_fixed_container_of_cap
    T E G score6400PairDetParameterCap hn hEcard hroot hdegree
      (score6400_pairDet_container_incidence_numeric T.card hT)

end ProximityPrize.SubmissionLower
