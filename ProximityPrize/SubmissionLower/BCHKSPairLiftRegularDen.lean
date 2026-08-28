import ProximityPrize.SubmissionLower.BCHKSPairLiftVanishing

namespace RationalFunctions.HenselNumerators

open Polynomial Polynomial.Bivariate ProximityPrize.SubmissionLower

variable {F : Type} [Field F] [Fintype F]

/-- Root-counting with the actual BCHKS regular denominator, rather than the
more restrictive special case where the denominator is lifted from `F[Z]`. -/
theorem functionField_coefficient_eq_zero_of_many_pair_roots_regularDen
    {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (D d t : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (α : ℕ → 𝕃 H) (β den : ℕ → 𝒪 H)
    (hembed : embeddingOf𝒪Into𝕃 H (β t) =
      α t * embeddingOf𝒪Into𝕃 H (den t))
    (hden : embeddingOf𝒪Into𝕃 H (den t) ≠ 0)
    (hweight : regularWeight hH (β t) D ≤
      (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (hspecialize : ∀ z : T, piZ (z : F) (root z) (β t) = 0)
    (hcard : ((2 * t + 1) * d * D) * H.natDegree < T.card) :
    α t = 0 := by
  classical
  letI : Fact (0 < H.natDegree) := ⟨hH⟩
  have hsubset : (↑T : Set F) ⊆ rationalVanishingSet (β t) := by
    intro z hz
    exact ⟨root ⟨z, hz⟩, hspecialize ⟨z, hz⟩⟩
  have hTcard : T.card ≤ Set.ncard (rationalVanishingSet (β t)) := by
    rw [← Set.ncard_coe_finset T]
    exact Set.ncard_le_ncard hsubset
  have hncard :
      (regularWeight hH (β t) D) * H.natDegree <
        Set.ncard (rationalVanishingSet (β t)) := by
    cases hw : regularWeight hH (β t) D with
    | bot => simp [Nat.ne_of_gt hH]
    | coe w =>
      have hwle : w ≤ (2 * t + 1) * d * D := by
        have hw' := hweight
        rw [hw] at hw'
        exact WithBot.coe_le_coe.mp hw'
      change ((w * H.natDegree : ℕ) : WithBot ℕ) <
        ((Set.ncard (rationalVanishingSet (β t)) : ℕ) : WithBot ℕ)
      exact WithBot.coe_lt_coe.mpr
        ((Nat.mul_le_mul_right H.natDegree hwle).trans_lt (hcard.trans_le hTcard))
  have hβzero : embeddingOf𝒪Into𝕃 H (β t) = 0 :=
    embedding_eq_zero_of_many_rational_roots hH (β t) D hD hncard
  rw [hembed] at hβzero
  exact (mul_eq_zero.mp hβzero).resolve_right hden


/-- Uniform middle-coefficient form for the actual regular denominator. -/
theorem functionField_middle_coefficients_eq_zero_regularDen
    {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (D d k DX e : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (α : ℕ → 𝕃 H) (β den : ℕ → 𝒪 H)
    (hembed : ∀ t, k < t → t < DX →
      embeddingOf𝒪Into𝕃 H (β t) = α t * embeddingOf𝒪Into𝕃 H (den t))
    (hden : ∀ t, k < t → t < DX → embeddingOf𝒪Into𝕃 H (den t) ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight hH (β t) D ≤
        (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (hspecialize : ∀ t, k < t → t < DX → ∀ z : T,
      piZ (z : F) (root z) (β t) = 0)
    (hcard : 2 * DX * H.natDegree * d * D + e + 1 < T.card) :
    ∀ t, k < t → t < DX → α t = 0 := by
  intro t hkt htDX
  apply functionField_coefficient_eq_zero_of_many_pair_roots_regularDen
    hH D d t hD α β den (hembed t hkt htDX) (hden t hkt htDX)
      (hweight t hkt htDX) T root (hspecialize t hkt htDX)
  have hcoef : 2 * t + 1 ≤ 2 * DX := by omega
  have hmul := Nat.mul_le_mul_right (d * D * H.natDegree) hcoef
  have hone : ((2 * t + 1) * d * D) * H.natDegree ≤
      2 * DX * H.natDegree * d * D := by
    calc
      ((2 * t + 1) * d * D) * H.natDegree =
          (2 * t + 1) * (d * D * H.natDegree) := by ring
      _ ≤ 2 * DX * (d * D * H.natDegree) := hmul
      _ = 2 * DX * H.natDegree * d * D := by ring
  omega

end RationalFunctions.HenselNumerators
