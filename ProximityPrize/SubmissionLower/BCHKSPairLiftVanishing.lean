import ProximityPrize.SubmissionLower.BCHKSFunctionField
import ProximityPrize.SubmissionLower.BCHKSLifts
import ProximityPrize.SubmissionLower.BCHKSRationalRootVanishing
import ProximityPrize.SubmissionLower.BCHKSParameters
import ProximityPrize.SubmissionLower.BCHKSRationalRootBridge

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions

variable {F : Type} [Field F] [Fintype F]

/-- One coefficient of a denominator-cleared function-field lift is zero if it
has more good pair specializations than its regular-weight root bound. -/
theorem functionField_coefficient_eq_zero_of_many_pair_roots
    {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (D d t : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (α : ℕ → 𝕃 H) (β : ℕ → 𝒪 H) (C : ℕ → F[X])
    (hembed : embeddingOf𝒪Into𝕃 H (β t) =
      α t * liftToFunctionField (H := H) (C t))
    (hC : C t ≠ 0)
    (hweight : regularWeight hH (β t) D ≤
      (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (hden : ∀ z : T, (C t).eval (z : F) ≠ 0)
    (hspecialize : ∀ z : T, piZOfDiv (z : F) (root z) (β t) (C t) = 0)
    (hcard : ((2 * t + 1) * d * D) * H.natDegree < T.card) :
    α t = 0 := by
  classical
  letI : Fact (0 < H.natDegree) := ⟨hH⟩
  have hsubset : (↑T : Set F) ⊆ rationalVanishingSet (β t) := by
    intro z hz
    let zT : T := ⟨z, hz⟩
    refine ⟨root zT, ?_⟩
    exact (piZOfDiv_eq_zero_iff z (root zT) (β t) (hden zT)).mp
      (hspecialize zT)
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
        have := hweight
        rw [hw] at this
        exact WithBot.coe_le_coe.mp this
      change ((w * H.natDegree : ℕ) : WithBot ℕ) <
        ((Set.ncard (rationalVanishingSet (β t)) : ℕ) : WithBot ℕ)
      apply WithBot.coe_lt_coe.mpr
      exact (Nat.mul_le_mul_right H.natDegree hwle).trans_lt (hcard.trans_le hTcard)
  have hβzero : embeddingOf𝒪Into𝕃 H (β t) = 0 :=
    embedding_eq_zero_of_many_rational_roots hH (β t) D hD hncard
  rw [hembed] at hβzero
  exact (mul_eq_zero.mp hβzero).resolve_right (liftToFunctionField_ne_zero hC)


/-- General denominator version: the clearing denominator may itself be a
regular element of `𝒪 H` (as happens for `W^(t+1) ξ^E`), rather than a lifted
base polynomial.  Root counting concerns the numerator `β` directly. -/
theorem functionField_coefficient_eq_zero_of_many_pair_roots_regular_den
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
    let zT : T := ⟨z, hz⟩
    exact ⟨root zT, hspecialize zT⟩
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
        have := hweight
        rw [hw] at this
        exact WithBot.coe_le_coe.mp this
      change ((w * H.natDegree : ℕ) : WithBot ℕ) <
        ((Set.ncard (rationalVanishingSet (β t)) : ℕ) : WithBot ℕ)
      apply WithBot.coe_lt_coe.mpr
      exact (Nat.mul_le_mul_right H.natDegree hwle).trans_lt (hcard.trans_le hTcard)
  have hβzero := embedding_eq_zero_of_many_rational_roots hH (β t) D hD hncard
  rw [hembed] at hβzero
  exact (mul_eq_zero.mp hβzero).resolve_right hden


/-- Simultaneous regular-denominator version. -/
theorem functionField_middle_coefficients_eq_zero_of_many_pair_roots_regular_den
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
  apply functionField_coefficient_eq_zero_of_many_pair_roots_regular_den
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

/-- Simultaneous form for every coefficient strictly between `k` and `DX`.
The uniform pair-fiber bound dominates every coefficient's individual
`(2t+1)dD dH` root bound. -/
theorem functionField_middle_coefficients_eq_zero_of_many_pair_roots
    {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (D d k DX e : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (α : ℕ → 𝕃 H) (β : ℕ → 𝒪 H) (C : ℕ → F[X])
    (hembed : ∀ t, k < t → t < DX →
      embeddingOf𝒪Into𝕃 H (β t) = α t * liftToFunctionField (H := H) (C t))
    (hC : ∀ t, k < t → t < DX → C t ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight hH (β t) D ≤
        (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (hden : ∀ t, k < t → t < DX → ∀ z : T, (C t).eval (z : F) ≠ 0)
    (hspecialize : ∀ t, k < t → t < DX → ∀ z : T,
      piZOfDiv (z : F) (root z) (β t) (C t) = 0)
    (hcard : 2 * DX * H.natDegree * d * D + e + 1 < T.card) :
    ∀ t, k < t → t < DX → α t = 0 := by
  intro t hkt htDX
  apply functionField_coefficient_eq_zero_of_many_pair_roots hH D d t hD α β C
    (hembed t hkt htDX) (hC t hkt htDX) (hweight t hkt htDX) T root
    (hden t hkt htDX) (hspecialize t hkt htDX)
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

/-- Generic pole-removal count: deleting at most `B` bad points from a fiber of
size greater than `A+B` leaves more than `A` good points. -/
theorem card_sdiff_gt_of_card_gt_add
    {ι : Type} [DecidableEq ι] (S bad : Finset ι) (A B : ℕ)
    (hbad : bad.card ≤ B) (hlarge : A + B < S.card) :
    A < (S \ bad).card := by
  have hinter : (S ∩ bad).card ≤ bad.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hsplit := Finset.card_sdiff_add_card_inter S bad
  omega

/-- Pole-removal arithmetic with the BCHKS uniform coefficient threshold. -/
theorem pair_fiber_after_pole_removal_large
    {ι : Type} [DecidableEq ι] (S poles : Finset ι)
    (DX dH d D e : ℕ) (hpoles : poles.card ≤ e + 1)
    (hfiber : 2 * DX * dH * d * D + (e + 1) < S.card) :
    2 * DX * dH * d * D < (S \ poles).card := by
  exact card_sdiff_gt_of_card_gt_add S poles
    (2 * DX * dH * d * D) (e + 1) hpoles hfiber

end ProximityPrize.SubmissionLower
