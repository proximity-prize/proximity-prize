import ProximityPrize.SubmissionLower.Z6970PlateauNatural
import ProximityPrize.SubmissionLower.Z6970PlateauEnvelopeFacts

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedPlateauNatural6970

open KoalaPiecewiseTriangle (Line)
open ExpandedPlateauEnvelope6970 (clippedFast billFast clipped_fast_eq)

private theorem ceiling_cast (offset base d : ℕ) (hd : 0 < d) :
    (ceiling (offset - base) d : ℤ) = max 0 (-(((base : ℤ) - offset) / d)) := by
  have pos : (0 : ℤ) < d := by exact_mod_cast hd
  by_cases h : base ≤ offset
  · have hb : (base : ℤ) ≤ offset := by exact_mod_cast h
    have nonneg : 0 ≤ -(((base : ℤ) - offset) / d) := by
      have q : ((base : ℤ) - offset) / d < 1 :=
        (Int.ediv_lt_iff_lt_mul pos).mpr (by simp; omega)
      omega
    rw [max_eq_right nonneg]
    have cast : (ceiling (offset - base) d : ℤ) =
        ((offset : ℤ) - base + ((d : ℤ) - 1)) / d := by
      simp only [ceiling, Int.natCast_ediv, Nat.cast_add, Nat.cast_sub h,
        Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
    rw [cast]
    apply le_antisymm
    · rw [Int.ediv_le_iff_le_mul pos]
      have q := Int.ediv_mul_le ((base : ℤ) - offset) (by omega : (d : ℤ) ≠ 0)
      rw [neg_mul]
      omega
    · apply Int.le_of_lt_add_one
      rw [Int.lt_add_one_iff, neg_le, Int.le_ediv_iff_mul_le pos]
      have q := (Int.ediv_le_iff_le_mul pos).mp
        (le_rfl : ((offset : ℤ) - base + ((d : ℤ) - 1)) / d ≤ _)
      rw [neg_mul]
      omega
  · have hb : (offset : ℤ) ≤ base := by exact_mod_cast (Nat.le_of_not_ge h)
    have gn : 0 ≤ ((base : ℤ) - offset) / d := Int.ediv_nonneg (by omega) (by omega)
    rw [max_eq_left (by omega), Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)]
    have zero : ceiling 0 d = 0 := by
      simpa only [ceiling, Nat.zero_add] using Nat.div_eq_of_lt (show d - 1 < d by omega)
    simp only [zero, Nat.cast_zero]

private theorem clipped_cast (offset lo hi : ℕ) (l : Ray) (hd : 0 < l.slope) :
    (clipped offset lo hi l : ℤ) =
      clippedFast lo hi (⟨(l.base : ℤ) - offset, (l.slope : ℤ)⟩ : Line) := by
  let start := max lo (ceiling (offset - l.base) l.slope)
  have start_cast : (start : ℤ) = max (lo : ℤ) (-(((l.base : ℤ) - offset) / l.slope)) := by
    change ((max lo (ceiling (offset - l.base) l.slope) : ℕ) : ℤ) = _
    rw [Nat.cast_max, ceiling_cast _ _ _ hd, ← max_assoc, max_eq_left (by omega : (0 : ℤ) ≤ lo)]
  have slope_pos : (0 : ℤ) < l.slope := by exact_mod_cast hd
  have start_pos : (offset : ℤ) ≤ l.base + (l.slope : ℤ) * start := by
    have cutoff : -(((l.base : ℤ) - offset) / l.slope) ≤ (start : ℤ) := by
      rw [start_cast]
      exact le_max_right _ _
    rw [neg_le, Int.le_ediv_iff_mul_le slope_pos, neg_mul] at cutoff
    rw [mul_comm (l.slope : ℤ)]
    omega
  simp only [clipped, clippedFast]
  rw [← start_cast]
  change (↑(if hi ≤ start then 0 else polynomial (l.base + l.slope * start - offset) l.slope (hi - start) / 6) : ℤ) =
    if (hi : ℤ) ≤ start then 0 else
      ExpandedPlateauIntegral6970.poly ((l.base : ℤ) - offset + l.slope * start) l.slope
        ((hi : ℤ) - start).toNat / 6
  by_cases h : hi ≤ start
  · have ht : (hi : ℤ) ≤ start := by exact_mod_cast h
    simp [h, ht]
  · have ht : ¬ (hi : ℤ) ≤ start := by exact_mod_cast h
    have hr : ((hi : ℤ) - start).toNat = hi - start := by
      rw [← Nat.cast_sub (show start ≤ hi by omega)]
      simp
    have ho : offset ≤ l.base + l.slope * start := by exact_mod_cast start_pos
    have h₁ : 1 ≤ hi - start := by omega
    have h₂ : 1 ≤ 2 * (hi - start) := by omega
    simp only [h, ht, ite_false, hr, Int.natCast_ediv, polynomial, ExpandedPlateauIntegral6970.poly]
    push_cast [Nat.cast_sub ho, Nat.cast_sub h₁, Nat.cast_sub h₂]
    congr 1
    ring

private theorem clipped_mono (lo hi : ℕ) (l : Ray) (hd : 0 < l.slope) :
    clipped 11835 lo hi l ≤ clipped 10000 lo hi l := by
  have hp : (0 : ℤ) < l.slope := by exact_mod_cast hd
  suffices h : (clipped 11835 lo hi l : ℤ) ≤ clipped 10000 lo hi l by exact_mod_cast h
  rw [clipped_cast _ _ _ _ hd, clipped_cast _ _ _ _ hd,
    clipped_fast_eq _ _ _ hp, clipped_fast_eq _ _ _ hp,
    ExpandedPlateauIntegral6970.clipped_eq, ExpandedPlateauIntegral6970.clipped_eq]
  apply Finset.sum_le_sum
  intro x _
  simp only [Low48PrimaryPivot.twiceTri, Line.at]
  have h : max (0 : ℤ) ((l.base : ℤ) - 11835 + l.slope * x) ≤
      max 0 ((l.base : ℤ) - 10000 + l.slope * x) := max_le_max le_rfl (by omega)
  exact mul_le_mul h (by omega) (by positivity) (le_max_left _ _)

theorem bill_eq (lo hi : ℕ) (l : Ray) (hd : 0 < l.slope) :
    (bill lo hi l : ℤ) = billFast lo hi (⟨(l.base : ℤ) - 10000, (l.slope : ℤ)⟩ : Line) := by
  by_cases h : hi ≤ lo
  · have ht : (hi : ℤ) ≤ lo := by exact_mod_cast h
    simp [bill, billFast, h, ht]
  · have ht : ¬ (hi : ℤ) ≤ lo := by exact_mod_cast h
    simp only [bill, billFast, h, ht, ite_false]
    rw [Nat.cast_sub (clipped_mono lo hi l hd), clipped_cast _ _ _ _ hd, clipped_cast _ _ _ _ hd]
    have off : (l.base : ℤ) - 11835 = (l.base : ℤ) - 10000 - 1835 := by ring
    simpa only [Nat.cast_ofNat, off]

end ExpandedPlateauNatural6970
