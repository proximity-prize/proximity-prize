import ProximityPrize.SubmissionLower.Low48BentLattice

set_option autoImplicit false

namespace Low48BentCount
open Finset
open Low48BentLattice
open K1_13_6_2_4 (Exponent)
open scoped BigOperators
open K1_13_6_2_3_1 (slice_count paired_sum)
open private slice evenSlice oddSlice sum_pair pairedSum from ProximityPrize.SubmissionLower.Fast054
noncomputable section

private def Slices (a : Cap) :=
  Σ h : Fin (2 * a.2 + 1), Σ z : Fin (2 * a.1.t - 2 * h.val + 1),
    Σ y : Fin ((2 * a.1.j - 4 * h.val - 3 * z.val) / 2 + 1),
      Σ x : Fin (2 * a.1.j - 4 * h.val - 3 * z.val - 2 * y.val + 1),
        Fin (2 * a.1.b - h.val - (z.val + y.val + x.val) + 1)

private def slicesEquiv (a : Cap) (ha : Chamber a) : latticePoints a ≃ Slices a where
  toFun e := by
    have he := (coords a e.val).mp e.property
    have hb := he.1
    have hj := he.2.1
    have ht := he.2.2.1
    have hh := he.2.2.2
    let h : Fin (2 * a.2 + 1) := ⟨e.val 4, by omega⟩
    let z : Fin (2 * a.1.t - 2 * h.val + 1) := ⟨e.val 3, by dsimp [h]; omega⟩
    let y : Fin ((2 * a.1.j - 4 * h.val - 3 * z.val) / 2 + 1) :=
      ⟨e.val 2, by dsimp [h, z]; omega⟩
    let x : Fin (2 * a.1.j - 4 * h.val - 3 * z.val - 2 * y.val + 1) :=
      ⟨e.val 1, by dsimp [h, z, y]; omega⟩
    exact ⟨h, z, y, x, ⟨e.val 0, by dsimp [h, z, y, x]; omega⟩⟩
  invFun s := by
    rcases s with ⟨h, z, y, x, u⟩
    have hh := h.isLt
    have hz := z.isLt
    have hy := y.isLt
    have hx := x.isLt
    have hu := u.isLt
    have haB := ha.1
    have haJ := ha.2.1
    have haT := ha.2.2
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val, x.val, y.val, z.val, h.val], (coords a _).mpr ?_⟩
    change u.val + x.val + y.val + z.val + h.val ≤ 2 * a.1.b ∧
      x.val + 2 * y.val + 3 * z.val + 4 * h.val ≤ 2 * a.1.j ∧
      z.val + 2 * h.val ≤ 2 * a.1.t ∧ h.val ≤ 2 * a.2
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv s := by
    rcases s with ⟨⟨h, hh⟩, ⟨z, hz⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨u, hu⟩⟩
    rfl

theorem slice_even_raw (b j i : ℕ) (hi : 3 * i ≤ j) (hb : 2 * j ≤ b) :
    slice (2 * j - 3 * (2 * i)) (b - 2 * i) =
      evenSlice ((b : ℚ) / 2) j i := by
  have hW : 2 * j - 3 * (2 * i) = 2 * (j - 3 * i) := by omega
  have hC : 2 * i ≤ b := by omega
  rw [hW]
  simp only [slice, evenSlice, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.mul_mod_right, Nat.cast_zero, add_zero]
  push_cast [Nat.cast_sub hi, Nat.cast_sub hC]
  ring

theorem slice_odd_raw (b j i : ℕ) (hi : 3 * i + 3 ≤ j) (hb : 2 * j ≤ b) :
    slice (2 * j - 3 * (2 * i + 1)) (b - (2 * i + 1)) =
      oddSlice ((b : ℚ) / 2) j i := by
  have hW : 3 * (2 * i + 1) ≤ 2 * j := by omega
  have hC : 2 * i + 1 ≤ b := by omega
  have hdiv : (2 * j - 3 * (2 * i + 1)) / 2 = j - (3 * i + 2) := by omega
  have hmod : (2 * j - 3 * (2 * i + 1)) % 2 = 1 := by omega
  simp only [slice, oddSlice, hdiv, hmod]
  push_cast [Nat.cast_sub hW, Nat.cast_sub hC, Nat.cast_sub (show 3 * i + 2 ≤ j by omega)]
  ring

def sliceFour (b j t : ℚ) : ℚ := pairedSum b j t + evenSlice b j t

private theorem sum_slice (b j t : ℕ) (hj : 3 * t ≤ j) (hb : 2 * j ≤ b) :
    (∑ z ∈ range (2 * t + 1), slice (2 * j - 3 * z) (b - z)) =
      sliceFour ((b : ℚ) / 2) j t := by
  rw [sliceFour, sum_range_succ, sum_pair, slice_even_raw _ _ _ hj hb, ← paired_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [slice_even_raw _ _ _ (by omega) hb, slice_odd_raw _ _ _ (by omega) hb]
  rfl

theorem card_eq (a : Cap) (ha : Chamber a) :
    ((latticePoints a).ncard : ℚ) =
      ∑ h ∈ range (2 * a.2 + 1),
        sliceFour ((a.1.b : ℚ) - (h : ℚ) / 2) (a.1.j - 2 * (h : ℚ)) (a.1.t - (h : ℚ)) := by
  classical
  let : Fintype (Slices a) := by unfold Slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (slicesEquiv a ha), Nat.card_eq_fintype_card]
  unfold Slices
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun h =>
    ∑ z : Fin (2 * a.1.t - 2 * h + 1),
    ∑ y : Fin ((2 * a.1.j - 4 * h - 3 * z.val) / 2 + 1),
    ∑ x : Fin (2 * a.1.j - 4 * h - 3 * z.val - 2 * y.val + 1),
      ((2 * a.1.b - h - (z.val + y.val + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro h hh
  have hh' := mem_range.mp hh
  obtain ⟨hB, hJ, hT⟩ := ha
  have hT' : h ≤ a.1.t := by omega
  have hJ' : 2 * h ≤ a.1.j := by omega
  have hB' : h ≤ 2 * a.1.b := by omega
  have hTW : 2 * a.1.t - 2 * h = 2 * (a.1.t - h) := by omega
  have hJW : 2 * a.1.j - 4 * h = 2 * (a.1.j - 2 * h) := by omega
  rw [hTW, hJW]
  rw [Fin.sum_univ_eq_sum_range (fun z =>
    ∑ y : Fin ((2 * (a.1.j - 2 * h) - 3 * z) / 2 + 1),
    ∑ x : Fin (2 * (a.1.j - 2 * h) - 3 * z - 2 * y.val + 1),
      ((2 * a.1.b - h - (z + y.val + x.val) + 1 : ℕ) : ℚ))]
  calc
    _ = ∑ z ∈ range (2 * (a.1.t - h) + 1),
        slice (2 * (a.1.j - 2 * h) - 3 * z) (2 * a.1.b - h - z) := by
      apply sum_congr rfl
      intro z hz
      have hz' := mem_range.mp hz
      have hw : 2 * (a.1.j - 2 * h) - 3 * z ≤ 2 * a.1.b - h - z := by omega
      rw [← slice_count _ _ hw]
      rw [Fin.sum_univ_eq_sum_range (fun y =>
        ∑ x : Fin (2 * (a.1.j - 2 * h) - 3 * z - 2 * y + 1),
          ((2 * a.1.b - h - (z + y + x.val) + 1 : ℕ) : ℚ))]
      apply sum_congr rfl
      intro y _
      rw [Fin.sum_univ_eq_sum_range (fun x =>
        ((2 * a.1.b - h - (z + y + x) + 1 : ℕ) : ℚ))]
      simp only [Nat.sub_sub, Nat.add_assoc]
    _ = _ := by
      rw [sum_slice _ _ _ (by omega) (by omega)]
      push_cast [Nat.cast_sub hT', Nat.cast_sub hJ', Nat.cast_sub hB']
      congr 1
      ring

end
end Low48BentCount
