import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessCounts
import ProximityPrize.SubmissionLower.Koala6844ReceiptsSource


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

private def rectangleRows (a b h : ℕ) :
    SeedlessRectangle a b h ≃ Σ i : Fin a, Fin (min b (h+1-i.val)) where
  toFun ij := ⟨ij.val.1,⟨ij.val.2.val, by
    have hb := ij.val.2.isLt
    have htotal := ij.property
    omega⟩⟩
  invFun ij := ⟨⟨ij.1,⟨ij.2.val, by have := ij.2.isLt; omega⟩⟩, by
    change ij.1.val+ij.2.val ≤ h
    have hb : ij.2.val < h+1-ij.1.val := ij.2.isLt.trans_le (min_le_right _ _)
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def totalRows (n : ℕ) : ℕ := (n+1).choose 2

private theorem totalRows_succ (n : ℕ) :
    totalRows (n+1) = totalRows n+(n+1) := by
  unfold totalRows
  rw [Nat.choose_succ_succ']
  simp [Nat.add_comm]

private theorem sum_sub_eq_totalRows (n a : ℕ) :
    (∑ i ∈ Finset.range a, (n-i)) = totalRows n-totalRows (n-a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases ha : a < n
    · have he : n-a = (n-(a+1))+1 := by omega
      have hmono := Nat.choose_mono 2 (show n-(a+1)+1 ≤ n+1 by omega)
      change totalRows (n-(a+1)) ≤ totalRows n at hmono
      have hm := Nat.choose_mono 2 (show n-a+1 ≤ n+1 by omega)
      change totalRows (n-a) ≤ totalRows n at hm
      have hh : totalRows (n-a) = totalRows (n-(a+1))+(n-a) := by
        rw [he, totalRows_succ]
      omega
    · have h0 : n-a = 0 := by omega
      have h1 : n-(a+1) = 0 := by omega
      simp [h0,h1]

private theorem shiftedTriangle_eq_totalRows (h a : ℕ) :
    Koala6844Receipts.shiftedTriangle h a = totalRows (h+1-a) := by
  unfold Koala6844Receipts.shiftedTriangle totalRows
  by_cases hh : a ≤ h
  · rw [ite_eq_left hh, Nat.choose_two_right]
    unfold Koala6844Receipts.triangle
    rw [show h+1-a+1 = h-a+2 by omega, show h-a+2-1=h-a+1 by omega, Nat.mul_comm]
  · rw [ite_eq_right hh, show h+1-a = 0 by omega]
    decide

theorem card_seedlessRectangle (a b h : ℕ) :
    Fintype.card (SeedlessRectangle a b h) = Koala6844Receipts.seedlessRectangle a b h := by
  rw [Fintype.card_congr (rectangleRows a b h)]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => min b (h+1-i))]
  have hs :
      (∑ i ∈ Finset.range a, min b (h+1-i)) =
        (∑ i ∈ Finset.range a, (h+1-i)) - ∑ i ∈ Finset.range a, (h+1-b-i) := by
    rw [← Finset.sum_tsub_distrib]
    · apply Finset.sum_congr rfl
      intro i _
      omega
    · intro i _
      omega
  rw [hs, sum_sub_eq_totalRows, sum_sub_eq_totalRows]
  have hc : totalRows (h+1) = Koala6844Receipts.triangle h := by
    simp [totalRows, Koala6844Receipts.triangle, Nat.choose_two_right, Nat.mul_comm]
  have he : h+1-b-a = h+1-(a+b) := by omega
  rw [he]
  have hg : totalRows (h+1-(a+b)) ≤ totalRows (h+1-b) :=
    Nat.choose_mono 2 (by omega)
  have hle : (∑ i ∈ Finset.range a, (h+1-b-i)) ≤ ∑ i ∈ Finset.range a, (h+1-i) :=
    Finset.sum_le_sum (fun i _ => by omega)
  rw [sum_sub_eq_totalRows, sum_sub_eq_totalRows, he] at hle
  unfold Koala6844Receipts.seedlessRectangle
  simp_rw [shiftedTriangle_eq_totalRows, ← hc]
  omega

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
