import ProximityPrize.SubmissionLower.Part.G073


section Compact_SecondJetRelaxedKernelCounts
/-! Closed kernel counts for the independent weighted second-jet family. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts
open scoped BigOperators
open SecondJetRelaxedRank SecondJetClippedRectangle
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev BlockSumIndex (m L B s U r h : ℕ) :=
  Σ i : Fin (r-q m s r h+1), Σ j : Fin (B-2*h-q m s r h+1),
    Fin (if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0)

def blockEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Block m L B s U caps r h ≃ BlockSumIndex m L B s U r h where
  toFun d := by
    have hd := d.property
    refine ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,?_⟩⟩
    change (d.val 2).val < if h+q m s r h+(d.val 0).val+(d.val 1).val ≤ U then
      L+1-h-q m s r h-(d.val 0).val-(d.val 1).val else 0
    rw [if_pos (by omega)]
    omega
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h+q m s r h+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    have hb := budgets m s r h hrm hhs
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_,?_,?_,?_⟩
    · change i.val+q m s r h ≤ r
      omega
    · change j.val+q m s r h+2*h ≤ B
      omega
    · exact hB
    · change i.val+j.val+h+q m s r h ≤ U
      omega
    · change i.val+j.val+h+q m s r h+z.val ≤ L
      omega
    · intro t
      change i.val+j.val+h+q m s r h ≤ caps (h+t.val)
      have ht := t.isLt
      have hc := hcaps (h+t.val) (by omega)
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Block m L B s U caps r h) =
      ∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
        if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0 := by
  rw [Fintype.card_congr (blockEquiv m L B s U caps r h hrm hhs hr hB hcaps)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hq : ¬ (q m s r h ≤ r ∧ m-r+2*h ≤ B)) :
    Fintype.card (Block m L B s U caps r h) = 0 := by
  letI : IsEmpty (Block m L B s U caps r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp

def kernelCell (m L B s U r h : ℕ) : ℕ :=
  if q m s r h ≤ r ∧ m-r+2*h ≤ B then
    clippedRectangle (r-q m s r h+1) (B-2*h-q m s r h+1)
      (L+1-h-q m s r h) (U-h-q m s r h)
  else 0

theorem card_block_closed (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hrm : r < m) (hhs : h ≤ s)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Block m L B s U caps r h) = kernelCell m L B s U r h := by
  unfold kernelCell
  split_ifs with hq
  · rw [card_block_of_le m L B s U caps r h (by omega) hhs hq.1 hq.2 hcaps]
    have hb := budgets m s r h (by omega) hhs
    have heq :
        (∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
          if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0) =
        ∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
          if i.val+j.val ≤ U-h-q m s r h then (L+1-h-q m s r h)-i.val-j.val else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hc : (h+q m s r h+i.val+j.val ≤ U) ↔
          (i.val+j.val ≤ U-h-q m s r h) := by omega
      simp only [hc]
    rw [heq]
    apply sum_clipped_rectangle
    · omega
    · omega
    · dsimp [corner]
      omega
    · dsimp [corner]
      omega
    · intro i j
      have hi := i.isLt
      have hj := j.isLt
      omega
  · exact card_block_of_not_le m L B s U caps r h hq

def kernelCount (m L B s U : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1), kernelCell m L B s U r.val h.val

theorem card_kernel_sum (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L B s U caps r.val h.val)) =
      kernelCount m L B s U := by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact card_block_closed m L B s U caps r.val h.val hBm hU hL r.isLt
    (Nat.le_of_lt_succ h.isLt) hcaps

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts

end Compact_SecondJetRelaxedKernelCounts
