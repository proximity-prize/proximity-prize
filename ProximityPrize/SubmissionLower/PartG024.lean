import ProximityPrize.SubmissionLower.PartG023


section Compact_SecondJetCounts
/-! Efficient counting interfaces for the local second-jet source and kernel.
The finite index types used in the rank proof are never evaluated directly. -/
namespace ProximityPrize.SubmissionLower.SecondJetCounts
open scoped BigOperators
open SecondJetSpace SecondJetRank
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev SourceSumIndex (m L s1 s2 : ℕ) :=
  Σ r : Fin m, Σ h : Fin (s2+1), Σ i : Fin (r.val+1), Σ j : Fin (s1+1),
    Fin (L+1-h.val-i.val-j.val)

def sourceEquiv (m L s1 s2 : ℕ) : Index m L s1 s2 ≃ SourceSumIndex m L s1 s2 where
  toFun d := by
    have hi := d.property.1
    have ht := d.property.2
    exact ⟨d.val 0,d.val 1,⟨(d.val 2).val,by omega⟩,d.val 3,⟨(d.val 4).val,by dsimp; omega⟩⟩
  invFun u := by
    rcases u with ⟨r,h,i,j,z⟩
    let iv : Fin m := ⟨i.val,by have hi := i.isLt; have hr := r.isLt; omega⟩
    let zv : Fin (L+1) := ⟨z.val,by have hz := z.isLt; omega⟩
    let d : ∀ k, Fin (bound m L s1 s2 k) :=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases j (Fin.cases zv (fun i => Fin.elim0 i)))))
    refine ⟨d,?_,?_⟩
    · change i.val ≤ r.val
      omega
    · change h.val+i.val+j.val+z.val ≤ L
      have hz := z.isLt
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L s1 s2 : ℕ) :
    Fintype.card (Index m L s1 s2) =
      ∑ r : Fin m, ∑ h : Fin (s2+1), ∑ i : Fin (r.val+1), ∑ j : Fin (s1+1),
        (L+1-h.val-i.val-j.val) := by
  rw [Fintype.card_congr (sourceEquiv m L s1 s2)]
  simp [SourceSumIndex]


abbrev BlockSumIndex (m L s1 s2 r h : ℕ) :=
  Σ i : Fin (r-q m s2 r h+1), Σ j : Fin (s1-q m s2 r h+1),
    Fin (L+1-h-q m s2 r h-i.val-j.val)

def blockEquiv (m L s1 s2 r h : ℕ) (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Block m L s1 s2 r h ≃ BlockSumIndex m L s1 s2 r h where
  toFun d := by
    have hd := d.property
    exact ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,by dsimp; omega⟩⟩
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_⟩
    · change i.val+q m s2 r h ≤ r
      omega
    · change j.val+q m s2 r h ≤ s1
      omega
    · change i.val+j.val+z.val+h+q m s2 r h ≤ L
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L s1 s2 r h : ℕ)
    (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Fintype.card (Block m L s1 s2 r h) =
      ∑ i : Fin (r-q m s2 r h+1), ∑ j : Fin (s1-q m s2 r h+1),
        (L+1-h-q m s2 r h-i.val-j.val) := by
  rw [Fintype.card_congr (blockEquiv m L s1 s2 r h hr hs)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L s1 s2 r h : ℕ)
    (hq : ¬ (q m s2 r h ≤ r ∧ q m s2 r h ≤ s1)) :
    Fintype.card (Block m L s1 s2 r h) = 0 := by
  letI : IsEmpty (Block m L s1 s2 r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp


def rectangle (A B C : ℕ) :=
  A*B*C-B*(A*(A-1)/2)-A*(B*(B-1)/2)

theorem sum_fin_val (n : ℕ) : (∑ i : Fin n, i.val) = n*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem sum_rectangle (A B C : ℕ) (h : ∀ i : Fin A, ∀ j : Fin B, i.val+j.val ≤ C) :
    (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) = rectangle A B C := by
  have hs : (∑ i : Fin A, ∑ j : Fin B, ((C-i.val-j.val)+i.val+j.val)) = A*(B*C) := by
    calc
      _ = ∑ _i : Fin A, ∑ _j : Fin B, C := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hij := h i j
        omega
      _ = _ := by simp
  have hs' : (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) +
      B*(A*(A-1)/2)+A*(B*(B-1)/2) = A*(B*C) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, sum_fin_val] using hs
  unfold rectangle
  rw [mul_assoc]
  omega

theorem card_source_closed (m L s1 s2 : ℕ) (hL : m+s1+s2 ≤ L) :
    Fintype.card (Index m L s1 s2) =
      ∑ r : Fin m, ∑ h : Fin (s2+1), rectangle (r.val+1) (s1+1) (L+1-h.val) := by
  rw [card_source]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  apply sum_rectangle
  intro i j
  have hr := r.isLt
  have hh := h.isLt
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem card_block_closed (m L s1 s2 r h : ℕ) (hL : m+s1+s2 ≤ L)
    (hrm : r < m) (hhs : h ≤ s2) :
    Fintype.card (Block m L s1 s2 r h) =
      if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
        rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
      else 0 := by
  split_ifs with hq
  · rw [card_block_of_le m L s1 s2 r h hq.1 hq.2]
    apply sum_rectangle
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exact card_block_of_not_le m L s1 s2 r h hq


def sourceCount (m L s1 s2 : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s2+1), rectangle (r.val+1) (s1+1) (L+1-h.val)

def kernelCell (m L s1 s2 r h : ℕ) : ℕ :=
  if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
    rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
  else 0

def kernelCount (m L s1 s2 : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s2+1), kernelCell m L s1 s2 r.val h.val

def rankBound (m L s1 s2 : ℕ) : ℕ := sourceCount m L s1 s2-kernelCount m L s1 s2

theorem card_kernel_sum (m L s1 s2 : ℕ) (hL : m+s1+s2 ≤ L) :
    (∑ r : Fin m, ∑ h : Fin (s2+1), Fintype.card (Block m L s1 s2 r.val h.val)) =
      kernelCount m L s1 s2 := by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact card_block_closed m L s1 s2 r.val h.val hL r.isLt (Nat.le_of_lt_succ h.isLt)

variable {K : Type*} [Field K]
theorem local_rank_le_count (m L s1 s2 : ℕ) (hL : m+s1+s2 ≤ L) :
    Module.finrank K (restrictedMap (K := K) m L s1 s2).range ≤ rankBound m L s1 s2 := by
  have h := local_rank_bound (K := K) m L s1 s2
  rw [card_source_closed m L s1 s2 hL, card_kernel_sum m L s1 s2 hL] at h
  exact Nat.le_sub_of_add_le h

end
end ProximityPrize.SubmissionLower.SecondJetCounts

end Compact_SecondJetCounts
