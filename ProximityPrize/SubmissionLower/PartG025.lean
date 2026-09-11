import ProximityPrize.SubmissionLower.PartG024


section Compact_SecondJetFacetCounts
/-! Closed rank counts for the shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetCounts
open scoped BigOperators
open SecondJetFacetSpace SecondJetFacetRank
open SecondJetRank (Block)
open SecondJetCounts (rectangle sum_rectangle kernelCell card_block_closed)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev SourceSumIndex (m L B s : ℕ) :=
  Σ r : Fin m, Σ h : Fin (s+1), Σ i : Fin (r.val+1), Σ j : Fin (B-h.val+1),
    Fin (L+1-h.val-i.val-j.val)

def sourceEquiv (m L B s : ℕ) (hsB : s ≤ B) : Index m L B s ≃ SourceSumIndex m L B s where
  toFun d := by
    have hi := d.val.property.1
    have ht := d.val.property.2
    have hrs := d.property
    exact ⟨d.val.val 0,d.val.val 1,⟨(d.val.val 2).val,by omega⟩,
      ⟨(d.val.val 3).val,by change (d.val.val 3).val < B-(d.val.val 1).val+1; omega⟩,
      ⟨(d.val.val 4).val,by
        change (d.val.val 4).val < L+1-(d.val.val 1).val-(d.val.val 2).val-(d.val.val 3).val
        omega⟩⟩
  invFun u := by
    rcases u with ⟨r,h,i,j,z⟩
    have hh : h.val ≤ B := (Nat.le_of_lt_succ h.isLt).trans hsB
    let iv : Fin m := ⟨i.val,by have hi := i.isLt; have hr := r.isLt; omega⟩
    let jv : Fin (B+1) := ⟨j.val,by have hj := j.isLt; omega⟩
    let zv : Fin (L+1) := ⟨z.val,by have hz := z.isLt; omega⟩
    let d : ∀ k, Fin (SecondJetSpace.bound m L B s k) :=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases jv (Fin.cases zv (fun i => Fin.elim0 i)))))
    refine ⟨⟨d,?_,?_⟩,?_⟩
    · change i.val ≤ r.val
      omega
    · change h.val+i.val+j.val+z.val ≤ L
      have hz := z.isLt
      omega
    · change h.val+j.val ≤ B
      have hj := j.isLt
      omega
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L B s : ℕ) (hsB : s ≤ B) :
    Fintype.card (Index m L B s) =
      ∑ r : Fin m, ∑ h : Fin (s+1), ∑ i : Fin (r.val+1), ∑ j : Fin (B-h.val+1),
        (L+1-h.val-i.val-j.val) := by
  rw [Fintype.card_congr (sourceEquiv m L B s hsB)]
  simp [SourceSumIndex]

theorem card_source_closed (m L B s : ℕ) (hsB : s ≤ B) (hL : m+B+s ≤ L) :
    Fintype.card (Index m L B s) =
      ∑ r : Fin m, ∑ h : Fin (s+1), rectangle (r.val+1) (B-h.val+1) (L+1-h.val) := by
  rw [card_source m L B s hsB]
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

def sourceCount (m L B s : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1), rectangle (r.val+1) (B-h.val+1) (L+1-h.val)

def kernelCount (m L B s : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1), kernelCell m L (B-h.val) s r.val h.val

def rankBound (m L B s : ℕ) : ℕ := sourceCount m L B s-kernelCount m L B s

theorem card_kernel_sum (m L B s : ℕ) (hL : m+B+s ≤ L) :
    (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L (B-h.val) s r.val h.val)) =
      kernelCount m L B s := by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact card_block_closed m L (B-h.val) s r.val h.val (by omega)
    r.isLt (Nat.le_of_lt_succ h.isLt)

variable {K : Type*} [Field K]
theorem local_rank_le_count (m L B s : ℕ) (hsB : s ≤ B) (hL : m+B+s ≤ L) :
    Module.finrank K (restrictedMap (K := K) m L B s).range ≤ rankBound m L B s := by
  have h := local_rank_bound (K := K) m L B s hsB
  rw [card_source_closed m L B s hsB hL, card_kernel_sum m L B s hL] at h
  exact Nat.le_sub_of_add_le h

end
end ProximityPrize.SubmissionLower.SecondJetFacetCounts

end Compact_SecondJetFacetCounts
