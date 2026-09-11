import ProximityPrize.SubmissionLower.PartG071


section Compact_SecondJetRelaxedSourceCounts
/-! Closed source counts when the varying middle caps contain the uniform cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts
open scoped BigOperators
open SecondJetRelaxedSpace SecondJetClippedRectangle
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev SourceSumIndex (m L B s U : ℕ) :=
  Σ r : Fin m, Σ h : Fin (s+1), Σ i : Fin (r.val+1), Σ j : Fin (B-2*h.val+1),
    Fin (if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0)

def sourceEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Index m L B s U caps ≃ SourceSumIndex m L B s U where
  toFun d := by
    have hi := d.val.property.1
    have ht := d.val.property.2
    have hd := d.property
    refine ⟨d.val.val 0,d.val.val 1,⟨(d.val.val 2).val,by omega⟩,
      ⟨(d.val.val 3).val,by change (d.val.val 3).val < B-2*(d.val.val 1).val+1; omega⟩,
      ⟨(d.val.val 4).val,?_⟩⟩
    change (d.val.val 4).val <
      if (d.val.val 1).val+(d.val.val 2).val+(d.val.val 3).val ≤ U then
        L+1-(d.val.val 1).val-(d.val.val 2).val-(d.val.val 3).val else 0
    rw [if_pos hd.2.1]
    omega
  invFun u := by
    rcases u with ⟨r,h,i,j,z⟩
    have hh := h.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h.val+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    let iv : Fin m := ⟨i.val,by have hr := r.isLt; omega⟩
    let jv : Fin (B+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    let d : ∀ k, Fin (SecondJetSpace.bound m L B s k) :=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases jv (Fin.cases zv (fun i => Fin.elim0 i)))))
    refine ⟨⟨d,?_,?_⟩,?_,?_,?_⟩
    · change i.val ≤ r.val
      omega
    · change h.val+i.val+j.val+z.val ≤ L
      omega
    · change 2*h.val+j.val ≤ B
      omega
    · exact hU
    · exact hU.trans (hcaps h.val (by omega))
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Index m L B s U caps) =
      ∑ r : Fin m, ∑ h : Fin (s+1), ∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0 := by
  rw [Fintype.card_congr (sourceEquiv m L B s U caps hsB hcaps)]
  simp [SourceSumIndex]

def sourceCount (m L B s U : ℕ) : ℕ :=
  ∑ r : Fin m, ∑ h : Fin (s+1),
    clippedRectangle (r.val+1) (B-2*h.val+1) (L+1-h.val) (U-h.val)

theorem card_source_closed (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hsB : 2*s ≤ B) (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Index m L B s U caps) = sourceCount m L B s U := by
  rw [card_source m L B s U caps hsB hcaps]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  have hr := r.isLt
  have hh := h.isLt
  have heq :
      (∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0) =
      ∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if i.val+j.val ≤ U-h.val then (L+1-h.val)-i.val-j.val else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : (h.val+i.val+j.val ≤ U) ↔ (i.val+j.val ≤ U-h.val) := by omega
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

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts

end Compact_SecondJetRelaxedSourceCounts
