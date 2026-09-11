import ProximityPrize.SubmissionLower.Part.G070


section Compact_SecondJetClippedRectangle
/-! A clipped rectangle is an ordinary rectangle minus its small reflected
corner. The closed expression only sums over the removed corner. -/
namespace ProximityPrize.SubmissionLower.SecondJetClippedRectangle
open scoped BigOperators
open SecondJetCounts
set_option autoImplicit false
set_option maxHeartbeats 4000000

def corner (A B H : ℕ) : ℕ := A+B-2-H

def clippedRectangle (A B C H : ℕ) : ℕ :=
  rectangle A B C - ∑ i ∈ Finset.range (corner A B H),
    ∑ j ∈ Finset.range (corner A B H),
      if i+j < corner A B H then C-(A-1-i)-(B-1-j) else 0

theorem outside_sum (A B C H : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hkA : corner A B H ≤ A) (hkB : corner A B H ≤ B) :
    (∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, if H < i+j then C-i-j else 0) =
      ∑ i ∈ Finset.range (corner A B H), ∑ j ∈ Finset.range (corner A B H),
        if i+j < corner A B H then C-(A-1-i)-(B-1-j) else 0 := by
  classical
  let s := ((Finset.range A) ×ˢ (Finset.range B)).filter (fun p => H < p.1+p.2)
  let t := ((Finset.range (corner A B H)) ×ˢ (Finset.range (corner A B H))).filter
    (fun p => p.1+p.2 < corner A B H)
  have heq : (∑ p ∈ s, (C-p.1-p.2)) =
      ∑ p ∈ t, (C-(A-1-p.1)-(B-1-p.2)) := by
    apply Finset.sum_bij (fun p _ => (A-1-p.1,B-1-p.2))
    · intro p hp
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range, corner,
        Prod.fst, Prod.snd]
      dsimp [corner] at hkA hkB
      omega
    · intro p hp q hq hpq
      simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hq
      have h1 := congrArg Prod.fst hpq
      have h2 := congrArg Prod.snd hpq
      apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
    · intro p hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      refine ⟨(A-1-p.1,B-1-p.2),?_,?_⟩
      · simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.fst, Prod.snd]
        dsimp [corner] at hp hkA hkB
        omega
      · apply Prod.ext <;> dsimp <;> omega
    · intro p hp
      have hpmem : (p.1 < A ∧ p.2 < B) ∧ H < p.1+p.2 := by
        simpa only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range] using hp
      change C-p.1-p.2 = C-(A-1-(A-1-p.1))-(B-1-(B-1-p.2))
      omega
  simpa only [s,t,Finset.sum_filter,Finset.sum_product] using heq

theorem sum_clipped_rectangle (A B C H : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hkA : corner A B H ≤ A) (hkB : corner A B H ≤ B)
    (hC : ∀ i : Fin A, ∀ j : Fin B, i.val+j.val ≤ C) :
    (∑ i : Fin A, ∑ j : Fin B, if i.val+j.val ≤ H then C-i.val-j.val else 0) =
      clippedRectangle A B C H := by
  have hsum :
      (∑ i : Fin A, ∑ j : Fin B, if i.val+j.val ≤ H then C-i.val-j.val else 0) +
      (∑ i : Fin A, ∑ j : Fin B, if H < i.val+j.val then C-i.val-j.val else 0) =
        rectangle A B C := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i.val+j.val ≤ H <;> simp [h, Nat.not_lt_of_ge, Nat.lt_of_not_ge]
      _ = _ := sum_rectangle A B C hC
  have hout := outside_sum A B C H hA hB hkA hkB
  have houtside :
      (∑ i : Fin A, ∑ j : Fin B, if H < i.val+j.val then C-i.val-j.val else 0) =
      ∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, if H < i+j then C-i-j else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j : Fin B, if H < i+j.val then C-i-j.val else 0)]
    apply Finset.sum_congr rfl
    intro i _
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => if H < i+j then C-i-j else 0) B
  rw [houtside, hout] at hsum
  unfold clippedRectangle
  omega

end ProximityPrize.SubmissionLower.SecondJetClippedRectangle

end Compact_SecondJetClippedRectangle
