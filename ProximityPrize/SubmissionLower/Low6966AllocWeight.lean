import ProximityPrize.SubmissionLower.Low6966Inventory

set_option Elab.async false

/-! Low-side copy of `KoalaAllocationWeight` for the 69.61 box (142, 58, 15): full charge from index 56, denominator 374. -/
namespace Low6966AllocWeight
open K1_13 (Shape)
open scoped BigOperators

def fullCharge (j t : ℕ) : Prop := 56 ≤ j ∨ 15 ≤ t

instance (j t : ℕ) : Decidable (fullCharge j t) := by unfold fullCharge; infer_instance

def weight (b j t : ℕ) : ℕ := if fullCharge j t then 374 else min (b+4*j) 374

theorem mono {b j t B J T : ℕ} (hb : b ≤ B) (hj : j ≤ J) (ht : t ≤ T) :
    weight b j t ≤ weight B J T := by
  by_cases h : fullCharge j t
  · have h' : fullCharge J T := h.imp (fun k => k.trans hj) (fun k => k.trans ht)
    simp [weight, h, h']
  · by_cases h' : fullCharge J T
    · simpa [weight, h, h'] using (min_le_right (b+4*j) 374)
    · simpa [weight, h, h'] using
        (min_le_min (Nat.add_le_add hb (Nat.mul_le_mul_left 4 hj)) (le_refl 374))

theorem sum_le {top n : ℕ} (htop : top ≤ 15) (a : Fin n → Shape) (hfits : LowProfile6966.Fits top a)
    (s : Finset (Fin n)) : (∑ i ∈ s, weight (a i).b (a i).j (a i).t) ≤ 374 := by
  classical
  have part (f : Fin n → ℕ) : ∑ i ∈ s, f i ≤ ∑ i, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  by_cases hall : ∃ i ∈ s, fullCharge (a i).j (a i).t
  · obtain ⟨i, hi, hc⟩ := hall
    have only (j : Fin n) (hji : j ≠ i) : False := by
      have pair (f : Fin n → ℕ) : f i+f j ≤ ∑ k, f k := by
        rw [← Finset.sum_pair (Ne.symm hji)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      obtain ⟨ht,hj,_⟩ := hfits.1 j
      have hJ := (pair fun k => (a k).j).trans hfits.2.2.1
      have hT := (pair fun k => (a k).t).trans hfits.2.2.2
      rcases hc with h | h <;> omega
    have he : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => by
      by_contra hne
      exact only j hne⟩
    rw [he, Finset.sum_singleton]
    simp [weight, hc]
  · have hw : ∀ i ∈ s, weight (a i).b (a i).j (a i).t ≤ (a i).b+4*(a i).j := by
      intro i hi
      simp [weight, show ¬ fullCharge (a i).j (a i).t from fun h => hall ⟨i,hi,h⟩]
    refine (Finset.sum_le_sum hw).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add ((part _).trans hfits.2.1)
      (Nat.mul_le_mul_left 4 ((part _).trans hfits.2.2.1))

end Low6966AllocWeight
