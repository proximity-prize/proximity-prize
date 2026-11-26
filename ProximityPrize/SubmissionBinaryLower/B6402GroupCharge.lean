import ProximityPrize.SubmissionBinaryLower.B6402BucketBudget

namespace ProximityPrize.SubmissionBinaryLower.B6402GroupCharge
open B6402BucketBudget
open scoped BigOperators
set_option autoImplicit false

theorem group_sum {K : Type*} (S : Finset K) (slot : K → Fin 5) (q extra : ℕ)
    (one : ∀ z∈S,S.card≤singleBudget q+extra ∨
        (S.filter fun w => slot w=slot z).card≤groupBudget (slot z) q+extra) :
    S.card≤singleBudget q+(∑ r : Fin 5,groupBudget r q)+5*extra := by
  classical
  by_cases single : S.card≤singleBudget q+extra
  · omega
  have each (r : Fin 5) : (S.filter fun w => slot w=r).card≤groupBudget r q+extra := by
    by_cases h : (S.filter fun w => slot w=r).Nonempty
    · obtain ⟨z,hz⟩ := h
      obtain ⟨hs,hslot⟩ := Finset.mem_filter.mp hz
      simpa only [hslot] using (one z hs).resolve_left single
    · rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.card_empty]; omega
  have cover : S ⊆ (Finset.univ.biUnion fun r : Fin 5 => S.filter fun w => slot w=r) := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨slot z,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,rfl⟩⟩
  have h := (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 5))) => each r)))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  omega

#print axioms group_sum
end ProximityPrize.SubmissionBinaryLower.B6402GroupCharge
