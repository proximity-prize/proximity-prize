import ProximityPrize.SubmissionLower.LocatorNestedProjection

namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators

theorem channelCount_mono {T T' YS YS' S S' : ℕ}
    (ht : T ≤ T') (hy : YS ≤ YS') (hs : S ≤ S') :
    channelCount T YS S ≤ channelCount T' YS' S' := by
  unfold channelCount
  calc
    _ ≤ ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S' (min (T' - y) (YS' - y)) + 1),
          (T' + 1 - y - r) := by
      apply Finset.sum_le_sum
      intro y _
      have hin : Finset.range (min S (min (T-y) (YS-y)) + 1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y)) + 1) := by
        apply Finset.range_mono
        have h := min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _ => by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => Nat.zero_le _))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _

theorem nestedCoefficientBox_mono
    {K : Type*} [Field K] {D D' w T T' YS YS' S S' : ℕ}
    (hD : D ≤ D') (hT : T ≤ T') (hYS : YS ≤ YS') (hS : S ≤ S')
    {P : MvPolynomial (Fin 4) K}
    (hP : P ∈ nestedCoefficientBox K D w T YS S) :
    P ∈ nestedCoefficientBox K D' w T' YS' S' := by
  intro d hd
  have h := hP hd
  exact ⟨h.1.trans hT, h.2.1.trans hYS, h.2.2.1.trans hS,
    h.2.2.2.trans_le hD⟩

end ProximityPrize.SubmissionLower.LocatorLowQuotient
