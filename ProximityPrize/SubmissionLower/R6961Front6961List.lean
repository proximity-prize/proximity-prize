import ProximityPrize.SubmissionLower.Front6963List

set_option Elab.async false

namespace Front6961ListBank
noncomputable section

/-- Monotonicity lift from the verified 179,798 scalar list bound (Front6963List)
to agreement 179,818 for 69.61. -/
theorem scalar_list : CJ0.ScalarList 179818 8877686491848982 := by
  intro w
  have h := Front6963ListBank.scalar_list w
  have hsub : CJ0.close 179818 w ⊆ CJ0.close 179798 w := by
    intro f hf
    refine ⟨hf.1, ?_⟩
    exact (show 179798 ≤ 179818 by decide).trans hf.2
  exact ⟨h.1.subset hsub, (Set.ncard_le_ncard hsub h.1).trans h.2⟩

#print axioms scalar_list
end
end Front6961ListBank
