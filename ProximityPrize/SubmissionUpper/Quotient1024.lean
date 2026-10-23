import ProximityPrize.SubmissionUpper.OrbitPencil


namespace ProximityPrize.SubmissionUpper.OrbitPencil

theorem saturated_row_degree : 511 + 255 * 512 = 131071 := by
  norm_num

theorem farness_cut : 512 + 131071 = 131583 := by
  norm_num

theorem block_agreement : 511 + 512 * 272 = 139775 := by
  norm_num

theorem disagreement_split : 262144 - 139775 = 122369 := by
  norm_num

theorem seven_past_budget : 139775 + 7 = 139782 ∧ ¬ 512 ∣ 7 := by
  refine ⟨by norm_num, ?_⟩
  intro h
  have : 512 ≤ 7 := Nat.le_of_dvd (by norm_num) h
  norm_num at this

theorem cpoly_bound_eq_row_budget {U : Finset Small} (hU : U ∈ Sel) :
    (cpoly U).natDegree ≤ 511 + 255 * 512 := by
  rw [saturated_row_degree]
  exact cpoly_natDegree_le hU

end ProximityPrize.SubmissionUpper.OrbitPencil
