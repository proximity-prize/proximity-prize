import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData
namespace ProximityPrize.SubmissionLower.BoundaryTailBaseFastValidated
open BoundaryTailBaseFast
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async true
theorem valid7 : ∀ v ∈ List.range 136, Valid (BoundaryTailBaseFastData.row 7 v) 7 v := by decide +kernel
theorem valid8 : ∀ v ∈ List.range 135, Valid (BoundaryTailBaseFastData.row 8 v) 8 v := by decide +kernel
theorem valid9 : ∀ v ∈ List.range 134, Valid (BoundaryTailBaseFastData.row 9 v) 9 v := by decide +kernel
theorem valid10 : ∀ v ∈ List.range 133, Valid (BoundaryTailBaseFastData.row 10 v) 10 v := by decide +kernel
theorem valid11 : ∀ v ∈ List.range 132, Valid (BoundaryTailBaseFastData.row 11 v) 11 v := by decide +kernel
theorem valid12 : ∀ v ∈ List.range 131, Valid (BoundaryTailBaseFastData.row 12 v) 12 v := by decide +kernel
theorem valid13 : ∀ v ∈ List.range 130, Valid (BoundaryTailBaseFastData.row 13 v) 13 v := by decide +kernel
theorem valid14 : ∀ v ∈ List.range 129, Valid (BoundaryTailBaseFastData.row 14 v) 14 v := by decide +kernel
theorem valid15 : ∀ v ∈ List.range 128, Valid (BoundaryTailBaseFastData.row 15 v) 15 v := by decide +kernel
theorem valid16 : ∀ v ∈ List.range 127, Valid (BoundaryTailBaseFastData.row 16 v) 16 v := by decide +kernel
theorem valid17 : ∀ v ∈ List.range 126, Valid (BoundaryTailBaseFastData.row 17 v) 17 v := by decide +kernel
theorem valid18 : ∀ v ∈ List.range 125, Valid (BoundaryTailBaseFastData.row 18 v) 18 v := by decide +kernel
theorem valid19 : ∀ v ∈ List.range 124, Valid (BoundaryTailBaseFastData.row 19 v) 19 v := by decide +kernel
theorem valid20 : ∀ v ∈ List.range 123, Valid (BoundaryTailBaseFastData.row 20 v) 20 v := by decide +kernel
theorem valid21 : ∀ v ∈ List.range 122, Valid (BoundaryTailBaseFastData.row 21 v) 21 v := by decide +kernel
theorem valid22 : ∀ v ∈ List.range 121, Valid (BoundaryTailBaseFastData.row 22 v) 22 v := by decide +kernel
theorem valid23 : ∀ v ∈ List.range 120, Valid (BoundaryTailBaseFastData.row 23 v) 23 v := by decide +kernel
theorem valid24 : ∀ v ∈ List.range 119, Valid (BoundaryTailBaseFastData.row 24 v) 24 v := by decide +kernel
theorem valid25 : ∀ v ∈ List.range 118, Valid (BoundaryTailBaseFastData.row 25 v) 25 v := by decide +kernel
theorem valid26 : ∀ v ∈ List.range 117, Valid (BoundaryTailBaseFastData.row 26 v) 26 v := by decide +kernel
theorem valid27 : ∀ v ∈ List.range 116, Valid (BoundaryTailBaseFastData.row 27 v) 27 v := by decide +kernel
theorem valid28 : ∀ v ∈ List.range 115, Valid (BoundaryTailBaseFastData.row 28 v) 28 v := by decide +kernel
theorem valid29 : ∀ v ∈ List.range 114, Valid (BoundaryTailBaseFastData.row 29 v) 29 v := by decide +kernel
theorem valid30 : ∀ v ∈ List.range 113, Valid (BoundaryTailBaseFastData.row 30 v) 30 v := by decide +kernel
theorem valid31 : ∀ v ∈ List.range 112, Valid (BoundaryTailBaseFastData.row 31 v) 31 v := by decide +kernel

theorem validAll (R V : ℕ) (hR : 7 ≤ R) (hRmax : R ≤ 31) (hRV : R+V ≤ 142) :
    Valid (BoundaryTailBaseFastData.row R V) R V := by
  have hV : V < 143-R := by omega
  interval_cases R
  · exact valid7 V (List.mem_range.mpr (by omega))
  · exact valid8 V (List.mem_range.mpr (by omega))
  · exact valid9 V (List.mem_range.mpr (by omega))
  · exact valid10 V (List.mem_range.mpr (by omega))
  · exact valid11 V (List.mem_range.mpr (by omega))
  · exact valid12 V (List.mem_range.mpr (by omega))
  · exact valid13 V (List.mem_range.mpr (by omega))
  · exact valid14 V (List.mem_range.mpr (by omega))
  · exact valid15 V (List.mem_range.mpr (by omega))
  · exact valid16 V (List.mem_range.mpr (by omega))
  · exact valid17 V (List.mem_range.mpr (by omega))
  · exact valid18 V (List.mem_range.mpr (by omega))
  · exact valid19 V (List.mem_range.mpr (by omega))
  · exact valid20 V (List.mem_range.mpr (by omega))
  · exact valid21 V (List.mem_range.mpr (by omega))
  · exact valid22 V (List.mem_range.mpr (by omega))
  · exact valid23 V (List.mem_range.mpr (by omega))
  · exact valid24 V (List.mem_range.mpr (by omega))
  · exact valid25 V (List.mem_range.mpr (by omega))
  · exact valid26 V (List.mem_range.mpr (by omega))
  · exact valid27 V (List.mem_range.mpr (by omega))
  · exact valid28 V (List.mem_range.mpr (by omega))
  · exact valid29 V (List.mem_range.mpr (by omega))
  · exact valid30 V (List.mem_range.mpr (by omega))
  · exact valid31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.BoundaryTailBaseFastValidated
