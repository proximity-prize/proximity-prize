import ProximityPrize.SubmissionLower.BoundaryTailBaseBlock03
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r4_part0 : ∀ i ∈ List.range 8, CorrectAt 4 (0+i) := by decide +kernel

theorem correct_r4_part8 : ∀ i ∈ List.range 8, CorrectAt 4 (8+i) := by decide +kernel

theorem correct_r4_part16 : ∀ i ∈ List.range 8, CorrectAt 4 (16+i) := by decide +kernel

theorem correct_r4_part24 : ∀ i ∈ List.range 8, CorrectAt 4 (24+i) := by decide +kernel

theorem correct_r4_part32 : ∀ i ∈ List.range 8, CorrectAt 4 (32+i) := by decide +kernel

theorem correct_r4_part40 : ∀ i ∈ List.range 8, CorrectAt 4 (40+i) := by decide +kernel

theorem correct_r4_part48 : ∀ i ∈ List.range 8, CorrectAt 4 (48+i) := by decide +kernel

theorem correct_r4_part56 : ∀ i ∈ List.range 8, CorrectAt 4 (56+i) := by decide +kernel

theorem correct_r4_part64 : ∀ i ∈ List.range 8, CorrectAt 4 (64+i) := by decide +kernel

theorem correct_r4_part72 : ∀ i ∈ List.range 8, CorrectAt 4 (72+i) := by decide +kernel

theorem correct_r4_part80 : ∀ i ∈ List.range 8, CorrectAt 4 (80+i) := by decide +kernel

theorem correct_r4_part88 : ∀ i ∈ List.range 8, CorrectAt 4 (88+i) := by decide +kernel

theorem correct_r4_part96 : ∀ i ∈ List.range 8, CorrectAt 4 (96+i) := by decide +kernel

theorem correct_r4_part104 : ∀ i ∈ List.range 8, CorrectAt 4 (104+i) := by decide +kernel

theorem correct_r4_part112 : ∀ i ∈ List.range 8, CorrectAt 4 (112+i) := by decide +kernel

theorem correct_r4_part120 : ∀ i ∈ List.range 8, CorrectAt 4 (120+i) := by decide +kernel

theorem correct_r4_part128 : ∀ i ∈ List.range 8, CorrectAt 4 (128+i) := by decide +kernel

theorem correct_r4_part136 : ∀ i ∈ List.range 3, CorrectAt 4 (136+i) := by decide +kernel

theorem correct_r4 (V : ℕ) (hV : V ∈ List.range 139) : CorrectAt 4 V := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := correct_r4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := correct_r4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r4_part0 : ∀ i ∈ List.range 8, BaseCheckAt 4 (0+i) := by decide +kernel

theorem base_r4_part8 : ∀ i ∈ List.range 8, BaseCheckAt 4 (8+i) := by decide +kernel

theorem base_r4_part16 : ∀ i ∈ List.range 8, BaseCheckAt 4 (16+i) := by decide +kernel

theorem base_r4_part24 : ∀ i ∈ List.range 8, BaseCheckAt 4 (24+i) := by decide +kernel

theorem base_r4_part32 : ∀ i ∈ List.range 8, BaseCheckAt 4 (32+i) := by decide +kernel

theorem base_r4_part40 : ∀ i ∈ List.range 8, BaseCheckAt 4 (40+i) := by decide +kernel

theorem base_r4_part48 : ∀ i ∈ List.range 8, BaseCheckAt 4 (48+i) := by decide +kernel

theorem base_r4_part56 : ∀ i ∈ List.range 8, BaseCheckAt 4 (56+i) := by decide +kernel

theorem base_r4_part64 : ∀ i ∈ List.range 8, BaseCheckAt 4 (64+i) := by decide +kernel

theorem base_r4_part72 : ∀ i ∈ List.range 8, BaseCheckAt 4 (72+i) := by decide +kernel

theorem base_r4_part80 : ∀ i ∈ List.range 8, BaseCheckAt 4 (80+i) := by decide +kernel

theorem base_r4_part88 : ∀ i ∈ List.range 8, BaseCheckAt 4 (88+i) := by decide +kernel

theorem base_r4_part96 : ∀ i ∈ List.range 8, BaseCheckAt 4 (96+i) := by decide +kernel

theorem base_r4_part104 : ∀ i ∈ List.range 8, BaseCheckAt 4 (104+i) := by decide +kernel

theorem base_r4_part112 : ∀ i ∈ List.range 8, BaseCheckAt 4 (112+i) := by decide +kernel

theorem base_r4_part120 : ∀ i ∈ List.range 8, BaseCheckAt 4 (120+i) := by decide +kernel

theorem base_r4_part128 : ∀ i ∈ List.range 8, BaseCheckAt 4 (128+i) := by decide +kernel

theorem base_r4_part136 : ∀ i ∈ List.range 3, BaseCheckAt 4 (136+i) := by decide +kernel

theorem base_r4 (V : ℕ) (hV : V ∈ List.range 139) : BaseCheckAt 4 V := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := base_r4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := base_r4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r4_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (0+i)) 4 (0+i) := by decide +kernel

theorem valid_r4_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (8+i)) 4 (8+i) := by decide +kernel

theorem valid_r4_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (16+i)) 4 (16+i) := by decide +kernel

theorem valid_r4_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (24+i)) 4 (24+i) := by decide +kernel

theorem valid_r4_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (32+i)) 4 (32+i) := by decide +kernel

theorem valid_r4_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (40+i)) 4 (40+i) := by decide +kernel

theorem valid_r4_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (48+i)) 4 (48+i) := by decide +kernel

theorem valid_r4_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (56+i)) 4 (56+i) := by decide +kernel

theorem valid_r4_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (64+i)) 4 (64+i) := by decide +kernel

theorem valid_r4_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (72+i)) 4 (72+i) := by decide +kernel

theorem valid_r4_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (80+i)) 4 (80+i) := by decide +kernel

theorem valid_r4_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (88+i)) 4 (88+i) := by decide +kernel

theorem valid_r4_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (96+i)) 4 (96+i) := by decide +kernel

theorem valid_r4_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (104+i)) 4 (104+i) := by decide +kernel

theorem valid_r4_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (112+i)) 4 (112+i) := by decide +kernel

theorem valid_r4_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (120+i)) 4 (120+i) := by decide +kernel

theorem valid_r4_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 4 (128+i)) 4 (128+i) := by decide +kernel

theorem valid_r4_part136 : ∀ i ∈ List.range 3, Valid (BoundaryTailBaseFastData.row 4 (136+i)) 4 (136+i) := by decide +kernel

theorem valid_r4 (V : ℕ) (hV : V ∈ List.range 139) : Valid (BoundaryTailBaseFastData.row 4 V) 4 V := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := valid_r4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := valid_r4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r4_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (0+i)) 4 (0+i) = true := by decide +kernel

theorem strictBool_r4_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (1+i)) 4 (1+i) = true := by decide +kernel

theorem strictBool_r4_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (2+i)) 4 (2+i) = true := by decide +kernel

theorem strictBool_r4_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (3+i)) 4 (3+i) = true := by decide +kernel

theorem strictBool_r4_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (4+i)) 4 (4+i) = true := by decide +kernel

theorem strictBool_r4_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (5+i)) 4 (5+i) = true := by decide +kernel

theorem strictBool_r4_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (6+i)) 4 (6+i) = true := by decide +kernel

theorem strictBool_r4_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (7+i)) 4 (7+i) = true := by decide +kernel

theorem strictBool_r4_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (8+i)) 4 (8+i) = true := by decide +kernel

theorem strictBool_r4_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (9+i)) 4 (9+i) = true := by decide +kernel

theorem strictBool_r4_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (10+i)) 4 (10+i) = true := by decide +kernel

theorem strictBool_r4_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (11+i)) 4 (11+i) = true := by decide +kernel

theorem strictBool_r4_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (12+i)) 4 (12+i) = true := by decide +kernel

theorem strictBool_r4_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (13+i)) 4 (13+i) = true := by decide +kernel

theorem strictBool_r4_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (14+i)) 4 (14+i) = true := by decide +kernel

theorem strictBool_r4_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (15+i)) 4 (15+i) = true := by decide +kernel

theorem strictBool_r4_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (16+i)) 4 (16+i) = true := by decide +kernel

theorem strictBool_r4_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (17+i)) 4 (17+i) = true := by decide +kernel

theorem strictBool_r4_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (18+i)) 4 (18+i) = true := by decide +kernel

theorem strictBool_r4_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (19+i)) 4 (19+i) = true := by decide +kernel

theorem strictBool_r4_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (20+i)) 4 (20+i) = true := by decide +kernel

theorem strictBool_r4_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (21+i)) 4 (21+i) = true := by decide +kernel

theorem strictBool_r4_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (22+i)) 4 (22+i) = true := by decide +kernel

theorem strictBool_r4_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (23+i)) 4 (23+i) = true := by decide +kernel

theorem strictBool_r4_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (24+i)) 4 (24+i) = true := by decide +kernel

theorem strictBool_r4_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (25+i)) 4 (25+i) = true := by decide +kernel

theorem strictBool_r4_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (26+i)) 4 (26+i) = true := by decide +kernel

theorem strictBool_r4_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (27+i)) 4 (27+i) = true := by decide +kernel

theorem strictBool_r4_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (28+i)) 4 (28+i) = true := by decide +kernel

theorem strictBool_r4_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (29+i)) 4 (29+i) = true := by decide +kernel

theorem strictBool_r4_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (30+i)) 4 (30+i) = true := by decide +kernel

theorem strictBool_r4_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (31+i)) 4 (31+i) = true := by decide +kernel

theorem strictBool_r4_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (32+i)) 4 (32+i) = true := by decide +kernel

theorem strictBool_r4_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (33+i)) 4 (33+i) = true := by decide +kernel

theorem strictBool_r4_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (34+i)) 4 (34+i) = true := by decide +kernel

theorem strictBool_r4_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (35+i)) 4 (35+i) = true := by decide +kernel

theorem strictBool_r4_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (36+i)) 4 (36+i) = true := by decide +kernel

theorem strictBool_r4_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (37+i)) 4 (37+i) = true := by decide +kernel

theorem strictBool_r4_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (38+i)) 4 (38+i) = true := by decide +kernel

theorem strictBool_r4_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (39+i)) 4 (39+i) = true := by decide +kernel

theorem strictBool_r4_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (40+i)) 4 (40+i) = true := by decide +kernel

theorem strictBool_r4_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (41+i)) 4 (41+i) = true := by decide +kernel

theorem strictBool_r4_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (42+i)) 4 (42+i) = true := by decide +kernel

theorem strictBool_r4_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (43+i)) 4 (43+i) = true := by decide +kernel

theorem strictBool_r4_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (44+i)) 4 (44+i) = true := by decide +kernel

theorem strictBool_r4_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (45+i)) 4 (45+i) = true := by decide +kernel

theorem strictBool_r4_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (46+i)) 4 (46+i) = true := by decide +kernel

theorem strictBool_r4_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (47+i)) 4 (47+i) = true := by decide +kernel

theorem strictBool_r4_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (48+i)) 4 (48+i) = true := by decide +kernel

theorem strictBool_r4_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (49+i)) 4 (49+i) = true := by decide +kernel

theorem strictBool_r4_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (50+i)) 4 (50+i) = true := by decide +kernel

theorem strictBool_r4_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (51+i)) 4 (51+i) = true := by decide +kernel

theorem strictBool_r4_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (52+i)) 4 (52+i) = true := by decide +kernel

theorem strictBool_r4_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (53+i)) 4 (53+i) = true := by decide +kernel

theorem strictBool_r4_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (54+i)) 4 (54+i) = true := by decide +kernel

theorem strictBool_r4_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (55+i)) 4 (55+i) = true := by decide +kernel

theorem strictBool_r4_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (56+i)) 4 (56+i) = true := by decide +kernel

theorem strictBool_r4_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (57+i)) 4 (57+i) = true := by decide +kernel

theorem strictBool_r4_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (58+i)) 4 (58+i) = true := by decide +kernel

theorem strictBool_r4_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (59+i)) 4 (59+i) = true := by decide +kernel

theorem strictBool_r4_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (60+i)) 4 (60+i) = true := by decide +kernel

theorem strictBool_r4_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (61+i)) 4 (61+i) = true := by decide +kernel

theorem strictBool_r4_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (62+i)) 4 (62+i) = true := by decide +kernel

theorem strictBool_r4_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (63+i)) 4 (63+i) = true := by decide +kernel

theorem strictBool_r4_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (64+i)) 4 (64+i) = true := by decide +kernel

theorem strictBool_r4_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (65+i)) 4 (65+i) = true := by decide +kernel

theorem strictBool_r4_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (66+i)) 4 (66+i) = true := by decide +kernel

theorem strictBool_r4_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (67+i)) 4 (67+i) = true := by decide +kernel

theorem strictBool_r4_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (68+i)) 4 (68+i) = true := by decide +kernel

theorem strictBool_r4_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (69+i)) 4 (69+i) = true := by decide +kernel

theorem strictBool_r4_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (70+i)) 4 (70+i) = true := by decide +kernel

theorem strictBool_r4_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (71+i)) 4 (71+i) = true := by decide +kernel

theorem strictBool_r4_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (72+i)) 4 (72+i) = true := by decide +kernel

theorem strictBool_r4_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (73+i)) 4 (73+i) = true := by decide +kernel

theorem strictBool_r4_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (74+i)) 4 (74+i) = true := by decide +kernel

theorem strictBool_r4_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (75+i)) 4 (75+i) = true := by decide +kernel

theorem strictBool_r4_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (76+i)) 4 (76+i) = true := by decide +kernel

theorem strictBool_r4_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (77+i)) 4 (77+i) = true := by decide +kernel

theorem strictBool_r4_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (78+i)) 4 (78+i) = true := by decide +kernel

theorem strictBool_r4_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (79+i)) 4 (79+i) = true := by decide +kernel

theorem strictBool_r4_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (80+i)) 4 (80+i) = true := by decide +kernel

theorem strictBool_r4_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (81+i)) 4 (81+i) = true := by decide +kernel

theorem strictBool_r4_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (82+i)) 4 (82+i) = true := by decide +kernel

theorem strictBool_r4_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (83+i)) 4 (83+i) = true := by decide +kernel

theorem strictBool_r4_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (84+i)) 4 (84+i) = true := by decide +kernel

theorem strictBool_r4_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (85+i)) 4 (85+i) = true := by decide +kernel

theorem strictBool_r4_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (86+i)) 4 (86+i) = true := by decide +kernel

theorem strictBool_r4_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (87+i)) 4 (87+i) = true := by decide +kernel

theorem strictBool_r4_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (88+i)) 4 (88+i) = true := by decide +kernel

theorem strictBool_r4_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (89+i)) 4 (89+i) = true := by decide +kernel

theorem strictBool_r4_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (90+i)) 4 (90+i) = true := by decide +kernel

theorem strictBool_r4_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (91+i)) 4 (91+i) = true := by decide +kernel

theorem strictBool_r4_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (92+i)) 4 (92+i) = true := by decide +kernel

theorem strictBool_r4_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (93+i)) 4 (93+i) = true := by decide +kernel

theorem strictBool_r4_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (94+i)) 4 (94+i) = true := by decide +kernel

theorem strictBool_r4_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (95+i)) 4 (95+i) = true := by decide +kernel

theorem strictBool_r4_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (96+i)) 4 (96+i) = true := by decide +kernel

theorem strictBool_r4_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (97+i)) 4 (97+i) = true := by decide +kernel

theorem strictBool_r4_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (98+i)) 4 (98+i) = true := by decide +kernel

theorem strictBool_r4_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (99+i)) 4 (99+i) = true := by decide +kernel

theorem strictBool_r4_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (100+i)) 4 (100+i) = true := by decide +kernel

theorem strictBool_r4_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (101+i)) 4 (101+i) = true := by decide +kernel

theorem strictBool_r4_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (102+i)) 4 (102+i) = true := by decide +kernel

theorem strictBool_r4_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (103+i)) 4 (103+i) = true := by decide +kernel

theorem strictBool_r4_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (104+i)) 4 (104+i) = true := by decide +kernel

theorem strictBool_r4_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (105+i)) 4 (105+i) = true := by decide +kernel

theorem strictBool_r4_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (106+i)) 4 (106+i) = true := by decide +kernel

theorem strictBool_r4_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (107+i)) 4 (107+i) = true := by decide +kernel

theorem strictBool_r4_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (108+i)) 4 (108+i) = true := by decide +kernel

theorem strictBool_r4_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (109+i)) 4 (109+i) = true := by decide +kernel

theorem strictBool_r4_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (110+i)) 4 (110+i) = true := by decide +kernel

theorem strictBool_r4_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (111+i)) 4 (111+i) = true := by decide +kernel

theorem strictBool_r4_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (112+i)) 4 (112+i) = true := by decide +kernel

theorem strictBool_r4_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (113+i)) 4 (113+i) = true := by decide +kernel

theorem strictBool_r4_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (114+i)) 4 (114+i) = true := by decide +kernel

theorem strictBool_r4_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (115+i)) 4 (115+i) = true := by decide +kernel

theorem strictBool_r4_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (116+i)) 4 (116+i) = true := by decide +kernel

theorem strictBool_r4_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (117+i)) 4 (117+i) = true := by decide +kernel

theorem strictBool_r4_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (118+i)) 4 (118+i) = true := by decide +kernel

theorem strictBool_r4_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (119+i)) 4 (119+i) = true := by decide +kernel

theorem strictBool_r4_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (120+i)) 4 (120+i) = true := by decide +kernel

theorem strictBool_r4_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (121+i)) 4 (121+i) = true := by decide +kernel

theorem strictBool_r4_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (122+i)) 4 (122+i) = true := by decide +kernel

theorem strictBool_r4_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (123+i)) 4 (123+i) = true := by decide +kernel

theorem strictBool_r4_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (124+i)) 4 (124+i) = true := by decide +kernel

theorem strictBool_r4_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (125+i)) 4 (125+i) = true := by decide +kernel

theorem strictBool_r4_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (126+i)) 4 (126+i) = true := by decide +kernel

theorem strictBool_r4_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (127+i)) 4 (127+i) = true := by decide +kernel

theorem strictBool_r4_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (128+i)) 4 (128+i) = true := by decide +kernel

theorem strictBool_r4_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (129+i)) 4 (129+i) = true := by decide +kernel

theorem strictBool_r4_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (130+i)) 4 (130+i) = true := by decide +kernel

theorem strictBool_r4_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (131+i)) 4 (131+i) = true := by decide +kernel

theorem strictBool_r4_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (132+i)) 4 (132+i) = true := by decide +kernel

theorem strictBool_r4_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (133+i)) 4 (133+i) = true := by decide +kernel

theorem strictBool_r4_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (134+i)) 4 (134+i) = true := by decide +kernel

theorem strictBool_r4_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (135+i)) 4 (135+i) = true := by decide +kernel

theorem strictBool_r4_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (136+i)) 4 (136+i) = true := by decide +kernel

theorem strictBool_r4_part137 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (137+i)) 4 (137+i) = true := by decide +kernel

theorem strictBool_r4_part138 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 4 (138+i)) 4 (138+i) = true := by decide +kernel

theorem strictBool_r4 (V : ℕ) (hV : V ∈ List.range 139) : strictBool (BoundaryTailBaseFastData.row 4 V) 4 V = true := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r4_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r4_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r4_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r4_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r4_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r4_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r4_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r4_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r4_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r4_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r4_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r4_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r4_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r4_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r4_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r4_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strictBool_r4_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strictBool_r4_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r4_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r4_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r4_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r4_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r4_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r4_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r4_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strictBool_r4_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strictBool_r4_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r4_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r4_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r4_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_60 : V < 58
              · have hi := strictBool_r4_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · by_cases h58_60 : V < 59
                · have hi := strictBool_r4_part58 (V-58) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r4_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r4_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r4_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_69 : V < 67
              · have hi := strictBool_r4_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · by_cases h67_69 : V < 68
                · have hi := strictBool_r4_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h69_139 : V < 104
    · by_cases h69_104 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r4_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r4_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r4_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r4_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r4_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r4_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r4_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_86 : V < 84
              · have hi := strictBool_r4_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · by_cases h84_86 : V < 85
                · have hi := strictBool_r4_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
      · by_cases h86_104 : V < 95
        · by_cases h86_95 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r4_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r4_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_95 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r4_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_95 : V < 93
              · have hi := strictBool_r4_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · by_cases h93_95 : V < 94
                · have hi := strictBool_r4_part93 (V-93) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
        · by_cases h95_104 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r4_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r4_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
          · by_cases h99_104 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r4_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_104 : V < 102
              · have hi := strictBool_r4_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · by_cases h102_104 : V < 103
                · have hi := strictBool_r4_part102 (V-102) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 121
      · by_cases h104_121 : V < 112
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r4_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r4_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r4_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r4_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
        · by_cases h112_121 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r4_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r4_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_121 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r4_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_121 : V < 119
              · have hi := strictBool_r4_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · by_cases h119_121 : V < 120
                · have hi := strictBool_r4_part119 (V-119) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part120 (V-120) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
      · by_cases h121_139 : V < 130
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r4_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r4_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r4_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
            · by_cases h127_130 : V < 128
              · have hi := strictBool_r4_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · by_cases h128_130 : V < 129
                · have hi := strictBool_r4_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
        · by_cases h130_139 : V < 134
          · by_cases h130_134 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := strictBool_r4_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_134 : V < 133
              · have hi := strictBool_r4_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
          · by_cases h134_139 : V < 136
            · by_cases h134_136 : V < 135
              · have hi := strictBool_r4_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · have hi := strictBool_r4_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
            · by_cases h136_139 : V < 137
              · have hi := strictBool_r4_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
              · by_cases h137_139 : V < 138
                · have hi := strictBool_r4_part137 (V-137) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
                · have hi := strictBool_r4_part138 (V-138) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi

theorem strictFast_r4 (V : ℕ) (hV : V ∈ List.range 139) : StrictAtFast (BoundaryTailBaseFastData.row 4 V) 4 V :=
  strictBool_sound _ _ _ (strictBool_r4 V hV)

theorem strict_r4 (V : ℕ) (hV : V ∈ List.range 139) : StrictCheckAt 4 V :=
  strictAtFast_sound _ _ _ (valid_r4 V hV) (strictFast_r4 V hV)

theorem zeroCertificate_r4_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (0+i)) 4 (0+i) := by decide +kernel

theorem zeroCertificate_r4_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (8+i)) 4 (8+i) := by decide +kernel

theorem zeroCertificate_r4_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (16+i)) 4 (16+i) := by decide +kernel

theorem zeroCertificate_r4_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (24+i)) 4 (24+i) := by decide +kernel

theorem zeroCertificate_r4_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (32+i)) 4 (32+i) := by decide +kernel

theorem zeroCertificate_r4_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (40+i)) 4 (40+i) := by decide +kernel

theorem zeroCertificate_r4_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (48+i)) 4 (48+i) := by decide +kernel

theorem zeroCertificate_r4_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (56+i)) 4 (56+i) := by decide +kernel

theorem zeroCertificate_r4_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (64+i)) 4 (64+i) := by decide +kernel

theorem zeroCertificate_r4_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (72+i)) 4 (72+i) := by decide +kernel

theorem zeroCertificate_r4_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (80+i)) 4 (80+i) := by decide +kernel

theorem zeroCertificate_r4_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (88+i)) 4 (88+i) := by decide +kernel

theorem zeroCertificate_r4_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (96+i)) 4 (96+i) := by decide +kernel

theorem zeroCertificate_r4_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (104+i)) 4 (104+i) := by decide +kernel

theorem zeroCertificate_r4_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (112+i)) 4 (112+i) := by decide +kernel

theorem zeroCertificate_r4_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (120+i)) 4 (120+i) := by decide +kernel

theorem zeroCertificate_r4_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 4 (128+i)) 4 (128+i) := by decide +kernel

theorem zeroCertificate_r4_part136 : ∀ i ∈ List.range 3, ZeroCertificate (BoundaryTailBaseFastData.row 4 (136+i)) 4 (136+i) := by decide +kernel

theorem zeroCertificate_r4 (V : ℕ) (hV : V ∈ List.range 139) : ZeroCertificate (BoundaryTailBaseFastData.row 4 V) 4 V := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := zeroCertificate_r4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := zeroCertificate_r4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r4 (V : ℕ) (hV : V ∈ List.range 139) : ZeroAtFast 4 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r4 V hV) (zeroCertificate_r4 V hV)

theorem zero_r4 (V : ℕ) (hV : V ∈ List.range 139) : ZeroCheckAt 4 V :=
  zeroAtFast_sound _ _ (zeroFast_r4 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r8_part0 : ∀ i ∈ List.range 8, CorrectAt 8 (0+i) := by decide +kernel

theorem correct_r8_part8 : ∀ i ∈ List.range 8, CorrectAt 8 (8+i) := by decide +kernel

theorem correct_r8_part16 : ∀ i ∈ List.range 8, CorrectAt 8 (16+i) := by decide +kernel

theorem correct_r8_part24 : ∀ i ∈ List.range 8, CorrectAt 8 (24+i) := by decide +kernel

theorem correct_r8_part32 : ∀ i ∈ List.range 8, CorrectAt 8 (32+i) := by decide +kernel

theorem correct_r8_part40 : ∀ i ∈ List.range 8, CorrectAt 8 (40+i) := by decide +kernel

theorem correct_r8_part48 : ∀ i ∈ List.range 8, CorrectAt 8 (48+i) := by decide +kernel

theorem correct_r8_part56 : ∀ i ∈ List.range 8, CorrectAt 8 (56+i) := by decide +kernel

theorem correct_r8_part64 : ∀ i ∈ List.range 8, CorrectAt 8 (64+i) := by decide +kernel

theorem correct_r8_part72 : ∀ i ∈ List.range 8, CorrectAt 8 (72+i) := by decide +kernel

theorem correct_r8_part80 : ∀ i ∈ List.range 8, CorrectAt 8 (80+i) := by decide +kernel

theorem correct_r8_part88 : ∀ i ∈ List.range 8, CorrectAt 8 (88+i) := by decide +kernel

theorem correct_r8_part96 : ∀ i ∈ List.range 8, CorrectAt 8 (96+i) := by decide +kernel

theorem correct_r8_part104 : ∀ i ∈ List.range 8, CorrectAt 8 (104+i) := by decide +kernel

theorem correct_r8_part112 : ∀ i ∈ List.range 8, CorrectAt 8 (112+i) := by decide +kernel

theorem correct_r8_part120 : ∀ i ∈ List.range 8, CorrectAt 8 (120+i) := by decide +kernel

theorem correct_r8_part128 : ∀ i ∈ List.range 7, CorrectAt 8 (128+i) := by decide +kernel

theorem correct_r8 (V : ℕ) (hV : V ∈ List.range 135) : CorrectAt 8 V := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := correct_r8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := correct_r8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r8_part0 : ∀ i ∈ List.range 8, BaseCheckAt 8 (0+i) := by decide +kernel

theorem base_r8_part8 : ∀ i ∈ List.range 8, BaseCheckAt 8 (8+i) := by decide +kernel

theorem base_r8_part16 : ∀ i ∈ List.range 8, BaseCheckAt 8 (16+i) := by decide +kernel

theorem base_r8_part24 : ∀ i ∈ List.range 8, BaseCheckAt 8 (24+i) := by decide +kernel

theorem base_r8_part32 : ∀ i ∈ List.range 8, BaseCheckAt 8 (32+i) := by decide +kernel

theorem base_r8_part40 : ∀ i ∈ List.range 8, BaseCheckAt 8 (40+i) := by decide +kernel

theorem base_r8_part48 : ∀ i ∈ List.range 8, BaseCheckAt 8 (48+i) := by decide +kernel

theorem base_r8_part56 : ∀ i ∈ List.range 8, BaseCheckAt 8 (56+i) := by decide +kernel

theorem base_r8_part64 : ∀ i ∈ List.range 8, BaseCheckAt 8 (64+i) := by decide +kernel

theorem base_r8_part72 : ∀ i ∈ List.range 8, BaseCheckAt 8 (72+i) := by decide +kernel

theorem base_r8_part80 : ∀ i ∈ List.range 8, BaseCheckAt 8 (80+i) := by decide +kernel

theorem base_r8_part88 : ∀ i ∈ List.range 8, BaseCheckAt 8 (88+i) := by decide +kernel

theorem base_r8_part96 : ∀ i ∈ List.range 8, BaseCheckAt 8 (96+i) := by decide +kernel

theorem base_r8_part104 : ∀ i ∈ List.range 8, BaseCheckAt 8 (104+i) := by decide +kernel

theorem base_r8_part112 : ∀ i ∈ List.range 8, BaseCheckAt 8 (112+i) := by decide +kernel

theorem base_r8_part120 : ∀ i ∈ List.range 8, BaseCheckAt 8 (120+i) := by decide +kernel

theorem base_r8_part128 : ∀ i ∈ List.range 7, BaseCheckAt 8 (128+i) := by decide +kernel

theorem base_r8 (V : ℕ) (hV : V ∈ List.range 135) : BaseCheckAt 8 V := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := base_r8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := base_r8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r8_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (0+i)) 8 (0+i) := by decide +kernel

theorem valid_r8_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (8+i)) 8 (8+i) := by decide +kernel

theorem valid_r8_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (16+i)) 8 (16+i) := by decide +kernel

theorem valid_r8_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (24+i)) 8 (24+i) := by decide +kernel

theorem valid_r8_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (32+i)) 8 (32+i) := by decide +kernel

theorem valid_r8_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (40+i)) 8 (40+i) := by decide +kernel

theorem valid_r8_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (48+i)) 8 (48+i) := by decide +kernel

theorem valid_r8_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (56+i)) 8 (56+i) := by decide +kernel

theorem valid_r8_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (64+i)) 8 (64+i) := by decide +kernel

theorem valid_r8_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (72+i)) 8 (72+i) := by decide +kernel

theorem valid_r8_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (80+i)) 8 (80+i) := by decide +kernel

theorem valid_r8_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (88+i)) 8 (88+i) := by decide +kernel

theorem valid_r8_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (96+i)) 8 (96+i) := by decide +kernel

theorem valid_r8_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (104+i)) 8 (104+i) := by decide +kernel

theorem valid_r8_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (112+i)) 8 (112+i) := by decide +kernel

theorem valid_r8_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 8 (120+i)) 8 (120+i) := by decide +kernel

theorem valid_r8_part128 : ∀ i ∈ List.range 7, Valid (BoundaryTailBaseFastData.row 8 (128+i)) 8 (128+i) := by decide +kernel

theorem valid_r8 (V : ℕ) (hV : V ∈ List.range 135) : Valid (BoundaryTailBaseFastData.row 8 V) 8 V := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := valid_r8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := valid_r8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r8_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (0+i)) 8 (0+i) = true := by decide +kernel

theorem strictBool_r8_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (1+i)) 8 (1+i) = true := by decide +kernel

theorem strictBool_r8_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (2+i)) 8 (2+i) = true := by decide +kernel

theorem strictBool_r8_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (3+i)) 8 (3+i) = true := by decide +kernel

theorem strictBool_r8_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (4+i)) 8 (4+i) = true := by decide +kernel

theorem strictBool_r8_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (5+i)) 8 (5+i) = true := by decide +kernel

theorem strictBool_r8_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (6+i)) 8 (6+i) = true := by decide +kernel

theorem strictBool_r8_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (7+i)) 8 (7+i) = true := by decide +kernel

theorem strictBool_r8_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (8+i)) 8 (8+i) = true := by decide +kernel

theorem strictBool_r8_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (9+i)) 8 (9+i) = true := by decide +kernel

theorem strictBool_r8_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (10+i)) 8 (10+i) = true := by decide +kernel

theorem strictBool_r8_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (11+i)) 8 (11+i) = true := by decide +kernel

theorem strictBool_r8_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (12+i)) 8 (12+i) = true := by decide +kernel

theorem strictBool_r8_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (13+i)) 8 (13+i) = true := by decide +kernel

theorem strictBool_r8_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (14+i)) 8 (14+i) = true := by decide +kernel

theorem strictBool_r8_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (15+i)) 8 (15+i) = true := by decide +kernel

theorem strictBool_r8_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (16+i)) 8 (16+i) = true := by decide +kernel

theorem strictBool_r8_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (17+i)) 8 (17+i) = true := by decide +kernel

theorem strictBool_r8_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (18+i)) 8 (18+i) = true := by decide +kernel

theorem strictBool_r8_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (19+i)) 8 (19+i) = true := by decide +kernel

theorem strictBool_r8_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (20+i)) 8 (20+i) = true := by decide +kernel

theorem strictBool_r8_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (21+i)) 8 (21+i) = true := by decide +kernel

theorem strictBool_r8_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (22+i)) 8 (22+i) = true := by decide +kernel

theorem strictBool_r8_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (23+i)) 8 (23+i) = true := by decide +kernel

theorem strictBool_r8_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (24+i)) 8 (24+i) = true := by decide +kernel

theorem strictBool_r8_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (25+i)) 8 (25+i) = true := by decide +kernel

theorem strictBool_r8_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (26+i)) 8 (26+i) = true := by decide +kernel

theorem strictBool_r8_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (27+i)) 8 (27+i) = true := by decide +kernel

theorem strictBool_r8_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (28+i)) 8 (28+i) = true := by decide +kernel

theorem strictBool_r8_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (29+i)) 8 (29+i) = true := by decide +kernel

theorem strictBool_r8_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (30+i)) 8 (30+i) = true := by decide +kernel

theorem strictBool_r8_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (31+i)) 8 (31+i) = true := by decide +kernel

theorem strictBool_r8_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (32+i)) 8 (32+i) = true := by decide +kernel

theorem strictBool_r8_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (33+i)) 8 (33+i) = true := by decide +kernel

theorem strictBool_r8_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (34+i)) 8 (34+i) = true := by decide +kernel

theorem strictBool_r8_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (35+i)) 8 (35+i) = true := by decide +kernel

theorem strictBool_r8_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (36+i)) 8 (36+i) = true := by decide +kernel

theorem strictBool_r8_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (37+i)) 8 (37+i) = true := by decide +kernel

theorem strictBool_r8_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (38+i)) 8 (38+i) = true := by decide +kernel

theorem strictBool_r8_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (39+i)) 8 (39+i) = true := by decide +kernel

theorem strictBool_r8_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (40+i)) 8 (40+i) = true := by decide +kernel

theorem strictBool_r8_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (41+i)) 8 (41+i) = true := by decide +kernel

theorem strictBool_r8_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (42+i)) 8 (42+i) = true := by decide +kernel

theorem strictBool_r8_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (43+i)) 8 (43+i) = true := by decide +kernel

theorem strictBool_r8_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (44+i)) 8 (44+i) = true := by decide +kernel

theorem strictBool_r8_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (45+i)) 8 (45+i) = true := by decide +kernel

theorem strictBool_r8_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (46+i)) 8 (46+i) = true := by decide +kernel

theorem strictBool_r8_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (47+i)) 8 (47+i) = true := by decide +kernel

theorem strictBool_r8_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (48+i)) 8 (48+i) = true := by decide +kernel

theorem strictBool_r8_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (49+i)) 8 (49+i) = true := by decide +kernel

theorem strictBool_r8_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (50+i)) 8 (50+i) = true := by decide +kernel

theorem strictBool_r8_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (51+i)) 8 (51+i) = true := by decide +kernel

theorem strictBool_r8_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (52+i)) 8 (52+i) = true := by decide +kernel

theorem strictBool_r8_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (53+i)) 8 (53+i) = true := by decide +kernel

theorem strictBool_r8_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (54+i)) 8 (54+i) = true := by decide +kernel

theorem strictBool_r8_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (55+i)) 8 (55+i) = true := by decide +kernel

theorem strictBool_r8_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (56+i)) 8 (56+i) = true := by decide +kernel

theorem strictBool_r8_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (57+i)) 8 (57+i) = true := by decide +kernel

theorem strictBool_r8_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (58+i)) 8 (58+i) = true := by decide +kernel

theorem strictBool_r8_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (59+i)) 8 (59+i) = true := by decide +kernel

theorem strictBool_r8_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (60+i)) 8 (60+i) = true := by decide +kernel

theorem strictBool_r8_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (61+i)) 8 (61+i) = true := by decide +kernel

theorem strictBool_r8_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (62+i)) 8 (62+i) = true := by decide +kernel

theorem strictBool_r8_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (63+i)) 8 (63+i) = true := by decide +kernel

theorem strictBool_r8_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (64+i)) 8 (64+i) = true := by decide +kernel

theorem strictBool_r8_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (65+i)) 8 (65+i) = true := by decide +kernel

theorem strictBool_r8_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (66+i)) 8 (66+i) = true := by decide +kernel

theorem strictBool_r8_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (67+i)) 8 (67+i) = true := by decide +kernel

theorem strictBool_r8_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (68+i)) 8 (68+i) = true := by decide +kernel

theorem strictBool_r8_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (69+i)) 8 (69+i) = true := by decide +kernel

theorem strictBool_r8_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (70+i)) 8 (70+i) = true := by decide +kernel

theorem strictBool_r8_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (71+i)) 8 (71+i) = true := by decide +kernel

theorem strictBool_r8_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (72+i)) 8 (72+i) = true := by decide +kernel

theorem strictBool_r8_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (73+i)) 8 (73+i) = true := by decide +kernel

theorem strictBool_r8_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (74+i)) 8 (74+i) = true := by decide +kernel

theorem strictBool_r8_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (75+i)) 8 (75+i) = true := by decide +kernel

theorem strictBool_r8_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (76+i)) 8 (76+i) = true := by decide +kernel

theorem strictBool_r8_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (77+i)) 8 (77+i) = true := by decide +kernel

theorem strictBool_r8_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (78+i)) 8 (78+i) = true := by decide +kernel

theorem strictBool_r8_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (79+i)) 8 (79+i) = true := by decide +kernel

theorem strictBool_r8_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (80+i)) 8 (80+i) = true := by decide +kernel

theorem strictBool_r8_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (81+i)) 8 (81+i) = true := by decide +kernel

theorem strictBool_r8_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (82+i)) 8 (82+i) = true := by decide +kernel

theorem strictBool_r8_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (83+i)) 8 (83+i) = true := by decide +kernel

theorem strictBool_r8_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (84+i)) 8 (84+i) = true := by decide +kernel

theorem strictBool_r8_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (85+i)) 8 (85+i) = true := by decide +kernel

theorem strictBool_r8_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (86+i)) 8 (86+i) = true := by decide +kernel

theorem strictBool_r8_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (87+i)) 8 (87+i) = true := by decide +kernel

theorem strictBool_r8_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (88+i)) 8 (88+i) = true := by decide +kernel

theorem strictBool_r8_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (89+i)) 8 (89+i) = true := by decide +kernel

theorem strictBool_r8_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (90+i)) 8 (90+i) = true := by decide +kernel

theorem strictBool_r8_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (91+i)) 8 (91+i) = true := by decide +kernel

theorem strictBool_r8_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (92+i)) 8 (92+i) = true := by decide +kernel

theorem strictBool_r8_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (93+i)) 8 (93+i) = true := by decide +kernel

theorem strictBool_r8_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (94+i)) 8 (94+i) = true := by decide +kernel

theorem strictBool_r8_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (95+i)) 8 (95+i) = true := by decide +kernel

theorem strictBool_r8_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (96+i)) 8 (96+i) = true := by decide +kernel

theorem strictBool_r8_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (97+i)) 8 (97+i) = true := by decide +kernel

theorem strictBool_r8_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (98+i)) 8 (98+i) = true := by decide +kernel

theorem strictBool_r8_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (99+i)) 8 (99+i) = true := by decide +kernel

theorem strictBool_r8_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (100+i)) 8 (100+i) = true := by decide +kernel

theorem strictBool_r8_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (101+i)) 8 (101+i) = true := by decide +kernel

theorem strictBool_r8_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (102+i)) 8 (102+i) = true := by decide +kernel

theorem strictBool_r8_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (103+i)) 8 (103+i) = true := by decide +kernel

theorem strictBool_r8_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (104+i)) 8 (104+i) = true := by decide +kernel

theorem strictBool_r8_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (105+i)) 8 (105+i) = true := by decide +kernel

theorem strictBool_r8_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (106+i)) 8 (106+i) = true := by decide +kernel

theorem strictBool_r8_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (107+i)) 8 (107+i) = true := by decide +kernel

theorem strictBool_r8_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (108+i)) 8 (108+i) = true := by decide +kernel

theorem strictBool_r8_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (109+i)) 8 (109+i) = true := by decide +kernel

theorem strictBool_r8_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (110+i)) 8 (110+i) = true := by decide +kernel

theorem strictBool_r8_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (111+i)) 8 (111+i) = true := by decide +kernel

theorem strictBool_r8_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (112+i)) 8 (112+i) = true := by decide +kernel

theorem strictBool_r8_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (113+i)) 8 (113+i) = true := by decide +kernel

theorem strictBool_r8_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (114+i)) 8 (114+i) = true := by decide +kernel

theorem strictBool_r8_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (115+i)) 8 (115+i) = true := by decide +kernel

theorem strictBool_r8_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (116+i)) 8 (116+i) = true := by decide +kernel

theorem strictBool_r8_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (117+i)) 8 (117+i) = true := by decide +kernel

theorem strictBool_r8_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (118+i)) 8 (118+i) = true := by decide +kernel

theorem strictBool_r8_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (119+i)) 8 (119+i) = true := by decide +kernel

theorem strictBool_r8_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (120+i)) 8 (120+i) = true := by decide +kernel

theorem strictBool_r8_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (121+i)) 8 (121+i) = true := by decide +kernel

theorem strictBool_r8_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (122+i)) 8 (122+i) = true := by decide +kernel

theorem strictBool_r8_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (123+i)) 8 (123+i) = true := by decide +kernel

theorem strictBool_r8_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (124+i)) 8 (124+i) = true := by decide +kernel

theorem strictBool_r8_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (125+i)) 8 (125+i) = true := by decide +kernel

theorem strictBool_r8_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (126+i)) 8 (126+i) = true := by decide +kernel

theorem strictBool_r8_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (127+i)) 8 (127+i) = true := by decide +kernel

theorem strictBool_r8_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (128+i)) 8 (128+i) = true := by decide +kernel

theorem strictBool_r8_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (129+i)) 8 (129+i) = true := by decide +kernel

theorem strictBool_r8_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (130+i)) 8 (130+i) = true := by decide +kernel

theorem strictBool_r8_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (131+i)) 8 (131+i) = true := by decide +kernel

theorem strictBool_r8_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (132+i)) 8 (132+i) = true := by decide +kernel

theorem strictBool_r8_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (133+i)) 8 (133+i) = true := by decide +kernel

theorem strictBool_r8_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 8 (134+i)) 8 (134+i) = true := by decide +kernel

theorem strictBool_r8 (V : ℕ) (hV : V ∈ List.range 135) : strictBool (BoundaryTailBaseFastData.row 8 V) 8 V = true := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r8_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r8_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r8_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r8_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r8_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r8_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r8_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r8_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r8_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r8_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r8_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r8_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r8_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r8_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r8_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := strictBool_r8_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := strictBool_r8_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r8_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r8_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r8_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r8_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r8_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r8_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r8_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_50 : V < 48
              · have hi := strictBool_r8_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · by_cases h48_50 : V < 49
                · have hi := strictBool_r8_part48 (V-48) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r8_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r8_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r8_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r8_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r8_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r8_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r8_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_67 : V < 65
              · have hi := strictBool_r8_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · by_cases h65_67 : V < 66
                · have hi := strictBool_r8_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
  · by_cases h67_135 : V < 101
    · by_cases h67_101 : V < 84
      · by_cases h67_84 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r8_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r8_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r8_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r8_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
        · by_cases h75_84 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r8_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r8_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
          · by_cases h79_84 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r8_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_84 : V < 82
              · have hi := strictBool_r8_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · by_cases h82_84 : V < 83
                · have hi := strictBool_r8_part82 (V-82) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
      · by_cases h84_101 : V < 92
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r8_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r8_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r8_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r8_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
        · by_cases h92_101 : V < 96
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r8_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r8_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
          · by_cases h96_101 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r8_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_101 : V < 99
              · have hi := strictBool_r8_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · by_cases h99_101 : V < 100
                · have hi := strictBool_r8_part99 (V-99) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
    · by_cases h101_135 : V < 118
      · by_cases h101_118 : V < 109
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r8_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r8_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r8_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r8_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h109_118 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r8_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r8_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · by_cases h113_118 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r8_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_118 : V < 116
              · have hi := strictBool_r8_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · by_cases h116_118 : V < 117
                · have hi := strictBool_r8_part116 (V-116) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
      · by_cases h118_135 : V < 126
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r8_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r8_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r8_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r8_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
        · by_cases h126_135 : V < 130
          · by_cases h126_130 : V < 128
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r8_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
            · by_cases h128_130 : V < 129
              · have hi := strictBool_r8_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
          · by_cases h130_135 : V < 132
            · by_cases h130_132 : V < 131
              · have hi := strictBool_r8_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := strictBool_r8_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
            · by_cases h132_135 : V < 133
              · have hi := strictBool_r8_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · by_cases h133_135 : V < 134
                · have hi := strictBool_r8_part133 (V-133) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
                · have hi := strictBool_r8_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi

theorem strictFast_r8 (V : ℕ) (hV : V ∈ List.range 135) : StrictAtFast (BoundaryTailBaseFastData.row 8 V) 8 V :=
  strictBool_sound _ _ _ (strictBool_r8 V hV)

theorem strict_r8 (V : ℕ) (hV : V ∈ List.range 135) : StrictCheckAt 8 V :=
  strictAtFast_sound _ _ _ (valid_r8 V hV) (strictFast_r8 V hV)

theorem zeroCertificate_r8_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (0+i)) 8 (0+i) := by decide +kernel

theorem zeroCertificate_r8_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (8+i)) 8 (8+i) := by decide +kernel

theorem zeroCertificate_r8_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (16+i)) 8 (16+i) := by decide +kernel

theorem zeroCertificate_r8_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (24+i)) 8 (24+i) := by decide +kernel

theorem zeroCertificate_r8_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (32+i)) 8 (32+i) := by decide +kernel

theorem zeroCertificate_r8_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (40+i)) 8 (40+i) := by decide +kernel

theorem zeroCertificate_r8_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (48+i)) 8 (48+i) := by decide +kernel

theorem zeroCertificate_r8_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (56+i)) 8 (56+i) := by decide +kernel

theorem zeroCertificate_r8_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (64+i)) 8 (64+i) := by decide +kernel

theorem zeroCertificate_r8_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (72+i)) 8 (72+i) := by decide +kernel

theorem zeroCertificate_r8_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (80+i)) 8 (80+i) := by decide +kernel

theorem zeroCertificate_r8_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (88+i)) 8 (88+i) := by decide +kernel

theorem zeroCertificate_r8_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (96+i)) 8 (96+i) := by decide +kernel

theorem zeroCertificate_r8_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (104+i)) 8 (104+i) := by decide +kernel

theorem zeroCertificate_r8_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (112+i)) 8 (112+i) := by decide +kernel

theorem zeroCertificate_r8_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 8 (120+i)) 8 (120+i) := by decide +kernel

theorem zeroCertificate_r8_part128 : ∀ i ∈ List.range 7, ZeroCertificate (BoundaryTailBaseFastData.row 8 (128+i)) 8 (128+i) := by decide +kernel

theorem zeroCertificate_r8 (V : ℕ) (hV : V ∈ List.range 135) : ZeroCertificate (BoundaryTailBaseFastData.row 8 V) 8 V := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := zeroCertificate_r8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := zeroCertificate_r8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r8 (V : ℕ) (hV : V ∈ List.range 135) : ZeroAtFast 8 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r8 V hV) (zeroCertificate_r8 V hV)

theorem zero_r8 (V : ℕ) (hV : V ∈ List.range 135) : ZeroCheckAt 8 V :=
  zeroAtFast_sound _ _ (zeroFast_r8 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r12_part0 : ∀ i ∈ List.range 8, CorrectAt 12 (0+i) := by decide +kernel

theorem correct_r12_part8 : ∀ i ∈ List.range 8, CorrectAt 12 (8+i) := by decide +kernel

theorem correct_r12_part16 : ∀ i ∈ List.range 8, CorrectAt 12 (16+i) := by decide +kernel

theorem correct_r12_part24 : ∀ i ∈ List.range 8, CorrectAt 12 (24+i) := by decide +kernel

theorem correct_r12_part32 : ∀ i ∈ List.range 8, CorrectAt 12 (32+i) := by decide +kernel

theorem correct_r12_part40 : ∀ i ∈ List.range 8, CorrectAt 12 (40+i) := by decide +kernel

theorem correct_r12_part48 : ∀ i ∈ List.range 8, CorrectAt 12 (48+i) := by decide +kernel

theorem correct_r12_part56 : ∀ i ∈ List.range 8, CorrectAt 12 (56+i) := by decide +kernel

theorem correct_r12_part64 : ∀ i ∈ List.range 8, CorrectAt 12 (64+i) := by decide +kernel

theorem correct_r12_part72 : ∀ i ∈ List.range 8, CorrectAt 12 (72+i) := by decide +kernel

theorem correct_r12_part80 : ∀ i ∈ List.range 8, CorrectAt 12 (80+i) := by decide +kernel

theorem correct_r12_part88 : ∀ i ∈ List.range 8, CorrectAt 12 (88+i) := by decide +kernel

theorem correct_r12_part96 : ∀ i ∈ List.range 8, CorrectAt 12 (96+i) := by decide +kernel

theorem correct_r12_part104 : ∀ i ∈ List.range 8, CorrectAt 12 (104+i) := by decide +kernel

theorem correct_r12_part112 : ∀ i ∈ List.range 8, CorrectAt 12 (112+i) := by decide +kernel

theorem correct_r12_part120 : ∀ i ∈ List.range 8, CorrectAt 12 (120+i) := by decide +kernel

theorem correct_r12_part128 : ∀ i ∈ List.range 3, CorrectAt 12 (128+i) := by decide +kernel

theorem correct_r12 (V : ℕ) (hV : V ∈ List.range 131) : CorrectAt 12 V := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := correct_r12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := correct_r12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r12_part0 : ∀ i ∈ List.range 8, BaseCheckAt 12 (0+i) := by decide +kernel

theorem base_r12_part8 : ∀ i ∈ List.range 8, BaseCheckAt 12 (8+i) := by decide +kernel

theorem base_r12_part16 : ∀ i ∈ List.range 8, BaseCheckAt 12 (16+i) := by decide +kernel

theorem base_r12_part24 : ∀ i ∈ List.range 8, BaseCheckAt 12 (24+i) := by decide +kernel

theorem base_r12_part32 : ∀ i ∈ List.range 8, BaseCheckAt 12 (32+i) := by decide +kernel

theorem base_r12_part40 : ∀ i ∈ List.range 8, BaseCheckAt 12 (40+i) := by decide +kernel

theorem base_r12_part48 : ∀ i ∈ List.range 8, BaseCheckAt 12 (48+i) := by decide +kernel

theorem base_r12_part56 : ∀ i ∈ List.range 8, BaseCheckAt 12 (56+i) := by decide +kernel

theorem base_r12_part64 : ∀ i ∈ List.range 8, BaseCheckAt 12 (64+i) := by decide +kernel

theorem base_r12_part72 : ∀ i ∈ List.range 8, BaseCheckAt 12 (72+i) := by decide +kernel

theorem base_r12_part80 : ∀ i ∈ List.range 8, BaseCheckAt 12 (80+i) := by decide +kernel

theorem base_r12_part88 : ∀ i ∈ List.range 8, BaseCheckAt 12 (88+i) := by decide +kernel

theorem base_r12_part96 : ∀ i ∈ List.range 8, BaseCheckAt 12 (96+i) := by decide +kernel

theorem base_r12_part104 : ∀ i ∈ List.range 8, BaseCheckAt 12 (104+i) := by decide +kernel

theorem base_r12_part112 : ∀ i ∈ List.range 8, BaseCheckAt 12 (112+i) := by decide +kernel

theorem base_r12_part120 : ∀ i ∈ List.range 8, BaseCheckAt 12 (120+i) := by decide +kernel

theorem base_r12_part128 : ∀ i ∈ List.range 3, BaseCheckAt 12 (128+i) := by decide +kernel

theorem base_r12 (V : ℕ) (hV : V ∈ List.range 131) : BaseCheckAt 12 V := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := base_r12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := base_r12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r12_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (0+i)) 12 (0+i) := by decide +kernel

theorem valid_r12_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (8+i)) 12 (8+i) := by decide +kernel

theorem valid_r12_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (16+i)) 12 (16+i) := by decide +kernel

theorem valid_r12_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (24+i)) 12 (24+i) := by decide +kernel

theorem valid_r12_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (32+i)) 12 (32+i) := by decide +kernel

theorem valid_r12_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (40+i)) 12 (40+i) := by decide +kernel

theorem valid_r12_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (48+i)) 12 (48+i) := by decide +kernel

theorem valid_r12_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (56+i)) 12 (56+i) := by decide +kernel

theorem valid_r12_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (64+i)) 12 (64+i) := by decide +kernel

theorem valid_r12_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (72+i)) 12 (72+i) := by decide +kernel

theorem valid_r12_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (80+i)) 12 (80+i) := by decide +kernel

theorem valid_r12_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (88+i)) 12 (88+i) := by decide +kernel

theorem valid_r12_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (96+i)) 12 (96+i) := by decide +kernel

theorem valid_r12_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (104+i)) 12 (104+i) := by decide +kernel

theorem valid_r12_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (112+i)) 12 (112+i) := by decide +kernel

theorem valid_r12_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 12 (120+i)) 12 (120+i) := by decide +kernel

theorem valid_r12_part128 : ∀ i ∈ List.range 3, Valid (BoundaryTailBaseFastData.row 12 (128+i)) 12 (128+i) := by decide +kernel

theorem valid_r12 (V : ℕ) (hV : V ∈ List.range 131) : Valid (BoundaryTailBaseFastData.row 12 V) 12 V := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := valid_r12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := valid_r12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r12_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (0+i)) 12 (0+i) = true := by decide +kernel

theorem strictBool_r12_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (1+i)) 12 (1+i) = true := by decide +kernel

theorem strictBool_r12_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (2+i)) 12 (2+i) = true := by decide +kernel

theorem strictBool_r12_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (3+i)) 12 (3+i) = true := by decide +kernel

theorem strictBool_r12_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (4+i)) 12 (4+i) = true := by decide +kernel

theorem strictBool_r12_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (5+i)) 12 (5+i) = true := by decide +kernel

theorem strictBool_r12_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (6+i)) 12 (6+i) = true := by decide +kernel

theorem strictBool_r12_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (7+i)) 12 (7+i) = true := by decide +kernel

theorem strictBool_r12_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (8+i)) 12 (8+i) = true := by decide +kernel

theorem strictBool_r12_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (9+i)) 12 (9+i) = true := by decide +kernel

theorem strictBool_r12_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (10+i)) 12 (10+i) = true := by decide +kernel

theorem strictBool_r12_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (11+i)) 12 (11+i) = true := by decide +kernel

theorem strictBool_r12_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (12+i)) 12 (12+i) = true := by decide +kernel

theorem strictBool_r12_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (13+i)) 12 (13+i) = true := by decide +kernel

theorem strictBool_r12_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (14+i)) 12 (14+i) = true := by decide +kernel

theorem strictBool_r12_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (15+i)) 12 (15+i) = true := by decide +kernel

theorem strictBool_r12_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (16+i)) 12 (16+i) = true := by decide +kernel

theorem strictBool_r12_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (17+i)) 12 (17+i) = true := by decide +kernel

theorem strictBool_r12_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (18+i)) 12 (18+i) = true := by decide +kernel

theorem strictBool_r12_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (19+i)) 12 (19+i) = true := by decide +kernel

theorem strictBool_r12_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (20+i)) 12 (20+i) = true := by decide +kernel

theorem strictBool_r12_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (21+i)) 12 (21+i) = true := by decide +kernel

theorem strictBool_r12_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (22+i)) 12 (22+i) = true := by decide +kernel

theorem strictBool_r12_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (23+i)) 12 (23+i) = true := by decide +kernel

theorem strictBool_r12_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (24+i)) 12 (24+i) = true := by decide +kernel

theorem strictBool_r12_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (25+i)) 12 (25+i) = true := by decide +kernel

theorem strictBool_r12_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (26+i)) 12 (26+i) = true := by decide +kernel

theorem strictBool_r12_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (27+i)) 12 (27+i) = true := by decide +kernel

theorem strictBool_r12_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (28+i)) 12 (28+i) = true := by decide +kernel

theorem strictBool_r12_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (29+i)) 12 (29+i) = true := by decide +kernel

theorem strictBool_r12_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (30+i)) 12 (30+i) = true := by decide +kernel

theorem strictBool_r12_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (31+i)) 12 (31+i) = true := by decide +kernel

theorem strictBool_r12_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (32+i)) 12 (32+i) = true := by decide +kernel

theorem strictBool_r12_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (33+i)) 12 (33+i) = true := by decide +kernel

theorem strictBool_r12_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (34+i)) 12 (34+i) = true := by decide +kernel

theorem strictBool_r12_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (35+i)) 12 (35+i) = true := by decide +kernel

theorem strictBool_r12_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (36+i)) 12 (36+i) = true := by decide +kernel

theorem strictBool_r12_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (37+i)) 12 (37+i) = true := by decide +kernel

theorem strictBool_r12_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (38+i)) 12 (38+i) = true := by decide +kernel

theorem strictBool_r12_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (39+i)) 12 (39+i) = true := by decide +kernel

theorem strictBool_r12_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (40+i)) 12 (40+i) = true := by decide +kernel

theorem strictBool_r12_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (41+i)) 12 (41+i) = true := by decide +kernel

theorem strictBool_r12_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (42+i)) 12 (42+i) = true := by decide +kernel

theorem strictBool_r12_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (43+i)) 12 (43+i) = true := by decide +kernel

theorem strictBool_r12_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (44+i)) 12 (44+i) = true := by decide +kernel

theorem strictBool_r12_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (45+i)) 12 (45+i) = true := by decide +kernel

theorem strictBool_r12_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (46+i)) 12 (46+i) = true := by decide +kernel

theorem strictBool_r12_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (47+i)) 12 (47+i) = true := by decide +kernel

theorem strictBool_r12_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (48+i)) 12 (48+i) = true := by decide +kernel

theorem strictBool_r12_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (49+i)) 12 (49+i) = true := by decide +kernel

theorem strictBool_r12_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (50+i)) 12 (50+i) = true := by decide +kernel

theorem strictBool_r12_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (51+i)) 12 (51+i) = true := by decide +kernel

theorem strictBool_r12_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (52+i)) 12 (52+i) = true := by decide +kernel

theorem strictBool_r12_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (53+i)) 12 (53+i) = true := by decide +kernel

theorem strictBool_r12_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (54+i)) 12 (54+i) = true := by decide +kernel

theorem strictBool_r12_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (55+i)) 12 (55+i) = true := by decide +kernel

theorem strictBool_r12_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (56+i)) 12 (56+i) = true := by decide +kernel

theorem strictBool_r12_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (57+i)) 12 (57+i) = true := by decide +kernel

theorem strictBool_r12_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (58+i)) 12 (58+i) = true := by decide +kernel

theorem strictBool_r12_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (59+i)) 12 (59+i) = true := by decide +kernel

theorem strictBool_r12_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (60+i)) 12 (60+i) = true := by decide +kernel

theorem strictBool_r12_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (61+i)) 12 (61+i) = true := by decide +kernel

theorem strictBool_r12_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (62+i)) 12 (62+i) = true := by decide +kernel

theorem strictBool_r12_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (63+i)) 12 (63+i) = true := by decide +kernel

theorem strictBool_r12_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (64+i)) 12 (64+i) = true := by decide +kernel

theorem strictBool_r12_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (65+i)) 12 (65+i) = true := by decide +kernel

theorem strictBool_r12_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (66+i)) 12 (66+i) = true := by decide +kernel

theorem strictBool_r12_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (67+i)) 12 (67+i) = true := by decide +kernel

theorem strictBool_r12_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (68+i)) 12 (68+i) = true := by decide +kernel

theorem strictBool_r12_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (69+i)) 12 (69+i) = true := by decide +kernel

theorem strictBool_r12_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (70+i)) 12 (70+i) = true := by decide +kernel

theorem strictBool_r12_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (71+i)) 12 (71+i) = true := by decide +kernel

theorem strictBool_r12_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (72+i)) 12 (72+i) = true := by decide +kernel

theorem strictBool_r12_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (73+i)) 12 (73+i) = true := by decide +kernel

theorem strictBool_r12_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (74+i)) 12 (74+i) = true := by decide +kernel

theorem strictBool_r12_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (75+i)) 12 (75+i) = true := by decide +kernel

theorem strictBool_r12_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (76+i)) 12 (76+i) = true := by decide +kernel

theorem strictBool_r12_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (77+i)) 12 (77+i) = true := by decide +kernel

theorem strictBool_r12_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (78+i)) 12 (78+i) = true := by decide +kernel

theorem strictBool_r12_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (79+i)) 12 (79+i) = true := by decide +kernel

theorem strictBool_r12_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (80+i)) 12 (80+i) = true := by decide +kernel

theorem strictBool_r12_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (81+i)) 12 (81+i) = true := by decide +kernel

theorem strictBool_r12_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (82+i)) 12 (82+i) = true := by decide +kernel

theorem strictBool_r12_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (83+i)) 12 (83+i) = true := by decide +kernel

theorem strictBool_r12_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (84+i)) 12 (84+i) = true := by decide +kernel

theorem strictBool_r12_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (85+i)) 12 (85+i) = true := by decide +kernel

theorem strictBool_r12_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (86+i)) 12 (86+i) = true := by decide +kernel

theorem strictBool_r12_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (87+i)) 12 (87+i) = true := by decide +kernel

theorem strictBool_r12_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (88+i)) 12 (88+i) = true := by decide +kernel

theorem strictBool_r12_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (89+i)) 12 (89+i) = true := by decide +kernel

theorem strictBool_r12_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (90+i)) 12 (90+i) = true := by decide +kernel

theorem strictBool_r12_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (91+i)) 12 (91+i) = true := by decide +kernel

theorem strictBool_r12_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (92+i)) 12 (92+i) = true := by decide +kernel

theorem strictBool_r12_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (93+i)) 12 (93+i) = true := by decide +kernel

theorem strictBool_r12_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (94+i)) 12 (94+i) = true := by decide +kernel

theorem strictBool_r12_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (95+i)) 12 (95+i) = true := by decide +kernel

theorem strictBool_r12_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (96+i)) 12 (96+i) = true := by decide +kernel

theorem strictBool_r12_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (97+i)) 12 (97+i) = true := by decide +kernel

theorem strictBool_r12_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (98+i)) 12 (98+i) = true := by decide +kernel

theorem strictBool_r12_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (99+i)) 12 (99+i) = true := by decide +kernel

theorem strictBool_r12_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (100+i)) 12 (100+i) = true := by decide +kernel

theorem strictBool_r12_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (101+i)) 12 (101+i) = true := by decide +kernel

theorem strictBool_r12_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (102+i)) 12 (102+i) = true := by decide +kernel

theorem strictBool_r12_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (103+i)) 12 (103+i) = true := by decide +kernel

theorem strictBool_r12_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (104+i)) 12 (104+i) = true := by decide +kernel

theorem strictBool_r12_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (105+i)) 12 (105+i) = true := by decide +kernel

theorem strictBool_r12_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (106+i)) 12 (106+i) = true := by decide +kernel

theorem strictBool_r12_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (107+i)) 12 (107+i) = true := by decide +kernel

theorem strictBool_r12_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (108+i)) 12 (108+i) = true := by decide +kernel

theorem strictBool_r12_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (109+i)) 12 (109+i) = true := by decide +kernel

theorem strictBool_r12_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (110+i)) 12 (110+i) = true := by decide +kernel

theorem strictBool_r12_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (111+i)) 12 (111+i) = true := by decide +kernel

theorem strictBool_r12_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (112+i)) 12 (112+i) = true := by decide +kernel

theorem strictBool_r12_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (113+i)) 12 (113+i) = true := by decide +kernel

theorem strictBool_r12_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (114+i)) 12 (114+i) = true := by decide +kernel

theorem strictBool_r12_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (115+i)) 12 (115+i) = true := by decide +kernel

theorem strictBool_r12_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (116+i)) 12 (116+i) = true := by decide +kernel

theorem strictBool_r12_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (117+i)) 12 (117+i) = true := by decide +kernel

theorem strictBool_r12_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (118+i)) 12 (118+i) = true := by decide +kernel

theorem strictBool_r12_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (119+i)) 12 (119+i) = true := by decide +kernel

theorem strictBool_r12_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (120+i)) 12 (120+i) = true := by decide +kernel

theorem strictBool_r12_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (121+i)) 12 (121+i) = true := by decide +kernel

theorem strictBool_r12_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (122+i)) 12 (122+i) = true := by decide +kernel

theorem strictBool_r12_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (123+i)) 12 (123+i) = true := by decide +kernel

theorem strictBool_r12_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (124+i)) 12 (124+i) = true := by decide +kernel

theorem strictBool_r12_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (125+i)) 12 (125+i) = true := by decide +kernel

theorem strictBool_r12_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (126+i)) 12 (126+i) = true := by decide +kernel

theorem strictBool_r12_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (127+i)) 12 (127+i) = true := by decide +kernel

theorem strictBool_r12_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (128+i)) 12 (128+i) = true := by decide +kernel

theorem strictBool_r12_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (129+i)) 12 (129+i) = true := by decide +kernel

theorem strictBool_r12_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 12 (130+i)) 12 (130+i) = true := by decide +kernel

theorem strictBool_r12 (V : ℕ) (hV : V ∈ List.range 131) : strictBool (BoundaryTailBaseFastData.row 12 V) 12 V = true := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 65
  · by_cases h0_65 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r12_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r12_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r12_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r12_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r12_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r12_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r12_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r12_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r12_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r12_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r12_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r12_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r12_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r12_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r12_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r12_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
    · by_cases h32_65 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r12_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r12_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r12_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r12_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r12_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r12_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r12_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r12_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
      · by_cases h48_65 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r12_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r12_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r12_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r12_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
        · by_cases h56_65 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r12_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r12_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_65 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r12_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_65 : V < 63
              · have hi := strictBool_r12_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · by_cases h63_65 : V < 64
                · have hi := strictBool_r12_part63 (V-63) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
                · have hi := strictBool_r12_part64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h65_131 : V < 98
    · by_cases h65_98 : V < 81
      · by_cases h65_81 : V < 73
        · by_cases h65_73 : V < 69
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r12_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r12_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r12_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r12_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h73_81 : V < 77
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r12_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r12_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r12_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r12_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h81_98 : V < 89
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r12_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r12_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r12_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r12_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h89_98 : V < 93
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r12_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r12_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h93_98 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r12_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_98 : V < 96
              · have hi := strictBool_r12_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · by_cases h96_98 : V < 97
                · have hi := strictBool_r12_part96 (V-96) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                · have hi := strictBool_r12_part97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
    · by_cases h98_131 : V < 114
      · by_cases h98_114 : V < 106
        · by_cases h98_106 : V < 102
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r12_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r12_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r12_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r12_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r12_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r12_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r12_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r12_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
      · by_cases h114_131 : V < 122
        · by_cases h114_122 : V < 118
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r12_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r12_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r12_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r12_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
        · by_cases h122_131 : V < 126
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r12_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r12_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
          · by_cases h126_131 : V < 128
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r12_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r12_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
            · by_cases h128_131 : V < 129
              · have hi := strictBool_r12_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · by_cases h129_131 : V < 130
                · have hi := strictBool_r12_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
                · have hi := strictBool_r12_part130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi

theorem strictFast_r12 (V : ℕ) (hV : V ∈ List.range 131) : StrictAtFast (BoundaryTailBaseFastData.row 12 V) 12 V :=
  strictBool_sound _ _ _ (strictBool_r12 V hV)

theorem strict_r12 (V : ℕ) (hV : V ∈ List.range 131) : StrictCheckAt 12 V :=
  strictAtFast_sound _ _ _ (valid_r12 V hV) (strictFast_r12 V hV)

theorem zeroCertificate_r12_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (0+i)) 12 (0+i) := by decide +kernel

theorem zeroCertificate_r12_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (8+i)) 12 (8+i) := by decide +kernel

theorem zeroCertificate_r12_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (16+i)) 12 (16+i) := by decide +kernel

theorem zeroCertificate_r12_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (24+i)) 12 (24+i) := by decide +kernel

theorem zeroCertificate_r12_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (32+i)) 12 (32+i) := by decide +kernel

theorem zeroCertificate_r12_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (40+i)) 12 (40+i) := by decide +kernel

theorem zeroCertificate_r12_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (48+i)) 12 (48+i) := by decide +kernel

theorem zeroCertificate_r12_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (56+i)) 12 (56+i) := by decide +kernel

theorem zeroCertificate_r12_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (64+i)) 12 (64+i) := by decide +kernel

theorem zeroCertificate_r12_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (72+i)) 12 (72+i) := by decide +kernel

theorem zeroCertificate_r12_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (80+i)) 12 (80+i) := by decide +kernel

theorem zeroCertificate_r12_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (88+i)) 12 (88+i) := by decide +kernel

theorem zeroCertificate_r12_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (96+i)) 12 (96+i) := by decide +kernel

theorem zeroCertificate_r12_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (104+i)) 12 (104+i) := by decide +kernel

theorem zeroCertificate_r12_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (112+i)) 12 (112+i) := by decide +kernel

theorem zeroCertificate_r12_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 12 (120+i)) 12 (120+i) := by decide +kernel

theorem zeroCertificate_r12_part128 : ∀ i ∈ List.range 3, ZeroCertificate (BoundaryTailBaseFastData.row 12 (128+i)) 12 (128+i) := by decide +kernel

theorem zeroCertificate_r12 (V : ℕ) (hV : V ∈ List.range 131) : ZeroCertificate (BoundaryTailBaseFastData.row 12 V) 12 V := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := zeroCertificate_r12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := zeroCertificate_r12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r12 (V : ℕ) (hV : V ∈ List.range 131) : ZeroAtFast 12 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r12 V hV) (zeroCertificate_r12 V hV)

theorem zero_r12 (V : ℕ) (hV : V ∈ List.range 131) : ZeroCheckAt 12 V :=
  zeroAtFast_sound _ _ (zeroFast_r12 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r16_part0 : ∀ i ∈ List.range 8, CorrectAt 16 (0+i) := by decide +kernel

theorem correct_r16_part8 : ∀ i ∈ List.range 8, CorrectAt 16 (8+i) := by decide +kernel

theorem correct_r16_part16 : ∀ i ∈ List.range 8, CorrectAt 16 (16+i) := by decide +kernel

theorem correct_r16_part24 : ∀ i ∈ List.range 8, CorrectAt 16 (24+i) := by decide +kernel

theorem correct_r16_part32 : ∀ i ∈ List.range 8, CorrectAt 16 (32+i) := by decide +kernel

theorem correct_r16_part40 : ∀ i ∈ List.range 8, CorrectAt 16 (40+i) := by decide +kernel

theorem correct_r16_part48 : ∀ i ∈ List.range 8, CorrectAt 16 (48+i) := by decide +kernel

theorem correct_r16_part56 : ∀ i ∈ List.range 8, CorrectAt 16 (56+i) := by decide +kernel

theorem correct_r16_part64 : ∀ i ∈ List.range 8, CorrectAt 16 (64+i) := by decide +kernel

theorem correct_r16_part72 : ∀ i ∈ List.range 8, CorrectAt 16 (72+i) := by decide +kernel

theorem correct_r16_part80 : ∀ i ∈ List.range 8, CorrectAt 16 (80+i) := by decide +kernel

theorem correct_r16_part88 : ∀ i ∈ List.range 8, CorrectAt 16 (88+i) := by decide +kernel

theorem correct_r16_part96 : ∀ i ∈ List.range 8, CorrectAt 16 (96+i) := by decide +kernel

theorem correct_r16_part104 : ∀ i ∈ List.range 8, CorrectAt 16 (104+i) := by decide +kernel

theorem correct_r16_part112 : ∀ i ∈ List.range 8, CorrectAt 16 (112+i) := by decide +kernel

theorem correct_r16_part120 : ∀ i ∈ List.range 7, CorrectAt 16 (120+i) := by decide +kernel

theorem correct_r16 (V : ℕ) (hV : V ∈ List.range 127) : CorrectAt 16 V := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := correct_r16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r16_part0 : ∀ i ∈ List.range 8, BaseCheckAt 16 (0+i) := by decide +kernel

theorem base_r16_part8 : ∀ i ∈ List.range 8, BaseCheckAt 16 (8+i) := by decide +kernel

theorem base_r16_part16 : ∀ i ∈ List.range 8, BaseCheckAt 16 (16+i) := by decide +kernel

theorem base_r16_part24 : ∀ i ∈ List.range 8, BaseCheckAt 16 (24+i) := by decide +kernel

theorem base_r16_part32 : ∀ i ∈ List.range 8, BaseCheckAt 16 (32+i) := by decide +kernel

theorem base_r16_part40 : ∀ i ∈ List.range 8, BaseCheckAt 16 (40+i) := by decide +kernel

theorem base_r16_part48 : ∀ i ∈ List.range 8, BaseCheckAt 16 (48+i) := by decide +kernel

theorem base_r16_part56 : ∀ i ∈ List.range 8, BaseCheckAt 16 (56+i) := by decide +kernel

theorem base_r16_part64 : ∀ i ∈ List.range 8, BaseCheckAt 16 (64+i) := by decide +kernel

theorem base_r16_part72 : ∀ i ∈ List.range 8, BaseCheckAt 16 (72+i) := by decide +kernel

theorem base_r16_part80 : ∀ i ∈ List.range 8, BaseCheckAt 16 (80+i) := by decide +kernel

theorem base_r16_part88 : ∀ i ∈ List.range 8, BaseCheckAt 16 (88+i) := by decide +kernel

theorem base_r16_part96 : ∀ i ∈ List.range 8, BaseCheckAt 16 (96+i) := by decide +kernel

theorem base_r16_part104 : ∀ i ∈ List.range 8, BaseCheckAt 16 (104+i) := by decide +kernel

theorem base_r16_part112 : ∀ i ∈ List.range 8, BaseCheckAt 16 (112+i) := by decide +kernel

theorem base_r16_part120 : ∀ i ∈ List.range 7, BaseCheckAt 16 (120+i) := by decide +kernel

theorem base_r16 (V : ℕ) (hV : V ∈ List.range 127) : BaseCheckAt 16 V := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := base_r16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r16_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (0+i)) 16 (0+i) := by decide +kernel

theorem valid_r16_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (8+i)) 16 (8+i) := by decide +kernel

theorem valid_r16_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (16+i)) 16 (16+i) := by decide +kernel

theorem valid_r16_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (24+i)) 16 (24+i) := by decide +kernel

theorem valid_r16_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (32+i)) 16 (32+i) := by decide +kernel

theorem valid_r16_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (40+i)) 16 (40+i) := by decide +kernel

theorem valid_r16_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (48+i)) 16 (48+i) := by decide +kernel

theorem valid_r16_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (56+i)) 16 (56+i) := by decide +kernel

theorem valid_r16_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (64+i)) 16 (64+i) := by decide +kernel

theorem valid_r16_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (72+i)) 16 (72+i) := by decide +kernel

theorem valid_r16_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (80+i)) 16 (80+i) := by decide +kernel

theorem valid_r16_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (88+i)) 16 (88+i) := by decide +kernel

theorem valid_r16_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (96+i)) 16 (96+i) := by decide +kernel

theorem valid_r16_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (104+i)) 16 (104+i) := by decide +kernel

theorem valid_r16_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 16 (112+i)) 16 (112+i) := by decide +kernel

theorem valid_r16_part120 : ∀ i ∈ List.range 7, Valid (BoundaryTailBaseFastData.row 16 (120+i)) 16 (120+i) := by decide +kernel

theorem valid_r16 (V : ℕ) (hV : V ∈ List.range 127) : Valid (BoundaryTailBaseFastData.row 16 V) 16 V := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := valid_r16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r16_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (0+i)) 16 (0+i) = true := by decide +kernel

theorem strictBool_r16_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (1+i)) 16 (1+i) = true := by decide +kernel

theorem strictBool_r16_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (2+i)) 16 (2+i) = true := by decide +kernel

theorem strictBool_r16_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (3+i)) 16 (3+i) = true := by decide +kernel

theorem strictBool_r16_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (4+i)) 16 (4+i) = true := by decide +kernel

theorem strictBool_r16_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (5+i)) 16 (5+i) = true := by decide +kernel

theorem strictBool_r16_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (6+i)) 16 (6+i) = true := by decide +kernel

theorem strictBool_r16_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (7+i)) 16 (7+i) = true := by decide +kernel

theorem strictBool_r16_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (8+i)) 16 (8+i) = true := by decide +kernel

theorem strictBool_r16_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (9+i)) 16 (9+i) = true := by decide +kernel

theorem strictBool_r16_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (10+i)) 16 (10+i) = true := by decide +kernel

theorem strictBool_r16_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (11+i)) 16 (11+i) = true := by decide +kernel

theorem strictBool_r16_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (12+i)) 16 (12+i) = true := by decide +kernel

theorem strictBool_r16_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (13+i)) 16 (13+i) = true := by decide +kernel

theorem strictBool_r16_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (14+i)) 16 (14+i) = true := by decide +kernel

theorem strictBool_r16_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (15+i)) 16 (15+i) = true := by decide +kernel

theorem strictBool_r16_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (16+i)) 16 (16+i) = true := by decide +kernel

theorem strictBool_r16_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (17+i)) 16 (17+i) = true := by decide +kernel

theorem strictBool_r16_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (18+i)) 16 (18+i) = true := by decide +kernel

theorem strictBool_r16_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (19+i)) 16 (19+i) = true := by decide +kernel

theorem strictBool_r16_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (20+i)) 16 (20+i) = true := by decide +kernel

theorem strictBool_r16_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (21+i)) 16 (21+i) = true := by decide +kernel

theorem strictBool_r16_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (22+i)) 16 (22+i) = true := by decide +kernel

theorem strictBool_r16_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (23+i)) 16 (23+i) = true := by decide +kernel

theorem strictBool_r16_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (24+i)) 16 (24+i) = true := by decide +kernel

theorem strictBool_r16_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (25+i)) 16 (25+i) = true := by decide +kernel

theorem strictBool_r16_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (26+i)) 16 (26+i) = true := by decide +kernel

theorem strictBool_r16_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (27+i)) 16 (27+i) = true := by decide +kernel

theorem strictBool_r16_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (28+i)) 16 (28+i) = true := by decide +kernel

theorem strictBool_r16_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (29+i)) 16 (29+i) = true := by decide +kernel

theorem strictBool_r16_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (30+i)) 16 (30+i) = true := by decide +kernel

theorem strictBool_r16_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (31+i)) 16 (31+i) = true := by decide +kernel

theorem strictBool_r16_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (32+i)) 16 (32+i) = true := by decide +kernel

theorem strictBool_r16_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (33+i)) 16 (33+i) = true := by decide +kernel

theorem strictBool_r16_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (34+i)) 16 (34+i) = true := by decide +kernel

theorem strictBool_r16_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (35+i)) 16 (35+i) = true := by decide +kernel

theorem strictBool_r16_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (36+i)) 16 (36+i) = true := by decide +kernel

theorem strictBool_r16_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (37+i)) 16 (37+i) = true := by decide +kernel

theorem strictBool_r16_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (38+i)) 16 (38+i) = true := by decide +kernel

theorem strictBool_r16_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (39+i)) 16 (39+i) = true := by decide +kernel

theorem strictBool_r16_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (40+i)) 16 (40+i) = true := by decide +kernel

theorem strictBool_r16_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (41+i)) 16 (41+i) = true := by decide +kernel

theorem strictBool_r16_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (42+i)) 16 (42+i) = true := by decide +kernel

theorem strictBool_r16_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (43+i)) 16 (43+i) = true := by decide +kernel

theorem strictBool_r16_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (44+i)) 16 (44+i) = true := by decide +kernel

theorem strictBool_r16_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (45+i)) 16 (45+i) = true := by decide +kernel

theorem strictBool_r16_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (46+i)) 16 (46+i) = true := by decide +kernel

theorem strictBool_r16_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (47+i)) 16 (47+i) = true := by decide +kernel

theorem strictBool_r16_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (48+i)) 16 (48+i) = true := by decide +kernel

theorem strictBool_r16_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (49+i)) 16 (49+i) = true := by decide +kernel

theorem strictBool_r16_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (50+i)) 16 (50+i) = true := by decide +kernel

theorem strictBool_r16_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (51+i)) 16 (51+i) = true := by decide +kernel

theorem strictBool_r16_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (52+i)) 16 (52+i) = true := by decide +kernel

theorem strictBool_r16_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (53+i)) 16 (53+i) = true := by decide +kernel

theorem strictBool_r16_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (54+i)) 16 (54+i) = true := by decide +kernel

theorem strictBool_r16_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (55+i)) 16 (55+i) = true := by decide +kernel

theorem strictBool_r16_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (56+i)) 16 (56+i) = true := by decide +kernel

theorem strictBool_r16_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (57+i)) 16 (57+i) = true := by decide +kernel

theorem strictBool_r16_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (58+i)) 16 (58+i) = true := by decide +kernel

theorem strictBool_r16_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (59+i)) 16 (59+i) = true := by decide +kernel

theorem strictBool_r16_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (60+i)) 16 (60+i) = true := by decide +kernel

theorem strictBool_r16_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (61+i)) 16 (61+i) = true := by decide +kernel

theorem strictBool_r16_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (62+i)) 16 (62+i) = true := by decide +kernel

theorem strictBool_r16_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (63+i)) 16 (63+i) = true := by decide +kernel

theorem strictBool_r16_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (64+i)) 16 (64+i) = true := by decide +kernel

theorem strictBool_r16_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (65+i)) 16 (65+i) = true := by decide +kernel

theorem strictBool_r16_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (66+i)) 16 (66+i) = true := by decide +kernel

theorem strictBool_r16_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (67+i)) 16 (67+i) = true := by decide +kernel

theorem strictBool_r16_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (68+i)) 16 (68+i) = true := by decide +kernel

theorem strictBool_r16_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (69+i)) 16 (69+i) = true := by decide +kernel

theorem strictBool_r16_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (70+i)) 16 (70+i) = true := by decide +kernel

theorem strictBool_r16_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (71+i)) 16 (71+i) = true := by decide +kernel

theorem strictBool_r16_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (72+i)) 16 (72+i) = true := by decide +kernel

theorem strictBool_r16_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (73+i)) 16 (73+i) = true := by decide +kernel

theorem strictBool_r16_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (74+i)) 16 (74+i) = true := by decide +kernel

theorem strictBool_r16_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (75+i)) 16 (75+i) = true := by decide +kernel

theorem strictBool_r16_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (76+i)) 16 (76+i) = true := by decide +kernel

theorem strictBool_r16_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (77+i)) 16 (77+i) = true := by decide +kernel

theorem strictBool_r16_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (78+i)) 16 (78+i) = true := by decide +kernel

theorem strictBool_r16_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (79+i)) 16 (79+i) = true := by decide +kernel

theorem strictBool_r16_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (80+i)) 16 (80+i) = true := by decide +kernel

theorem strictBool_r16_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (81+i)) 16 (81+i) = true := by decide +kernel

theorem strictBool_r16_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (82+i)) 16 (82+i) = true := by decide +kernel

theorem strictBool_r16_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (83+i)) 16 (83+i) = true := by decide +kernel

theorem strictBool_r16_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (84+i)) 16 (84+i) = true := by decide +kernel

theorem strictBool_r16_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (85+i)) 16 (85+i) = true := by decide +kernel

theorem strictBool_r16_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (86+i)) 16 (86+i) = true := by decide +kernel

theorem strictBool_r16_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (87+i)) 16 (87+i) = true := by decide +kernel

theorem strictBool_r16_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (88+i)) 16 (88+i) = true := by decide +kernel

theorem strictBool_r16_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (89+i)) 16 (89+i) = true := by decide +kernel

theorem strictBool_r16_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (90+i)) 16 (90+i) = true := by decide +kernel

theorem strictBool_r16_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (91+i)) 16 (91+i) = true := by decide +kernel

theorem strictBool_r16_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (92+i)) 16 (92+i) = true := by decide +kernel

theorem strictBool_r16_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (93+i)) 16 (93+i) = true := by decide +kernel

theorem strictBool_r16_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (94+i)) 16 (94+i) = true := by decide +kernel

theorem strictBool_r16_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (95+i)) 16 (95+i) = true := by decide +kernel

theorem strictBool_r16_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (96+i)) 16 (96+i) = true := by decide +kernel

theorem strictBool_r16_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (97+i)) 16 (97+i) = true := by decide +kernel

theorem strictBool_r16_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (98+i)) 16 (98+i) = true := by decide +kernel

theorem strictBool_r16_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (99+i)) 16 (99+i) = true := by decide +kernel

theorem strictBool_r16_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (100+i)) 16 (100+i) = true := by decide +kernel

theorem strictBool_r16_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (101+i)) 16 (101+i) = true := by decide +kernel

theorem strictBool_r16_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (102+i)) 16 (102+i) = true := by decide +kernel

theorem strictBool_r16_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (103+i)) 16 (103+i) = true := by decide +kernel

theorem strictBool_r16_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (104+i)) 16 (104+i) = true := by decide +kernel

theorem strictBool_r16_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (105+i)) 16 (105+i) = true := by decide +kernel

theorem strictBool_r16_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (106+i)) 16 (106+i) = true := by decide +kernel

theorem strictBool_r16_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (107+i)) 16 (107+i) = true := by decide +kernel

theorem strictBool_r16_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (108+i)) 16 (108+i) = true := by decide +kernel

theorem strictBool_r16_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (109+i)) 16 (109+i) = true := by decide +kernel

theorem strictBool_r16_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (110+i)) 16 (110+i) = true := by decide +kernel

theorem strictBool_r16_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (111+i)) 16 (111+i) = true := by decide +kernel

theorem strictBool_r16_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (112+i)) 16 (112+i) = true := by decide +kernel

theorem strictBool_r16_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (113+i)) 16 (113+i) = true := by decide +kernel

theorem strictBool_r16_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (114+i)) 16 (114+i) = true := by decide +kernel

theorem strictBool_r16_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (115+i)) 16 (115+i) = true := by decide +kernel

theorem strictBool_r16_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (116+i)) 16 (116+i) = true := by decide +kernel

theorem strictBool_r16_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (117+i)) 16 (117+i) = true := by decide +kernel

theorem strictBool_r16_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (118+i)) 16 (118+i) = true := by decide +kernel

theorem strictBool_r16_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (119+i)) 16 (119+i) = true := by decide +kernel

theorem strictBool_r16_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (120+i)) 16 (120+i) = true := by decide +kernel

theorem strictBool_r16_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (121+i)) 16 (121+i) = true := by decide +kernel

theorem strictBool_r16_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (122+i)) 16 (122+i) = true := by decide +kernel

theorem strictBool_r16_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (123+i)) 16 (123+i) = true := by decide +kernel

theorem strictBool_r16_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (124+i)) 16 (124+i) = true := by decide +kernel

theorem strictBool_r16_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (125+i)) 16 (125+i) = true := by decide +kernel

theorem strictBool_r16_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 16 (126+i)) 16 (126+i) = true := by decide +kernel

theorem strictBool_r16 (V : ℕ) (hV : V ∈ List.range 127) : strictBool (BoundaryTailBaseFastData.row 16 V) 16 V = true := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 63
  · by_cases h0_63 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r16_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r16_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r16_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r16_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r16_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r16_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r16_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r16_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r16_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r16_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r16_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r16_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r16_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r16_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r16_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r16_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
    · by_cases h31_63 : V < 47
      · by_cases h31_47 : V < 39
        · by_cases h31_39 : V < 35
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r16_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r16_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r16_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r16_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
        · by_cases h39_47 : V < 43
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r16_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r16_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r16_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r16_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
      · by_cases h47_63 : V < 55
        · by_cases h47_55 : V < 51
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r16_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r16_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r16_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r16_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
        · by_cases h55_63 : V < 59
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r16_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r16_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r16_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r16_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
  · by_cases h63_127 : V < 95
    · by_cases h63_95 : V < 79
      · by_cases h63_79 : V < 71
        · by_cases h63_71 : V < 67
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r16_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r16_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r16_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r16_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
        · by_cases h71_79 : V < 75
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r16_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r16_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r16_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r16_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
      · by_cases h79_95 : V < 87
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r16_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r16_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r16_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r16_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
        · by_cases h87_95 : V < 91
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r16_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r16_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r16_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r16_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
    · by_cases h95_127 : V < 111
      · by_cases h95_111 : V < 103
        · by_cases h95_103 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r16_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r16_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r16_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r16_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
        · by_cases h103_111 : V < 107
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r16_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r16_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r16_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r16_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
      · by_cases h111_127 : V < 119
        · by_cases h111_119 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r16_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r16_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r16_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r16_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r16_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r16_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r16_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r16_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r16_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi

theorem strictFast_r16 (V : ℕ) (hV : V ∈ List.range 127) : StrictAtFast (BoundaryTailBaseFastData.row 16 V) 16 V :=
  strictBool_sound _ _ _ (strictBool_r16 V hV)

theorem strict_r16 (V : ℕ) (hV : V ∈ List.range 127) : StrictCheckAt 16 V :=
  strictAtFast_sound _ _ _ (valid_r16 V hV) (strictFast_r16 V hV)

theorem zeroCertificate_r16_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (0+i)) 16 (0+i) := by decide +kernel

theorem zeroCertificate_r16_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (8+i)) 16 (8+i) := by decide +kernel

theorem zeroCertificate_r16_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (16+i)) 16 (16+i) := by decide +kernel

theorem zeroCertificate_r16_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (24+i)) 16 (24+i) := by decide +kernel

theorem zeroCertificate_r16_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (32+i)) 16 (32+i) := by decide +kernel

theorem zeroCertificate_r16_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (40+i)) 16 (40+i) := by decide +kernel

theorem zeroCertificate_r16_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (48+i)) 16 (48+i) := by decide +kernel

theorem zeroCertificate_r16_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (56+i)) 16 (56+i) := by decide +kernel

theorem zeroCertificate_r16_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (64+i)) 16 (64+i) := by decide +kernel

theorem zeroCertificate_r16_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (72+i)) 16 (72+i) := by decide +kernel

theorem zeroCertificate_r16_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (80+i)) 16 (80+i) := by decide +kernel

theorem zeroCertificate_r16_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (88+i)) 16 (88+i) := by decide +kernel

theorem zeroCertificate_r16_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (96+i)) 16 (96+i) := by decide +kernel

theorem zeroCertificate_r16_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (104+i)) 16 (104+i) := by decide +kernel

theorem zeroCertificate_r16_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 16 (112+i)) 16 (112+i) := by decide +kernel

theorem zeroCertificate_r16_part120 : ∀ i ∈ List.range 7, ZeroCertificate (BoundaryTailBaseFastData.row 16 (120+i)) 16 (120+i) := by decide +kernel

theorem zeroCertificate_r16 (V : ℕ) (hV : V ∈ List.range 127) : ZeroCertificate (BoundaryTailBaseFastData.row 16 V) 16 V := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := zeroCertificate_r16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r16 (V : ℕ) (hV : V ∈ List.range 127) : ZeroAtFast 16 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r16 V hV) (zeroCertificate_r16 V hV)

theorem zero_r16 (V : ℕ) (hV : V ∈ List.range 127) : ZeroCheckAt 16 V :=
  zeroAtFast_sound _ _ (zeroFast_r16 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r20_part0 : ∀ i ∈ List.range 8, CorrectAt 20 (0+i) := by decide +kernel

theorem correct_r20_part8 : ∀ i ∈ List.range 8, CorrectAt 20 (8+i) := by decide +kernel

theorem correct_r20_part16 : ∀ i ∈ List.range 8, CorrectAt 20 (16+i) := by decide +kernel

theorem correct_r20_part24 : ∀ i ∈ List.range 8, CorrectAt 20 (24+i) := by decide +kernel

theorem correct_r20_part32 : ∀ i ∈ List.range 8, CorrectAt 20 (32+i) := by decide +kernel

theorem correct_r20_part40 : ∀ i ∈ List.range 8, CorrectAt 20 (40+i) := by decide +kernel

theorem correct_r20_part48 : ∀ i ∈ List.range 8, CorrectAt 20 (48+i) := by decide +kernel

theorem correct_r20_part56 : ∀ i ∈ List.range 8, CorrectAt 20 (56+i) := by decide +kernel

theorem correct_r20_part64 : ∀ i ∈ List.range 8, CorrectAt 20 (64+i) := by decide +kernel

theorem correct_r20_part72 : ∀ i ∈ List.range 8, CorrectAt 20 (72+i) := by decide +kernel

theorem correct_r20_part80 : ∀ i ∈ List.range 8, CorrectAt 20 (80+i) := by decide +kernel

theorem correct_r20_part88 : ∀ i ∈ List.range 8, CorrectAt 20 (88+i) := by decide +kernel

theorem correct_r20_part96 : ∀ i ∈ List.range 8, CorrectAt 20 (96+i) := by decide +kernel

theorem correct_r20_part104 : ∀ i ∈ List.range 8, CorrectAt 20 (104+i) := by decide +kernel

theorem correct_r20_part112 : ∀ i ∈ List.range 8, CorrectAt 20 (112+i) := by decide +kernel

theorem correct_r20_part120 : ∀ i ∈ List.range 3, CorrectAt 20 (120+i) := by decide +kernel

theorem correct_r20 (V : ℕ) (hV : V ∈ List.range 123) : CorrectAt 20 V := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := correct_r20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r20_part0 : ∀ i ∈ List.range 8, BaseCheckAt 20 (0+i) := by decide +kernel

theorem base_r20_part8 : ∀ i ∈ List.range 8, BaseCheckAt 20 (8+i) := by decide +kernel

theorem base_r20_part16 : ∀ i ∈ List.range 8, BaseCheckAt 20 (16+i) := by decide +kernel

theorem base_r20_part24 : ∀ i ∈ List.range 8, BaseCheckAt 20 (24+i) := by decide +kernel

theorem base_r20_part32 : ∀ i ∈ List.range 8, BaseCheckAt 20 (32+i) := by decide +kernel

theorem base_r20_part40 : ∀ i ∈ List.range 8, BaseCheckAt 20 (40+i) := by decide +kernel

theorem base_r20_part48 : ∀ i ∈ List.range 8, BaseCheckAt 20 (48+i) := by decide +kernel

theorem base_r20_part56 : ∀ i ∈ List.range 8, BaseCheckAt 20 (56+i) := by decide +kernel

theorem base_r20_part64 : ∀ i ∈ List.range 8, BaseCheckAt 20 (64+i) := by decide +kernel

theorem base_r20_part72 : ∀ i ∈ List.range 8, BaseCheckAt 20 (72+i) := by decide +kernel

theorem base_r20_part80 : ∀ i ∈ List.range 8, BaseCheckAt 20 (80+i) := by decide +kernel

theorem base_r20_part88 : ∀ i ∈ List.range 8, BaseCheckAt 20 (88+i) := by decide +kernel

theorem base_r20_part96 : ∀ i ∈ List.range 8, BaseCheckAt 20 (96+i) := by decide +kernel

theorem base_r20_part104 : ∀ i ∈ List.range 8, BaseCheckAt 20 (104+i) := by decide +kernel

theorem base_r20_part112 : ∀ i ∈ List.range 8, BaseCheckAt 20 (112+i) := by decide +kernel

theorem base_r20_part120 : ∀ i ∈ List.range 3, BaseCheckAt 20 (120+i) := by decide +kernel

theorem base_r20 (V : ℕ) (hV : V ∈ List.range 123) : BaseCheckAt 20 V := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := base_r20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r20_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (0+i)) 20 (0+i) := by decide +kernel

theorem valid_r20_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (8+i)) 20 (8+i) := by decide +kernel

theorem valid_r20_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (16+i)) 20 (16+i) := by decide +kernel

theorem valid_r20_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (24+i)) 20 (24+i) := by decide +kernel

theorem valid_r20_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (32+i)) 20 (32+i) := by decide +kernel

theorem valid_r20_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (40+i)) 20 (40+i) := by decide +kernel

theorem valid_r20_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (48+i)) 20 (48+i) := by decide +kernel

theorem valid_r20_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (56+i)) 20 (56+i) := by decide +kernel

theorem valid_r20_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (64+i)) 20 (64+i) := by decide +kernel

theorem valid_r20_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (72+i)) 20 (72+i) := by decide +kernel

theorem valid_r20_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (80+i)) 20 (80+i) := by decide +kernel

theorem valid_r20_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (88+i)) 20 (88+i) := by decide +kernel

theorem valid_r20_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (96+i)) 20 (96+i) := by decide +kernel

theorem valid_r20_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (104+i)) 20 (104+i) := by decide +kernel

theorem valid_r20_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 20 (112+i)) 20 (112+i) := by decide +kernel

theorem valid_r20_part120 : ∀ i ∈ List.range 3, Valid (BoundaryTailBaseFastData.row 20 (120+i)) 20 (120+i) := by decide +kernel

theorem valid_r20 (V : ℕ) (hV : V ∈ List.range 123) : Valid (BoundaryTailBaseFastData.row 20 V) 20 V := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := valid_r20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r20_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (0+i)) 20 (0+i) = true := by decide +kernel

theorem strictBool_r20_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (1+i)) 20 (1+i) = true := by decide +kernel

theorem strictBool_r20_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (2+i)) 20 (2+i) = true := by decide +kernel

theorem strictBool_r20_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (3+i)) 20 (3+i) = true := by decide +kernel

theorem strictBool_r20_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (4+i)) 20 (4+i) = true := by decide +kernel

theorem strictBool_r20_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (5+i)) 20 (5+i) = true := by decide +kernel

theorem strictBool_r20_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (6+i)) 20 (6+i) = true := by decide +kernel

theorem strictBool_r20_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (7+i)) 20 (7+i) = true := by decide +kernel

theorem strictBool_r20_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (8+i)) 20 (8+i) = true := by decide +kernel

theorem strictBool_r20_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (9+i)) 20 (9+i) = true := by decide +kernel

theorem strictBool_r20_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (10+i)) 20 (10+i) = true := by decide +kernel

theorem strictBool_r20_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (11+i)) 20 (11+i) = true := by decide +kernel

theorem strictBool_r20_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (12+i)) 20 (12+i) = true := by decide +kernel

theorem strictBool_r20_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (13+i)) 20 (13+i) = true := by decide +kernel

theorem strictBool_r20_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (14+i)) 20 (14+i) = true := by decide +kernel

theorem strictBool_r20_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (15+i)) 20 (15+i) = true := by decide +kernel

theorem strictBool_r20_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (16+i)) 20 (16+i) = true := by decide +kernel

theorem strictBool_r20_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (17+i)) 20 (17+i) = true := by decide +kernel

theorem strictBool_r20_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (18+i)) 20 (18+i) = true := by decide +kernel

theorem strictBool_r20_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (19+i)) 20 (19+i) = true := by decide +kernel

theorem strictBool_r20_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (20+i)) 20 (20+i) = true := by decide +kernel

theorem strictBool_r20_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (21+i)) 20 (21+i) = true := by decide +kernel

theorem strictBool_r20_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (22+i)) 20 (22+i) = true := by decide +kernel

theorem strictBool_r20_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (23+i)) 20 (23+i) = true := by decide +kernel

theorem strictBool_r20_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (24+i)) 20 (24+i) = true := by decide +kernel

theorem strictBool_r20_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (25+i)) 20 (25+i) = true := by decide +kernel

theorem strictBool_r20_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (26+i)) 20 (26+i) = true := by decide +kernel

theorem strictBool_r20_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (27+i)) 20 (27+i) = true := by decide +kernel

theorem strictBool_r20_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (28+i)) 20 (28+i) = true := by decide +kernel

theorem strictBool_r20_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (29+i)) 20 (29+i) = true := by decide +kernel

theorem strictBool_r20_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (30+i)) 20 (30+i) = true := by decide +kernel

theorem strictBool_r20_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (31+i)) 20 (31+i) = true := by decide +kernel

theorem strictBool_r20_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (32+i)) 20 (32+i) = true := by decide +kernel

theorem strictBool_r20_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (33+i)) 20 (33+i) = true := by decide +kernel

theorem strictBool_r20_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (34+i)) 20 (34+i) = true := by decide +kernel

theorem strictBool_r20_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (35+i)) 20 (35+i) = true := by decide +kernel

theorem strictBool_r20_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (36+i)) 20 (36+i) = true := by decide +kernel

theorem strictBool_r20_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (37+i)) 20 (37+i) = true := by decide +kernel

theorem strictBool_r20_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (38+i)) 20 (38+i) = true := by decide +kernel

theorem strictBool_r20_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (39+i)) 20 (39+i) = true := by decide +kernel

theorem strictBool_r20_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (40+i)) 20 (40+i) = true := by decide +kernel

theorem strictBool_r20_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (41+i)) 20 (41+i) = true := by decide +kernel

theorem strictBool_r20_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (42+i)) 20 (42+i) = true := by decide +kernel

theorem strictBool_r20_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (43+i)) 20 (43+i) = true := by decide +kernel

theorem strictBool_r20_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (44+i)) 20 (44+i) = true := by decide +kernel

theorem strictBool_r20_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (45+i)) 20 (45+i) = true := by decide +kernel

theorem strictBool_r20_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (46+i)) 20 (46+i) = true := by decide +kernel

theorem strictBool_r20_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (47+i)) 20 (47+i) = true := by decide +kernel

theorem strictBool_r20_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (48+i)) 20 (48+i) = true := by decide +kernel

theorem strictBool_r20_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (49+i)) 20 (49+i) = true := by decide +kernel

theorem strictBool_r20_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (50+i)) 20 (50+i) = true := by decide +kernel

theorem strictBool_r20_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (51+i)) 20 (51+i) = true := by decide +kernel

theorem strictBool_r20_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (52+i)) 20 (52+i) = true := by decide +kernel

theorem strictBool_r20_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (53+i)) 20 (53+i) = true := by decide +kernel

theorem strictBool_r20_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (54+i)) 20 (54+i) = true := by decide +kernel

theorem strictBool_r20_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (55+i)) 20 (55+i) = true := by decide +kernel

theorem strictBool_r20_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (56+i)) 20 (56+i) = true := by decide +kernel

theorem strictBool_r20_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (57+i)) 20 (57+i) = true := by decide +kernel

theorem strictBool_r20_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (58+i)) 20 (58+i) = true := by decide +kernel

theorem strictBool_r20_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (59+i)) 20 (59+i) = true := by decide +kernel

theorem strictBool_r20_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (60+i)) 20 (60+i) = true := by decide +kernel

theorem strictBool_r20_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (61+i)) 20 (61+i) = true := by decide +kernel

theorem strictBool_r20_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (62+i)) 20 (62+i) = true := by decide +kernel

theorem strictBool_r20_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (63+i)) 20 (63+i) = true := by decide +kernel

theorem strictBool_r20_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (64+i)) 20 (64+i) = true := by decide +kernel

theorem strictBool_r20_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (65+i)) 20 (65+i) = true := by decide +kernel

theorem strictBool_r20_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (66+i)) 20 (66+i) = true := by decide +kernel

theorem strictBool_r20_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (67+i)) 20 (67+i) = true := by decide +kernel

theorem strictBool_r20_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (68+i)) 20 (68+i) = true := by decide +kernel

theorem strictBool_r20_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (69+i)) 20 (69+i) = true := by decide +kernel

theorem strictBool_r20_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (70+i)) 20 (70+i) = true := by decide +kernel

theorem strictBool_r20_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (71+i)) 20 (71+i) = true := by decide +kernel

theorem strictBool_r20_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (72+i)) 20 (72+i) = true := by decide +kernel

theorem strictBool_r20_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (73+i)) 20 (73+i) = true := by decide +kernel

theorem strictBool_r20_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (74+i)) 20 (74+i) = true := by decide +kernel

theorem strictBool_r20_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (75+i)) 20 (75+i) = true := by decide +kernel

theorem strictBool_r20_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (76+i)) 20 (76+i) = true := by decide +kernel

theorem strictBool_r20_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (77+i)) 20 (77+i) = true := by decide +kernel

theorem strictBool_r20_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (78+i)) 20 (78+i) = true := by decide +kernel

theorem strictBool_r20_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (79+i)) 20 (79+i) = true := by decide +kernel

theorem strictBool_r20_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (80+i)) 20 (80+i) = true := by decide +kernel

theorem strictBool_r20_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (81+i)) 20 (81+i) = true := by decide +kernel

theorem strictBool_r20_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (82+i)) 20 (82+i) = true := by decide +kernel

theorem strictBool_r20_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (83+i)) 20 (83+i) = true := by decide +kernel

theorem strictBool_r20_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (84+i)) 20 (84+i) = true := by decide +kernel

theorem strictBool_r20_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (85+i)) 20 (85+i) = true := by decide +kernel

theorem strictBool_r20_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (86+i)) 20 (86+i) = true := by decide +kernel

theorem strictBool_r20_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (87+i)) 20 (87+i) = true := by decide +kernel

theorem strictBool_r20_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (88+i)) 20 (88+i) = true := by decide +kernel

theorem strictBool_r20_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (89+i)) 20 (89+i) = true := by decide +kernel

theorem strictBool_r20_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (90+i)) 20 (90+i) = true := by decide +kernel

theorem strictBool_r20_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (91+i)) 20 (91+i) = true := by decide +kernel

theorem strictBool_r20_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (92+i)) 20 (92+i) = true := by decide +kernel

theorem strictBool_r20_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (93+i)) 20 (93+i) = true := by decide +kernel

theorem strictBool_r20_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (94+i)) 20 (94+i) = true := by decide +kernel

theorem strictBool_r20_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (95+i)) 20 (95+i) = true := by decide +kernel

theorem strictBool_r20_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (96+i)) 20 (96+i) = true := by decide +kernel

theorem strictBool_r20_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (97+i)) 20 (97+i) = true := by decide +kernel

theorem strictBool_r20_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (98+i)) 20 (98+i) = true := by decide +kernel

theorem strictBool_r20_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (99+i)) 20 (99+i) = true := by decide +kernel

theorem strictBool_r20_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (100+i)) 20 (100+i) = true := by decide +kernel

theorem strictBool_r20_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (101+i)) 20 (101+i) = true := by decide +kernel

theorem strictBool_r20_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (102+i)) 20 (102+i) = true := by decide +kernel

theorem strictBool_r20_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (103+i)) 20 (103+i) = true := by decide +kernel

theorem strictBool_r20_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (104+i)) 20 (104+i) = true := by decide +kernel

theorem strictBool_r20_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (105+i)) 20 (105+i) = true := by decide +kernel

theorem strictBool_r20_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (106+i)) 20 (106+i) = true := by decide +kernel

theorem strictBool_r20_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (107+i)) 20 (107+i) = true := by decide +kernel

theorem strictBool_r20_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (108+i)) 20 (108+i) = true := by decide +kernel

theorem strictBool_r20_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (109+i)) 20 (109+i) = true := by decide +kernel

theorem strictBool_r20_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (110+i)) 20 (110+i) = true := by decide +kernel

theorem strictBool_r20_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (111+i)) 20 (111+i) = true := by decide +kernel

theorem strictBool_r20_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (112+i)) 20 (112+i) = true := by decide +kernel

theorem strictBool_r20_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (113+i)) 20 (113+i) = true := by decide +kernel

theorem strictBool_r20_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (114+i)) 20 (114+i) = true := by decide +kernel

theorem strictBool_r20_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (115+i)) 20 (115+i) = true := by decide +kernel

theorem strictBool_r20_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (116+i)) 20 (116+i) = true := by decide +kernel

theorem strictBool_r20_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (117+i)) 20 (117+i) = true := by decide +kernel

theorem strictBool_r20_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (118+i)) 20 (118+i) = true := by decide +kernel

theorem strictBool_r20_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (119+i)) 20 (119+i) = true := by decide +kernel

theorem strictBool_r20_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (120+i)) 20 (120+i) = true := by decide +kernel

theorem strictBool_r20_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (121+i)) 20 (121+i) = true := by decide +kernel

theorem strictBool_r20_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 20 (122+i)) 20 (122+i) = true := by decide +kernel

theorem strictBool_r20 (V : ℕ) (hV : V ∈ List.range 123) : strictBool (BoundaryTailBaseFastData.row 20 V) 20 V = true := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 61
  · by_cases h0_61 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r20_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r20_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r20_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r20_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r20_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r20_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r20_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r20_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have hi := strictBool_r20_part15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r20_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r20_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r20_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r20_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r20_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r20_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r20_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
    · by_cases h30_61 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have hi := strictBool_r20_part30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r20_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r20_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r20_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r20_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r20_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r20_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r20_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h45_61 : V < 53
        · by_cases h45_53 : V < 49
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r20_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r20_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r20_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r20_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h53_61 : V < 57
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r20_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r20_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r20_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r20_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
  · by_cases h61_123 : V < 92
    · by_cases h61_92 : V < 76
      · by_cases h61_76 : V < 68
        · by_cases h61_68 : V < 64
          · by_cases h61_64 : V < 62
            · have hi := strictBool_r20_part61 (V-61) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r20_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r20_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r20_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r20_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r20_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r20_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r20_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
      · by_cases h76_92 : V < 84
        · by_cases h76_84 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r20_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r20_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r20_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r20_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r20_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r20_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r20_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r20_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
    · by_cases h92_123 : V < 107
      · by_cases h92_107 : V < 99
        · by_cases h92_99 : V < 95
          · by_cases h92_95 : V < 93
            · have hi := strictBool_r20_part92 (V-92) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r20_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r20_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r20_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r20_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r20_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r20_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r20_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
      · by_cases h107_123 : V < 115
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r20_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r20_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r20_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r20_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
        · by_cases h115_123 : V < 119
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r20_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r20_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r20_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r20_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r20_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi

theorem strictFast_r20 (V : ℕ) (hV : V ∈ List.range 123) : StrictAtFast (BoundaryTailBaseFastData.row 20 V) 20 V :=
  strictBool_sound _ _ _ (strictBool_r20 V hV)

theorem strict_r20 (V : ℕ) (hV : V ∈ List.range 123) : StrictCheckAt 20 V :=
  strictAtFast_sound _ _ _ (valid_r20 V hV) (strictFast_r20 V hV)

theorem zeroCertificate_r20_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (0+i)) 20 (0+i) := by decide +kernel

theorem zeroCertificate_r20_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (8+i)) 20 (8+i) := by decide +kernel

theorem zeroCertificate_r20_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (16+i)) 20 (16+i) := by decide +kernel

theorem zeroCertificate_r20_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (24+i)) 20 (24+i) := by decide +kernel

theorem zeroCertificate_r20_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (32+i)) 20 (32+i) := by decide +kernel

theorem zeroCertificate_r20_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (40+i)) 20 (40+i) := by decide +kernel

theorem zeroCertificate_r20_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (48+i)) 20 (48+i) := by decide +kernel

theorem zeroCertificate_r20_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (56+i)) 20 (56+i) := by decide +kernel

theorem zeroCertificate_r20_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (64+i)) 20 (64+i) := by decide +kernel

theorem zeroCertificate_r20_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (72+i)) 20 (72+i) := by decide +kernel

theorem zeroCertificate_r20_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (80+i)) 20 (80+i) := by decide +kernel

theorem zeroCertificate_r20_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (88+i)) 20 (88+i) := by decide +kernel

theorem zeroCertificate_r20_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (96+i)) 20 (96+i) := by decide +kernel

theorem zeroCertificate_r20_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (104+i)) 20 (104+i) := by decide +kernel

theorem zeroCertificate_r20_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 20 (112+i)) 20 (112+i) := by decide +kernel

theorem zeroCertificate_r20_part120 : ∀ i ∈ List.range 3, ZeroCertificate (BoundaryTailBaseFastData.row 20 (120+i)) 20 (120+i) := by decide +kernel

theorem zeroCertificate_r20 (V : ℕ) (hV : V ∈ List.range 123) : ZeroCertificate (BoundaryTailBaseFastData.row 20 V) 20 V := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := zeroCertificate_r20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r20 (V : ℕ) (hV : V ∈ List.range 123) : ZeroAtFast 20 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r20 V hV) (zeroCertificate_r20 V hV)

theorem zero_r20 (V : ℕ) (hV : V ∈ List.range 123) : ZeroCheckAt 20 V :=
  zeroAtFast_sound _ _ (zeroFast_r20 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r24_part0 : ∀ i ∈ List.range 8, CorrectAt 24 (0+i) := by decide +kernel

theorem correct_r24_part8 : ∀ i ∈ List.range 8, CorrectAt 24 (8+i) := by decide +kernel

theorem correct_r24_part16 : ∀ i ∈ List.range 8, CorrectAt 24 (16+i) := by decide +kernel

theorem correct_r24_part24 : ∀ i ∈ List.range 8, CorrectAt 24 (24+i) := by decide +kernel

theorem correct_r24_part32 : ∀ i ∈ List.range 8, CorrectAt 24 (32+i) := by decide +kernel

theorem correct_r24_part40 : ∀ i ∈ List.range 8, CorrectAt 24 (40+i) := by decide +kernel

theorem correct_r24_part48 : ∀ i ∈ List.range 8, CorrectAt 24 (48+i) := by decide +kernel

theorem correct_r24_part56 : ∀ i ∈ List.range 8, CorrectAt 24 (56+i) := by decide +kernel

theorem correct_r24_part64 : ∀ i ∈ List.range 8, CorrectAt 24 (64+i) := by decide +kernel

theorem correct_r24_part72 : ∀ i ∈ List.range 8, CorrectAt 24 (72+i) := by decide +kernel

theorem correct_r24_part80 : ∀ i ∈ List.range 8, CorrectAt 24 (80+i) := by decide +kernel

theorem correct_r24_part88 : ∀ i ∈ List.range 8, CorrectAt 24 (88+i) := by decide +kernel

theorem correct_r24_part96 : ∀ i ∈ List.range 8, CorrectAt 24 (96+i) := by decide +kernel

theorem correct_r24_part104 : ∀ i ∈ List.range 8, CorrectAt 24 (104+i) := by decide +kernel

theorem correct_r24_part112 : ∀ i ∈ List.range 7, CorrectAt 24 (112+i) := by decide +kernel

theorem correct_r24 (V : ℕ) (hV : V ∈ List.range 119) : CorrectAt 24 V := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := correct_r24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r24_part0 : ∀ i ∈ List.range 8, BaseCheckAt 24 (0+i) := by decide +kernel

theorem base_r24_part8 : ∀ i ∈ List.range 8, BaseCheckAt 24 (8+i) := by decide +kernel

theorem base_r24_part16 : ∀ i ∈ List.range 8, BaseCheckAt 24 (16+i) := by decide +kernel

theorem base_r24_part24 : ∀ i ∈ List.range 8, BaseCheckAt 24 (24+i) := by decide +kernel

theorem base_r24_part32 : ∀ i ∈ List.range 8, BaseCheckAt 24 (32+i) := by decide +kernel

theorem base_r24_part40 : ∀ i ∈ List.range 8, BaseCheckAt 24 (40+i) := by decide +kernel

theorem base_r24_part48 : ∀ i ∈ List.range 8, BaseCheckAt 24 (48+i) := by decide +kernel

theorem base_r24_part56 : ∀ i ∈ List.range 8, BaseCheckAt 24 (56+i) := by decide +kernel

theorem base_r24_part64 : ∀ i ∈ List.range 8, BaseCheckAt 24 (64+i) := by decide +kernel

theorem base_r24_part72 : ∀ i ∈ List.range 8, BaseCheckAt 24 (72+i) := by decide +kernel

theorem base_r24_part80 : ∀ i ∈ List.range 8, BaseCheckAt 24 (80+i) := by decide +kernel

theorem base_r24_part88 : ∀ i ∈ List.range 8, BaseCheckAt 24 (88+i) := by decide +kernel

theorem base_r24_part96 : ∀ i ∈ List.range 8, BaseCheckAt 24 (96+i) := by decide +kernel

theorem base_r24_part104 : ∀ i ∈ List.range 8, BaseCheckAt 24 (104+i) := by decide +kernel

theorem base_r24_part112 : ∀ i ∈ List.range 7, BaseCheckAt 24 (112+i) := by decide +kernel

theorem base_r24 (V : ℕ) (hV : V ∈ List.range 119) : BaseCheckAt 24 V := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := base_r24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r24_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (0+i)) 24 (0+i) := by decide +kernel

theorem valid_r24_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (8+i)) 24 (8+i) := by decide +kernel

theorem valid_r24_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (16+i)) 24 (16+i) := by decide +kernel

theorem valid_r24_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (24+i)) 24 (24+i) := by decide +kernel

theorem valid_r24_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (32+i)) 24 (32+i) := by decide +kernel

theorem valid_r24_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (40+i)) 24 (40+i) := by decide +kernel

theorem valid_r24_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (48+i)) 24 (48+i) := by decide +kernel

theorem valid_r24_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (56+i)) 24 (56+i) := by decide +kernel

theorem valid_r24_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (64+i)) 24 (64+i) := by decide +kernel

theorem valid_r24_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (72+i)) 24 (72+i) := by decide +kernel

theorem valid_r24_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (80+i)) 24 (80+i) := by decide +kernel

theorem valid_r24_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (88+i)) 24 (88+i) := by decide +kernel

theorem valid_r24_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (96+i)) 24 (96+i) := by decide +kernel

theorem valid_r24_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 24 (104+i)) 24 (104+i) := by decide +kernel

theorem valid_r24_part112 : ∀ i ∈ List.range 7, Valid (BoundaryTailBaseFastData.row 24 (112+i)) 24 (112+i) := by decide +kernel

theorem valid_r24 (V : ℕ) (hV : V ∈ List.range 119) : Valid (BoundaryTailBaseFastData.row 24 V) 24 V := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := valid_r24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r24_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (0+i)) 24 (0+i) = true := by decide +kernel

theorem strictBool_r24_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (1+i)) 24 (1+i) = true := by decide +kernel

theorem strictBool_r24_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (2+i)) 24 (2+i) = true := by decide +kernel

theorem strictBool_r24_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (3+i)) 24 (3+i) = true := by decide +kernel

theorem strictBool_r24_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (4+i)) 24 (4+i) = true := by decide +kernel

theorem strictBool_r24_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (5+i)) 24 (5+i) = true := by decide +kernel

theorem strictBool_r24_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (6+i)) 24 (6+i) = true := by decide +kernel

theorem strictBool_r24_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (7+i)) 24 (7+i) = true := by decide +kernel

theorem strictBool_r24_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (8+i)) 24 (8+i) = true := by decide +kernel

theorem strictBool_r24_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (9+i)) 24 (9+i) = true := by decide +kernel

theorem strictBool_r24_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (10+i)) 24 (10+i) = true := by decide +kernel

theorem strictBool_r24_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (11+i)) 24 (11+i) = true := by decide +kernel

theorem strictBool_r24_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (12+i)) 24 (12+i) = true := by decide +kernel

theorem strictBool_r24_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (13+i)) 24 (13+i) = true := by decide +kernel

theorem strictBool_r24_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (14+i)) 24 (14+i) = true := by decide +kernel

theorem strictBool_r24_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (15+i)) 24 (15+i) = true := by decide +kernel

theorem strictBool_r24_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (16+i)) 24 (16+i) = true := by decide +kernel

theorem strictBool_r24_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (17+i)) 24 (17+i) = true := by decide +kernel

theorem strictBool_r24_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (18+i)) 24 (18+i) = true := by decide +kernel

theorem strictBool_r24_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (19+i)) 24 (19+i) = true := by decide +kernel

theorem strictBool_r24_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (20+i)) 24 (20+i) = true := by decide +kernel

theorem strictBool_r24_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (21+i)) 24 (21+i) = true := by decide +kernel

theorem strictBool_r24_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (22+i)) 24 (22+i) = true := by decide +kernel

theorem strictBool_r24_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (23+i)) 24 (23+i) = true := by decide +kernel

theorem strictBool_r24_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (24+i)) 24 (24+i) = true := by decide +kernel

theorem strictBool_r24_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (25+i)) 24 (25+i) = true := by decide +kernel

theorem strictBool_r24_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (26+i)) 24 (26+i) = true := by decide +kernel

theorem strictBool_r24_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (27+i)) 24 (27+i) = true := by decide +kernel

theorem strictBool_r24_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (28+i)) 24 (28+i) = true := by decide +kernel

theorem strictBool_r24_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (29+i)) 24 (29+i) = true := by decide +kernel

theorem strictBool_r24_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (30+i)) 24 (30+i) = true := by decide +kernel

theorem strictBool_r24_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (31+i)) 24 (31+i) = true := by decide +kernel

theorem strictBool_r24_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (32+i)) 24 (32+i) = true := by decide +kernel

theorem strictBool_r24_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (33+i)) 24 (33+i) = true := by decide +kernel

theorem strictBool_r24_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (34+i)) 24 (34+i) = true := by decide +kernel

theorem strictBool_r24_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (35+i)) 24 (35+i) = true := by decide +kernel

theorem strictBool_r24_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (36+i)) 24 (36+i) = true := by decide +kernel

theorem strictBool_r24_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (37+i)) 24 (37+i) = true := by decide +kernel

theorem strictBool_r24_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (38+i)) 24 (38+i) = true := by decide +kernel

theorem strictBool_r24_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (39+i)) 24 (39+i) = true := by decide +kernel

theorem strictBool_r24_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (40+i)) 24 (40+i) = true := by decide +kernel

theorem strictBool_r24_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (41+i)) 24 (41+i) = true := by decide +kernel

theorem strictBool_r24_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (42+i)) 24 (42+i) = true := by decide +kernel

theorem strictBool_r24_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (43+i)) 24 (43+i) = true := by decide +kernel

theorem strictBool_r24_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (44+i)) 24 (44+i) = true := by decide +kernel

theorem strictBool_r24_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (45+i)) 24 (45+i) = true := by decide +kernel

theorem strictBool_r24_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (46+i)) 24 (46+i) = true := by decide +kernel

theorem strictBool_r24_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (47+i)) 24 (47+i) = true := by decide +kernel

theorem strictBool_r24_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (48+i)) 24 (48+i) = true := by decide +kernel

theorem strictBool_r24_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (49+i)) 24 (49+i) = true := by decide +kernel

theorem strictBool_r24_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (50+i)) 24 (50+i) = true := by decide +kernel

theorem strictBool_r24_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (51+i)) 24 (51+i) = true := by decide +kernel

theorem strictBool_r24_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (52+i)) 24 (52+i) = true := by decide +kernel

theorem strictBool_r24_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (53+i)) 24 (53+i) = true := by decide +kernel

theorem strictBool_r24_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (54+i)) 24 (54+i) = true := by decide +kernel

theorem strictBool_r24_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (55+i)) 24 (55+i) = true := by decide +kernel

theorem strictBool_r24_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (56+i)) 24 (56+i) = true := by decide +kernel

theorem strictBool_r24_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (57+i)) 24 (57+i) = true := by decide +kernel

theorem strictBool_r24_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (58+i)) 24 (58+i) = true := by decide +kernel

theorem strictBool_r24_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (59+i)) 24 (59+i) = true := by decide +kernel

theorem strictBool_r24_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (60+i)) 24 (60+i) = true := by decide +kernel

theorem strictBool_r24_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (61+i)) 24 (61+i) = true := by decide +kernel

theorem strictBool_r24_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (62+i)) 24 (62+i) = true := by decide +kernel

theorem strictBool_r24_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (63+i)) 24 (63+i) = true := by decide +kernel

theorem strictBool_r24_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (64+i)) 24 (64+i) = true := by decide +kernel

theorem strictBool_r24_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (65+i)) 24 (65+i) = true := by decide +kernel

theorem strictBool_r24_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (66+i)) 24 (66+i) = true := by decide +kernel

theorem strictBool_r24_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (67+i)) 24 (67+i) = true := by decide +kernel

theorem strictBool_r24_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (68+i)) 24 (68+i) = true := by decide +kernel

theorem strictBool_r24_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (69+i)) 24 (69+i) = true := by decide +kernel

theorem strictBool_r24_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (70+i)) 24 (70+i) = true := by decide +kernel

theorem strictBool_r24_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (71+i)) 24 (71+i) = true := by decide +kernel

theorem strictBool_r24_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (72+i)) 24 (72+i) = true := by decide +kernel

theorem strictBool_r24_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (73+i)) 24 (73+i) = true := by decide +kernel

theorem strictBool_r24_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (74+i)) 24 (74+i) = true := by decide +kernel

theorem strictBool_r24_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (75+i)) 24 (75+i) = true := by decide +kernel

theorem strictBool_r24_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (76+i)) 24 (76+i) = true := by decide +kernel

theorem strictBool_r24_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (77+i)) 24 (77+i) = true := by decide +kernel

theorem strictBool_r24_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (78+i)) 24 (78+i) = true := by decide +kernel

theorem strictBool_r24_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (79+i)) 24 (79+i) = true := by decide +kernel

theorem strictBool_r24_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (80+i)) 24 (80+i) = true := by decide +kernel

theorem strictBool_r24_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (81+i)) 24 (81+i) = true := by decide +kernel

theorem strictBool_r24_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (82+i)) 24 (82+i) = true := by decide +kernel

theorem strictBool_r24_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (83+i)) 24 (83+i) = true := by decide +kernel

theorem strictBool_r24_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (84+i)) 24 (84+i) = true := by decide +kernel

theorem strictBool_r24_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (85+i)) 24 (85+i) = true := by decide +kernel

theorem strictBool_r24_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (86+i)) 24 (86+i) = true := by decide +kernel

theorem strictBool_r24_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (87+i)) 24 (87+i) = true := by decide +kernel

theorem strictBool_r24_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (88+i)) 24 (88+i) = true := by decide +kernel

theorem strictBool_r24_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (89+i)) 24 (89+i) = true := by decide +kernel

theorem strictBool_r24_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (90+i)) 24 (90+i) = true := by decide +kernel

theorem strictBool_r24_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (91+i)) 24 (91+i) = true := by decide +kernel

theorem strictBool_r24_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (92+i)) 24 (92+i) = true := by decide +kernel

theorem strictBool_r24_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (93+i)) 24 (93+i) = true := by decide +kernel

theorem strictBool_r24_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (94+i)) 24 (94+i) = true := by decide +kernel

theorem strictBool_r24_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (95+i)) 24 (95+i) = true := by decide +kernel

theorem strictBool_r24_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (96+i)) 24 (96+i) = true := by decide +kernel

theorem strictBool_r24_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (97+i)) 24 (97+i) = true := by decide +kernel

theorem strictBool_r24_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (98+i)) 24 (98+i) = true := by decide +kernel

theorem strictBool_r24_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (99+i)) 24 (99+i) = true := by decide +kernel

theorem strictBool_r24_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (100+i)) 24 (100+i) = true := by decide +kernel

theorem strictBool_r24_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (101+i)) 24 (101+i) = true := by decide +kernel

theorem strictBool_r24_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (102+i)) 24 (102+i) = true := by decide +kernel

theorem strictBool_r24_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (103+i)) 24 (103+i) = true := by decide +kernel

theorem strictBool_r24_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (104+i)) 24 (104+i) = true := by decide +kernel

theorem strictBool_r24_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (105+i)) 24 (105+i) = true := by decide +kernel

theorem strictBool_r24_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (106+i)) 24 (106+i) = true := by decide +kernel

theorem strictBool_r24_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (107+i)) 24 (107+i) = true := by decide +kernel

theorem strictBool_r24_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (108+i)) 24 (108+i) = true := by decide +kernel

theorem strictBool_r24_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (109+i)) 24 (109+i) = true := by decide +kernel

theorem strictBool_r24_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (110+i)) 24 (110+i) = true := by decide +kernel

theorem strictBool_r24_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (111+i)) 24 (111+i) = true := by decide +kernel

theorem strictBool_r24_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (112+i)) 24 (112+i) = true := by decide +kernel

theorem strictBool_r24_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (113+i)) 24 (113+i) = true := by decide +kernel

theorem strictBool_r24_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (114+i)) 24 (114+i) = true := by decide +kernel

theorem strictBool_r24_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (115+i)) 24 (115+i) = true := by decide +kernel

theorem strictBool_r24_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (116+i)) 24 (116+i) = true := by decide +kernel

theorem strictBool_r24_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (117+i)) 24 (117+i) = true := by decide +kernel

theorem strictBool_r24_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 24 (118+i)) 24 (118+i) = true := by decide +kernel

theorem strictBool_r24 (V : ℕ) (hV : V ∈ List.range 119) : strictBool (BoundaryTailBaseFastData.row 24 V) 24 V = true := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 59
  · by_cases h0_59 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r24_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r24_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r24_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r24_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r24_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r24_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r24_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r24_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r24_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r24_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r24_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r24_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r24_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r24_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r24_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r24_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h29_59 : V < 44
      · by_cases h29_44 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have hi := strictBool_r24_part29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r24_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r24_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r24_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
        · by_cases h36_44 : V < 40
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r24_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r24_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r24_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r24_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
      · by_cases h44_59 : V < 51
        · by_cases h44_51 : V < 47
          · by_cases h44_47 : V < 45
            · have hi := strictBool_r24_part44 (V-44) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r24_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r24_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r24_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r24_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r24_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r24_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r24_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
  · by_cases h59_119 : V < 89
    · by_cases h59_89 : V < 74
      · by_cases h59_74 : V < 66
        · by_cases h59_66 : V < 62
          · by_cases h59_62 : V < 60
            · have hi := strictBool_r24_part59 (V-59) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r24_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_66 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r24_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r24_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r24_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r24_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r24_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r24_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
      · by_cases h74_89 : V < 81
        · by_cases h74_81 : V < 77
          · by_cases h74_77 : V < 75
            · have hi := strictBool_r24_part74 (V-74) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r24_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r24_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r24_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r24_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r24_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r24_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r24_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h89_119 : V < 104
      · by_cases h89_104 : V < 96
        · by_cases h89_96 : V < 92
          · by_cases h89_92 : V < 90
            · have hi := strictBool_r24_part89 (V-89) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r24_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r24_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r24_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
        · by_cases h96_104 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r24_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r24_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r24_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r24_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 111
        · by_cases h104_111 : V < 107
          · by_cases h104_107 : V < 105
            · have hi := strictBool_r24_part104 (V-104) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r24_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r24_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r24_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
        · by_cases h111_119 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r24_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r24_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r24_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r24_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r24_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi

theorem strictFast_r24 (V : ℕ) (hV : V ∈ List.range 119) : StrictAtFast (BoundaryTailBaseFastData.row 24 V) 24 V :=
  strictBool_sound _ _ _ (strictBool_r24 V hV)

theorem strict_r24 (V : ℕ) (hV : V ∈ List.range 119) : StrictCheckAt 24 V :=
  strictAtFast_sound _ _ _ (valid_r24 V hV) (strictFast_r24 V hV)

theorem zeroCertificate_r24_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (0+i)) 24 (0+i) := by decide +kernel

theorem zeroCertificate_r24_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (8+i)) 24 (8+i) := by decide +kernel

theorem zeroCertificate_r24_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (16+i)) 24 (16+i) := by decide +kernel

theorem zeroCertificate_r24_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (24+i)) 24 (24+i) := by decide +kernel

theorem zeroCertificate_r24_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (32+i)) 24 (32+i) := by decide +kernel

theorem zeroCertificate_r24_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (40+i)) 24 (40+i) := by decide +kernel

theorem zeroCertificate_r24_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (48+i)) 24 (48+i) := by decide +kernel

theorem zeroCertificate_r24_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (56+i)) 24 (56+i) := by decide +kernel

theorem zeroCertificate_r24_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (64+i)) 24 (64+i) := by decide +kernel

theorem zeroCertificate_r24_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (72+i)) 24 (72+i) := by decide +kernel

theorem zeroCertificate_r24_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (80+i)) 24 (80+i) := by decide +kernel

theorem zeroCertificate_r24_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (88+i)) 24 (88+i) := by decide +kernel

theorem zeroCertificate_r24_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (96+i)) 24 (96+i) := by decide +kernel

theorem zeroCertificate_r24_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 24 (104+i)) 24 (104+i) := by decide +kernel

theorem zeroCertificate_r24_part112 : ∀ i ∈ List.range 7, ZeroCertificate (BoundaryTailBaseFastData.row 24 (112+i)) 24 (112+i) := by decide +kernel

theorem zeroCertificate_r24 (V : ℕ) (hV : V ∈ List.range 119) : ZeroCertificate (BoundaryTailBaseFastData.row 24 V) 24 V := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := zeroCertificate_r24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r24 (V : ℕ) (hV : V ∈ List.range 119) : ZeroAtFast 24 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r24 V hV) (zeroCertificate_r24 V hV)

theorem zero_r24 (V : ℕ) (hV : V ∈ List.range 119) : ZeroCheckAt 24 V :=
  zeroAtFast_sound _ _ (zeroFast_r24 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r28_part0 : ∀ i ∈ List.range 8, CorrectAt 28 (0+i) := by decide +kernel

theorem correct_r28_part8 : ∀ i ∈ List.range 8, CorrectAt 28 (8+i) := by decide +kernel

theorem correct_r28_part16 : ∀ i ∈ List.range 8, CorrectAt 28 (16+i) := by decide +kernel

theorem correct_r28_part24 : ∀ i ∈ List.range 8, CorrectAt 28 (24+i) := by decide +kernel

theorem correct_r28_part32 : ∀ i ∈ List.range 8, CorrectAt 28 (32+i) := by decide +kernel

theorem correct_r28_part40 : ∀ i ∈ List.range 8, CorrectAt 28 (40+i) := by decide +kernel

theorem correct_r28_part48 : ∀ i ∈ List.range 8, CorrectAt 28 (48+i) := by decide +kernel

theorem correct_r28_part56 : ∀ i ∈ List.range 8, CorrectAt 28 (56+i) := by decide +kernel

theorem correct_r28_part64 : ∀ i ∈ List.range 8, CorrectAt 28 (64+i) := by decide +kernel

theorem correct_r28_part72 : ∀ i ∈ List.range 8, CorrectAt 28 (72+i) := by decide +kernel

theorem correct_r28_part80 : ∀ i ∈ List.range 8, CorrectAt 28 (80+i) := by decide +kernel

theorem correct_r28_part88 : ∀ i ∈ List.range 8, CorrectAt 28 (88+i) := by decide +kernel

theorem correct_r28_part96 : ∀ i ∈ List.range 8, CorrectAt 28 (96+i) := by decide +kernel

theorem correct_r28_part104 : ∀ i ∈ List.range 8, CorrectAt 28 (104+i) := by decide +kernel

theorem correct_r28_part112 : ∀ i ∈ List.range 3, CorrectAt 28 (112+i) := by decide +kernel

theorem correct_r28 (V : ℕ) (hV : V ∈ List.range 115) : CorrectAt 28 V := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := correct_r28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r28_part0 : ∀ i ∈ List.range 8, BaseCheckAt 28 (0+i) := by decide +kernel

theorem base_r28_part8 : ∀ i ∈ List.range 8, BaseCheckAt 28 (8+i) := by decide +kernel

theorem base_r28_part16 : ∀ i ∈ List.range 8, BaseCheckAt 28 (16+i) := by decide +kernel

theorem base_r28_part24 : ∀ i ∈ List.range 8, BaseCheckAt 28 (24+i) := by decide +kernel

theorem base_r28_part32 : ∀ i ∈ List.range 8, BaseCheckAt 28 (32+i) := by decide +kernel

theorem base_r28_part40 : ∀ i ∈ List.range 8, BaseCheckAt 28 (40+i) := by decide +kernel

theorem base_r28_part48 : ∀ i ∈ List.range 8, BaseCheckAt 28 (48+i) := by decide +kernel

theorem base_r28_part56 : ∀ i ∈ List.range 8, BaseCheckAt 28 (56+i) := by decide +kernel

theorem base_r28_part64 : ∀ i ∈ List.range 8, BaseCheckAt 28 (64+i) := by decide +kernel

theorem base_r28_part72 : ∀ i ∈ List.range 8, BaseCheckAt 28 (72+i) := by decide +kernel

theorem base_r28_part80 : ∀ i ∈ List.range 8, BaseCheckAt 28 (80+i) := by decide +kernel

theorem base_r28_part88 : ∀ i ∈ List.range 8, BaseCheckAt 28 (88+i) := by decide +kernel

theorem base_r28_part96 : ∀ i ∈ List.range 8, BaseCheckAt 28 (96+i) := by decide +kernel

theorem base_r28_part104 : ∀ i ∈ List.range 8, BaseCheckAt 28 (104+i) := by decide +kernel

theorem base_r28_part112 : ∀ i ∈ List.range 3, BaseCheckAt 28 (112+i) := by decide +kernel

theorem base_r28 (V : ℕ) (hV : V ∈ List.range 115) : BaseCheckAt 28 V := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := base_r28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r28_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (0+i)) 28 (0+i) := by decide +kernel

theorem valid_r28_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (8+i)) 28 (8+i) := by decide +kernel

theorem valid_r28_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (16+i)) 28 (16+i) := by decide +kernel

theorem valid_r28_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (24+i)) 28 (24+i) := by decide +kernel

theorem valid_r28_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (32+i)) 28 (32+i) := by decide +kernel

theorem valid_r28_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (40+i)) 28 (40+i) := by decide +kernel

theorem valid_r28_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (48+i)) 28 (48+i) := by decide +kernel

theorem valid_r28_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (56+i)) 28 (56+i) := by decide +kernel

theorem valid_r28_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (64+i)) 28 (64+i) := by decide +kernel

theorem valid_r28_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (72+i)) 28 (72+i) := by decide +kernel

theorem valid_r28_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (80+i)) 28 (80+i) := by decide +kernel

theorem valid_r28_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (88+i)) 28 (88+i) := by decide +kernel

theorem valid_r28_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (96+i)) 28 (96+i) := by decide +kernel

theorem valid_r28_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 28 (104+i)) 28 (104+i) := by decide +kernel

theorem valid_r28_part112 : ∀ i ∈ List.range 3, Valid (BoundaryTailBaseFastData.row 28 (112+i)) 28 (112+i) := by decide +kernel

theorem valid_r28 (V : ℕ) (hV : V ∈ List.range 115) : Valid (BoundaryTailBaseFastData.row 28 V) 28 V := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := valid_r28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r28_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (0+i)) 28 (0+i) = true := by decide +kernel

theorem strictBool_r28_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (1+i)) 28 (1+i) = true := by decide +kernel

theorem strictBool_r28_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (2+i)) 28 (2+i) = true := by decide +kernel

theorem strictBool_r28_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (3+i)) 28 (3+i) = true := by decide +kernel

theorem strictBool_r28_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (4+i)) 28 (4+i) = true := by decide +kernel

theorem strictBool_r28_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (5+i)) 28 (5+i) = true := by decide +kernel

theorem strictBool_r28_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (6+i)) 28 (6+i) = true := by decide +kernel

theorem strictBool_r28_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (7+i)) 28 (7+i) = true := by decide +kernel

theorem strictBool_r28_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (8+i)) 28 (8+i) = true := by decide +kernel

theorem strictBool_r28_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (9+i)) 28 (9+i) = true := by decide +kernel

theorem strictBool_r28_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (10+i)) 28 (10+i) = true := by decide +kernel

theorem strictBool_r28_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (11+i)) 28 (11+i) = true := by decide +kernel

theorem strictBool_r28_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (12+i)) 28 (12+i) = true := by decide +kernel

theorem strictBool_r28_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (13+i)) 28 (13+i) = true := by decide +kernel

theorem strictBool_r28_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (14+i)) 28 (14+i) = true := by decide +kernel

theorem strictBool_r28_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (15+i)) 28 (15+i) = true := by decide +kernel

theorem strictBool_r28_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (16+i)) 28 (16+i) = true := by decide +kernel

theorem strictBool_r28_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (17+i)) 28 (17+i) = true := by decide +kernel

theorem strictBool_r28_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (18+i)) 28 (18+i) = true := by decide +kernel

theorem strictBool_r28_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (19+i)) 28 (19+i) = true := by decide +kernel

theorem strictBool_r28_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (20+i)) 28 (20+i) = true := by decide +kernel

theorem strictBool_r28_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (21+i)) 28 (21+i) = true := by decide +kernel

theorem strictBool_r28_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (22+i)) 28 (22+i) = true := by decide +kernel

theorem strictBool_r28_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (23+i)) 28 (23+i) = true := by decide +kernel

theorem strictBool_r28_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (24+i)) 28 (24+i) = true := by decide +kernel

theorem strictBool_r28_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (25+i)) 28 (25+i) = true := by decide +kernel

theorem strictBool_r28_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (26+i)) 28 (26+i) = true := by decide +kernel

theorem strictBool_r28_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (27+i)) 28 (27+i) = true := by decide +kernel

theorem strictBool_r28_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (28+i)) 28 (28+i) = true := by decide +kernel

theorem strictBool_r28_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (29+i)) 28 (29+i) = true := by decide +kernel

theorem strictBool_r28_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (30+i)) 28 (30+i) = true := by decide +kernel

theorem strictBool_r28_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (31+i)) 28 (31+i) = true := by decide +kernel

theorem strictBool_r28_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (32+i)) 28 (32+i) = true := by decide +kernel

theorem strictBool_r28_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (33+i)) 28 (33+i) = true := by decide +kernel

theorem strictBool_r28_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (34+i)) 28 (34+i) = true := by decide +kernel

theorem strictBool_r28_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (35+i)) 28 (35+i) = true := by decide +kernel

theorem strictBool_r28_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (36+i)) 28 (36+i) = true := by decide +kernel

theorem strictBool_r28_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (37+i)) 28 (37+i) = true := by decide +kernel

theorem strictBool_r28_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (38+i)) 28 (38+i) = true := by decide +kernel

theorem strictBool_r28_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (39+i)) 28 (39+i) = true := by decide +kernel

theorem strictBool_r28_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (40+i)) 28 (40+i) = true := by decide +kernel

theorem strictBool_r28_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (41+i)) 28 (41+i) = true := by decide +kernel

theorem strictBool_r28_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (42+i)) 28 (42+i) = true := by decide +kernel

theorem strictBool_r28_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (43+i)) 28 (43+i) = true := by decide +kernel

theorem strictBool_r28_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (44+i)) 28 (44+i) = true := by decide +kernel

theorem strictBool_r28_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (45+i)) 28 (45+i) = true := by decide +kernel

theorem strictBool_r28_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (46+i)) 28 (46+i) = true := by decide +kernel

theorem strictBool_r28_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (47+i)) 28 (47+i) = true := by decide +kernel

theorem strictBool_r28_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (48+i)) 28 (48+i) = true := by decide +kernel

theorem strictBool_r28_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (49+i)) 28 (49+i) = true := by decide +kernel

theorem strictBool_r28_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (50+i)) 28 (50+i) = true := by decide +kernel

theorem strictBool_r28_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (51+i)) 28 (51+i) = true := by decide +kernel

theorem strictBool_r28_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (52+i)) 28 (52+i) = true := by decide +kernel

theorem strictBool_r28_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (53+i)) 28 (53+i) = true := by decide +kernel

theorem strictBool_r28_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (54+i)) 28 (54+i) = true := by decide +kernel

theorem strictBool_r28_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (55+i)) 28 (55+i) = true := by decide +kernel

theorem strictBool_r28_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (56+i)) 28 (56+i) = true := by decide +kernel

theorem strictBool_r28_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (57+i)) 28 (57+i) = true := by decide +kernel

theorem strictBool_r28_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (58+i)) 28 (58+i) = true := by decide +kernel

theorem strictBool_r28_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (59+i)) 28 (59+i) = true := by decide +kernel

theorem strictBool_r28_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (60+i)) 28 (60+i) = true := by decide +kernel

theorem strictBool_r28_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (61+i)) 28 (61+i) = true := by decide +kernel

theorem strictBool_r28_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (62+i)) 28 (62+i) = true := by decide +kernel

theorem strictBool_r28_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (63+i)) 28 (63+i) = true := by decide +kernel

theorem strictBool_r28_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (64+i)) 28 (64+i) = true := by decide +kernel

theorem strictBool_r28_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (65+i)) 28 (65+i) = true := by decide +kernel

theorem strictBool_r28_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (66+i)) 28 (66+i) = true := by decide +kernel

theorem strictBool_r28_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (67+i)) 28 (67+i) = true := by decide +kernel

theorem strictBool_r28_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (68+i)) 28 (68+i) = true := by decide +kernel

theorem strictBool_r28_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (69+i)) 28 (69+i) = true := by decide +kernel

theorem strictBool_r28_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (70+i)) 28 (70+i) = true := by decide +kernel

theorem strictBool_r28_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (71+i)) 28 (71+i) = true := by decide +kernel

theorem strictBool_r28_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (72+i)) 28 (72+i) = true := by decide +kernel

theorem strictBool_r28_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (73+i)) 28 (73+i) = true := by decide +kernel

theorem strictBool_r28_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (74+i)) 28 (74+i) = true := by decide +kernel

theorem strictBool_r28_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (75+i)) 28 (75+i) = true := by decide +kernel

theorem strictBool_r28_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (76+i)) 28 (76+i) = true := by decide +kernel

theorem strictBool_r28_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (77+i)) 28 (77+i) = true := by decide +kernel

theorem strictBool_r28_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (78+i)) 28 (78+i) = true := by decide +kernel

theorem strictBool_r28_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (79+i)) 28 (79+i) = true := by decide +kernel

theorem strictBool_r28_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (80+i)) 28 (80+i) = true := by decide +kernel

theorem strictBool_r28_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (81+i)) 28 (81+i) = true := by decide +kernel

theorem strictBool_r28_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (82+i)) 28 (82+i) = true := by decide +kernel

theorem strictBool_r28_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (83+i)) 28 (83+i) = true := by decide +kernel

theorem strictBool_r28_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (84+i)) 28 (84+i) = true := by decide +kernel

theorem strictBool_r28_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (85+i)) 28 (85+i) = true := by decide +kernel

theorem strictBool_r28_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (86+i)) 28 (86+i) = true := by decide +kernel

theorem strictBool_r28_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (87+i)) 28 (87+i) = true := by decide +kernel

theorem strictBool_r28_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (88+i)) 28 (88+i) = true := by decide +kernel

theorem strictBool_r28_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (89+i)) 28 (89+i) = true := by decide +kernel

theorem strictBool_r28_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (90+i)) 28 (90+i) = true := by decide +kernel

theorem strictBool_r28_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (91+i)) 28 (91+i) = true := by decide +kernel

theorem strictBool_r28_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (92+i)) 28 (92+i) = true := by decide +kernel

theorem strictBool_r28_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (93+i)) 28 (93+i) = true := by decide +kernel

theorem strictBool_r28_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (94+i)) 28 (94+i) = true := by decide +kernel

theorem strictBool_r28_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (95+i)) 28 (95+i) = true := by decide +kernel

theorem strictBool_r28_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (96+i)) 28 (96+i) = true := by decide +kernel

theorem strictBool_r28_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (97+i)) 28 (97+i) = true := by decide +kernel

theorem strictBool_r28_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (98+i)) 28 (98+i) = true := by decide +kernel

theorem strictBool_r28_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (99+i)) 28 (99+i) = true := by decide +kernel

theorem strictBool_r28_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (100+i)) 28 (100+i) = true := by decide +kernel

theorem strictBool_r28_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (101+i)) 28 (101+i) = true := by decide +kernel

theorem strictBool_r28_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (102+i)) 28 (102+i) = true := by decide +kernel

theorem strictBool_r28_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (103+i)) 28 (103+i) = true := by decide +kernel

theorem strictBool_r28_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (104+i)) 28 (104+i) = true := by decide +kernel

theorem strictBool_r28_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (105+i)) 28 (105+i) = true := by decide +kernel

theorem strictBool_r28_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (106+i)) 28 (106+i) = true := by decide +kernel

theorem strictBool_r28_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (107+i)) 28 (107+i) = true := by decide +kernel

theorem strictBool_r28_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (108+i)) 28 (108+i) = true := by decide +kernel

theorem strictBool_r28_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (109+i)) 28 (109+i) = true := by decide +kernel

theorem strictBool_r28_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (110+i)) 28 (110+i) = true := by decide +kernel

theorem strictBool_r28_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (111+i)) 28 (111+i) = true := by decide +kernel

theorem strictBool_r28_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (112+i)) 28 (112+i) = true := by decide +kernel

theorem strictBool_r28_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (113+i)) 28 (113+i) = true := by decide +kernel

theorem strictBool_r28_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 28 (114+i)) 28 (114+i) = true := by decide +kernel

theorem strictBool_r28 (V : ℕ) (hV : V ∈ List.range 115) : strictBool (BoundaryTailBaseFastData.row 28 V) 28 V = true := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 57
  · by_cases h0_57 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r28_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r28_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r28_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r28_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r28_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r28_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r28_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r28_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r28_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r28_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r28_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r28_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have hi := strictBool_r28_part21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r28_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r28_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r28_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
    · by_cases h28_57 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have hi := strictBool_r28_part28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r28_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r28_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r28_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have hi := strictBool_r28_part35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r28_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r28_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r28_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
      · by_cases h42_57 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have hi := strictBool_r28_part42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r28_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r28_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r28_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r28_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r28_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r28_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r28_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h57_115 : V < 86
    · by_cases h57_86 : V < 71
      · by_cases h57_71 : V < 64
        · by_cases h57_64 : V < 60
          · by_cases h57_60 : V < 58
            · have hi := strictBool_r28_part57 (V-57) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r28_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r28_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r28_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
        · by_cases h64_71 : V < 67
          · by_cases h64_67 : V < 65
            · have hi := strictBool_r28_part64 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r28_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r28_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r28_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
      · by_cases h71_86 : V < 78
        · by_cases h71_78 : V < 74
          · by_cases h71_74 : V < 72
            · have hi := strictBool_r28_part71 (V-71) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r28_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r28_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r28_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
        · by_cases h78_86 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r28_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r28_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r28_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r28_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
    · by_cases h86_115 : V < 100
      · by_cases h86_100 : V < 93
        · by_cases h86_93 : V < 89
          · by_cases h86_89 : V < 87
            · have hi := strictBool_r28_part86 (V-86) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r28_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r28_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r28_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_100 : V < 96
          · by_cases h93_96 : V < 94
            · have hi := strictBool_r28_part93 (V-93) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r28_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r28_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r28_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
      · by_cases h100_115 : V < 107
        · by_cases h100_107 : V < 103
          · by_cases h100_103 : V < 101
            · have hi := strictBool_r28_part100 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r28_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r28_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r28_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r28_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r28_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r28_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r28_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r28_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi

theorem strictFast_r28 (V : ℕ) (hV : V ∈ List.range 115) : StrictAtFast (BoundaryTailBaseFastData.row 28 V) 28 V :=
  strictBool_sound _ _ _ (strictBool_r28 V hV)

theorem strict_r28 (V : ℕ) (hV : V ∈ List.range 115) : StrictCheckAt 28 V :=
  strictAtFast_sound _ _ _ (valid_r28 V hV) (strictFast_r28 V hV)

theorem zeroCertificate_r28_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (0+i)) 28 (0+i) := by decide +kernel

theorem zeroCertificate_r28_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (8+i)) 28 (8+i) := by decide +kernel

theorem zeroCertificate_r28_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (16+i)) 28 (16+i) := by decide +kernel

theorem zeroCertificate_r28_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (24+i)) 28 (24+i) := by decide +kernel

theorem zeroCertificate_r28_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (32+i)) 28 (32+i) := by decide +kernel

theorem zeroCertificate_r28_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (40+i)) 28 (40+i) := by decide +kernel

theorem zeroCertificate_r28_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (48+i)) 28 (48+i) := by decide +kernel

theorem zeroCertificate_r28_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (56+i)) 28 (56+i) := by decide +kernel

theorem zeroCertificate_r28_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (64+i)) 28 (64+i) := by decide +kernel

theorem zeroCertificate_r28_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (72+i)) 28 (72+i) := by decide +kernel

theorem zeroCertificate_r28_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (80+i)) 28 (80+i) := by decide +kernel

theorem zeroCertificate_r28_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (88+i)) 28 (88+i) := by decide +kernel

theorem zeroCertificate_r28_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (96+i)) 28 (96+i) := by decide +kernel

theorem zeroCertificate_r28_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 28 (104+i)) 28 (104+i) := by decide +kernel

theorem zeroCertificate_r28_part112 : ∀ i ∈ List.range 3, ZeroCertificate (BoundaryTailBaseFastData.row 28 (112+i)) 28 (112+i) := by decide +kernel

theorem zeroCertificate_r28 (V : ℕ) (hV : V ∈ List.range 115) : ZeroCertificate (BoundaryTailBaseFastData.row 28 V) 28 V := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := zeroCertificate_r28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r28 (V : ℕ) (hV : V ∈ List.range 115) : ZeroAtFast 28 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r28 V hV) (zeroCertificate_r28 V hV)

theorem zero_r28 (V : ℕ) (hV : V ∈ List.range 115) : ZeroCheckAt 28 V :=
  zeroAtFast_sound _ _ (zeroFast_r28 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
