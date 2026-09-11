import ProximityPrize.SubmissionLower.BoundaryTailBaseBlock01
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r2_part0 : ∀ i ∈ List.range 8, CorrectAt 2 (0+i) := by decide +kernel

theorem correct_r2_part8 : ∀ i ∈ List.range 8, CorrectAt 2 (8+i) := by decide +kernel

theorem correct_r2_part16 : ∀ i ∈ List.range 8, CorrectAt 2 (16+i) := by decide +kernel

theorem correct_r2_part24 : ∀ i ∈ List.range 8, CorrectAt 2 (24+i) := by decide +kernel

theorem correct_r2_part32 : ∀ i ∈ List.range 8, CorrectAt 2 (32+i) := by decide +kernel

theorem correct_r2_part40 : ∀ i ∈ List.range 8, CorrectAt 2 (40+i) := by decide +kernel

theorem correct_r2_part48 : ∀ i ∈ List.range 8, CorrectAt 2 (48+i) := by decide +kernel

theorem correct_r2_part56 : ∀ i ∈ List.range 8, CorrectAt 2 (56+i) := by decide +kernel

theorem correct_r2_part64 : ∀ i ∈ List.range 8, CorrectAt 2 (64+i) := by decide +kernel

theorem correct_r2_part72 : ∀ i ∈ List.range 8, CorrectAt 2 (72+i) := by decide +kernel

theorem correct_r2_part80 : ∀ i ∈ List.range 8, CorrectAt 2 (80+i) := by decide +kernel

theorem correct_r2_part88 : ∀ i ∈ List.range 8, CorrectAt 2 (88+i) := by decide +kernel

theorem correct_r2_part96 : ∀ i ∈ List.range 8, CorrectAt 2 (96+i) := by decide +kernel

theorem correct_r2_part104 : ∀ i ∈ List.range 8, CorrectAt 2 (104+i) := by decide +kernel

theorem correct_r2_part112 : ∀ i ∈ List.range 8, CorrectAt 2 (112+i) := by decide +kernel

theorem correct_r2_part120 : ∀ i ∈ List.range 8, CorrectAt 2 (120+i) := by decide +kernel

theorem correct_r2_part128 : ∀ i ∈ List.range 8, CorrectAt 2 (128+i) := by decide +kernel

theorem correct_r2_part136 : ∀ i ∈ List.range 5, CorrectAt 2 (136+i) := by decide +kernel

theorem correct_r2 (V : ℕ) (hV : V ∈ List.range 141) : CorrectAt 2 V := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := correct_r2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := correct_r2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r2_part0 : ∀ i ∈ List.range 8, BaseCheckAt 2 (0+i) := by decide +kernel

theorem base_r2_part8 : ∀ i ∈ List.range 8, BaseCheckAt 2 (8+i) := by decide +kernel

theorem base_r2_part16 : ∀ i ∈ List.range 8, BaseCheckAt 2 (16+i) := by decide +kernel

theorem base_r2_part24 : ∀ i ∈ List.range 8, BaseCheckAt 2 (24+i) := by decide +kernel

theorem base_r2_part32 : ∀ i ∈ List.range 8, BaseCheckAt 2 (32+i) := by decide +kernel

theorem base_r2_part40 : ∀ i ∈ List.range 8, BaseCheckAt 2 (40+i) := by decide +kernel

theorem base_r2_part48 : ∀ i ∈ List.range 8, BaseCheckAt 2 (48+i) := by decide +kernel

theorem base_r2_part56 : ∀ i ∈ List.range 8, BaseCheckAt 2 (56+i) := by decide +kernel

theorem base_r2_part64 : ∀ i ∈ List.range 8, BaseCheckAt 2 (64+i) := by decide +kernel

theorem base_r2_part72 : ∀ i ∈ List.range 8, BaseCheckAt 2 (72+i) := by decide +kernel

theorem base_r2_part80 : ∀ i ∈ List.range 8, BaseCheckAt 2 (80+i) := by decide +kernel

theorem base_r2_part88 : ∀ i ∈ List.range 8, BaseCheckAt 2 (88+i) := by decide +kernel

theorem base_r2_part96 : ∀ i ∈ List.range 8, BaseCheckAt 2 (96+i) := by decide +kernel

theorem base_r2_part104 : ∀ i ∈ List.range 8, BaseCheckAt 2 (104+i) := by decide +kernel

theorem base_r2_part112 : ∀ i ∈ List.range 8, BaseCheckAt 2 (112+i) := by decide +kernel

theorem base_r2_part120 : ∀ i ∈ List.range 8, BaseCheckAt 2 (120+i) := by decide +kernel

theorem base_r2_part128 : ∀ i ∈ List.range 8, BaseCheckAt 2 (128+i) := by decide +kernel

theorem base_r2_part136 : ∀ i ∈ List.range 5, BaseCheckAt 2 (136+i) := by decide +kernel

theorem base_r2 (V : ℕ) (hV : V ∈ List.range 141) : BaseCheckAt 2 V := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := base_r2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := base_r2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r2_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (0+i)) 2 (0+i) := by decide +kernel

theorem valid_r2_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (8+i)) 2 (8+i) := by decide +kernel

theorem valid_r2_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (16+i)) 2 (16+i) := by decide +kernel

theorem valid_r2_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (24+i)) 2 (24+i) := by decide +kernel

theorem valid_r2_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (32+i)) 2 (32+i) := by decide +kernel

theorem valid_r2_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (40+i)) 2 (40+i) := by decide +kernel

theorem valid_r2_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (48+i)) 2 (48+i) := by decide +kernel

theorem valid_r2_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (56+i)) 2 (56+i) := by decide +kernel

theorem valid_r2_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (64+i)) 2 (64+i) := by decide +kernel

theorem valid_r2_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (72+i)) 2 (72+i) := by decide +kernel

theorem valid_r2_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (80+i)) 2 (80+i) := by decide +kernel

theorem valid_r2_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (88+i)) 2 (88+i) := by decide +kernel

theorem valid_r2_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (96+i)) 2 (96+i) := by decide +kernel

theorem valid_r2_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (104+i)) 2 (104+i) := by decide +kernel

theorem valid_r2_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (112+i)) 2 (112+i) := by decide +kernel

theorem valid_r2_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (120+i)) 2 (120+i) := by decide +kernel

theorem valid_r2_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 2 (128+i)) 2 (128+i) := by decide +kernel

theorem valid_r2_part136 : ∀ i ∈ List.range 5, Valid (BoundaryTailBaseFastData.row 2 (136+i)) 2 (136+i) := by decide +kernel

theorem valid_r2 (V : ℕ) (hV : V ∈ List.range 141) : Valid (BoundaryTailBaseFastData.row 2 V) 2 V := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := valid_r2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := valid_r2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r2_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (0+i)) 2 (0+i) = true := by decide +kernel

theorem strictBool_r2_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (1+i)) 2 (1+i) = true := by decide +kernel

theorem strictBool_r2_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (2+i)) 2 (2+i) = true := by decide +kernel

theorem strictBool_r2_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (3+i)) 2 (3+i) = true := by decide +kernel

theorem strictBool_r2_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (4+i)) 2 (4+i) = true := by decide +kernel

theorem strictBool_r2_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (5+i)) 2 (5+i) = true := by decide +kernel

theorem strictBool_r2_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (6+i)) 2 (6+i) = true := by decide +kernel

theorem strictBool_r2_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (7+i)) 2 (7+i) = true := by decide +kernel

theorem strictBool_r2_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (8+i)) 2 (8+i) = true := by decide +kernel

theorem strictBool_r2_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (9+i)) 2 (9+i) = true := by decide +kernel

theorem strictBool_r2_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (10+i)) 2 (10+i) = true := by decide +kernel

theorem strictBool_r2_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (11+i)) 2 (11+i) = true := by decide +kernel

theorem strictBool_r2_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (12+i)) 2 (12+i) = true := by decide +kernel

theorem strictBool_r2_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (13+i)) 2 (13+i) = true := by decide +kernel

theorem strictBool_r2_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (14+i)) 2 (14+i) = true := by decide +kernel

theorem strictBool_r2_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (15+i)) 2 (15+i) = true := by decide +kernel

theorem strictBool_r2_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (16+i)) 2 (16+i) = true := by decide +kernel

theorem strictBool_r2_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (17+i)) 2 (17+i) = true := by decide +kernel

theorem strictBool_r2_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (18+i)) 2 (18+i) = true := by decide +kernel

theorem strictBool_r2_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (19+i)) 2 (19+i) = true := by decide +kernel

theorem strictBool_r2_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (20+i)) 2 (20+i) = true := by decide +kernel

theorem strictBool_r2_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (21+i)) 2 (21+i) = true := by decide +kernel

theorem strictBool_r2_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (22+i)) 2 (22+i) = true := by decide +kernel

theorem strictBool_r2_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (23+i)) 2 (23+i) = true := by decide +kernel

theorem strictBool_r2_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (24+i)) 2 (24+i) = true := by decide +kernel

theorem strictBool_r2_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (25+i)) 2 (25+i) = true := by decide +kernel

theorem strictBool_r2_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (26+i)) 2 (26+i) = true := by decide +kernel

theorem strictBool_r2_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (27+i)) 2 (27+i) = true := by decide +kernel

theorem strictBool_r2_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (28+i)) 2 (28+i) = true := by decide +kernel

theorem strictBool_r2_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (29+i)) 2 (29+i) = true := by decide +kernel

theorem strictBool_r2_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (30+i)) 2 (30+i) = true := by decide +kernel

theorem strictBool_r2_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (31+i)) 2 (31+i) = true := by decide +kernel

theorem strictBool_r2_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (32+i)) 2 (32+i) = true := by decide +kernel

theorem strictBool_r2_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (33+i)) 2 (33+i) = true := by decide +kernel

theorem strictBool_r2_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (34+i)) 2 (34+i) = true := by decide +kernel

theorem strictBool_r2_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (35+i)) 2 (35+i) = true := by decide +kernel

theorem strictBool_r2_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (36+i)) 2 (36+i) = true := by decide +kernel

theorem strictBool_r2_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (37+i)) 2 (37+i) = true := by decide +kernel

theorem strictBool_r2_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (38+i)) 2 (38+i) = true := by decide +kernel

theorem strictBool_r2_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (39+i)) 2 (39+i) = true := by decide +kernel

theorem strictBool_r2_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (40+i)) 2 (40+i) = true := by decide +kernel

theorem strictBool_r2_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (41+i)) 2 (41+i) = true := by decide +kernel

theorem strictBool_r2_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (42+i)) 2 (42+i) = true := by decide +kernel

theorem strictBool_r2_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (43+i)) 2 (43+i) = true := by decide +kernel

theorem strictBool_r2_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (44+i)) 2 (44+i) = true := by decide +kernel

theorem strictBool_r2_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (45+i)) 2 (45+i) = true := by decide +kernel

theorem strictBool_r2_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (46+i)) 2 (46+i) = true := by decide +kernel

theorem strictBool_r2_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (47+i)) 2 (47+i) = true := by decide +kernel

theorem strictBool_r2_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (48+i)) 2 (48+i) = true := by decide +kernel

theorem strictBool_r2_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (49+i)) 2 (49+i) = true := by decide +kernel

theorem strictBool_r2_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (50+i)) 2 (50+i) = true := by decide +kernel

theorem strictBool_r2_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (51+i)) 2 (51+i) = true := by decide +kernel

theorem strictBool_r2_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (52+i)) 2 (52+i) = true := by decide +kernel

theorem strictBool_r2_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (53+i)) 2 (53+i) = true := by decide +kernel

theorem strictBool_r2_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (54+i)) 2 (54+i) = true := by decide +kernel

theorem strictBool_r2_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (55+i)) 2 (55+i) = true := by decide +kernel

theorem strictBool_r2_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (56+i)) 2 (56+i) = true := by decide +kernel

theorem strictBool_r2_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (57+i)) 2 (57+i) = true := by decide +kernel

theorem strictBool_r2_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (58+i)) 2 (58+i) = true := by decide +kernel

theorem strictBool_r2_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (59+i)) 2 (59+i) = true := by decide +kernel

theorem strictBool_r2_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (60+i)) 2 (60+i) = true := by decide +kernel

theorem strictBool_r2_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (61+i)) 2 (61+i) = true := by decide +kernel

theorem strictBool_r2_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (62+i)) 2 (62+i) = true := by decide +kernel

theorem strictBool_r2_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (63+i)) 2 (63+i) = true := by decide +kernel

theorem strictBool_r2_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (64+i)) 2 (64+i) = true := by decide +kernel

theorem strictBool_r2_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (65+i)) 2 (65+i) = true := by decide +kernel

theorem strictBool_r2_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (66+i)) 2 (66+i) = true := by decide +kernel

theorem strictBool_r2_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (67+i)) 2 (67+i) = true := by decide +kernel

theorem strictBool_r2_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (68+i)) 2 (68+i) = true := by decide +kernel

theorem strictBool_r2_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (69+i)) 2 (69+i) = true := by decide +kernel

theorem strictBool_r2_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (70+i)) 2 (70+i) = true := by decide +kernel

theorem strictBool_r2_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (71+i)) 2 (71+i) = true := by decide +kernel

theorem strictBool_r2_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (72+i)) 2 (72+i) = true := by decide +kernel

theorem strictBool_r2_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (73+i)) 2 (73+i) = true := by decide +kernel

theorem strictBool_r2_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (74+i)) 2 (74+i) = true := by decide +kernel

theorem strictBool_r2_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (75+i)) 2 (75+i) = true := by decide +kernel

theorem strictBool_r2_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (76+i)) 2 (76+i) = true := by decide +kernel

theorem strictBool_r2_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (77+i)) 2 (77+i) = true := by decide +kernel

theorem strictBool_r2_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (78+i)) 2 (78+i) = true := by decide +kernel

theorem strictBool_r2_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (79+i)) 2 (79+i) = true := by decide +kernel

theorem strictBool_r2_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (80+i)) 2 (80+i) = true := by decide +kernel

theorem strictBool_r2_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (81+i)) 2 (81+i) = true := by decide +kernel

theorem strictBool_r2_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (82+i)) 2 (82+i) = true := by decide +kernel

theorem strictBool_r2_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (83+i)) 2 (83+i) = true := by decide +kernel

theorem strictBool_r2_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (84+i)) 2 (84+i) = true := by decide +kernel

theorem strictBool_r2_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (85+i)) 2 (85+i) = true := by decide +kernel

theorem strictBool_r2_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (86+i)) 2 (86+i) = true := by decide +kernel

theorem strictBool_r2_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (87+i)) 2 (87+i) = true := by decide +kernel

theorem strictBool_r2_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (88+i)) 2 (88+i) = true := by decide +kernel

theorem strictBool_r2_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (89+i)) 2 (89+i) = true := by decide +kernel

theorem strictBool_r2_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (90+i)) 2 (90+i) = true := by decide +kernel

theorem strictBool_r2_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (91+i)) 2 (91+i) = true := by decide +kernel

theorem strictBool_r2_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (92+i)) 2 (92+i) = true := by decide +kernel

theorem strictBool_r2_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (93+i)) 2 (93+i) = true := by decide +kernel

theorem strictBool_r2_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (94+i)) 2 (94+i) = true := by decide +kernel

theorem strictBool_r2_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (95+i)) 2 (95+i) = true := by decide +kernel

theorem strictBool_r2_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (96+i)) 2 (96+i) = true := by decide +kernel

theorem strictBool_r2_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (97+i)) 2 (97+i) = true := by decide +kernel

theorem strictBool_r2_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (98+i)) 2 (98+i) = true := by decide +kernel

theorem strictBool_r2_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (99+i)) 2 (99+i) = true := by decide +kernel

theorem strictBool_r2_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (100+i)) 2 (100+i) = true := by decide +kernel

theorem strictBool_r2_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (101+i)) 2 (101+i) = true := by decide +kernel

theorem strictBool_r2_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (102+i)) 2 (102+i) = true := by decide +kernel

theorem strictBool_r2_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (103+i)) 2 (103+i) = true := by decide +kernel

theorem strictBool_r2_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (104+i)) 2 (104+i) = true := by decide +kernel

theorem strictBool_r2_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (105+i)) 2 (105+i) = true := by decide +kernel

theorem strictBool_r2_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (106+i)) 2 (106+i) = true := by decide +kernel

theorem strictBool_r2_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (107+i)) 2 (107+i) = true := by decide +kernel

theorem strictBool_r2_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (108+i)) 2 (108+i) = true := by decide +kernel

theorem strictBool_r2_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (109+i)) 2 (109+i) = true := by decide +kernel

theorem strictBool_r2_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (110+i)) 2 (110+i) = true := by decide +kernel

theorem strictBool_r2_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (111+i)) 2 (111+i) = true := by decide +kernel

theorem strictBool_r2_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (112+i)) 2 (112+i) = true := by decide +kernel

theorem strictBool_r2_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (113+i)) 2 (113+i) = true := by decide +kernel

theorem strictBool_r2_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (114+i)) 2 (114+i) = true := by decide +kernel

theorem strictBool_r2_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (115+i)) 2 (115+i) = true := by decide +kernel

theorem strictBool_r2_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (116+i)) 2 (116+i) = true := by decide +kernel

theorem strictBool_r2_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (117+i)) 2 (117+i) = true := by decide +kernel

theorem strictBool_r2_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (118+i)) 2 (118+i) = true := by decide +kernel

theorem strictBool_r2_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (119+i)) 2 (119+i) = true := by decide +kernel

theorem strictBool_r2_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (120+i)) 2 (120+i) = true := by decide +kernel

theorem strictBool_r2_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (121+i)) 2 (121+i) = true := by decide +kernel

theorem strictBool_r2_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (122+i)) 2 (122+i) = true := by decide +kernel

theorem strictBool_r2_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (123+i)) 2 (123+i) = true := by decide +kernel

theorem strictBool_r2_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (124+i)) 2 (124+i) = true := by decide +kernel

theorem strictBool_r2_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (125+i)) 2 (125+i) = true := by decide +kernel

theorem strictBool_r2_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (126+i)) 2 (126+i) = true := by decide +kernel

theorem strictBool_r2_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (127+i)) 2 (127+i) = true := by decide +kernel

theorem strictBool_r2_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (128+i)) 2 (128+i) = true := by decide +kernel

theorem strictBool_r2_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (129+i)) 2 (129+i) = true := by decide +kernel

theorem strictBool_r2_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (130+i)) 2 (130+i) = true := by decide +kernel

theorem strictBool_r2_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (131+i)) 2 (131+i) = true := by decide +kernel

theorem strictBool_r2_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (132+i)) 2 (132+i) = true := by decide +kernel

theorem strictBool_r2_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (133+i)) 2 (133+i) = true := by decide +kernel

theorem strictBool_r2_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (134+i)) 2 (134+i) = true := by decide +kernel

theorem strictBool_r2_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (135+i)) 2 (135+i) = true := by decide +kernel

theorem strictBool_r2_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (136+i)) 2 (136+i) = true := by decide +kernel

theorem strictBool_r2_part137 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (137+i)) 2 (137+i) = true := by decide +kernel

theorem strictBool_r2_part138 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (138+i)) 2 (138+i) = true := by decide +kernel

theorem strictBool_r2_part139 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (139+i)) 2 (139+i) = true := by decide +kernel

theorem strictBool_r2_part140 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 2 (140+i)) 2 (140+i) = true := by decide +kernel

theorem strictBool_r2 (V : ℕ) (hV : V ∈ List.range 141) : strictBool (BoundaryTailBaseFastData.row 2 V) 2 V = true := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 70
  · by_cases h0_70 : V < 35
    · by_cases h0_35 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r2_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r2_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r2_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r2_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r2_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r2_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r2_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r2_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r2_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35 : V < 26
        · by_cases h17_26 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r2_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r2_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r2_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26 : V < 24
              · have hi := strictBool_r2_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26 : V < 25
                · have hi := strictBool_r2_part24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35 : V < 30
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r2_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r2_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35 : V < 32
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r2_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35 : V < 33
              · have hi := strictBool_r2_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35 : V < 34
                · have hi := strictBool_r2_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_70 : V < 52
      · by_cases h35_52 : V < 43
        · by_cases h35_43 : V < 39
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r2_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r2_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r2_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r2_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
        · by_cases h43_52 : V < 47
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r2_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r2_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
          · by_cases h47_52 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r2_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_52 : V < 50
              · have hi := strictBool_r2_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · by_cases h50_52 : V < 51
                · have hi := strictBool_r2_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
      · by_cases h52_70 : V < 61
        · by_cases h52_61 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r2_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r2_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
          · by_cases h56_61 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r2_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_61 : V < 59
              · have hi := strictBool_r2_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · by_cases h59_61 : V < 60
                · have hi := strictBool_r2_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
        · by_cases h61_70 : V < 65
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r2_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r2_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
          · by_cases h65_70 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r2_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_70 : V < 68
              · have hi := strictBool_r2_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · by_cases h68_70 : V < 69
                · have hi := strictBool_r2_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
  · by_cases h70_141 : V < 105
    · by_cases h70_105 : V < 87
      · by_cases h70_87 : V < 78
        · by_cases h70_78 : V < 74
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r2_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r2_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r2_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r2_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
        · by_cases h78_87 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r2_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r2_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
          · by_cases h82_87 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r2_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_87 : V < 85
              · have hi := strictBool_r2_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · by_cases h85_87 : V < 86
                · have hi := strictBool_r2_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
      · by_cases h87_105 : V < 96
        · by_cases h87_96 : V < 91
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r2_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r2_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
          · by_cases h91_96 : V < 93
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r2_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_96 : V < 94
              · have hi := strictBool_r2_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · by_cases h94_96 : V < 95
                · have hi := strictBool_r2_part94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
        · by_cases h96_105 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r2_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r2_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_105 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r2_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_105 : V < 103
              · have hi := strictBool_r2_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · by_cases h103_105 : V < 104
                · have hi := strictBool_r2_part103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
    · by_cases h105_141 : V < 123
      · by_cases h105_123 : V < 114
        · by_cases h105_114 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r2_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r2_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_114 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r2_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_114 : V < 112
              · have hi := strictBool_r2_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · by_cases h112_114 : V < 113
                · have hi := strictBool_r2_part112 (V-112) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part113 (V-113) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
        · by_cases h114_123 : V < 118
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r2_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r2_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
          · by_cases h118_123 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r2_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_123 : V < 121
              · have hi := strictBool_r2_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · by_cases h121_123 : V < 122
                · have hi := strictBool_r2_part121 (V-121) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part122 (V-122) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
      · by_cases h123_141 : V < 132
        · by_cases h123_132 : V < 127
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r2_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r2_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
          · by_cases h127_132 : V < 129
            · by_cases h127_129 : V < 128
              · have hi := strictBool_r2_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_132 : V < 130
              · have hi := strictBool_r2_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · by_cases h130_132 : V < 131
                · have hi := strictBool_r2_part130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
        · by_cases h132_141 : V < 136
          · by_cases h132_136 : V < 134
            · by_cases h132_134 : V < 133
              · have hi := strictBool_r2_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
            · by_cases h134_136 : V < 135
              · have hi := strictBool_r2_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
          · by_cases h136_141 : V < 138
            · by_cases h136_138 : V < 137
              · have hi := strictBool_r2_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
              · have hi := strictBool_r2_part137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
            · by_cases h138_141 : V < 139
              · have hi := strictBool_r2_part138 (V-138) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
              · by_cases h139_141 : V < 140
                · have hi := strictBool_r2_part139 (V-139) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi
                · have hi := strictBool_r2_part140 (V-140) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi

theorem strictFast_r2 (V : ℕ) (hV : V ∈ List.range 141) : StrictAtFast (BoundaryTailBaseFastData.row 2 V) 2 V :=
  strictBool_sound _ _ _ (strictBool_r2 V hV)

theorem strict_r2 (V : ℕ) (hV : V ∈ List.range 141) : StrictCheckAt 2 V :=
  strictAtFast_sound _ _ _ (valid_r2 V hV) (strictFast_r2 V hV)

theorem zeroCertificate_r2_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (0+i)) 2 (0+i) := by decide +kernel

theorem zeroCertificate_r2_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (8+i)) 2 (8+i) := by decide +kernel

theorem zeroCertificate_r2_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (16+i)) 2 (16+i) := by decide +kernel

theorem zeroCertificate_r2_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (24+i)) 2 (24+i) := by decide +kernel

theorem zeroCertificate_r2_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (32+i)) 2 (32+i) := by decide +kernel

theorem zeroCertificate_r2_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (40+i)) 2 (40+i) := by decide +kernel

theorem zeroCertificate_r2_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (48+i)) 2 (48+i) := by decide +kernel

theorem zeroCertificate_r2_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (56+i)) 2 (56+i) := by decide +kernel

theorem zeroCertificate_r2_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (64+i)) 2 (64+i) := by decide +kernel

theorem zeroCertificate_r2_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (72+i)) 2 (72+i) := by decide +kernel

theorem zeroCertificate_r2_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (80+i)) 2 (80+i) := by decide +kernel

theorem zeroCertificate_r2_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (88+i)) 2 (88+i) := by decide +kernel

theorem zeroCertificate_r2_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (96+i)) 2 (96+i) := by decide +kernel

theorem zeroCertificate_r2_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (104+i)) 2 (104+i) := by decide +kernel

theorem zeroCertificate_r2_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (112+i)) 2 (112+i) := by decide +kernel

theorem zeroCertificate_r2_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (120+i)) 2 (120+i) := by decide +kernel

theorem zeroCertificate_r2_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 2 (128+i)) 2 (128+i) := by decide +kernel

theorem zeroCertificate_r2_part136 : ∀ i ∈ List.range 5, ZeroCertificate (BoundaryTailBaseFastData.row 2 (136+i)) 2 (136+i) := by decide +kernel

theorem zeroCertificate_r2 (V : ℕ) (hV : V ∈ List.range 141) : ZeroCertificate (BoundaryTailBaseFastData.row 2 V) 2 V := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := zeroCertificate_r2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := zeroCertificate_r2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r2 (V : ℕ) (hV : V ∈ List.range 141) : ZeroAtFast 2 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r2 V hV) (zeroCertificate_r2 V hV)

theorem zero_r2 (V : ℕ) (hV : V ∈ List.range 141) : ZeroCheckAt 2 V :=
  zeroAtFast_sound _ _ (zeroFast_r2 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r6_part0 : ∀ i ∈ List.range 8, CorrectAt 6 (0+i) := by decide +kernel

theorem correct_r6_part8 : ∀ i ∈ List.range 8, CorrectAt 6 (8+i) := by decide +kernel

theorem correct_r6_part16 : ∀ i ∈ List.range 8, CorrectAt 6 (16+i) := by decide +kernel

theorem correct_r6_part24 : ∀ i ∈ List.range 8, CorrectAt 6 (24+i) := by decide +kernel

theorem correct_r6_part32 : ∀ i ∈ List.range 8, CorrectAt 6 (32+i) := by decide +kernel

theorem correct_r6_part40 : ∀ i ∈ List.range 8, CorrectAt 6 (40+i) := by decide +kernel

theorem correct_r6_part48 : ∀ i ∈ List.range 8, CorrectAt 6 (48+i) := by decide +kernel

theorem correct_r6_part56 : ∀ i ∈ List.range 8, CorrectAt 6 (56+i) := by decide +kernel

theorem correct_r6_part64 : ∀ i ∈ List.range 8, CorrectAt 6 (64+i) := by decide +kernel

theorem correct_r6_part72 : ∀ i ∈ List.range 8, CorrectAt 6 (72+i) := by decide +kernel

theorem correct_r6_part80 : ∀ i ∈ List.range 8, CorrectAt 6 (80+i) := by decide +kernel

theorem correct_r6_part88 : ∀ i ∈ List.range 8, CorrectAt 6 (88+i) := by decide +kernel

theorem correct_r6_part96 : ∀ i ∈ List.range 8, CorrectAt 6 (96+i) := by decide +kernel

theorem correct_r6_part104 : ∀ i ∈ List.range 8, CorrectAt 6 (104+i) := by decide +kernel

theorem correct_r6_part112 : ∀ i ∈ List.range 8, CorrectAt 6 (112+i) := by decide +kernel

theorem correct_r6_part120 : ∀ i ∈ List.range 8, CorrectAt 6 (120+i) := by decide +kernel

theorem correct_r6_part128 : ∀ i ∈ List.range 8, CorrectAt 6 (128+i) := by decide +kernel

theorem correct_r6_part136 : ∀ i ∈ List.range 1, CorrectAt 6 (136+i) := by decide +kernel

theorem correct_r6 (V : ℕ) (hV : V ∈ List.range 137) : CorrectAt 6 V := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := correct_r6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := correct_r6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r6_part0 : ∀ i ∈ List.range 8, BaseCheckAt 6 (0+i) := by decide +kernel

theorem base_r6_part8 : ∀ i ∈ List.range 8, BaseCheckAt 6 (8+i) := by decide +kernel

theorem base_r6_part16 : ∀ i ∈ List.range 8, BaseCheckAt 6 (16+i) := by decide +kernel

theorem base_r6_part24 : ∀ i ∈ List.range 8, BaseCheckAt 6 (24+i) := by decide +kernel

theorem base_r6_part32 : ∀ i ∈ List.range 8, BaseCheckAt 6 (32+i) := by decide +kernel

theorem base_r6_part40 : ∀ i ∈ List.range 8, BaseCheckAt 6 (40+i) := by decide +kernel

theorem base_r6_part48 : ∀ i ∈ List.range 8, BaseCheckAt 6 (48+i) := by decide +kernel

theorem base_r6_part56 : ∀ i ∈ List.range 8, BaseCheckAt 6 (56+i) := by decide +kernel

theorem base_r6_part64 : ∀ i ∈ List.range 8, BaseCheckAt 6 (64+i) := by decide +kernel

theorem base_r6_part72 : ∀ i ∈ List.range 8, BaseCheckAt 6 (72+i) := by decide +kernel

theorem base_r6_part80 : ∀ i ∈ List.range 8, BaseCheckAt 6 (80+i) := by decide +kernel

theorem base_r6_part88 : ∀ i ∈ List.range 8, BaseCheckAt 6 (88+i) := by decide +kernel

theorem base_r6_part96 : ∀ i ∈ List.range 8, BaseCheckAt 6 (96+i) := by decide +kernel

theorem base_r6_part104 : ∀ i ∈ List.range 8, BaseCheckAt 6 (104+i) := by decide +kernel

theorem base_r6_part112 : ∀ i ∈ List.range 8, BaseCheckAt 6 (112+i) := by decide +kernel

theorem base_r6_part120 : ∀ i ∈ List.range 8, BaseCheckAt 6 (120+i) := by decide +kernel

theorem base_r6_part128 : ∀ i ∈ List.range 8, BaseCheckAt 6 (128+i) := by decide +kernel

theorem base_r6_part136 : ∀ i ∈ List.range 1, BaseCheckAt 6 (136+i) := by decide +kernel

theorem base_r6 (V : ℕ) (hV : V ∈ List.range 137) : BaseCheckAt 6 V := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := base_r6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := base_r6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r6_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (0+i)) 6 (0+i) := by decide +kernel

theorem valid_r6_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (8+i)) 6 (8+i) := by decide +kernel

theorem valid_r6_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (16+i)) 6 (16+i) := by decide +kernel

theorem valid_r6_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (24+i)) 6 (24+i) := by decide +kernel

theorem valid_r6_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (32+i)) 6 (32+i) := by decide +kernel

theorem valid_r6_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (40+i)) 6 (40+i) := by decide +kernel

theorem valid_r6_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (48+i)) 6 (48+i) := by decide +kernel

theorem valid_r6_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (56+i)) 6 (56+i) := by decide +kernel

theorem valid_r6_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (64+i)) 6 (64+i) := by decide +kernel

theorem valid_r6_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (72+i)) 6 (72+i) := by decide +kernel

theorem valid_r6_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (80+i)) 6 (80+i) := by decide +kernel

theorem valid_r6_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (88+i)) 6 (88+i) := by decide +kernel

theorem valid_r6_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (96+i)) 6 (96+i) := by decide +kernel

theorem valid_r6_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (104+i)) 6 (104+i) := by decide +kernel

theorem valid_r6_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (112+i)) 6 (112+i) := by decide +kernel

theorem valid_r6_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (120+i)) 6 (120+i) := by decide +kernel

theorem valid_r6_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 6 (128+i)) 6 (128+i) := by decide +kernel

theorem valid_r6_part136 : ∀ i ∈ List.range 1, Valid (BoundaryTailBaseFastData.row 6 (136+i)) 6 (136+i) := by decide +kernel

theorem valid_r6 (V : ℕ) (hV : V ∈ List.range 137) : Valid (BoundaryTailBaseFastData.row 6 V) 6 V := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := valid_r6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := valid_r6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r6_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (0+i)) 6 (0+i) = true := by decide +kernel

theorem strictBool_r6_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (1+i)) 6 (1+i) = true := by decide +kernel

theorem strictBool_r6_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (2+i)) 6 (2+i) = true := by decide +kernel

theorem strictBool_r6_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (3+i)) 6 (3+i) = true := by decide +kernel

theorem strictBool_r6_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (4+i)) 6 (4+i) = true := by decide +kernel

theorem strictBool_r6_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (5+i)) 6 (5+i) = true := by decide +kernel

theorem strictBool_r6_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (6+i)) 6 (6+i) = true := by decide +kernel

theorem strictBool_r6_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (7+i)) 6 (7+i) = true := by decide +kernel

theorem strictBool_r6_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (8+i)) 6 (8+i) = true := by decide +kernel

theorem strictBool_r6_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (9+i)) 6 (9+i) = true := by decide +kernel

theorem strictBool_r6_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (10+i)) 6 (10+i) = true := by decide +kernel

theorem strictBool_r6_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (11+i)) 6 (11+i) = true := by decide +kernel

theorem strictBool_r6_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (12+i)) 6 (12+i) = true := by decide +kernel

theorem strictBool_r6_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (13+i)) 6 (13+i) = true := by decide +kernel

theorem strictBool_r6_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (14+i)) 6 (14+i) = true := by decide +kernel

theorem strictBool_r6_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (15+i)) 6 (15+i) = true := by decide +kernel

theorem strictBool_r6_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (16+i)) 6 (16+i) = true := by decide +kernel

theorem strictBool_r6_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (17+i)) 6 (17+i) = true := by decide +kernel

theorem strictBool_r6_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (18+i)) 6 (18+i) = true := by decide +kernel

theorem strictBool_r6_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (19+i)) 6 (19+i) = true := by decide +kernel

theorem strictBool_r6_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (20+i)) 6 (20+i) = true := by decide +kernel

theorem strictBool_r6_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (21+i)) 6 (21+i) = true := by decide +kernel

theorem strictBool_r6_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (22+i)) 6 (22+i) = true := by decide +kernel

theorem strictBool_r6_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (23+i)) 6 (23+i) = true := by decide +kernel

theorem strictBool_r6_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (24+i)) 6 (24+i) = true := by decide +kernel

theorem strictBool_r6_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (25+i)) 6 (25+i) = true := by decide +kernel

theorem strictBool_r6_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (26+i)) 6 (26+i) = true := by decide +kernel

theorem strictBool_r6_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (27+i)) 6 (27+i) = true := by decide +kernel

theorem strictBool_r6_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (28+i)) 6 (28+i) = true := by decide +kernel

theorem strictBool_r6_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (29+i)) 6 (29+i) = true := by decide +kernel

theorem strictBool_r6_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (30+i)) 6 (30+i) = true := by decide +kernel

theorem strictBool_r6_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (31+i)) 6 (31+i) = true := by decide +kernel

theorem strictBool_r6_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (32+i)) 6 (32+i) = true := by decide +kernel

theorem strictBool_r6_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (33+i)) 6 (33+i) = true := by decide +kernel

theorem strictBool_r6_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (34+i)) 6 (34+i) = true := by decide +kernel

theorem strictBool_r6_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (35+i)) 6 (35+i) = true := by decide +kernel

theorem strictBool_r6_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (36+i)) 6 (36+i) = true := by decide +kernel

theorem strictBool_r6_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (37+i)) 6 (37+i) = true := by decide +kernel

theorem strictBool_r6_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (38+i)) 6 (38+i) = true := by decide +kernel

theorem strictBool_r6_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (39+i)) 6 (39+i) = true := by decide +kernel

theorem strictBool_r6_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (40+i)) 6 (40+i) = true := by decide +kernel

theorem strictBool_r6_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (41+i)) 6 (41+i) = true := by decide +kernel

theorem strictBool_r6_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (42+i)) 6 (42+i) = true := by decide +kernel

theorem strictBool_r6_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (43+i)) 6 (43+i) = true := by decide +kernel

theorem strictBool_r6_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (44+i)) 6 (44+i) = true := by decide +kernel

theorem strictBool_r6_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (45+i)) 6 (45+i) = true := by decide +kernel

theorem strictBool_r6_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (46+i)) 6 (46+i) = true := by decide +kernel

theorem strictBool_r6_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (47+i)) 6 (47+i) = true := by decide +kernel

theorem strictBool_r6_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (48+i)) 6 (48+i) = true := by decide +kernel

theorem strictBool_r6_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (49+i)) 6 (49+i) = true := by decide +kernel

theorem strictBool_r6_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (50+i)) 6 (50+i) = true := by decide +kernel

theorem strictBool_r6_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (51+i)) 6 (51+i) = true := by decide +kernel

theorem strictBool_r6_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (52+i)) 6 (52+i) = true := by decide +kernel

theorem strictBool_r6_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (53+i)) 6 (53+i) = true := by decide +kernel

theorem strictBool_r6_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (54+i)) 6 (54+i) = true := by decide +kernel

theorem strictBool_r6_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (55+i)) 6 (55+i) = true := by decide +kernel

theorem strictBool_r6_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (56+i)) 6 (56+i) = true := by decide +kernel

theorem strictBool_r6_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (57+i)) 6 (57+i) = true := by decide +kernel

theorem strictBool_r6_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (58+i)) 6 (58+i) = true := by decide +kernel

theorem strictBool_r6_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (59+i)) 6 (59+i) = true := by decide +kernel

theorem strictBool_r6_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (60+i)) 6 (60+i) = true := by decide +kernel

theorem strictBool_r6_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (61+i)) 6 (61+i) = true := by decide +kernel

theorem strictBool_r6_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (62+i)) 6 (62+i) = true := by decide +kernel

theorem strictBool_r6_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (63+i)) 6 (63+i) = true := by decide +kernel

theorem strictBool_r6_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (64+i)) 6 (64+i) = true := by decide +kernel

theorem strictBool_r6_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (65+i)) 6 (65+i) = true := by decide +kernel

theorem strictBool_r6_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (66+i)) 6 (66+i) = true := by decide +kernel

theorem strictBool_r6_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (67+i)) 6 (67+i) = true := by decide +kernel

theorem strictBool_r6_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (68+i)) 6 (68+i) = true := by decide +kernel

theorem strictBool_r6_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (69+i)) 6 (69+i) = true := by decide +kernel

theorem strictBool_r6_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (70+i)) 6 (70+i) = true := by decide +kernel

theorem strictBool_r6_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (71+i)) 6 (71+i) = true := by decide +kernel

theorem strictBool_r6_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (72+i)) 6 (72+i) = true := by decide +kernel

theorem strictBool_r6_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (73+i)) 6 (73+i) = true := by decide +kernel

theorem strictBool_r6_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (74+i)) 6 (74+i) = true := by decide +kernel

theorem strictBool_r6_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (75+i)) 6 (75+i) = true := by decide +kernel

theorem strictBool_r6_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (76+i)) 6 (76+i) = true := by decide +kernel

theorem strictBool_r6_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (77+i)) 6 (77+i) = true := by decide +kernel

theorem strictBool_r6_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (78+i)) 6 (78+i) = true := by decide +kernel

theorem strictBool_r6_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (79+i)) 6 (79+i) = true := by decide +kernel

theorem strictBool_r6_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (80+i)) 6 (80+i) = true := by decide +kernel

theorem strictBool_r6_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (81+i)) 6 (81+i) = true := by decide +kernel

theorem strictBool_r6_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (82+i)) 6 (82+i) = true := by decide +kernel

theorem strictBool_r6_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (83+i)) 6 (83+i) = true := by decide +kernel

theorem strictBool_r6_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (84+i)) 6 (84+i) = true := by decide +kernel

theorem strictBool_r6_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (85+i)) 6 (85+i) = true := by decide +kernel

theorem strictBool_r6_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (86+i)) 6 (86+i) = true := by decide +kernel

theorem strictBool_r6_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (87+i)) 6 (87+i) = true := by decide +kernel

theorem strictBool_r6_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (88+i)) 6 (88+i) = true := by decide +kernel

theorem strictBool_r6_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (89+i)) 6 (89+i) = true := by decide +kernel

theorem strictBool_r6_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (90+i)) 6 (90+i) = true := by decide +kernel

theorem strictBool_r6_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (91+i)) 6 (91+i) = true := by decide +kernel

theorem strictBool_r6_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (92+i)) 6 (92+i) = true := by decide +kernel

theorem strictBool_r6_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (93+i)) 6 (93+i) = true := by decide +kernel

theorem strictBool_r6_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (94+i)) 6 (94+i) = true := by decide +kernel

theorem strictBool_r6_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (95+i)) 6 (95+i) = true := by decide +kernel

theorem strictBool_r6_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (96+i)) 6 (96+i) = true := by decide +kernel

theorem strictBool_r6_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (97+i)) 6 (97+i) = true := by decide +kernel

theorem strictBool_r6_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (98+i)) 6 (98+i) = true := by decide +kernel

theorem strictBool_r6_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (99+i)) 6 (99+i) = true := by decide +kernel

theorem strictBool_r6_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (100+i)) 6 (100+i) = true := by decide +kernel

theorem strictBool_r6_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (101+i)) 6 (101+i) = true := by decide +kernel

theorem strictBool_r6_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (102+i)) 6 (102+i) = true := by decide +kernel

theorem strictBool_r6_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (103+i)) 6 (103+i) = true := by decide +kernel

theorem strictBool_r6_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (104+i)) 6 (104+i) = true := by decide +kernel

theorem strictBool_r6_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (105+i)) 6 (105+i) = true := by decide +kernel

theorem strictBool_r6_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (106+i)) 6 (106+i) = true := by decide +kernel

theorem strictBool_r6_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (107+i)) 6 (107+i) = true := by decide +kernel

theorem strictBool_r6_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (108+i)) 6 (108+i) = true := by decide +kernel

theorem strictBool_r6_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (109+i)) 6 (109+i) = true := by decide +kernel

theorem strictBool_r6_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (110+i)) 6 (110+i) = true := by decide +kernel

theorem strictBool_r6_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (111+i)) 6 (111+i) = true := by decide +kernel

theorem strictBool_r6_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (112+i)) 6 (112+i) = true := by decide +kernel

theorem strictBool_r6_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (113+i)) 6 (113+i) = true := by decide +kernel

theorem strictBool_r6_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (114+i)) 6 (114+i) = true := by decide +kernel

theorem strictBool_r6_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (115+i)) 6 (115+i) = true := by decide +kernel

theorem strictBool_r6_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (116+i)) 6 (116+i) = true := by decide +kernel

theorem strictBool_r6_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (117+i)) 6 (117+i) = true := by decide +kernel

theorem strictBool_r6_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (118+i)) 6 (118+i) = true := by decide +kernel

theorem strictBool_r6_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (119+i)) 6 (119+i) = true := by decide +kernel

theorem strictBool_r6_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (120+i)) 6 (120+i) = true := by decide +kernel

theorem strictBool_r6_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (121+i)) 6 (121+i) = true := by decide +kernel

theorem strictBool_r6_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (122+i)) 6 (122+i) = true := by decide +kernel

theorem strictBool_r6_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (123+i)) 6 (123+i) = true := by decide +kernel

theorem strictBool_r6_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (124+i)) 6 (124+i) = true := by decide +kernel

theorem strictBool_r6_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (125+i)) 6 (125+i) = true := by decide +kernel

theorem strictBool_r6_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (126+i)) 6 (126+i) = true := by decide +kernel

theorem strictBool_r6_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (127+i)) 6 (127+i) = true := by decide +kernel

theorem strictBool_r6_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (128+i)) 6 (128+i) = true := by decide +kernel

theorem strictBool_r6_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (129+i)) 6 (129+i) = true := by decide +kernel

theorem strictBool_r6_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (130+i)) 6 (130+i) = true := by decide +kernel

theorem strictBool_r6_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (131+i)) 6 (131+i) = true := by decide +kernel

theorem strictBool_r6_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (132+i)) 6 (132+i) = true := by decide +kernel

theorem strictBool_r6_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (133+i)) 6 (133+i) = true := by decide +kernel

theorem strictBool_r6_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (134+i)) 6 (134+i) = true := by decide +kernel

theorem strictBool_r6_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (135+i)) 6 (135+i) = true := by decide +kernel

theorem strictBool_r6_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 6 (136+i)) 6 (136+i) = true := by decide +kernel

theorem strictBool_r6 (V : ℕ) (hV : V ∈ List.range 137) : strictBool (BoundaryTailBaseFastData.row 6 V) 6 V = true := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r6_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r6_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r6_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r6_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r6_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r6_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r6_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r6_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r6_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r6_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r6_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r6_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r6_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r6_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r6_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r6_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strictBool_r6_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strictBool_r6_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r6_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r6_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r6_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r6_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r6_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r6_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r6_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strictBool_r6_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strictBool_r6_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r6_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r6_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r6_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r6_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r6_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r6_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r6_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_68 : V < 66
              · have hi := strictBool_r6_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · by_cases h66_68 : V < 67
                · have hi := strictBool_r6_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
  · by_cases h68_137 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r6_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r6_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r6_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r6_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r6_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r6_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r6_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_85 : V < 83
              · have hi := strictBool_r6_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · by_cases h83_85 : V < 84
                · have hi := strictBool_r6_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r6_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r6_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r6_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r6_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r6_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r6_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r6_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_102 : V < 100
              · have hi := strictBool_r6_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · by_cases h100_102 : V < 101
                · have hi := strictBool_r6_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
    · by_cases h102_137 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r6_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r6_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r6_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r6_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r6_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r6_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r6_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_119 : V < 117
              · have hi := strictBool_r6_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · by_cases h117_119 : V < 118
                · have hi := strictBool_r6_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
      · by_cases h119_137 : V < 128
        · by_cases h119_128 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r6_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r6_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_128 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r6_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_128 : V < 126
              · have hi := strictBool_r6_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · by_cases h126_128 : V < 127
                · have hi := strictBool_r6_part126 (V-126) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part127 (V-127) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 132
          · by_cases h128_132 : V < 130
            · by_cases h128_130 : V < 129
              · have hi := strictBool_r6_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_132 : V < 131
              · have hi := strictBool_r6_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
          · by_cases h132_137 : V < 134
            · by_cases h132_134 : V < 133
              · have hi := strictBool_r6_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
              · have hi := strictBool_r6_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
            · by_cases h134_137 : V < 135
              · have hi := strictBool_r6_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
              · by_cases h135_137 : V < 136
                · have hi := strictBool_r6_part135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
                · have hi := strictBool_r6_part136 (V-136) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictFast_r6 (V : ℕ) (hV : V ∈ List.range 137) : StrictAtFast (BoundaryTailBaseFastData.row 6 V) 6 V :=
  strictBool_sound _ _ _ (strictBool_r6 V hV)

theorem strict_r6 (V : ℕ) (hV : V ∈ List.range 137) : StrictCheckAt 6 V :=
  strictAtFast_sound _ _ _ (valid_r6 V hV) (strictFast_r6 V hV)

theorem zeroCertificate_r6_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (0+i)) 6 (0+i) := by decide +kernel

theorem zeroCertificate_r6_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (8+i)) 6 (8+i) := by decide +kernel

theorem zeroCertificate_r6_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (16+i)) 6 (16+i) := by decide +kernel

theorem zeroCertificate_r6_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (24+i)) 6 (24+i) := by decide +kernel

theorem zeroCertificate_r6_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (32+i)) 6 (32+i) := by decide +kernel

theorem zeroCertificate_r6_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (40+i)) 6 (40+i) := by decide +kernel

theorem zeroCertificate_r6_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (48+i)) 6 (48+i) := by decide +kernel

theorem zeroCertificate_r6_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (56+i)) 6 (56+i) := by decide +kernel

theorem zeroCertificate_r6_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (64+i)) 6 (64+i) := by decide +kernel

theorem zeroCertificate_r6_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (72+i)) 6 (72+i) := by decide +kernel

theorem zeroCertificate_r6_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (80+i)) 6 (80+i) := by decide +kernel

theorem zeroCertificate_r6_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (88+i)) 6 (88+i) := by decide +kernel

theorem zeroCertificate_r6_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (96+i)) 6 (96+i) := by decide +kernel

theorem zeroCertificate_r6_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (104+i)) 6 (104+i) := by decide +kernel

theorem zeroCertificate_r6_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (112+i)) 6 (112+i) := by decide +kernel

theorem zeroCertificate_r6_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (120+i)) 6 (120+i) := by decide +kernel

theorem zeroCertificate_r6_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 6 (128+i)) 6 (128+i) := by decide +kernel

theorem zeroCertificate_r6_part136 : ∀ i ∈ List.range 1, ZeroCertificate (BoundaryTailBaseFastData.row 6 (136+i)) 6 (136+i) := by decide +kernel

theorem zeroCertificate_r6 (V : ℕ) (hV : V ∈ List.range 137) : ZeroCertificate (BoundaryTailBaseFastData.row 6 V) 6 V := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := zeroCertificate_r6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := zeroCertificate_r6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r6 (V : ℕ) (hV : V ∈ List.range 137) : ZeroAtFast 6 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r6 V hV) (zeroCertificate_r6 V hV)

theorem zero_r6 (V : ℕ) (hV : V ∈ List.range 137) : ZeroCheckAt 6 V :=
  zeroAtFast_sound _ _ (zeroFast_r6 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r10_part0 : ∀ i ∈ List.range 8, CorrectAt 10 (0+i) := by decide +kernel

theorem correct_r10_part8 : ∀ i ∈ List.range 8, CorrectAt 10 (8+i) := by decide +kernel

theorem correct_r10_part16 : ∀ i ∈ List.range 8, CorrectAt 10 (16+i) := by decide +kernel

theorem correct_r10_part24 : ∀ i ∈ List.range 8, CorrectAt 10 (24+i) := by decide +kernel

theorem correct_r10_part32 : ∀ i ∈ List.range 8, CorrectAt 10 (32+i) := by decide +kernel

theorem correct_r10_part40 : ∀ i ∈ List.range 8, CorrectAt 10 (40+i) := by decide +kernel

theorem correct_r10_part48 : ∀ i ∈ List.range 8, CorrectAt 10 (48+i) := by decide +kernel

theorem correct_r10_part56 : ∀ i ∈ List.range 8, CorrectAt 10 (56+i) := by decide +kernel

theorem correct_r10_part64 : ∀ i ∈ List.range 8, CorrectAt 10 (64+i) := by decide +kernel

theorem correct_r10_part72 : ∀ i ∈ List.range 8, CorrectAt 10 (72+i) := by decide +kernel

theorem correct_r10_part80 : ∀ i ∈ List.range 8, CorrectAt 10 (80+i) := by decide +kernel

theorem correct_r10_part88 : ∀ i ∈ List.range 8, CorrectAt 10 (88+i) := by decide +kernel

theorem correct_r10_part96 : ∀ i ∈ List.range 8, CorrectAt 10 (96+i) := by decide +kernel

theorem correct_r10_part104 : ∀ i ∈ List.range 8, CorrectAt 10 (104+i) := by decide +kernel

theorem correct_r10_part112 : ∀ i ∈ List.range 8, CorrectAt 10 (112+i) := by decide +kernel

theorem correct_r10_part120 : ∀ i ∈ List.range 8, CorrectAt 10 (120+i) := by decide +kernel

theorem correct_r10_part128 : ∀ i ∈ List.range 5, CorrectAt 10 (128+i) := by decide +kernel

theorem correct_r10 (V : ℕ) (hV : V ∈ List.range 133) : CorrectAt 10 V := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := correct_r10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := correct_r10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r10_part0 : ∀ i ∈ List.range 8, BaseCheckAt 10 (0+i) := by decide +kernel

theorem base_r10_part8 : ∀ i ∈ List.range 8, BaseCheckAt 10 (8+i) := by decide +kernel

theorem base_r10_part16 : ∀ i ∈ List.range 8, BaseCheckAt 10 (16+i) := by decide +kernel

theorem base_r10_part24 : ∀ i ∈ List.range 8, BaseCheckAt 10 (24+i) := by decide +kernel

theorem base_r10_part32 : ∀ i ∈ List.range 8, BaseCheckAt 10 (32+i) := by decide +kernel

theorem base_r10_part40 : ∀ i ∈ List.range 8, BaseCheckAt 10 (40+i) := by decide +kernel

theorem base_r10_part48 : ∀ i ∈ List.range 8, BaseCheckAt 10 (48+i) := by decide +kernel

theorem base_r10_part56 : ∀ i ∈ List.range 8, BaseCheckAt 10 (56+i) := by decide +kernel

theorem base_r10_part64 : ∀ i ∈ List.range 8, BaseCheckAt 10 (64+i) := by decide +kernel

theorem base_r10_part72 : ∀ i ∈ List.range 8, BaseCheckAt 10 (72+i) := by decide +kernel

theorem base_r10_part80 : ∀ i ∈ List.range 8, BaseCheckAt 10 (80+i) := by decide +kernel

theorem base_r10_part88 : ∀ i ∈ List.range 8, BaseCheckAt 10 (88+i) := by decide +kernel

theorem base_r10_part96 : ∀ i ∈ List.range 8, BaseCheckAt 10 (96+i) := by decide +kernel

theorem base_r10_part104 : ∀ i ∈ List.range 8, BaseCheckAt 10 (104+i) := by decide +kernel

theorem base_r10_part112 : ∀ i ∈ List.range 8, BaseCheckAt 10 (112+i) := by decide +kernel

theorem base_r10_part120 : ∀ i ∈ List.range 8, BaseCheckAt 10 (120+i) := by decide +kernel

theorem base_r10_part128 : ∀ i ∈ List.range 5, BaseCheckAt 10 (128+i) := by decide +kernel

theorem base_r10 (V : ℕ) (hV : V ∈ List.range 133) : BaseCheckAt 10 V := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := base_r10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := base_r10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r10_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (0+i)) 10 (0+i) := by decide +kernel

theorem valid_r10_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (8+i)) 10 (8+i) := by decide +kernel

theorem valid_r10_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (16+i)) 10 (16+i) := by decide +kernel

theorem valid_r10_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (24+i)) 10 (24+i) := by decide +kernel

theorem valid_r10_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (32+i)) 10 (32+i) := by decide +kernel

theorem valid_r10_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (40+i)) 10 (40+i) := by decide +kernel

theorem valid_r10_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (48+i)) 10 (48+i) := by decide +kernel

theorem valid_r10_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (56+i)) 10 (56+i) := by decide +kernel

theorem valid_r10_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (64+i)) 10 (64+i) := by decide +kernel

theorem valid_r10_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (72+i)) 10 (72+i) := by decide +kernel

theorem valid_r10_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (80+i)) 10 (80+i) := by decide +kernel

theorem valid_r10_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (88+i)) 10 (88+i) := by decide +kernel

theorem valid_r10_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (96+i)) 10 (96+i) := by decide +kernel

theorem valid_r10_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (104+i)) 10 (104+i) := by decide +kernel

theorem valid_r10_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (112+i)) 10 (112+i) := by decide +kernel

theorem valid_r10_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 10 (120+i)) 10 (120+i) := by decide +kernel

theorem valid_r10_part128 : ∀ i ∈ List.range 5, Valid (BoundaryTailBaseFastData.row 10 (128+i)) 10 (128+i) := by decide +kernel

theorem valid_r10 (V : ℕ) (hV : V ∈ List.range 133) : Valid (BoundaryTailBaseFastData.row 10 V) 10 V := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := valid_r10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := valid_r10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r10_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (0+i)) 10 (0+i) = true := by decide +kernel

theorem strictBool_r10_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (1+i)) 10 (1+i) = true := by decide +kernel

theorem strictBool_r10_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (2+i)) 10 (2+i) = true := by decide +kernel

theorem strictBool_r10_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (3+i)) 10 (3+i) = true := by decide +kernel

theorem strictBool_r10_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (4+i)) 10 (4+i) = true := by decide +kernel

theorem strictBool_r10_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (5+i)) 10 (5+i) = true := by decide +kernel

theorem strictBool_r10_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (6+i)) 10 (6+i) = true := by decide +kernel

theorem strictBool_r10_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (7+i)) 10 (7+i) = true := by decide +kernel

theorem strictBool_r10_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (8+i)) 10 (8+i) = true := by decide +kernel

theorem strictBool_r10_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (9+i)) 10 (9+i) = true := by decide +kernel

theorem strictBool_r10_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (10+i)) 10 (10+i) = true := by decide +kernel

theorem strictBool_r10_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (11+i)) 10 (11+i) = true := by decide +kernel

theorem strictBool_r10_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (12+i)) 10 (12+i) = true := by decide +kernel

theorem strictBool_r10_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (13+i)) 10 (13+i) = true := by decide +kernel

theorem strictBool_r10_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (14+i)) 10 (14+i) = true := by decide +kernel

theorem strictBool_r10_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (15+i)) 10 (15+i) = true := by decide +kernel

theorem strictBool_r10_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (16+i)) 10 (16+i) = true := by decide +kernel

theorem strictBool_r10_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (17+i)) 10 (17+i) = true := by decide +kernel

theorem strictBool_r10_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (18+i)) 10 (18+i) = true := by decide +kernel

theorem strictBool_r10_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (19+i)) 10 (19+i) = true := by decide +kernel

theorem strictBool_r10_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (20+i)) 10 (20+i) = true := by decide +kernel

theorem strictBool_r10_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (21+i)) 10 (21+i) = true := by decide +kernel

theorem strictBool_r10_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (22+i)) 10 (22+i) = true := by decide +kernel

theorem strictBool_r10_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (23+i)) 10 (23+i) = true := by decide +kernel

theorem strictBool_r10_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (24+i)) 10 (24+i) = true := by decide +kernel

theorem strictBool_r10_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (25+i)) 10 (25+i) = true := by decide +kernel

theorem strictBool_r10_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (26+i)) 10 (26+i) = true := by decide +kernel

theorem strictBool_r10_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (27+i)) 10 (27+i) = true := by decide +kernel

theorem strictBool_r10_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (28+i)) 10 (28+i) = true := by decide +kernel

theorem strictBool_r10_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (29+i)) 10 (29+i) = true := by decide +kernel

theorem strictBool_r10_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (30+i)) 10 (30+i) = true := by decide +kernel

theorem strictBool_r10_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (31+i)) 10 (31+i) = true := by decide +kernel

theorem strictBool_r10_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (32+i)) 10 (32+i) = true := by decide +kernel

theorem strictBool_r10_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (33+i)) 10 (33+i) = true := by decide +kernel

theorem strictBool_r10_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (34+i)) 10 (34+i) = true := by decide +kernel

theorem strictBool_r10_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (35+i)) 10 (35+i) = true := by decide +kernel

theorem strictBool_r10_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (36+i)) 10 (36+i) = true := by decide +kernel

theorem strictBool_r10_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (37+i)) 10 (37+i) = true := by decide +kernel

theorem strictBool_r10_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (38+i)) 10 (38+i) = true := by decide +kernel

theorem strictBool_r10_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (39+i)) 10 (39+i) = true := by decide +kernel

theorem strictBool_r10_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (40+i)) 10 (40+i) = true := by decide +kernel

theorem strictBool_r10_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (41+i)) 10 (41+i) = true := by decide +kernel

theorem strictBool_r10_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (42+i)) 10 (42+i) = true := by decide +kernel

theorem strictBool_r10_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (43+i)) 10 (43+i) = true := by decide +kernel

theorem strictBool_r10_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (44+i)) 10 (44+i) = true := by decide +kernel

theorem strictBool_r10_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (45+i)) 10 (45+i) = true := by decide +kernel

theorem strictBool_r10_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (46+i)) 10 (46+i) = true := by decide +kernel

theorem strictBool_r10_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (47+i)) 10 (47+i) = true := by decide +kernel

theorem strictBool_r10_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (48+i)) 10 (48+i) = true := by decide +kernel

theorem strictBool_r10_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (49+i)) 10 (49+i) = true := by decide +kernel

theorem strictBool_r10_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (50+i)) 10 (50+i) = true := by decide +kernel

theorem strictBool_r10_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (51+i)) 10 (51+i) = true := by decide +kernel

theorem strictBool_r10_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (52+i)) 10 (52+i) = true := by decide +kernel

theorem strictBool_r10_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (53+i)) 10 (53+i) = true := by decide +kernel

theorem strictBool_r10_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (54+i)) 10 (54+i) = true := by decide +kernel

theorem strictBool_r10_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (55+i)) 10 (55+i) = true := by decide +kernel

theorem strictBool_r10_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (56+i)) 10 (56+i) = true := by decide +kernel

theorem strictBool_r10_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (57+i)) 10 (57+i) = true := by decide +kernel

theorem strictBool_r10_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (58+i)) 10 (58+i) = true := by decide +kernel

theorem strictBool_r10_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (59+i)) 10 (59+i) = true := by decide +kernel

theorem strictBool_r10_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (60+i)) 10 (60+i) = true := by decide +kernel

theorem strictBool_r10_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (61+i)) 10 (61+i) = true := by decide +kernel

theorem strictBool_r10_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (62+i)) 10 (62+i) = true := by decide +kernel

theorem strictBool_r10_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (63+i)) 10 (63+i) = true := by decide +kernel

theorem strictBool_r10_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (64+i)) 10 (64+i) = true := by decide +kernel

theorem strictBool_r10_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (65+i)) 10 (65+i) = true := by decide +kernel

theorem strictBool_r10_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (66+i)) 10 (66+i) = true := by decide +kernel

theorem strictBool_r10_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (67+i)) 10 (67+i) = true := by decide +kernel

theorem strictBool_r10_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (68+i)) 10 (68+i) = true := by decide +kernel

theorem strictBool_r10_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (69+i)) 10 (69+i) = true := by decide +kernel

theorem strictBool_r10_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (70+i)) 10 (70+i) = true := by decide +kernel

theorem strictBool_r10_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (71+i)) 10 (71+i) = true := by decide +kernel

theorem strictBool_r10_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (72+i)) 10 (72+i) = true := by decide +kernel

theorem strictBool_r10_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (73+i)) 10 (73+i) = true := by decide +kernel

theorem strictBool_r10_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (74+i)) 10 (74+i) = true := by decide +kernel

theorem strictBool_r10_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (75+i)) 10 (75+i) = true := by decide +kernel

theorem strictBool_r10_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (76+i)) 10 (76+i) = true := by decide +kernel

theorem strictBool_r10_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (77+i)) 10 (77+i) = true := by decide +kernel

theorem strictBool_r10_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (78+i)) 10 (78+i) = true := by decide +kernel

theorem strictBool_r10_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (79+i)) 10 (79+i) = true := by decide +kernel

theorem strictBool_r10_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (80+i)) 10 (80+i) = true := by decide +kernel

theorem strictBool_r10_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (81+i)) 10 (81+i) = true := by decide +kernel

theorem strictBool_r10_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (82+i)) 10 (82+i) = true := by decide +kernel

theorem strictBool_r10_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (83+i)) 10 (83+i) = true := by decide +kernel

theorem strictBool_r10_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (84+i)) 10 (84+i) = true := by decide +kernel

theorem strictBool_r10_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (85+i)) 10 (85+i) = true := by decide +kernel

theorem strictBool_r10_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (86+i)) 10 (86+i) = true := by decide +kernel

theorem strictBool_r10_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (87+i)) 10 (87+i) = true := by decide +kernel

theorem strictBool_r10_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (88+i)) 10 (88+i) = true := by decide +kernel

theorem strictBool_r10_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (89+i)) 10 (89+i) = true := by decide +kernel

theorem strictBool_r10_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (90+i)) 10 (90+i) = true := by decide +kernel

theorem strictBool_r10_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (91+i)) 10 (91+i) = true := by decide +kernel

theorem strictBool_r10_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (92+i)) 10 (92+i) = true := by decide +kernel

theorem strictBool_r10_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (93+i)) 10 (93+i) = true := by decide +kernel

theorem strictBool_r10_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (94+i)) 10 (94+i) = true := by decide +kernel

theorem strictBool_r10_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (95+i)) 10 (95+i) = true := by decide +kernel

theorem strictBool_r10_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (96+i)) 10 (96+i) = true := by decide +kernel

theorem strictBool_r10_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (97+i)) 10 (97+i) = true := by decide +kernel

theorem strictBool_r10_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (98+i)) 10 (98+i) = true := by decide +kernel

theorem strictBool_r10_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (99+i)) 10 (99+i) = true := by decide +kernel

theorem strictBool_r10_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (100+i)) 10 (100+i) = true := by decide +kernel

theorem strictBool_r10_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (101+i)) 10 (101+i) = true := by decide +kernel

theorem strictBool_r10_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (102+i)) 10 (102+i) = true := by decide +kernel

theorem strictBool_r10_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (103+i)) 10 (103+i) = true := by decide +kernel

theorem strictBool_r10_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (104+i)) 10 (104+i) = true := by decide +kernel

theorem strictBool_r10_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (105+i)) 10 (105+i) = true := by decide +kernel

theorem strictBool_r10_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (106+i)) 10 (106+i) = true := by decide +kernel

theorem strictBool_r10_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (107+i)) 10 (107+i) = true := by decide +kernel

theorem strictBool_r10_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (108+i)) 10 (108+i) = true := by decide +kernel

theorem strictBool_r10_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (109+i)) 10 (109+i) = true := by decide +kernel

theorem strictBool_r10_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (110+i)) 10 (110+i) = true := by decide +kernel

theorem strictBool_r10_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (111+i)) 10 (111+i) = true := by decide +kernel

theorem strictBool_r10_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (112+i)) 10 (112+i) = true := by decide +kernel

theorem strictBool_r10_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (113+i)) 10 (113+i) = true := by decide +kernel

theorem strictBool_r10_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (114+i)) 10 (114+i) = true := by decide +kernel

theorem strictBool_r10_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (115+i)) 10 (115+i) = true := by decide +kernel

theorem strictBool_r10_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (116+i)) 10 (116+i) = true := by decide +kernel

theorem strictBool_r10_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (117+i)) 10 (117+i) = true := by decide +kernel

theorem strictBool_r10_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (118+i)) 10 (118+i) = true := by decide +kernel

theorem strictBool_r10_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (119+i)) 10 (119+i) = true := by decide +kernel

theorem strictBool_r10_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (120+i)) 10 (120+i) = true := by decide +kernel

theorem strictBool_r10_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (121+i)) 10 (121+i) = true := by decide +kernel

theorem strictBool_r10_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (122+i)) 10 (122+i) = true := by decide +kernel

theorem strictBool_r10_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (123+i)) 10 (123+i) = true := by decide +kernel

theorem strictBool_r10_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (124+i)) 10 (124+i) = true := by decide +kernel

theorem strictBool_r10_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (125+i)) 10 (125+i) = true := by decide +kernel

theorem strictBool_r10_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (126+i)) 10 (126+i) = true := by decide +kernel

theorem strictBool_r10_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (127+i)) 10 (127+i) = true := by decide +kernel

theorem strictBool_r10_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (128+i)) 10 (128+i) = true := by decide +kernel

theorem strictBool_r10_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (129+i)) 10 (129+i) = true := by decide +kernel

theorem strictBool_r10_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (130+i)) 10 (130+i) = true := by decide +kernel

theorem strictBool_r10_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (131+i)) 10 (131+i) = true := by decide +kernel

theorem strictBool_r10_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 10 (132+i)) 10 (132+i) = true := by decide +kernel

theorem strictBool_r10 (V : ℕ) (hV : V ∈ List.range 133) : strictBool (BoundaryTailBaseFastData.row 10 V) 10 V = true := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 66
  · by_cases h0_66 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r10_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r10_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r10_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r10_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r10_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r10_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r10_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r10_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r10_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r10_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r10_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r10_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r10_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r10_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r10_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := strictBool_r10_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := strictBool_r10_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := strictBool_r10_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_66 : V < 49
      · by_cases h33_49 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r10_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r10_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r10_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r10_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_49 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r10_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r10_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r10_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r10_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
      · by_cases h49_66 : V < 57
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r10_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r10_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r10_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r10_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · by_cases h57_66 : V < 61
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r10_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r10_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h61_66 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r10_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_66 : V < 64
              · have hi := strictBool_r10_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · by_cases h64_66 : V < 65
                · have hi := strictBool_r10_part64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                · have hi := strictBool_r10_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
  · by_cases h66_133 : V < 99
    · by_cases h66_99 : V < 82
      · by_cases h66_82 : V < 74
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r10_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r10_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r10_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r10_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
        · by_cases h74_82 : V < 78
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r10_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r10_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r10_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r10_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
      · by_cases h82_99 : V < 90
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r10_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r10_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r10_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r10_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
        · by_cases h90_99 : V < 94
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r10_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r10_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
          · by_cases h94_99 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r10_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_99 : V < 97
              · have hi := strictBool_r10_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · by_cases h97_99 : V < 98
                · have hi := strictBool_r10_part97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
                · have hi := strictBool_r10_part98 (V-98) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
    · by_cases h99_133 : V < 116
      · by_cases h99_116 : V < 107
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r10_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r10_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r10_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r10_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
        · by_cases h107_116 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r10_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r10_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
          · by_cases h111_116 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r10_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_116 : V < 114
              · have hi := strictBool_r10_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · by_cases h114_116 : V < 115
                · have hi := strictBool_r10_part114 (V-114) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
                · have hi := strictBool_r10_part115 (V-115) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
      · by_cases h116_133 : V < 124
        · by_cases h116_124 : V < 120
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r10_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r10_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r10_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r10_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
        · by_cases h124_133 : V < 128
          · by_cases h124_128 : V < 126
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r10_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r10_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
          · by_cases h128_133 : V < 130
            · by_cases h128_130 : V < 129
              · have hi := strictBool_r10_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := strictBool_r10_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_133 : V < 131
              · have hi := strictBool_r10_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · by_cases h131_133 : V < 132
                · have hi := strictBool_r10_part131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
                · have hi := strictBool_r10_part132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi

theorem strictFast_r10 (V : ℕ) (hV : V ∈ List.range 133) : StrictAtFast (BoundaryTailBaseFastData.row 10 V) 10 V :=
  strictBool_sound _ _ _ (strictBool_r10 V hV)

theorem strict_r10 (V : ℕ) (hV : V ∈ List.range 133) : StrictCheckAt 10 V :=
  strictAtFast_sound _ _ _ (valid_r10 V hV) (strictFast_r10 V hV)

theorem zeroCertificate_r10_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (0+i)) 10 (0+i) := by decide +kernel

theorem zeroCertificate_r10_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (8+i)) 10 (8+i) := by decide +kernel

theorem zeroCertificate_r10_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (16+i)) 10 (16+i) := by decide +kernel

theorem zeroCertificate_r10_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (24+i)) 10 (24+i) := by decide +kernel

theorem zeroCertificate_r10_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (32+i)) 10 (32+i) := by decide +kernel

theorem zeroCertificate_r10_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (40+i)) 10 (40+i) := by decide +kernel

theorem zeroCertificate_r10_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (48+i)) 10 (48+i) := by decide +kernel

theorem zeroCertificate_r10_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (56+i)) 10 (56+i) := by decide +kernel

theorem zeroCertificate_r10_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (64+i)) 10 (64+i) := by decide +kernel

theorem zeroCertificate_r10_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (72+i)) 10 (72+i) := by decide +kernel

theorem zeroCertificate_r10_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (80+i)) 10 (80+i) := by decide +kernel

theorem zeroCertificate_r10_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (88+i)) 10 (88+i) := by decide +kernel

theorem zeroCertificate_r10_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (96+i)) 10 (96+i) := by decide +kernel

theorem zeroCertificate_r10_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (104+i)) 10 (104+i) := by decide +kernel

theorem zeroCertificate_r10_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (112+i)) 10 (112+i) := by decide +kernel

theorem zeroCertificate_r10_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 10 (120+i)) 10 (120+i) := by decide +kernel

theorem zeroCertificate_r10_part128 : ∀ i ∈ List.range 5, ZeroCertificate (BoundaryTailBaseFastData.row 10 (128+i)) 10 (128+i) := by decide +kernel

theorem zeroCertificate_r10 (V : ℕ) (hV : V ∈ List.range 133) : ZeroCertificate (BoundaryTailBaseFastData.row 10 V) 10 V := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := zeroCertificate_r10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := zeroCertificate_r10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r10 (V : ℕ) (hV : V ∈ List.range 133) : ZeroAtFast 10 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r10 V hV) (zeroCertificate_r10 V hV)

theorem zero_r10 (V : ℕ) (hV : V ∈ List.range 133) : ZeroCheckAt 10 V :=
  zeroAtFast_sound _ _ (zeroFast_r10 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r14_part0 : ∀ i ∈ List.range 8, CorrectAt 14 (0+i) := by decide +kernel

theorem correct_r14_part8 : ∀ i ∈ List.range 8, CorrectAt 14 (8+i) := by decide +kernel

theorem correct_r14_part16 : ∀ i ∈ List.range 8, CorrectAt 14 (16+i) := by decide +kernel

theorem correct_r14_part24 : ∀ i ∈ List.range 8, CorrectAt 14 (24+i) := by decide +kernel

theorem correct_r14_part32 : ∀ i ∈ List.range 8, CorrectAt 14 (32+i) := by decide +kernel

theorem correct_r14_part40 : ∀ i ∈ List.range 8, CorrectAt 14 (40+i) := by decide +kernel

theorem correct_r14_part48 : ∀ i ∈ List.range 8, CorrectAt 14 (48+i) := by decide +kernel

theorem correct_r14_part56 : ∀ i ∈ List.range 8, CorrectAt 14 (56+i) := by decide +kernel

theorem correct_r14_part64 : ∀ i ∈ List.range 8, CorrectAt 14 (64+i) := by decide +kernel

theorem correct_r14_part72 : ∀ i ∈ List.range 8, CorrectAt 14 (72+i) := by decide +kernel

theorem correct_r14_part80 : ∀ i ∈ List.range 8, CorrectAt 14 (80+i) := by decide +kernel

theorem correct_r14_part88 : ∀ i ∈ List.range 8, CorrectAt 14 (88+i) := by decide +kernel

theorem correct_r14_part96 : ∀ i ∈ List.range 8, CorrectAt 14 (96+i) := by decide +kernel

theorem correct_r14_part104 : ∀ i ∈ List.range 8, CorrectAt 14 (104+i) := by decide +kernel

theorem correct_r14_part112 : ∀ i ∈ List.range 8, CorrectAt 14 (112+i) := by decide +kernel

theorem correct_r14_part120 : ∀ i ∈ List.range 8, CorrectAt 14 (120+i) := by decide +kernel

theorem correct_r14_part128 : ∀ i ∈ List.range 1, CorrectAt 14 (128+i) := by decide +kernel

theorem correct_r14 (V : ℕ) (hV : V ∈ List.range 129) : CorrectAt 14 V := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := correct_r14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := correct_r14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r14_part0 : ∀ i ∈ List.range 8, BaseCheckAt 14 (0+i) := by decide +kernel

theorem base_r14_part8 : ∀ i ∈ List.range 8, BaseCheckAt 14 (8+i) := by decide +kernel

theorem base_r14_part16 : ∀ i ∈ List.range 8, BaseCheckAt 14 (16+i) := by decide +kernel

theorem base_r14_part24 : ∀ i ∈ List.range 8, BaseCheckAt 14 (24+i) := by decide +kernel

theorem base_r14_part32 : ∀ i ∈ List.range 8, BaseCheckAt 14 (32+i) := by decide +kernel

theorem base_r14_part40 : ∀ i ∈ List.range 8, BaseCheckAt 14 (40+i) := by decide +kernel

theorem base_r14_part48 : ∀ i ∈ List.range 8, BaseCheckAt 14 (48+i) := by decide +kernel

theorem base_r14_part56 : ∀ i ∈ List.range 8, BaseCheckAt 14 (56+i) := by decide +kernel

theorem base_r14_part64 : ∀ i ∈ List.range 8, BaseCheckAt 14 (64+i) := by decide +kernel

theorem base_r14_part72 : ∀ i ∈ List.range 8, BaseCheckAt 14 (72+i) := by decide +kernel

theorem base_r14_part80 : ∀ i ∈ List.range 8, BaseCheckAt 14 (80+i) := by decide +kernel

theorem base_r14_part88 : ∀ i ∈ List.range 8, BaseCheckAt 14 (88+i) := by decide +kernel

theorem base_r14_part96 : ∀ i ∈ List.range 8, BaseCheckAt 14 (96+i) := by decide +kernel

theorem base_r14_part104 : ∀ i ∈ List.range 8, BaseCheckAt 14 (104+i) := by decide +kernel

theorem base_r14_part112 : ∀ i ∈ List.range 8, BaseCheckAt 14 (112+i) := by decide +kernel

theorem base_r14_part120 : ∀ i ∈ List.range 8, BaseCheckAt 14 (120+i) := by decide +kernel

theorem base_r14_part128 : ∀ i ∈ List.range 1, BaseCheckAt 14 (128+i) := by decide +kernel

theorem base_r14 (V : ℕ) (hV : V ∈ List.range 129) : BaseCheckAt 14 V := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := base_r14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := base_r14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r14_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (0+i)) 14 (0+i) := by decide +kernel

theorem valid_r14_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (8+i)) 14 (8+i) := by decide +kernel

theorem valid_r14_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (16+i)) 14 (16+i) := by decide +kernel

theorem valid_r14_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (24+i)) 14 (24+i) := by decide +kernel

theorem valid_r14_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (32+i)) 14 (32+i) := by decide +kernel

theorem valid_r14_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (40+i)) 14 (40+i) := by decide +kernel

theorem valid_r14_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (48+i)) 14 (48+i) := by decide +kernel

theorem valid_r14_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (56+i)) 14 (56+i) := by decide +kernel

theorem valid_r14_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (64+i)) 14 (64+i) := by decide +kernel

theorem valid_r14_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (72+i)) 14 (72+i) := by decide +kernel

theorem valid_r14_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (80+i)) 14 (80+i) := by decide +kernel

theorem valid_r14_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (88+i)) 14 (88+i) := by decide +kernel

theorem valid_r14_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (96+i)) 14 (96+i) := by decide +kernel

theorem valid_r14_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (104+i)) 14 (104+i) := by decide +kernel

theorem valid_r14_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (112+i)) 14 (112+i) := by decide +kernel

theorem valid_r14_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 14 (120+i)) 14 (120+i) := by decide +kernel

theorem valid_r14_part128 : ∀ i ∈ List.range 1, Valid (BoundaryTailBaseFastData.row 14 (128+i)) 14 (128+i) := by decide +kernel

theorem valid_r14 (V : ℕ) (hV : V ∈ List.range 129) : Valid (BoundaryTailBaseFastData.row 14 V) 14 V := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := valid_r14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := valid_r14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r14_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (0+i)) 14 (0+i) = true := by decide +kernel

theorem strictBool_r14_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (1+i)) 14 (1+i) = true := by decide +kernel

theorem strictBool_r14_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (2+i)) 14 (2+i) = true := by decide +kernel

theorem strictBool_r14_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (3+i)) 14 (3+i) = true := by decide +kernel

theorem strictBool_r14_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (4+i)) 14 (4+i) = true := by decide +kernel

theorem strictBool_r14_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (5+i)) 14 (5+i) = true := by decide +kernel

theorem strictBool_r14_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (6+i)) 14 (6+i) = true := by decide +kernel

theorem strictBool_r14_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (7+i)) 14 (7+i) = true := by decide +kernel

theorem strictBool_r14_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (8+i)) 14 (8+i) = true := by decide +kernel

theorem strictBool_r14_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (9+i)) 14 (9+i) = true := by decide +kernel

theorem strictBool_r14_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (10+i)) 14 (10+i) = true := by decide +kernel

theorem strictBool_r14_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (11+i)) 14 (11+i) = true := by decide +kernel

theorem strictBool_r14_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (12+i)) 14 (12+i) = true := by decide +kernel

theorem strictBool_r14_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (13+i)) 14 (13+i) = true := by decide +kernel

theorem strictBool_r14_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (14+i)) 14 (14+i) = true := by decide +kernel

theorem strictBool_r14_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (15+i)) 14 (15+i) = true := by decide +kernel

theorem strictBool_r14_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (16+i)) 14 (16+i) = true := by decide +kernel

theorem strictBool_r14_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (17+i)) 14 (17+i) = true := by decide +kernel

theorem strictBool_r14_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (18+i)) 14 (18+i) = true := by decide +kernel

theorem strictBool_r14_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (19+i)) 14 (19+i) = true := by decide +kernel

theorem strictBool_r14_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (20+i)) 14 (20+i) = true := by decide +kernel

theorem strictBool_r14_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (21+i)) 14 (21+i) = true := by decide +kernel

theorem strictBool_r14_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (22+i)) 14 (22+i) = true := by decide +kernel

theorem strictBool_r14_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (23+i)) 14 (23+i) = true := by decide +kernel

theorem strictBool_r14_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (24+i)) 14 (24+i) = true := by decide +kernel

theorem strictBool_r14_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (25+i)) 14 (25+i) = true := by decide +kernel

theorem strictBool_r14_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (26+i)) 14 (26+i) = true := by decide +kernel

theorem strictBool_r14_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (27+i)) 14 (27+i) = true := by decide +kernel

theorem strictBool_r14_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (28+i)) 14 (28+i) = true := by decide +kernel

theorem strictBool_r14_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (29+i)) 14 (29+i) = true := by decide +kernel

theorem strictBool_r14_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (30+i)) 14 (30+i) = true := by decide +kernel

theorem strictBool_r14_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (31+i)) 14 (31+i) = true := by decide +kernel

theorem strictBool_r14_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (32+i)) 14 (32+i) = true := by decide +kernel

theorem strictBool_r14_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (33+i)) 14 (33+i) = true := by decide +kernel

theorem strictBool_r14_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (34+i)) 14 (34+i) = true := by decide +kernel

theorem strictBool_r14_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (35+i)) 14 (35+i) = true := by decide +kernel

theorem strictBool_r14_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (36+i)) 14 (36+i) = true := by decide +kernel

theorem strictBool_r14_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (37+i)) 14 (37+i) = true := by decide +kernel

theorem strictBool_r14_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (38+i)) 14 (38+i) = true := by decide +kernel

theorem strictBool_r14_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (39+i)) 14 (39+i) = true := by decide +kernel

theorem strictBool_r14_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (40+i)) 14 (40+i) = true := by decide +kernel

theorem strictBool_r14_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (41+i)) 14 (41+i) = true := by decide +kernel

theorem strictBool_r14_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (42+i)) 14 (42+i) = true := by decide +kernel

theorem strictBool_r14_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (43+i)) 14 (43+i) = true := by decide +kernel

theorem strictBool_r14_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (44+i)) 14 (44+i) = true := by decide +kernel

theorem strictBool_r14_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (45+i)) 14 (45+i) = true := by decide +kernel

theorem strictBool_r14_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (46+i)) 14 (46+i) = true := by decide +kernel

theorem strictBool_r14_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (47+i)) 14 (47+i) = true := by decide +kernel

theorem strictBool_r14_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (48+i)) 14 (48+i) = true := by decide +kernel

theorem strictBool_r14_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (49+i)) 14 (49+i) = true := by decide +kernel

theorem strictBool_r14_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (50+i)) 14 (50+i) = true := by decide +kernel

theorem strictBool_r14_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (51+i)) 14 (51+i) = true := by decide +kernel

theorem strictBool_r14_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (52+i)) 14 (52+i) = true := by decide +kernel

theorem strictBool_r14_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (53+i)) 14 (53+i) = true := by decide +kernel

theorem strictBool_r14_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (54+i)) 14 (54+i) = true := by decide +kernel

theorem strictBool_r14_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (55+i)) 14 (55+i) = true := by decide +kernel

theorem strictBool_r14_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (56+i)) 14 (56+i) = true := by decide +kernel

theorem strictBool_r14_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (57+i)) 14 (57+i) = true := by decide +kernel

theorem strictBool_r14_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (58+i)) 14 (58+i) = true := by decide +kernel

theorem strictBool_r14_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (59+i)) 14 (59+i) = true := by decide +kernel

theorem strictBool_r14_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (60+i)) 14 (60+i) = true := by decide +kernel

theorem strictBool_r14_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (61+i)) 14 (61+i) = true := by decide +kernel

theorem strictBool_r14_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (62+i)) 14 (62+i) = true := by decide +kernel

theorem strictBool_r14_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (63+i)) 14 (63+i) = true := by decide +kernel

theorem strictBool_r14_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (64+i)) 14 (64+i) = true := by decide +kernel

theorem strictBool_r14_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (65+i)) 14 (65+i) = true := by decide +kernel

theorem strictBool_r14_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (66+i)) 14 (66+i) = true := by decide +kernel

theorem strictBool_r14_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (67+i)) 14 (67+i) = true := by decide +kernel

theorem strictBool_r14_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (68+i)) 14 (68+i) = true := by decide +kernel

theorem strictBool_r14_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (69+i)) 14 (69+i) = true := by decide +kernel

theorem strictBool_r14_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (70+i)) 14 (70+i) = true := by decide +kernel

theorem strictBool_r14_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (71+i)) 14 (71+i) = true := by decide +kernel

theorem strictBool_r14_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (72+i)) 14 (72+i) = true := by decide +kernel

theorem strictBool_r14_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (73+i)) 14 (73+i) = true := by decide +kernel

theorem strictBool_r14_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (74+i)) 14 (74+i) = true := by decide +kernel

theorem strictBool_r14_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (75+i)) 14 (75+i) = true := by decide +kernel

theorem strictBool_r14_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (76+i)) 14 (76+i) = true := by decide +kernel

theorem strictBool_r14_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (77+i)) 14 (77+i) = true := by decide +kernel

theorem strictBool_r14_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (78+i)) 14 (78+i) = true := by decide +kernel

theorem strictBool_r14_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (79+i)) 14 (79+i) = true := by decide +kernel

theorem strictBool_r14_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (80+i)) 14 (80+i) = true := by decide +kernel

theorem strictBool_r14_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (81+i)) 14 (81+i) = true := by decide +kernel

theorem strictBool_r14_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (82+i)) 14 (82+i) = true := by decide +kernel

theorem strictBool_r14_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (83+i)) 14 (83+i) = true := by decide +kernel

theorem strictBool_r14_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (84+i)) 14 (84+i) = true := by decide +kernel

theorem strictBool_r14_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (85+i)) 14 (85+i) = true := by decide +kernel

theorem strictBool_r14_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (86+i)) 14 (86+i) = true := by decide +kernel

theorem strictBool_r14_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (87+i)) 14 (87+i) = true := by decide +kernel

theorem strictBool_r14_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (88+i)) 14 (88+i) = true := by decide +kernel

theorem strictBool_r14_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (89+i)) 14 (89+i) = true := by decide +kernel

theorem strictBool_r14_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (90+i)) 14 (90+i) = true := by decide +kernel

theorem strictBool_r14_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (91+i)) 14 (91+i) = true := by decide +kernel

theorem strictBool_r14_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (92+i)) 14 (92+i) = true := by decide +kernel

theorem strictBool_r14_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (93+i)) 14 (93+i) = true := by decide +kernel

theorem strictBool_r14_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (94+i)) 14 (94+i) = true := by decide +kernel

theorem strictBool_r14_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (95+i)) 14 (95+i) = true := by decide +kernel

theorem strictBool_r14_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (96+i)) 14 (96+i) = true := by decide +kernel

theorem strictBool_r14_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (97+i)) 14 (97+i) = true := by decide +kernel

theorem strictBool_r14_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (98+i)) 14 (98+i) = true := by decide +kernel

theorem strictBool_r14_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (99+i)) 14 (99+i) = true := by decide +kernel

theorem strictBool_r14_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (100+i)) 14 (100+i) = true := by decide +kernel

theorem strictBool_r14_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (101+i)) 14 (101+i) = true := by decide +kernel

theorem strictBool_r14_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (102+i)) 14 (102+i) = true := by decide +kernel

theorem strictBool_r14_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (103+i)) 14 (103+i) = true := by decide +kernel

theorem strictBool_r14_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (104+i)) 14 (104+i) = true := by decide +kernel

theorem strictBool_r14_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (105+i)) 14 (105+i) = true := by decide +kernel

theorem strictBool_r14_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (106+i)) 14 (106+i) = true := by decide +kernel

theorem strictBool_r14_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (107+i)) 14 (107+i) = true := by decide +kernel

theorem strictBool_r14_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (108+i)) 14 (108+i) = true := by decide +kernel

theorem strictBool_r14_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (109+i)) 14 (109+i) = true := by decide +kernel

theorem strictBool_r14_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (110+i)) 14 (110+i) = true := by decide +kernel

theorem strictBool_r14_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (111+i)) 14 (111+i) = true := by decide +kernel

theorem strictBool_r14_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (112+i)) 14 (112+i) = true := by decide +kernel

theorem strictBool_r14_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (113+i)) 14 (113+i) = true := by decide +kernel

theorem strictBool_r14_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (114+i)) 14 (114+i) = true := by decide +kernel

theorem strictBool_r14_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (115+i)) 14 (115+i) = true := by decide +kernel

theorem strictBool_r14_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (116+i)) 14 (116+i) = true := by decide +kernel

theorem strictBool_r14_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (117+i)) 14 (117+i) = true := by decide +kernel

theorem strictBool_r14_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (118+i)) 14 (118+i) = true := by decide +kernel

theorem strictBool_r14_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (119+i)) 14 (119+i) = true := by decide +kernel

theorem strictBool_r14_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (120+i)) 14 (120+i) = true := by decide +kernel

theorem strictBool_r14_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (121+i)) 14 (121+i) = true := by decide +kernel

theorem strictBool_r14_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (122+i)) 14 (122+i) = true := by decide +kernel

theorem strictBool_r14_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (123+i)) 14 (123+i) = true := by decide +kernel

theorem strictBool_r14_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (124+i)) 14 (124+i) = true := by decide +kernel

theorem strictBool_r14_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (125+i)) 14 (125+i) = true := by decide +kernel

theorem strictBool_r14_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (126+i)) 14 (126+i) = true := by decide +kernel

theorem strictBool_r14_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (127+i)) 14 (127+i) = true := by decide +kernel

theorem strictBool_r14_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 14 (128+i)) 14 (128+i) = true := by decide +kernel

theorem strictBool_r14 (V : ℕ) (hV : V ∈ List.range 129) : strictBool (BoundaryTailBaseFastData.row 14 V) 14 V = true := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r14_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r14_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r14_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r14_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r14_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r14_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r14_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r14_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r14_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r14_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r14_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r14_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r14_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r14_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r14_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r14_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r14_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r14_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r14_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r14_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r14_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r14_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r14_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r14_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r14_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r14_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r14_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r14_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
        · by_cases h56_64 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r14_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r14_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r14_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r14_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · by_cases h64_72 : V < 68
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r14_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r14_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r14_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r14_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
        · by_cases h72_80 : V < 76
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r14_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r14_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r14_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r14_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · by_cases h80_88 : V < 84
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r14_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r14_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r14_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r14_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
        · by_cases h88_96 : V < 92
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r14_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r14_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r14_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r14_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · by_cases h96_104 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r14_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r14_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r14_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r14_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r14_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r14_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r14_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r14_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · by_cases h112_120 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r14_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r14_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r14_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r14_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 124
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r14_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r14_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
          · by_cases h124_129 : V < 126
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r14_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r14_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_129 : V < 127
              · have hi := strictBool_r14_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · by_cases h127_129 : V < 128
                · have hi := strictBool_r14_part127 (V-127) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
                · have hi := strictBool_r14_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictFast_r14 (V : ℕ) (hV : V ∈ List.range 129) : StrictAtFast (BoundaryTailBaseFastData.row 14 V) 14 V :=
  strictBool_sound _ _ _ (strictBool_r14 V hV)

theorem strict_r14 (V : ℕ) (hV : V ∈ List.range 129) : StrictCheckAt 14 V :=
  strictAtFast_sound _ _ _ (valid_r14 V hV) (strictFast_r14 V hV)

theorem zeroCertificate_r14_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (0+i)) 14 (0+i) := by decide +kernel

theorem zeroCertificate_r14_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (8+i)) 14 (8+i) := by decide +kernel

theorem zeroCertificate_r14_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (16+i)) 14 (16+i) := by decide +kernel

theorem zeroCertificate_r14_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (24+i)) 14 (24+i) := by decide +kernel

theorem zeroCertificate_r14_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (32+i)) 14 (32+i) := by decide +kernel

theorem zeroCertificate_r14_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (40+i)) 14 (40+i) := by decide +kernel

theorem zeroCertificate_r14_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (48+i)) 14 (48+i) := by decide +kernel

theorem zeroCertificate_r14_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (56+i)) 14 (56+i) := by decide +kernel

theorem zeroCertificate_r14_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (64+i)) 14 (64+i) := by decide +kernel

theorem zeroCertificate_r14_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (72+i)) 14 (72+i) := by decide +kernel

theorem zeroCertificate_r14_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (80+i)) 14 (80+i) := by decide +kernel

theorem zeroCertificate_r14_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (88+i)) 14 (88+i) := by decide +kernel

theorem zeroCertificate_r14_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (96+i)) 14 (96+i) := by decide +kernel

theorem zeroCertificate_r14_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (104+i)) 14 (104+i) := by decide +kernel

theorem zeroCertificate_r14_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (112+i)) 14 (112+i) := by decide +kernel

theorem zeroCertificate_r14_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 14 (120+i)) 14 (120+i) := by decide +kernel

theorem zeroCertificate_r14_part128 : ∀ i ∈ List.range 1, ZeroCertificate (BoundaryTailBaseFastData.row 14 (128+i)) 14 (128+i) := by decide +kernel

theorem zeroCertificate_r14 (V : ℕ) (hV : V ∈ List.range 129) : ZeroCertificate (BoundaryTailBaseFastData.row 14 V) 14 V := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := zeroCertificate_r14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := zeroCertificate_r14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r14 (V : ℕ) (hV : V ∈ List.range 129) : ZeroAtFast 14 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r14 V hV) (zeroCertificate_r14 V hV)

theorem zero_r14 (V : ℕ) (hV : V ∈ List.range 129) : ZeroCheckAt 14 V :=
  zeroAtFast_sound _ _ (zeroFast_r14 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r18_part0 : ∀ i ∈ List.range 8, CorrectAt 18 (0+i) := by decide +kernel

theorem correct_r18_part8 : ∀ i ∈ List.range 8, CorrectAt 18 (8+i) := by decide +kernel

theorem correct_r18_part16 : ∀ i ∈ List.range 8, CorrectAt 18 (16+i) := by decide +kernel

theorem correct_r18_part24 : ∀ i ∈ List.range 8, CorrectAt 18 (24+i) := by decide +kernel

theorem correct_r18_part32 : ∀ i ∈ List.range 8, CorrectAt 18 (32+i) := by decide +kernel

theorem correct_r18_part40 : ∀ i ∈ List.range 8, CorrectAt 18 (40+i) := by decide +kernel

theorem correct_r18_part48 : ∀ i ∈ List.range 8, CorrectAt 18 (48+i) := by decide +kernel

theorem correct_r18_part56 : ∀ i ∈ List.range 8, CorrectAt 18 (56+i) := by decide +kernel

theorem correct_r18_part64 : ∀ i ∈ List.range 8, CorrectAt 18 (64+i) := by decide +kernel

theorem correct_r18_part72 : ∀ i ∈ List.range 8, CorrectAt 18 (72+i) := by decide +kernel

theorem correct_r18_part80 : ∀ i ∈ List.range 8, CorrectAt 18 (80+i) := by decide +kernel

theorem correct_r18_part88 : ∀ i ∈ List.range 8, CorrectAt 18 (88+i) := by decide +kernel

theorem correct_r18_part96 : ∀ i ∈ List.range 8, CorrectAt 18 (96+i) := by decide +kernel

theorem correct_r18_part104 : ∀ i ∈ List.range 8, CorrectAt 18 (104+i) := by decide +kernel

theorem correct_r18_part112 : ∀ i ∈ List.range 8, CorrectAt 18 (112+i) := by decide +kernel

theorem correct_r18_part120 : ∀ i ∈ List.range 5, CorrectAt 18 (120+i) := by decide +kernel

theorem correct_r18 (V : ℕ) (hV : V ∈ List.range 125) : CorrectAt 18 V := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := correct_r18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r18_part0 : ∀ i ∈ List.range 8, BaseCheckAt 18 (0+i) := by decide +kernel

theorem base_r18_part8 : ∀ i ∈ List.range 8, BaseCheckAt 18 (8+i) := by decide +kernel

theorem base_r18_part16 : ∀ i ∈ List.range 8, BaseCheckAt 18 (16+i) := by decide +kernel

theorem base_r18_part24 : ∀ i ∈ List.range 8, BaseCheckAt 18 (24+i) := by decide +kernel

theorem base_r18_part32 : ∀ i ∈ List.range 8, BaseCheckAt 18 (32+i) := by decide +kernel

theorem base_r18_part40 : ∀ i ∈ List.range 8, BaseCheckAt 18 (40+i) := by decide +kernel

theorem base_r18_part48 : ∀ i ∈ List.range 8, BaseCheckAt 18 (48+i) := by decide +kernel

theorem base_r18_part56 : ∀ i ∈ List.range 8, BaseCheckAt 18 (56+i) := by decide +kernel

theorem base_r18_part64 : ∀ i ∈ List.range 8, BaseCheckAt 18 (64+i) := by decide +kernel

theorem base_r18_part72 : ∀ i ∈ List.range 8, BaseCheckAt 18 (72+i) := by decide +kernel

theorem base_r18_part80 : ∀ i ∈ List.range 8, BaseCheckAt 18 (80+i) := by decide +kernel

theorem base_r18_part88 : ∀ i ∈ List.range 8, BaseCheckAt 18 (88+i) := by decide +kernel

theorem base_r18_part96 : ∀ i ∈ List.range 8, BaseCheckAt 18 (96+i) := by decide +kernel

theorem base_r18_part104 : ∀ i ∈ List.range 8, BaseCheckAt 18 (104+i) := by decide +kernel

theorem base_r18_part112 : ∀ i ∈ List.range 8, BaseCheckAt 18 (112+i) := by decide +kernel

theorem base_r18_part120 : ∀ i ∈ List.range 5, BaseCheckAt 18 (120+i) := by decide +kernel

theorem base_r18 (V : ℕ) (hV : V ∈ List.range 125) : BaseCheckAt 18 V := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := base_r18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r18_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (0+i)) 18 (0+i) := by decide +kernel

theorem valid_r18_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (8+i)) 18 (8+i) := by decide +kernel

theorem valid_r18_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (16+i)) 18 (16+i) := by decide +kernel

theorem valid_r18_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (24+i)) 18 (24+i) := by decide +kernel

theorem valid_r18_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (32+i)) 18 (32+i) := by decide +kernel

theorem valid_r18_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (40+i)) 18 (40+i) := by decide +kernel

theorem valid_r18_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (48+i)) 18 (48+i) := by decide +kernel

theorem valid_r18_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (56+i)) 18 (56+i) := by decide +kernel

theorem valid_r18_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (64+i)) 18 (64+i) := by decide +kernel

theorem valid_r18_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (72+i)) 18 (72+i) := by decide +kernel

theorem valid_r18_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (80+i)) 18 (80+i) := by decide +kernel

theorem valid_r18_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (88+i)) 18 (88+i) := by decide +kernel

theorem valid_r18_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (96+i)) 18 (96+i) := by decide +kernel

theorem valid_r18_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (104+i)) 18 (104+i) := by decide +kernel

theorem valid_r18_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 18 (112+i)) 18 (112+i) := by decide +kernel

theorem valid_r18_part120 : ∀ i ∈ List.range 5, Valid (BoundaryTailBaseFastData.row 18 (120+i)) 18 (120+i) := by decide +kernel

theorem valid_r18 (V : ℕ) (hV : V ∈ List.range 125) : Valid (BoundaryTailBaseFastData.row 18 V) 18 V := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := valid_r18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r18_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (0+i)) 18 (0+i) = true := by decide +kernel

theorem strictBool_r18_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (1+i)) 18 (1+i) = true := by decide +kernel

theorem strictBool_r18_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (2+i)) 18 (2+i) = true := by decide +kernel

theorem strictBool_r18_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (3+i)) 18 (3+i) = true := by decide +kernel

theorem strictBool_r18_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (4+i)) 18 (4+i) = true := by decide +kernel

theorem strictBool_r18_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (5+i)) 18 (5+i) = true := by decide +kernel

theorem strictBool_r18_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (6+i)) 18 (6+i) = true := by decide +kernel

theorem strictBool_r18_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (7+i)) 18 (7+i) = true := by decide +kernel

theorem strictBool_r18_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (8+i)) 18 (8+i) = true := by decide +kernel

theorem strictBool_r18_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (9+i)) 18 (9+i) = true := by decide +kernel

theorem strictBool_r18_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (10+i)) 18 (10+i) = true := by decide +kernel

theorem strictBool_r18_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (11+i)) 18 (11+i) = true := by decide +kernel

theorem strictBool_r18_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (12+i)) 18 (12+i) = true := by decide +kernel

theorem strictBool_r18_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (13+i)) 18 (13+i) = true := by decide +kernel

theorem strictBool_r18_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (14+i)) 18 (14+i) = true := by decide +kernel

theorem strictBool_r18_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (15+i)) 18 (15+i) = true := by decide +kernel

theorem strictBool_r18_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (16+i)) 18 (16+i) = true := by decide +kernel

theorem strictBool_r18_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (17+i)) 18 (17+i) = true := by decide +kernel

theorem strictBool_r18_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (18+i)) 18 (18+i) = true := by decide +kernel

theorem strictBool_r18_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (19+i)) 18 (19+i) = true := by decide +kernel

theorem strictBool_r18_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (20+i)) 18 (20+i) = true := by decide +kernel

theorem strictBool_r18_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (21+i)) 18 (21+i) = true := by decide +kernel

theorem strictBool_r18_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (22+i)) 18 (22+i) = true := by decide +kernel

theorem strictBool_r18_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (23+i)) 18 (23+i) = true := by decide +kernel

theorem strictBool_r18_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (24+i)) 18 (24+i) = true := by decide +kernel

theorem strictBool_r18_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (25+i)) 18 (25+i) = true := by decide +kernel

theorem strictBool_r18_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (26+i)) 18 (26+i) = true := by decide +kernel

theorem strictBool_r18_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (27+i)) 18 (27+i) = true := by decide +kernel

theorem strictBool_r18_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (28+i)) 18 (28+i) = true := by decide +kernel

theorem strictBool_r18_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (29+i)) 18 (29+i) = true := by decide +kernel

theorem strictBool_r18_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (30+i)) 18 (30+i) = true := by decide +kernel

theorem strictBool_r18_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (31+i)) 18 (31+i) = true := by decide +kernel

theorem strictBool_r18_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (32+i)) 18 (32+i) = true := by decide +kernel

theorem strictBool_r18_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (33+i)) 18 (33+i) = true := by decide +kernel

theorem strictBool_r18_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (34+i)) 18 (34+i) = true := by decide +kernel

theorem strictBool_r18_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (35+i)) 18 (35+i) = true := by decide +kernel

theorem strictBool_r18_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (36+i)) 18 (36+i) = true := by decide +kernel

theorem strictBool_r18_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (37+i)) 18 (37+i) = true := by decide +kernel

theorem strictBool_r18_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (38+i)) 18 (38+i) = true := by decide +kernel

theorem strictBool_r18_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (39+i)) 18 (39+i) = true := by decide +kernel

theorem strictBool_r18_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (40+i)) 18 (40+i) = true := by decide +kernel

theorem strictBool_r18_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (41+i)) 18 (41+i) = true := by decide +kernel

theorem strictBool_r18_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (42+i)) 18 (42+i) = true := by decide +kernel

theorem strictBool_r18_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (43+i)) 18 (43+i) = true := by decide +kernel

theorem strictBool_r18_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (44+i)) 18 (44+i) = true := by decide +kernel

theorem strictBool_r18_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (45+i)) 18 (45+i) = true := by decide +kernel

theorem strictBool_r18_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (46+i)) 18 (46+i) = true := by decide +kernel

theorem strictBool_r18_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (47+i)) 18 (47+i) = true := by decide +kernel

theorem strictBool_r18_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (48+i)) 18 (48+i) = true := by decide +kernel

theorem strictBool_r18_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (49+i)) 18 (49+i) = true := by decide +kernel

theorem strictBool_r18_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (50+i)) 18 (50+i) = true := by decide +kernel

theorem strictBool_r18_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (51+i)) 18 (51+i) = true := by decide +kernel

theorem strictBool_r18_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (52+i)) 18 (52+i) = true := by decide +kernel

theorem strictBool_r18_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (53+i)) 18 (53+i) = true := by decide +kernel

theorem strictBool_r18_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (54+i)) 18 (54+i) = true := by decide +kernel

theorem strictBool_r18_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (55+i)) 18 (55+i) = true := by decide +kernel

theorem strictBool_r18_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (56+i)) 18 (56+i) = true := by decide +kernel

theorem strictBool_r18_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (57+i)) 18 (57+i) = true := by decide +kernel

theorem strictBool_r18_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (58+i)) 18 (58+i) = true := by decide +kernel

theorem strictBool_r18_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (59+i)) 18 (59+i) = true := by decide +kernel

theorem strictBool_r18_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (60+i)) 18 (60+i) = true := by decide +kernel

theorem strictBool_r18_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (61+i)) 18 (61+i) = true := by decide +kernel

theorem strictBool_r18_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (62+i)) 18 (62+i) = true := by decide +kernel

theorem strictBool_r18_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (63+i)) 18 (63+i) = true := by decide +kernel

theorem strictBool_r18_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (64+i)) 18 (64+i) = true := by decide +kernel

theorem strictBool_r18_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (65+i)) 18 (65+i) = true := by decide +kernel

theorem strictBool_r18_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (66+i)) 18 (66+i) = true := by decide +kernel

theorem strictBool_r18_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (67+i)) 18 (67+i) = true := by decide +kernel

theorem strictBool_r18_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (68+i)) 18 (68+i) = true := by decide +kernel

theorem strictBool_r18_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (69+i)) 18 (69+i) = true := by decide +kernel

theorem strictBool_r18_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (70+i)) 18 (70+i) = true := by decide +kernel

theorem strictBool_r18_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (71+i)) 18 (71+i) = true := by decide +kernel

theorem strictBool_r18_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (72+i)) 18 (72+i) = true := by decide +kernel

theorem strictBool_r18_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (73+i)) 18 (73+i) = true := by decide +kernel

theorem strictBool_r18_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (74+i)) 18 (74+i) = true := by decide +kernel

theorem strictBool_r18_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (75+i)) 18 (75+i) = true := by decide +kernel

theorem strictBool_r18_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (76+i)) 18 (76+i) = true := by decide +kernel

theorem strictBool_r18_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (77+i)) 18 (77+i) = true := by decide +kernel

theorem strictBool_r18_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (78+i)) 18 (78+i) = true := by decide +kernel

theorem strictBool_r18_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (79+i)) 18 (79+i) = true := by decide +kernel

theorem strictBool_r18_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (80+i)) 18 (80+i) = true := by decide +kernel

theorem strictBool_r18_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (81+i)) 18 (81+i) = true := by decide +kernel

theorem strictBool_r18_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (82+i)) 18 (82+i) = true := by decide +kernel

theorem strictBool_r18_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (83+i)) 18 (83+i) = true := by decide +kernel

theorem strictBool_r18_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (84+i)) 18 (84+i) = true := by decide +kernel

theorem strictBool_r18_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (85+i)) 18 (85+i) = true := by decide +kernel

theorem strictBool_r18_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (86+i)) 18 (86+i) = true := by decide +kernel

theorem strictBool_r18_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (87+i)) 18 (87+i) = true := by decide +kernel

theorem strictBool_r18_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (88+i)) 18 (88+i) = true := by decide +kernel

theorem strictBool_r18_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (89+i)) 18 (89+i) = true := by decide +kernel

theorem strictBool_r18_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (90+i)) 18 (90+i) = true := by decide +kernel

theorem strictBool_r18_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (91+i)) 18 (91+i) = true := by decide +kernel

theorem strictBool_r18_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (92+i)) 18 (92+i) = true := by decide +kernel

theorem strictBool_r18_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (93+i)) 18 (93+i) = true := by decide +kernel

theorem strictBool_r18_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (94+i)) 18 (94+i) = true := by decide +kernel

theorem strictBool_r18_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (95+i)) 18 (95+i) = true := by decide +kernel

theorem strictBool_r18_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (96+i)) 18 (96+i) = true := by decide +kernel

theorem strictBool_r18_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (97+i)) 18 (97+i) = true := by decide +kernel

theorem strictBool_r18_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (98+i)) 18 (98+i) = true := by decide +kernel

theorem strictBool_r18_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (99+i)) 18 (99+i) = true := by decide +kernel

theorem strictBool_r18_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (100+i)) 18 (100+i) = true := by decide +kernel

theorem strictBool_r18_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (101+i)) 18 (101+i) = true := by decide +kernel

theorem strictBool_r18_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (102+i)) 18 (102+i) = true := by decide +kernel

theorem strictBool_r18_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (103+i)) 18 (103+i) = true := by decide +kernel

theorem strictBool_r18_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (104+i)) 18 (104+i) = true := by decide +kernel

theorem strictBool_r18_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (105+i)) 18 (105+i) = true := by decide +kernel

theorem strictBool_r18_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (106+i)) 18 (106+i) = true := by decide +kernel

theorem strictBool_r18_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (107+i)) 18 (107+i) = true := by decide +kernel

theorem strictBool_r18_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (108+i)) 18 (108+i) = true := by decide +kernel

theorem strictBool_r18_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (109+i)) 18 (109+i) = true := by decide +kernel

theorem strictBool_r18_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (110+i)) 18 (110+i) = true := by decide +kernel

theorem strictBool_r18_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (111+i)) 18 (111+i) = true := by decide +kernel

theorem strictBool_r18_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (112+i)) 18 (112+i) = true := by decide +kernel

theorem strictBool_r18_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (113+i)) 18 (113+i) = true := by decide +kernel

theorem strictBool_r18_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (114+i)) 18 (114+i) = true := by decide +kernel

theorem strictBool_r18_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (115+i)) 18 (115+i) = true := by decide +kernel

theorem strictBool_r18_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (116+i)) 18 (116+i) = true := by decide +kernel

theorem strictBool_r18_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (117+i)) 18 (117+i) = true := by decide +kernel

theorem strictBool_r18_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (118+i)) 18 (118+i) = true := by decide +kernel

theorem strictBool_r18_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (119+i)) 18 (119+i) = true := by decide +kernel

theorem strictBool_r18_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (120+i)) 18 (120+i) = true := by decide +kernel

theorem strictBool_r18_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (121+i)) 18 (121+i) = true := by decide +kernel

theorem strictBool_r18_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (122+i)) 18 (122+i) = true := by decide +kernel

theorem strictBool_r18_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (123+i)) 18 (123+i) = true := by decide +kernel

theorem strictBool_r18_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 18 (124+i)) 18 (124+i) = true := by decide +kernel

theorem strictBool_r18 (V : ℕ) (hV : V ∈ List.range 125) : strictBool (BoundaryTailBaseFastData.row 18 V) 18 V = true := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 62
  · by_cases h0_62 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r18_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r18_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r18_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r18_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r18_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r18_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r18_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r18_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r18_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r18_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r18_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r18_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r18_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r18_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r18_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r18_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
    · by_cases h31_62 : V < 46
      · by_cases h31_46 : V < 38
        · by_cases h31_38 : V < 34
          · by_cases h31_34 : V < 32
            · have hi := strictBool_r18_part31 (V-31) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r18_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r18_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r18_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
        · by_cases h38_46 : V < 42
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r18_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r18_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r18_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r18_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
      · by_cases h46_62 : V < 54
        · by_cases h46_54 : V < 50
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r18_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r18_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r18_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r18_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
        · by_cases h54_62 : V < 58
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r18_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r18_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r18_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r18_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
  · by_cases h62_125 : V < 93
    · by_cases h62_93 : V < 77
      · by_cases h62_77 : V < 69
        · by_cases h62_69 : V < 65
          · by_cases h62_65 : V < 63
            · have hi := strictBool_r18_part62 (V-62) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r18_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r18_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r18_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r18_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r18_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r18_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r18_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
      · by_cases h77_93 : V < 85
        · by_cases h77_85 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r18_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r18_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r18_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r18_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r18_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r18_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r18_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r18_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
    · by_cases h93_125 : V < 109
      · by_cases h93_109 : V < 101
        · by_cases h93_101 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r18_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r18_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r18_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r18_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r18_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r18_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r18_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r18_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
      · by_cases h109_125 : V < 117
        · by_cases h109_117 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r18_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r18_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r18_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r18_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
        · by_cases h117_125 : V < 121
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r18_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r18_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r18_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r18_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r18_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi

theorem strictFast_r18 (V : ℕ) (hV : V ∈ List.range 125) : StrictAtFast (BoundaryTailBaseFastData.row 18 V) 18 V :=
  strictBool_sound _ _ _ (strictBool_r18 V hV)

theorem strict_r18 (V : ℕ) (hV : V ∈ List.range 125) : StrictCheckAt 18 V :=
  strictAtFast_sound _ _ _ (valid_r18 V hV) (strictFast_r18 V hV)

theorem zeroCertificate_r18_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (0+i)) 18 (0+i) := by decide +kernel

theorem zeroCertificate_r18_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (8+i)) 18 (8+i) := by decide +kernel

theorem zeroCertificate_r18_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (16+i)) 18 (16+i) := by decide +kernel

theorem zeroCertificate_r18_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (24+i)) 18 (24+i) := by decide +kernel

theorem zeroCertificate_r18_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (32+i)) 18 (32+i) := by decide +kernel

theorem zeroCertificate_r18_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (40+i)) 18 (40+i) := by decide +kernel

theorem zeroCertificate_r18_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (48+i)) 18 (48+i) := by decide +kernel

theorem zeroCertificate_r18_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (56+i)) 18 (56+i) := by decide +kernel

theorem zeroCertificate_r18_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (64+i)) 18 (64+i) := by decide +kernel

theorem zeroCertificate_r18_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (72+i)) 18 (72+i) := by decide +kernel

theorem zeroCertificate_r18_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (80+i)) 18 (80+i) := by decide +kernel

theorem zeroCertificate_r18_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (88+i)) 18 (88+i) := by decide +kernel

theorem zeroCertificate_r18_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (96+i)) 18 (96+i) := by decide +kernel

theorem zeroCertificate_r18_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (104+i)) 18 (104+i) := by decide +kernel

theorem zeroCertificate_r18_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 18 (112+i)) 18 (112+i) := by decide +kernel

theorem zeroCertificate_r18_part120 : ∀ i ∈ List.range 5, ZeroCertificate (BoundaryTailBaseFastData.row 18 (120+i)) 18 (120+i) := by decide +kernel

theorem zeroCertificate_r18 (V : ℕ) (hV : V ∈ List.range 125) : ZeroCertificate (BoundaryTailBaseFastData.row 18 V) 18 V := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := zeroCertificate_r18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r18 (V : ℕ) (hV : V ∈ List.range 125) : ZeroAtFast 18 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r18 V hV) (zeroCertificate_r18 V hV)

theorem zero_r18 (V : ℕ) (hV : V ∈ List.range 125) : ZeroCheckAt 18 V :=
  zeroAtFast_sound _ _ (zeroFast_r18 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r22_part0 : ∀ i ∈ List.range 8, CorrectAt 22 (0+i) := by decide +kernel

theorem correct_r22_part8 : ∀ i ∈ List.range 8, CorrectAt 22 (8+i) := by decide +kernel

theorem correct_r22_part16 : ∀ i ∈ List.range 8, CorrectAt 22 (16+i) := by decide +kernel

theorem correct_r22_part24 : ∀ i ∈ List.range 8, CorrectAt 22 (24+i) := by decide +kernel

theorem correct_r22_part32 : ∀ i ∈ List.range 8, CorrectAt 22 (32+i) := by decide +kernel

theorem correct_r22_part40 : ∀ i ∈ List.range 8, CorrectAt 22 (40+i) := by decide +kernel

theorem correct_r22_part48 : ∀ i ∈ List.range 8, CorrectAt 22 (48+i) := by decide +kernel

theorem correct_r22_part56 : ∀ i ∈ List.range 8, CorrectAt 22 (56+i) := by decide +kernel

theorem correct_r22_part64 : ∀ i ∈ List.range 8, CorrectAt 22 (64+i) := by decide +kernel

theorem correct_r22_part72 : ∀ i ∈ List.range 8, CorrectAt 22 (72+i) := by decide +kernel

theorem correct_r22_part80 : ∀ i ∈ List.range 8, CorrectAt 22 (80+i) := by decide +kernel

theorem correct_r22_part88 : ∀ i ∈ List.range 8, CorrectAt 22 (88+i) := by decide +kernel

theorem correct_r22_part96 : ∀ i ∈ List.range 8, CorrectAt 22 (96+i) := by decide +kernel

theorem correct_r22_part104 : ∀ i ∈ List.range 8, CorrectAt 22 (104+i) := by decide +kernel

theorem correct_r22_part112 : ∀ i ∈ List.range 8, CorrectAt 22 (112+i) := by decide +kernel

theorem correct_r22_part120 : ∀ i ∈ List.range 1, CorrectAt 22 (120+i) := by decide +kernel

theorem correct_r22 (V : ℕ) (hV : V ∈ List.range 121) : CorrectAt 22 V := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := correct_r22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r22_part0 : ∀ i ∈ List.range 8, BaseCheckAt 22 (0+i) := by decide +kernel

theorem base_r22_part8 : ∀ i ∈ List.range 8, BaseCheckAt 22 (8+i) := by decide +kernel

theorem base_r22_part16 : ∀ i ∈ List.range 8, BaseCheckAt 22 (16+i) := by decide +kernel

theorem base_r22_part24 : ∀ i ∈ List.range 8, BaseCheckAt 22 (24+i) := by decide +kernel

theorem base_r22_part32 : ∀ i ∈ List.range 8, BaseCheckAt 22 (32+i) := by decide +kernel

theorem base_r22_part40 : ∀ i ∈ List.range 8, BaseCheckAt 22 (40+i) := by decide +kernel

theorem base_r22_part48 : ∀ i ∈ List.range 8, BaseCheckAt 22 (48+i) := by decide +kernel

theorem base_r22_part56 : ∀ i ∈ List.range 8, BaseCheckAt 22 (56+i) := by decide +kernel

theorem base_r22_part64 : ∀ i ∈ List.range 8, BaseCheckAt 22 (64+i) := by decide +kernel

theorem base_r22_part72 : ∀ i ∈ List.range 8, BaseCheckAt 22 (72+i) := by decide +kernel

theorem base_r22_part80 : ∀ i ∈ List.range 8, BaseCheckAt 22 (80+i) := by decide +kernel

theorem base_r22_part88 : ∀ i ∈ List.range 8, BaseCheckAt 22 (88+i) := by decide +kernel

theorem base_r22_part96 : ∀ i ∈ List.range 8, BaseCheckAt 22 (96+i) := by decide +kernel

theorem base_r22_part104 : ∀ i ∈ List.range 8, BaseCheckAt 22 (104+i) := by decide +kernel

theorem base_r22_part112 : ∀ i ∈ List.range 8, BaseCheckAt 22 (112+i) := by decide +kernel

theorem base_r22_part120 : ∀ i ∈ List.range 1, BaseCheckAt 22 (120+i) := by decide +kernel

theorem base_r22 (V : ℕ) (hV : V ∈ List.range 121) : BaseCheckAt 22 V := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := base_r22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r22_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (0+i)) 22 (0+i) := by decide +kernel

theorem valid_r22_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (8+i)) 22 (8+i) := by decide +kernel

theorem valid_r22_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (16+i)) 22 (16+i) := by decide +kernel

theorem valid_r22_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (24+i)) 22 (24+i) := by decide +kernel

theorem valid_r22_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (32+i)) 22 (32+i) := by decide +kernel

theorem valid_r22_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (40+i)) 22 (40+i) := by decide +kernel

theorem valid_r22_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (48+i)) 22 (48+i) := by decide +kernel

theorem valid_r22_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (56+i)) 22 (56+i) := by decide +kernel

theorem valid_r22_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (64+i)) 22 (64+i) := by decide +kernel

theorem valid_r22_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (72+i)) 22 (72+i) := by decide +kernel

theorem valid_r22_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (80+i)) 22 (80+i) := by decide +kernel

theorem valid_r22_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (88+i)) 22 (88+i) := by decide +kernel

theorem valid_r22_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (96+i)) 22 (96+i) := by decide +kernel

theorem valid_r22_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (104+i)) 22 (104+i) := by decide +kernel

theorem valid_r22_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 22 (112+i)) 22 (112+i) := by decide +kernel

theorem valid_r22_part120 : ∀ i ∈ List.range 1, Valid (BoundaryTailBaseFastData.row 22 (120+i)) 22 (120+i) := by decide +kernel

theorem valid_r22 (V : ℕ) (hV : V ∈ List.range 121) : Valid (BoundaryTailBaseFastData.row 22 V) 22 V := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := valid_r22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r22_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (0+i)) 22 (0+i) = true := by decide +kernel

theorem strictBool_r22_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (1+i)) 22 (1+i) = true := by decide +kernel

theorem strictBool_r22_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (2+i)) 22 (2+i) = true := by decide +kernel

theorem strictBool_r22_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (3+i)) 22 (3+i) = true := by decide +kernel

theorem strictBool_r22_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (4+i)) 22 (4+i) = true := by decide +kernel

theorem strictBool_r22_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (5+i)) 22 (5+i) = true := by decide +kernel

theorem strictBool_r22_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (6+i)) 22 (6+i) = true := by decide +kernel

theorem strictBool_r22_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (7+i)) 22 (7+i) = true := by decide +kernel

theorem strictBool_r22_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (8+i)) 22 (8+i) = true := by decide +kernel

theorem strictBool_r22_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (9+i)) 22 (9+i) = true := by decide +kernel

theorem strictBool_r22_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (10+i)) 22 (10+i) = true := by decide +kernel

theorem strictBool_r22_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (11+i)) 22 (11+i) = true := by decide +kernel

theorem strictBool_r22_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (12+i)) 22 (12+i) = true := by decide +kernel

theorem strictBool_r22_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (13+i)) 22 (13+i) = true := by decide +kernel

theorem strictBool_r22_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (14+i)) 22 (14+i) = true := by decide +kernel

theorem strictBool_r22_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (15+i)) 22 (15+i) = true := by decide +kernel

theorem strictBool_r22_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (16+i)) 22 (16+i) = true := by decide +kernel

theorem strictBool_r22_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (17+i)) 22 (17+i) = true := by decide +kernel

theorem strictBool_r22_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (18+i)) 22 (18+i) = true := by decide +kernel

theorem strictBool_r22_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (19+i)) 22 (19+i) = true := by decide +kernel

theorem strictBool_r22_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (20+i)) 22 (20+i) = true := by decide +kernel

theorem strictBool_r22_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (21+i)) 22 (21+i) = true := by decide +kernel

theorem strictBool_r22_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (22+i)) 22 (22+i) = true := by decide +kernel

theorem strictBool_r22_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (23+i)) 22 (23+i) = true := by decide +kernel

theorem strictBool_r22_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (24+i)) 22 (24+i) = true := by decide +kernel

theorem strictBool_r22_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (25+i)) 22 (25+i) = true := by decide +kernel

theorem strictBool_r22_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (26+i)) 22 (26+i) = true := by decide +kernel

theorem strictBool_r22_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (27+i)) 22 (27+i) = true := by decide +kernel

theorem strictBool_r22_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (28+i)) 22 (28+i) = true := by decide +kernel

theorem strictBool_r22_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (29+i)) 22 (29+i) = true := by decide +kernel

theorem strictBool_r22_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (30+i)) 22 (30+i) = true := by decide +kernel

theorem strictBool_r22_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (31+i)) 22 (31+i) = true := by decide +kernel

theorem strictBool_r22_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (32+i)) 22 (32+i) = true := by decide +kernel

theorem strictBool_r22_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (33+i)) 22 (33+i) = true := by decide +kernel

theorem strictBool_r22_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (34+i)) 22 (34+i) = true := by decide +kernel

theorem strictBool_r22_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (35+i)) 22 (35+i) = true := by decide +kernel

theorem strictBool_r22_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (36+i)) 22 (36+i) = true := by decide +kernel

theorem strictBool_r22_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (37+i)) 22 (37+i) = true := by decide +kernel

theorem strictBool_r22_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (38+i)) 22 (38+i) = true := by decide +kernel

theorem strictBool_r22_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (39+i)) 22 (39+i) = true := by decide +kernel

theorem strictBool_r22_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (40+i)) 22 (40+i) = true := by decide +kernel

theorem strictBool_r22_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (41+i)) 22 (41+i) = true := by decide +kernel

theorem strictBool_r22_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (42+i)) 22 (42+i) = true := by decide +kernel

theorem strictBool_r22_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (43+i)) 22 (43+i) = true := by decide +kernel

theorem strictBool_r22_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (44+i)) 22 (44+i) = true := by decide +kernel

theorem strictBool_r22_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (45+i)) 22 (45+i) = true := by decide +kernel

theorem strictBool_r22_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (46+i)) 22 (46+i) = true := by decide +kernel

theorem strictBool_r22_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (47+i)) 22 (47+i) = true := by decide +kernel

theorem strictBool_r22_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (48+i)) 22 (48+i) = true := by decide +kernel

theorem strictBool_r22_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (49+i)) 22 (49+i) = true := by decide +kernel

theorem strictBool_r22_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (50+i)) 22 (50+i) = true := by decide +kernel

theorem strictBool_r22_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (51+i)) 22 (51+i) = true := by decide +kernel

theorem strictBool_r22_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (52+i)) 22 (52+i) = true := by decide +kernel

theorem strictBool_r22_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (53+i)) 22 (53+i) = true := by decide +kernel

theorem strictBool_r22_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (54+i)) 22 (54+i) = true := by decide +kernel

theorem strictBool_r22_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (55+i)) 22 (55+i) = true := by decide +kernel

theorem strictBool_r22_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (56+i)) 22 (56+i) = true := by decide +kernel

theorem strictBool_r22_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (57+i)) 22 (57+i) = true := by decide +kernel

theorem strictBool_r22_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (58+i)) 22 (58+i) = true := by decide +kernel

theorem strictBool_r22_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (59+i)) 22 (59+i) = true := by decide +kernel

theorem strictBool_r22_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (60+i)) 22 (60+i) = true := by decide +kernel

theorem strictBool_r22_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (61+i)) 22 (61+i) = true := by decide +kernel

theorem strictBool_r22_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (62+i)) 22 (62+i) = true := by decide +kernel

theorem strictBool_r22_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (63+i)) 22 (63+i) = true := by decide +kernel

theorem strictBool_r22_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (64+i)) 22 (64+i) = true := by decide +kernel

theorem strictBool_r22_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (65+i)) 22 (65+i) = true := by decide +kernel

theorem strictBool_r22_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (66+i)) 22 (66+i) = true := by decide +kernel

theorem strictBool_r22_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (67+i)) 22 (67+i) = true := by decide +kernel

theorem strictBool_r22_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (68+i)) 22 (68+i) = true := by decide +kernel

theorem strictBool_r22_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (69+i)) 22 (69+i) = true := by decide +kernel

theorem strictBool_r22_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (70+i)) 22 (70+i) = true := by decide +kernel

theorem strictBool_r22_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (71+i)) 22 (71+i) = true := by decide +kernel

theorem strictBool_r22_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (72+i)) 22 (72+i) = true := by decide +kernel

theorem strictBool_r22_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (73+i)) 22 (73+i) = true := by decide +kernel

theorem strictBool_r22_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (74+i)) 22 (74+i) = true := by decide +kernel

theorem strictBool_r22_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (75+i)) 22 (75+i) = true := by decide +kernel

theorem strictBool_r22_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (76+i)) 22 (76+i) = true := by decide +kernel

theorem strictBool_r22_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (77+i)) 22 (77+i) = true := by decide +kernel

theorem strictBool_r22_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (78+i)) 22 (78+i) = true := by decide +kernel

theorem strictBool_r22_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (79+i)) 22 (79+i) = true := by decide +kernel

theorem strictBool_r22_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (80+i)) 22 (80+i) = true := by decide +kernel

theorem strictBool_r22_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (81+i)) 22 (81+i) = true := by decide +kernel

theorem strictBool_r22_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (82+i)) 22 (82+i) = true := by decide +kernel

theorem strictBool_r22_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (83+i)) 22 (83+i) = true := by decide +kernel

theorem strictBool_r22_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (84+i)) 22 (84+i) = true := by decide +kernel

theorem strictBool_r22_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (85+i)) 22 (85+i) = true := by decide +kernel

theorem strictBool_r22_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (86+i)) 22 (86+i) = true := by decide +kernel

theorem strictBool_r22_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (87+i)) 22 (87+i) = true := by decide +kernel

theorem strictBool_r22_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (88+i)) 22 (88+i) = true := by decide +kernel

theorem strictBool_r22_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (89+i)) 22 (89+i) = true := by decide +kernel

theorem strictBool_r22_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (90+i)) 22 (90+i) = true := by decide +kernel

theorem strictBool_r22_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (91+i)) 22 (91+i) = true := by decide +kernel

theorem strictBool_r22_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (92+i)) 22 (92+i) = true := by decide +kernel

theorem strictBool_r22_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (93+i)) 22 (93+i) = true := by decide +kernel

theorem strictBool_r22_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (94+i)) 22 (94+i) = true := by decide +kernel

theorem strictBool_r22_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (95+i)) 22 (95+i) = true := by decide +kernel

theorem strictBool_r22_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (96+i)) 22 (96+i) = true := by decide +kernel

theorem strictBool_r22_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (97+i)) 22 (97+i) = true := by decide +kernel

theorem strictBool_r22_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (98+i)) 22 (98+i) = true := by decide +kernel

theorem strictBool_r22_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (99+i)) 22 (99+i) = true := by decide +kernel

theorem strictBool_r22_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (100+i)) 22 (100+i) = true := by decide +kernel

theorem strictBool_r22_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (101+i)) 22 (101+i) = true := by decide +kernel

theorem strictBool_r22_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (102+i)) 22 (102+i) = true := by decide +kernel

theorem strictBool_r22_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (103+i)) 22 (103+i) = true := by decide +kernel

theorem strictBool_r22_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (104+i)) 22 (104+i) = true := by decide +kernel

theorem strictBool_r22_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (105+i)) 22 (105+i) = true := by decide +kernel

theorem strictBool_r22_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (106+i)) 22 (106+i) = true := by decide +kernel

theorem strictBool_r22_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (107+i)) 22 (107+i) = true := by decide +kernel

theorem strictBool_r22_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (108+i)) 22 (108+i) = true := by decide +kernel

theorem strictBool_r22_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (109+i)) 22 (109+i) = true := by decide +kernel

theorem strictBool_r22_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (110+i)) 22 (110+i) = true := by decide +kernel

theorem strictBool_r22_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (111+i)) 22 (111+i) = true := by decide +kernel

theorem strictBool_r22_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (112+i)) 22 (112+i) = true := by decide +kernel

theorem strictBool_r22_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (113+i)) 22 (113+i) = true := by decide +kernel

theorem strictBool_r22_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (114+i)) 22 (114+i) = true := by decide +kernel

theorem strictBool_r22_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (115+i)) 22 (115+i) = true := by decide +kernel

theorem strictBool_r22_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (116+i)) 22 (116+i) = true := by decide +kernel

theorem strictBool_r22_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (117+i)) 22 (117+i) = true := by decide +kernel

theorem strictBool_r22_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (118+i)) 22 (118+i) = true := by decide +kernel

theorem strictBool_r22_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (119+i)) 22 (119+i) = true := by decide +kernel

theorem strictBool_r22_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 22 (120+i)) 22 (120+i) = true := by decide +kernel

theorem strictBool_r22 (V : ℕ) (hV : V ∈ List.range 121) : strictBool (BoundaryTailBaseFastData.row 22 V) 22 V = true := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 60
  · by_cases h0_60 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r22_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r22_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r22_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r22_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r22_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r22_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r22_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r22_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have hi := strictBool_r22_part15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r22_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r22_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r22_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r22_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r22_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r22_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r22_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
    · by_cases h30_60 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have hi := strictBool_r22_part30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r22_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r22_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r22_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r22_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r22_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r22_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r22_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h45_60 : V < 52
        · by_cases h45_52 : V < 48
          · by_cases h45_48 : V < 46
            · have hi := strictBool_r22_part45 (V-45) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r22_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r22_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r22_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
        · by_cases h52_60 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r22_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r22_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r22_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r22_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
  · by_cases h60_121 : V < 90
    · by_cases h60_90 : V < 75
      · by_cases h60_75 : V < 67
        · by_cases h60_67 : V < 63
          · by_cases h60_63 : V < 61
            · have hi := strictBool_r22_part60 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r22_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r22_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r22_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r22_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r22_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r22_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r22_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
      · by_cases h75_90 : V < 82
        · by_cases h75_82 : V < 78
          · by_cases h75_78 : V < 76
            · have hi := strictBool_r22_part75 (V-75) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r22_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r22_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r22_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r22_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r22_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r22_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r22_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
    · by_cases h90_121 : V < 105
      · by_cases h90_105 : V < 97
        · by_cases h90_97 : V < 93
          · by_cases h90_93 : V < 91
            · have hi := strictBool_r22_part90 (V-90) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r22_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r22_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r22_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r22_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r22_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r22_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r22_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h105_121 : V < 113
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r22_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r22_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r22_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r22_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h113_121 : V < 117
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r22_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r22_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r22_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r22_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r22_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictFast_r22 (V : ℕ) (hV : V ∈ List.range 121) : StrictAtFast (BoundaryTailBaseFastData.row 22 V) 22 V :=
  strictBool_sound _ _ _ (strictBool_r22 V hV)

theorem strict_r22 (V : ℕ) (hV : V ∈ List.range 121) : StrictCheckAt 22 V :=
  strictAtFast_sound _ _ _ (valid_r22 V hV) (strictFast_r22 V hV)

theorem zeroCertificate_r22_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (0+i)) 22 (0+i) := by decide +kernel

theorem zeroCertificate_r22_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (8+i)) 22 (8+i) := by decide +kernel

theorem zeroCertificate_r22_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (16+i)) 22 (16+i) := by decide +kernel

theorem zeroCertificate_r22_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (24+i)) 22 (24+i) := by decide +kernel

theorem zeroCertificate_r22_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (32+i)) 22 (32+i) := by decide +kernel

theorem zeroCertificate_r22_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (40+i)) 22 (40+i) := by decide +kernel

theorem zeroCertificate_r22_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (48+i)) 22 (48+i) := by decide +kernel

theorem zeroCertificate_r22_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (56+i)) 22 (56+i) := by decide +kernel

theorem zeroCertificate_r22_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (64+i)) 22 (64+i) := by decide +kernel

theorem zeroCertificate_r22_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (72+i)) 22 (72+i) := by decide +kernel

theorem zeroCertificate_r22_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (80+i)) 22 (80+i) := by decide +kernel

theorem zeroCertificate_r22_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (88+i)) 22 (88+i) := by decide +kernel

theorem zeroCertificate_r22_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (96+i)) 22 (96+i) := by decide +kernel

theorem zeroCertificate_r22_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (104+i)) 22 (104+i) := by decide +kernel

theorem zeroCertificate_r22_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 22 (112+i)) 22 (112+i) := by decide +kernel

theorem zeroCertificate_r22_part120 : ∀ i ∈ List.range 1, ZeroCertificate (BoundaryTailBaseFastData.row 22 (120+i)) 22 (120+i) := by decide +kernel

theorem zeroCertificate_r22 (V : ℕ) (hV : V ∈ List.range 121) : ZeroCertificate (BoundaryTailBaseFastData.row 22 V) 22 V := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := zeroCertificate_r22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r22 (V : ℕ) (hV : V ∈ List.range 121) : ZeroAtFast 22 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r22 V hV) (zeroCertificate_r22 V hV)

theorem zero_r22 (V : ℕ) (hV : V ∈ List.range 121) : ZeroCheckAt 22 V :=
  zeroAtFast_sound _ _ (zeroFast_r22 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r26_part0 : ∀ i ∈ List.range 8, CorrectAt 26 (0+i) := by decide +kernel

theorem correct_r26_part8 : ∀ i ∈ List.range 8, CorrectAt 26 (8+i) := by decide +kernel

theorem correct_r26_part16 : ∀ i ∈ List.range 8, CorrectAt 26 (16+i) := by decide +kernel

theorem correct_r26_part24 : ∀ i ∈ List.range 8, CorrectAt 26 (24+i) := by decide +kernel

theorem correct_r26_part32 : ∀ i ∈ List.range 8, CorrectAt 26 (32+i) := by decide +kernel

theorem correct_r26_part40 : ∀ i ∈ List.range 8, CorrectAt 26 (40+i) := by decide +kernel

theorem correct_r26_part48 : ∀ i ∈ List.range 8, CorrectAt 26 (48+i) := by decide +kernel

theorem correct_r26_part56 : ∀ i ∈ List.range 8, CorrectAt 26 (56+i) := by decide +kernel

theorem correct_r26_part64 : ∀ i ∈ List.range 8, CorrectAt 26 (64+i) := by decide +kernel

theorem correct_r26_part72 : ∀ i ∈ List.range 8, CorrectAt 26 (72+i) := by decide +kernel

theorem correct_r26_part80 : ∀ i ∈ List.range 8, CorrectAt 26 (80+i) := by decide +kernel

theorem correct_r26_part88 : ∀ i ∈ List.range 8, CorrectAt 26 (88+i) := by decide +kernel

theorem correct_r26_part96 : ∀ i ∈ List.range 8, CorrectAt 26 (96+i) := by decide +kernel

theorem correct_r26_part104 : ∀ i ∈ List.range 8, CorrectAt 26 (104+i) := by decide +kernel

theorem correct_r26_part112 : ∀ i ∈ List.range 5, CorrectAt 26 (112+i) := by decide +kernel

theorem correct_r26 (V : ℕ) (hV : V ∈ List.range 117) : CorrectAt 26 V := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := correct_r26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r26_part0 : ∀ i ∈ List.range 8, BaseCheckAt 26 (0+i) := by decide +kernel

theorem base_r26_part8 : ∀ i ∈ List.range 8, BaseCheckAt 26 (8+i) := by decide +kernel

theorem base_r26_part16 : ∀ i ∈ List.range 8, BaseCheckAt 26 (16+i) := by decide +kernel

theorem base_r26_part24 : ∀ i ∈ List.range 8, BaseCheckAt 26 (24+i) := by decide +kernel

theorem base_r26_part32 : ∀ i ∈ List.range 8, BaseCheckAt 26 (32+i) := by decide +kernel

theorem base_r26_part40 : ∀ i ∈ List.range 8, BaseCheckAt 26 (40+i) := by decide +kernel

theorem base_r26_part48 : ∀ i ∈ List.range 8, BaseCheckAt 26 (48+i) := by decide +kernel

theorem base_r26_part56 : ∀ i ∈ List.range 8, BaseCheckAt 26 (56+i) := by decide +kernel

theorem base_r26_part64 : ∀ i ∈ List.range 8, BaseCheckAt 26 (64+i) := by decide +kernel

theorem base_r26_part72 : ∀ i ∈ List.range 8, BaseCheckAt 26 (72+i) := by decide +kernel

theorem base_r26_part80 : ∀ i ∈ List.range 8, BaseCheckAt 26 (80+i) := by decide +kernel

theorem base_r26_part88 : ∀ i ∈ List.range 8, BaseCheckAt 26 (88+i) := by decide +kernel

theorem base_r26_part96 : ∀ i ∈ List.range 8, BaseCheckAt 26 (96+i) := by decide +kernel

theorem base_r26_part104 : ∀ i ∈ List.range 8, BaseCheckAt 26 (104+i) := by decide +kernel

theorem base_r26_part112 : ∀ i ∈ List.range 5, BaseCheckAt 26 (112+i) := by decide +kernel

theorem base_r26 (V : ℕ) (hV : V ∈ List.range 117) : BaseCheckAt 26 V := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := base_r26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r26_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (0+i)) 26 (0+i) := by decide +kernel

theorem valid_r26_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (8+i)) 26 (8+i) := by decide +kernel

theorem valid_r26_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (16+i)) 26 (16+i) := by decide +kernel

theorem valid_r26_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (24+i)) 26 (24+i) := by decide +kernel

theorem valid_r26_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (32+i)) 26 (32+i) := by decide +kernel

theorem valid_r26_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (40+i)) 26 (40+i) := by decide +kernel

theorem valid_r26_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (48+i)) 26 (48+i) := by decide +kernel

theorem valid_r26_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (56+i)) 26 (56+i) := by decide +kernel

theorem valid_r26_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (64+i)) 26 (64+i) := by decide +kernel

theorem valid_r26_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (72+i)) 26 (72+i) := by decide +kernel

theorem valid_r26_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (80+i)) 26 (80+i) := by decide +kernel

theorem valid_r26_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (88+i)) 26 (88+i) := by decide +kernel

theorem valid_r26_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (96+i)) 26 (96+i) := by decide +kernel

theorem valid_r26_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 26 (104+i)) 26 (104+i) := by decide +kernel

theorem valid_r26_part112 : ∀ i ∈ List.range 5, Valid (BoundaryTailBaseFastData.row 26 (112+i)) 26 (112+i) := by decide +kernel

theorem valid_r26 (V : ℕ) (hV : V ∈ List.range 117) : Valid (BoundaryTailBaseFastData.row 26 V) 26 V := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := valid_r26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r26_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (0+i)) 26 (0+i) = true := by decide +kernel

theorem strictBool_r26_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (1+i)) 26 (1+i) = true := by decide +kernel

theorem strictBool_r26_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (2+i)) 26 (2+i) = true := by decide +kernel

theorem strictBool_r26_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (3+i)) 26 (3+i) = true := by decide +kernel

theorem strictBool_r26_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (4+i)) 26 (4+i) = true := by decide +kernel

theorem strictBool_r26_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (5+i)) 26 (5+i) = true := by decide +kernel

theorem strictBool_r26_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (6+i)) 26 (6+i) = true := by decide +kernel

theorem strictBool_r26_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (7+i)) 26 (7+i) = true := by decide +kernel

theorem strictBool_r26_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (8+i)) 26 (8+i) = true := by decide +kernel

theorem strictBool_r26_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (9+i)) 26 (9+i) = true := by decide +kernel

theorem strictBool_r26_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (10+i)) 26 (10+i) = true := by decide +kernel

theorem strictBool_r26_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (11+i)) 26 (11+i) = true := by decide +kernel

theorem strictBool_r26_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (12+i)) 26 (12+i) = true := by decide +kernel

theorem strictBool_r26_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (13+i)) 26 (13+i) = true := by decide +kernel

theorem strictBool_r26_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (14+i)) 26 (14+i) = true := by decide +kernel

theorem strictBool_r26_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (15+i)) 26 (15+i) = true := by decide +kernel

theorem strictBool_r26_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (16+i)) 26 (16+i) = true := by decide +kernel

theorem strictBool_r26_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (17+i)) 26 (17+i) = true := by decide +kernel

theorem strictBool_r26_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (18+i)) 26 (18+i) = true := by decide +kernel

theorem strictBool_r26_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (19+i)) 26 (19+i) = true := by decide +kernel

theorem strictBool_r26_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (20+i)) 26 (20+i) = true := by decide +kernel

theorem strictBool_r26_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (21+i)) 26 (21+i) = true := by decide +kernel

theorem strictBool_r26_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (22+i)) 26 (22+i) = true := by decide +kernel

theorem strictBool_r26_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (23+i)) 26 (23+i) = true := by decide +kernel

theorem strictBool_r26_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (24+i)) 26 (24+i) = true := by decide +kernel

theorem strictBool_r26_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (25+i)) 26 (25+i) = true := by decide +kernel

theorem strictBool_r26_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (26+i)) 26 (26+i) = true := by decide +kernel

theorem strictBool_r26_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (27+i)) 26 (27+i) = true := by decide +kernel

theorem strictBool_r26_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (28+i)) 26 (28+i) = true := by decide +kernel

theorem strictBool_r26_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (29+i)) 26 (29+i) = true := by decide +kernel

theorem strictBool_r26_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (30+i)) 26 (30+i) = true := by decide +kernel

theorem strictBool_r26_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (31+i)) 26 (31+i) = true := by decide +kernel

theorem strictBool_r26_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (32+i)) 26 (32+i) = true := by decide +kernel

theorem strictBool_r26_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (33+i)) 26 (33+i) = true := by decide +kernel

theorem strictBool_r26_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (34+i)) 26 (34+i) = true := by decide +kernel

theorem strictBool_r26_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (35+i)) 26 (35+i) = true := by decide +kernel

theorem strictBool_r26_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (36+i)) 26 (36+i) = true := by decide +kernel

theorem strictBool_r26_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (37+i)) 26 (37+i) = true := by decide +kernel

theorem strictBool_r26_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (38+i)) 26 (38+i) = true := by decide +kernel

theorem strictBool_r26_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (39+i)) 26 (39+i) = true := by decide +kernel

theorem strictBool_r26_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (40+i)) 26 (40+i) = true := by decide +kernel

theorem strictBool_r26_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (41+i)) 26 (41+i) = true := by decide +kernel

theorem strictBool_r26_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (42+i)) 26 (42+i) = true := by decide +kernel

theorem strictBool_r26_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (43+i)) 26 (43+i) = true := by decide +kernel

theorem strictBool_r26_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (44+i)) 26 (44+i) = true := by decide +kernel

theorem strictBool_r26_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (45+i)) 26 (45+i) = true := by decide +kernel

theorem strictBool_r26_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (46+i)) 26 (46+i) = true := by decide +kernel

theorem strictBool_r26_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (47+i)) 26 (47+i) = true := by decide +kernel

theorem strictBool_r26_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (48+i)) 26 (48+i) = true := by decide +kernel

theorem strictBool_r26_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (49+i)) 26 (49+i) = true := by decide +kernel

theorem strictBool_r26_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (50+i)) 26 (50+i) = true := by decide +kernel

theorem strictBool_r26_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (51+i)) 26 (51+i) = true := by decide +kernel

theorem strictBool_r26_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (52+i)) 26 (52+i) = true := by decide +kernel

theorem strictBool_r26_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (53+i)) 26 (53+i) = true := by decide +kernel

theorem strictBool_r26_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (54+i)) 26 (54+i) = true := by decide +kernel

theorem strictBool_r26_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (55+i)) 26 (55+i) = true := by decide +kernel

theorem strictBool_r26_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (56+i)) 26 (56+i) = true := by decide +kernel

theorem strictBool_r26_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (57+i)) 26 (57+i) = true := by decide +kernel

theorem strictBool_r26_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (58+i)) 26 (58+i) = true := by decide +kernel

theorem strictBool_r26_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (59+i)) 26 (59+i) = true := by decide +kernel

theorem strictBool_r26_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (60+i)) 26 (60+i) = true := by decide +kernel

theorem strictBool_r26_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (61+i)) 26 (61+i) = true := by decide +kernel

theorem strictBool_r26_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (62+i)) 26 (62+i) = true := by decide +kernel

theorem strictBool_r26_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (63+i)) 26 (63+i) = true := by decide +kernel

theorem strictBool_r26_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (64+i)) 26 (64+i) = true := by decide +kernel

theorem strictBool_r26_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (65+i)) 26 (65+i) = true := by decide +kernel

theorem strictBool_r26_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (66+i)) 26 (66+i) = true := by decide +kernel

theorem strictBool_r26_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (67+i)) 26 (67+i) = true := by decide +kernel

theorem strictBool_r26_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (68+i)) 26 (68+i) = true := by decide +kernel

theorem strictBool_r26_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (69+i)) 26 (69+i) = true := by decide +kernel

theorem strictBool_r26_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (70+i)) 26 (70+i) = true := by decide +kernel

theorem strictBool_r26_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (71+i)) 26 (71+i) = true := by decide +kernel

theorem strictBool_r26_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (72+i)) 26 (72+i) = true := by decide +kernel

theorem strictBool_r26_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (73+i)) 26 (73+i) = true := by decide +kernel

theorem strictBool_r26_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (74+i)) 26 (74+i) = true := by decide +kernel

theorem strictBool_r26_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (75+i)) 26 (75+i) = true := by decide +kernel

theorem strictBool_r26_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (76+i)) 26 (76+i) = true := by decide +kernel

theorem strictBool_r26_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (77+i)) 26 (77+i) = true := by decide +kernel

theorem strictBool_r26_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (78+i)) 26 (78+i) = true := by decide +kernel

theorem strictBool_r26_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (79+i)) 26 (79+i) = true := by decide +kernel

theorem strictBool_r26_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (80+i)) 26 (80+i) = true := by decide +kernel

theorem strictBool_r26_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (81+i)) 26 (81+i) = true := by decide +kernel

theorem strictBool_r26_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (82+i)) 26 (82+i) = true := by decide +kernel

theorem strictBool_r26_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (83+i)) 26 (83+i) = true := by decide +kernel

theorem strictBool_r26_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (84+i)) 26 (84+i) = true := by decide +kernel

theorem strictBool_r26_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (85+i)) 26 (85+i) = true := by decide +kernel

theorem strictBool_r26_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (86+i)) 26 (86+i) = true := by decide +kernel

theorem strictBool_r26_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (87+i)) 26 (87+i) = true := by decide +kernel

theorem strictBool_r26_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (88+i)) 26 (88+i) = true := by decide +kernel

theorem strictBool_r26_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (89+i)) 26 (89+i) = true := by decide +kernel

theorem strictBool_r26_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (90+i)) 26 (90+i) = true := by decide +kernel

theorem strictBool_r26_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (91+i)) 26 (91+i) = true := by decide +kernel

theorem strictBool_r26_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (92+i)) 26 (92+i) = true := by decide +kernel

theorem strictBool_r26_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (93+i)) 26 (93+i) = true := by decide +kernel

theorem strictBool_r26_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (94+i)) 26 (94+i) = true := by decide +kernel

theorem strictBool_r26_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (95+i)) 26 (95+i) = true := by decide +kernel

theorem strictBool_r26_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (96+i)) 26 (96+i) = true := by decide +kernel

theorem strictBool_r26_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (97+i)) 26 (97+i) = true := by decide +kernel

theorem strictBool_r26_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (98+i)) 26 (98+i) = true := by decide +kernel

theorem strictBool_r26_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (99+i)) 26 (99+i) = true := by decide +kernel

theorem strictBool_r26_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (100+i)) 26 (100+i) = true := by decide +kernel

theorem strictBool_r26_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (101+i)) 26 (101+i) = true := by decide +kernel

theorem strictBool_r26_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (102+i)) 26 (102+i) = true := by decide +kernel

theorem strictBool_r26_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (103+i)) 26 (103+i) = true := by decide +kernel

theorem strictBool_r26_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (104+i)) 26 (104+i) = true := by decide +kernel

theorem strictBool_r26_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (105+i)) 26 (105+i) = true := by decide +kernel

theorem strictBool_r26_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (106+i)) 26 (106+i) = true := by decide +kernel

theorem strictBool_r26_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (107+i)) 26 (107+i) = true := by decide +kernel

theorem strictBool_r26_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (108+i)) 26 (108+i) = true := by decide +kernel

theorem strictBool_r26_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (109+i)) 26 (109+i) = true := by decide +kernel

theorem strictBool_r26_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (110+i)) 26 (110+i) = true := by decide +kernel

theorem strictBool_r26_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (111+i)) 26 (111+i) = true := by decide +kernel

theorem strictBool_r26_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (112+i)) 26 (112+i) = true := by decide +kernel

theorem strictBool_r26_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (113+i)) 26 (113+i) = true := by decide +kernel

theorem strictBool_r26_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (114+i)) 26 (114+i) = true := by decide +kernel

theorem strictBool_r26_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (115+i)) 26 (115+i) = true := by decide +kernel

theorem strictBool_r26_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 26 (116+i)) 26 (116+i) = true := by decide +kernel

theorem strictBool_r26 (V : ℕ) (hV : V ∈ List.range 117) : strictBool (BoundaryTailBaseFastData.row 26 V) 26 V = true := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 58
  · by_cases h0_58 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r26_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r26_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r26_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r26_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r26_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r26_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r26_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r26_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r26_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r26_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r26_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r26_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r26_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r26_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r26_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r26_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h29_58 : V < 43
      · by_cases h29_43 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have hi := strictBool_r26_part29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r26_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r26_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r26_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
        · by_cases h36_43 : V < 39
          · by_cases h36_39 : V < 37
            · have hi := strictBool_r26_part36 (V-36) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r26_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r26_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r26_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
      · by_cases h43_58 : V < 50
        · by_cases h43_50 : V < 46
          · by_cases h43_46 : V < 44
            · have hi := strictBool_r26_part43 (V-43) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r26_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r26_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r26_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r26_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r26_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r26_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r26_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
  · by_cases h58_117 : V < 87
    · by_cases h58_87 : V < 72
      · by_cases h58_72 : V < 65
        · by_cases h58_65 : V < 61
          · by_cases h58_61 : V < 59
            · have hi := strictBool_r26_part58 (V-58) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r26_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r26_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r26_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · by_cases h65_72 : V < 68
          · by_cases h65_68 : V < 66
            · have hi := strictBool_r26_part65 (V-65) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r26_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r26_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r26_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
      · by_cases h72_87 : V < 79
        · by_cases h72_79 : V < 75
          · by_cases h72_75 : V < 73
            · have hi := strictBool_r26_part72 (V-72) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r26_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r26_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r26_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r26_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r26_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r26_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r26_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
    · by_cases h87_117 : V < 102
      · by_cases h87_102 : V < 94
        · by_cases h87_94 : V < 90
          · by_cases h87_90 : V < 88
            · have hi := strictBool_r26_part87 (V-87) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r26_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r26_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r26_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
        · by_cases h94_102 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r26_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r26_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r26_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r26_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
      · by_cases h102_117 : V < 109
        · by_cases h102_109 : V < 105
          · by_cases h102_105 : V < 103
            · have hi := strictBool_r26_part102 (V-102) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r26_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r26_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r26_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
        · by_cases h109_117 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r26_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r26_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r26_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r26_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r26_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi

theorem strictFast_r26 (V : ℕ) (hV : V ∈ List.range 117) : StrictAtFast (BoundaryTailBaseFastData.row 26 V) 26 V :=
  strictBool_sound _ _ _ (strictBool_r26 V hV)

theorem strict_r26 (V : ℕ) (hV : V ∈ List.range 117) : StrictCheckAt 26 V :=
  strictAtFast_sound _ _ _ (valid_r26 V hV) (strictFast_r26 V hV)

theorem zeroCertificate_r26_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (0+i)) 26 (0+i) := by decide +kernel

theorem zeroCertificate_r26_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (8+i)) 26 (8+i) := by decide +kernel

theorem zeroCertificate_r26_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (16+i)) 26 (16+i) := by decide +kernel

theorem zeroCertificate_r26_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (24+i)) 26 (24+i) := by decide +kernel

theorem zeroCertificate_r26_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (32+i)) 26 (32+i) := by decide +kernel

theorem zeroCertificate_r26_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (40+i)) 26 (40+i) := by decide +kernel

theorem zeroCertificate_r26_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (48+i)) 26 (48+i) := by decide +kernel

theorem zeroCertificate_r26_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (56+i)) 26 (56+i) := by decide +kernel

theorem zeroCertificate_r26_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (64+i)) 26 (64+i) := by decide +kernel

theorem zeroCertificate_r26_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (72+i)) 26 (72+i) := by decide +kernel

theorem zeroCertificate_r26_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (80+i)) 26 (80+i) := by decide +kernel

theorem zeroCertificate_r26_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (88+i)) 26 (88+i) := by decide +kernel

theorem zeroCertificate_r26_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (96+i)) 26 (96+i) := by decide +kernel

theorem zeroCertificate_r26_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 26 (104+i)) 26 (104+i) := by decide +kernel

theorem zeroCertificate_r26_part112 : ∀ i ∈ List.range 5, ZeroCertificate (BoundaryTailBaseFastData.row 26 (112+i)) 26 (112+i) := by decide +kernel

theorem zeroCertificate_r26 (V : ℕ) (hV : V ∈ List.range 117) : ZeroCertificate (BoundaryTailBaseFastData.row 26 V) 26 V := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := zeroCertificate_r26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r26 (V : ℕ) (hV : V ∈ List.range 117) : ZeroAtFast 26 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r26 V hV) (zeroCertificate_r26 V hV)

theorem zero_r26 (V : ℕ) (hV : V ∈ List.range 117) : ZeroCheckAt 26 V :=
  zeroAtFast_sound _ _ (zeroFast_r26 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r30_part0 : ∀ i ∈ List.range 8, CorrectAt 30 (0+i) := by decide +kernel

theorem correct_r30_part8 : ∀ i ∈ List.range 8, CorrectAt 30 (8+i) := by decide +kernel

theorem correct_r30_part16 : ∀ i ∈ List.range 8, CorrectAt 30 (16+i) := by decide +kernel

theorem correct_r30_part24 : ∀ i ∈ List.range 8, CorrectAt 30 (24+i) := by decide +kernel

theorem correct_r30_part32 : ∀ i ∈ List.range 8, CorrectAt 30 (32+i) := by decide +kernel

theorem correct_r30_part40 : ∀ i ∈ List.range 8, CorrectAt 30 (40+i) := by decide +kernel

theorem correct_r30_part48 : ∀ i ∈ List.range 8, CorrectAt 30 (48+i) := by decide +kernel

theorem correct_r30_part56 : ∀ i ∈ List.range 8, CorrectAt 30 (56+i) := by decide +kernel

theorem correct_r30_part64 : ∀ i ∈ List.range 8, CorrectAt 30 (64+i) := by decide +kernel

theorem correct_r30_part72 : ∀ i ∈ List.range 8, CorrectAt 30 (72+i) := by decide +kernel

theorem correct_r30_part80 : ∀ i ∈ List.range 8, CorrectAt 30 (80+i) := by decide +kernel

theorem correct_r30_part88 : ∀ i ∈ List.range 8, CorrectAt 30 (88+i) := by decide +kernel

theorem correct_r30_part96 : ∀ i ∈ List.range 8, CorrectAt 30 (96+i) := by decide +kernel

theorem correct_r30_part104 : ∀ i ∈ List.range 8, CorrectAt 30 (104+i) := by decide +kernel

theorem correct_r30_part112 : ∀ i ∈ List.range 1, CorrectAt 30 (112+i) := by decide +kernel

theorem correct_r30 (V : ℕ) (hV : V ∈ List.range 113) : CorrectAt 30 V := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := correct_r30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r30_part0 : ∀ i ∈ List.range 8, BaseCheckAt 30 (0+i) := by decide +kernel

theorem base_r30_part8 : ∀ i ∈ List.range 8, BaseCheckAt 30 (8+i) := by decide +kernel

theorem base_r30_part16 : ∀ i ∈ List.range 8, BaseCheckAt 30 (16+i) := by decide +kernel

theorem base_r30_part24 : ∀ i ∈ List.range 8, BaseCheckAt 30 (24+i) := by decide +kernel

theorem base_r30_part32 : ∀ i ∈ List.range 8, BaseCheckAt 30 (32+i) := by decide +kernel

theorem base_r30_part40 : ∀ i ∈ List.range 8, BaseCheckAt 30 (40+i) := by decide +kernel

theorem base_r30_part48 : ∀ i ∈ List.range 8, BaseCheckAt 30 (48+i) := by decide +kernel

theorem base_r30_part56 : ∀ i ∈ List.range 8, BaseCheckAt 30 (56+i) := by decide +kernel

theorem base_r30_part64 : ∀ i ∈ List.range 8, BaseCheckAt 30 (64+i) := by decide +kernel

theorem base_r30_part72 : ∀ i ∈ List.range 8, BaseCheckAt 30 (72+i) := by decide +kernel

theorem base_r30_part80 : ∀ i ∈ List.range 8, BaseCheckAt 30 (80+i) := by decide +kernel

theorem base_r30_part88 : ∀ i ∈ List.range 8, BaseCheckAt 30 (88+i) := by decide +kernel

theorem base_r30_part96 : ∀ i ∈ List.range 8, BaseCheckAt 30 (96+i) := by decide +kernel

theorem base_r30_part104 : ∀ i ∈ List.range 8, BaseCheckAt 30 (104+i) := by decide +kernel

theorem base_r30_part112 : ∀ i ∈ List.range 1, BaseCheckAt 30 (112+i) := by decide +kernel

theorem base_r30 (V : ℕ) (hV : V ∈ List.range 113) : BaseCheckAt 30 V := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := base_r30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r30_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (0+i)) 30 (0+i) := by decide +kernel

theorem valid_r30_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (8+i)) 30 (8+i) := by decide +kernel

theorem valid_r30_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (16+i)) 30 (16+i) := by decide +kernel

theorem valid_r30_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (24+i)) 30 (24+i) := by decide +kernel

theorem valid_r30_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (32+i)) 30 (32+i) := by decide +kernel

theorem valid_r30_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (40+i)) 30 (40+i) := by decide +kernel

theorem valid_r30_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (48+i)) 30 (48+i) := by decide +kernel

theorem valid_r30_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (56+i)) 30 (56+i) := by decide +kernel

theorem valid_r30_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (64+i)) 30 (64+i) := by decide +kernel

theorem valid_r30_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (72+i)) 30 (72+i) := by decide +kernel

theorem valid_r30_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (80+i)) 30 (80+i) := by decide +kernel

theorem valid_r30_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (88+i)) 30 (88+i) := by decide +kernel

theorem valid_r30_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (96+i)) 30 (96+i) := by decide +kernel

theorem valid_r30_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 30 (104+i)) 30 (104+i) := by decide +kernel

theorem valid_r30_part112 : ∀ i ∈ List.range 1, Valid (BoundaryTailBaseFastData.row 30 (112+i)) 30 (112+i) := by decide +kernel

theorem valid_r30 (V : ℕ) (hV : V ∈ List.range 113) : Valid (BoundaryTailBaseFastData.row 30 V) 30 V := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := valid_r30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r30_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (0+i)) 30 (0+i) = true := by decide +kernel

theorem strictBool_r30_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (1+i)) 30 (1+i) = true := by decide +kernel

theorem strictBool_r30_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (2+i)) 30 (2+i) = true := by decide +kernel

theorem strictBool_r30_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (3+i)) 30 (3+i) = true := by decide +kernel

theorem strictBool_r30_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (4+i)) 30 (4+i) = true := by decide +kernel

theorem strictBool_r30_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (5+i)) 30 (5+i) = true := by decide +kernel

theorem strictBool_r30_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (6+i)) 30 (6+i) = true := by decide +kernel

theorem strictBool_r30_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (7+i)) 30 (7+i) = true := by decide +kernel

theorem strictBool_r30_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (8+i)) 30 (8+i) = true := by decide +kernel

theorem strictBool_r30_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (9+i)) 30 (9+i) = true := by decide +kernel

theorem strictBool_r30_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (10+i)) 30 (10+i) = true := by decide +kernel

theorem strictBool_r30_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (11+i)) 30 (11+i) = true := by decide +kernel

theorem strictBool_r30_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (12+i)) 30 (12+i) = true := by decide +kernel

theorem strictBool_r30_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (13+i)) 30 (13+i) = true := by decide +kernel

theorem strictBool_r30_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (14+i)) 30 (14+i) = true := by decide +kernel

theorem strictBool_r30_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (15+i)) 30 (15+i) = true := by decide +kernel

theorem strictBool_r30_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (16+i)) 30 (16+i) = true := by decide +kernel

theorem strictBool_r30_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (17+i)) 30 (17+i) = true := by decide +kernel

theorem strictBool_r30_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (18+i)) 30 (18+i) = true := by decide +kernel

theorem strictBool_r30_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (19+i)) 30 (19+i) = true := by decide +kernel

theorem strictBool_r30_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (20+i)) 30 (20+i) = true := by decide +kernel

theorem strictBool_r30_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (21+i)) 30 (21+i) = true := by decide +kernel

theorem strictBool_r30_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (22+i)) 30 (22+i) = true := by decide +kernel

theorem strictBool_r30_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (23+i)) 30 (23+i) = true := by decide +kernel

theorem strictBool_r30_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (24+i)) 30 (24+i) = true := by decide +kernel

theorem strictBool_r30_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (25+i)) 30 (25+i) = true := by decide +kernel

theorem strictBool_r30_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (26+i)) 30 (26+i) = true := by decide +kernel

theorem strictBool_r30_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (27+i)) 30 (27+i) = true := by decide +kernel

theorem strictBool_r30_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (28+i)) 30 (28+i) = true := by decide +kernel

theorem strictBool_r30_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (29+i)) 30 (29+i) = true := by decide +kernel

theorem strictBool_r30_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (30+i)) 30 (30+i) = true := by decide +kernel

theorem strictBool_r30_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (31+i)) 30 (31+i) = true := by decide +kernel

theorem strictBool_r30_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (32+i)) 30 (32+i) = true := by decide +kernel

theorem strictBool_r30_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (33+i)) 30 (33+i) = true := by decide +kernel

theorem strictBool_r30_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (34+i)) 30 (34+i) = true := by decide +kernel

theorem strictBool_r30_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (35+i)) 30 (35+i) = true := by decide +kernel

theorem strictBool_r30_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (36+i)) 30 (36+i) = true := by decide +kernel

theorem strictBool_r30_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (37+i)) 30 (37+i) = true := by decide +kernel

theorem strictBool_r30_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (38+i)) 30 (38+i) = true := by decide +kernel

theorem strictBool_r30_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (39+i)) 30 (39+i) = true := by decide +kernel

theorem strictBool_r30_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (40+i)) 30 (40+i) = true := by decide +kernel

theorem strictBool_r30_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (41+i)) 30 (41+i) = true := by decide +kernel

theorem strictBool_r30_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (42+i)) 30 (42+i) = true := by decide +kernel

theorem strictBool_r30_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (43+i)) 30 (43+i) = true := by decide +kernel

theorem strictBool_r30_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (44+i)) 30 (44+i) = true := by decide +kernel

theorem strictBool_r30_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (45+i)) 30 (45+i) = true := by decide +kernel

theorem strictBool_r30_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (46+i)) 30 (46+i) = true := by decide +kernel

theorem strictBool_r30_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (47+i)) 30 (47+i) = true := by decide +kernel

theorem strictBool_r30_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (48+i)) 30 (48+i) = true := by decide +kernel

theorem strictBool_r30_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (49+i)) 30 (49+i) = true := by decide +kernel

theorem strictBool_r30_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (50+i)) 30 (50+i) = true := by decide +kernel

theorem strictBool_r30_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (51+i)) 30 (51+i) = true := by decide +kernel

theorem strictBool_r30_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (52+i)) 30 (52+i) = true := by decide +kernel

theorem strictBool_r30_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (53+i)) 30 (53+i) = true := by decide +kernel

theorem strictBool_r30_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (54+i)) 30 (54+i) = true := by decide +kernel

theorem strictBool_r30_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (55+i)) 30 (55+i) = true := by decide +kernel

theorem strictBool_r30_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (56+i)) 30 (56+i) = true := by decide +kernel

theorem strictBool_r30_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (57+i)) 30 (57+i) = true := by decide +kernel

theorem strictBool_r30_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (58+i)) 30 (58+i) = true := by decide +kernel

theorem strictBool_r30_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (59+i)) 30 (59+i) = true := by decide +kernel

theorem strictBool_r30_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (60+i)) 30 (60+i) = true := by decide +kernel

theorem strictBool_r30_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (61+i)) 30 (61+i) = true := by decide +kernel

theorem strictBool_r30_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (62+i)) 30 (62+i) = true := by decide +kernel

theorem strictBool_r30_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (63+i)) 30 (63+i) = true := by decide +kernel

theorem strictBool_r30_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (64+i)) 30 (64+i) = true := by decide +kernel

theorem strictBool_r30_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (65+i)) 30 (65+i) = true := by decide +kernel

theorem strictBool_r30_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (66+i)) 30 (66+i) = true := by decide +kernel

theorem strictBool_r30_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (67+i)) 30 (67+i) = true := by decide +kernel

theorem strictBool_r30_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (68+i)) 30 (68+i) = true := by decide +kernel

theorem strictBool_r30_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (69+i)) 30 (69+i) = true := by decide +kernel

theorem strictBool_r30_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (70+i)) 30 (70+i) = true := by decide +kernel

theorem strictBool_r30_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (71+i)) 30 (71+i) = true := by decide +kernel

theorem strictBool_r30_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (72+i)) 30 (72+i) = true := by decide +kernel

theorem strictBool_r30_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (73+i)) 30 (73+i) = true := by decide +kernel

theorem strictBool_r30_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (74+i)) 30 (74+i) = true := by decide +kernel

theorem strictBool_r30_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (75+i)) 30 (75+i) = true := by decide +kernel

theorem strictBool_r30_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (76+i)) 30 (76+i) = true := by decide +kernel

theorem strictBool_r30_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (77+i)) 30 (77+i) = true := by decide +kernel

theorem strictBool_r30_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (78+i)) 30 (78+i) = true := by decide +kernel

theorem strictBool_r30_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (79+i)) 30 (79+i) = true := by decide +kernel

theorem strictBool_r30_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (80+i)) 30 (80+i) = true := by decide +kernel

theorem strictBool_r30_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (81+i)) 30 (81+i) = true := by decide +kernel

theorem strictBool_r30_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (82+i)) 30 (82+i) = true := by decide +kernel

theorem strictBool_r30_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (83+i)) 30 (83+i) = true := by decide +kernel

theorem strictBool_r30_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (84+i)) 30 (84+i) = true := by decide +kernel

theorem strictBool_r30_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (85+i)) 30 (85+i) = true := by decide +kernel

theorem strictBool_r30_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (86+i)) 30 (86+i) = true := by decide +kernel

theorem strictBool_r30_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (87+i)) 30 (87+i) = true := by decide +kernel

theorem strictBool_r30_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (88+i)) 30 (88+i) = true := by decide +kernel

theorem strictBool_r30_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (89+i)) 30 (89+i) = true := by decide +kernel

theorem strictBool_r30_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (90+i)) 30 (90+i) = true := by decide +kernel

theorem strictBool_r30_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (91+i)) 30 (91+i) = true := by decide +kernel

theorem strictBool_r30_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (92+i)) 30 (92+i) = true := by decide +kernel

theorem strictBool_r30_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (93+i)) 30 (93+i) = true := by decide +kernel

theorem strictBool_r30_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (94+i)) 30 (94+i) = true := by decide +kernel

theorem strictBool_r30_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (95+i)) 30 (95+i) = true := by decide +kernel

theorem strictBool_r30_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (96+i)) 30 (96+i) = true := by decide +kernel

theorem strictBool_r30_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (97+i)) 30 (97+i) = true := by decide +kernel

theorem strictBool_r30_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (98+i)) 30 (98+i) = true := by decide +kernel

theorem strictBool_r30_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (99+i)) 30 (99+i) = true := by decide +kernel

theorem strictBool_r30_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (100+i)) 30 (100+i) = true := by decide +kernel

theorem strictBool_r30_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (101+i)) 30 (101+i) = true := by decide +kernel

theorem strictBool_r30_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (102+i)) 30 (102+i) = true := by decide +kernel

theorem strictBool_r30_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (103+i)) 30 (103+i) = true := by decide +kernel

theorem strictBool_r30_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (104+i)) 30 (104+i) = true := by decide +kernel

theorem strictBool_r30_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (105+i)) 30 (105+i) = true := by decide +kernel

theorem strictBool_r30_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (106+i)) 30 (106+i) = true := by decide +kernel

theorem strictBool_r30_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (107+i)) 30 (107+i) = true := by decide +kernel

theorem strictBool_r30_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (108+i)) 30 (108+i) = true := by decide +kernel

theorem strictBool_r30_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (109+i)) 30 (109+i) = true := by decide +kernel

theorem strictBool_r30_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (110+i)) 30 (110+i) = true := by decide +kernel

theorem strictBool_r30_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (111+i)) 30 (111+i) = true := by decide +kernel

theorem strictBool_r30_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 30 (112+i)) 30 (112+i) = true := by decide +kernel

theorem strictBool_r30 (V : ℕ) (hV : V ∈ List.range 113) : strictBool (BoundaryTailBaseFastData.row 30 V) 30 V = true := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r30_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r30_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r30_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r30_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r30_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r30_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r30_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r30_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r30_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r30_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r30_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r30_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have hi := strictBool_r30_part21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r30_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r30_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r30_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
    · by_cases h28_56 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have hi := strictBool_r30_part28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r30_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r30_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r30_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have hi := strictBool_r30_part35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r30_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r30_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r30_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
      · by_cases h42_56 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have hi := strictBool_r30_part42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r30_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r30_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r30_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h49_56 : V < 52
          · by_cases h49_52 : V < 50
            · have hi := strictBool_r30_part49 (V-49) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r30_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r30_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r30_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 84
    · by_cases h56_84 : V < 70
      · by_cases h56_70 : V < 63
        · by_cases h56_63 : V < 59
          · by_cases h56_59 : V < 57
            · have hi := strictBool_r30_part56 (V-56) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r30_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r30_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r30_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have hi := strictBool_r30_part63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r30_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r30_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r30_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
      · by_cases h70_84 : V < 77
        · by_cases h70_77 : V < 73
          · by_cases h70_73 : V < 71
            · have hi := strictBool_r30_part70 (V-70) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r30_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r30_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r30_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_84 : V < 80
          · by_cases h77_80 : V < 78
            · have hi := strictBool_r30_part77 (V-77) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r30_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r30_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r30_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
    · by_cases h84_113 : V < 98
      · by_cases h84_98 : V < 91
        · by_cases h84_91 : V < 87
          · by_cases h84_87 : V < 85
            · have hi := strictBool_r30_part84 (V-84) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r30_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r30_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r30_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have hi := strictBool_r30_part91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r30_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r30_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r30_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
      · by_cases h98_113 : V < 105
        · by_cases h98_105 : V < 101
          · by_cases h98_101 : V < 99
            · have hi := strictBool_r30_part98 (V-98) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r30_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r30_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r30_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r30_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r30_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r30_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r30_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r30_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictFast_r30 (V : ℕ) (hV : V ∈ List.range 113) : StrictAtFast (BoundaryTailBaseFastData.row 30 V) 30 V :=
  strictBool_sound _ _ _ (strictBool_r30 V hV)

theorem strict_r30 (V : ℕ) (hV : V ∈ List.range 113) : StrictCheckAt 30 V :=
  strictAtFast_sound _ _ _ (valid_r30 V hV) (strictFast_r30 V hV)

theorem zeroCertificate_r30_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (0+i)) 30 (0+i) := by decide +kernel

theorem zeroCertificate_r30_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (8+i)) 30 (8+i) := by decide +kernel

theorem zeroCertificate_r30_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (16+i)) 30 (16+i) := by decide +kernel

theorem zeroCertificate_r30_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (24+i)) 30 (24+i) := by decide +kernel

theorem zeroCertificate_r30_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (32+i)) 30 (32+i) := by decide +kernel

theorem zeroCertificate_r30_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (40+i)) 30 (40+i) := by decide +kernel

theorem zeroCertificate_r30_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (48+i)) 30 (48+i) := by decide +kernel

theorem zeroCertificate_r30_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (56+i)) 30 (56+i) := by decide +kernel

theorem zeroCertificate_r30_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (64+i)) 30 (64+i) := by decide +kernel

theorem zeroCertificate_r30_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (72+i)) 30 (72+i) := by decide +kernel

theorem zeroCertificate_r30_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (80+i)) 30 (80+i) := by decide +kernel

theorem zeroCertificate_r30_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (88+i)) 30 (88+i) := by decide +kernel

theorem zeroCertificate_r30_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (96+i)) 30 (96+i) := by decide +kernel

theorem zeroCertificate_r30_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 30 (104+i)) 30 (104+i) := by decide +kernel

theorem zeroCertificate_r30_part112 : ∀ i ∈ List.range 1, ZeroCertificate (BoundaryTailBaseFastData.row 30 (112+i)) 30 (112+i) := by decide +kernel

theorem zeroCertificate_r30 (V : ℕ) (hV : V ∈ List.range 113) : ZeroCertificate (BoundaryTailBaseFastData.row 30 V) 30 V := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := zeroCertificate_r30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r30 (V : ℕ) (hV : V ∈ List.range 113) : ZeroAtFast 30 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r30 V hV) (zeroCertificate_r30 V hV)

theorem zero_r30 (V : ℕ) (hV : V ∈ List.range 113) : ZeroCheckAt 30 V :=
  zeroAtFast_sound _ _ (zeroFast_r30 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
