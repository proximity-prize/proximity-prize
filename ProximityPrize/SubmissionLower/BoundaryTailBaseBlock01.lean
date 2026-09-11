import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r1_part0 : ∀ i ∈ List.range 8, CorrectAt 1 (0+i) := by decide +kernel

theorem correct_r1_part8 : ∀ i ∈ List.range 8, CorrectAt 1 (8+i) := by decide +kernel

theorem correct_r1_part16 : ∀ i ∈ List.range 8, CorrectAt 1 (16+i) := by decide +kernel

theorem correct_r1_part24 : ∀ i ∈ List.range 8, CorrectAt 1 (24+i) := by decide +kernel

theorem correct_r1_part32 : ∀ i ∈ List.range 8, CorrectAt 1 (32+i) := by decide +kernel

theorem correct_r1_part40 : ∀ i ∈ List.range 8, CorrectAt 1 (40+i) := by decide +kernel

theorem correct_r1_part48 : ∀ i ∈ List.range 8, CorrectAt 1 (48+i) := by decide +kernel

theorem correct_r1_part56 : ∀ i ∈ List.range 8, CorrectAt 1 (56+i) := by decide +kernel

theorem correct_r1_part64 : ∀ i ∈ List.range 8, CorrectAt 1 (64+i) := by decide +kernel

theorem correct_r1_part72 : ∀ i ∈ List.range 8, CorrectAt 1 (72+i) := by decide +kernel

theorem correct_r1_part80 : ∀ i ∈ List.range 8, CorrectAt 1 (80+i) := by decide +kernel

theorem correct_r1_part88 : ∀ i ∈ List.range 8, CorrectAt 1 (88+i) := by decide +kernel

theorem correct_r1_part96 : ∀ i ∈ List.range 8, CorrectAt 1 (96+i) := by decide +kernel

theorem correct_r1_part104 : ∀ i ∈ List.range 8, CorrectAt 1 (104+i) := by decide +kernel

theorem correct_r1_part112 : ∀ i ∈ List.range 8, CorrectAt 1 (112+i) := by decide +kernel

theorem correct_r1_part120 : ∀ i ∈ List.range 8, CorrectAt 1 (120+i) := by decide +kernel

theorem correct_r1_part128 : ∀ i ∈ List.range 8, CorrectAt 1 (128+i) := by decide +kernel

theorem correct_r1_part136 : ∀ i ∈ List.range 6, CorrectAt 1 (136+i) := by decide +kernel

theorem correct_r1 (V : ℕ) (hV : V ∈ List.range 142) : CorrectAt 1 V := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := correct_r1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := correct_r1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r1_part0 : ∀ i ∈ List.range 8, BaseCheckAt 1 (0+i) := by decide +kernel

theorem base_r1_part8 : ∀ i ∈ List.range 8, BaseCheckAt 1 (8+i) := by decide +kernel

theorem base_r1_part16 : ∀ i ∈ List.range 8, BaseCheckAt 1 (16+i) := by decide +kernel

theorem base_r1_part24 : ∀ i ∈ List.range 8, BaseCheckAt 1 (24+i) := by decide +kernel

theorem base_r1_part32 : ∀ i ∈ List.range 8, BaseCheckAt 1 (32+i) := by decide +kernel

theorem base_r1_part40 : ∀ i ∈ List.range 8, BaseCheckAt 1 (40+i) := by decide +kernel

theorem base_r1_part48 : ∀ i ∈ List.range 8, BaseCheckAt 1 (48+i) := by decide +kernel

theorem base_r1_part56 : ∀ i ∈ List.range 8, BaseCheckAt 1 (56+i) := by decide +kernel

theorem base_r1_part64 : ∀ i ∈ List.range 8, BaseCheckAt 1 (64+i) := by decide +kernel

theorem base_r1_part72 : ∀ i ∈ List.range 8, BaseCheckAt 1 (72+i) := by decide +kernel

theorem base_r1_part80 : ∀ i ∈ List.range 8, BaseCheckAt 1 (80+i) := by decide +kernel

theorem base_r1_part88 : ∀ i ∈ List.range 8, BaseCheckAt 1 (88+i) := by decide +kernel

theorem base_r1_part96 : ∀ i ∈ List.range 8, BaseCheckAt 1 (96+i) := by decide +kernel

theorem base_r1_part104 : ∀ i ∈ List.range 8, BaseCheckAt 1 (104+i) := by decide +kernel

theorem base_r1_part112 : ∀ i ∈ List.range 8, BaseCheckAt 1 (112+i) := by decide +kernel

theorem base_r1_part120 : ∀ i ∈ List.range 8, BaseCheckAt 1 (120+i) := by decide +kernel

theorem base_r1_part128 : ∀ i ∈ List.range 8, BaseCheckAt 1 (128+i) := by decide +kernel

theorem base_r1_part136 : ∀ i ∈ List.range 6, BaseCheckAt 1 (136+i) := by decide +kernel

theorem base_r1 (V : ℕ) (hV : V ∈ List.range 142) : BaseCheckAt 1 V := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := base_r1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := base_r1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r1_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (0+i)) 1 (0+i) := by decide +kernel

theorem valid_r1_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (8+i)) 1 (8+i) := by decide +kernel

theorem valid_r1_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (16+i)) 1 (16+i) := by decide +kernel

theorem valid_r1_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (24+i)) 1 (24+i) := by decide +kernel

theorem valid_r1_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (32+i)) 1 (32+i) := by decide +kernel

theorem valid_r1_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (40+i)) 1 (40+i) := by decide +kernel

theorem valid_r1_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (48+i)) 1 (48+i) := by decide +kernel

theorem valid_r1_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (56+i)) 1 (56+i) := by decide +kernel

theorem valid_r1_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (64+i)) 1 (64+i) := by decide +kernel

theorem valid_r1_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (72+i)) 1 (72+i) := by decide +kernel

theorem valid_r1_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (80+i)) 1 (80+i) := by decide +kernel

theorem valid_r1_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (88+i)) 1 (88+i) := by decide +kernel

theorem valid_r1_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (96+i)) 1 (96+i) := by decide +kernel

theorem valid_r1_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (104+i)) 1 (104+i) := by decide +kernel

theorem valid_r1_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (112+i)) 1 (112+i) := by decide +kernel

theorem valid_r1_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (120+i)) 1 (120+i) := by decide +kernel

theorem valid_r1_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 1 (128+i)) 1 (128+i) := by decide +kernel

theorem valid_r1_part136 : ∀ i ∈ List.range 6, Valid (BoundaryTailBaseFastData.row 1 (136+i)) 1 (136+i) := by decide +kernel

theorem valid_r1 (V : ℕ) (hV : V ∈ List.range 142) : Valid (BoundaryTailBaseFastData.row 1 V) 1 V := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := valid_r1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := valid_r1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r1_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (0+i)) 1 (0+i) = true := by decide +kernel

theorem strictBool_r1_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (1+i)) 1 (1+i) = true := by decide +kernel

theorem strictBool_r1_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (2+i)) 1 (2+i) = true := by decide +kernel

theorem strictBool_r1_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (3+i)) 1 (3+i) = true := by decide +kernel

theorem strictBool_r1_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (4+i)) 1 (4+i) = true := by decide +kernel

theorem strictBool_r1_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (5+i)) 1 (5+i) = true := by decide +kernel

theorem strictBool_r1_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (6+i)) 1 (6+i) = true := by decide +kernel

theorem strictBool_r1_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (7+i)) 1 (7+i) = true := by decide +kernel

theorem strictBool_r1_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (8+i)) 1 (8+i) = true := by decide +kernel

theorem strictBool_r1_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (9+i)) 1 (9+i) = true := by decide +kernel

theorem strictBool_r1_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (10+i)) 1 (10+i) = true := by decide +kernel

theorem strictBool_r1_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (11+i)) 1 (11+i) = true := by decide +kernel

theorem strictBool_r1_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (12+i)) 1 (12+i) = true := by decide +kernel

theorem strictBool_r1_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (13+i)) 1 (13+i) = true := by decide +kernel

theorem strictBool_r1_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (14+i)) 1 (14+i) = true := by decide +kernel

theorem strictBool_r1_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (15+i)) 1 (15+i) = true := by decide +kernel

theorem strictBool_r1_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (16+i)) 1 (16+i) = true := by decide +kernel

theorem strictBool_r1_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (17+i)) 1 (17+i) = true := by decide +kernel

theorem strictBool_r1_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (18+i)) 1 (18+i) = true := by decide +kernel

theorem strictBool_r1_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (19+i)) 1 (19+i) = true := by decide +kernel

theorem strictBool_r1_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (20+i)) 1 (20+i) = true := by decide +kernel

theorem strictBool_r1_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (21+i)) 1 (21+i) = true := by decide +kernel

theorem strictBool_r1_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (22+i)) 1 (22+i) = true := by decide +kernel

theorem strictBool_r1_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (23+i)) 1 (23+i) = true := by decide +kernel

theorem strictBool_r1_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (24+i)) 1 (24+i) = true := by decide +kernel

theorem strictBool_r1_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (25+i)) 1 (25+i) = true := by decide +kernel

theorem strictBool_r1_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (26+i)) 1 (26+i) = true := by decide +kernel

theorem strictBool_r1_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (27+i)) 1 (27+i) = true := by decide +kernel

theorem strictBool_r1_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (28+i)) 1 (28+i) = true := by decide +kernel

theorem strictBool_r1_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (29+i)) 1 (29+i) = true := by decide +kernel

theorem strictBool_r1_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (30+i)) 1 (30+i) = true := by decide +kernel

theorem strictBool_r1_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (31+i)) 1 (31+i) = true := by decide +kernel

theorem strictBool_r1_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (32+i)) 1 (32+i) = true := by decide +kernel

theorem strictBool_r1_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (33+i)) 1 (33+i) = true := by decide +kernel

theorem strictBool_r1_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (34+i)) 1 (34+i) = true := by decide +kernel

theorem strictBool_r1_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (35+i)) 1 (35+i) = true := by decide +kernel

theorem strictBool_r1_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (36+i)) 1 (36+i) = true := by decide +kernel

theorem strictBool_r1_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (37+i)) 1 (37+i) = true := by decide +kernel

theorem strictBool_r1_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (38+i)) 1 (38+i) = true := by decide +kernel

theorem strictBool_r1_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (39+i)) 1 (39+i) = true := by decide +kernel

theorem strictBool_r1_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (40+i)) 1 (40+i) = true := by decide +kernel

theorem strictBool_r1_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (41+i)) 1 (41+i) = true := by decide +kernel

theorem strictBool_r1_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (42+i)) 1 (42+i) = true := by decide +kernel

theorem strictBool_r1_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (43+i)) 1 (43+i) = true := by decide +kernel

theorem strictBool_r1_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (44+i)) 1 (44+i) = true := by decide +kernel

theorem strictBool_r1_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (45+i)) 1 (45+i) = true := by decide +kernel

theorem strictBool_r1_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (46+i)) 1 (46+i) = true := by decide +kernel

theorem strictBool_r1_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (47+i)) 1 (47+i) = true := by decide +kernel

theorem strictBool_r1_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (48+i)) 1 (48+i) = true := by decide +kernel

theorem strictBool_r1_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (49+i)) 1 (49+i) = true := by decide +kernel

theorem strictBool_r1_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (50+i)) 1 (50+i) = true := by decide +kernel

theorem strictBool_r1_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (51+i)) 1 (51+i) = true := by decide +kernel

theorem strictBool_r1_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (52+i)) 1 (52+i) = true := by decide +kernel

theorem strictBool_r1_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (53+i)) 1 (53+i) = true := by decide +kernel

theorem strictBool_r1_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (54+i)) 1 (54+i) = true := by decide +kernel

theorem strictBool_r1_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (55+i)) 1 (55+i) = true := by decide +kernel

theorem strictBool_r1_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (56+i)) 1 (56+i) = true := by decide +kernel

theorem strictBool_r1_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (57+i)) 1 (57+i) = true := by decide +kernel

theorem strictBool_r1_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (58+i)) 1 (58+i) = true := by decide +kernel

theorem strictBool_r1_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (59+i)) 1 (59+i) = true := by decide +kernel

theorem strictBool_r1_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (60+i)) 1 (60+i) = true := by decide +kernel

theorem strictBool_r1_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (61+i)) 1 (61+i) = true := by decide +kernel

theorem strictBool_r1_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (62+i)) 1 (62+i) = true := by decide +kernel

theorem strictBool_r1_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (63+i)) 1 (63+i) = true := by decide +kernel

theorem strictBool_r1_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (64+i)) 1 (64+i) = true := by decide +kernel

theorem strictBool_r1_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (65+i)) 1 (65+i) = true := by decide +kernel

theorem strictBool_r1_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (66+i)) 1 (66+i) = true := by decide +kernel

theorem strictBool_r1_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (67+i)) 1 (67+i) = true := by decide +kernel

theorem strictBool_r1_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (68+i)) 1 (68+i) = true := by decide +kernel

theorem strictBool_r1_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (69+i)) 1 (69+i) = true := by decide +kernel

theorem strictBool_r1_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (70+i)) 1 (70+i) = true := by decide +kernel

theorem strictBool_r1_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (71+i)) 1 (71+i) = true := by decide +kernel

theorem strictBool_r1_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (72+i)) 1 (72+i) = true := by decide +kernel

theorem strictBool_r1_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (73+i)) 1 (73+i) = true := by decide +kernel

theorem strictBool_r1_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (74+i)) 1 (74+i) = true := by decide +kernel

theorem strictBool_r1_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (75+i)) 1 (75+i) = true := by decide +kernel

theorem strictBool_r1_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (76+i)) 1 (76+i) = true := by decide +kernel

theorem strictBool_r1_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (77+i)) 1 (77+i) = true := by decide +kernel

theorem strictBool_r1_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (78+i)) 1 (78+i) = true := by decide +kernel

theorem strictBool_r1_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (79+i)) 1 (79+i) = true := by decide +kernel

theorem strictBool_r1_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (80+i)) 1 (80+i) = true := by decide +kernel

theorem strictBool_r1_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (81+i)) 1 (81+i) = true := by decide +kernel

theorem strictBool_r1_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (82+i)) 1 (82+i) = true := by decide +kernel

theorem strictBool_r1_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (83+i)) 1 (83+i) = true := by decide +kernel

theorem strictBool_r1_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (84+i)) 1 (84+i) = true := by decide +kernel

theorem strictBool_r1_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (85+i)) 1 (85+i) = true := by decide +kernel

theorem strictBool_r1_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (86+i)) 1 (86+i) = true := by decide +kernel

theorem strictBool_r1_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (87+i)) 1 (87+i) = true := by decide +kernel

theorem strictBool_r1_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (88+i)) 1 (88+i) = true := by decide +kernel

theorem strictBool_r1_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (89+i)) 1 (89+i) = true := by decide +kernel

theorem strictBool_r1_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (90+i)) 1 (90+i) = true := by decide +kernel

theorem strictBool_r1_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (91+i)) 1 (91+i) = true := by decide +kernel

theorem strictBool_r1_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (92+i)) 1 (92+i) = true := by decide +kernel

theorem strictBool_r1_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (93+i)) 1 (93+i) = true := by decide +kernel

theorem strictBool_r1_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (94+i)) 1 (94+i) = true := by decide +kernel

theorem strictBool_r1_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (95+i)) 1 (95+i) = true := by decide +kernel

theorem strictBool_r1_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (96+i)) 1 (96+i) = true := by decide +kernel

theorem strictBool_r1_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (97+i)) 1 (97+i) = true := by decide +kernel

theorem strictBool_r1_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (98+i)) 1 (98+i) = true := by decide +kernel

theorem strictBool_r1_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (99+i)) 1 (99+i) = true := by decide +kernel

theorem strictBool_r1_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (100+i)) 1 (100+i) = true := by decide +kernel

theorem strictBool_r1_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (101+i)) 1 (101+i) = true := by decide +kernel

theorem strictBool_r1_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (102+i)) 1 (102+i) = true := by decide +kernel

theorem strictBool_r1_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (103+i)) 1 (103+i) = true := by decide +kernel

theorem strictBool_r1_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (104+i)) 1 (104+i) = true := by decide +kernel

theorem strictBool_r1_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (105+i)) 1 (105+i) = true := by decide +kernel

theorem strictBool_r1_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (106+i)) 1 (106+i) = true := by decide +kernel

theorem strictBool_r1_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (107+i)) 1 (107+i) = true := by decide +kernel

theorem strictBool_r1_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (108+i)) 1 (108+i) = true := by decide +kernel

theorem strictBool_r1_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (109+i)) 1 (109+i) = true := by decide +kernel

theorem strictBool_r1_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (110+i)) 1 (110+i) = true := by decide +kernel

theorem strictBool_r1_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (111+i)) 1 (111+i) = true := by decide +kernel

theorem strictBool_r1_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (112+i)) 1 (112+i) = true := by decide +kernel

theorem strictBool_r1_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (113+i)) 1 (113+i) = true := by decide +kernel

theorem strictBool_r1_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (114+i)) 1 (114+i) = true := by decide +kernel

theorem strictBool_r1_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (115+i)) 1 (115+i) = true := by decide +kernel

theorem strictBool_r1_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (116+i)) 1 (116+i) = true := by decide +kernel

theorem strictBool_r1_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (117+i)) 1 (117+i) = true := by decide +kernel

theorem strictBool_r1_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (118+i)) 1 (118+i) = true := by decide +kernel

theorem strictBool_r1_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (119+i)) 1 (119+i) = true := by decide +kernel

theorem strictBool_r1_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (120+i)) 1 (120+i) = true := by decide +kernel

theorem strictBool_r1_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (121+i)) 1 (121+i) = true := by decide +kernel

theorem strictBool_r1_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (122+i)) 1 (122+i) = true := by decide +kernel

theorem strictBool_r1_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (123+i)) 1 (123+i) = true := by decide +kernel

theorem strictBool_r1_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (124+i)) 1 (124+i) = true := by decide +kernel

theorem strictBool_r1_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (125+i)) 1 (125+i) = true := by decide +kernel

theorem strictBool_r1_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (126+i)) 1 (126+i) = true := by decide +kernel

theorem strictBool_r1_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (127+i)) 1 (127+i) = true := by decide +kernel

theorem strictBool_r1_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (128+i)) 1 (128+i) = true := by decide +kernel

theorem strictBool_r1_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (129+i)) 1 (129+i) = true := by decide +kernel

theorem strictBool_r1_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (130+i)) 1 (130+i) = true := by decide +kernel

theorem strictBool_r1_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (131+i)) 1 (131+i) = true := by decide +kernel

theorem strictBool_r1_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (132+i)) 1 (132+i) = true := by decide +kernel

theorem strictBool_r1_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (133+i)) 1 (133+i) = true := by decide +kernel

theorem strictBool_r1_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (134+i)) 1 (134+i) = true := by decide +kernel

theorem strictBool_r1_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (135+i)) 1 (135+i) = true := by decide +kernel

theorem strictBool_r1_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (136+i)) 1 (136+i) = true := by decide +kernel

theorem strictBool_r1_part137 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (137+i)) 1 (137+i) = true := by decide +kernel

theorem strictBool_r1_part138 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (138+i)) 1 (138+i) = true := by decide +kernel

theorem strictBool_r1_part139 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (139+i)) 1 (139+i) = true := by decide +kernel

theorem strictBool_r1_part140 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (140+i)) 1 (140+i) = true := by decide +kernel

theorem strictBool_r1_part141 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 1 (141+i)) 1 (141+i) = true := by decide +kernel

theorem strictBool_r1 (V : ℕ) (hV : V ∈ List.range 142) : strictBool (BoundaryTailBaseFastData.row 1 V) 1 V = true := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 71
  · by_cases h0_71 : V < 35
    · by_cases h0_35 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r1_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r1_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r1_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r1_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r1_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r1_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r1_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r1_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r1_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35 : V < 26
        · by_cases h17_26 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r1_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r1_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r1_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26 : V < 24
              · have hi := strictBool_r1_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26 : V < 25
                · have hi := strictBool_r1_part24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35 : V < 30
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r1_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r1_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35 : V < 32
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r1_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35 : V < 33
              · have hi := strictBool_r1_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35 : V < 34
                · have hi := strictBool_r1_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_71 : V < 53
      · by_cases h35_53 : V < 44
        · by_cases h35_44 : V < 39
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r1_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r1_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_44 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r1_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_44 : V < 42
              · have hi := strictBool_r1_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · by_cases h42_44 : V < 43
                · have hi := strictBool_r1_part42 (V-42) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part43 (V-43) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
        · by_cases h44_53 : V < 48
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r1_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r1_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
          · by_cases h48_53 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r1_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_53 : V < 51
              · have hi := strictBool_r1_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · by_cases h51_53 : V < 52
                · have hi := strictBool_r1_part51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part52 (V-52) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
      · by_cases h53_71 : V < 62
        · by_cases h53_62 : V < 57
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r1_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r1_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h57_62 : V < 59
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r1_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_62 : V < 60
              · have hi := strictBool_r1_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · by_cases h60_62 : V < 61
                · have hi := strictBool_r1_part60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part61 (V-61) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
        · by_cases h62_71 : V < 66
          · by_cases h62_66 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r1_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r1_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_71 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r1_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_71 : V < 69
              · have hi := strictBool_r1_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · by_cases h69_71 : V < 70
                · have hi := strictBool_r1_part69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part70 (V-70) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
  · by_cases h71_142 : V < 106
    · by_cases h71_106 : V < 88
      · by_cases h71_88 : V < 79
        · by_cases h71_79 : V < 75
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r1_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r1_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r1_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r1_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
        · by_cases h79_88 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r1_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r1_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_88 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r1_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_88 : V < 86
              · have hi := strictBool_r1_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · by_cases h86_88 : V < 87
                · have hi := strictBool_r1_part86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part87 (V-87) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
      · by_cases h88_106 : V < 97
        · by_cases h88_97 : V < 92
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r1_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r1_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_97 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r1_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_97 : V < 95
              · have hi := strictBool_r1_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · by_cases h95_97 : V < 96
                · have hi := strictBool_r1_part95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part96 (V-96) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · by_cases h97_106 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r1_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r1_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_106 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r1_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_106 : V < 104
              · have hi := strictBool_r1_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · by_cases h104_106 : V < 105
                · have hi := strictBool_r1_part104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part105 (V-105) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
    · by_cases h106_142 : V < 124
      · by_cases h106_124 : V < 115
        · by_cases h106_115 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r1_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r1_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_115 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r1_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_115 : V < 113
              · have hi := strictBool_r1_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · by_cases h113_115 : V < 114
                · have hi := strictBool_r1_part113 (V-113) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part114 (V-114) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
        · by_cases h115_124 : V < 119
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r1_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r1_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
          · by_cases h119_124 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r1_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_124 : V < 122
              · have hi := strictBool_r1_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · by_cases h122_124 : V < 123
                · have hi := strictBool_r1_part122 (V-122) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part123 (V-123) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
      · by_cases h124_142 : V < 133
        · by_cases h124_133 : V < 128
          · by_cases h124_128 : V < 126
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r1_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r1_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
          · by_cases h128_133 : V < 130
            · by_cases h128_130 : V < 129
              · have hi := strictBool_r1_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
            · by_cases h130_133 : V < 131
              · have hi := strictBool_r1_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
              · by_cases h131_133 : V < 132
                · have hi := strictBool_r1_part131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
        · by_cases h133_142 : V < 137
          · by_cases h133_137 : V < 135
            · by_cases h133_135 : V < 134
              · have hi := strictBool_r1_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
            · by_cases h135_137 : V < 136
              · have hi := strictBool_r1_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
          · by_cases h137_142 : V < 139
            · by_cases h137_139 : V < 138
              · have hi := strictBool_r1_part137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
              · have hi := strictBool_r1_part138 (V-138) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
            · by_cases h139_142 : V < 140
              · have hi := strictBool_r1_part139 (V-139) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi
              · by_cases h140_142 : V < 141
                · have hi := strictBool_r1_part140 (V-140) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 140 ≤ V by omega)] using hi
                · have hi := strictBool_r1_part141 (V-141) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 141 ≤ V by omega)] using hi

theorem strictFast_r1 (V : ℕ) (hV : V ∈ List.range 142) : StrictAtFast (BoundaryTailBaseFastData.row 1 V) 1 V :=
  strictBool_sound _ _ _ (strictBool_r1 V hV)

theorem strict_r1 (V : ℕ) (hV : V ∈ List.range 142) : StrictCheckAt 1 V :=
  strictAtFast_sound _ _ _ (valid_r1 V hV) (strictFast_r1 V hV)

theorem zeroCertificate_r1_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (0+i)) 1 (0+i) := by decide +kernel

theorem zeroCertificate_r1_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (8+i)) 1 (8+i) := by decide +kernel

theorem zeroCertificate_r1_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (16+i)) 1 (16+i) := by decide +kernel

theorem zeroCertificate_r1_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (24+i)) 1 (24+i) := by decide +kernel

theorem zeroCertificate_r1_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (32+i)) 1 (32+i) := by decide +kernel

theorem zeroCertificate_r1_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (40+i)) 1 (40+i) := by decide +kernel

theorem zeroCertificate_r1_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (48+i)) 1 (48+i) := by decide +kernel

theorem zeroCertificate_r1_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (56+i)) 1 (56+i) := by decide +kernel

theorem zeroCertificate_r1_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (64+i)) 1 (64+i) := by decide +kernel

theorem zeroCertificate_r1_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (72+i)) 1 (72+i) := by decide +kernel

theorem zeroCertificate_r1_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (80+i)) 1 (80+i) := by decide +kernel

theorem zeroCertificate_r1_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (88+i)) 1 (88+i) := by decide +kernel

theorem zeroCertificate_r1_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (96+i)) 1 (96+i) := by decide +kernel

theorem zeroCertificate_r1_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (104+i)) 1 (104+i) := by decide +kernel

theorem zeroCertificate_r1_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (112+i)) 1 (112+i) := by decide +kernel

theorem zeroCertificate_r1_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (120+i)) 1 (120+i) := by decide +kernel

theorem zeroCertificate_r1_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 1 (128+i)) 1 (128+i) := by decide +kernel

theorem zeroCertificate_r1_part136 : ∀ i ∈ List.range 6, ZeroCertificate (BoundaryTailBaseFastData.row 1 (136+i)) 1 (136+i) := by decide +kernel

theorem zeroCertificate_r1 (V : ℕ) (hV : V ∈ List.range 142) : ZeroCertificate (BoundaryTailBaseFastData.row 1 V) 1 V := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := zeroCertificate_r1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := zeroCertificate_r1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r1 (V : ℕ) (hV : V ∈ List.range 142) : ZeroAtFast 1 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r1 V hV) (zeroCertificate_r1 V hV)

theorem zero_r1 (V : ℕ) (hV : V ∈ List.range 142) : ZeroCheckAt 1 V :=
  zeroAtFast_sound _ _ (zeroFast_r1 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r5_part0 : ∀ i ∈ List.range 8, CorrectAt 5 (0+i) := by decide +kernel

theorem correct_r5_part8 : ∀ i ∈ List.range 8, CorrectAt 5 (8+i) := by decide +kernel

theorem correct_r5_part16 : ∀ i ∈ List.range 8, CorrectAt 5 (16+i) := by decide +kernel

theorem correct_r5_part24 : ∀ i ∈ List.range 8, CorrectAt 5 (24+i) := by decide +kernel

theorem correct_r5_part32 : ∀ i ∈ List.range 8, CorrectAt 5 (32+i) := by decide +kernel

theorem correct_r5_part40 : ∀ i ∈ List.range 8, CorrectAt 5 (40+i) := by decide +kernel

theorem correct_r5_part48 : ∀ i ∈ List.range 8, CorrectAt 5 (48+i) := by decide +kernel

theorem correct_r5_part56 : ∀ i ∈ List.range 8, CorrectAt 5 (56+i) := by decide +kernel

theorem correct_r5_part64 : ∀ i ∈ List.range 8, CorrectAt 5 (64+i) := by decide +kernel

theorem correct_r5_part72 : ∀ i ∈ List.range 8, CorrectAt 5 (72+i) := by decide +kernel

theorem correct_r5_part80 : ∀ i ∈ List.range 8, CorrectAt 5 (80+i) := by decide +kernel

theorem correct_r5_part88 : ∀ i ∈ List.range 8, CorrectAt 5 (88+i) := by decide +kernel

theorem correct_r5_part96 : ∀ i ∈ List.range 8, CorrectAt 5 (96+i) := by decide +kernel

theorem correct_r5_part104 : ∀ i ∈ List.range 8, CorrectAt 5 (104+i) := by decide +kernel

theorem correct_r5_part112 : ∀ i ∈ List.range 8, CorrectAt 5 (112+i) := by decide +kernel

theorem correct_r5_part120 : ∀ i ∈ List.range 8, CorrectAt 5 (120+i) := by decide +kernel

theorem correct_r5_part128 : ∀ i ∈ List.range 8, CorrectAt 5 (128+i) := by decide +kernel

theorem correct_r5_part136 : ∀ i ∈ List.range 2, CorrectAt 5 (136+i) := by decide +kernel

theorem correct_r5 (V : ℕ) (hV : V ∈ List.range 138) : CorrectAt 5 V := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := correct_r5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := correct_r5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r5_part0 : ∀ i ∈ List.range 8, BaseCheckAt 5 (0+i) := by decide +kernel

theorem base_r5_part8 : ∀ i ∈ List.range 8, BaseCheckAt 5 (8+i) := by decide +kernel

theorem base_r5_part16 : ∀ i ∈ List.range 8, BaseCheckAt 5 (16+i) := by decide +kernel

theorem base_r5_part24 : ∀ i ∈ List.range 8, BaseCheckAt 5 (24+i) := by decide +kernel

theorem base_r5_part32 : ∀ i ∈ List.range 8, BaseCheckAt 5 (32+i) := by decide +kernel

theorem base_r5_part40 : ∀ i ∈ List.range 8, BaseCheckAt 5 (40+i) := by decide +kernel

theorem base_r5_part48 : ∀ i ∈ List.range 8, BaseCheckAt 5 (48+i) := by decide +kernel

theorem base_r5_part56 : ∀ i ∈ List.range 8, BaseCheckAt 5 (56+i) := by decide +kernel

theorem base_r5_part64 : ∀ i ∈ List.range 8, BaseCheckAt 5 (64+i) := by decide +kernel

theorem base_r5_part72 : ∀ i ∈ List.range 8, BaseCheckAt 5 (72+i) := by decide +kernel

theorem base_r5_part80 : ∀ i ∈ List.range 8, BaseCheckAt 5 (80+i) := by decide +kernel

theorem base_r5_part88 : ∀ i ∈ List.range 8, BaseCheckAt 5 (88+i) := by decide +kernel

theorem base_r5_part96 : ∀ i ∈ List.range 8, BaseCheckAt 5 (96+i) := by decide +kernel

theorem base_r5_part104 : ∀ i ∈ List.range 8, BaseCheckAt 5 (104+i) := by decide +kernel

theorem base_r5_part112 : ∀ i ∈ List.range 8, BaseCheckAt 5 (112+i) := by decide +kernel

theorem base_r5_part120 : ∀ i ∈ List.range 8, BaseCheckAt 5 (120+i) := by decide +kernel

theorem base_r5_part128 : ∀ i ∈ List.range 8, BaseCheckAt 5 (128+i) := by decide +kernel

theorem base_r5_part136 : ∀ i ∈ List.range 2, BaseCheckAt 5 (136+i) := by decide +kernel

theorem base_r5 (V : ℕ) (hV : V ∈ List.range 138) : BaseCheckAt 5 V := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := base_r5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := base_r5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r5_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (0+i)) 5 (0+i) := by decide +kernel

theorem valid_r5_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (8+i)) 5 (8+i) := by decide +kernel

theorem valid_r5_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (16+i)) 5 (16+i) := by decide +kernel

theorem valid_r5_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (24+i)) 5 (24+i) := by decide +kernel

theorem valid_r5_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (32+i)) 5 (32+i) := by decide +kernel

theorem valid_r5_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (40+i)) 5 (40+i) := by decide +kernel

theorem valid_r5_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (48+i)) 5 (48+i) := by decide +kernel

theorem valid_r5_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (56+i)) 5 (56+i) := by decide +kernel

theorem valid_r5_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (64+i)) 5 (64+i) := by decide +kernel

theorem valid_r5_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (72+i)) 5 (72+i) := by decide +kernel

theorem valid_r5_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (80+i)) 5 (80+i) := by decide +kernel

theorem valid_r5_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (88+i)) 5 (88+i) := by decide +kernel

theorem valid_r5_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (96+i)) 5 (96+i) := by decide +kernel

theorem valid_r5_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (104+i)) 5 (104+i) := by decide +kernel

theorem valid_r5_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (112+i)) 5 (112+i) := by decide +kernel

theorem valid_r5_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (120+i)) 5 (120+i) := by decide +kernel

theorem valid_r5_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 5 (128+i)) 5 (128+i) := by decide +kernel

theorem valid_r5_part136 : ∀ i ∈ List.range 2, Valid (BoundaryTailBaseFastData.row 5 (136+i)) 5 (136+i) := by decide +kernel

theorem valid_r5 (V : ℕ) (hV : V ∈ List.range 138) : Valid (BoundaryTailBaseFastData.row 5 V) 5 V := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := valid_r5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := valid_r5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r5_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (0+i)) 5 (0+i) = true := by decide +kernel

theorem strictBool_r5_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (1+i)) 5 (1+i) = true := by decide +kernel

theorem strictBool_r5_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (2+i)) 5 (2+i) = true := by decide +kernel

theorem strictBool_r5_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (3+i)) 5 (3+i) = true := by decide +kernel

theorem strictBool_r5_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (4+i)) 5 (4+i) = true := by decide +kernel

theorem strictBool_r5_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (5+i)) 5 (5+i) = true := by decide +kernel

theorem strictBool_r5_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (6+i)) 5 (6+i) = true := by decide +kernel

theorem strictBool_r5_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (7+i)) 5 (7+i) = true := by decide +kernel

theorem strictBool_r5_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (8+i)) 5 (8+i) = true := by decide +kernel

theorem strictBool_r5_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (9+i)) 5 (9+i) = true := by decide +kernel

theorem strictBool_r5_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (10+i)) 5 (10+i) = true := by decide +kernel

theorem strictBool_r5_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (11+i)) 5 (11+i) = true := by decide +kernel

theorem strictBool_r5_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (12+i)) 5 (12+i) = true := by decide +kernel

theorem strictBool_r5_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (13+i)) 5 (13+i) = true := by decide +kernel

theorem strictBool_r5_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (14+i)) 5 (14+i) = true := by decide +kernel

theorem strictBool_r5_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (15+i)) 5 (15+i) = true := by decide +kernel

theorem strictBool_r5_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (16+i)) 5 (16+i) = true := by decide +kernel

theorem strictBool_r5_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (17+i)) 5 (17+i) = true := by decide +kernel

theorem strictBool_r5_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (18+i)) 5 (18+i) = true := by decide +kernel

theorem strictBool_r5_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (19+i)) 5 (19+i) = true := by decide +kernel

theorem strictBool_r5_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (20+i)) 5 (20+i) = true := by decide +kernel

theorem strictBool_r5_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (21+i)) 5 (21+i) = true := by decide +kernel

theorem strictBool_r5_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (22+i)) 5 (22+i) = true := by decide +kernel

theorem strictBool_r5_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (23+i)) 5 (23+i) = true := by decide +kernel

theorem strictBool_r5_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (24+i)) 5 (24+i) = true := by decide +kernel

theorem strictBool_r5_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (25+i)) 5 (25+i) = true := by decide +kernel

theorem strictBool_r5_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (26+i)) 5 (26+i) = true := by decide +kernel

theorem strictBool_r5_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (27+i)) 5 (27+i) = true := by decide +kernel

theorem strictBool_r5_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (28+i)) 5 (28+i) = true := by decide +kernel

theorem strictBool_r5_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (29+i)) 5 (29+i) = true := by decide +kernel

theorem strictBool_r5_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (30+i)) 5 (30+i) = true := by decide +kernel

theorem strictBool_r5_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (31+i)) 5 (31+i) = true := by decide +kernel

theorem strictBool_r5_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (32+i)) 5 (32+i) = true := by decide +kernel

theorem strictBool_r5_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (33+i)) 5 (33+i) = true := by decide +kernel

theorem strictBool_r5_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (34+i)) 5 (34+i) = true := by decide +kernel

theorem strictBool_r5_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (35+i)) 5 (35+i) = true := by decide +kernel

theorem strictBool_r5_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (36+i)) 5 (36+i) = true := by decide +kernel

theorem strictBool_r5_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (37+i)) 5 (37+i) = true := by decide +kernel

theorem strictBool_r5_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (38+i)) 5 (38+i) = true := by decide +kernel

theorem strictBool_r5_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (39+i)) 5 (39+i) = true := by decide +kernel

theorem strictBool_r5_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (40+i)) 5 (40+i) = true := by decide +kernel

theorem strictBool_r5_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (41+i)) 5 (41+i) = true := by decide +kernel

theorem strictBool_r5_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (42+i)) 5 (42+i) = true := by decide +kernel

theorem strictBool_r5_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (43+i)) 5 (43+i) = true := by decide +kernel

theorem strictBool_r5_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (44+i)) 5 (44+i) = true := by decide +kernel

theorem strictBool_r5_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (45+i)) 5 (45+i) = true := by decide +kernel

theorem strictBool_r5_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (46+i)) 5 (46+i) = true := by decide +kernel

theorem strictBool_r5_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (47+i)) 5 (47+i) = true := by decide +kernel

theorem strictBool_r5_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (48+i)) 5 (48+i) = true := by decide +kernel

theorem strictBool_r5_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (49+i)) 5 (49+i) = true := by decide +kernel

theorem strictBool_r5_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (50+i)) 5 (50+i) = true := by decide +kernel

theorem strictBool_r5_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (51+i)) 5 (51+i) = true := by decide +kernel

theorem strictBool_r5_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (52+i)) 5 (52+i) = true := by decide +kernel

theorem strictBool_r5_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (53+i)) 5 (53+i) = true := by decide +kernel

theorem strictBool_r5_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (54+i)) 5 (54+i) = true := by decide +kernel

theorem strictBool_r5_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (55+i)) 5 (55+i) = true := by decide +kernel

theorem strictBool_r5_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (56+i)) 5 (56+i) = true := by decide +kernel

theorem strictBool_r5_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (57+i)) 5 (57+i) = true := by decide +kernel

theorem strictBool_r5_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (58+i)) 5 (58+i) = true := by decide +kernel

theorem strictBool_r5_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (59+i)) 5 (59+i) = true := by decide +kernel

theorem strictBool_r5_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (60+i)) 5 (60+i) = true := by decide +kernel

theorem strictBool_r5_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (61+i)) 5 (61+i) = true := by decide +kernel

theorem strictBool_r5_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (62+i)) 5 (62+i) = true := by decide +kernel

theorem strictBool_r5_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (63+i)) 5 (63+i) = true := by decide +kernel

theorem strictBool_r5_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (64+i)) 5 (64+i) = true := by decide +kernel

theorem strictBool_r5_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (65+i)) 5 (65+i) = true := by decide +kernel

theorem strictBool_r5_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (66+i)) 5 (66+i) = true := by decide +kernel

theorem strictBool_r5_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (67+i)) 5 (67+i) = true := by decide +kernel

theorem strictBool_r5_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (68+i)) 5 (68+i) = true := by decide +kernel

theorem strictBool_r5_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (69+i)) 5 (69+i) = true := by decide +kernel

theorem strictBool_r5_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (70+i)) 5 (70+i) = true := by decide +kernel

theorem strictBool_r5_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (71+i)) 5 (71+i) = true := by decide +kernel

theorem strictBool_r5_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (72+i)) 5 (72+i) = true := by decide +kernel

theorem strictBool_r5_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (73+i)) 5 (73+i) = true := by decide +kernel

theorem strictBool_r5_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (74+i)) 5 (74+i) = true := by decide +kernel

theorem strictBool_r5_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (75+i)) 5 (75+i) = true := by decide +kernel

theorem strictBool_r5_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (76+i)) 5 (76+i) = true := by decide +kernel

theorem strictBool_r5_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (77+i)) 5 (77+i) = true := by decide +kernel

theorem strictBool_r5_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (78+i)) 5 (78+i) = true := by decide +kernel

theorem strictBool_r5_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (79+i)) 5 (79+i) = true := by decide +kernel

theorem strictBool_r5_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (80+i)) 5 (80+i) = true := by decide +kernel

theorem strictBool_r5_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (81+i)) 5 (81+i) = true := by decide +kernel

theorem strictBool_r5_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (82+i)) 5 (82+i) = true := by decide +kernel

theorem strictBool_r5_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (83+i)) 5 (83+i) = true := by decide +kernel

theorem strictBool_r5_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (84+i)) 5 (84+i) = true := by decide +kernel

theorem strictBool_r5_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (85+i)) 5 (85+i) = true := by decide +kernel

theorem strictBool_r5_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (86+i)) 5 (86+i) = true := by decide +kernel

theorem strictBool_r5_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (87+i)) 5 (87+i) = true := by decide +kernel

theorem strictBool_r5_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (88+i)) 5 (88+i) = true := by decide +kernel

theorem strictBool_r5_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (89+i)) 5 (89+i) = true := by decide +kernel

theorem strictBool_r5_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (90+i)) 5 (90+i) = true := by decide +kernel

theorem strictBool_r5_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (91+i)) 5 (91+i) = true := by decide +kernel

theorem strictBool_r5_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (92+i)) 5 (92+i) = true := by decide +kernel

theorem strictBool_r5_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (93+i)) 5 (93+i) = true := by decide +kernel

theorem strictBool_r5_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (94+i)) 5 (94+i) = true := by decide +kernel

theorem strictBool_r5_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (95+i)) 5 (95+i) = true := by decide +kernel

theorem strictBool_r5_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (96+i)) 5 (96+i) = true := by decide +kernel

theorem strictBool_r5_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (97+i)) 5 (97+i) = true := by decide +kernel

theorem strictBool_r5_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (98+i)) 5 (98+i) = true := by decide +kernel

theorem strictBool_r5_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (99+i)) 5 (99+i) = true := by decide +kernel

theorem strictBool_r5_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (100+i)) 5 (100+i) = true := by decide +kernel

theorem strictBool_r5_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (101+i)) 5 (101+i) = true := by decide +kernel

theorem strictBool_r5_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (102+i)) 5 (102+i) = true := by decide +kernel

theorem strictBool_r5_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (103+i)) 5 (103+i) = true := by decide +kernel

theorem strictBool_r5_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (104+i)) 5 (104+i) = true := by decide +kernel

theorem strictBool_r5_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (105+i)) 5 (105+i) = true := by decide +kernel

theorem strictBool_r5_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (106+i)) 5 (106+i) = true := by decide +kernel

theorem strictBool_r5_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (107+i)) 5 (107+i) = true := by decide +kernel

theorem strictBool_r5_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (108+i)) 5 (108+i) = true := by decide +kernel

theorem strictBool_r5_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (109+i)) 5 (109+i) = true := by decide +kernel

theorem strictBool_r5_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (110+i)) 5 (110+i) = true := by decide +kernel

theorem strictBool_r5_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (111+i)) 5 (111+i) = true := by decide +kernel

theorem strictBool_r5_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (112+i)) 5 (112+i) = true := by decide +kernel

theorem strictBool_r5_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (113+i)) 5 (113+i) = true := by decide +kernel

theorem strictBool_r5_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (114+i)) 5 (114+i) = true := by decide +kernel

theorem strictBool_r5_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (115+i)) 5 (115+i) = true := by decide +kernel

theorem strictBool_r5_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (116+i)) 5 (116+i) = true := by decide +kernel

theorem strictBool_r5_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (117+i)) 5 (117+i) = true := by decide +kernel

theorem strictBool_r5_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (118+i)) 5 (118+i) = true := by decide +kernel

theorem strictBool_r5_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (119+i)) 5 (119+i) = true := by decide +kernel

theorem strictBool_r5_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (120+i)) 5 (120+i) = true := by decide +kernel

theorem strictBool_r5_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (121+i)) 5 (121+i) = true := by decide +kernel

theorem strictBool_r5_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (122+i)) 5 (122+i) = true := by decide +kernel

theorem strictBool_r5_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (123+i)) 5 (123+i) = true := by decide +kernel

theorem strictBool_r5_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (124+i)) 5 (124+i) = true := by decide +kernel

theorem strictBool_r5_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (125+i)) 5 (125+i) = true := by decide +kernel

theorem strictBool_r5_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (126+i)) 5 (126+i) = true := by decide +kernel

theorem strictBool_r5_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (127+i)) 5 (127+i) = true := by decide +kernel

theorem strictBool_r5_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (128+i)) 5 (128+i) = true := by decide +kernel

theorem strictBool_r5_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (129+i)) 5 (129+i) = true := by decide +kernel

theorem strictBool_r5_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (130+i)) 5 (130+i) = true := by decide +kernel

theorem strictBool_r5_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (131+i)) 5 (131+i) = true := by decide +kernel

theorem strictBool_r5_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (132+i)) 5 (132+i) = true := by decide +kernel

theorem strictBool_r5_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (133+i)) 5 (133+i) = true := by decide +kernel

theorem strictBool_r5_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (134+i)) 5 (134+i) = true := by decide +kernel

theorem strictBool_r5_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (135+i)) 5 (135+i) = true := by decide +kernel

theorem strictBool_r5_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (136+i)) 5 (136+i) = true := by decide +kernel

theorem strictBool_r5_part137 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 5 (137+i)) 5 (137+i) = true := by decide +kernel

theorem strictBool_r5 (V : ℕ) (hV : V ∈ List.range 138) : strictBool (BoundaryTailBaseFastData.row 5 V) 5 V = true := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r5_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r5_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r5_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r5_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r5_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r5_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r5_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r5_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r5_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r5_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r5_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r5_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r5_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r5_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r5_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r5_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strictBool_r5_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strictBool_r5_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r5_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r5_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r5_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r5_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r5_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r5_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r5_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strictBool_r5_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strictBool_r5_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r5_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r5_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r5_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_60 : V < 58
              · have hi := strictBool_r5_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · by_cases h58_60 : V < 59
                · have hi := strictBool_r5_part58 (V-58) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r5_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r5_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r5_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_69 : V < 67
              · have hi := strictBool_r5_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · by_cases h67_69 : V < 68
                · have hi := strictBool_r5_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
  · by_cases h69_138 : V < 103
    · by_cases h69_103 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r5_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r5_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r5_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r5_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r5_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r5_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r5_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_86 : V < 84
              · have hi := strictBool_r5_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · by_cases h84_86 : V < 85
                · have hi := strictBool_r5_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
      · by_cases h86_103 : V < 94
        · by_cases h86_94 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r5_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r5_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r5_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r5_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
        · by_cases h94_103 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r5_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r5_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
          · by_cases h98_103 : V < 100
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r5_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_103 : V < 101
              · have hi := strictBool_r5_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · by_cases h101_103 : V < 102
                · have hi := strictBool_r5_part101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part102 (V-102) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
    · by_cases h103_138 : V < 120
      · by_cases h103_120 : V < 111
        · by_cases h103_111 : V < 107
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r5_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r5_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r5_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r5_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
        · by_cases h111_120 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r5_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r5_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
          · by_cases h115_120 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r5_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_120 : V < 118
              · have hi := strictBool_r5_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · by_cases h118_120 : V < 119
                · have hi := strictBool_r5_part118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part119 (V-119) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 129
        · by_cases h120_129 : V < 124
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r5_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r5_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
          · by_cases h124_129 : V < 126
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r5_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_129 : V < 127
              · have hi := strictBool_r5_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · by_cases h127_129 : V < 128
                · have hi := strictBool_r5_part127 (V-127) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
        · by_cases h129_138 : V < 133
          · by_cases h129_133 : V < 131
            · by_cases h129_131 : V < 130
              · have hi := strictBool_r5_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
            · by_cases h131_133 : V < 132
              · have hi := strictBool_r5_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
          · by_cases h133_138 : V < 135
            · by_cases h133_135 : V < 134
              · have hi := strictBool_r5_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · have hi := strictBool_r5_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
            · by_cases h135_138 : V < 136
              · have hi := strictBool_r5_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
              · by_cases h136_138 : V < 137
                · have hi := strictBool_r5_part136 (V-136) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
                · have hi := strictBool_r5_part137 (V-137) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi

theorem strictFast_r5 (V : ℕ) (hV : V ∈ List.range 138) : StrictAtFast (BoundaryTailBaseFastData.row 5 V) 5 V :=
  strictBool_sound _ _ _ (strictBool_r5 V hV)

theorem strict_r5 (V : ℕ) (hV : V ∈ List.range 138) : StrictCheckAt 5 V :=
  strictAtFast_sound _ _ _ (valid_r5 V hV) (strictFast_r5 V hV)

theorem zeroCertificate_r5_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (0+i)) 5 (0+i) := by decide +kernel

theorem zeroCertificate_r5_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (8+i)) 5 (8+i) := by decide +kernel

theorem zeroCertificate_r5_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (16+i)) 5 (16+i) := by decide +kernel

theorem zeroCertificate_r5_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (24+i)) 5 (24+i) := by decide +kernel

theorem zeroCertificate_r5_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (32+i)) 5 (32+i) := by decide +kernel

theorem zeroCertificate_r5_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (40+i)) 5 (40+i) := by decide +kernel

theorem zeroCertificate_r5_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (48+i)) 5 (48+i) := by decide +kernel

theorem zeroCertificate_r5_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (56+i)) 5 (56+i) := by decide +kernel

theorem zeroCertificate_r5_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (64+i)) 5 (64+i) := by decide +kernel

theorem zeroCertificate_r5_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (72+i)) 5 (72+i) := by decide +kernel

theorem zeroCertificate_r5_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (80+i)) 5 (80+i) := by decide +kernel

theorem zeroCertificate_r5_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (88+i)) 5 (88+i) := by decide +kernel

theorem zeroCertificate_r5_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (96+i)) 5 (96+i) := by decide +kernel

theorem zeroCertificate_r5_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (104+i)) 5 (104+i) := by decide +kernel

theorem zeroCertificate_r5_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (112+i)) 5 (112+i) := by decide +kernel

theorem zeroCertificate_r5_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (120+i)) 5 (120+i) := by decide +kernel

theorem zeroCertificate_r5_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 5 (128+i)) 5 (128+i) := by decide +kernel

theorem zeroCertificate_r5_part136 : ∀ i ∈ List.range 2, ZeroCertificate (BoundaryTailBaseFastData.row 5 (136+i)) 5 (136+i) := by decide +kernel

theorem zeroCertificate_r5 (V : ℕ) (hV : V ∈ List.range 138) : ZeroCertificate (BoundaryTailBaseFastData.row 5 V) 5 V := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := zeroCertificate_r5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := zeroCertificate_r5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r5 (V : ℕ) (hV : V ∈ List.range 138) : ZeroAtFast 5 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r5 V hV) (zeroCertificate_r5 V hV)

theorem zero_r5 (V : ℕ) (hV : V ∈ List.range 138) : ZeroCheckAt 5 V :=
  zeroAtFast_sound _ _ (zeroFast_r5 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r9_part0 : ∀ i ∈ List.range 8, CorrectAt 9 (0+i) := by decide +kernel

theorem correct_r9_part8 : ∀ i ∈ List.range 8, CorrectAt 9 (8+i) := by decide +kernel

theorem correct_r9_part16 : ∀ i ∈ List.range 8, CorrectAt 9 (16+i) := by decide +kernel

theorem correct_r9_part24 : ∀ i ∈ List.range 8, CorrectAt 9 (24+i) := by decide +kernel

theorem correct_r9_part32 : ∀ i ∈ List.range 8, CorrectAt 9 (32+i) := by decide +kernel

theorem correct_r9_part40 : ∀ i ∈ List.range 8, CorrectAt 9 (40+i) := by decide +kernel

theorem correct_r9_part48 : ∀ i ∈ List.range 8, CorrectAt 9 (48+i) := by decide +kernel

theorem correct_r9_part56 : ∀ i ∈ List.range 8, CorrectAt 9 (56+i) := by decide +kernel

theorem correct_r9_part64 : ∀ i ∈ List.range 8, CorrectAt 9 (64+i) := by decide +kernel

theorem correct_r9_part72 : ∀ i ∈ List.range 8, CorrectAt 9 (72+i) := by decide +kernel

theorem correct_r9_part80 : ∀ i ∈ List.range 8, CorrectAt 9 (80+i) := by decide +kernel

theorem correct_r9_part88 : ∀ i ∈ List.range 8, CorrectAt 9 (88+i) := by decide +kernel

theorem correct_r9_part96 : ∀ i ∈ List.range 8, CorrectAt 9 (96+i) := by decide +kernel

theorem correct_r9_part104 : ∀ i ∈ List.range 8, CorrectAt 9 (104+i) := by decide +kernel

theorem correct_r9_part112 : ∀ i ∈ List.range 8, CorrectAt 9 (112+i) := by decide +kernel

theorem correct_r9_part120 : ∀ i ∈ List.range 8, CorrectAt 9 (120+i) := by decide +kernel

theorem correct_r9_part128 : ∀ i ∈ List.range 6, CorrectAt 9 (128+i) := by decide +kernel

theorem correct_r9 (V : ℕ) (hV : V ∈ List.range 134) : CorrectAt 9 V := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := correct_r9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := correct_r9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r9_part0 : ∀ i ∈ List.range 8, BaseCheckAt 9 (0+i) := by decide +kernel

theorem base_r9_part8 : ∀ i ∈ List.range 8, BaseCheckAt 9 (8+i) := by decide +kernel

theorem base_r9_part16 : ∀ i ∈ List.range 8, BaseCheckAt 9 (16+i) := by decide +kernel

theorem base_r9_part24 : ∀ i ∈ List.range 8, BaseCheckAt 9 (24+i) := by decide +kernel

theorem base_r9_part32 : ∀ i ∈ List.range 8, BaseCheckAt 9 (32+i) := by decide +kernel

theorem base_r9_part40 : ∀ i ∈ List.range 8, BaseCheckAt 9 (40+i) := by decide +kernel

theorem base_r9_part48 : ∀ i ∈ List.range 8, BaseCheckAt 9 (48+i) := by decide +kernel

theorem base_r9_part56 : ∀ i ∈ List.range 8, BaseCheckAt 9 (56+i) := by decide +kernel

theorem base_r9_part64 : ∀ i ∈ List.range 8, BaseCheckAt 9 (64+i) := by decide +kernel

theorem base_r9_part72 : ∀ i ∈ List.range 8, BaseCheckAt 9 (72+i) := by decide +kernel

theorem base_r9_part80 : ∀ i ∈ List.range 8, BaseCheckAt 9 (80+i) := by decide +kernel

theorem base_r9_part88 : ∀ i ∈ List.range 8, BaseCheckAt 9 (88+i) := by decide +kernel

theorem base_r9_part96 : ∀ i ∈ List.range 8, BaseCheckAt 9 (96+i) := by decide +kernel

theorem base_r9_part104 : ∀ i ∈ List.range 8, BaseCheckAt 9 (104+i) := by decide +kernel

theorem base_r9_part112 : ∀ i ∈ List.range 8, BaseCheckAt 9 (112+i) := by decide +kernel

theorem base_r9_part120 : ∀ i ∈ List.range 8, BaseCheckAt 9 (120+i) := by decide +kernel

theorem base_r9_part128 : ∀ i ∈ List.range 6, BaseCheckAt 9 (128+i) := by decide +kernel

theorem base_r9 (V : ℕ) (hV : V ∈ List.range 134) : BaseCheckAt 9 V := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := base_r9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := base_r9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r9_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (0+i)) 9 (0+i) := by decide +kernel

theorem valid_r9_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (8+i)) 9 (8+i) := by decide +kernel

theorem valid_r9_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (16+i)) 9 (16+i) := by decide +kernel

theorem valid_r9_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (24+i)) 9 (24+i) := by decide +kernel

theorem valid_r9_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (32+i)) 9 (32+i) := by decide +kernel

theorem valid_r9_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (40+i)) 9 (40+i) := by decide +kernel

theorem valid_r9_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (48+i)) 9 (48+i) := by decide +kernel

theorem valid_r9_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (56+i)) 9 (56+i) := by decide +kernel

theorem valid_r9_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (64+i)) 9 (64+i) := by decide +kernel

theorem valid_r9_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (72+i)) 9 (72+i) := by decide +kernel

theorem valid_r9_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (80+i)) 9 (80+i) := by decide +kernel

theorem valid_r9_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (88+i)) 9 (88+i) := by decide +kernel

theorem valid_r9_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (96+i)) 9 (96+i) := by decide +kernel

theorem valid_r9_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (104+i)) 9 (104+i) := by decide +kernel

theorem valid_r9_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (112+i)) 9 (112+i) := by decide +kernel

theorem valid_r9_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 9 (120+i)) 9 (120+i) := by decide +kernel

theorem valid_r9_part128 : ∀ i ∈ List.range 6, Valid (BoundaryTailBaseFastData.row 9 (128+i)) 9 (128+i) := by decide +kernel

theorem valid_r9 (V : ℕ) (hV : V ∈ List.range 134) : Valid (BoundaryTailBaseFastData.row 9 V) 9 V := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := valid_r9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := valid_r9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r9_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (0+i)) 9 (0+i) = true := by decide +kernel

theorem strictBool_r9_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (1+i)) 9 (1+i) = true := by decide +kernel

theorem strictBool_r9_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (2+i)) 9 (2+i) = true := by decide +kernel

theorem strictBool_r9_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (3+i)) 9 (3+i) = true := by decide +kernel

theorem strictBool_r9_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (4+i)) 9 (4+i) = true := by decide +kernel

theorem strictBool_r9_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (5+i)) 9 (5+i) = true := by decide +kernel

theorem strictBool_r9_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (6+i)) 9 (6+i) = true := by decide +kernel

theorem strictBool_r9_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (7+i)) 9 (7+i) = true := by decide +kernel

theorem strictBool_r9_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (8+i)) 9 (8+i) = true := by decide +kernel

theorem strictBool_r9_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (9+i)) 9 (9+i) = true := by decide +kernel

theorem strictBool_r9_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (10+i)) 9 (10+i) = true := by decide +kernel

theorem strictBool_r9_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (11+i)) 9 (11+i) = true := by decide +kernel

theorem strictBool_r9_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (12+i)) 9 (12+i) = true := by decide +kernel

theorem strictBool_r9_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (13+i)) 9 (13+i) = true := by decide +kernel

theorem strictBool_r9_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (14+i)) 9 (14+i) = true := by decide +kernel

theorem strictBool_r9_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (15+i)) 9 (15+i) = true := by decide +kernel

theorem strictBool_r9_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (16+i)) 9 (16+i) = true := by decide +kernel

theorem strictBool_r9_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (17+i)) 9 (17+i) = true := by decide +kernel

theorem strictBool_r9_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (18+i)) 9 (18+i) = true := by decide +kernel

theorem strictBool_r9_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (19+i)) 9 (19+i) = true := by decide +kernel

theorem strictBool_r9_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (20+i)) 9 (20+i) = true := by decide +kernel

theorem strictBool_r9_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (21+i)) 9 (21+i) = true := by decide +kernel

theorem strictBool_r9_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (22+i)) 9 (22+i) = true := by decide +kernel

theorem strictBool_r9_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (23+i)) 9 (23+i) = true := by decide +kernel

theorem strictBool_r9_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (24+i)) 9 (24+i) = true := by decide +kernel

theorem strictBool_r9_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (25+i)) 9 (25+i) = true := by decide +kernel

theorem strictBool_r9_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (26+i)) 9 (26+i) = true := by decide +kernel

theorem strictBool_r9_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (27+i)) 9 (27+i) = true := by decide +kernel

theorem strictBool_r9_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (28+i)) 9 (28+i) = true := by decide +kernel

theorem strictBool_r9_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (29+i)) 9 (29+i) = true := by decide +kernel

theorem strictBool_r9_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (30+i)) 9 (30+i) = true := by decide +kernel

theorem strictBool_r9_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (31+i)) 9 (31+i) = true := by decide +kernel

theorem strictBool_r9_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (32+i)) 9 (32+i) = true := by decide +kernel

theorem strictBool_r9_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (33+i)) 9 (33+i) = true := by decide +kernel

theorem strictBool_r9_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (34+i)) 9 (34+i) = true := by decide +kernel

theorem strictBool_r9_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (35+i)) 9 (35+i) = true := by decide +kernel

theorem strictBool_r9_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (36+i)) 9 (36+i) = true := by decide +kernel

theorem strictBool_r9_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (37+i)) 9 (37+i) = true := by decide +kernel

theorem strictBool_r9_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (38+i)) 9 (38+i) = true := by decide +kernel

theorem strictBool_r9_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (39+i)) 9 (39+i) = true := by decide +kernel

theorem strictBool_r9_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (40+i)) 9 (40+i) = true := by decide +kernel

theorem strictBool_r9_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (41+i)) 9 (41+i) = true := by decide +kernel

theorem strictBool_r9_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (42+i)) 9 (42+i) = true := by decide +kernel

theorem strictBool_r9_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (43+i)) 9 (43+i) = true := by decide +kernel

theorem strictBool_r9_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (44+i)) 9 (44+i) = true := by decide +kernel

theorem strictBool_r9_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (45+i)) 9 (45+i) = true := by decide +kernel

theorem strictBool_r9_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (46+i)) 9 (46+i) = true := by decide +kernel

theorem strictBool_r9_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (47+i)) 9 (47+i) = true := by decide +kernel

theorem strictBool_r9_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (48+i)) 9 (48+i) = true := by decide +kernel

theorem strictBool_r9_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (49+i)) 9 (49+i) = true := by decide +kernel

theorem strictBool_r9_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (50+i)) 9 (50+i) = true := by decide +kernel

theorem strictBool_r9_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (51+i)) 9 (51+i) = true := by decide +kernel

theorem strictBool_r9_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (52+i)) 9 (52+i) = true := by decide +kernel

theorem strictBool_r9_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (53+i)) 9 (53+i) = true := by decide +kernel

theorem strictBool_r9_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (54+i)) 9 (54+i) = true := by decide +kernel

theorem strictBool_r9_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (55+i)) 9 (55+i) = true := by decide +kernel

theorem strictBool_r9_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (56+i)) 9 (56+i) = true := by decide +kernel

theorem strictBool_r9_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (57+i)) 9 (57+i) = true := by decide +kernel

theorem strictBool_r9_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (58+i)) 9 (58+i) = true := by decide +kernel

theorem strictBool_r9_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (59+i)) 9 (59+i) = true := by decide +kernel

theorem strictBool_r9_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (60+i)) 9 (60+i) = true := by decide +kernel

theorem strictBool_r9_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (61+i)) 9 (61+i) = true := by decide +kernel

theorem strictBool_r9_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (62+i)) 9 (62+i) = true := by decide +kernel

theorem strictBool_r9_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (63+i)) 9 (63+i) = true := by decide +kernel

theorem strictBool_r9_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (64+i)) 9 (64+i) = true := by decide +kernel

theorem strictBool_r9_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (65+i)) 9 (65+i) = true := by decide +kernel

theorem strictBool_r9_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (66+i)) 9 (66+i) = true := by decide +kernel

theorem strictBool_r9_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (67+i)) 9 (67+i) = true := by decide +kernel

theorem strictBool_r9_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (68+i)) 9 (68+i) = true := by decide +kernel

theorem strictBool_r9_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (69+i)) 9 (69+i) = true := by decide +kernel

theorem strictBool_r9_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (70+i)) 9 (70+i) = true := by decide +kernel

theorem strictBool_r9_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (71+i)) 9 (71+i) = true := by decide +kernel

theorem strictBool_r9_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (72+i)) 9 (72+i) = true := by decide +kernel

theorem strictBool_r9_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (73+i)) 9 (73+i) = true := by decide +kernel

theorem strictBool_r9_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (74+i)) 9 (74+i) = true := by decide +kernel

theorem strictBool_r9_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (75+i)) 9 (75+i) = true := by decide +kernel

theorem strictBool_r9_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (76+i)) 9 (76+i) = true := by decide +kernel

theorem strictBool_r9_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (77+i)) 9 (77+i) = true := by decide +kernel

theorem strictBool_r9_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (78+i)) 9 (78+i) = true := by decide +kernel

theorem strictBool_r9_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (79+i)) 9 (79+i) = true := by decide +kernel

theorem strictBool_r9_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (80+i)) 9 (80+i) = true := by decide +kernel

theorem strictBool_r9_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (81+i)) 9 (81+i) = true := by decide +kernel

theorem strictBool_r9_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (82+i)) 9 (82+i) = true := by decide +kernel

theorem strictBool_r9_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (83+i)) 9 (83+i) = true := by decide +kernel

theorem strictBool_r9_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (84+i)) 9 (84+i) = true := by decide +kernel

theorem strictBool_r9_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (85+i)) 9 (85+i) = true := by decide +kernel

theorem strictBool_r9_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (86+i)) 9 (86+i) = true := by decide +kernel

theorem strictBool_r9_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (87+i)) 9 (87+i) = true := by decide +kernel

theorem strictBool_r9_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (88+i)) 9 (88+i) = true := by decide +kernel

theorem strictBool_r9_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (89+i)) 9 (89+i) = true := by decide +kernel

theorem strictBool_r9_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (90+i)) 9 (90+i) = true := by decide +kernel

theorem strictBool_r9_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (91+i)) 9 (91+i) = true := by decide +kernel

theorem strictBool_r9_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (92+i)) 9 (92+i) = true := by decide +kernel

theorem strictBool_r9_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (93+i)) 9 (93+i) = true := by decide +kernel

theorem strictBool_r9_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (94+i)) 9 (94+i) = true := by decide +kernel

theorem strictBool_r9_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (95+i)) 9 (95+i) = true := by decide +kernel

theorem strictBool_r9_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (96+i)) 9 (96+i) = true := by decide +kernel

theorem strictBool_r9_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (97+i)) 9 (97+i) = true := by decide +kernel

theorem strictBool_r9_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (98+i)) 9 (98+i) = true := by decide +kernel

theorem strictBool_r9_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (99+i)) 9 (99+i) = true := by decide +kernel

theorem strictBool_r9_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (100+i)) 9 (100+i) = true := by decide +kernel

theorem strictBool_r9_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (101+i)) 9 (101+i) = true := by decide +kernel

theorem strictBool_r9_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (102+i)) 9 (102+i) = true := by decide +kernel

theorem strictBool_r9_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (103+i)) 9 (103+i) = true := by decide +kernel

theorem strictBool_r9_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (104+i)) 9 (104+i) = true := by decide +kernel

theorem strictBool_r9_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (105+i)) 9 (105+i) = true := by decide +kernel

theorem strictBool_r9_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (106+i)) 9 (106+i) = true := by decide +kernel

theorem strictBool_r9_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (107+i)) 9 (107+i) = true := by decide +kernel

theorem strictBool_r9_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (108+i)) 9 (108+i) = true := by decide +kernel

theorem strictBool_r9_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (109+i)) 9 (109+i) = true := by decide +kernel

theorem strictBool_r9_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (110+i)) 9 (110+i) = true := by decide +kernel

theorem strictBool_r9_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (111+i)) 9 (111+i) = true := by decide +kernel

theorem strictBool_r9_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (112+i)) 9 (112+i) = true := by decide +kernel

theorem strictBool_r9_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (113+i)) 9 (113+i) = true := by decide +kernel

theorem strictBool_r9_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (114+i)) 9 (114+i) = true := by decide +kernel

theorem strictBool_r9_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (115+i)) 9 (115+i) = true := by decide +kernel

theorem strictBool_r9_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (116+i)) 9 (116+i) = true := by decide +kernel

theorem strictBool_r9_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (117+i)) 9 (117+i) = true := by decide +kernel

theorem strictBool_r9_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (118+i)) 9 (118+i) = true := by decide +kernel

theorem strictBool_r9_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (119+i)) 9 (119+i) = true := by decide +kernel

theorem strictBool_r9_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (120+i)) 9 (120+i) = true := by decide +kernel

theorem strictBool_r9_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (121+i)) 9 (121+i) = true := by decide +kernel

theorem strictBool_r9_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (122+i)) 9 (122+i) = true := by decide +kernel

theorem strictBool_r9_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (123+i)) 9 (123+i) = true := by decide +kernel

theorem strictBool_r9_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (124+i)) 9 (124+i) = true := by decide +kernel

theorem strictBool_r9_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (125+i)) 9 (125+i) = true := by decide +kernel

theorem strictBool_r9_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (126+i)) 9 (126+i) = true := by decide +kernel

theorem strictBool_r9_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (127+i)) 9 (127+i) = true := by decide +kernel

theorem strictBool_r9_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (128+i)) 9 (128+i) = true := by decide +kernel

theorem strictBool_r9_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (129+i)) 9 (129+i) = true := by decide +kernel

theorem strictBool_r9_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (130+i)) 9 (130+i) = true := by decide +kernel

theorem strictBool_r9_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (131+i)) 9 (131+i) = true := by decide +kernel

theorem strictBool_r9_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (132+i)) 9 (132+i) = true := by decide +kernel

theorem strictBool_r9_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 9 (133+i)) 9 (133+i) = true := by decide +kernel

theorem strictBool_r9 (V : ℕ) (hV : V ∈ List.range 134) : strictBool (BoundaryTailBaseFastData.row 9 V) 9 V = true := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r9_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r9_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r9_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r9_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r9_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r9_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r9_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r9_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r9_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r9_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r9_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r9_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r9_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r9_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r9_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := strictBool_r9_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := strictBool_r9_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r9_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r9_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r9_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r9_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r9_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r9_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r9_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_50 : V < 48
              · have hi := strictBool_r9_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · by_cases h48_50 : V < 49
                · have hi := strictBool_r9_part48 (V-48) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r9_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r9_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r9_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r9_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r9_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r9_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r9_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_67 : V < 65
              · have hi := strictBool_r9_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · by_cases h65_67 : V < 66
                · have hi := strictBool_r9_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
  · by_cases h67_134 : V < 100
    · by_cases h67_100 : V < 83
      · by_cases h67_83 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r9_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r9_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r9_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r9_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
        · by_cases h75_83 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r9_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r9_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r9_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r9_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
      · by_cases h83_100 : V < 91
        · by_cases h83_91 : V < 87
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r9_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r9_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r9_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r9_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
        · by_cases h91_100 : V < 95
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r9_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r9_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
          · by_cases h95_100 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r9_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_100 : V < 98
              · have hi := strictBool_r9_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · by_cases h98_100 : V < 99
                · have hi := strictBool_r9_part98 (V-98) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part99 (V-99) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
    · by_cases h100_134 : V < 117
      · by_cases h100_117 : V < 108
        · by_cases h100_108 : V < 104
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r9_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r9_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r9_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r9_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
        · by_cases h108_117 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r9_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r9_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
          · by_cases h112_117 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r9_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_117 : V < 115
              · have hi := strictBool_r9_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · by_cases h115_117 : V < 116
                · have hi := strictBool_r9_part115 (V-115) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part116 (V-116) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
      · by_cases h117_134 : V < 125
        · by_cases h117_125 : V < 121
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r9_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r9_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r9_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r9_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
        · by_cases h125_134 : V < 129
          · by_cases h125_129 : V < 127
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r9_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
            · by_cases h127_129 : V < 128
              · have hi := strictBool_r9_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · by_cases h129_134 : V < 131
            · by_cases h129_131 : V < 130
              · have hi := strictBool_r9_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · have hi := strictBool_r9_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
            · by_cases h131_134 : V < 132
              · have hi := strictBool_r9_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · by_cases h132_134 : V < 133
                · have hi := strictBool_r9_part132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
                · have hi := strictBool_r9_part133 (V-133) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi

theorem strictFast_r9 (V : ℕ) (hV : V ∈ List.range 134) : StrictAtFast (BoundaryTailBaseFastData.row 9 V) 9 V :=
  strictBool_sound _ _ _ (strictBool_r9 V hV)

theorem strict_r9 (V : ℕ) (hV : V ∈ List.range 134) : StrictCheckAt 9 V :=
  strictAtFast_sound _ _ _ (valid_r9 V hV) (strictFast_r9 V hV)

theorem zeroCertificate_r9_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (0+i)) 9 (0+i) := by decide +kernel

theorem zeroCertificate_r9_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (8+i)) 9 (8+i) := by decide +kernel

theorem zeroCertificate_r9_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (16+i)) 9 (16+i) := by decide +kernel

theorem zeroCertificate_r9_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (24+i)) 9 (24+i) := by decide +kernel

theorem zeroCertificate_r9_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (32+i)) 9 (32+i) := by decide +kernel

theorem zeroCertificate_r9_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (40+i)) 9 (40+i) := by decide +kernel

theorem zeroCertificate_r9_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (48+i)) 9 (48+i) := by decide +kernel

theorem zeroCertificate_r9_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (56+i)) 9 (56+i) := by decide +kernel

theorem zeroCertificate_r9_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (64+i)) 9 (64+i) := by decide +kernel

theorem zeroCertificate_r9_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (72+i)) 9 (72+i) := by decide +kernel

theorem zeroCertificate_r9_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (80+i)) 9 (80+i) := by decide +kernel

theorem zeroCertificate_r9_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (88+i)) 9 (88+i) := by decide +kernel

theorem zeroCertificate_r9_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (96+i)) 9 (96+i) := by decide +kernel

theorem zeroCertificate_r9_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (104+i)) 9 (104+i) := by decide +kernel

theorem zeroCertificate_r9_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (112+i)) 9 (112+i) := by decide +kernel

theorem zeroCertificate_r9_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 9 (120+i)) 9 (120+i) := by decide +kernel

theorem zeroCertificate_r9_part128 : ∀ i ∈ List.range 6, ZeroCertificate (BoundaryTailBaseFastData.row 9 (128+i)) 9 (128+i) := by decide +kernel

theorem zeroCertificate_r9 (V : ℕ) (hV : V ∈ List.range 134) : ZeroCertificate (BoundaryTailBaseFastData.row 9 V) 9 V := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := zeroCertificate_r9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := zeroCertificate_r9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r9 (V : ℕ) (hV : V ∈ List.range 134) : ZeroAtFast 9 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r9 V hV) (zeroCertificate_r9 V hV)

theorem zero_r9 (V : ℕ) (hV : V ∈ List.range 134) : ZeroCheckAt 9 V :=
  zeroAtFast_sound _ _ (zeroFast_r9 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r13_part0 : ∀ i ∈ List.range 8, CorrectAt 13 (0+i) := by decide +kernel

theorem correct_r13_part8 : ∀ i ∈ List.range 8, CorrectAt 13 (8+i) := by decide +kernel

theorem correct_r13_part16 : ∀ i ∈ List.range 8, CorrectAt 13 (16+i) := by decide +kernel

theorem correct_r13_part24 : ∀ i ∈ List.range 8, CorrectAt 13 (24+i) := by decide +kernel

theorem correct_r13_part32 : ∀ i ∈ List.range 8, CorrectAt 13 (32+i) := by decide +kernel

theorem correct_r13_part40 : ∀ i ∈ List.range 8, CorrectAt 13 (40+i) := by decide +kernel

theorem correct_r13_part48 : ∀ i ∈ List.range 8, CorrectAt 13 (48+i) := by decide +kernel

theorem correct_r13_part56 : ∀ i ∈ List.range 8, CorrectAt 13 (56+i) := by decide +kernel

theorem correct_r13_part64 : ∀ i ∈ List.range 8, CorrectAt 13 (64+i) := by decide +kernel

theorem correct_r13_part72 : ∀ i ∈ List.range 8, CorrectAt 13 (72+i) := by decide +kernel

theorem correct_r13_part80 : ∀ i ∈ List.range 8, CorrectAt 13 (80+i) := by decide +kernel

theorem correct_r13_part88 : ∀ i ∈ List.range 8, CorrectAt 13 (88+i) := by decide +kernel

theorem correct_r13_part96 : ∀ i ∈ List.range 8, CorrectAt 13 (96+i) := by decide +kernel

theorem correct_r13_part104 : ∀ i ∈ List.range 8, CorrectAt 13 (104+i) := by decide +kernel

theorem correct_r13_part112 : ∀ i ∈ List.range 8, CorrectAt 13 (112+i) := by decide +kernel

theorem correct_r13_part120 : ∀ i ∈ List.range 8, CorrectAt 13 (120+i) := by decide +kernel

theorem correct_r13_part128 : ∀ i ∈ List.range 2, CorrectAt 13 (128+i) := by decide +kernel

theorem correct_r13 (V : ℕ) (hV : V ∈ List.range 130) : CorrectAt 13 V := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := correct_r13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := correct_r13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r13_part0 : ∀ i ∈ List.range 8, BaseCheckAt 13 (0+i) := by decide +kernel

theorem base_r13_part8 : ∀ i ∈ List.range 8, BaseCheckAt 13 (8+i) := by decide +kernel

theorem base_r13_part16 : ∀ i ∈ List.range 8, BaseCheckAt 13 (16+i) := by decide +kernel

theorem base_r13_part24 : ∀ i ∈ List.range 8, BaseCheckAt 13 (24+i) := by decide +kernel

theorem base_r13_part32 : ∀ i ∈ List.range 8, BaseCheckAt 13 (32+i) := by decide +kernel

theorem base_r13_part40 : ∀ i ∈ List.range 8, BaseCheckAt 13 (40+i) := by decide +kernel

theorem base_r13_part48 : ∀ i ∈ List.range 8, BaseCheckAt 13 (48+i) := by decide +kernel

theorem base_r13_part56 : ∀ i ∈ List.range 8, BaseCheckAt 13 (56+i) := by decide +kernel

theorem base_r13_part64 : ∀ i ∈ List.range 8, BaseCheckAt 13 (64+i) := by decide +kernel

theorem base_r13_part72 : ∀ i ∈ List.range 8, BaseCheckAt 13 (72+i) := by decide +kernel

theorem base_r13_part80 : ∀ i ∈ List.range 8, BaseCheckAt 13 (80+i) := by decide +kernel

theorem base_r13_part88 : ∀ i ∈ List.range 8, BaseCheckAt 13 (88+i) := by decide +kernel

theorem base_r13_part96 : ∀ i ∈ List.range 8, BaseCheckAt 13 (96+i) := by decide +kernel

theorem base_r13_part104 : ∀ i ∈ List.range 8, BaseCheckAt 13 (104+i) := by decide +kernel

theorem base_r13_part112 : ∀ i ∈ List.range 8, BaseCheckAt 13 (112+i) := by decide +kernel

theorem base_r13_part120 : ∀ i ∈ List.range 8, BaseCheckAt 13 (120+i) := by decide +kernel

theorem base_r13_part128 : ∀ i ∈ List.range 2, BaseCheckAt 13 (128+i) := by decide +kernel

theorem base_r13 (V : ℕ) (hV : V ∈ List.range 130) : BaseCheckAt 13 V := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := base_r13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := base_r13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r13_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (0+i)) 13 (0+i) := by decide +kernel

theorem valid_r13_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (8+i)) 13 (8+i) := by decide +kernel

theorem valid_r13_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (16+i)) 13 (16+i) := by decide +kernel

theorem valid_r13_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (24+i)) 13 (24+i) := by decide +kernel

theorem valid_r13_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (32+i)) 13 (32+i) := by decide +kernel

theorem valid_r13_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (40+i)) 13 (40+i) := by decide +kernel

theorem valid_r13_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (48+i)) 13 (48+i) := by decide +kernel

theorem valid_r13_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (56+i)) 13 (56+i) := by decide +kernel

theorem valid_r13_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (64+i)) 13 (64+i) := by decide +kernel

theorem valid_r13_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (72+i)) 13 (72+i) := by decide +kernel

theorem valid_r13_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (80+i)) 13 (80+i) := by decide +kernel

theorem valid_r13_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (88+i)) 13 (88+i) := by decide +kernel

theorem valid_r13_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (96+i)) 13 (96+i) := by decide +kernel

theorem valid_r13_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (104+i)) 13 (104+i) := by decide +kernel

theorem valid_r13_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (112+i)) 13 (112+i) := by decide +kernel

theorem valid_r13_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 13 (120+i)) 13 (120+i) := by decide +kernel

theorem valid_r13_part128 : ∀ i ∈ List.range 2, Valid (BoundaryTailBaseFastData.row 13 (128+i)) 13 (128+i) := by decide +kernel

theorem valid_r13 (V : ℕ) (hV : V ∈ List.range 130) : Valid (BoundaryTailBaseFastData.row 13 V) 13 V := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := valid_r13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := valid_r13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r13_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (0+i)) 13 (0+i) = true := by decide +kernel

theorem strictBool_r13_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (1+i)) 13 (1+i) = true := by decide +kernel

theorem strictBool_r13_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (2+i)) 13 (2+i) = true := by decide +kernel

theorem strictBool_r13_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (3+i)) 13 (3+i) = true := by decide +kernel

theorem strictBool_r13_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (4+i)) 13 (4+i) = true := by decide +kernel

theorem strictBool_r13_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (5+i)) 13 (5+i) = true := by decide +kernel

theorem strictBool_r13_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (6+i)) 13 (6+i) = true := by decide +kernel

theorem strictBool_r13_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (7+i)) 13 (7+i) = true := by decide +kernel

theorem strictBool_r13_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (8+i)) 13 (8+i) = true := by decide +kernel

theorem strictBool_r13_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (9+i)) 13 (9+i) = true := by decide +kernel

theorem strictBool_r13_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (10+i)) 13 (10+i) = true := by decide +kernel

theorem strictBool_r13_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (11+i)) 13 (11+i) = true := by decide +kernel

theorem strictBool_r13_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (12+i)) 13 (12+i) = true := by decide +kernel

theorem strictBool_r13_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (13+i)) 13 (13+i) = true := by decide +kernel

theorem strictBool_r13_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (14+i)) 13 (14+i) = true := by decide +kernel

theorem strictBool_r13_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (15+i)) 13 (15+i) = true := by decide +kernel

theorem strictBool_r13_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (16+i)) 13 (16+i) = true := by decide +kernel

theorem strictBool_r13_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (17+i)) 13 (17+i) = true := by decide +kernel

theorem strictBool_r13_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (18+i)) 13 (18+i) = true := by decide +kernel

theorem strictBool_r13_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (19+i)) 13 (19+i) = true := by decide +kernel

theorem strictBool_r13_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (20+i)) 13 (20+i) = true := by decide +kernel

theorem strictBool_r13_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (21+i)) 13 (21+i) = true := by decide +kernel

theorem strictBool_r13_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (22+i)) 13 (22+i) = true := by decide +kernel

theorem strictBool_r13_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (23+i)) 13 (23+i) = true := by decide +kernel

theorem strictBool_r13_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (24+i)) 13 (24+i) = true := by decide +kernel

theorem strictBool_r13_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (25+i)) 13 (25+i) = true := by decide +kernel

theorem strictBool_r13_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (26+i)) 13 (26+i) = true := by decide +kernel

theorem strictBool_r13_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (27+i)) 13 (27+i) = true := by decide +kernel

theorem strictBool_r13_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (28+i)) 13 (28+i) = true := by decide +kernel

theorem strictBool_r13_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (29+i)) 13 (29+i) = true := by decide +kernel

theorem strictBool_r13_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (30+i)) 13 (30+i) = true := by decide +kernel

theorem strictBool_r13_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (31+i)) 13 (31+i) = true := by decide +kernel

theorem strictBool_r13_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (32+i)) 13 (32+i) = true := by decide +kernel

theorem strictBool_r13_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (33+i)) 13 (33+i) = true := by decide +kernel

theorem strictBool_r13_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (34+i)) 13 (34+i) = true := by decide +kernel

theorem strictBool_r13_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (35+i)) 13 (35+i) = true := by decide +kernel

theorem strictBool_r13_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (36+i)) 13 (36+i) = true := by decide +kernel

theorem strictBool_r13_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (37+i)) 13 (37+i) = true := by decide +kernel

theorem strictBool_r13_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (38+i)) 13 (38+i) = true := by decide +kernel

theorem strictBool_r13_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (39+i)) 13 (39+i) = true := by decide +kernel

theorem strictBool_r13_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (40+i)) 13 (40+i) = true := by decide +kernel

theorem strictBool_r13_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (41+i)) 13 (41+i) = true := by decide +kernel

theorem strictBool_r13_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (42+i)) 13 (42+i) = true := by decide +kernel

theorem strictBool_r13_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (43+i)) 13 (43+i) = true := by decide +kernel

theorem strictBool_r13_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (44+i)) 13 (44+i) = true := by decide +kernel

theorem strictBool_r13_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (45+i)) 13 (45+i) = true := by decide +kernel

theorem strictBool_r13_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (46+i)) 13 (46+i) = true := by decide +kernel

theorem strictBool_r13_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (47+i)) 13 (47+i) = true := by decide +kernel

theorem strictBool_r13_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (48+i)) 13 (48+i) = true := by decide +kernel

theorem strictBool_r13_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (49+i)) 13 (49+i) = true := by decide +kernel

theorem strictBool_r13_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (50+i)) 13 (50+i) = true := by decide +kernel

theorem strictBool_r13_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (51+i)) 13 (51+i) = true := by decide +kernel

theorem strictBool_r13_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (52+i)) 13 (52+i) = true := by decide +kernel

theorem strictBool_r13_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (53+i)) 13 (53+i) = true := by decide +kernel

theorem strictBool_r13_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (54+i)) 13 (54+i) = true := by decide +kernel

theorem strictBool_r13_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (55+i)) 13 (55+i) = true := by decide +kernel

theorem strictBool_r13_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (56+i)) 13 (56+i) = true := by decide +kernel

theorem strictBool_r13_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (57+i)) 13 (57+i) = true := by decide +kernel

theorem strictBool_r13_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (58+i)) 13 (58+i) = true := by decide +kernel

theorem strictBool_r13_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (59+i)) 13 (59+i) = true := by decide +kernel

theorem strictBool_r13_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (60+i)) 13 (60+i) = true := by decide +kernel

theorem strictBool_r13_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (61+i)) 13 (61+i) = true := by decide +kernel

theorem strictBool_r13_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (62+i)) 13 (62+i) = true := by decide +kernel

theorem strictBool_r13_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (63+i)) 13 (63+i) = true := by decide +kernel

theorem strictBool_r13_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (64+i)) 13 (64+i) = true := by decide +kernel

theorem strictBool_r13_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (65+i)) 13 (65+i) = true := by decide +kernel

theorem strictBool_r13_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (66+i)) 13 (66+i) = true := by decide +kernel

theorem strictBool_r13_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (67+i)) 13 (67+i) = true := by decide +kernel

theorem strictBool_r13_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (68+i)) 13 (68+i) = true := by decide +kernel

theorem strictBool_r13_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (69+i)) 13 (69+i) = true := by decide +kernel

theorem strictBool_r13_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (70+i)) 13 (70+i) = true := by decide +kernel

theorem strictBool_r13_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (71+i)) 13 (71+i) = true := by decide +kernel

theorem strictBool_r13_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (72+i)) 13 (72+i) = true := by decide +kernel

theorem strictBool_r13_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (73+i)) 13 (73+i) = true := by decide +kernel

theorem strictBool_r13_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (74+i)) 13 (74+i) = true := by decide +kernel

theorem strictBool_r13_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (75+i)) 13 (75+i) = true := by decide +kernel

theorem strictBool_r13_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (76+i)) 13 (76+i) = true := by decide +kernel

theorem strictBool_r13_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (77+i)) 13 (77+i) = true := by decide +kernel

theorem strictBool_r13_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (78+i)) 13 (78+i) = true := by decide +kernel

theorem strictBool_r13_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (79+i)) 13 (79+i) = true := by decide +kernel

theorem strictBool_r13_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (80+i)) 13 (80+i) = true := by decide +kernel

theorem strictBool_r13_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (81+i)) 13 (81+i) = true := by decide +kernel

theorem strictBool_r13_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (82+i)) 13 (82+i) = true := by decide +kernel

theorem strictBool_r13_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (83+i)) 13 (83+i) = true := by decide +kernel

theorem strictBool_r13_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (84+i)) 13 (84+i) = true := by decide +kernel

theorem strictBool_r13_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (85+i)) 13 (85+i) = true := by decide +kernel

theorem strictBool_r13_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (86+i)) 13 (86+i) = true := by decide +kernel

theorem strictBool_r13_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (87+i)) 13 (87+i) = true := by decide +kernel

theorem strictBool_r13_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (88+i)) 13 (88+i) = true := by decide +kernel

theorem strictBool_r13_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (89+i)) 13 (89+i) = true := by decide +kernel

theorem strictBool_r13_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (90+i)) 13 (90+i) = true := by decide +kernel

theorem strictBool_r13_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (91+i)) 13 (91+i) = true := by decide +kernel

theorem strictBool_r13_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (92+i)) 13 (92+i) = true := by decide +kernel

theorem strictBool_r13_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (93+i)) 13 (93+i) = true := by decide +kernel

theorem strictBool_r13_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (94+i)) 13 (94+i) = true := by decide +kernel

theorem strictBool_r13_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (95+i)) 13 (95+i) = true := by decide +kernel

theorem strictBool_r13_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (96+i)) 13 (96+i) = true := by decide +kernel

theorem strictBool_r13_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (97+i)) 13 (97+i) = true := by decide +kernel

theorem strictBool_r13_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (98+i)) 13 (98+i) = true := by decide +kernel

theorem strictBool_r13_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (99+i)) 13 (99+i) = true := by decide +kernel

theorem strictBool_r13_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (100+i)) 13 (100+i) = true := by decide +kernel

theorem strictBool_r13_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (101+i)) 13 (101+i) = true := by decide +kernel

theorem strictBool_r13_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (102+i)) 13 (102+i) = true := by decide +kernel

theorem strictBool_r13_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (103+i)) 13 (103+i) = true := by decide +kernel

theorem strictBool_r13_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (104+i)) 13 (104+i) = true := by decide +kernel

theorem strictBool_r13_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (105+i)) 13 (105+i) = true := by decide +kernel

theorem strictBool_r13_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (106+i)) 13 (106+i) = true := by decide +kernel

theorem strictBool_r13_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (107+i)) 13 (107+i) = true := by decide +kernel

theorem strictBool_r13_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (108+i)) 13 (108+i) = true := by decide +kernel

theorem strictBool_r13_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (109+i)) 13 (109+i) = true := by decide +kernel

theorem strictBool_r13_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (110+i)) 13 (110+i) = true := by decide +kernel

theorem strictBool_r13_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (111+i)) 13 (111+i) = true := by decide +kernel

theorem strictBool_r13_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (112+i)) 13 (112+i) = true := by decide +kernel

theorem strictBool_r13_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (113+i)) 13 (113+i) = true := by decide +kernel

theorem strictBool_r13_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (114+i)) 13 (114+i) = true := by decide +kernel

theorem strictBool_r13_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (115+i)) 13 (115+i) = true := by decide +kernel

theorem strictBool_r13_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (116+i)) 13 (116+i) = true := by decide +kernel

theorem strictBool_r13_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (117+i)) 13 (117+i) = true := by decide +kernel

theorem strictBool_r13_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (118+i)) 13 (118+i) = true := by decide +kernel

theorem strictBool_r13_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (119+i)) 13 (119+i) = true := by decide +kernel

theorem strictBool_r13_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (120+i)) 13 (120+i) = true := by decide +kernel

theorem strictBool_r13_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (121+i)) 13 (121+i) = true := by decide +kernel

theorem strictBool_r13_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (122+i)) 13 (122+i) = true := by decide +kernel

theorem strictBool_r13_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (123+i)) 13 (123+i) = true := by decide +kernel

theorem strictBool_r13_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (124+i)) 13 (124+i) = true := by decide +kernel

theorem strictBool_r13_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (125+i)) 13 (125+i) = true := by decide +kernel

theorem strictBool_r13_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (126+i)) 13 (126+i) = true := by decide +kernel

theorem strictBool_r13_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (127+i)) 13 (127+i) = true := by decide +kernel

theorem strictBool_r13_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (128+i)) 13 (128+i) = true := by decide +kernel

theorem strictBool_r13_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 13 (129+i)) 13 (129+i) = true := by decide +kernel

theorem strictBool_r13 (V : ℕ) (hV : V ∈ List.range 130) : strictBool (BoundaryTailBaseFastData.row 13 V) 13 V = true := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 65
  · by_cases h0_65 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r13_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r13_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r13_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r13_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r13_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r13_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r13_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r13_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r13_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r13_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r13_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r13_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r13_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r13_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r13_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r13_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
    · by_cases h32_65 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r13_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r13_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r13_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r13_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r13_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r13_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r13_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r13_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
      · by_cases h48_65 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r13_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r13_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r13_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r13_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
        · by_cases h56_65 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r13_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r13_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_65 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r13_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_65 : V < 63
              · have hi := strictBool_r13_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · by_cases h63_65 : V < 64
                · have hi := strictBool_r13_part63 (V-63) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
                · have hi := strictBool_r13_part64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h65_130 : V < 97
    · by_cases h65_97 : V < 81
      · by_cases h65_81 : V < 73
        · by_cases h65_73 : V < 69
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r13_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r13_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r13_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r13_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · by_cases h73_81 : V < 77
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r13_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r13_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r13_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r13_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h81_97 : V < 89
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r13_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r13_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r13_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r13_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · by_cases h89_97 : V < 93
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r13_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r13_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r13_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r13_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h97_130 : V < 113
      · by_cases h97_113 : V < 105
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r13_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r13_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r13_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r13_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r13_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r13_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r13_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r13_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h113_130 : V < 121
        · by_cases h113_121 : V < 117
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r13_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r13_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r13_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r13_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r13_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r13_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r13_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r13_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
            · by_cases h127_130 : V < 128
              · have hi := strictBool_r13_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · by_cases h128_130 : V < 129
                · have hi := strictBool_r13_part128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
                · have hi := strictBool_r13_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi

theorem strictFast_r13 (V : ℕ) (hV : V ∈ List.range 130) : StrictAtFast (BoundaryTailBaseFastData.row 13 V) 13 V :=
  strictBool_sound _ _ _ (strictBool_r13 V hV)

theorem strict_r13 (V : ℕ) (hV : V ∈ List.range 130) : StrictCheckAt 13 V :=
  strictAtFast_sound _ _ _ (valid_r13 V hV) (strictFast_r13 V hV)

theorem zeroCertificate_r13_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (0+i)) 13 (0+i) := by decide +kernel

theorem zeroCertificate_r13_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (8+i)) 13 (8+i) := by decide +kernel

theorem zeroCertificate_r13_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (16+i)) 13 (16+i) := by decide +kernel

theorem zeroCertificate_r13_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (24+i)) 13 (24+i) := by decide +kernel

theorem zeroCertificate_r13_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (32+i)) 13 (32+i) := by decide +kernel

theorem zeroCertificate_r13_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (40+i)) 13 (40+i) := by decide +kernel

theorem zeroCertificate_r13_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (48+i)) 13 (48+i) := by decide +kernel

theorem zeroCertificate_r13_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (56+i)) 13 (56+i) := by decide +kernel

theorem zeroCertificate_r13_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (64+i)) 13 (64+i) := by decide +kernel

theorem zeroCertificate_r13_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (72+i)) 13 (72+i) := by decide +kernel

theorem zeroCertificate_r13_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (80+i)) 13 (80+i) := by decide +kernel

theorem zeroCertificate_r13_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (88+i)) 13 (88+i) := by decide +kernel

theorem zeroCertificate_r13_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (96+i)) 13 (96+i) := by decide +kernel

theorem zeroCertificate_r13_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (104+i)) 13 (104+i) := by decide +kernel

theorem zeroCertificate_r13_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (112+i)) 13 (112+i) := by decide +kernel

theorem zeroCertificate_r13_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 13 (120+i)) 13 (120+i) := by decide +kernel

theorem zeroCertificate_r13_part128 : ∀ i ∈ List.range 2, ZeroCertificate (BoundaryTailBaseFastData.row 13 (128+i)) 13 (128+i) := by decide +kernel

theorem zeroCertificate_r13 (V : ℕ) (hV : V ∈ List.range 130) : ZeroCertificate (BoundaryTailBaseFastData.row 13 V) 13 V := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := zeroCertificate_r13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := zeroCertificate_r13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r13 (V : ℕ) (hV : V ∈ List.range 130) : ZeroAtFast 13 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r13 V hV) (zeroCertificate_r13 V hV)

theorem zero_r13 (V : ℕ) (hV : V ∈ List.range 130) : ZeroCheckAt 13 V :=
  zeroAtFast_sound _ _ (zeroFast_r13 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r17_part0 : ∀ i ∈ List.range 8, CorrectAt 17 (0+i) := by decide +kernel

theorem correct_r17_part8 : ∀ i ∈ List.range 8, CorrectAt 17 (8+i) := by decide +kernel

theorem correct_r17_part16 : ∀ i ∈ List.range 8, CorrectAt 17 (16+i) := by decide +kernel

theorem correct_r17_part24 : ∀ i ∈ List.range 8, CorrectAt 17 (24+i) := by decide +kernel

theorem correct_r17_part32 : ∀ i ∈ List.range 8, CorrectAt 17 (32+i) := by decide +kernel

theorem correct_r17_part40 : ∀ i ∈ List.range 8, CorrectAt 17 (40+i) := by decide +kernel

theorem correct_r17_part48 : ∀ i ∈ List.range 8, CorrectAt 17 (48+i) := by decide +kernel

theorem correct_r17_part56 : ∀ i ∈ List.range 8, CorrectAt 17 (56+i) := by decide +kernel

theorem correct_r17_part64 : ∀ i ∈ List.range 8, CorrectAt 17 (64+i) := by decide +kernel

theorem correct_r17_part72 : ∀ i ∈ List.range 8, CorrectAt 17 (72+i) := by decide +kernel

theorem correct_r17_part80 : ∀ i ∈ List.range 8, CorrectAt 17 (80+i) := by decide +kernel

theorem correct_r17_part88 : ∀ i ∈ List.range 8, CorrectAt 17 (88+i) := by decide +kernel

theorem correct_r17_part96 : ∀ i ∈ List.range 8, CorrectAt 17 (96+i) := by decide +kernel

theorem correct_r17_part104 : ∀ i ∈ List.range 8, CorrectAt 17 (104+i) := by decide +kernel

theorem correct_r17_part112 : ∀ i ∈ List.range 8, CorrectAt 17 (112+i) := by decide +kernel

theorem correct_r17_part120 : ∀ i ∈ List.range 6, CorrectAt 17 (120+i) := by decide +kernel

theorem correct_r17 (V : ℕ) (hV : V ∈ List.range 126) : CorrectAt 17 V := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := correct_r17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r17_part0 : ∀ i ∈ List.range 8, BaseCheckAt 17 (0+i) := by decide +kernel

theorem base_r17_part8 : ∀ i ∈ List.range 8, BaseCheckAt 17 (8+i) := by decide +kernel

theorem base_r17_part16 : ∀ i ∈ List.range 8, BaseCheckAt 17 (16+i) := by decide +kernel

theorem base_r17_part24 : ∀ i ∈ List.range 8, BaseCheckAt 17 (24+i) := by decide +kernel

theorem base_r17_part32 : ∀ i ∈ List.range 8, BaseCheckAt 17 (32+i) := by decide +kernel

theorem base_r17_part40 : ∀ i ∈ List.range 8, BaseCheckAt 17 (40+i) := by decide +kernel

theorem base_r17_part48 : ∀ i ∈ List.range 8, BaseCheckAt 17 (48+i) := by decide +kernel

theorem base_r17_part56 : ∀ i ∈ List.range 8, BaseCheckAt 17 (56+i) := by decide +kernel

theorem base_r17_part64 : ∀ i ∈ List.range 8, BaseCheckAt 17 (64+i) := by decide +kernel

theorem base_r17_part72 : ∀ i ∈ List.range 8, BaseCheckAt 17 (72+i) := by decide +kernel

theorem base_r17_part80 : ∀ i ∈ List.range 8, BaseCheckAt 17 (80+i) := by decide +kernel

theorem base_r17_part88 : ∀ i ∈ List.range 8, BaseCheckAt 17 (88+i) := by decide +kernel

theorem base_r17_part96 : ∀ i ∈ List.range 8, BaseCheckAt 17 (96+i) := by decide +kernel

theorem base_r17_part104 : ∀ i ∈ List.range 8, BaseCheckAt 17 (104+i) := by decide +kernel

theorem base_r17_part112 : ∀ i ∈ List.range 8, BaseCheckAt 17 (112+i) := by decide +kernel

theorem base_r17_part120 : ∀ i ∈ List.range 6, BaseCheckAt 17 (120+i) := by decide +kernel

theorem base_r17 (V : ℕ) (hV : V ∈ List.range 126) : BaseCheckAt 17 V := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := base_r17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r17_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (0+i)) 17 (0+i) := by decide +kernel

theorem valid_r17_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (8+i)) 17 (8+i) := by decide +kernel

theorem valid_r17_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (16+i)) 17 (16+i) := by decide +kernel

theorem valid_r17_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (24+i)) 17 (24+i) := by decide +kernel

theorem valid_r17_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (32+i)) 17 (32+i) := by decide +kernel

theorem valid_r17_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (40+i)) 17 (40+i) := by decide +kernel

theorem valid_r17_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (48+i)) 17 (48+i) := by decide +kernel

theorem valid_r17_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (56+i)) 17 (56+i) := by decide +kernel

theorem valid_r17_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (64+i)) 17 (64+i) := by decide +kernel

theorem valid_r17_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (72+i)) 17 (72+i) := by decide +kernel

theorem valid_r17_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (80+i)) 17 (80+i) := by decide +kernel

theorem valid_r17_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (88+i)) 17 (88+i) := by decide +kernel

theorem valid_r17_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (96+i)) 17 (96+i) := by decide +kernel

theorem valid_r17_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (104+i)) 17 (104+i) := by decide +kernel

theorem valid_r17_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 17 (112+i)) 17 (112+i) := by decide +kernel

theorem valid_r17_part120 : ∀ i ∈ List.range 6, Valid (BoundaryTailBaseFastData.row 17 (120+i)) 17 (120+i) := by decide +kernel

theorem valid_r17 (V : ℕ) (hV : V ∈ List.range 126) : Valid (BoundaryTailBaseFastData.row 17 V) 17 V := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := valid_r17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r17_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (0+i)) 17 (0+i) = true := by decide +kernel

theorem strictBool_r17_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (1+i)) 17 (1+i) = true := by decide +kernel

theorem strictBool_r17_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (2+i)) 17 (2+i) = true := by decide +kernel

theorem strictBool_r17_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (3+i)) 17 (3+i) = true := by decide +kernel

theorem strictBool_r17_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (4+i)) 17 (4+i) = true := by decide +kernel

theorem strictBool_r17_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (5+i)) 17 (5+i) = true := by decide +kernel

theorem strictBool_r17_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (6+i)) 17 (6+i) = true := by decide +kernel

theorem strictBool_r17_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (7+i)) 17 (7+i) = true := by decide +kernel

theorem strictBool_r17_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (8+i)) 17 (8+i) = true := by decide +kernel

theorem strictBool_r17_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (9+i)) 17 (9+i) = true := by decide +kernel

theorem strictBool_r17_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (10+i)) 17 (10+i) = true := by decide +kernel

theorem strictBool_r17_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (11+i)) 17 (11+i) = true := by decide +kernel

theorem strictBool_r17_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (12+i)) 17 (12+i) = true := by decide +kernel

theorem strictBool_r17_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (13+i)) 17 (13+i) = true := by decide +kernel

theorem strictBool_r17_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (14+i)) 17 (14+i) = true := by decide +kernel

theorem strictBool_r17_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (15+i)) 17 (15+i) = true := by decide +kernel

theorem strictBool_r17_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (16+i)) 17 (16+i) = true := by decide +kernel

theorem strictBool_r17_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (17+i)) 17 (17+i) = true := by decide +kernel

theorem strictBool_r17_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (18+i)) 17 (18+i) = true := by decide +kernel

theorem strictBool_r17_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (19+i)) 17 (19+i) = true := by decide +kernel

theorem strictBool_r17_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (20+i)) 17 (20+i) = true := by decide +kernel

theorem strictBool_r17_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (21+i)) 17 (21+i) = true := by decide +kernel

theorem strictBool_r17_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (22+i)) 17 (22+i) = true := by decide +kernel

theorem strictBool_r17_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (23+i)) 17 (23+i) = true := by decide +kernel

theorem strictBool_r17_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (24+i)) 17 (24+i) = true := by decide +kernel

theorem strictBool_r17_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (25+i)) 17 (25+i) = true := by decide +kernel

theorem strictBool_r17_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (26+i)) 17 (26+i) = true := by decide +kernel

theorem strictBool_r17_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (27+i)) 17 (27+i) = true := by decide +kernel

theorem strictBool_r17_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (28+i)) 17 (28+i) = true := by decide +kernel

theorem strictBool_r17_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (29+i)) 17 (29+i) = true := by decide +kernel

theorem strictBool_r17_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (30+i)) 17 (30+i) = true := by decide +kernel

theorem strictBool_r17_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (31+i)) 17 (31+i) = true := by decide +kernel

theorem strictBool_r17_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (32+i)) 17 (32+i) = true := by decide +kernel

theorem strictBool_r17_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (33+i)) 17 (33+i) = true := by decide +kernel

theorem strictBool_r17_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (34+i)) 17 (34+i) = true := by decide +kernel

theorem strictBool_r17_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (35+i)) 17 (35+i) = true := by decide +kernel

theorem strictBool_r17_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (36+i)) 17 (36+i) = true := by decide +kernel

theorem strictBool_r17_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (37+i)) 17 (37+i) = true := by decide +kernel

theorem strictBool_r17_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (38+i)) 17 (38+i) = true := by decide +kernel

theorem strictBool_r17_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (39+i)) 17 (39+i) = true := by decide +kernel

theorem strictBool_r17_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (40+i)) 17 (40+i) = true := by decide +kernel

theorem strictBool_r17_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (41+i)) 17 (41+i) = true := by decide +kernel

theorem strictBool_r17_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (42+i)) 17 (42+i) = true := by decide +kernel

theorem strictBool_r17_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (43+i)) 17 (43+i) = true := by decide +kernel

theorem strictBool_r17_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (44+i)) 17 (44+i) = true := by decide +kernel

theorem strictBool_r17_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (45+i)) 17 (45+i) = true := by decide +kernel

theorem strictBool_r17_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (46+i)) 17 (46+i) = true := by decide +kernel

theorem strictBool_r17_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (47+i)) 17 (47+i) = true := by decide +kernel

theorem strictBool_r17_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (48+i)) 17 (48+i) = true := by decide +kernel

theorem strictBool_r17_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (49+i)) 17 (49+i) = true := by decide +kernel

theorem strictBool_r17_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (50+i)) 17 (50+i) = true := by decide +kernel

theorem strictBool_r17_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (51+i)) 17 (51+i) = true := by decide +kernel

theorem strictBool_r17_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (52+i)) 17 (52+i) = true := by decide +kernel

theorem strictBool_r17_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (53+i)) 17 (53+i) = true := by decide +kernel

theorem strictBool_r17_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (54+i)) 17 (54+i) = true := by decide +kernel

theorem strictBool_r17_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (55+i)) 17 (55+i) = true := by decide +kernel

theorem strictBool_r17_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (56+i)) 17 (56+i) = true := by decide +kernel

theorem strictBool_r17_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (57+i)) 17 (57+i) = true := by decide +kernel

theorem strictBool_r17_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (58+i)) 17 (58+i) = true := by decide +kernel

theorem strictBool_r17_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (59+i)) 17 (59+i) = true := by decide +kernel

theorem strictBool_r17_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (60+i)) 17 (60+i) = true := by decide +kernel

theorem strictBool_r17_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (61+i)) 17 (61+i) = true := by decide +kernel

theorem strictBool_r17_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (62+i)) 17 (62+i) = true := by decide +kernel

theorem strictBool_r17_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (63+i)) 17 (63+i) = true := by decide +kernel

theorem strictBool_r17_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (64+i)) 17 (64+i) = true := by decide +kernel

theorem strictBool_r17_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (65+i)) 17 (65+i) = true := by decide +kernel

theorem strictBool_r17_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (66+i)) 17 (66+i) = true := by decide +kernel

theorem strictBool_r17_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (67+i)) 17 (67+i) = true := by decide +kernel

theorem strictBool_r17_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (68+i)) 17 (68+i) = true := by decide +kernel

theorem strictBool_r17_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (69+i)) 17 (69+i) = true := by decide +kernel

theorem strictBool_r17_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (70+i)) 17 (70+i) = true := by decide +kernel

theorem strictBool_r17_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (71+i)) 17 (71+i) = true := by decide +kernel

theorem strictBool_r17_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (72+i)) 17 (72+i) = true := by decide +kernel

theorem strictBool_r17_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (73+i)) 17 (73+i) = true := by decide +kernel

theorem strictBool_r17_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (74+i)) 17 (74+i) = true := by decide +kernel

theorem strictBool_r17_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (75+i)) 17 (75+i) = true := by decide +kernel

theorem strictBool_r17_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (76+i)) 17 (76+i) = true := by decide +kernel

theorem strictBool_r17_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (77+i)) 17 (77+i) = true := by decide +kernel

theorem strictBool_r17_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (78+i)) 17 (78+i) = true := by decide +kernel

theorem strictBool_r17_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (79+i)) 17 (79+i) = true := by decide +kernel

theorem strictBool_r17_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (80+i)) 17 (80+i) = true := by decide +kernel

theorem strictBool_r17_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (81+i)) 17 (81+i) = true := by decide +kernel

theorem strictBool_r17_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (82+i)) 17 (82+i) = true := by decide +kernel

theorem strictBool_r17_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (83+i)) 17 (83+i) = true := by decide +kernel

theorem strictBool_r17_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (84+i)) 17 (84+i) = true := by decide +kernel

theorem strictBool_r17_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (85+i)) 17 (85+i) = true := by decide +kernel

theorem strictBool_r17_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (86+i)) 17 (86+i) = true := by decide +kernel

theorem strictBool_r17_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (87+i)) 17 (87+i) = true := by decide +kernel

theorem strictBool_r17_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (88+i)) 17 (88+i) = true := by decide +kernel

theorem strictBool_r17_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (89+i)) 17 (89+i) = true := by decide +kernel

theorem strictBool_r17_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (90+i)) 17 (90+i) = true := by decide +kernel

theorem strictBool_r17_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (91+i)) 17 (91+i) = true := by decide +kernel

theorem strictBool_r17_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (92+i)) 17 (92+i) = true := by decide +kernel

theorem strictBool_r17_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (93+i)) 17 (93+i) = true := by decide +kernel

theorem strictBool_r17_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (94+i)) 17 (94+i) = true := by decide +kernel

theorem strictBool_r17_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (95+i)) 17 (95+i) = true := by decide +kernel

theorem strictBool_r17_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (96+i)) 17 (96+i) = true := by decide +kernel

theorem strictBool_r17_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (97+i)) 17 (97+i) = true := by decide +kernel

theorem strictBool_r17_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (98+i)) 17 (98+i) = true := by decide +kernel

theorem strictBool_r17_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (99+i)) 17 (99+i) = true := by decide +kernel

theorem strictBool_r17_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (100+i)) 17 (100+i) = true := by decide +kernel

theorem strictBool_r17_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (101+i)) 17 (101+i) = true := by decide +kernel

theorem strictBool_r17_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (102+i)) 17 (102+i) = true := by decide +kernel

theorem strictBool_r17_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (103+i)) 17 (103+i) = true := by decide +kernel

theorem strictBool_r17_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (104+i)) 17 (104+i) = true := by decide +kernel

theorem strictBool_r17_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (105+i)) 17 (105+i) = true := by decide +kernel

theorem strictBool_r17_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (106+i)) 17 (106+i) = true := by decide +kernel

theorem strictBool_r17_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (107+i)) 17 (107+i) = true := by decide +kernel

theorem strictBool_r17_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (108+i)) 17 (108+i) = true := by decide +kernel

theorem strictBool_r17_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (109+i)) 17 (109+i) = true := by decide +kernel

theorem strictBool_r17_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (110+i)) 17 (110+i) = true := by decide +kernel

theorem strictBool_r17_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (111+i)) 17 (111+i) = true := by decide +kernel

theorem strictBool_r17_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (112+i)) 17 (112+i) = true := by decide +kernel

theorem strictBool_r17_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (113+i)) 17 (113+i) = true := by decide +kernel

theorem strictBool_r17_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (114+i)) 17 (114+i) = true := by decide +kernel

theorem strictBool_r17_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (115+i)) 17 (115+i) = true := by decide +kernel

theorem strictBool_r17_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (116+i)) 17 (116+i) = true := by decide +kernel

theorem strictBool_r17_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (117+i)) 17 (117+i) = true := by decide +kernel

theorem strictBool_r17_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (118+i)) 17 (118+i) = true := by decide +kernel

theorem strictBool_r17_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (119+i)) 17 (119+i) = true := by decide +kernel

theorem strictBool_r17_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (120+i)) 17 (120+i) = true := by decide +kernel

theorem strictBool_r17_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (121+i)) 17 (121+i) = true := by decide +kernel

theorem strictBool_r17_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (122+i)) 17 (122+i) = true := by decide +kernel

theorem strictBool_r17_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (123+i)) 17 (123+i) = true := by decide +kernel

theorem strictBool_r17_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (124+i)) 17 (124+i) = true := by decide +kernel

theorem strictBool_r17_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 17 (125+i)) 17 (125+i) = true := by decide +kernel

theorem strictBool_r17 (V : ℕ) (hV : V ∈ List.range 126) : strictBool (BoundaryTailBaseFastData.row 17 V) 17 V = true := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 63
  · by_cases h0_63 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r17_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r17_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r17_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r17_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r17_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r17_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r17_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r17_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r17_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r17_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r17_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r17_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r17_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r17_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r17_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r17_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
    · by_cases h31_63 : V < 47
      · by_cases h31_47 : V < 39
        · by_cases h31_39 : V < 35
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r17_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r17_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r17_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r17_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
        · by_cases h39_47 : V < 43
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r17_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r17_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r17_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r17_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
      · by_cases h47_63 : V < 55
        · by_cases h47_55 : V < 51
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r17_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r17_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r17_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r17_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
        · by_cases h55_63 : V < 59
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r17_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r17_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r17_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r17_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
  · by_cases h63_126 : V < 94
    · by_cases h63_94 : V < 78
      · by_cases h63_78 : V < 70
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have hi := strictBool_r17_part63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r17_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r17_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r17_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
        · by_cases h70_78 : V < 74
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r17_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r17_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r17_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r17_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
      · by_cases h78_94 : V < 86
        · by_cases h78_86 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r17_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r17_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r17_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r17_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
        · by_cases h86_94 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r17_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r17_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r17_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r17_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
    · by_cases h94_126 : V < 110
      · by_cases h94_110 : V < 102
        · by_cases h94_102 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r17_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r17_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r17_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r17_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r17_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r17_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r17_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r17_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
      · by_cases h110_126 : V < 118
        · by_cases h110_118 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r17_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r17_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r17_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r17_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r17_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r17_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r17_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r17_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r17_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi

theorem strictFast_r17 (V : ℕ) (hV : V ∈ List.range 126) : StrictAtFast (BoundaryTailBaseFastData.row 17 V) 17 V :=
  strictBool_sound _ _ _ (strictBool_r17 V hV)

theorem strict_r17 (V : ℕ) (hV : V ∈ List.range 126) : StrictCheckAt 17 V :=
  strictAtFast_sound _ _ _ (valid_r17 V hV) (strictFast_r17 V hV)

theorem zeroCertificate_r17_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (0+i)) 17 (0+i) := by decide +kernel

theorem zeroCertificate_r17_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (8+i)) 17 (8+i) := by decide +kernel

theorem zeroCertificate_r17_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (16+i)) 17 (16+i) := by decide +kernel

theorem zeroCertificate_r17_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (24+i)) 17 (24+i) := by decide +kernel

theorem zeroCertificate_r17_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (32+i)) 17 (32+i) := by decide +kernel

theorem zeroCertificate_r17_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (40+i)) 17 (40+i) := by decide +kernel

theorem zeroCertificate_r17_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (48+i)) 17 (48+i) := by decide +kernel

theorem zeroCertificate_r17_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (56+i)) 17 (56+i) := by decide +kernel

theorem zeroCertificate_r17_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (64+i)) 17 (64+i) := by decide +kernel

theorem zeroCertificate_r17_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (72+i)) 17 (72+i) := by decide +kernel

theorem zeroCertificate_r17_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (80+i)) 17 (80+i) := by decide +kernel

theorem zeroCertificate_r17_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (88+i)) 17 (88+i) := by decide +kernel

theorem zeroCertificate_r17_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (96+i)) 17 (96+i) := by decide +kernel

theorem zeroCertificate_r17_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (104+i)) 17 (104+i) := by decide +kernel

theorem zeroCertificate_r17_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 17 (112+i)) 17 (112+i) := by decide +kernel

theorem zeroCertificate_r17_part120 : ∀ i ∈ List.range 6, ZeroCertificate (BoundaryTailBaseFastData.row 17 (120+i)) 17 (120+i) := by decide +kernel

theorem zeroCertificate_r17 (V : ℕ) (hV : V ∈ List.range 126) : ZeroCertificate (BoundaryTailBaseFastData.row 17 V) 17 V := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := zeroCertificate_r17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r17 (V : ℕ) (hV : V ∈ List.range 126) : ZeroAtFast 17 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r17 V hV) (zeroCertificate_r17 V hV)

theorem zero_r17 (V : ℕ) (hV : V ∈ List.range 126) : ZeroCheckAt 17 V :=
  zeroAtFast_sound _ _ (zeroFast_r17 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r21_part0 : ∀ i ∈ List.range 8, CorrectAt 21 (0+i) := by decide +kernel

theorem correct_r21_part8 : ∀ i ∈ List.range 8, CorrectAt 21 (8+i) := by decide +kernel

theorem correct_r21_part16 : ∀ i ∈ List.range 8, CorrectAt 21 (16+i) := by decide +kernel

theorem correct_r21_part24 : ∀ i ∈ List.range 8, CorrectAt 21 (24+i) := by decide +kernel

theorem correct_r21_part32 : ∀ i ∈ List.range 8, CorrectAt 21 (32+i) := by decide +kernel

theorem correct_r21_part40 : ∀ i ∈ List.range 8, CorrectAt 21 (40+i) := by decide +kernel

theorem correct_r21_part48 : ∀ i ∈ List.range 8, CorrectAt 21 (48+i) := by decide +kernel

theorem correct_r21_part56 : ∀ i ∈ List.range 8, CorrectAt 21 (56+i) := by decide +kernel

theorem correct_r21_part64 : ∀ i ∈ List.range 8, CorrectAt 21 (64+i) := by decide +kernel

theorem correct_r21_part72 : ∀ i ∈ List.range 8, CorrectAt 21 (72+i) := by decide +kernel

theorem correct_r21_part80 : ∀ i ∈ List.range 8, CorrectAt 21 (80+i) := by decide +kernel

theorem correct_r21_part88 : ∀ i ∈ List.range 8, CorrectAt 21 (88+i) := by decide +kernel

theorem correct_r21_part96 : ∀ i ∈ List.range 8, CorrectAt 21 (96+i) := by decide +kernel

theorem correct_r21_part104 : ∀ i ∈ List.range 8, CorrectAt 21 (104+i) := by decide +kernel

theorem correct_r21_part112 : ∀ i ∈ List.range 8, CorrectAt 21 (112+i) := by decide +kernel

theorem correct_r21_part120 : ∀ i ∈ List.range 2, CorrectAt 21 (120+i) := by decide +kernel

theorem correct_r21 (V : ℕ) (hV : V ∈ List.range 122) : CorrectAt 21 V := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := correct_r21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r21_part0 : ∀ i ∈ List.range 8, BaseCheckAt 21 (0+i) := by decide +kernel

theorem base_r21_part8 : ∀ i ∈ List.range 8, BaseCheckAt 21 (8+i) := by decide +kernel

theorem base_r21_part16 : ∀ i ∈ List.range 8, BaseCheckAt 21 (16+i) := by decide +kernel

theorem base_r21_part24 : ∀ i ∈ List.range 8, BaseCheckAt 21 (24+i) := by decide +kernel

theorem base_r21_part32 : ∀ i ∈ List.range 8, BaseCheckAt 21 (32+i) := by decide +kernel

theorem base_r21_part40 : ∀ i ∈ List.range 8, BaseCheckAt 21 (40+i) := by decide +kernel

theorem base_r21_part48 : ∀ i ∈ List.range 8, BaseCheckAt 21 (48+i) := by decide +kernel

theorem base_r21_part56 : ∀ i ∈ List.range 8, BaseCheckAt 21 (56+i) := by decide +kernel

theorem base_r21_part64 : ∀ i ∈ List.range 8, BaseCheckAt 21 (64+i) := by decide +kernel

theorem base_r21_part72 : ∀ i ∈ List.range 8, BaseCheckAt 21 (72+i) := by decide +kernel

theorem base_r21_part80 : ∀ i ∈ List.range 8, BaseCheckAt 21 (80+i) := by decide +kernel

theorem base_r21_part88 : ∀ i ∈ List.range 8, BaseCheckAt 21 (88+i) := by decide +kernel

theorem base_r21_part96 : ∀ i ∈ List.range 8, BaseCheckAt 21 (96+i) := by decide +kernel

theorem base_r21_part104 : ∀ i ∈ List.range 8, BaseCheckAt 21 (104+i) := by decide +kernel

theorem base_r21_part112 : ∀ i ∈ List.range 8, BaseCheckAt 21 (112+i) := by decide +kernel

theorem base_r21_part120 : ∀ i ∈ List.range 2, BaseCheckAt 21 (120+i) := by decide +kernel

theorem base_r21 (V : ℕ) (hV : V ∈ List.range 122) : BaseCheckAt 21 V := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := base_r21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r21_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (0+i)) 21 (0+i) := by decide +kernel

theorem valid_r21_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (8+i)) 21 (8+i) := by decide +kernel

theorem valid_r21_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (16+i)) 21 (16+i) := by decide +kernel

theorem valid_r21_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (24+i)) 21 (24+i) := by decide +kernel

theorem valid_r21_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (32+i)) 21 (32+i) := by decide +kernel

theorem valid_r21_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (40+i)) 21 (40+i) := by decide +kernel

theorem valid_r21_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (48+i)) 21 (48+i) := by decide +kernel

theorem valid_r21_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (56+i)) 21 (56+i) := by decide +kernel

theorem valid_r21_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (64+i)) 21 (64+i) := by decide +kernel

theorem valid_r21_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (72+i)) 21 (72+i) := by decide +kernel

theorem valid_r21_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (80+i)) 21 (80+i) := by decide +kernel

theorem valid_r21_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (88+i)) 21 (88+i) := by decide +kernel

theorem valid_r21_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (96+i)) 21 (96+i) := by decide +kernel

theorem valid_r21_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (104+i)) 21 (104+i) := by decide +kernel

theorem valid_r21_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 21 (112+i)) 21 (112+i) := by decide +kernel

theorem valid_r21_part120 : ∀ i ∈ List.range 2, Valid (BoundaryTailBaseFastData.row 21 (120+i)) 21 (120+i) := by decide +kernel

theorem valid_r21 (V : ℕ) (hV : V ∈ List.range 122) : Valid (BoundaryTailBaseFastData.row 21 V) 21 V := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := valid_r21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r21_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (0+i)) 21 (0+i) = true := by decide +kernel

theorem strictBool_r21_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (1+i)) 21 (1+i) = true := by decide +kernel

theorem strictBool_r21_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (2+i)) 21 (2+i) = true := by decide +kernel

theorem strictBool_r21_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (3+i)) 21 (3+i) = true := by decide +kernel

theorem strictBool_r21_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (4+i)) 21 (4+i) = true := by decide +kernel

theorem strictBool_r21_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (5+i)) 21 (5+i) = true := by decide +kernel

theorem strictBool_r21_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (6+i)) 21 (6+i) = true := by decide +kernel

theorem strictBool_r21_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (7+i)) 21 (7+i) = true := by decide +kernel

theorem strictBool_r21_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (8+i)) 21 (8+i) = true := by decide +kernel

theorem strictBool_r21_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (9+i)) 21 (9+i) = true := by decide +kernel

theorem strictBool_r21_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (10+i)) 21 (10+i) = true := by decide +kernel

theorem strictBool_r21_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (11+i)) 21 (11+i) = true := by decide +kernel

theorem strictBool_r21_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (12+i)) 21 (12+i) = true := by decide +kernel

theorem strictBool_r21_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (13+i)) 21 (13+i) = true := by decide +kernel

theorem strictBool_r21_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (14+i)) 21 (14+i) = true := by decide +kernel

theorem strictBool_r21_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (15+i)) 21 (15+i) = true := by decide +kernel

theorem strictBool_r21_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (16+i)) 21 (16+i) = true := by decide +kernel

theorem strictBool_r21_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (17+i)) 21 (17+i) = true := by decide +kernel

theorem strictBool_r21_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (18+i)) 21 (18+i) = true := by decide +kernel

theorem strictBool_r21_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (19+i)) 21 (19+i) = true := by decide +kernel

theorem strictBool_r21_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (20+i)) 21 (20+i) = true := by decide +kernel

theorem strictBool_r21_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (21+i)) 21 (21+i) = true := by decide +kernel

theorem strictBool_r21_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (22+i)) 21 (22+i) = true := by decide +kernel

theorem strictBool_r21_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (23+i)) 21 (23+i) = true := by decide +kernel

theorem strictBool_r21_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (24+i)) 21 (24+i) = true := by decide +kernel

theorem strictBool_r21_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (25+i)) 21 (25+i) = true := by decide +kernel

theorem strictBool_r21_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (26+i)) 21 (26+i) = true := by decide +kernel

theorem strictBool_r21_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (27+i)) 21 (27+i) = true := by decide +kernel

theorem strictBool_r21_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (28+i)) 21 (28+i) = true := by decide +kernel

theorem strictBool_r21_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (29+i)) 21 (29+i) = true := by decide +kernel

theorem strictBool_r21_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (30+i)) 21 (30+i) = true := by decide +kernel

theorem strictBool_r21_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (31+i)) 21 (31+i) = true := by decide +kernel

theorem strictBool_r21_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (32+i)) 21 (32+i) = true := by decide +kernel

theorem strictBool_r21_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (33+i)) 21 (33+i) = true := by decide +kernel

theorem strictBool_r21_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (34+i)) 21 (34+i) = true := by decide +kernel

theorem strictBool_r21_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (35+i)) 21 (35+i) = true := by decide +kernel

theorem strictBool_r21_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (36+i)) 21 (36+i) = true := by decide +kernel

theorem strictBool_r21_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (37+i)) 21 (37+i) = true := by decide +kernel

theorem strictBool_r21_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (38+i)) 21 (38+i) = true := by decide +kernel

theorem strictBool_r21_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (39+i)) 21 (39+i) = true := by decide +kernel

theorem strictBool_r21_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (40+i)) 21 (40+i) = true := by decide +kernel

theorem strictBool_r21_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (41+i)) 21 (41+i) = true := by decide +kernel

theorem strictBool_r21_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (42+i)) 21 (42+i) = true := by decide +kernel

theorem strictBool_r21_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (43+i)) 21 (43+i) = true := by decide +kernel

theorem strictBool_r21_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (44+i)) 21 (44+i) = true := by decide +kernel

theorem strictBool_r21_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (45+i)) 21 (45+i) = true := by decide +kernel

theorem strictBool_r21_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (46+i)) 21 (46+i) = true := by decide +kernel

theorem strictBool_r21_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (47+i)) 21 (47+i) = true := by decide +kernel

theorem strictBool_r21_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (48+i)) 21 (48+i) = true := by decide +kernel

theorem strictBool_r21_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (49+i)) 21 (49+i) = true := by decide +kernel

theorem strictBool_r21_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (50+i)) 21 (50+i) = true := by decide +kernel

theorem strictBool_r21_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (51+i)) 21 (51+i) = true := by decide +kernel

theorem strictBool_r21_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (52+i)) 21 (52+i) = true := by decide +kernel

theorem strictBool_r21_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (53+i)) 21 (53+i) = true := by decide +kernel

theorem strictBool_r21_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (54+i)) 21 (54+i) = true := by decide +kernel

theorem strictBool_r21_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (55+i)) 21 (55+i) = true := by decide +kernel

theorem strictBool_r21_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (56+i)) 21 (56+i) = true := by decide +kernel

theorem strictBool_r21_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (57+i)) 21 (57+i) = true := by decide +kernel

theorem strictBool_r21_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (58+i)) 21 (58+i) = true := by decide +kernel

theorem strictBool_r21_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (59+i)) 21 (59+i) = true := by decide +kernel

theorem strictBool_r21_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (60+i)) 21 (60+i) = true := by decide +kernel

theorem strictBool_r21_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (61+i)) 21 (61+i) = true := by decide +kernel

theorem strictBool_r21_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (62+i)) 21 (62+i) = true := by decide +kernel

theorem strictBool_r21_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (63+i)) 21 (63+i) = true := by decide +kernel

theorem strictBool_r21_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (64+i)) 21 (64+i) = true := by decide +kernel

theorem strictBool_r21_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (65+i)) 21 (65+i) = true := by decide +kernel

theorem strictBool_r21_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (66+i)) 21 (66+i) = true := by decide +kernel

theorem strictBool_r21_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (67+i)) 21 (67+i) = true := by decide +kernel

theorem strictBool_r21_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (68+i)) 21 (68+i) = true := by decide +kernel

theorem strictBool_r21_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (69+i)) 21 (69+i) = true := by decide +kernel

theorem strictBool_r21_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (70+i)) 21 (70+i) = true := by decide +kernel

theorem strictBool_r21_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (71+i)) 21 (71+i) = true := by decide +kernel

theorem strictBool_r21_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (72+i)) 21 (72+i) = true := by decide +kernel

theorem strictBool_r21_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (73+i)) 21 (73+i) = true := by decide +kernel

theorem strictBool_r21_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (74+i)) 21 (74+i) = true := by decide +kernel

theorem strictBool_r21_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (75+i)) 21 (75+i) = true := by decide +kernel

theorem strictBool_r21_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (76+i)) 21 (76+i) = true := by decide +kernel

theorem strictBool_r21_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (77+i)) 21 (77+i) = true := by decide +kernel

theorem strictBool_r21_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (78+i)) 21 (78+i) = true := by decide +kernel

theorem strictBool_r21_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (79+i)) 21 (79+i) = true := by decide +kernel

theorem strictBool_r21_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (80+i)) 21 (80+i) = true := by decide +kernel

theorem strictBool_r21_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (81+i)) 21 (81+i) = true := by decide +kernel

theorem strictBool_r21_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (82+i)) 21 (82+i) = true := by decide +kernel

theorem strictBool_r21_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (83+i)) 21 (83+i) = true := by decide +kernel

theorem strictBool_r21_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (84+i)) 21 (84+i) = true := by decide +kernel

theorem strictBool_r21_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (85+i)) 21 (85+i) = true := by decide +kernel

theorem strictBool_r21_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (86+i)) 21 (86+i) = true := by decide +kernel

theorem strictBool_r21_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (87+i)) 21 (87+i) = true := by decide +kernel

theorem strictBool_r21_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (88+i)) 21 (88+i) = true := by decide +kernel

theorem strictBool_r21_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (89+i)) 21 (89+i) = true := by decide +kernel

theorem strictBool_r21_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (90+i)) 21 (90+i) = true := by decide +kernel

theorem strictBool_r21_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (91+i)) 21 (91+i) = true := by decide +kernel

theorem strictBool_r21_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (92+i)) 21 (92+i) = true := by decide +kernel

theorem strictBool_r21_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (93+i)) 21 (93+i) = true := by decide +kernel

theorem strictBool_r21_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (94+i)) 21 (94+i) = true := by decide +kernel

theorem strictBool_r21_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (95+i)) 21 (95+i) = true := by decide +kernel

theorem strictBool_r21_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (96+i)) 21 (96+i) = true := by decide +kernel

theorem strictBool_r21_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (97+i)) 21 (97+i) = true := by decide +kernel

theorem strictBool_r21_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (98+i)) 21 (98+i) = true := by decide +kernel

theorem strictBool_r21_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (99+i)) 21 (99+i) = true := by decide +kernel

theorem strictBool_r21_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (100+i)) 21 (100+i) = true := by decide +kernel

theorem strictBool_r21_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (101+i)) 21 (101+i) = true := by decide +kernel

theorem strictBool_r21_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (102+i)) 21 (102+i) = true := by decide +kernel

theorem strictBool_r21_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (103+i)) 21 (103+i) = true := by decide +kernel

theorem strictBool_r21_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (104+i)) 21 (104+i) = true := by decide +kernel

theorem strictBool_r21_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (105+i)) 21 (105+i) = true := by decide +kernel

theorem strictBool_r21_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (106+i)) 21 (106+i) = true := by decide +kernel

theorem strictBool_r21_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (107+i)) 21 (107+i) = true := by decide +kernel

theorem strictBool_r21_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (108+i)) 21 (108+i) = true := by decide +kernel

theorem strictBool_r21_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (109+i)) 21 (109+i) = true := by decide +kernel

theorem strictBool_r21_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (110+i)) 21 (110+i) = true := by decide +kernel

theorem strictBool_r21_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (111+i)) 21 (111+i) = true := by decide +kernel

theorem strictBool_r21_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (112+i)) 21 (112+i) = true := by decide +kernel

theorem strictBool_r21_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (113+i)) 21 (113+i) = true := by decide +kernel

theorem strictBool_r21_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (114+i)) 21 (114+i) = true := by decide +kernel

theorem strictBool_r21_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (115+i)) 21 (115+i) = true := by decide +kernel

theorem strictBool_r21_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (116+i)) 21 (116+i) = true := by decide +kernel

theorem strictBool_r21_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (117+i)) 21 (117+i) = true := by decide +kernel

theorem strictBool_r21_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (118+i)) 21 (118+i) = true := by decide +kernel

theorem strictBool_r21_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (119+i)) 21 (119+i) = true := by decide +kernel

theorem strictBool_r21_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (120+i)) 21 (120+i) = true := by decide +kernel

theorem strictBool_r21_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 21 (121+i)) 21 (121+i) = true := by decide +kernel

theorem strictBool_r21 (V : ℕ) (hV : V ∈ List.range 122) : strictBool (BoundaryTailBaseFastData.row 21 V) 21 V = true := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 61
  · by_cases h0_61 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r21_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r21_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r21_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r21_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r21_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r21_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r21_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r21_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have hi := strictBool_r21_part15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r21_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r21_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r21_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r21_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r21_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r21_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r21_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
    · by_cases h30_61 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have hi := strictBool_r21_part30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r21_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r21_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r21_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r21_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r21_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r21_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r21_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h45_61 : V < 53
        · by_cases h45_53 : V < 49
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r21_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r21_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r21_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r21_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
        · by_cases h53_61 : V < 57
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r21_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r21_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r21_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r21_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
  · by_cases h61_122 : V < 91
    · by_cases h61_91 : V < 76
      · by_cases h61_76 : V < 68
        · by_cases h61_68 : V < 64
          · by_cases h61_64 : V < 62
            · have hi := strictBool_r21_part61 (V-61) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r21_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r21_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r21_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r21_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r21_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r21_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r21_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
      · by_cases h76_91 : V < 83
        · by_cases h76_83 : V < 79
          · by_cases h76_79 : V < 77
            · have hi := strictBool_r21_part76 (V-76) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r21_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r21_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r21_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
        · by_cases h83_91 : V < 87
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r21_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r21_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r21_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r21_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
    · by_cases h91_122 : V < 106
      · by_cases h91_106 : V < 98
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have hi := strictBool_r21_part91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r21_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r21_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r21_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
        · by_cases h98_106 : V < 102
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r21_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r21_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r21_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r21_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
      · by_cases h106_122 : V < 114
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r21_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r21_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r21_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r21_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
        · by_cases h114_122 : V < 118
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r21_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r21_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r21_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r21_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r21_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi

theorem strictFast_r21 (V : ℕ) (hV : V ∈ List.range 122) : StrictAtFast (BoundaryTailBaseFastData.row 21 V) 21 V :=
  strictBool_sound _ _ _ (strictBool_r21 V hV)

theorem strict_r21 (V : ℕ) (hV : V ∈ List.range 122) : StrictCheckAt 21 V :=
  strictAtFast_sound _ _ _ (valid_r21 V hV) (strictFast_r21 V hV)

theorem zeroCertificate_r21_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (0+i)) 21 (0+i) := by decide +kernel

theorem zeroCertificate_r21_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (8+i)) 21 (8+i) := by decide +kernel

theorem zeroCertificate_r21_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (16+i)) 21 (16+i) := by decide +kernel

theorem zeroCertificate_r21_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (24+i)) 21 (24+i) := by decide +kernel

theorem zeroCertificate_r21_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (32+i)) 21 (32+i) := by decide +kernel

theorem zeroCertificate_r21_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (40+i)) 21 (40+i) := by decide +kernel

theorem zeroCertificate_r21_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (48+i)) 21 (48+i) := by decide +kernel

theorem zeroCertificate_r21_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (56+i)) 21 (56+i) := by decide +kernel

theorem zeroCertificate_r21_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (64+i)) 21 (64+i) := by decide +kernel

theorem zeroCertificate_r21_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (72+i)) 21 (72+i) := by decide +kernel

theorem zeroCertificate_r21_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (80+i)) 21 (80+i) := by decide +kernel

theorem zeroCertificate_r21_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (88+i)) 21 (88+i) := by decide +kernel

theorem zeroCertificate_r21_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (96+i)) 21 (96+i) := by decide +kernel

theorem zeroCertificate_r21_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (104+i)) 21 (104+i) := by decide +kernel

theorem zeroCertificate_r21_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 21 (112+i)) 21 (112+i) := by decide +kernel

theorem zeroCertificate_r21_part120 : ∀ i ∈ List.range 2, ZeroCertificate (BoundaryTailBaseFastData.row 21 (120+i)) 21 (120+i) := by decide +kernel

theorem zeroCertificate_r21 (V : ℕ) (hV : V ∈ List.range 122) : ZeroCertificate (BoundaryTailBaseFastData.row 21 V) 21 V := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := zeroCertificate_r21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r21 (V : ℕ) (hV : V ∈ List.range 122) : ZeroAtFast 21 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r21 V hV) (zeroCertificate_r21 V hV)

theorem zero_r21 (V : ℕ) (hV : V ∈ List.range 122) : ZeroCheckAt 21 V :=
  zeroAtFast_sound _ _ (zeroFast_r21 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r25_part0 : ∀ i ∈ List.range 8, CorrectAt 25 (0+i) := by decide +kernel

theorem correct_r25_part8 : ∀ i ∈ List.range 8, CorrectAt 25 (8+i) := by decide +kernel

theorem correct_r25_part16 : ∀ i ∈ List.range 8, CorrectAt 25 (16+i) := by decide +kernel

theorem correct_r25_part24 : ∀ i ∈ List.range 8, CorrectAt 25 (24+i) := by decide +kernel

theorem correct_r25_part32 : ∀ i ∈ List.range 8, CorrectAt 25 (32+i) := by decide +kernel

theorem correct_r25_part40 : ∀ i ∈ List.range 8, CorrectAt 25 (40+i) := by decide +kernel

theorem correct_r25_part48 : ∀ i ∈ List.range 8, CorrectAt 25 (48+i) := by decide +kernel

theorem correct_r25_part56 : ∀ i ∈ List.range 8, CorrectAt 25 (56+i) := by decide +kernel

theorem correct_r25_part64 : ∀ i ∈ List.range 8, CorrectAt 25 (64+i) := by decide +kernel

theorem correct_r25_part72 : ∀ i ∈ List.range 8, CorrectAt 25 (72+i) := by decide +kernel

theorem correct_r25_part80 : ∀ i ∈ List.range 8, CorrectAt 25 (80+i) := by decide +kernel

theorem correct_r25_part88 : ∀ i ∈ List.range 8, CorrectAt 25 (88+i) := by decide +kernel

theorem correct_r25_part96 : ∀ i ∈ List.range 8, CorrectAt 25 (96+i) := by decide +kernel

theorem correct_r25_part104 : ∀ i ∈ List.range 8, CorrectAt 25 (104+i) := by decide +kernel

theorem correct_r25_part112 : ∀ i ∈ List.range 6, CorrectAt 25 (112+i) := by decide +kernel

theorem correct_r25 (V : ℕ) (hV : V ∈ List.range 118) : CorrectAt 25 V := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := correct_r25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r25_part0 : ∀ i ∈ List.range 8, BaseCheckAt 25 (0+i) := by decide +kernel

theorem base_r25_part8 : ∀ i ∈ List.range 8, BaseCheckAt 25 (8+i) := by decide +kernel

theorem base_r25_part16 : ∀ i ∈ List.range 8, BaseCheckAt 25 (16+i) := by decide +kernel

theorem base_r25_part24 : ∀ i ∈ List.range 8, BaseCheckAt 25 (24+i) := by decide +kernel

theorem base_r25_part32 : ∀ i ∈ List.range 8, BaseCheckAt 25 (32+i) := by decide +kernel

theorem base_r25_part40 : ∀ i ∈ List.range 8, BaseCheckAt 25 (40+i) := by decide +kernel

theorem base_r25_part48 : ∀ i ∈ List.range 8, BaseCheckAt 25 (48+i) := by decide +kernel

theorem base_r25_part56 : ∀ i ∈ List.range 8, BaseCheckAt 25 (56+i) := by decide +kernel

theorem base_r25_part64 : ∀ i ∈ List.range 8, BaseCheckAt 25 (64+i) := by decide +kernel

theorem base_r25_part72 : ∀ i ∈ List.range 8, BaseCheckAt 25 (72+i) := by decide +kernel

theorem base_r25_part80 : ∀ i ∈ List.range 8, BaseCheckAt 25 (80+i) := by decide +kernel

theorem base_r25_part88 : ∀ i ∈ List.range 8, BaseCheckAt 25 (88+i) := by decide +kernel

theorem base_r25_part96 : ∀ i ∈ List.range 8, BaseCheckAt 25 (96+i) := by decide +kernel

theorem base_r25_part104 : ∀ i ∈ List.range 8, BaseCheckAt 25 (104+i) := by decide +kernel

theorem base_r25_part112 : ∀ i ∈ List.range 6, BaseCheckAt 25 (112+i) := by decide +kernel

theorem base_r25 (V : ℕ) (hV : V ∈ List.range 118) : BaseCheckAt 25 V := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := base_r25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r25_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (0+i)) 25 (0+i) := by decide +kernel

theorem valid_r25_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (8+i)) 25 (8+i) := by decide +kernel

theorem valid_r25_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (16+i)) 25 (16+i) := by decide +kernel

theorem valid_r25_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (24+i)) 25 (24+i) := by decide +kernel

theorem valid_r25_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (32+i)) 25 (32+i) := by decide +kernel

theorem valid_r25_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (40+i)) 25 (40+i) := by decide +kernel

theorem valid_r25_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (48+i)) 25 (48+i) := by decide +kernel

theorem valid_r25_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (56+i)) 25 (56+i) := by decide +kernel

theorem valid_r25_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (64+i)) 25 (64+i) := by decide +kernel

theorem valid_r25_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (72+i)) 25 (72+i) := by decide +kernel

theorem valid_r25_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (80+i)) 25 (80+i) := by decide +kernel

theorem valid_r25_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (88+i)) 25 (88+i) := by decide +kernel

theorem valid_r25_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (96+i)) 25 (96+i) := by decide +kernel

theorem valid_r25_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 25 (104+i)) 25 (104+i) := by decide +kernel

theorem valid_r25_part112 : ∀ i ∈ List.range 6, Valid (BoundaryTailBaseFastData.row 25 (112+i)) 25 (112+i) := by decide +kernel

theorem valid_r25 (V : ℕ) (hV : V ∈ List.range 118) : Valid (BoundaryTailBaseFastData.row 25 V) 25 V := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := valid_r25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r25_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (0+i)) 25 (0+i) = true := by decide +kernel

theorem strictBool_r25_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (1+i)) 25 (1+i) = true := by decide +kernel

theorem strictBool_r25_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (2+i)) 25 (2+i) = true := by decide +kernel

theorem strictBool_r25_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (3+i)) 25 (3+i) = true := by decide +kernel

theorem strictBool_r25_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (4+i)) 25 (4+i) = true := by decide +kernel

theorem strictBool_r25_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (5+i)) 25 (5+i) = true := by decide +kernel

theorem strictBool_r25_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (6+i)) 25 (6+i) = true := by decide +kernel

theorem strictBool_r25_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (7+i)) 25 (7+i) = true := by decide +kernel

theorem strictBool_r25_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (8+i)) 25 (8+i) = true := by decide +kernel

theorem strictBool_r25_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (9+i)) 25 (9+i) = true := by decide +kernel

theorem strictBool_r25_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (10+i)) 25 (10+i) = true := by decide +kernel

theorem strictBool_r25_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (11+i)) 25 (11+i) = true := by decide +kernel

theorem strictBool_r25_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (12+i)) 25 (12+i) = true := by decide +kernel

theorem strictBool_r25_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (13+i)) 25 (13+i) = true := by decide +kernel

theorem strictBool_r25_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (14+i)) 25 (14+i) = true := by decide +kernel

theorem strictBool_r25_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (15+i)) 25 (15+i) = true := by decide +kernel

theorem strictBool_r25_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (16+i)) 25 (16+i) = true := by decide +kernel

theorem strictBool_r25_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (17+i)) 25 (17+i) = true := by decide +kernel

theorem strictBool_r25_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (18+i)) 25 (18+i) = true := by decide +kernel

theorem strictBool_r25_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (19+i)) 25 (19+i) = true := by decide +kernel

theorem strictBool_r25_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (20+i)) 25 (20+i) = true := by decide +kernel

theorem strictBool_r25_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (21+i)) 25 (21+i) = true := by decide +kernel

theorem strictBool_r25_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (22+i)) 25 (22+i) = true := by decide +kernel

theorem strictBool_r25_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (23+i)) 25 (23+i) = true := by decide +kernel

theorem strictBool_r25_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (24+i)) 25 (24+i) = true := by decide +kernel

theorem strictBool_r25_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (25+i)) 25 (25+i) = true := by decide +kernel

theorem strictBool_r25_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (26+i)) 25 (26+i) = true := by decide +kernel

theorem strictBool_r25_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (27+i)) 25 (27+i) = true := by decide +kernel

theorem strictBool_r25_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (28+i)) 25 (28+i) = true := by decide +kernel

theorem strictBool_r25_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (29+i)) 25 (29+i) = true := by decide +kernel

theorem strictBool_r25_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (30+i)) 25 (30+i) = true := by decide +kernel

theorem strictBool_r25_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (31+i)) 25 (31+i) = true := by decide +kernel

theorem strictBool_r25_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (32+i)) 25 (32+i) = true := by decide +kernel

theorem strictBool_r25_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (33+i)) 25 (33+i) = true := by decide +kernel

theorem strictBool_r25_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (34+i)) 25 (34+i) = true := by decide +kernel

theorem strictBool_r25_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (35+i)) 25 (35+i) = true := by decide +kernel

theorem strictBool_r25_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (36+i)) 25 (36+i) = true := by decide +kernel

theorem strictBool_r25_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (37+i)) 25 (37+i) = true := by decide +kernel

theorem strictBool_r25_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (38+i)) 25 (38+i) = true := by decide +kernel

theorem strictBool_r25_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (39+i)) 25 (39+i) = true := by decide +kernel

theorem strictBool_r25_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (40+i)) 25 (40+i) = true := by decide +kernel

theorem strictBool_r25_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (41+i)) 25 (41+i) = true := by decide +kernel

theorem strictBool_r25_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (42+i)) 25 (42+i) = true := by decide +kernel

theorem strictBool_r25_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (43+i)) 25 (43+i) = true := by decide +kernel

theorem strictBool_r25_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (44+i)) 25 (44+i) = true := by decide +kernel

theorem strictBool_r25_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (45+i)) 25 (45+i) = true := by decide +kernel

theorem strictBool_r25_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (46+i)) 25 (46+i) = true := by decide +kernel

theorem strictBool_r25_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (47+i)) 25 (47+i) = true := by decide +kernel

theorem strictBool_r25_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (48+i)) 25 (48+i) = true := by decide +kernel

theorem strictBool_r25_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (49+i)) 25 (49+i) = true := by decide +kernel

theorem strictBool_r25_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (50+i)) 25 (50+i) = true := by decide +kernel

theorem strictBool_r25_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (51+i)) 25 (51+i) = true := by decide +kernel

theorem strictBool_r25_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (52+i)) 25 (52+i) = true := by decide +kernel

theorem strictBool_r25_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (53+i)) 25 (53+i) = true := by decide +kernel

theorem strictBool_r25_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (54+i)) 25 (54+i) = true := by decide +kernel

theorem strictBool_r25_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (55+i)) 25 (55+i) = true := by decide +kernel

theorem strictBool_r25_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (56+i)) 25 (56+i) = true := by decide +kernel

theorem strictBool_r25_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (57+i)) 25 (57+i) = true := by decide +kernel

theorem strictBool_r25_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (58+i)) 25 (58+i) = true := by decide +kernel

theorem strictBool_r25_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (59+i)) 25 (59+i) = true := by decide +kernel

theorem strictBool_r25_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (60+i)) 25 (60+i) = true := by decide +kernel

theorem strictBool_r25_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (61+i)) 25 (61+i) = true := by decide +kernel

theorem strictBool_r25_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (62+i)) 25 (62+i) = true := by decide +kernel

theorem strictBool_r25_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (63+i)) 25 (63+i) = true := by decide +kernel

theorem strictBool_r25_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (64+i)) 25 (64+i) = true := by decide +kernel

theorem strictBool_r25_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (65+i)) 25 (65+i) = true := by decide +kernel

theorem strictBool_r25_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (66+i)) 25 (66+i) = true := by decide +kernel

theorem strictBool_r25_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (67+i)) 25 (67+i) = true := by decide +kernel

theorem strictBool_r25_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (68+i)) 25 (68+i) = true := by decide +kernel

theorem strictBool_r25_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (69+i)) 25 (69+i) = true := by decide +kernel

theorem strictBool_r25_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (70+i)) 25 (70+i) = true := by decide +kernel

theorem strictBool_r25_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (71+i)) 25 (71+i) = true := by decide +kernel

theorem strictBool_r25_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (72+i)) 25 (72+i) = true := by decide +kernel

theorem strictBool_r25_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (73+i)) 25 (73+i) = true := by decide +kernel

theorem strictBool_r25_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (74+i)) 25 (74+i) = true := by decide +kernel

theorem strictBool_r25_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (75+i)) 25 (75+i) = true := by decide +kernel

theorem strictBool_r25_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (76+i)) 25 (76+i) = true := by decide +kernel

theorem strictBool_r25_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (77+i)) 25 (77+i) = true := by decide +kernel

theorem strictBool_r25_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (78+i)) 25 (78+i) = true := by decide +kernel

theorem strictBool_r25_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (79+i)) 25 (79+i) = true := by decide +kernel

theorem strictBool_r25_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (80+i)) 25 (80+i) = true := by decide +kernel

theorem strictBool_r25_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (81+i)) 25 (81+i) = true := by decide +kernel

theorem strictBool_r25_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (82+i)) 25 (82+i) = true := by decide +kernel

theorem strictBool_r25_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (83+i)) 25 (83+i) = true := by decide +kernel

theorem strictBool_r25_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (84+i)) 25 (84+i) = true := by decide +kernel

theorem strictBool_r25_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (85+i)) 25 (85+i) = true := by decide +kernel

theorem strictBool_r25_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (86+i)) 25 (86+i) = true := by decide +kernel

theorem strictBool_r25_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (87+i)) 25 (87+i) = true := by decide +kernel

theorem strictBool_r25_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (88+i)) 25 (88+i) = true := by decide +kernel

theorem strictBool_r25_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (89+i)) 25 (89+i) = true := by decide +kernel

theorem strictBool_r25_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (90+i)) 25 (90+i) = true := by decide +kernel

theorem strictBool_r25_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (91+i)) 25 (91+i) = true := by decide +kernel

theorem strictBool_r25_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (92+i)) 25 (92+i) = true := by decide +kernel

theorem strictBool_r25_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (93+i)) 25 (93+i) = true := by decide +kernel

theorem strictBool_r25_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (94+i)) 25 (94+i) = true := by decide +kernel

theorem strictBool_r25_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (95+i)) 25 (95+i) = true := by decide +kernel

theorem strictBool_r25_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (96+i)) 25 (96+i) = true := by decide +kernel

theorem strictBool_r25_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (97+i)) 25 (97+i) = true := by decide +kernel

theorem strictBool_r25_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (98+i)) 25 (98+i) = true := by decide +kernel

theorem strictBool_r25_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (99+i)) 25 (99+i) = true := by decide +kernel

theorem strictBool_r25_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (100+i)) 25 (100+i) = true := by decide +kernel

theorem strictBool_r25_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (101+i)) 25 (101+i) = true := by decide +kernel

theorem strictBool_r25_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (102+i)) 25 (102+i) = true := by decide +kernel

theorem strictBool_r25_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (103+i)) 25 (103+i) = true := by decide +kernel

theorem strictBool_r25_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (104+i)) 25 (104+i) = true := by decide +kernel

theorem strictBool_r25_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (105+i)) 25 (105+i) = true := by decide +kernel

theorem strictBool_r25_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (106+i)) 25 (106+i) = true := by decide +kernel

theorem strictBool_r25_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (107+i)) 25 (107+i) = true := by decide +kernel

theorem strictBool_r25_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (108+i)) 25 (108+i) = true := by decide +kernel

theorem strictBool_r25_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (109+i)) 25 (109+i) = true := by decide +kernel

theorem strictBool_r25_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (110+i)) 25 (110+i) = true := by decide +kernel

theorem strictBool_r25_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (111+i)) 25 (111+i) = true := by decide +kernel

theorem strictBool_r25_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (112+i)) 25 (112+i) = true := by decide +kernel

theorem strictBool_r25_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (113+i)) 25 (113+i) = true := by decide +kernel

theorem strictBool_r25_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (114+i)) 25 (114+i) = true := by decide +kernel

theorem strictBool_r25_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (115+i)) 25 (115+i) = true := by decide +kernel

theorem strictBool_r25_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (116+i)) 25 (116+i) = true := by decide +kernel

theorem strictBool_r25_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 25 (117+i)) 25 (117+i) = true := by decide +kernel

theorem strictBool_r25 (V : ℕ) (hV : V ∈ List.range 118) : strictBool (BoundaryTailBaseFastData.row 25 V) 25 V = true := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 59
  · by_cases h0_59 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r25_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r25_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r25_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r25_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r25_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r25_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r25_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r25_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r25_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r25_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r25_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r25_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r25_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r25_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r25_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r25_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h29_59 : V < 44
      · by_cases h29_44 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have hi := strictBool_r25_part29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r25_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r25_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r25_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
        · by_cases h36_44 : V < 40
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r25_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r25_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r25_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r25_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
      · by_cases h44_59 : V < 51
        · by_cases h44_51 : V < 47
          · by_cases h44_47 : V < 45
            · have hi := strictBool_r25_part44 (V-44) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r25_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r25_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r25_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r25_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r25_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r25_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r25_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
  · by_cases h59_118 : V < 88
    · by_cases h59_88 : V < 73
      · by_cases h59_73 : V < 66
        · by_cases h59_66 : V < 62
          · by_cases h59_62 : V < 60
            · have hi := strictBool_r25_part59 (V-59) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r25_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
          · by_cases h62_66 : V < 64
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r25_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r25_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
        · by_cases h66_73 : V < 69
          · by_cases h66_69 : V < 67
            · have hi := strictBool_r25_part66 (V-66) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r25_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r25_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r25_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h73_88 : V < 80
        · by_cases h73_80 : V < 76
          · by_cases h73_76 : V < 74
            · have hi := strictBool_r25_part73 (V-73) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r25_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r25_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r25_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
        · by_cases h80_88 : V < 84
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r25_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r25_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r25_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r25_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 103
      · by_cases h88_103 : V < 95
        · by_cases h88_95 : V < 91
          · by_cases h88_91 : V < 89
            · have hi := strictBool_r25_part88 (V-88) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r25_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r25_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r25_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
        · by_cases h95_103 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r25_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r25_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r25_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r25_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
      · by_cases h103_118 : V < 110
        · by_cases h103_110 : V < 106
          · by_cases h103_106 : V < 104
            · have hi := strictBool_r25_part103 (V-103) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r25_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r25_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r25_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_118 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r25_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r25_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r25_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r25_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r25_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi

theorem strictFast_r25 (V : ℕ) (hV : V ∈ List.range 118) : StrictAtFast (BoundaryTailBaseFastData.row 25 V) 25 V :=
  strictBool_sound _ _ _ (strictBool_r25 V hV)

theorem strict_r25 (V : ℕ) (hV : V ∈ List.range 118) : StrictCheckAt 25 V :=
  strictAtFast_sound _ _ _ (valid_r25 V hV) (strictFast_r25 V hV)

theorem zeroCertificate_r25_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (0+i)) 25 (0+i) := by decide +kernel

theorem zeroCertificate_r25_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (8+i)) 25 (8+i) := by decide +kernel

theorem zeroCertificate_r25_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (16+i)) 25 (16+i) := by decide +kernel

theorem zeroCertificate_r25_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (24+i)) 25 (24+i) := by decide +kernel

theorem zeroCertificate_r25_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (32+i)) 25 (32+i) := by decide +kernel

theorem zeroCertificate_r25_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (40+i)) 25 (40+i) := by decide +kernel

theorem zeroCertificate_r25_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (48+i)) 25 (48+i) := by decide +kernel

theorem zeroCertificate_r25_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (56+i)) 25 (56+i) := by decide +kernel

theorem zeroCertificate_r25_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (64+i)) 25 (64+i) := by decide +kernel

theorem zeroCertificate_r25_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (72+i)) 25 (72+i) := by decide +kernel

theorem zeroCertificate_r25_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (80+i)) 25 (80+i) := by decide +kernel

theorem zeroCertificate_r25_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (88+i)) 25 (88+i) := by decide +kernel

theorem zeroCertificate_r25_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (96+i)) 25 (96+i) := by decide +kernel

theorem zeroCertificate_r25_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 25 (104+i)) 25 (104+i) := by decide +kernel

theorem zeroCertificate_r25_part112 : ∀ i ∈ List.range 6, ZeroCertificate (BoundaryTailBaseFastData.row 25 (112+i)) 25 (112+i) := by decide +kernel

theorem zeroCertificate_r25 (V : ℕ) (hV : V ∈ List.range 118) : ZeroCertificate (BoundaryTailBaseFastData.row 25 V) 25 V := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := zeroCertificate_r25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r25 (V : ℕ) (hV : V ∈ List.range 118) : ZeroAtFast 25 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r25 V hV) (zeroCertificate_r25 V hV)

theorem zero_r25 (V : ℕ) (hV : V ∈ List.range 118) : ZeroCheckAt 25 V :=
  zeroAtFast_sound _ _ (zeroFast_r25 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r29_part0 : ∀ i ∈ List.range 8, CorrectAt 29 (0+i) := by decide +kernel

theorem correct_r29_part8 : ∀ i ∈ List.range 8, CorrectAt 29 (8+i) := by decide +kernel

theorem correct_r29_part16 : ∀ i ∈ List.range 8, CorrectAt 29 (16+i) := by decide +kernel

theorem correct_r29_part24 : ∀ i ∈ List.range 8, CorrectAt 29 (24+i) := by decide +kernel

theorem correct_r29_part32 : ∀ i ∈ List.range 8, CorrectAt 29 (32+i) := by decide +kernel

theorem correct_r29_part40 : ∀ i ∈ List.range 8, CorrectAt 29 (40+i) := by decide +kernel

theorem correct_r29_part48 : ∀ i ∈ List.range 8, CorrectAt 29 (48+i) := by decide +kernel

theorem correct_r29_part56 : ∀ i ∈ List.range 8, CorrectAt 29 (56+i) := by decide +kernel

theorem correct_r29_part64 : ∀ i ∈ List.range 8, CorrectAt 29 (64+i) := by decide +kernel

theorem correct_r29_part72 : ∀ i ∈ List.range 8, CorrectAt 29 (72+i) := by decide +kernel

theorem correct_r29_part80 : ∀ i ∈ List.range 8, CorrectAt 29 (80+i) := by decide +kernel

theorem correct_r29_part88 : ∀ i ∈ List.range 8, CorrectAt 29 (88+i) := by decide +kernel

theorem correct_r29_part96 : ∀ i ∈ List.range 8, CorrectAt 29 (96+i) := by decide +kernel

theorem correct_r29_part104 : ∀ i ∈ List.range 8, CorrectAt 29 (104+i) := by decide +kernel

theorem correct_r29_part112 : ∀ i ∈ List.range 2, CorrectAt 29 (112+i) := by decide +kernel

theorem correct_r29 (V : ℕ) (hV : V ∈ List.range 114) : CorrectAt 29 V := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := correct_r29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r29_part0 : ∀ i ∈ List.range 8, BaseCheckAt 29 (0+i) := by decide +kernel

theorem base_r29_part8 : ∀ i ∈ List.range 8, BaseCheckAt 29 (8+i) := by decide +kernel

theorem base_r29_part16 : ∀ i ∈ List.range 8, BaseCheckAt 29 (16+i) := by decide +kernel

theorem base_r29_part24 : ∀ i ∈ List.range 8, BaseCheckAt 29 (24+i) := by decide +kernel

theorem base_r29_part32 : ∀ i ∈ List.range 8, BaseCheckAt 29 (32+i) := by decide +kernel

theorem base_r29_part40 : ∀ i ∈ List.range 8, BaseCheckAt 29 (40+i) := by decide +kernel

theorem base_r29_part48 : ∀ i ∈ List.range 8, BaseCheckAt 29 (48+i) := by decide +kernel

theorem base_r29_part56 : ∀ i ∈ List.range 8, BaseCheckAt 29 (56+i) := by decide +kernel

theorem base_r29_part64 : ∀ i ∈ List.range 8, BaseCheckAt 29 (64+i) := by decide +kernel

theorem base_r29_part72 : ∀ i ∈ List.range 8, BaseCheckAt 29 (72+i) := by decide +kernel

theorem base_r29_part80 : ∀ i ∈ List.range 8, BaseCheckAt 29 (80+i) := by decide +kernel

theorem base_r29_part88 : ∀ i ∈ List.range 8, BaseCheckAt 29 (88+i) := by decide +kernel

theorem base_r29_part96 : ∀ i ∈ List.range 8, BaseCheckAt 29 (96+i) := by decide +kernel

theorem base_r29_part104 : ∀ i ∈ List.range 8, BaseCheckAt 29 (104+i) := by decide +kernel

theorem base_r29_part112 : ∀ i ∈ List.range 2, BaseCheckAt 29 (112+i) := by decide +kernel

theorem base_r29 (V : ℕ) (hV : V ∈ List.range 114) : BaseCheckAt 29 V := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := base_r29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r29_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (0+i)) 29 (0+i) := by decide +kernel

theorem valid_r29_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (8+i)) 29 (8+i) := by decide +kernel

theorem valid_r29_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (16+i)) 29 (16+i) := by decide +kernel

theorem valid_r29_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (24+i)) 29 (24+i) := by decide +kernel

theorem valid_r29_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (32+i)) 29 (32+i) := by decide +kernel

theorem valid_r29_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (40+i)) 29 (40+i) := by decide +kernel

theorem valid_r29_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (48+i)) 29 (48+i) := by decide +kernel

theorem valid_r29_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (56+i)) 29 (56+i) := by decide +kernel

theorem valid_r29_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (64+i)) 29 (64+i) := by decide +kernel

theorem valid_r29_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (72+i)) 29 (72+i) := by decide +kernel

theorem valid_r29_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (80+i)) 29 (80+i) := by decide +kernel

theorem valid_r29_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (88+i)) 29 (88+i) := by decide +kernel

theorem valid_r29_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (96+i)) 29 (96+i) := by decide +kernel

theorem valid_r29_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 29 (104+i)) 29 (104+i) := by decide +kernel

theorem valid_r29_part112 : ∀ i ∈ List.range 2, Valid (BoundaryTailBaseFastData.row 29 (112+i)) 29 (112+i) := by decide +kernel

theorem valid_r29 (V : ℕ) (hV : V ∈ List.range 114) : Valid (BoundaryTailBaseFastData.row 29 V) 29 V := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := valid_r29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r29_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (0+i)) 29 (0+i) = true := by decide +kernel

theorem strictBool_r29_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (1+i)) 29 (1+i) = true := by decide +kernel

theorem strictBool_r29_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (2+i)) 29 (2+i) = true := by decide +kernel

theorem strictBool_r29_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (3+i)) 29 (3+i) = true := by decide +kernel

theorem strictBool_r29_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (4+i)) 29 (4+i) = true := by decide +kernel

theorem strictBool_r29_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (5+i)) 29 (5+i) = true := by decide +kernel

theorem strictBool_r29_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (6+i)) 29 (6+i) = true := by decide +kernel

theorem strictBool_r29_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (7+i)) 29 (7+i) = true := by decide +kernel

theorem strictBool_r29_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (8+i)) 29 (8+i) = true := by decide +kernel

theorem strictBool_r29_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (9+i)) 29 (9+i) = true := by decide +kernel

theorem strictBool_r29_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (10+i)) 29 (10+i) = true := by decide +kernel

theorem strictBool_r29_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (11+i)) 29 (11+i) = true := by decide +kernel

theorem strictBool_r29_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (12+i)) 29 (12+i) = true := by decide +kernel

theorem strictBool_r29_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (13+i)) 29 (13+i) = true := by decide +kernel

theorem strictBool_r29_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (14+i)) 29 (14+i) = true := by decide +kernel

theorem strictBool_r29_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (15+i)) 29 (15+i) = true := by decide +kernel

theorem strictBool_r29_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (16+i)) 29 (16+i) = true := by decide +kernel

theorem strictBool_r29_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (17+i)) 29 (17+i) = true := by decide +kernel

theorem strictBool_r29_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (18+i)) 29 (18+i) = true := by decide +kernel

theorem strictBool_r29_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (19+i)) 29 (19+i) = true := by decide +kernel

theorem strictBool_r29_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (20+i)) 29 (20+i) = true := by decide +kernel

theorem strictBool_r29_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (21+i)) 29 (21+i) = true := by decide +kernel

theorem strictBool_r29_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (22+i)) 29 (22+i) = true := by decide +kernel

theorem strictBool_r29_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (23+i)) 29 (23+i) = true := by decide +kernel

theorem strictBool_r29_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (24+i)) 29 (24+i) = true := by decide +kernel

theorem strictBool_r29_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (25+i)) 29 (25+i) = true := by decide +kernel

theorem strictBool_r29_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (26+i)) 29 (26+i) = true := by decide +kernel

theorem strictBool_r29_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (27+i)) 29 (27+i) = true := by decide +kernel

theorem strictBool_r29_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (28+i)) 29 (28+i) = true := by decide +kernel

theorem strictBool_r29_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (29+i)) 29 (29+i) = true := by decide +kernel

theorem strictBool_r29_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (30+i)) 29 (30+i) = true := by decide +kernel

theorem strictBool_r29_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (31+i)) 29 (31+i) = true := by decide +kernel

theorem strictBool_r29_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (32+i)) 29 (32+i) = true := by decide +kernel

theorem strictBool_r29_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (33+i)) 29 (33+i) = true := by decide +kernel

theorem strictBool_r29_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (34+i)) 29 (34+i) = true := by decide +kernel

theorem strictBool_r29_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (35+i)) 29 (35+i) = true := by decide +kernel

theorem strictBool_r29_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (36+i)) 29 (36+i) = true := by decide +kernel

theorem strictBool_r29_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (37+i)) 29 (37+i) = true := by decide +kernel

theorem strictBool_r29_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (38+i)) 29 (38+i) = true := by decide +kernel

theorem strictBool_r29_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (39+i)) 29 (39+i) = true := by decide +kernel

theorem strictBool_r29_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (40+i)) 29 (40+i) = true := by decide +kernel

theorem strictBool_r29_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (41+i)) 29 (41+i) = true := by decide +kernel

theorem strictBool_r29_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (42+i)) 29 (42+i) = true := by decide +kernel

theorem strictBool_r29_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (43+i)) 29 (43+i) = true := by decide +kernel

theorem strictBool_r29_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (44+i)) 29 (44+i) = true := by decide +kernel

theorem strictBool_r29_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (45+i)) 29 (45+i) = true := by decide +kernel

theorem strictBool_r29_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (46+i)) 29 (46+i) = true := by decide +kernel

theorem strictBool_r29_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (47+i)) 29 (47+i) = true := by decide +kernel

theorem strictBool_r29_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (48+i)) 29 (48+i) = true := by decide +kernel

theorem strictBool_r29_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (49+i)) 29 (49+i) = true := by decide +kernel

theorem strictBool_r29_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (50+i)) 29 (50+i) = true := by decide +kernel

theorem strictBool_r29_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (51+i)) 29 (51+i) = true := by decide +kernel

theorem strictBool_r29_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (52+i)) 29 (52+i) = true := by decide +kernel

theorem strictBool_r29_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (53+i)) 29 (53+i) = true := by decide +kernel

theorem strictBool_r29_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (54+i)) 29 (54+i) = true := by decide +kernel

theorem strictBool_r29_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (55+i)) 29 (55+i) = true := by decide +kernel

theorem strictBool_r29_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (56+i)) 29 (56+i) = true := by decide +kernel

theorem strictBool_r29_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (57+i)) 29 (57+i) = true := by decide +kernel

theorem strictBool_r29_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (58+i)) 29 (58+i) = true := by decide +kernel

theorem strictBool_r29_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (59+i)) 29 (59+i) = true := by decide +kernel

theorem strictBool_r29_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (60+i)) 29 (60+i) = true := by decide +kernel

theorem strictBool_r29_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (61+i)) 29 (61+i) = true := by decide +kernel

theorem strictBool_r29_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (62+i)) 29 (62+i) = true := by decide +kernel

theorem strictBool_r29_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (63+i)) 29 (63+i) = true := by decide +kernel

theorem strictBool_r29_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (64+i)) 29 (64+i) = true := by decide +kernel

theorem strictBool_r29_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (65+i)) 29 (65+i) = true := by decide +kernel

theorem strictBool_r29_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (66+i)) 29 (66+i) = true := by decide +kernel

theorem strictBool_r29_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (67+i)) 29 (67+i) = true := by decide +kernel

theorem strictBool_r29_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (68+i)) 29 (68+i) = true := by decide +kernel

theorem strictBool_r29_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (69+i)) 29 (69+i) = true := by decide +kernel

theorem strictBool_r29_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (70+i)) 29 (70+i) = true := by decide +kernel

theorem strictBool_r29_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (71+i)) 29 (71+i) = true := by decide +kernel

theorem strictBool_r29_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (72+i)) 29 (72+i) = true := by decide +kernel

theorem strictBool_r29_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (73+i)) 29 (73+i) = true := by decide +kernel

theorem strictBool_r29_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (74+i)) 29 (74+i) = true := by decide +kernel

theorem strictBool_r29_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (75+i)) 29 (75+i) = true := by decide +kernel

theorem strictBool_r29_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (76+i)) 29 (76+i) = true := by decide +kernel

theorem strictBool_r29_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (77+i)) 29 (77+i) = true := by decide +kernel

theorem strictBool_r29_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (78+i)) 29 (78+i) = true := by decide +kernel

theorem strictBool_r29_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (79+i)) 29 (79+i) = true := by decide +kernel

theorem strictBool_r29_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (80+i)) 29 (80+i) = true := by decide +kernel

theorem strictBool_r29_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (81+i)) 29 (81+i) = true := by decide +kernel

theorem strictBool_r29_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (82+i)) 29 (82+i) = true := by decide +kernel

theorem strictBool_r29_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (83+i)) 29 (83+i) = true := by decide +kernel

theorem strictBool_r29_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (84+i)) 29 (84+i) = true := by decide +kernel

theorem strictBool_r29_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (85+i)) 29 (85+i) = true := by decide +kernel

theorem strictBool_r29_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (86+i)) 29 (86+i) = true := by decide +kernel

theorem strictBool_r29_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (87+i)) 29 (87+i) = true := by decide +kernel

theorem strictBool_r29_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (88+i)) 29 (88+i) = true := by decide +kernel

theorem strictBool_r29_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (89+i)) 29 (89+i) = true := by decide +kernel

theorem strictBool_r29_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (90+i)) 29 (90+i) = true := by decide +kernel

theorem strictBool_r29_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (91+i)) 29 (91+i) = true := by decide +kernel

theorem strictBool_r29_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (92+i)) 29 (92+i) = true := by decide +kernel

theorem strictBool_r29_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (93+i)) 29 (93+i) = true := by decide +kernel

theorem strictBool_r29_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (94+i)) 29 (94+i) = true := by decide +kernel

theorem strictBool_r29_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (95+i)) 29 (95+i) = true := by decide +kernel

theorem strictBool_r29_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (96+i)) 29 (96+i) = true := by decide +kernel

theorem strictBool_r29_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (97+i)) 29 (97+i) = true := by decide +kernel

theorem strictBool_r29_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (98+i)) 29 (98+i) = true := by decide +kernel

theorem strictBool_r29_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (99+i)) 29 (99+i) = true := by decide +kernel

theorem strictBool_r29_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (100+i)) 29 (100+i) = true := by decide +kernel

theorem strictBool_r29_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (101+i)) 29 (101+i) = true := by decide +kernel

theorem strictBool_r29_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (102+i)) 29 (102+i) = true := by decide +kernel

theorem strictBool_r29_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (103+i)) 29 (103+i) = true := by decide +kernel

theorem strictBool_r29_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (104+i)) 29 (104+i) = true := by decide +kernel

theorem strictBool_r29_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (105+i)) 29 (105+i) = true := by decide +kernel

theorem strictBool_r29_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (106+i)) 29 (106+i) = true := by decide +kernel

theorem strictBool_r29_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (107+i)) 29 (107+i) = true := by decide +kernel

theorem strictBool_r29_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (108+i)) 29 (108+i) = true := by decide +kernel

theorem strictBool_r29_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (109+i)) 29 (109+i) = true := by decide +kernel

theorem strictBool_r29_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (110+i)) 29 (110+i) = true := by decide +kernel

theorem strictBool_r29_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (111+i)) 29 (111+i) = true := by decide +kernel

theorem strictBool_r29_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (112+i)) 29 (112+i) = true := by decide +kernel

theorem strictBool_r29_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 29 (113+i)) 29 (113+i) = true := by decide +kernel

theorem strictBool_r29 (V : ℕ) (hV : V ∈ List.range 114) : strictBool (BoundaryTailBaseFastData.row 29 V) 29 V = true := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 57
  · by_cases h0_57 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r29_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r29_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r29_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r29_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r29_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r29_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r29_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r29_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r29_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r29_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r29_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r29_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have hi := strictBool_r29_part21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r29_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r29_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r29_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
    · by_cases h28_57 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have hi := strictBool_r29_part28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r29_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r29_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r29_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have hi := strictBool_r29_part35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r29_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r29_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r29_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
      · by_cases h42_57 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have hi := strictBool_r29_part42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r29_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r29_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r29_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r29_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r29_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r29_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r29_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h57_114 : V < 85
    · by_cases h57_85 : V < 71
      · by_cases h57_71 : V < 64
        · by_cases h57_64 : V < 60
          · by_cases h57_60 : V < 58
            · have hi := strictBool_r29_part57 (V-57) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r29_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r29_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r29_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
        · by_cases h64_71 : V < 67
          · by_cases h64_67 : V < 65
            · have hi := strictBool_r29_part64 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r29_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r29_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r29_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
      · by_cases h71_85 : V < 78
        · by_cases h71_78 : V < 74
          · by_cases h71_74 : V < 72
            · have hi := strictBool_r29_part71 (V-71) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r29_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r29_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r29_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
        · by_cases h78_85 : V < 81
          · by_cases h78_81 : V < 79
            · have hi := strictBool_r29_part78 (V-78) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r29_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r29_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r29_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
    · by_cases h85_114 : V < 99
      · by_cases h85_99 : V < 92
        · by_cases h85_92 : V < 88
          · by_cases h85_88 : V < 86
            · have hi := strictBool_r29_part85 (V-85) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r29_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r29_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r29_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
        · by_cases h92_99 : V < 95
          · by_cases h92_95 : V < 93
            · have hi := strictBool_r29_part92 (V-92) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r29_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r29_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r29_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
      · by_cases h99_114 : V < 106
        · by_cases h99_106 : V < 102
          · by_cases h99_102 : V < 100
            · have hi := strictBool_r29_part99 (V-99) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r29_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r29_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r29_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r29_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r29_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r29_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r29_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r29_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi

theorem strictFast_r29 (V : ℕ) (hV : V ∈ List.range 114) : StrictAtFast (BoundaryTailBaseFastData.row 29 V) 29 V :=
  strictBool_sound _ _ _ (strictBool_r29 V hV)

theorem strict_r29 (V : ℕ) (hV : V ∈ List.range 114) : StrictCheckAt 29 V :=
  strictAtFast_sound _ _ _ (valid_r29 V hV) (strictFast_r29 V hV)

theorem zeroCertificate_r29_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (0+i)) 29 (0+i) := by decide +kernel

theorem zeroCertificate_r29_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (8+i)) 29 (8+i) := by decide +kernel

theorem zeroCertificate_r29_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (16+i)) 29 (16+i) := by decide +kernel

theorem zeroCertificate_r29_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (24+i)) 29 (24+i) := by decide +kernel

theorem zeroCertificate_r29_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (32+i)) 29 (32+i) := by decide +kernel

theorem zeroCertificate_r29_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (40+i)) 29 (40+i) := by decide +kernel

theorem zeroCertificate_r29_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (48+i)) 29 (48+i) := by decide +kernel

theorem zeroCertificate_r29_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (56+i)) 29 (56+i) := by decide +kernel

theorem zeroCertificate_r29_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (64+i)) 29 (64+i) := by decide +kernel

theorem zeroCertificate_r29_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (72+i)) 29 (72+i) := by decide +kernel

theorem zeroCertificate_r29_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (80+i)) 29 (80+i) := by decide +kernel

theorem zeroCertificate_r29_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (88+i)) 29 (88+i) := by decide +kernel

theorem zeroCertificate_r29_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (96+i)) 29 (96+i) := by decide +kernel

theorem zeroCertificate_r29_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 29 (104+i)) 29 (104+i) := by decide +kernel

theorem zeroCertificate_r29_part112 : ∀ i ∈ List.range 2, ZeroCertificate (BoundaryTailBaseFastData.row 29 (112+i)) 29 (112+i) := by decide +kernel

theorem zeroCertificate_r29 (V : ℕ) (hV : V ∈ List.range 114) : ZeroCertificate (BoundaryTailBaseFastData.row 29 V) 29 V := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := zeroCertificate_r29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r29 (V : ℕ) (hV : V ∈ List.range 114) : ZeroAtFast 29 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r29 V hV) (zeroCertificate_r29 V hV)

theorem zero_r29 (V : ℕ) (hV : V ∈ List.range 114) : ZeroCheckAt 29 V :=
  zeroAtFast_sound _ _ (zeroFast_r29 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
