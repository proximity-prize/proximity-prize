import ProximityPrize.SubmissionLower.BoundaryTailBaseBlock02
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r3_part0 : ∀ i ∈ List.range 8, CorrectAt 3 (0+i) := by decide +kernel

theorem correct_r3_part8 : ∀ i ∈ List.range 8, CorrectAt 3 (8+i) := by decide +kernel

theorem correct_r3_part16 : ∀ i ∈ List.range 8, CorrectAt 3 (16+i) := by decide +kernel

theorem correct_r3_part24 : ∀ i ∈ List.range 8, CorrectAt 3 (24+i) := by decide +kernel

theorem correct_r3_part32 : ∀ i ∈ List.range 8, CorrectAt 3 (32+i) := by decide +kernel

theorem correct_r3_part40 : ∀ i ∈ List.range 8, CorrectAt 3 (40+i) := by decide +kernel

theorem correct_r3_part48 : ∀ i ∈ List.range 8, CorrectAt 3 (48+i) := by decide +kernel

theorem correct_r3_part56 : ∀ i ∈ List.range 8, CorrectAt 3 (56+i) := by decide +kernel

theorem correct_r3_part64 : ∀ i ∈ List.range 8, CorrectAt 3 (64+i) := by decide +kernel

theorem correct_r3_part72 : ∀ i ∈ List.range 8, CorrectAt 3 (72+i) := by decide +kernel

theorem correct_r3_part80 : ∀ i ∈ List.range 8, CorrectAt 3 (80+i) := by decide +kernel

theorem correct_r3_part88 : ∀ i ∈ List.range 8, CorrectAt 3 (88+i) := by decide +kernel

theorem correct_r3_part96 : ∀ i ∈ List.range 8, CorrectAt 3 (96+i) := by decide +kernel

theorem correct_r3_part104 : ∀ i ∈ List.range 8, CorrectAt 3 (104+i) := by decide +kernel

theorem correct_r3_part112 : ∀ i ∈ List.range 8, CorrectAt 3 (112+i) := by decide +kernel

theorem correct_r3_part120 : ∀ i ∈ List.range 8, CorrectAt 3 (120+i) := by decide +kernel

theorem correct_r3_part128 : ∀ i ∈ List.range 8, CorrectAt 3 (128+i) := by decide +kernel

theorem correct_r3_part136 : ∀ i ∈ List.range 4, CorrectAt 3 (136+i) := by decide +kernel

theorem correct_r3 (V : ℕ) (hV : V ∈ List.range 140) : CorrectAt 3 V := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := correct_r3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := correct_r3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := correct_r3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := correct_r3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := correct_r3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := correct_r3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := correct_r3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := correct_r3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := correct_r3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem base_r3_part0 : ∀ i ∈ List.range 8, BaseCheckAt 3 (0+i) := by decide +kernel

theorem base_r3_part8 : ∀ i ∈ List.range 8, BaseCheckAt 3 (8+i) := by decide +kernel

theorem base_r3_part16 : ∀ i ∈ List.range 8, BaseCheckAt 3 (16+i) := by decide +kernel

theorem base_r3_part24 : ∀ i ∈ List.range 8, BaseCheckAt 3 (24+i) := by decide +kernel

theorem base_r3_part32 : ∀ i ∈ List.range 8, BaseCheckAt 3 (32+i) := by decide +kernel

theorem base_r3_part40 : ∀ i ∈ List.range 8, BaseCheckAt 3 (40+i) := by decide +kernel

theorem base_r3_part48 : ∀ i ∈ List.range 8, BaseCheckAt 3 (48+i) := by decide +kernel

theorem base_r3_part56 : ∀ i ∈ List.range 8, BaseCheckAt 3 (56+i) := by decide +kernel

theorem base_r3_part64 : ∀ i ∈ List.range 8, BaseCheckAt 3 (64+i) := by decide +kernel

theorem base_r3_part72 : ∀ i ∈ List.range 8, BaseCheckAt 3 (72+i) := by decide +kernel

theorem base_r3_part80 : ∀ i ∈ List.range 8, BaseCheckAt 3 (80+i) := by decide +kernel

theorem base_r3_part88 : ∀ i ∈ List.range 8, BaseCheckAt 3 (88+i) := by decide +kernel

theorem base_r3_part96 : ∀ i ∈ List.range 8, BaseCheckAt 3 (96+i) := by decide +kernel

theorem base_r3_part104 : ∀ i ∈ List.range 8, BaseCheckAt 3 (104+i) := by decide +kernel

theorem base_r3_part112 : ∀ i ∈ List.range 8, BaseCheckAt 3 (112+i) := by decide +kernel

theorem base_r3_part120 : ∀ i ∈ List.range 8, BaseCheckAt 3 (120+i) := by decide +kernel

theorem base_r3_part128 : ∀ i ∈ List.range 8, BaseCheckAt 3 (128+i) := by decide +kernel

theorem base_r3_part136 : ∀ i ∈ List.range 4, BaseCheckAt 3 (136+i) := by decide +kernel

theorem base_r3 (V : ℕ) (hV : V ∈ List.range 140) : BaseCheckAt 3 V := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := base_r3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := base_r3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := base_r3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := base_r3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := base_r3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := base_r3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := base_r3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := base_r3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := base_r3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem valid_r3_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (0+i)) 3 (0+i) := by decide +kernel

theorem valid_r3_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (8+i)) 3 (8+i) := by decide +kernel

theorem valid_r3_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (16+i)) 3 (16+i) := by decide +kernel

theorem valid_r3_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (24+i)) 3 (24+i) := by decide +kernel

theorem valid_r3_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (32+i)) 3 (32+i) := by decide +kernel

theorem valid_r3_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (40+i)) 3 (40+i) := by decide +kernel

theorem valid_r3_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (48+i)) 3 (48+i) := by decide +kernel

theorem valid_r3_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (56+i)) 3 (56+i) := by decide +kernel

theorem valid_r3_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (64+i)) 3 (64+i) := by decide +kernel

theorem valid_r3_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (72+i)) 3 (72+i) := by decide +kernel

theorem valid_r3_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (80+i)) 3 (80+i) := by decide +kernel

theorem valid_r3_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (88+i)) 3 (88+i) := by decide +kernel

theorem valid_r3_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (96+i)) 3 (96+i) := by decide +kernel

theorem valid_r3_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (104+i)) 3 (104+i) := by decide +kernel

theorem valid_r3_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (112+i)) 3 (112+i) := by decide +kernel

theorem valid_r3_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (120+i)) 3 (120+i) := by decide +kernel

theorem valid_r3_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 3 (128+i)) 3 (128+i) := by decide +kernel

theorem valid_r3_part136 : ∀ i ∈ List.range 4, Valid (BoundaryTailBaseFastData.row 3 (136+i)) 3 (136+i) := by decide +kernel

theorem valid_r3 (V : ℕ) (hV : V ∈ List.range 140) : Valid (BoundaryTailBaseFastData.row 3 V) 3 V := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := valid_r3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := valid_r3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := valid_r3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := valid_r3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := valid_r3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := valid_r3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := valid_r3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := valid_r3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := valid_r3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem strictBool_r3_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (0+i)) 3 (0+i) = true := by decide +kernel

theorem strictBool_r3_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (1+i)) 3 (1+i) = true := by decide +kernel

theorem strictBool_r3_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (2+i)) 3 (2+i) = true := by decide +kernel

theorem strictBool_r3_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (3+i)) 3 (3+i) = true := by decide +kernel

theorem strictBool_r3_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (4+i)) 3 (4+i) = true := by decide +kernel

theorem strictBool_r3_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (5+i)) 3 (5+i) = true := by decide +kernel

theorem strictBool_r3_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (6+i)) 3 (6+i) = true := by decide +kernel

theorem strictBool_r3_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (7+i)) 3 (7+i) = true := by decide +kernel

theorem strictBool_r3_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (8+i)) 3 (8+i) = true := by decide +kernel

theorem strictBool_r3_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (9+i)) 3 (9+i) = true := by decide +kernel

theorem strictBool_r3_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (10+i)) 3 (10+i) = true := by decide +kernel

theorem strictBool_r3_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (11+i)) 3 (11+i) = true := by decide +kernel

theorem strictBool_r3_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (12+i)) 3 (12+i) = true := by decide +kernel

theorem strictBool_r3_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (13+i)) 3 (13+i) = true := by decide +kernel

theorem strictBool_r3_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (14+i)) 3 (14+i) = true := by decide +kernel

theorem strictBool_r3_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (15+i)) 3 (15+i) = true := by decide +kernel

theorem strictBool_r3_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (16+i)) 3 (16+i) = true := by decide +kernel

theorem strictBool_r3_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (17+i)) 3 (17+i) = true := by decide +kernel

theorem strictBool_r3_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (18+i)) 3 (18+i) = true := by decide +kernel

theorem strictBool_r3_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (19+i)) 3 (19+i) = true := by decide +kernel

theorem strictBool_r3_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (20+i)) 3 (20+i) = true := by decide +kernel

theorem strictBool_r3_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (21+i)) 3 (21+i) = true := by decide +kernel

theorem strictBool_r3_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (22+i)) 3 (22+i) = true := by decide +kernel

theorem strictBool_r3_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (23+i)) 3 (23+i) = true := by decide +kernel

theorem strictBool_r3_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (24+i)) 3 (24+i) = true := by decide +kernel

theorem strictBool_r3_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (25+i)) 3 (25+i) = true := by decide +kernel

theorem strictBool_r3_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (26+i)) 3 (26+i) = true := by decide +kernel

theorem strictBool_r3_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (27+i)) 3 (27+i) = true := by decide +kernel

theorem strictBool_r3_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (28+i)) 3 (28+i) = true := by decide +kernel

theorem strictBool_r3_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (29+i)) 3 (29+i) = true := by decide +kernel

theorem strictBool_r3_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (30+i)) 3 (30+i) = true := by decide +kernel

theorem strictBool_r3_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (31+i)) 3 (31+i) = true := by decide +kernel

theorem strictBool_r3_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (32+i)) 3 (32+i) = true := by decide +kernel

theorem strictBool_r3_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (33+i)) 3 (33+i) = true := by decide +kernel

theorem strictBool_r3_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (34+i)) 3 (34+i) = true := by decide +kernel

theorem strictBool_r3_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (35+i)) 3 (35+i) = true := by decide +kernel

theorem strictBool_r3_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (36+i)) 3 (36+i) = true := by decide +kernel

theorem strictBool_r3_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (37+i)) 3 (37+i) = true := by decide +kernel

theorem strictBool_r3_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (38+i)) 3 (38+i) = true := by decide +kernel

theorem strictBool_r3_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (39+i)) 3 (39+i) = true := by decide +kernel

theorem strictBool_r3_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (40+i)) 3 (40+i) = true := by decide +kernel

theorem strictBool_r3_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (41+i)) 3 (41+i) = true := by decide +kernel

theorem strictBool_r3_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (42+i)) 3 (42+i) = true := by decide +kernel

theorem strictBool_r3_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (43+i)) 3 (43+i) = true := by decide +kernel

theorem strictBool_r3_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (44+i)) 3 (44+i) = true := by decide +kernel

theorem strictBool_r3_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (45+i)) 3 (45+i) = true := by decide +kernel

theorem strictBool_r3_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (46+i)) 3 (46+i) = true := by decide +kernel

theorem strictBool_r3_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (47+i)) 3 (47+i) = true := by decide +kernel

theorem strictBool_r3_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (48+i)) 3 (48+i) = true := by decide +kernel

theorem strictBool_r3_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (49+i)) 3 (49+i) = true := by decide +kernel

theorem strictBool_r3_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (50+i)) 3 (50+i) = true := by decide +kernel

theorem strictBool_r3_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (51+i)) 3 (51+i) = true := by decide +kernel

theorem strictBool_r3_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (52+i)) 3 (52+i) = true := by decide +kernel

theorem strictBool_r3_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (53+i)) 3 (53+i) = true := by decide +kernel

theorem strictBool_r3_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (54+i)) 3 (54+i) = true := by decide +kernel

theorem strictBool_r3_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (55+i)) 3 (55+i) = true := by decide +kernel

theorem strictBool_r3_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (56+i)) 3 (56+i) = true := by decide +kernel

theorem strictBool_r3_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (57+i)) 3 (57+i) = true := by decide +kernel

theorem strictBool_r3_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (58+i)) 3 (58+i) = true := by decide +kernel

theorem strictBool_r3_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (59+i)) 3 (59+i) = true := by decide +kernel

theorem strictBool_r3_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (60+i)) 3 (60+i) = true := by decide +kernel

theorem strictBool_r3_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (61+i)) 3 (61+i) = true := by decide +kernel

theorem strictBool_r3_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (62+i)) 3 (62+i) = true := by decide +kernel

theorem strictBool_r3_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (63+i)) 3 (63+i) = true := by decide +kernel

theorem strictBool_r3_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (64+i)) 3 (64+i) = true := by decide +kernel

theorem strictBool_r3_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (65+i)) 3 (65+i) = true := by decide +kernel

theorem strictBool_r3_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (66+i)) 3 (66+i) = true := by decide +kernel

theorem strictBool_r3_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (67+i)) 3 (67+i) = true := by decide +kernel

theorem strictBool_r3_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (68+i)) 3 (68+i) = true := by decide +kernel

theorem strictBool_r3_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (69+i)) 3 (69+i) = true := by decide +kernel

theorem strictBool_r3_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (70+i)) 3 (70+i) = true := by decide +kernel

theorem strictBool_r3_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (71+i)) 3 (71+i) = true := by decide +kernel

theorem strictBool_r3_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (72+i)) 3 (72+i) = true := by decide +kernel

theorem strictBool_r3_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (73+i)) 3 (73+i) = true := by decide +kernel

theorem strictBool_r3_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (74+i)) 3 (74+i) = true := by decide +kernel

theorem strictBool_r3_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (75+i)) 3 (75+i) = true := by decide +kernel

theorem strictBool_r3_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (76+i)) 3 (76+i) = true := by decide +kernel

theorem strictBool_r3_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (77+i)) 3 (77+i) = true := by decide +kernel

theorem strictBool_r3_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (78+i)) 3 (78+i) = true := by decide +kernel

theorem strictBool_r3_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (79+i)) 3 (79+i) = true := by decide +kernel

theorem strictBool_r3_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (80+i)) 3 (80+i) = true := by decide +kernel

theorem strictBool_r3_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (81+i)) 3 (81+i) = true := by decide +kernel

theorem strictBool_r3_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (82+i)) 3 (82+i) = true := by decide +kernel

theorem strictBool_r3_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (83+i)) 3 (83+i) = true := by decide +kernel

theorem strictBool_r3_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (84+i)) 3 (84+i) = true := by decide +kernel

theorem strictBool_r3_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (85+i)) 3 (85+i) = true := by decide +kernel

theorem strictBool_r3_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (86+i)) 3 (86+i) = true := by decide +kernel

theorem strictBool_r3_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (87+i)) 3 (87+i) = true := by decide +kernel

theorem strictBool_r3_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (88+i)) 3 (88+i) = true := by decide +kernel

theorem strictBool_r3_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (89+i)) 3 (89+i) = true := by decide +kernel

theorem strictBool_r3_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (90+i)) 3 (90+i) = true := by decide +kernel

theorem strictBool_r3_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (91+i)) 3 (91+i) = true := by decide +kernel

theorem strictBool_r3_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (92+i)) 3 (92+i) = true := by decide +kernel

theorem strictBool_r3_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (93+i)) 3 (93+i) = true := by decide +kernel

theorem strictBool_r3_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (94+i)) 3 (94+i) = true := by decide +kernel

theorem strictBool_r3_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (95+i)) 3 (95+i) = true := by decide +kernel

theorem strictBool_r3_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (96+i)) 3 (96+i) = true := by decide +kernel

theorem strictBool_r3_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (97+i)) 3 (97+i) = true := by decide +kernel

theorem strictBool_r3_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (98+i)) 3 (98+i) = true := by decide +kernel

theorem strictBool_r3_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (99+i)) 3 (99+i) = true := by decide +kernel

theorem strictBool_r3_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (100+i)) 3 (100+i) = true := by decide +kernel

theorem strictBool_r3_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (101+i)) 3 (101+i) = true := by decide +kernel

theorem strictBool_r3_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (102+i)) 3 (102+i) = true := by decide +kernel

theorem strictBool_r3_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (103+i)) 3 (103+i) = true := by decide +kernel

theorem strictBool_r3_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (104+i)) 3 (104+i) = true := by decide +kernel

theorem strictBool_r3_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (105+i)) 3 (105+i) = true := by decide +kernel

theorem strictBool_r3_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (106+i)) 3 (106+i) = true := by decide +kernel

theorem strictBool_r3_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (107+i)) 3 (107+i) = true := by decide +kernel

theorem strictBool_r3_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (108+i)) 3 (108+i) = true := by decide +kernel

theorem strictBool_r3_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (109+i)) 3 (109+i) = true := by decide +kernel

theorem strictBool_r3_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (110+i)) 3 (110+i) = true := by decide +kernel

theorem strictBool_r3_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (111+i)) 3 (111+i) = true := by decide +kernel

theorem strictBool_r3_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (112+i)) 3 (112+i) = true := by decide +kernel

theorem strictBool_r3_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (113+i)) 3 (113+i) = true := by decide +kernel

theorem strictBool_r3_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (114+i)) 3 (114+i) = true := by decide +kernel

theorem strictBool_r3_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (115+i)) 3 (115+i) = true := by decide +kernel

theorem strictBool_r3_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (116+i)) 3 (116+i) = true := by decide +kernel

theorem strictBool_r3_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (117+i)) 3 (117+i) = true := by decide +kernel

theorem strictBool_r3_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (118+i)) 3 (118+i) = true := by decide +kernel

theorem strictBool_r3_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (119+i)) 3 (119+i) = true := by decide +kernel

theorem strictBool_r3_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (120+i)) 3 (120+i) = true := by decide +kernel

theorem strictBool_r3_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (121+i)) 3 (121+i) = true := by decide +kernel

theorem strictBool_r3_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (122+i)) 3 (122+i) = true := by decide +kernel

theorem strictBool_r3_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (123+i)) 3 (123+i) = true := by decide +kernel

theorem strictBool_r3_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (124+i)) 3 (124+i) = true := by decide +kernel

theorem strictBool_r3_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (125+i)) 3 (125+i) = true := by decide +kernel

theorem strictBool_r3_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (126+i)) 3 (126+i) = true := by decide +kernel

theorem strictBool_r3_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (127+i)) 3 (127+i) = true := by decide +kernel

theorem strictBool_r3_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (128+i)) 3 (128+i) = true := by decide +kernel

theorem strictBool_r3_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (129+i)) 3 (129+i) = true := by decide +kernel

theorem strictBool_r3_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (130+i)) 3 (130+i) = true := by decide +kernel

theorem strictBool_r3_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (131+i)) 3 (131+i) = true := by decide +kernel

theorem strictBool_r3_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (132+i)) 3 (132+i) = true := by decide +kernel

theorem strictBool_r3_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (133+i)) 3 (133+i) = true := by decide +kernel

theorem strictBool_r3_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (134+i)) 3 (134+i) = true := by decide +kernel

theorem strictBool_r3_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (135+i)) 3 (135+i) = true := by decide +kernel

theorem strictBool_r3_part136 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (136+i)) 3 (136+i) = true := by decide +kernel

theorem strictBool_r3_part137 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (137+i)) 3 (137+i) = true := by decide +kernel

theorem strictBool_r3_part138 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (138+i)) 3 (138+i) = true := by decide +kernel

theorem strictBool_r3_part139 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 3 (139+i)) 3 (139+i) = true := by decide +kernel

theorem strictBool_r3 (V : ℕ) (hV : V ∈ List.range 140) : strictBool (BoundaryTailBaseFastData.row 3 V) 3 V = true := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 70
  · by_cases h0_70 : V < 35
    · by_cases h0_35 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r3_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r3_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r3_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r3_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r3_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r3_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r3_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r3_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r3_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_35 : V < 26
        · by_cases h17_26 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r3_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r3_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_26 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r3_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_26 : V < 24
              · have hi := strictBool_r3_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · by_cases h24_26 : V < 25
                · have hi := strictBool_r3_part24 (V-24) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part25 (V-25) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
        · by_cases h26_35 : V < 30
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r3_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r3_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
          · by_cases h30_35 : V < 32
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r3_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_35 : V < 33
              · have hi := strictBool_r3_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · by_cases h33_35 : V < 34
                · have hi := strictBool_r3_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part34 (V-34) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
    · by_cases h35_70 : V < 52
      · by_cases h35_52 : V < 43
        · by_cases h35_43 : V < 39
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r3_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r3_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r3_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r3_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
        · by_cases h43_52 : V < 47
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r3_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r3_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
          · by_cases h47_52 : V < 49
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r3_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
            · by_cases h49_52 : V < 50
              · have hi := strictBool_r3_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · by_cases h50_52 : V < 51
                · have hi := strictBool_r3_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part51 (V-51) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
      · by_cases h52_70 : V < 61
        · by_cases h52_61 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r3_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r3_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
          · by_cases h56_61 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r3_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_61 : V < 59
              · have hi := strictBool_r3_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · by_cases h59_61 : V < 60
                · have hi := strictBool_r3_part59 (V-59) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part60 (V-60) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
        · by_cases h61_70 : V < 65
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r3_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r3_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
          · by_cases h65_70 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r3_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_70 : V < 68
              · have hi := strictBool_r3_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · by_cases h68_70 : V < 69
                · have hi := strictBool_r3_part68 (V-68) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part69 (V-69) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
  · by_cases h70_140 : V < 105
    · by_cases h70_105 : V < 87
      · by_cases h70_87 : V < 78
        · by_cases h70_78 : V < 74
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r3_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r3_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r3_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r3_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
        · by_cases h78_87 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r3_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r3_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
          · by_cases h82_87 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r3_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_87 : V < 85
              · have hi := strictBool_r3_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · by_cases h85_87 : V < 86
                · have hi := strictBool_r3_part85 (V-85) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part86 (V-86) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
      · by_cases h87_105 : V < 96
        · by_cases h87_96 : V < 91
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r3_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r3_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
          · by_cases h91_96 : V < 93
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r3_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
            · by_cases h93_96 : V < 94
              · have hi := strictBool_r3_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · by_cases h94_96 : V < 95
                · have hi := strictBool_r3_part94 (V-94) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part95 (V-95) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
        · by_cases h96_105 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r3_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r3_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_105 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r3_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_105 : V < 103
              · have hi := strictBool_r3_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · by_cases h103_105 : V < 104
                · have hi := strictBool_r3_part103 (V-103) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part104 (V-104) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
    · by_cases h105_140 : V < 122
      · by_cases h105_122 : V < 113
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r3_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r3_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r3_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r3_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h113_122 : V < 117
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r3_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r3_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
          · by_cases h117_122 : V < 119
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r3_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
            · by_cases h119_122 : V < 120
              · have hi := strictBool_r3_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · by_cases h120_122 : V < 121
                · have hi := strictBool_r3_part120 (V-120) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part121 (V-121) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
      · by_cases h122_140 : V < 131
        · by_cases h122_131 : V < 126
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r3_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r3_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
          · by_cases h126_131 : V < 128
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r3_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
            · by_cases h128_131 : V < 129
              · have hi := strictBool_r3_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
              · by_cases h129_131 : V < 130
                · have hi := strictBool_r3_part129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
        · by_cases h131_140 : V < 135
          · by_cases h131_135 : V < 133
            · by_cases h131_133 : V < 132
              · have hi := strictBool_r3_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · by_cases h133_135 : V < 134
              · have hi := strictBool_r3_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part134 (V-134) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
          · by_cases h135_140 : V < 137
            · by_cases h135_137 : V < 136
              · have hi := strictBool_r3_part135 (V-135) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi
              · have hi := strictBool_r3_part136 (V-136) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi
            · by_cases h137_140 : V < 138
              · have hi := strictBool_r3_part137 (V-137) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 137 ≤ V by omega)] using hi
              · by_cases h138_140 : V < 139
                · have hi := strictBool_r3_part138 (V-138) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 138 ≤ V by omega)] using hi
                · have hi := strictBool_r3_part139 (V-139) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 139 ≤ V by omega)] using hi

theorem strictFast_r3 (V : ℕ) (hV : V ∈ List.range 140) : StrictAtFast (BoundaryTailBaseFastData.row 3 V) 3 V :=
  strictBool_sound _ _ _ (strictBool_r3 V hV)

theorem strict_r3 (V : ℕ) (hV : V ∈ List.range 140) : StrictCheckAt 3 V :=
  strictAtFast_sound _ _ _ (valid_r3 V hV) (strictFast_r3 V hV)

theorem zeroCertificate_r3_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (0+i)) 3 (0+i) := by decide +kernel

theorem zeroCertificate_r3_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (8+i)) 3 (8+i) := by decide +kernel

theorem zeroCertificate_r3_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (16+i)) 3 (16+i) := by decide +kernel

theorem zeroCertificate_r3_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (24+i)) 3 (24+i) := by decide +kernel

theorem zeroCertificate_r3_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (32+i)) 3 (32+i) := by decide +kernel

theorem zeroCertificate_r3_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (40+i)) 3 (40+i) := by decide +kernel

theorem zeroCertificate_r3_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (48+i)) 3 (48+i) := by decide +kernel

theorem zeroCertificate_r3_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (56+i)) 3 (56+i) := by decide +kernel

theorem zeroCertificate_r3_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (64+i)) 3 (64+i) := by decide +kernel

theorem zeroCertificate_r3_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (72+i)) 3 (72+i) := by decide +kernel

theorem zeroCertificate_r3_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (80+i)) 3 (80+i) := by decide +kernel

theorem zeroCertificate_r3_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (88+i)) 3 (88+i) := by decide +kernel

theorem zeroCertificate_r3_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (96+i)) 3 (96+i) := by decide +kernel

theorem zeroCertificate_r3_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (104+i)) 3 (104+i) := by decide +kernel

theorem zeroCertificate_r3_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (112+i)) 3 (112+i) := by decide +kernel

theorem zeroCertificate_r3_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (120+i)) 3 (120+i) := by decide +kernel

theorem zeroCertificate_r3_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 3 (128+i)) 3 (128+i) := by decide +kernel

theorem zeroCertificate_r3_part136 : ∀ i ∈ List.range 4, ZeroCertificate (BoundaryTailBaseFastData.row 3 (136+i)) 3 (136+i) := by decide +kernel

theorem zeroCertificate_r3 (V : ℕ) (hV : V ∈ List.range 140) : ZeroCertificate (BoundaryTailBaseFastData.row 3 V) 3 V := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := zeroCertificate_r3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := zeroCertificate_r3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := zeroCertificate_r3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := zeroCertificate_r3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi

theorem zeroFast_r3 (V : ℕ) (hV : V ∈ List.range 140) : ZeroAtFast 3 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r3 V hV) (zeroCertificate_r3 V hV)

theorem zero_r3 (V : ℕ) (hV : V ∈ List.range 140) : ZeroCheckAt 3 V :=
  zeroAtFast_sound _ _ (zeroFast_r3 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r7_part0 : ∀ i ∈ List.range 8, CorrectAt 7 (0+i) := by decide +kernel

theorem correct_r7_part8 : ∀ i ∈ List.range 8, CorrectAt 7 (8+i) := by decide +kernel

theorem correct_r7_part16 : ∀ i ∈ List.range 8, CorrectAt 7 (16+i) := by decide +kernel

theorem correct_r7_part24 : ∀ i ∈ List.range 8, CorrectAt 7 (24+i) := by decide +kernel

theorem correct_r7_part32 : ∀ i ∈ List.range 8, CorrectAt 7 (32+i) := by decide +kernel

theorem correct_r7_part40 : ∀ i ∈ List.range 8, CorrectAt 7 (40+i) := by decide +kernel

theorem correct_r7_part48 : ∀ i ∈ List.range 8, CorrectAt 7 (48+i) := by decide +kernel

theorem correct_r7_part56 : ∀ i ∈ List.range 8, CorrectAt 7 (56+i) := by decide +kernel

theorem correct_r7_part64 : ∀ i ∈ List.range 8, CorrectAt 7 (64+i) := by decide +kernel

theorem correct_r7_part72 : ∀ i ∈ List.range 8, CorrectAt 7 (72+i) := by decide +kernel

theorem correct_r7_part80 : ∀ i ∈ List.range 8, CorrectAt 7 (80+i) := by decide +kernel

theorem correct_r7_part88 : ∀ i ∈ List.range 8, CorrectAt 7 (88+i) := by decide +kernel

theorem correct_r7_part96 : ∀ i ∈ List.range 8, CorrectAt 7 (96+i) := by decide +kernel

theorem correct_r7_part104 : ∀ i ∈ List.range 8, CorrectAt 7 (104+i) := by decide +kernel

theorem correct_r7_part112 : ∀ i ∈ List.range 8, CorrectAt 7 (112+i) := by decide +kernel

theorem correct_r7_part120 : ∀ i ∈ List.range 8, CorrectAt 7 (120+i) := by decide +kernel

theorem correct_r7_part128 : ∀ i ∈ List.range 8, CorrectAt 7 (128+i) := by decide +kernel

theorem correct_r7 (V : ℕ) (hV : V ∈ List.range 136) : CorrectAt 7 V := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := correct_r7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := correct_r7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r7_part0 : ∀ i ∈ List.range 8, BaseCheckAt 7 (0+i) := by decide +kernel

theorem base_r7_part8 : ∀ i ∈ List.range 8, BaseCheckAt 7 (8+i) := by decide +kernel

theorem base_r7_part16 : ∀ i ∈ List.range 8, BaseCheckAt 7 (16+i) := by decide +kernel

theorem base_r7_part24 : ∀ i ∈ List.range 8, BaseCheckAt 7 (24+i) := by decide +kernel

theorem base_r7_part32 : ∀ i ∈ List.range 8, BaseCheckAt 7 (32+i) := by decide +kernel

theorem base_r7_part40 : ∀ i ∈ List.range 8, BaseCheckAt 7 (40+i) := by decide +kernel

theorem base_r7_part48 : ∀ i ∈ List.range 8, BaseCheckAt 7 (48+i) := by decide +kernel

theorem base_r7_part56 : ∀ i ∈ List.range 8, BaseCheckAt 7 (56+i) := by decide +kernel

theorem base_r7_part64 : ∀ i ∈ List.range 8, BaseCheckAt 7 (64+i) := by decide +kernel

theorem base_r7_part72 : ∀ i ∈ List.range 8, BaseCheckAt 7 (72+i) := by decide +kernel

theorem base_r7_part80 : ∀ i ∈ List.range 8, BaseCheckAt 7 (80+i) := by decide +kernel

theorem base_r7_part88 : ∀ i ∈ List.range 8, BaseCheckAt 7 (88+i) := by decide +kernel

theorem base_r7_part96 : ∀ i ∈ List.range 8, BaseCheckAt 7 (96+i) := by decide +kernel

theorem base_r7_part104 : ∀ i ∈ List.range 8, BaseCheckAt 7 (104+i) := by decide +kernel

theorem base_r7_part112 : ∀ i ∈ List.range 8, BaseCheckAt 7 (112+i) := by decide +kernel

theorem base_r7_part120 : ∀ i ∈ List.range 8, BaseCheckAt 7 (120+i) := by decide +kernel

theorem base_r7_part128 : ∀ i ∈ List.range 8, BaseCheckAt 7 (128+i) := by decide +kernel

theorem base_r7 (V : ℕ) (hV : V ∈ List.range 136) : BaseCheckAt 7 V := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := base_r7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := base_r7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r7_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (0+i)) 7 (0+i) := by decide +kernel

theorem valid_r7_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (8+i)) 7 (8+i) := by decide +kernel

theorem valid_r7_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (16+i)) 7 (16+i) := by decide +kernel

theorem valid_r7_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (24+i)) 7 (24+i) := by decide +kernel

theorem valid_r7_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (32+i)) 7 (32+i) := by decide +kernel

theorem valid_r7_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (40+i)) 7 (40+i) := by decide +kernel

theorem valid_r7_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (48+i)) 7 (48+i) := by decide +kernel

theorem valid_r7_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (56+i)) 7 (56+i) := by decide +kernel

theorem valid_r7_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (64+i)) 7 (64+i) := by decide +kernel

theorem valid_r7_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (72+i)) 7 (72+i) := by decide +kernel

theorem valid_r7_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (80+i)) 7 (80+i) := by decide +kernel

theorem valid_r7_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (88+i)) 7 (88+i) := by decide +kernel

theorem valid_r7_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (96+i)) 7 (96+i) := by decide +kernel

theorem valid_r7_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (104+i)) 7 (104+i) := by decide +kernel

theorem valid_r7_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (112+i)) 7 (112+i) := by decide +kernel

theorem valid_r7_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (120+i)) 7 (120+i) := by decide +kernel

theorem valid_r7_part128 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 7 (128+i)) 7 (128+i) := by decide +kernel

theorem valid_r7 (V : ℕ) (hV : V ∈ List.range 136) : Valid (BoundaryTailBaseFastData.row 7 V) 7 V := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := valid_r7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := valid_r7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r7_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (0+i)) 7 (0+i) = true := by decide +kernel

theorem strictBool_r7_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (1+i)) 7 (1+i) = true := by decide +kernel

theorem strictBool_r7_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (2+i)) 7 (2+i) = true := by decide +kernel

theorem strictBool_r7_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (3+i)) 7 (3+i) = true := by decide +kernel

theorem strictBool_r7_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (4+i)) 7 (4+i) = true := by decide +kernel

theorem strictBool_r7_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (5+i)) 7 (5+i) = true := by decide +kernel

theorem strictBool_r7_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (6+i)) 7 (6+i) = true := by decide +kernel

theorem strictBool_r7_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (7+i)) 7 (7+i) = true := by decide +kernel

theorem strictBool_r7_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (8+i)) 7 (8+i) = true := by decide +kernel

theorem strictBool_r7_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (9+i)) 7 (9+i) = true := by decide +kernel

theorem strictBool_r7_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (10+i)) 7 (10+i) = true := by decide +kernel

theorem strictBool_r7_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (11+i)) 7 (11+i) = true := by decide +kernel

theorem strictBool_r7_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (12+i)) 7 (12+i) = true := by decide +kernel

theorem strictBool_r7_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (13+i)) 7 (13+i) = true := by decide +kernel

theorem strictBool_r7_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (14+i)) 7 (14+i) = true := by decide +kernel

theorem strictBool_r7_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (15+i)) 7 (15+i) = true := by decide +kernel

theorem strictBool_r7_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (16+i)) 7 (16+i) = true := by decide +kernel

theorem strictBool_r7_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (17+i)) 7 (17+i) = true := by decide +kernel

theorem strictBool_r7_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (18+i)) 7 (18+i) = true := by decide +kernel

theorem strictBool_r7_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (19+i)) 7 (19+i) = true := by decide +kernel

theorem strictBool_r7_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (20+i)) 7 (20+i) = true := by decide +kernel

theorem strictBool_r7_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (21+i)) 7 (21+i) = true := by decide +kernel

theorem strictBool_r7_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (22+i)) 7 (22+i) = true := by decide +kernel

theorem strictBool_r7_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (23+i)) 7 (23+i) = true := by decide +kernel

theorem strictBool_r7_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (24+i)) 7 (24+i) = true := by decide +kernel

theorem strictBool_r7_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (25+i)) 7 (25+i) = true := by decide +kernel

theorem strictBool_r7_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (26+i)) 7 (26+i) = true := by decide +kernel

theorem strictBool_r7_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (27+i)) 7 (27+i) = true := by decide +kernel

theorem strictBool_r7_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (28+i)) 7 (28+i) = true := by decide +kernel

theorem strictBool_r7_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (29+i)) 7 (29+i) = true := by decide +kernel

theorem strictBool_r7_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (30+i)) 7 (30+i) = true := by decide +kernel

theorem strictBool_r7_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (31+i)) 7 (31+i) = true := by decide +kernel

theorem strictBool_r7_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (32+i)) 7 (32+i) = true := by decide +kernel

theorem strictBool_r7_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (33+i)) 7 (33+i) = true := by decide +kernel

theorem strictBool_r7_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (34+i)) 7 (34+i) = true := by decide +kernel

theorem strictBool_r7_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (35+i)) 7 (35+i) = true := by decide +kernel

theorem strictBool_r7_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (36+i)) 7 (36+i) = true := by decide +kernel

theorem strictBool_r7_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (37+i)) 7 (37+i) = true := by decide +kernel

theorem strictBool_r7_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (38+i)) 7 (38+i) = true := by decide +kernel

theorem strictBool_r7_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (39+i)) 7 (39+i) = true := by decide +kernel

theorem strictBool_r7_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (40+i)) 7 (40+i) = true := by decide +kernel

theorem strictBool_r7_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (41+i)) 7 (41+i) = true := by decide +kernel

theorem strictBool_r7_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (42+i)) 7 (42+i) = true := by decide +kernel

theorem strictBool_r7_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (43+i)) 7 (43+i) = true := by decide +kernel

theorem strictBool_r7_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (44+i)) 7 (44+i) = true := by decide +kernel

theorem strictBool_r7_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (45+i)) 7 (45+i) = true := by decide +kernel

theorem strictBool_r7_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (46+i)) 7 (46+i) = true := by decide +kernel

theorem strictBool_r7_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (47+i)) 7 (47+i) = true := by decide +kernel

theorem strictBool_r7_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (48+i)) 7 (48+i) = true := by decide +kernel

theorem strictBool_r7_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (49+i)) 7 (49+i) = true := by decide +kernel

theorem strictBool_r7_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (50+i)) 7 (50+i) = true := by decide +kernel

theorem strictBool_r7_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (51+i)) 7 (51+i) = true := by decide +kernel

theorem strictBool_r7_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (52+i)) 7 (52+i) = true := by decide +kernel

theorem strictBool_r7_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (53+i)) 7 (53+i) = true := by decide +kernel

theorem strictBool_r7_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (54+i)) 7 (54+i) = true := by decide +kernel

theorem strictBool_r7_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (55+i)) 7 (55+i) = true := by decide +kernel

theorem strictBool_r7_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (56+i)) 7 (56+i) = true := by decide +kernel

theorem strictBool_r7_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (57+i)) 7 (57+i) = true := by decide +kernel

theorem strictBool_r7_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (58+i)) 7 (58+i) = true := by decide +kernel

theorem strictBool_r7_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (59+i)) 7 (59+i) = true := by decide +kernel

theorem strictBool_r7_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (60+i)) 7 (60+i) = true := by decide +kernel

theorem strictBool_r7_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (61+i)) 7 (61+i) = true := by decide +kernel

theorem strictBool_r7_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (62+i)) 7 (62+i) = true := by decide +kernel

theorem strictBool_r7_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (63+i)) 7 (63+i) = true := by decide +kernel

theorem strictBool_r7_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (64+i)) 7 (64+i) = true := by decide +kernel

theorem strictBool_r7_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (65+i)) 7 (65+i) = true := by decide +kernel

theorem strictBool_r7_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (66+i)) 7 (66+i) = true := by decide +kernel

theorem strictBool_r7_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (67+i)) 7 (67+i) = true := by decide +kernel

theorem strictBool_r7_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (68+i)) 7 (68+i) = true := by decide +kernel

theorem strictBool_r7_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (69+i)) 7 (69+i) = true := by decide +kernel

theorem strictBool_r7_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (70+i)) 7 (70+i) = true := by decide +kernel

theorem strictBool_r7_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (71+i)) 7 (71+i) = true := by decide +kernel

theorem strictBool_r7_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (72+i)) 7 (72+i) = true := by decide +kernel

theorem strictBool_r7_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (73+i)) 7 (73+i) = true := by decide +kernel

theorem strictBool_r7_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (74+i)) 7 (74+i) = true := by decide +kernel

theorem strictBool_r7_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (75+i)) 7 (75+i) = true := by decide +kernel

theorem strictBool_r7_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (76+i)) 7 (76+i) = true := by decide +kernel

theorem strictBool_r7_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (77+i)) 7 (77+i) = true := by decide +kernel

theorem strictBool_r7_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (78+i)) 7 (78+i) = true := by decide +kernel

theorem strictBool_r7_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (79+i)) 7 (79+i) = true := by decide +kernel

theorem strictBool_r7_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (80+i)) 7 (80+i) = true := by decide +kernel

theorem strictBool_r7_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (81+i)) 7 (81+i) = true := by decide +kernel

theorem strictBool_r7_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (82+i)) 7 (82+i) = true := by decide +kernel

theorem strictBool_r7_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (83+i)) 7 (83+i) = true := by decide +kernel

theorem strictBool_r7_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (84+i)) 7 (84+i) = true := by decide +kernel

theorem strictBool_r7_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (85+i)) 7 (85+i) = true := by decide +kernel

theorem strictBool_r7_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (86+i)) 7 (86+i) = true := by decide +kernel

theorem strictBool_r7_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (87+i)) 7 (87+i) = true := by decide +kernel

theorem strictBool_r7_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (88+i)) 7 (88+i) = true := by decide +kernel

theorem strictBool_r7_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (89+i)) 7 (89+i) = true := by decide +kernel

theorem strictBool_r7_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (90+i)) 7 (90+i) = true := by decide +kernel

theorem strictBool_r7_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (91+i)) 7 (91+i) = true := by decide +kernel

theorem strictBool_r7_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (92+i)) 7 (92+i) = true := by decide +kernel

theorem strictBool_r7_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (93+i)) 7 (93+i) = true := by decide +kernel

theorem strictBool_r7_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (94+i)) 7 (94+i) = true := by decide +kernel

theorem strictBool_r7_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (95+i)) 7 (95+i) = true := by decide +kernel

theorem strictBool_r7_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (96+i)) 7 (96+i) = true := by decide +kernel

theorem strictBool_r7_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (97+i)) 7 (97+i) = true := by decide +kernel

theorem strictBool_r7_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (98+i)) 7 (98+i) = true := by decide +kernel

theorem strictBool_r7_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (99+i)) 7 (99+i) = true := by decide +kernel

theorem strictBool_r7_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (100+i)) 7 (100+i) = true := by decide +kernel

theorem strictBool_r7_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (101+i)) 7 (101+i) = true := by decide +kernel

theorem strictBool_r7_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (102+i)) 7 (102+i) = true := by decide +kernel

theorem strictBool_r7_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (103+i)) 7 (103+i) = true := by decide +kernel

theorem strictBool_r7_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (104+i)) 7 (104+i) = true := by decide +kernel

theorem strictBool_r7_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (105+i)) 7 (105+i) = true := by decide +kernel

theorem strictBool_r7_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (106+i)) 7 (106+i) = true := by decide +kernel

theorem strictBool_r7_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (107+i)) 7 (107+i) = true := by decide +kernel

theorem strictBool_r7_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (108+i)) 7 (108+i) = true := by decide +kernel

theorem strictBool_r7_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (109+i)) 7 (109+i) = true := by decide +kernel

theorem strictBool_r7_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (110+i)) 7 (110+i) = true := by decide +kernel

theorem strictBool_r7_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (111+i)) 7 (111+i) = true := by decide +kernel

theorem strictBool_r7_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (112+i)) 7 (112+i) = true := by decide +kernel

theorem strictBool_r7_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (113+i)) 7 (113+i) = true := by decide +kernel

theorem strictBool_r7_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (114+i)) 7 (114+i) = true := by decide +kernel

theorem strictBool_r7_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (115+i)) 7 (115+i) = true := by decide +kernel

theorem strictBool_r7_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (116+i)) 7 (116+i) = true := by decide +kernel

theorem strictBool_r7_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (117+i)) 7 (117+i) = true := by decide +kernel

theorem strictBool_r7_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (118+i)) 7 (118+i) = true := by decide +kernel

theorem strictBool_r7_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (119+i)) 7 (119+i) = true := by decide +kernel

theorem strictBool_r7_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (120+i)) 7 (120+i) = true := by decide +kernel

theorem strictBool_r7_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (121+i)) 7 (121+i) = true := by decide +kernel

theorem strictBool_r7_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (122+i)) 7 (122+i) = true := by decide +kernel

theorem strictBool_r7_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (123+i)) 7 (123+i) = true := by decide +kernel

theorem strictBool_r7_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (124+i)) 7 (124+i) = true := by decide +kernel

theorem strictBool_r7_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (125+i)) 7 (125+i) = true := by decide +kernel

theorem strictBool_r7_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (126+i)) 7 (126+i) = true := by decide +kernel

theorem strictBool_r7_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (127+i)) 7 (127+i) = true := by decide +kernel

theorem strictBool_r7_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (128+i)) 7 (128+i) = true := by decide +kernel

theorem strictBool_r7_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (129+i)) 7 (129+i) = true := by decide +kernel

theorem strictBool_r7_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (130+i)) 7 (130+i) = true := by decide +kernel

theorem strictBool_r7_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (131+i)) 7 (131+i) = true := by decide +kernel

theorem strictBool_r7_part132 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (132+i)) 7 (132+i) = true := by decide +kernel

theorem strictBool_r7_part133 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (133+i)) 7 (133+i) = true := by decide +kernel

theorem strictBool_r7_part134 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (134+i)) 7 (134+i) = true := by decide +kernel

theorem strictBool_r7_part135 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 7 (135+i)) 7 (135+i) = true := by decide +kernel

theorem strictBool_r7 (V : ℕ) (hV : V ∈ List.range 136) : strictBool (BoundaryTailBaseFastData.row 7 V) 7 V = true := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r7_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r7_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r7_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r7_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r7_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r7_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r7_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_17 : V < 15
              · have hi := strictBool_r7_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · by_cases h15_17 : V < 16
                · have hi := strictBool_r7_part15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r7_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r7_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r7_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r7_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r7_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r7_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r7_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_34 : V < 32
              · have hi := strictBool_r7_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · by_cases h32_34 : V < 33
                · have hi := strictBool_r7_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r7_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r7_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r7_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r7_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r7_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r7_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r7_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_51 : V < 49
              · have hi := strictBool_r7_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · by_cases h49_51 : V < 50
                · have hi := strictBool_r7_part49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r7_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r7_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r7_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r7_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r7_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r7_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r7_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_68 : V < 66
              · have hi := strictBool_r7_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · by_cases h66_68 : V < 67
                · have hi := strictBool_r7_part66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
  · by_cases h68_136 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r7_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r7_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r7_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r7_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r7_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r7_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r7_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_85 : V < 83
              · have hi := strictBool_r7_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · by_cases h83_85 : V < 84
                · have hi := strictBool_r7_part83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r7_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r7_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r7_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r7_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r7_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r7_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r7_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_102 : V < 100
              · have hi := strictBool_r7_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · by_cases h100_102 : V < 101
                · have hi := strictBool_r7_part100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
    · by_cases h102_136 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r7_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r7_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r7_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r7_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r7_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r7_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r7_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
            · by_cases h116_119 : V < 117
              · have hi := strictBool_r7_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · by_cases h117_119 : V < 118
                · have hi := strictBool_r7_part117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
      · by_cases h119_136 : V < 127
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r7_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r7_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r7_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r7_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
        · by_cases h127_136 : V < 131
          · by_cases h127_131 : V < 129
            · by_cases h127_129 : V < 128
              · have hi := strictBool_r7_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_131 : V < 130
              · have hi := strictBool_r7_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
          · by_cases h131_136 : V < 133
            · by_cases h131_133 : V < 132
              · have hi := strictBool_r7_part131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi
              · have hi := strictBool_r7_part132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hi
            · by_cases h133_136 : V < 134
              · have hi := strictBool_r7_part133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using hi
              · by_cases h134_136 : V < 135
                · have hi := strictBool_r7_part134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using hi
                · have hi := strictBool_r7_part135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using hi

theorem strictFast_r7 (V : ℕ) (hV : V ∈ List.range 136) : StrictAtFast (BoundaryTailBaseFastData.row 7 V) 7 V :=
  strictBool_sound _ _ _ (strictBool_r7 V hV)

theorem strict_r7 (V : ℕ) (hV : V ∈ List.range 136) : StrictCheckAt 7 V :=
  strictAtFast_sound _ _ _ (valid_r7 V hV) (strictFast_r7 V hV)

theorem zeroCertificate_r7_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (0+i)) 7 (0+i) := by decide +kernel

theorem zeroCertificate_r7_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (8+i)) 7 (8+i) := by decide +kernel

theorem zeroCertificate_r7_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (16+i)) 7 (16+i) := by decide +kernel

theorem zeroCertificate_r7_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (24+i)) 7 (24+i) := by decide +kernel

theorem zeroCertificate_r7_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (32+i)) 7 (32+i) := by decide +kernel

theorem zeroCertificate_r7_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (40+i)) 7 (40+i) := by decide +kernel

theorem zeroCertificate_r7_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (48+i)) 7 (48+i) := by decide +kernel

theorem zeroCertificate_r7_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (56+i)) 7 (56+i) := by decide +kernel

theorem zeroCertificate_r7_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (64+i)) 7 (64+i) := by decide +kernel

theorem zeroCertificate_r7_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (72+i)) 7 (72+i) := by decide +kernel

theorem zeroCertificate_r7_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (80+i)) 7 (80+i) := by decide +kernel

theorem zeroCertificate_r7_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (88+i)) 7 (88+i) := by decide +kernel

theorem zeroCertificate_r7_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (96+i)) 7 (96+i) := by decide +kernel

theorem zeroCertificate_r7_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (104+i)) 7 (104+i) := by decide +kernel

theorem zeroCertificate_r7_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (112+i)) 7 (112+i) := by decide +kernel

theorem zeroCertificate_r7_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (120+i)) 7 (120+i) := by decide +kernel

theorem zeroCertificate_r7_part128 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 7 (128+i)) 7 (128+i) := by decide +kernel

theorem zeroCertificate_r7 (V : ℕ) (hV : V ∈ List.range 136) : ZeroCertificate (BoundaryTailBaseFastData.row 7 V) 7 V := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := zeroCertificate_r7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := zeroCertificate_r7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r7 (V : ℕ) (hV : V ∈ List.range 136) : ZeroAtFast 7 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r7 V hV) (zeroCertificate_r7 V hV)

theorem zero_r7 (V : ℕ) (hV : V ∈ List.range 136) : ZeroCheckAt 7 V :=
  zeroAtFast_sound _ _ (zeroFast_r7 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r11_part0 : ∀ i ∈ List.range 8, CorrectAt 11 (0+i) := by decide +kernel

theorem correct_r11_part8 : ∀ i ∈ List.range 8, CorrectAt 11 (8+i) := by decide +kernel

theorem correct_r11_part16 : ∀ i ∈ List.range 8, CorrectAt 11 (16+i) := by decide +kernel

theorem correct_r11_part24 : ∀ i ∈ List.range 8, CorrectAt 11 (24+i) := by decide +kernel

theorem correct_r11_part32 : ∀ i ∈ List.range 8, CorrectAt 11 (32+i) := by decide +kernel

theorem correct_r11_part40 : ∀ i ∈ List.range 8, CorrectAt 11 (40+i) := by decide +kernel

theorem correct_r11_part48 : ∀ i ∈ List.range 8, CorrectAt 11 (48+i) := by decide +kernel

theorem correct_r11_part56 : ∀ i ∈ List.range 8, CorrectAt 11 (56+i) := by decide +kernel

theorem correct_r11_part64 : ∀ i ∈ List.range 8, CorrectAt 11 (64+i) := by decide +kernel

theorem correct_r11_part72 : ∀ i ∈ List.range 8, CorrectAt 11 (72+i) := by decide +kernel

theorem correct_r11_part80 : ∀ i ∈ List.range 8, CorrectAt 11 (80+i) := by decide +kernel

theorem correct_r11_part88 : ∀ i ∈ List.range 8, CorrectAt 11 (88+i) := by decide +kernel

theorem correct_r11_part96 : ∀ i ∈ List.range 8, CorrectAt 11 (96+i) := by decide +kernel

theorem correct_r11_part104 : ∀ i ∈ List.range 8, CorrectAt 11 (104+i) := by decide +kernel

theorem correct_r11_part112 : ∀ i ∈ List.range 8, CorrectAt 11 (112+i) := by decide +kernel

theorem correct_r11_part120 : ∀ i ∈ List.range 8, CorrectAt 11 (120+i) := by decide +kernel

theorem correct_r11_part128 : ∀ i ∈ List.range 4, CorrectAt 11 (128+i) := by decide +kernel

theorem correct_r11 (V : ℕ) (hV : V ∈ List.range 132) : CorrectAt 11 V := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := correct_r11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := correct_r11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := correct_r11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem base_r11_part0 : ∀ i ∈ List.range 8, BaseCheckAt 11 (0+i) := by decide +kernel

theorem base_r11_part8 : ∀ i ∈ List.range 8, BaseCheckAt 11 (8+i) := by decide +kernel

theorem base_r11_part16 : ∀ i ∈ List.range 8, BaseCheckAt 11 (16+i) := by decide +kernel

theorem base_r11_part24 : ∀ i ∈ List.range 8, BaseCheckAt 11 (24+i) := by decide +kernel

theorem base_r11_part32 : ∀ i ∈ List.range 8, BaseCheckAt 11 (32+i) := by decide +kernel

theorem base_r11_part40 : ∀ i ∈ List.range 8, BaseCheckAt 11 (40+i) := by decide +kernel

theorem base_r11_part48 : ∀ i ∈ List.range 8, BaseCheckAt 11 (48+i) := by decide +kernel

theorem base_r11_part56 : ∀ i ∈ List.range 8, BaseCheckAt 11 (56+i) := by decide +kernel

theorem base_r11_part64 : ∀ i ∈ List.range 8, BaseCheckAt 11 (64+i) := by decide +kernel

theorem base_r11_part72 : ∀ i ∈ List.range 8, BaseCheckAt 11 (72+i) := by decide +kernel

theorem base_r11_part80 : ∀ i ∈ List.range 8, BaseCheckAt 11 (80+i) := by decide +kernel

theorem base_r11_part88 : ∀ i ∈ List.range 8, BaseCheckAt 11 (88+i) := by decide +kernel

theorem base_r11_part96 : ∀ i ∈ List.range 8, BaseCheckAt 11 (96+i) := by decide +kernel

theorem base_r11_part104 : ∀ i ∈ List.range 8, BaseCheckAt 11 (104+i) := by decide +kernel

theorem base_r11_part112 : ∀ i ∈ List.range 8, BaseCheckAt 11 (112+i) := by decide +kernel

theorem base_r11_part120 : ∀ i ∈ List.range 8, BaseCheckAt 11 (120+i) := by decide +kernel

theorem base_r11_part128 : ∀ i ∈ List.range 4, BaseCheckAt 11 (128+i) := by decide +kernel

theorem base_r11 (V : ℕ) (hV : V ∈ List.range 132) : BaseCheckAt 11 V := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := base_r11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := base_r11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := base_r11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem valid_r11_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (0+i)) 11 (0+i) := by decide +kernel

theorem valid_r11_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (8+i)) 11 (8+i) := by decide +kernel

theorem valid_r11_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (16+i)) 11 (16+i) := by decide +kernel

theorem valid_r11_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (24+i)) 11 (24+i) := by decide +kernel

theorem valid_r11_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (32+i)) 11 (32+i) := by decide +kernel

theorem valid_r11_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (40+i)) 11 (40+i) := by decide +kernel

theorem valid_r11_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (48+i)) 11 (48+i) := by decide +kernel

theorem valid_r11_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (56+i)) 11 (56+i) := by decide +kernel

theorem valid_r11_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (64+i)) 11 (64+i) := by decide +kernel

theorem valid_r11_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (72+i)) 11 (72+i) := by decide +kernel

theorem valid_r11_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (80+i)) 11 (80+i) := by decide +kernel

theorem valid_r11_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (88+i)) 11 (88+i) := by decide +kernel

theorem valid_r11_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (96+i)) 11 (96+i) := by decide +kernel

theorem valid_r11_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (104+i)) 11 (104+i) := by decide +kernel

theorem valid_r11_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (112+i)) 11 (112+i) := by decide +kernel

theorem valid_r11_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 11 (120+i)) 11 (120+i) := by decide +kernel

theorem valid_r11_part128 : ∀ i ∈ List.range 4, Valid (BoundaryTailBaseFastData.row 11 (128+i)) 11 (128+i) := by decide +kernel

theorem valid_r11 (V : ℕ) (hV : V ∈ List.range 132) : Valid (BoundaryTailBaseFastData.row 11 V) 11 V := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := valid_r11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := valid_r11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := valid_r11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem strictBool_r11_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (0+i)) 11 (0+i) = true := by decide +kernel

theorem strictBool_r11_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (1+i)) 11 (1+i) = true := by decide +kernel

theorem strictBool_r11_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (2+i)) 11 (2+i) = true := by decide +kernel

theorem strictBool_r11_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (3+i)) 11 (3+i) = true := by decide +kernel

theorem strictBool_r11_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (4+i)) 11 (4+i) = true := by decide +kernel

theorem strictBool_r11_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (5+i)) 11 (5+i) = true := by decide +kernel

theorem strictBool_r11_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (6+i)) 11 (6+i) = true := by decide +kernel

theorem strictBool_r11_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (7+i)) 11 (7+i) = true := by decide +kernel

theorem strictBool_r11_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (8+i)) 11 (8+i) = true := by decide +kernel

theorem strictBool_r11_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (9+i)) 11 (9+i) = true := by decide +kernel

theorem strictBool_r11_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (10+i)) 11 (10+i) = true := by decide +kernel

theorem strictBool_r11_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (11+i)) 11 (11+i) = true := by decide +kernel

theorem strictBool_r11_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (12+i)) 11 (12+i) = true := by decide +kernel

theorem strictBool_r11_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (13+i)) 11 (13+i) = true := by decide +kernel

theorem strictBool_r11_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (14+i)) 11 (14+i) = true := by decide +kernel

theorem strictBool_r11_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (15+i)) 11 (15+i) = true := by decide +kernel

theorem strictBool_r11_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (16+i)) 11 (16+i) = true := by decide +kernel

theorem strictBool_r11_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (17+i)) 11 (17+i) = true := by decide +kernel

theorem strictBool_r11_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (18+i)) 11 (18+i) = true := by decide +kernel

theorem strictBool_r11_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (19+i)) 11 (19+i) = true := by decide +kernel

theorem strictBool_r11_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (20+i)) 11 (20+i) = true := by decide +kernel

theorem strictBool_r11_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (21+i)) 11 (21+i) = true := by decide +kernel

theorem strictBool_r11_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (22+i)) 11 (22+i) = true := by decide +kernel

theorem strictBool_r11_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (23+i)) 11 (23+i) = true := by decide +kernel

theorem strictBool_r11_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (24+i)) 11 (24+i) = true := by decide +kernel

theorem strictBool_r11_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (25+i)) 11 (25+i) = true := by decide +kernel

theorem strictBool_r11_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (26+i)) 11 (26+i) = true := by decide +kernel

theorem strictBool_r11_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (27+i)) 11 (27+i) = true := by decide +kernel

theorem strictBool_r11_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (28+i)) 11 (28+i) = true := by decide +kernel

theorem strictBool_r11_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (29+i)) 11 (29+i) = true := by decide +kernel

theorem strictBool_r11_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (30+i)) 11 (30+i) = true := by decide +kernel

theorem strictBool_r11_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (31+i)) 11 (31+i) = true := by decide +kernel

theorem strictBool_r11_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (32+i)) 11 (32+i) = true := by decide +kernel

theorem strictBool_r11_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (33+i)) 11 (33+i) = true := by decide +kernel

theorem strictBool_r11_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (34+i)) 11 (34+i) = true := by decide +kernel

theorem strictBool_r11_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (35+i)) 11 (35+i) = true := by decide +kernel

theorem strictBool_r11_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (36+i)) 11 (36+i) = true := by decide +kernel

theorem strictBool_r11_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (37+i)) 11 (37+i) = true := by decide +kernel

theorem strictBool_r11_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (38+i)) 11 (38+i) = true := by decide +kernel

theorem strictBool_r11_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (39+i)) 11 (39+i) = true := by decide +kernel

theorem strictBool_r11_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (40+i)) 11 (40+i) = true := by decide +kernel

theorem strictBool_r11_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (41+i)) 11 (41+i) = true := by decide +kernel

theorem strictBool_r11_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (42+i)) 11 (42+i) = true := by decide +kernel

theorem strictBool_r11_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (43+i)) 11 (43+i) = true := by decide +kernel

theorem strictBool_r11_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (44+i)) 11 (44+i) = true := by decide +kernel

theorem strictBool_r11_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (45+i)) 11 (45+i) = true := by decide +kernel

theorem strictBool_r11_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (46+i)) 11 (46+i) = true := by decide +kernel

theorem strictBool_r11_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (47+i)) 11 (47+i) = true := by decide +kernel

theorem strictBool_r11_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (48+i)) 11 (48+i) = true := by decide +kernel

theorem strictBool_r11_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (49+i)) 11 (49+i) = true := by decide +kernel

theorem strictBool_r11_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (50+i)) 11 (50+i) = true := by decide +kernel

theorem strictBool_r11_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (51+i)) 11 (51+i) = true := by decide +kernel

theorem strictBool_r11_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (52+i)) 11 (52+i) = true := by decide +kernel

theorem strictBool_r11_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (53+i)) 11 (53+i) = true := by decide +kernel

theorem strictBool_r11_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (54+i)) 11 (54+i) = true := by decide +kernel

theorem strictBool_r11_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (55+i)) 11 (55+i) = true := by decide +kernel

theorem strictBool_r11_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (56+i)) 11 (56+i) = true := by decide +kernel

theorem strictBool_r11_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (57+i)) 11 (57+i) = true := by decide +kernel

theorem strictBool_r11_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (58+i)) 11 (58+i) = true := by decide +kernel

theorem strictBool_r11_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (59+i)) 11 (59+i) = true := by decide +kernel

theorem strictBool_r11_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (60+i)) 11 (60+i) = true := by decide +kernel

theorem strictBool_r11_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (61+i)) 11 (61+i) = true := by decide +kernel

theorem strictBool_r11_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (62+i)) 11 (62+i) = true := by decide +kernel

theorem strictBool_r11_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (63+i)) 11 (63+i) = true := by decide +kernel

theorem strictBool_r11_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (64+i)) 11 (64+i) = true := by decide +kernel

theorem strictBool_r11_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (65+i)) 11 (65+i) = true := by decide +kernel

theorem strictBool_r11_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (66+i)) 11 (66+i) = true := by decide +kernel

theorem strictBool_r11_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (67+i)) 11 (67+i) = true := by decide +kernel

theorem strictBool_r11_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (68+i)) 11 (68+i) = true := by decide +kernel

theorem strictBool_r11_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (69+i)) 11 (69+i) = true := by decide +kernel

theorem strictBool_r11_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (70+i)) 11 (70+i) = true := by decide +kernel

theorem strictBool_r11_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (71+i)) 11 (71+i) = true := by decide +kernel

theorem strictBool_r11_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (72+i)) 11 (72+i) = true := by decide +kernel

theorem strictBool_r11_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (73+i)) 11 (73+i) = true := by decide +kernel

theorem strictBool_r11_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (74+i)) 11 (74+i) = true := by decide +kernel

theorem strictBool_r11_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (75+i)) 11 (75+i) = true := by decide +kernel

theorem strictBool_r11_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (76+i)) 11 (76+i) = true := by decide +kernel

theorem strictBool_r11_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (77+i)) 11 (77+i) = true := by decide +kernel

theorem strictBool_r11_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (78+i)) 11 (78+i) = true := by decide +kernel

theorem strictBool_r11_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (79+i)) 11 (79+i) = true := by decide +kernel

theorem strictBool_r11_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (80+i)) 11 (80+i) = true := by decide +kernel

theorem strictBool_r11_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (81+i)) 11 (81+i) = true := by decide +kernel

theorem strictBool_r11_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (82+i)) 11 (82+i) = true := by decide +kernel

theorem strictBool_r11_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (83+i)) 11 (83+i) = true := by decide +kernel

theorem strictBool_r11_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (84+i)) 11 (84+i) = true := by decide +kernel

theorem strictBool_r11_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (85+i)) 11 (85+i) = true := by decide +kernel

theorem strictBool_r11_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (86+i)) 11 (86+i) = true := by decide +kernel

theorem strictBool_r11_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (87+i)) 11 (87+i) = true := by decide +kernel

theorem strictBool_r11_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (88+i)) 11 (88+i) = true := by decide +kernel

theorem strictBool_r11_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (89+i)) 11 (89+i) = true := by decide +kernel

theorem strictBool_r11_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (90+i)) 11 (90+i) = true := by decide +kernel

theorem strictBool_r11_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (91+i)) 11 (91+i) = true := by decide +kernel

theorem strictBool_r11_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (92+i)) 11 (92+i) = true := by decide +kernel

theorem strictBool_r11_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (93+i)) 11 (93+i) = true := by decide +kernel

theorem strictBool_r11_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (94+i)) 11 (94+i) = true := by decide +kernel

theorem strictBool_r11_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (95+i)) 11 (95+i) = true := by decide +kernel

theorem strictBool_r11_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (96+i)) 11 (96+i) = true := by decide +kernel

theorem strictBool_r11_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (97+i)) 11 (97+i) = true := by decide +kernel

theorem strictBool_r11_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (98+i)) 11 (98+i) = true := by decide +kernel

theorem strictBool_r11_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (99+i)) 11 (99+i) = true := by decide +kernel

theorem strictBool_r11_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (100+i)) 11 (100+i) = true := by decide +kernel

theorem strictBool_r11_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (101+i)) 11 (101+i) = true := by decide +kernel

theorem strictBool_r11_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (102+i)) 11 (102+i) = true := by decide +kernel

theorem strictBool_r11_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (103+i)) 11 (103+i) = true := by decide +kernel

theorem strictBool_r11_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (104+i)) 11 (104+i) = true := by decide +kernel

theorem strictBool_r11_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (105+i)) 11 (105+i) = true := by decide +kernel

theorem strictBool_r11_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (106+i)) 11 (106+i) = true := by decide +kernel

theorem strictBool_r11_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (107+i)) 11 (107+i) = true := by decide +kernel

theorem strictBool_r11_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (108+i)) 11 (108+i) = true := by decide +kernel

theorem strictBool_r11_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (109+i)) 11 (109+i) = true := by decide +kernel

theorem strictBool_r11_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (110+i)) 11 (110+i) = true := by decide +kernel

theorem strictBool_r11_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (111+i)) 11 (111+i) = true := by decide +kernel

theorem strictBool_r11_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (112+i)) 11 (112+i) = true := by decide +kernel

theorem strictBool_r11_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (113+i)) 11 (113+i) = true := by decide +kernel

theorem strictBool_r11_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (114+i)) 11 (114+i) = true := by decide +kernel

theorem strictBool_r11_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (115+i)) 11 (115+i) = true := by decide +kernel

theorem strictBool_r11_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (116+i)) 11 (116+i) = true := by decide +kernel

theorem strictBool_r11_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (117+i)) 11 (117+i) = true := by decide +kernel

theorem strictBool_r11_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (118+i)) 11 (118+i) = true := by decide +kernel

theorem strictBool_r11_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (119+i)) 11 (119+i) = true := by decide +kernel

theorem strictBool_r11_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (120+i)) 11 (120+i) = true := by decide +kernel

theorem strictBool_r11_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (121+i)) 11 (121+i) = true := by decide +kernel

theorem strictBool_r11_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (122+i)) 11 (122+i) = true := by decide +kernel

theorem strictBool_r11_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (123+i)) 11 (123+i) = true := by decide +kernel

theorem strictBool_r11_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (124+i)) 11 (124+i) = true := by decide +kernel

theorem strictBool_r11_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (125+i)) 11 (125+i) = true := by decide +kernel

theorem strictBool_r11_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (126+i)) 11 (126+i) = true := by decide +kernel

theorem strictBool_r11_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (127+i)) 11 (127+i) = true := by decide +kernel

theorem strictBool_r11_part128 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (128+i)) 11 (128+i) = true := by decide +kernel

theorem strictBool_r11_part129 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (129+i)) 11 (129+i) = true := by decide +kernel

theorem strictBool_r11_part130 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (130+i)) 11 (130+i) = true := by decide +kernel

theorem strictBool_r11_part131 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 11 (131+i)) 11 (131+i) = true := by decide +kernel

theorem strictBool_r11 (V : ℕ) (hV : V ∈ List.range 132) : strictBool (BoundaryTailBaseFastData.row 11 V) 11 V = true := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 66
  · by_cases h0_66 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r11_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r11_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r11_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r11_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r11_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r11_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r11_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r11_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r11_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r11_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r11_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r11_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r11_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r11_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r11_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_33 : V < 31
              · have hi := strictBool_r11_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · by_cases h31_33 : V < 32
                · have hi := strictBool_r11_part31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
                · have hi := strictBool_r11_part32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
    · by_cases h33_66 : V < 49
      · by_cases h33_49 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r11_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r11_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r11_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r11_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · by_cases h41_49 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r11_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r11_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r11_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r11_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
      · by_cases h49_66 : V < 57
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have hi := strictBool_r11_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
            · by_cases h51_53 : V < 52
              · have hi := strictBool_r11_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have hi := strictBool_r11_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
            · by_cases h55_57 : V < 56
              · have hi := strictBool_r11_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · by_cases h57_66 : V < 61
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r11_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r11_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h61_66 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r11_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_66 : V < 64
              · have hi := strictBool_r11_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · by_cases h64_66 : V < 65
                · have hi := strictBool_r11_part64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                · have hi := strictBool_r11_part65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
  · by_cases h66_132 : V < 99
    · by_cases h66_99 : V < 82
      · by_cases h66_82 : V < 74
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r11_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r11_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r11_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r11_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
        · by_cases h74_82 : V < 78
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r11_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r11_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r11_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r11_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
      · by_cases h82_99 : V < 90
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r11_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r11_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r11_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r11_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
        · by_cases h90_99 : V < 94
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r11_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r11_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
          · by_cases h94_99 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r11_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_99 : V < 97
              · have hi := strictBool_r11_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · by_cases h97_99 : V < 98
                · have hi := strictBool_r11_part97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
                · have hi := strictBool_r11_part98 (V-98) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
    · by_cases h99_132 : V < 115
      · by_cases h99_115 : V < 107
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r11_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r11_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r11_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
            · by_cases h105_107 : V < 106
              · have hi := strictBool_r11_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have hi := strictBool_r11_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
            · by_cases h109_111 : V < 110
              · have hi := strictBool_r11_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have hi := strictBool_r11_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
            · by_cases h113_115 : V < 114
              · have hi := strictBool_r11_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
      · by_cases h115_132 : V < 123
        · by_cases h115_123 : V < 119
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have hi := strictBool_r11_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
            · by_cases h117_119 : V < 118
              · have hi := strictBool_r11_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have hi := strictBool_r11_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
            · by_cases h121_123 : V < 122
              · have hi := strictBool_r11_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
        · by_cases h123_132 : V < 127
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have hi := strictBool_r11_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
            · by_cases h125_127 : V < 126
              · have hi := strictBool_r11_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
          · by_cases h127_132 : V < 129
            · by_cases h127_129 : V < 128
              · have hi := strictBool_r11_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi
              · have hi := strictBool_r11_part128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
            · by_cases h129_132 : V < 130
              · have hi := strictBool_r11_part129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using hi
              · by_cases h130_132 : V < 131
                · have hi := strictBool_r11_part130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using hi
                · have hi := strictBool_r11_part131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using hi

theorem strictFast_r11 (V : ℕ) (hV : V ∈ List.range 132) : StrictAtFast (BoundaryTailBaseFastData.row 11 V) 11 V :=
  strictBool_sound _ _ _ (strictBool_r11 V hV)

theorem strict_r11 (V : ℕ) (hV : V ∈ List.range 132) : StrictCheckAt 11 V :=
  strictAtFast_sound _ _ _ (valid_r11 V hV) (strictFast_r11 V hV)

theorem zeroCertificate_r11_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (0+i)) 11 (0+i) := by decide +kernel

theorem zeroCertificate_r11_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (8+i)) 11 (8+i) := by decide +kernel

theorem zeroCertificate_r11_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (16+i)) 11 (16+i) := by decide +kernel

theorem zeroCertificate_r11_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (24+i)) 11 (24+i) := by decide +kernel

theorem zeroCertificate_r11_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (32+i)) 11 (32+i) := by decide +kernel

theorem zeroCertificate_r11_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (40+i)) 11 (40+i) := by decide +kernel

theorem zeroCertificate_r11_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (48+i)) 11 (48+i) := by decide +kernel

theorem zeroCertificate_r11_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (56+i)) 11 (56+i) := by decide +kernel

theorem zeroCertificate_r11_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (64+i)) 11 (64+i) := by decide +kernel

theorem zeroCertificate_r11_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (72+i)) 11 (72+i) := by decide +kernel

theorem zeroCertificate_r11_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (80+i)) 11 (80+i) := by decide +kernel

theorem zeroCertificate_r11_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (88+i)) 11 (88+i) := by decide +kernel

theorem zeroCertificate_r11_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (96+i)) 11 (96+i) := by decide +kernel

theorem zeroCertificate_r11_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (104+i)) 11 (104+i) := by decide +kernel

theorem zeroCertificate_r11_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (112+i)) 11 (112+i) := by decide +kernel

theorem zeroCertificate_r11_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 11 (120+i)) 11 (120+i) := by decide +kernel

theorem zeroCertificate_r11_part128 : ∀ i ∈ List.range 4, ZeroCertificate (BoundaryTailBaseFastData.row 11 (128+i)) 11 (128+i) := by decide +kernel

theorem zeroCertificate_r11 (V : ℕ) (hV : V ∈ List.range 132) : ZeroCertificate (BoundaryTailBaseFastData.row 11 V) 11 V := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := zeroCertificate_r11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := zeroCertificate_r11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := zeroCertificate_r11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi

theorem zeroFast_r11 (V : ℕ) (hV : V ∈ List.range 132) : ZeroAtFast 11 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r11 V hV) (zeroCertificate_r11 V hV)

theorem zero_r11 (V : ℕ) (hV : V ∈ List.range 132) : ZeroCheckAt 11 V :=
  zeroAtFast_sound _ _ (zeroFast_r11 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r15_part0 : ∀ i ∈ List.range 8, CorrectAt 15 (0+i) := by decide +kernel

theorem correct_r15_part8 : ∀ i ∈ List.range 8, CorrectAt 15 (8+i) := by decide +kernel

theorem correct_r15_part16 : ∀ i ∈ List.range 8, CorrectAt 15 (16+i) := by decide +kernel

theorem correct_r15_part24 : ∀ i ∈ List.range 8, CorrectAt 15 (24+i) := by decide +kernel

theorem correct_r15_part32 : ∀ i ∈ List.range 8, CorrectAt 15 (32+i) := by decide +kernel

theorem correct_r15_part40 : ∀ i ∈ List.range 8, CorrectAt 15 (40+i) := by decide +kernel

theorem correct_r15_part48 : ∀ i ∈ List.range 8, CorrectAt 15 (48+i) := by decide +kernel

theorem correct_r15_part56 : ∀ i ∈ List.range 8, CorrectAt 15 (56+i) := by decide +kernel

theorem correct_r15_part64 : ∀ i ∈ List.range 8, CorrectAt 15 (64+i) := by decide +kernel

theorem correct_r15_part72 : ∀ i ∈ List.range 8, CorrectAt 15 (72+i) := by decide +kernel

theorem correct_r15_part80 : ∀ i ∈ List.range 8, CorrectAt 15 (80+i) := by decide +kernel

theorem correct_r15_part88 : ∀ i ∈ List.range 8, CorrectAt 15 (88+i) := by decide +kernel

theorem correct_r15_part96 : ∀ i ∈ List.range 8, CorrectAt 15 (96+i) := by decide +kernel

theorem correct_r15_part104 : ∀ i ∈ List.range 8, CorrectAt 15 (104+i) := by decide +kernel

theorem correct_r15_part112 : ∀ i ∈ List.range 8, CorrectAt 15 (112+i) := by decide +kernel

theorem correct_r15_part120 : ∀ i ∈ List.range 8, CorrectAt 15 (120+i) := by decide +kernel

theorem correct_r15 (V : ℕ) (hV : V ∈ List.range 128) : CorrectAt 15 V := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := correct_r15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r15_part0 : ∀ i ∈ List.range 8, BaseCheckAt 15 (0+i) := by decide +kernel

theorem base_r15_part8 : ∀ i ∈ List.range 8, BaseCheckAt 15 (8+i) := by decide +kernel

theorem base_r15_part16 : ∀ i ∈ List.range 8, BaseCheckAt 15 (16+i) := by decide +kernel

theorem base_r15_part24 : ∀ i ∈ List.range 8, BaseCheckAt 15 (24+i) := by decide +kernel

theorem base_r15_part32 : ∀ i ∈ List.range 8, BaseCheckAt 15 (32+i) := by decide +kernel

theorem base_r15_part40 : ∀ i ∈ List.range 8, BaseCheckAt 15 (40+i) := by decide +kernel

theorem base_r15_part48 : ∀ i ∈ List.range 8, BaseCheckAt 15 (48+i) := by decide +kernel

theorem base_r15_part56 : ∀ i ∈ List.range 8, BaseCheckAt 15 (56+i) := by decide +kernel

theorem base_r15_part64 : ∀ i ∈ List.range 8, BaseCheckAt 15 (64+i) := by decide +kernel

theorem base_r15_part72 : ∀ i ∈ List.range 8, BaseCheckAt 15 (72+i) := by decide +kernel

theorem base_r15_part80 : ∀ i ∈ List.range 8, BaseCheckAt 15 (80+i) := by decide +kernel

theorem base_r15_part88 : ∀ i ∈ List.range 8, BaseCheckAt 15 (88+i) := by decide +kernel

theorem base_r15_part96 : ∀ i ∈ List.range 8, BaseCheckAt 15 (96+i) := by decide +kernel

theorem base_r15_part104 : ∀ i ∈ List.range 8, BaseCheckAt 15 (104+i) := by decide +kernel

theorem base_r15_part112 : ∀ i ∈ List.range 8, BaseCheckAt 15 (112+i) := by decide +kernel

theorem base_r15_part120 : ∀ i ∈ List.range 8, BaseCheckAt 15 (120+i) := by decide +kernel

theorem base_r15 (V : ℕ) (hV : V ∈ List.range 128) : BaseCheckAt 15 V := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := base_r15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r15_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (0+i)) 15 (0+i) := by decide +kernel

theorem valid_r15_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (8+i)) 15 (8+i) := by decide +kernel

theorem valid_r15_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (16+i)) 15 (16+i) := by decide +kernel

theorem valid_r15_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (24+i)) 15 (24+i) := by decide +kernel

theorem valid_r15_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (32+i)) 15 (32+i) := by decide +kernel

theorem valid_r15_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (40+i)) 15 (40+i) := by decide +kernel

theorem valid_r15_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (48+i)) 15 (48+i) := by decide +kernel

theorem valid_r15_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (56+i)) 15 (56+i) := by decide +kernel

theorem valid_r15_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (64+i)) 15 (64+i) := by decide +kernel

theorem valid_r15_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (72+i)) 15 (72+i) := by decide +kernel

theorem valid_r15_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (80+i)) 15 (80+i) := by decide +kernel

theorem valid_r15_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (88+i)) 15 (88+i) := by decide +kernel

theorem valid_r15_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (96+i)) 15 (96+i) := by decide +kernel

theorem valid_r15_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (104+i)) 15 (104+i) := by decide +kernel

theorem valid_r15_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (112+i)) 15 (112+i) := by decide +kernel

theorem valid_r15_part120 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 15 (120+i)) 15 (120+i) := by decide +kernel

theorem valid_r15 (V : ℕ) (hV : V ∈ List.range 128) : Valid (BoundaryTailBaseFastData.row 15 V) 15 V := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := valid_r15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r15_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (0+i)) 15 (0+i) = true := by decide +kernel

theorem strictBool_r15_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (1+i)) 15 (1+i) = true := by decide +kernel

theorem strictBool_r15_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (2+i)) 15 (2+i) = true := by decide +kernel

theorem strictBool_r15_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (3+i)) 15 (3+i) = true := by decide +kernel

theorem strictBool_r15_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (4+i)) 15 (4+i) = true := by decide +kernel

theorem strictBool_r15_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (5+i)) 15 (5+i) = true := by decide +kernel

theorem strictBool_r15_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (6+i)) 15 (6+i) = true := by decide +kernel

theorem strictBool_r15_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (7+i)) 15 (7+i) = true := by decide +kernel

theorem strictBool_r15_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (8+i)) 15 (8+i) = true := by decide +kernel

theorem strictBool_r15_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (9+i)) 15 (9+i) = true := by decide +kernel

theorem strictBool_r15_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (10+i)) 15 (10+i) = true := by decide +kernel

theorem strictBool_r15_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (11+i)) 15 (11+i) = true := by decide +kernel

theorem strictBool_r15_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (12+i)) 15 (12+i) = true := by decide +kernel

theorem strictBool_r15_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (13+i)) 15 (13+i) = true := by decide +kernel

theorem strictBool_r15_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (14+i)) 15 (14+i) = true := by decide +kernel

theorem strictBool_r15_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (15+i)) 15 (15+i) = true := by decide +kernel

theorem strictBool_r15_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (16+i)) 15 (16+i) = true := by decide +kernel

theorem strictBool_r15_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (17+i)) 15 (17+i) = true := by decide +kernel

theorem strictBool_r15_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (18+i)) 15 (18+i) = true := by decide +kernel

theorem strictBool_r15_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (19+i)) 15 (19+i) = true := by decide +kernel

theorem strictBool_r15_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (20+i)) 15 (20+i) = true := by decide +kernel

theorem strictBool_r15_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (21+i)) 15 (21+i) = true := by decide +kernel

theorem strictBool_r15_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (22+i)) 15 (22+i) = true := by decide +kernel

theorem strictBool_r15_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (23+i)) 15 (23+i) = true := by decide +kernel

theorem strictBool_r15_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (24+i)) 15 (24+i) = true := by decide +kernel

theorem strictBool_r15_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (25+i)) 15 (25+i) = true := by decide +kernel

theorem strictBool_r15_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (26+i)) 15 (26+i) = true := by decide +kernel

theorem strictBool_r15_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (27+i)) 15 (27+i) = true := by decide +kernel

theorem strictBool_r15_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (28+i)) 15 (28+i) = true := by decide +kernel

theorem strictBool_r15_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (29+i)) 15 (29+i) = true := by decide +kernel

theorem strictBool_r15_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (30+i)) 15 (30+i) = true := by decide +kernel

theorem strictBool_r15_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (31+i)) 15 (31+i) = true := by decide +kernel

theorem strictBool_r15_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (32+i)) 15 (32+i) = true := by decide +kernel

theorem strictBool_r15_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (33+i)) 15 (33+i) = true := by decide +kernel

theorem strictBool_r15_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (34+i)) 15 (34+i) = true := by decide +kernel

theorem strictBool_r15_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (35+i)) 15 (35+i) = true := by decide +kernel

theorem strictBool_r15_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (36+i)) 15 (36+i) = true := by decide +kernel

theorem strictBool_r15_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (37+i)) 15 (37+i) = true := by decide +kernel

theorem strictBool_r15_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (38+i)) 15 (38+i) = true := by decide +kernel

theorem strictBool_r15_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (39+i)) 15 (39+i) = true := by decide +kernel

theorem strictBool_r15_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (40+i)) 15 (40+i) = true := by decide +kernel

theorem strictBool_r15_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (41+i)) 15 (41+i) = true := by decide +kernel

theorem strictBool_r15_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (42+i)) 15 (42+i) = true := by decide +kernel

theorem strictBool_r15_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (43+i)) 15 (43+i) = true := by decide +kernel

theorem strictBool_r15_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (44+i)) 15 (44+i) = true := by decide +kernel

theorem strictBool_r15_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (45+i)) 15 (45+i) = true := by decide +kernel

theorem strictBool_r15_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (46+i)) 15 (46+i) = true := by decide +kernel

theorem strictBool_r15_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (47+i)) 15 (47+i) = true := by decide +kernel

theorem strictBool_r15_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (48+i)) 15 (48+i) = true := by decide +kernel

theorem strictBool_r15_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (49+i)) 15 (49+i) = true := by decide +kernel

theorem strictBool_r15_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (50+i)) 15 (50+i) = true := by decide +kernel

theorem strictBool_r15_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (51+i)) 15 (51+i) = true := by decide +kernel

theorem strictBool_r15_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (52+i)) 15 (52+i) = true := by decide +kernel

theorem strictBool_r15_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (53+i)) 15 (53+i) = true := by decide +kernel

theorem strictBool_r15_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (54+i)) 15 (54+i) = true := by decide +kernel

theorem strictBool_r15_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (55+i)) 15 (55+i) = true := by decide +kernel

theorem strictBool_r15_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (56+i)) 15 (56+i) = true := by decide +kernel

theorem strictBool_r15_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (57+i)) 15 (57+i) = true := by decide +kernel

theorem strictBool_r15_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (58+i)) 15 (58+i) = true := by decide +kernel

theorem strictBool_r15_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (59+i)) 15 (59+i) = true := by decide +kernel

theorem strictBool_r15_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (60+i)) 15 (60+i) = true := by decide +kernel

theorem strictBool_r15_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (61+i)) 15 (61+i) = true := by decide +kernel

theorem strictBool_r15_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (62+i)) 15 (62+i) = true := by decide +kernel

theorem strictBool_r15_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (63+i)) 15 (63+i) = true := by decide +kernel

theorem strictBool_r15_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (64+i)) 15 (64+i) = true := by decide +kernel

theorem strictBool_r15_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (65+i)) 15 (65+i) = true := by decide +kernel

theorem strictBool_r15_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (66+i)) 15 (66+i) = true := by decide +kernel

theorem strictBool_r15_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (67+i)) 15 (67+i) = true := by decide +kernel

theorem strictBool_r15_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (68+i)) 15 (68+i) = true := by decide +kernel

theorem strictBool_r15_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (69+i)) 15 (69+i) = true := by decide +kernel

theorem strictBool_r15_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (70+i)) 15 (70+i) = true := by decide +kernel

theorem strictBool_r15_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (71+i)) 15 (71+i) = true := by decide +kernel

theorem strictBool_r15_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (72+i)) 15 (72+i) = true := by decide +kernel

theorem strictBool_r15_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (73+i)) 15 (73+i) = true := by decide +kernel

theorem strictBool_r15_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (74+i)) 15 (74+i) = true := by decide +kernel

theorem strictBool_r15_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (75+i)) 15 (75+i) = true := by decide +kernel

theorem strictBool_r15_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (76+i)) 15 (76+i) = true := by decide +kernel

theorem strictBool_r15_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (77+i)) 15 (77+i) = true := by decide +kernel

theorem strictBool_r15_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (78+i)) 15 (78+i) = true := by decide +kernel

theorem strictBool_r15_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (79+i)) 15 (79+i) = true := by decide +kernel

theorem strictBool_r15_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (80+i)) 15 (80+i) = true := by decide +kernel

theorem strictBool_r15_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (81+i)) 15 (81+i) = true := by decide +kernel

theorem strictBool_r15_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (82+i)) 15 (82+i) = true := by decide +kernel

theorem strictBool_r15_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (83+i)) 15 (83+i) = true := by decide +kernel

theorem strictBool_r15_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (84+i)) 15 (84+i) = true := by decide +kernel

theorem strictBool_r15_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (85+i)) 15 (85+i) = true := by decide +kernel

theorem strictBool_r15_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (86+i)) 15 (86+i) = true := by decide +kernel

theorem strictBool_r15_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (87+i)) 15 (87+i) = true := by decide +kernel

theorem strictBool_r15_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (88+i)) 15 (88+i) = true := by decide +kernel

theorem strictBool_r15_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (89+i)) 15 (89+i) = true := by decide +kernel

theorem strictBool_r15_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (90+i)) 15 (90+i) = true := by decide +kernel

theorem strictBool_r15_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (91+i)) 15 (91+i) = true := by decide +kernel

theorem strictBool_r15_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (92+i)) 15 (92+i) = true := by decide +kernel

theorem strictBool_r15_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (93+i)) 15 (93+i) = true := by decide +kernel

theorem strictBool_r15_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (94+i)) 15 (94+i) = true := by decide +kernel

theorem strictBool_r15_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (95+i)) 15 (95+i) = true := by decide +kernel

theorem strictBool_r15_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (96+i)) 15 (96+i) = true := by decide +kernel

theorem strictBool_r15_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (97+i)) 15 (97+i) = true := by decide +kernel

theorem strictBool_r15_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (98+i)) 15 (98+i) = true := by decide +kernel

theorem strictBool_r15_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (99+i)) 15 (99+i) = true := by decide +kernel

theorem strictBool_r15_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (100+i)) 15 (100+i) = true := by decide +kernel

theorem strictBool_r15_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (101+i)) 15 (101+i) = true := by decide +kernel

theorem strictBool_r15_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (102+i)) 15 (102+i) = true := by decide +kernel

theorem strictBool_r15_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (103+i)) 15 (103+i) = true := by decide +kernel

theorem strictBool_r15_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (104+i)) 15 (104+i) = true := by decide +kernel

theorem strictBool_r15_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (105+i)) 15 (105+i) = true := by decide +kernel

theorem strictBool_r15_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (106+i)) 15 (106+i) = true := by decide +kernel

theorem strictBool_r15_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (107+i)) 15 (107+i) = true := by decide +kernel

theorem strictBool_r15_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (108+i)) 15 (108+i) = true := by decide +kernel

theorem strictBool_r15_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (109+i)) 15 (109+i) = true := by decide +kernel

theorem strictBool_r15_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (110+i)) 15 (110+i) = true := by decide +kernel

theorem strictBool_r15_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (111+i)) 15 (111+i) = true := by decide +kernel

theorem strictBool_r15_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (112+i)) 15 (112+i) = true := by decide +kernel

theorem strictBool_r15_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (113+i)) 15 (113+i) = true := by decide +kernel

theorem strictBool_r15_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (114+i)) 15 (114+i) = true := by decide +kernel

theorem strictBool_r15_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (115+i)) 15 (115+i) = true := by decide +kernel

theorem strictBool_r15_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (116+i)) 15 (116+i) = true := by decide +kernel

theorem strictBool_r15_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (117+i)) 15 (117+i) = true := by decide +kernel

theorem strictBool_r15_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (118+i)) 15 (118+i) = true := by decide +kernel

theorem strictBool_r15_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (119+i)) 15 (119+i) = true := by decide +kernel

theorem strictBool_r15_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (120+i)) 15 (120+i) = true := by decide +kernel

theorem strictBool_r15_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (121+i)) 15 (121+i) = true := by decide +kernel

theorem strictBool_r15_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (122+i)) 15 (122+i) = true := by decide +kernel

theorem strictBool_r15_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (123+i)) 15 (123+i) = true := by decide +kernel

theorem strictBool_r15_part124 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (124+i)) 15 (124+i) = true := by decide +kernel

theorem strictBool_r15_part125 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (125+i)) 15 (125+i) = true := by decide +kernel

theorem strictBool_r15_part126 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (126+i)) 15 (126+i) = true := by decide +kernel

theorem strictBool_r15_part127 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 15 (127+i)) 15 (127+i) = true := by decide +kernel

theorem strictBool_r15 (V : ℕ) (hV : V ∈ List.range 128) : strictBool (BoundaryTailBaseFastData.row 15 V) 15 V = true := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have hi := strictBool_r15_part0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
            · by_cases h2_4 : V < 3
              · have hi := strictBool_r15_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have hi := strictBool_r15_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
            · by_cases h6_8 : V < 7
              · have hi := strictBool_r15_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r15_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r15_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r15_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
            · by_cases h14_16 : V < 15
              · have hi := strictBool_r15_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r15_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r15_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r15_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r15_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r15_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r15_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r15_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r15_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r15_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r15_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r15_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r15_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r15_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r15_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r15_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r15_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r15_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r15_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r15_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r15_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
        · by_cases h56_64 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r15_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r15_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r15_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
            · by_cases h62_64 : V < 63
              · have hi := strictBool_r15_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · by_cases h64_72 : V < 68
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r15_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r15_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r15_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r15_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
        · by_cases h72_80 : V < 76
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have hi := strictBool_r15_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
            · by_cases h74_76 : V < 75
              · have hi := strictBool_r15_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r15_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r15_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · by_cases h80_88 : V < 84
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r15_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r15_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r15_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r15_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
        · by_cases h88_96 : V < 92
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r15_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r15_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r15_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r15_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · by_cases h96_104 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r15_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r15_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r15_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r15_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r15_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r15_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r15_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r15_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · by_cases h112_120 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r15_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r15_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r15_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r15_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
        · by_cases h120_128 : V < 124
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r15_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r15_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi
          · by_cases h124_128 : V < 126
            · by_cases h124_126 : V < 125
              · have hi := strictBool_r15_part124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using hi
            · by_cases h126_128 : V < 127
              · have hi := strictBool_r15_part126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using hi
              · have hi := strictBool_r15_part127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using hi

theorem strictFast_r15 (V : ℕ) (hV : V ∈ List.range 128) : StrictAtFast (BoundaryTailBaseFastData.row 15 V) 15 V :=
  strictBool_sound _ _ _ (strictBool_r15 V hV)

theorem strict_r15 (V : ℕ) (hV : V ∈ List.range 128) : StrictCheckAt 15 V :=
  strictAtFast_sound _ _ _ (valid_r15 V hV) (strictFast_r15 V hV)

theorem zeroCertificate_r15_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (0+i)) 15 (0+i) := by decide +kernel

theorem zeroCertificate_r15_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (8+i)) 15 (8+i) := by decide +kernel

theorem zeroCertificate_r15_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (16+i)) 15 (16+i) := by decide +kernel

theorem zeroCertificate_r15_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (24+i)) 15 (24+i) := by decide +kernel

theorem zeroCertificate_r15_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (32+i)) 15 (32+i) := by decide +kernel

theorem zeroCertificate_r15_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (40+i)) 15 (40+i) := by decide +kernel

theorem zeroCertificate_r15_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (48+i)) 15 (48+i) := by decide +kernel

theorem zeroCertificate_r15_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (56+i)) 15 (56+i) := by decide +kernel

theorem zeroCertificate_r15_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (64+i)) 15 (64+i) := by decide +kernel

theorem zeroCertificate_r15_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (72+i)) 15 (72+i) := by decide +kernel

theorem zeroCertificate_r15_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (80+i)) 15 (80+i) := by decide +kernel

theorem zeroCertificate_r15_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (88+i)) 15 (88+i) := by decide +kernel

theorem zeroCertificate_r15_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (96+i)) 15 (96+i) := by decide +kernel

theorem zeroCertificate_r15_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (104+i)) 15 (104+i) := by decide +kernel

theorem zeroCertificate_r15_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (112+i)) 15 (112+i) := by decide +kernel

theorem zeroCertificate_r15_part120 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 15 (120+i)) 15 (120+i) := by decide +kernel

theorem zeroCertificate_r15 (V : ℕ) (hV : V ∈ List.range 128) : ZeroCertificate (BoundaryTailBaseFastData.row 15 V) 15 V := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := zeroCertificate_r15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r15 (V : ℕ) (hV : V ∈ List.range 128) : ZeroAtFast 15 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r15 V hV) (zeroCertificate_r15 V hV)

theorem zero_r15 (V : ℕ) (hV : V ∈ List.range 128) : ZeroCheckAt 15 V :=
  zeroAtFast_sound _ _ (zeroFast_r15 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r19_part0 : ∀ i ∈ List.range 8, CorrectAt 19 (0+i) := by decide +kernel

theorem correct_r19_part8 : ∀ i ∈ List.range 8, CorrectAt 19 (8+i) := by decide +kernel

theorem correct_r19_part16 : ∀ i ∈ List.range 8, CorrectAt 19 (16+i) := by decide +kernel

theorem correct_r19_part24 : ∀ i ∈ List.range 8, CorrectAt 19 (24+i) := by decide +kernel

theorem correct_r19_part32 : ∀ i ∈ List.range 8, CorrectAt 19 (32+i) := by decide +kernel

theorem correct_r19_part40 : ∀ i ∈ List.range 8, CorrectAt 19 (40+i) := by decide +kernel

theorem correct_r19_part48 : ∀ i ∈ List.range 8, CorrectAt 19 (48+i) := by decide +kernel

theorem correct_r19_part56 : ∀ i ∈ List.range 8, CorrectAt 19 (56+i) := by decide +kernel

theorem correct_r19_part64 : ∀ i ∈ List.range 8, CorrectAt 19 (64+i) := by decide +kernel

theorem correct_r19_part72 : ∀ i ∈ List.range 8, CorrectAt 19 (72+i) := by decide +kernel

theorem correct_r19_part80 : ∀ i ∈ List.range 8, CorrectAt 19 (80+i) := by decide +kernel

theorem correct_r19_part88 : ∀ i ∈ List.range 8, CorrectAt 19 (88+i) := by decide +kernel

theorem correct_r19_part96 : ∀ i ∈ List.range 8, CorrectAt 19 (96+i) := by decide +kernel

theorem correct_r19_part104 : ∀ i ∈ List.range 8, CorrectAt 19 (104+i) := by decide +kernel

theorem correct_r19_part112 : ∀ i ∈ List.range 8, CorrectAt 19 (112+i) := by decide +kernel

theorem correct_r19_part120 : ∀ i ∈ List.range 4, CorrectAt 19 (120+i) := by decide +kernel

theorem correct_r19 (V : ℕ) (hV : V ∈ List.range 124) : CorrectAt 19 V := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := correct_r19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := correct_r19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := correct_r19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := correct_r19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := correct_r19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := correct_r19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := correct_r19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := correct_r19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := correct_r19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := correct_r19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := correct_r19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := correct_r19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := correct_r19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem base_r19_part0 : ∀ i ∈ List.range 8, BaseCheckAt 19 (0+i) := by decide +kernel

theorem base_r19_part8 : ∀ i ∈ List.range 8, BaseCheckAt 19 (8+i) := by decide +kernel

theorem base_r19_part16 : ∀ i ∈ List.range 8, BaseCheckAt 19 (16+i) := by decide +kernel

theorem base_r19_part24 : ∀ i ∈ List.range 8, BaseCheckAt 19 (24+i) := by decide +kernel

theorem base_r19_part32 : ∀ i ∈ List.range 8, BaseCheckAt 19 (32+i) := by decide +kernel

theorem base_r19_part40 : ∀ i ∈ List.range 8, BaseCheckAt 19 (40+i) := by decide +kernel

theorem base_r19_part48 : ∀ i ∈ List.range 8, BaseCheckAt 19 (48+i) := by decide +kernel

theorem base_r19_part56 : ∀ i ∈ List.range 8, BaseCheckAt 19 (56+i) := by decide +kernel

theorem base_r19_part64 : ∀ i ∈ List.range 8, BaseCheckAt 19 (64+i) := by decide +kernel

theorem base_r19_part72 : ∀ i ∈ List.range 8, BaseCheckAt 19 (72+i) := by decide +kernel

theorem base_r19_part80 : ∀ i ∈ List.range 8, BaseCheckAt 19 (80+i) := by decide +kernel

theorem base_r19_part88 : ∀ i ∈ List.range 8, BaseCheckAt 19 (88+i) := by decide +kernel

theorem base_r19_part96 : ∀ i ∈ List.range 8, BaseCheckAt 19 (96+i) := by decide +kernel

theorem base_r19_part104 : ∀ i ∈ List.range 8, BaseCheckAt 19 (104+i) := by decide +kernel

theorem base_r19_part112 : ∀ i ∈ List.range 8, BaseCheckAt 19 (112+i) := by decide +kernel

theorem base_r19_part120 : ∀ i ∈ List.range 4, BaseCheckAt 19 (120+i) := by decide +kernel

theorem base_r19 (V : ℕ) (hV : V ∈ List.range 124) : BaseCheckAt 19 V := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := base_r19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := base_r19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := base_r19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := base_r19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := base_r19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := base_r19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := base_r19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := base_r19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := base_r19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := base_r19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := base_r19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := base_r19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := base_r19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem valid_r19_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (0+i)) 19 (0+i) := by decide +kernel

theorem valid_r19_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (8+i)) 19 (8+i) := by decide +kernel

theorem valid_r19_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (16+i)) 19 (16+i) := by decide +kernel

theorem valid_r19_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (24+i)) 19 (24+i) := by decide +kernel

theorem valid_r19_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (32+i)) 19 (32+i) := by decide +kernel

theorem valid_r19_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (40+i)) 19 (40+i) := by decide +kernel

theorem valid_r19_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (48+i)) 19 (48+i) := by decide +kernel

theorem valid_r19_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (56+i)) 19 (56+i) := by decide +kernel

theorem valid_r19_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (64+i)) 19 (64+i) := by decide +kernel

theorem valid_r19_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (72+i)) 19 (72+i) := by decide +kernel

theorem valid_r19_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (80+i)) 19 (80+i) := by decide +kernel

theorem valid_r19_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (88+i)) 19 (88+i) := by decide +kernel

theorem valid_r19_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (96+i)) 19 (96+i) := by decide +kernel

theorem valid_r19_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (104+i)) 19 (104+i) := by decide +kernel

theorem valid_r19_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 19 (112+i)) 19 (112+i) := by decide +kernel

theorem valid_r19_part120 : ∀ i ∈ List.range 4, Valid (BoundaryTailBaseFastData.row 19 (120+i)) 19 (120+i) := by decide +kernel

theorem valid_r19 (V : ℕ) (hV : V ∈ List.range 124) : Valid (BoundaryTailBaseFastData.row 19 V) 19 V := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := valid_r19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := valid_r19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := valid_r19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := valid_r19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := valid_r19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := valid_r19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := valid_r19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := valid_r19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := valid_r19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := valid_r19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := valid_r19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := valid_r19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := valid_r19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem strictBool_r19_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (0+i)) 19 (0+i) = true := by decide +kernel

theorem strictBool_r19_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (1+i)) 19 (1+i) = true := by decide +kernel

theorem strictBool_r19_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (2+i)) 19 (2+i) = true := by decide +kernel

theorem strictBool_r19_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (3+i)) 19 (3+i) = true := by decide +kernel

theorem strictBool_r19_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (4+i)) 19 (4+i) = true := by decide +kernel

theorem strictBool_r19_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (5+i)) 19 (5+i) = true := by decide +kernel

theorem strictBool_r19_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (6+i)) 19 (6+i) = true := by decide +kernel

theorem strictBool_r19_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (7+i)) 19 (7+i) = true := by decide +kernel

theorem strictBool_r19_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (8+i)) 19 (8+i) = true := by decide +kernel

theorem strictBool_r19_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (9+i)) 19 (9+i) = true := by decide +kernel

theorem strictBool_r19_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (10+i)) 19 (10+i) = true := by decide +kernel

theorem strictBool_r19_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (11+i)) 19 (11+i) = true := by decide +kernel

theorem strictBool_r19_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (12+i)) 19 (12+i) = true := by decide +kernel

theorem strictBool_r19_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (13+i)) 19 (13+i) = true := by decide +kernel

theorem strictBool_r19_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (14+i)) 19 (14+i) = true := by decide +kernel

theorem strictBool_r19_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (15+i)) 19 (15+i) = true := by decide +kernel

theorem strictBool_r19_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (16+i)) 19 (16+i) = true := by decide +kernel

theorem strictBool_r19_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (17+i)) 19 (17+i) = true := by decide +kernel

theorem strictBool_r19_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (18+i)) 19 (18+i) = true := by decide +kernel

theorem strictBool_r19_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (19+i)) 19 (19+i) = true := by decide +kernel

theorem strictBool_r19_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (20+i)) 19 (20+i) = true := by decide +kernel

theorem strictBool_r19_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (21+i)) 19 (21+i) = true := by decide +kernel

theorem strictBool_r19_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (22+i)) 19 (22+i) = true := by decide +kernel

theorem strictBool_r19_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (23+i)) 19 (23+i) = true := by decide +kernel

theorem strictBool_r19_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (24+i)) 19 (24+i) = true := by decide +kernel

theorem strictBool_r19_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (25+i)) 19 (25+i) = true := by decide +kernel

theorem strictBool_r19_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (26+i)) 19 (26+i) = true := by decide +kernel

theorem strictBool_r19_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (27+i)) 19 (27+i) = true := by decide +kernel

theorem strictBool_r19_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (28+i)) 19 (28+i) = true := by decide +kernel

theorem strictBool_r19_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (29+i)) 19 (29+i) = true := by decide +kernel

theorem strictBool_r19_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (30+i)) 19 (30+i) = true := by decide +kernel

theorem strictBool_r19_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (31+i)) 19 (31+i) = true := by decide +kernel

theorem strictBool_r19_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (32+i)) 19 (32+i) = true := by decide +kernel

theorem strictBool_r19_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (33+i)) 19 (33+i) = true := by decide +kernel

theorem strictBool_r19_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (34+i)) 19 (34+i) = true := by decide +kernel

theorem strictBool_r19_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (35+i)) 19 (35+i) = true := by decide +kernel

theorem strictBool_r19_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (36+i)) 19 (36+i) = true := by decide +kernel

theorem strictBool_r19_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (37+i)) 19 (37+i) = true := by decide +kernel

theorem strictBool_r19_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (38+i)) 19 (38+i) = true := by decide +kernel

theorem strictBool_r19_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (39+i)) 19 (39+i) = true := by decide +kernel

theorem strictBool_r19_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (40+i)) 19 (40+i) = true := by decide +kernel

theorem strictBool_r19_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (41+i)) 19 (41+i) = true := by decide +kernel

theorem strictBool_r19_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (42+i)) 19 (42+i) = true := by decide +kernel

theorem strictBool_r19_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (43+i)) 19 (43+i) = true := by decide +kernel

theorem strictBool_r19_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (44+i)) 19 (44+i) = true := by decide +kernel

theorem strictBool_r19_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (45+i)) 19 (45+i) = true := by decide +kernel

theorem strictBool_r19_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (46+i)) 19 (46+i) = true := by decide +kernel

theorem strictBool_r19_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (47+i)) 19 (47+i) = true := by decide +kernel

theorem strictBool_r19_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (48+i)) 19 (48+i) = true := by decide +kernel

theorem strictBool_r19_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (49+i)) 19 (49+i) = true := by decide +kernel

theorem strictBool_r19_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (50+i)) 19 (50+i) = true := by decide +kernel

theorem strictBool_r19_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (51+i)) 19 (51+i) = true := by decide +kernel

theorem strictBool_r19_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (52+i)) 19 (52+i) = true := by decide +kernel

theorem strictBool_r19_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (53+i)) 19 (53+i) = true := by decide +kernel

theorem strictBool_r19_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (54+i)) 19 (54+i) = true := by decide +kernel

theorem strictBool_r19_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (55+i)) 19 (55+i) = true := by decide +kernel

theorem strictBool_r19_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (56+i)) 19 (56+i) = true := by decide +kernel

theorem strictBool_r19_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (57+i)) 19 (57+i) = true := by decide +kernel

theorem strictBool_r19_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (58+i)) 19 (58+i) = true := by decide +kernel

theorem strictBool_r19_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (59+i)) 19 (59+i) = true := by decide +kernel

theorem strictBool_r19_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (60+i)) 19 (60+i) = true := by decide +kernel

theorem strictBool_r19_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (61+i)) 19 (61+i) = true := by decide +kernel

theorem strictBool_r19_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (62+i)) 19 (62+i) = true := by decide +kernel

theorem strictBool_r19_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (63+i)) 19 (63+i) = true := by decide +kernel

theorem strictBool_r19_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (64+i)) 19 (64+i) = true := by decide +kernel

theorem strictBool_r19_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (65+i)) 19 (65+i) = true := by decide +kernel

theorem strictBool_r19_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (66+i)) 19 (66+i) = true := by decide +kernel

theorem strictBool_r19_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (67+i)) 19 (67+i) = true := by decide +kernel

theorem strictBool_r19_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (68+i)) 19 (68+i) = true := by decide +kernel

theorem strictBool_r19_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (69+i)) 19 (69+i) = true := by decide +kernel

theorem strictBool_r19_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (70+i)) 19 (70+i) = true := by decide +kernel

theorem strictBool_r19_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (71+i)) 19 (71+i) = true := by decide +kernel

theorem strictBool_r19_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (72+i)) 19 (72+i) = true := by decide +kernel

theorem strictBool_r19_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (73+i)) 19 (73+i) = true := by decide +kernel

theorem strictBool_r19_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (74+i)) 19 (74+i) = true := by decide +kernel

theorem strictBool_r19_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (75+i)) 19 (75+i) = true := by decide +kernel

theorem strictBool_r19_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (76+i)) 19 (76+i) = true := by decide +kernel

theorem strictBool_r19_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (77+i)) 19 (77+i) = true := by decide +kernel

theorem strictBool_r19_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (78+i)) 19 (78+i) = true := by decide +kernel

theorem strictBool_r19_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (79+i)) 19 (79+i) = true := by decide +kernel

theorem strictBool_r19_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (80+i)) 19 (80+i) = true := by decide +kernel

theorem strictBool_r19_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (81+i)) 19 (81+i) = true := by decide +kernel

theorem strictBool_r19_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (82+i)) 19 (82+i) = true := by decide +kernel

theorem strictBool_r19_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (83+i)) 19 (83+i) = true := by decide +kernel

theorem strictBool_r19_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (84+i)) 19 (84+i) = true := by decide +kernel

theorem strictBool_r19_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (85+i)) 19 (85+i) = true := by decide +kernel

theorem strictBool_r19_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (86+i)) 19 (86+i) = true := by decide +kernel

theorem strictBool_r19_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (87+i)) 19 (87+i) = true := by decide +kernel

theorem strictBool_r19_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (88+i)) 19 (88+i) = true := by decide +kernel

theorem strictBool_r19_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (89+i)) 19 (89+i) = true := by decide +kernel

theorem strictBool_r19_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (90+i)) 19 (90+i) = true := by decide +kernel

theorem strictBool_r19_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (91+i)) 19 (91+i) = true := by decide +kernel

theorem strictBool_r19_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (92+i)) 19 (92+i) = true := by decide +kernel

theorem strictBool_r19_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (93+i)) 19 (93+i) = true := by decide +kernel

theorem strictBool_r19_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (94+i)) 19 (94+i) = true := by decide +kernel

theorem strictBool_r19_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (95+i)) 19 (95+i) = true := by decide +kernel

theorem strictBool_r19_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (96+i)) 19 (96+i) = true := by decide +kernel

theorem strictBool_r19_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (97+i)) 19 (97+i) = true := by decide +kernel

theorem strictBool_r19_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (98+i)) 19 (98+i) = true := by decide +kernel

theorem strictBool_r19_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (99+i)) 19 (99+i) = true := by decide +kernel

theorem strictBool_r19_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (100+i)) 19 (100+i) = true := by decide +kernel

theorem strictBool_r19_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (101+i)) 19 (101+i) = true := by decide +kernel

theorem strictBool_r19_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (102+i)) 19 (102+i) = true := by decide +kernel

theorem strictBool_r19_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (103+i)) 19 (103+i) = true := by decide +kernel

theorem strictBool_r19_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (104+i)) 19 (104+i) = true := by decide +kernel

theorem strictBool_r19_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (105+i)) 19 (105+i) = true := by decide +kernel

theorem strictBool_r19_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (106+i)) 19 (106+i) = true := by decide +kernel

theorem strictBool_r19_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (107+i)) 19 (107+i) = true := by decide +kernel

theorem strictBool_r19_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (108+i)) 19 (108+i) = true := by decide +kernel

theorem strictBool_r19_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (109+i)) 19 (109+i) = true := by decide +kernel

theorem strictBool_r19_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (110+i)) 19 (110+i) = true := by decide +kernel

theorem strictBool_r19_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (111+i)) 19 (111+i) = true := by decide +kernel

theorem strictBool_r19_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (112+i)) 19 (112+i) = true := by decide +kernel

theorem strictBool_r19_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (113+i)) 19 (113+i) = true := by decide +kernel

theorem strictBool_r19_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (114+i)) 19 (114+i) = true := by decide +kernel

theorem strictBool_r19_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (115+i)) 19 (115+i) = true := by decide +kernel

theorem strictBool_r19_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (116+i)) 19 (116+i) = true := by decide +kernel

theorem strictBool_r19_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (117+i)) 19 (117+i) = true := by decide +kernel

theorem strictBool_r19_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (118+i)) 19 (118+i) = true := by decide +kernel

theorem strictBool_r19_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (119+i)) 19 (119+i) = true := by decide +kernel

theorem strictBool_r19_part120 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (120+i)) 19 (120+i) = true := by decide +kernel

theorem strictBool_r19_part121 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (121+i)) 19 (121+i) = true := by decide +kernel

theorem strictBool_r19_part122 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (122+i)) 19 (122+i) = true := by decide +kernel

theorem strictBool_r19_part123 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 19 (123+i)) 19 (123+i) = true := by decide +kernel

theorem strictBool_r19 (V : ℕ) (hV : V ∈ List.range 124) : strictBool (BoundaryTailBaseFastData.row 19 V) 19 V = true := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 62
  · by_cases h0_62 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r19_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r19_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r19_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r19_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r19_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r19_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r19_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r19_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r19_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r19_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r19_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r19_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r19_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r19_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r19_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r19_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
    · by_cases h31_62 : V < 46
      · by_cases h31_46 : V < 38
        · by_cases h31_38 : V < 34
          · by_cases h31_34 : V < 32
            · have hi := strictBool_r19_part31 (V-31) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r19_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r19_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r19_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
        · by_cases h38_46 : V < 42
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r19_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r19_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have hi := strictBool_r19_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r19_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
      · by_cases h46_62 : V < 54
        · by_cases h46_54 : V < 50
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r19_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r19_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r19_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r19_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
        · by_cases h54_62 : V < 58
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r19_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r19_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r19_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
            · by_cases h60_62 : V < 61
              · have hi := strictBool_r19_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
  · by_cases h62_124 : V < 93
    · by_cases h62_93 : V < 77
      · by_cases h62_77 : V < 69
        · by_cases h62_69 : V < 65
          · by_cases h62_65 : V < 63
            · have hi := strictBool_r19_part62 (V-62) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r19_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r19_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r19_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r19_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r19_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r19_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r19_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
      · by_cases h77_93 : V < 85
        · by_cases h77_85 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r19_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r19_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r19_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r19_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r19_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r19_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r19_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r19_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
    · by_cases h93_124 : V < 108
      · by_cases h93_108 : V < 100
        · by_cases h93_100 : V < 96
          · by_cases h93_96 : V < 94
            · have hi := strictBool_r19_part93 (V-93) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r19_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r19_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
            · by_cases h98_100 : V < 99
              · have hi := strictBool_r19_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
        · by_cases h100_108 : V < 104
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have hi := strictBool_r19_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r19_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r19_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r19_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
      · by_cases h108_124 : V < 116
        · by_cases h108_116 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r19_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r19_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r19_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r19_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
        · by_cases h116_124 : V < 120
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r19_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r19_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have hi := strictBool_r19_part120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using hi
            · by_cases h122_124 : V < 123
              · have hi := strictBool_r19_part122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using hi
              · have hi := strictBool_r19_part123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using hi

theorem strictFast_r19 (V : ℕ) (hV : V ∈ List.range 124) : StrictAtFast (BoundaryTailBaseFastData.row 19 V) 19 V :=
  strictBool_sound _ _ _ (strictBool_r19 V hV)

theorem strict_r19 (V : ℕ) (hV : V ∈ List.range 124) : StrictCheckAt 19 V :=
  strictAtFast_sound _ _ _ (valid_r19 V hV) (strictFast_r19 V hV)

theorem zeroCertificate_r19_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (0+i)) 19 (0+i) := by decide +kernel

theorem zeroCertificate_r19_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (8+i)) 19 (8+i) := by decide +kernel

theorem zeroCertificate_r19_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (16+i)) 19 (16+i) := by decide +kernel

theorem zeroCertificate_r19_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (24+i)) 19 (24+i) := by decide +kernel

theorem zeroCertificate_r19_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (32+i)) 19 (32+i) := by decide +kernel

theorem zeroCertificate_r19_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (40+i)) 19 (40+i) := by decide +kernel

theorem zeroCertificate_r19_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (48+i)) 19 (48+i) := by decide +kernel

theorem zeroCertificate_r19_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (56+i)) 19 (56+i) := by decide +kernel

theorem zeroCertificate_r19_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (64+i)) 19 (64+i) := by decide +kernel

theorem zeroCertificate_r19_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (72+i)) 19 (72+i) := by decide +kernel

theorem zeroCertificate_r19_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (80+i)) 19 (80+i) := by decide +kernel

theorem zeroCertificate_r19_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (88+i)) 19 (88+i) := by decide +kernel

theorem zeroCertificate_r19_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (96+i)) 19 (96+i) := by decide +kernel

theorem zeroCertificate_r19_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (104+i)) 19 (104+i) := by decide +kernel

theorem zeroCertificate_r19_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 19 (112+i)) 19 (112+i) := by decide +kernel

theorem zeroCertificate_r19_part120 : ∀ i ∈ List.range 4, ZeroCertificate (BoundaryTailBaseFastData.row 19 (120+i)) 19 (120+i) := by decide +kernel

theorem zeroCertificate_r19 (V : ℕ) (hV : V ∈ List.range 124) : ZeroCertificate (BoundaryTailBaseFastData.row 19 V) 19 V := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := zeroCertificate_r19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := zeroCertificate_r19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := zeroCertificate_r19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := zeroCertificate_r19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := zeroCertificate_r19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi

theorem zeroFast_r19 (V : ℕ) (hV : V ∈ List.range 124) : ZeroAtFast 19 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r19 V hV) (zeroCertificate_r19 V hV)

theorem zero_r19 (V : ℕ) (hV : V ∈ List.range 124) : ZeroCheckAt 19 V :=
  zeroAtFast_sound _ _ (zeroFast_r19 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r23_part0 : ∀ i ∈ List.range 8, CorrectAt 23 (0+i) := by decide +kernel

theorem correct_r23_part8 : ∀ i ∈ List.range 8, CorrectAt 23 (8+i) := by decide +kernel

theorem correct_r23_part16 : ∀ i ∈ List.range 8, CorrectAt 23 (16+i) := by decide +kernel

theorem correct_r23_part24 : ∀ i ∈ List.range 8, CorrectAt 23 (24+i) := by decide +kernel

theorem correct_r23_part32 : ∀ i ∈ List.range 8, CorrectAt 23 (32+i) := by decide +kernel

theorem correct_r23_part40 : ∀ i ∈ List.range 8, CorrectAt 23 (40+i) := by decide +kernel

theorem correct_r23_part48 : ∀ i ∈ List.range 8, CorrectAt 23 (48+i) := by decide +kernel

theorem correct_r23_part56 : ∀ i ∈ List.range 8, CorrectAt 23 (56+i) := by decide +kernel

theorem correct_r23_part64 : ∀ i ∈ List.range 8, CorrectAt 23 (64+i) := by decide +kernel

theorem correct_r23_part72 : ∀ i ∈ List.range 8, CorrectAt 23 (72+i) := by decide +kernel

theorem correct_r23_part80 : ∀ i ∈ List.range 8, CorrectAt 23 (80+i) := by decide +kernel

theorem correct_r23_part88 : ∀ i ∈ List.range 8, CorrectAt 23 (88+i) := by decide +kernel

theorem correct_r23_part96 : ∀ i ∈ List.range 8, CorrectAt 23 (96+i) := by decide +kernel

theorem correct_r23_part104 : ∀ i ∈ List.range 8, CorrectAt 23 (104+i) := by decide +kernel

theorem correct_r23_part112 : ∀ i ∈ List.range 8, CorrectAt 23 (112+i) := by decide +kernel

theorem correct_r23 (V : ℕ) (hV : V ∈ List.range 120) : CorrectAt 23 V := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := correct_r23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r23_part0 : ∀ i ∈ List.range 8, BaseCheckAt 23 (0+i) := by decide +kernel

theorem base_r23_part8 : ∀ i ∈ List.range 8, BaseCheckAt 23 (8+i) := by decide +kernel

theorem base_r23_part16 : ∀ i ∈ List.range 8, BaseCheckAt 23 (16+i) := by decide +kernel

theorem base_r23_part24 : ∀ i ∈ List.range 8, BaseCheckAt 23 (24+i) := by decide +kernel

theorem base_r23_part32 : ∀ i ∈ List.range 8, BaseCheckAt 23 (32+i) := by decide +kernel

theorem base_r23_part40 : ∀ i ∈ List.range 8, BaseCheckAt 23 (40+i) := by decide +kernel

theorem base_r23_part48 : ∀ i ∈ List.range 8, BaseCheckAt 23 (48+i) := by decide +kernel

theorem base_r23_part56 : ∀ i ∈ List.range 8, BaseCheckAt 23 (56+i) := by decide +kernel

theorem base_r23_part64 : ∀ i ∈ List.range 8, BaseCheckAt 23 (64+i) := by decide +kernel

theorem base_r23_part72 : ∀ i ∈ List.range 8, BaseCheckAt 23 (72+i) := by decide +kernel

theorem base_r23_part80 : ∀ i ∈ List.range 8, BaseCheckAt 23 (80+i) := by decide +kernel

theorem base_r23_part88 : ∀ i ∈ List.range 8, BaseCheckAt 23 (88+i) := by decide +kernel

theorem base_r23_part96 : ∀ i ∈ List.range 8, BaseCheckAt 23 (96+i) := by decide +kernel

theorem base_r23_part104 : ∀ i ∈ List.range 8, BaseCheckAt 23 (104+i) := by decide +kernel

theorem base_r23_part112 : ∀ i ∈ List.range 8, BaseCheckAt 23 (112+i) := by decide +kernel

theorem base_r23 (V : ℕ) (hV : V ∈ List.range 120) : BaseCheckAt 23 V := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := base_r23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r23_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (0+i)) 23 (0+i) := by decide +kernel

theorem valid_r23_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (8+i)) 23 (8+i) := by decide +kernel

theorem valid_r23_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (16+i)) 23 (16+i) := by decide +kernel

theorem valid_r23_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (24+i)) 23 (24+i) := by decide +kernel

theorem valid_r23_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (32+i)) 23 (32+i) := by decide +kernel

theorem valid_r23_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (40+i)) 23 (40+i) := by decide +kernel

theorem valid_r23_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (48+i)) 23 (48+i) := by decide +kernel

theorem valid_r23_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (56+i)) 23 (56+i) := by decide +kernel

theorem valid_r23_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (64+i)) 23 (64+i) := by decide +kernel

theorem valid_r23_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (72+i)) 23 (72+i) := by decide +kernel

theorem valid_r23_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (80+i)) 23 (80+i) := by decide +kernel

theorem valid_r23_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (88+i)) 23 (88+i) := by decide +kernel

theorem valid_r23_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (96+i)) 23 (96+i) := by decide +kernel

theorem valid_r23_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (104+i)) 23 (104+i) := by decide +kernel

theorem valid_r23_part112 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 23 (112+i)) 23 (112+i) := by decide +kernel

theorem valid_r23 (V : ℕ) (hV : V ∈ List.range 120) : Valid (BoundaryTailBaseFastData.row 23 V) 23 V := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := valid_r23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r23_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (0+i)) 23 (0+i) = true := by decide +kernel

theorem strictBool_r23_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (1+i)) 23 (1+i) = true := by decide +kernel

theorem strictBool_r23_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (2+i)) 23 (2+i) = true := by decide +kernel

theorem strictBool_r23_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (3+i)) 23 (3+i) = true := by decide +kernel

theorem strictBool_r23_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (4+i)) 23 (4+i) = true := by decide +kernel

theorem strictBool_r23_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (5+i)) 23 (5+i) = true := by decide +kernel

theorem strictBool_r23_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (6+i)) 23 (6+i) = true := by decide +kernel

theorem strictBool_r23_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (7+i)) 23 (7+i) = true := by decide +kernel

theorem strictBool_r23_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (8+i)) 23 (8+i) = true := by decide +kernel

theorem strictBool_r23_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (9+i)) 23 (9+i) = true := by decide +kernel

theorem strictBool_r23_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (10+i)) 23 (10+i) = true := by decide +kernel

theorem strictBool_r23_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (11+i)) 23 (11+i) = true := by decide +kernel

theorem strictBool_r23_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (12+i)) 23 (12+i) = true := by decide +kernel

theorem strictBool_r23_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (13+i)) 23 (13+i) = true := by decide +kernel

theorem strictBool_r23_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (14+i)) 23 (14+i) = true := by decide +kernel

theorem strictBool_r23_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (15+i)) 23 (15+i) = true := by decide +kernel

theorem strictBool_r23_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (16+i)) 23 (16+i) = true := by decide +kernel

theorem strictBool_r23_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (17+i)) 23 (17+i) = true := by decide +kernel

theorem strictBool_r23_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (18+i)) 23 (18+i) = true := by decide +kernel

theorem strictBool_r23_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (19+i)) 23 (19+i) = true := by decide +kernel

theorem strictBool_r23_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (20+i)) 23 (20+i) = true := by decide +kernel

theorem strictBool_r23_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (21+i)) 23 (21+i) = true := by decide +kernel

theorem strictBool_r23_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (22+i)) 23 (22+i) = true := by decide +kernel

theorem strictBool_r23_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (23+i)) 23 (23+i) = true := by decide +kernel

theorem strictBool_r23_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (24+i)) 23 (24+i) = true := by decide +kernel

theorem strictBool_r23_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (25+i)) 23 (25+i) = true := by decide +kernel

theorem strictBool_r23_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (26+i)) 23 (26+i) = true := by decide +kernel

theorem strictBool_r23_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (27+i)) 23 (27+i) = true := by decide +kernel

theorem strictBool_r23_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (28+i)) 23 (28+i) = true := by decide +kernel

theorem strictBool_r23_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (29+i)) 23 (29+i) = true := by decide +kernel

theorem strictBool_r23_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (30+i)) 23 (30+i) = true := by decide +kernel

theorem strictBool_r23_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (31+i)) 23 (31+i) = true := by decide +kernel

theorem strictBool_r23_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (32+i)) 23 (32+i) = true := by decide +kernel

theorem strictBool_r23_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (33+i)) 23 (33+i) = true := by decide +kernel

theorem strictBool_r23_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (34+i)) 23 (34+i) = true := by decide +kernel

theorem strictBool_r23_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (35+i)) 23 (35+i) = true := by decide +kernel

theorem strictBool_r23_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (36+i)) 23 (36+i) = true := by decide +kernel

theorem strictBool_r23_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (37+i)) 23 (37+i) = true := by decide +kernel

theorem strictBool_r23_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (38+i)) 23 (38+i) = true := by decide +kernel

theorem strictBool_r23_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (39+i)) 23 (39+i) = true := by decide +kernel

theorem strictBool_r23_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (40+i)) 23 (40+i) = true := by decide +kernel

theorem strictBool_r23_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (41+i)) 23 (41+i) = true := by decide +kernel

theorem strictBool_r23_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (42+i)) 23 (42+i) = true := by decide +kernel

theorem strictBool_r23_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (43+i)) 23 (43+i) = true := by decide +kernel

theorem strictBool_r23_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (44+i)) 23 (44+i) = true := by decide +kernel

theorem strictBool_r23_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (45+i)) 23 (45+i) = true := by decide +kernel

theorem strictBool_r23_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (46+i)) 23 (46+i) = true := by decide +kernel

theorem strictBool_r23_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (47+i)) 23 (47+i) = true := by decide +kernel

theorem strictBool_r23_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (48+i)) 23 (48+i) = true := by decide +kernel

theorem strictBool_r23_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (49+i)) 23 (49+i) = true := by decide +kernel

theorem strictBool_r23_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (50+i)) 23 (50+i) = true := by decide +kernel

theorem strictBool_r23_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (51+i)) 23 (51+i) = true := by decide +kernel

theorem strictBool_r23_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (52+i)) 23 (52+i) = true := by decide +kernel

theorem strictBool_r23_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (53+i)) 23 (53+i) = true := by decide +kernel

theorem strictBool_r23_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (54+i)) 23 (54+i) = true := by decide +kernel

theorem strictBool_r23_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (55+i)) 23 (55+i) = true := by decide +kernel

theorem strictBool_r23_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (56+i)) 23 (56+i) = true := by decide +kernel

theorem strictBool_r23_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (57+i)) 23 (57+i) = true := by decide +kernel

theorem strictBool_r23_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (58+i)) 23 (58+i) = true := by decide +kernel

theorem strictBool_r23_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (59+i)) 23 (59+i) = true := by decide +kernel

theorem strictBool_r23_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (60+i)) 23 (60+i) = true := by decide +kernel

theorem strictBool_r23_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (61+i)) 23 (61+i) = true := by decide +kernel

theorem strictBool_r23_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (62+i)) 23 (62+i) = true := by decide +kernel

theorem strictBool_r23_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (63+i)) 23 (63+i) = true := by decide +kernel

theorem strictBool_r23_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (64+i)) 23 (64+i) = true := by decide +kernel

theorem strictBool_r23_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (65+i)) 23 (65+i) = true := by decide +kernel

theorem strictBool_r23_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (66+i)) 23 (66+i) = true := by decide +kernel

theorem strictBool_r23_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (67+i)) 23 (67+i) = true := by decide +kernel

theorem strictBool_r23_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (68+i)) 23 (68+i) = true := by decide +kernel

theorem strictBool_r23_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (69+i)) 23 (69+i) = true := by decide +kernel

theorem strictBool_r23_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (70+i)) 23 (70+i) = true := by decide +kernel

theorem strictBool_r23_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (71+i)) 23 (71+i) = true := by decide +kernel

theorem strictBool_r23_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (72+i)) 23 (72+i) = true := by decide +kernel

theorem strictBool_r23_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (73+i)) 23 (73+i) = true := by decide +kernel

theorem strictBool_r23_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (74+i)) 23 (74+i) = true := by decide +kernel

theorem strictBool_r23_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (75+i)) 23 (75+i) = true := by decide +kernel

theorem strictBool_r23_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (76+i)) 23 (76+i) = true := by decide +kernel

theorem strictBool_r23_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (77+i)) 23 (77+i) = true := by decide +kernel

theorem strictBool_r23_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (78+i)) 23 (78+i) = true := by decide +kernel

theorem strictBool_r23_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (79+i)) 23 (79+i) = true := by decide +kernel

theorem strictBool_r23_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (80+i)) 23 (80+i) = true := by decide +kernel

theorem strictBool_r23_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (81+i)) 23 (81+i) = true := by decide +kernel

theorem strictBool_r23_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (82+i)) 23 (82+i) = true := by decide +kernel

theorem strictBool_r23_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (83+i)) 23 (83+i) = true := by decide +kernel

theorem strictBool_r23_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (84+i)) 23 (84+i) = true := by decide +kernel

theorem strictBool_r23_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (85+i)) 23 (85+i) = true := by decide +kernel

theorem strictBool_r23_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (86+i)) 23 (86+i) = true := by decide +kernel

theorem strictBool_r23_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (87+i)) 23 (87+i) = true := by decide +kernel

theorem strictBool_r23_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (88+i)) 23 (88+i) = true := by decide +kernel

theorem strictBool_r23_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (89+i)) 23 (89+i) = true := by decide +kernel

theorem strictBool_r23_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (90+i)) 23 (90+i) = true := by decide +kernel

theorem strictBool_r23_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (91+i)) 23 (91+i) = true := by decide +kernel

theorem strictBool_r23_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (92+i)) 23 (92+i) = true := by decide +kernel

theorem strictBool_r23_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (93+i)) 23 (93+i) = true := by decide +kernel

theorem strictBool_r23_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (94+i)) 23 (94+i) = true := by decide +kernel

theorem strictBool_r23_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (95+i)) 23 (95+i) = true := by decide +kernel

theorem strictBool_r23_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (96+i)) 23 (96+i) = true := by decide +kernel

theorem strictBool_r23_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (97+i)) 23 (97+i) = true := by decide +kernel

theorem strictBool_r23_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (98+i)) 23 (98+i) = true := by decide +kernel

theorem strictBool_r23_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (99+i)) 23 (99+i) = true := by decide +kernel

theorem strictBool_r23_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (100+i)) 23 (100+i) = true := by decide +kernel

theorem strictBool_r23_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (101+i)) 23 (101+i) = true := by decide +kernel

theorem strictBool_r23_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (102+i)) 23 (102+i) = true := by decide +kernel

theorem strictBool_r23_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (103+i)) 23 (103+i) = true := by decide +kernel

theorem strictBool_r23_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (104+i)) 23 (104+i) = true := by decide +kernel

theorem strictBool_r23_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (105+i)) 23 (105+i) = true := by decide +kernel

theorem strictBool_r23_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (106+i)) 23 (106+i) = true := by decide +kernel

theorem strictBool_r23_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (107+i)) 23 (107+i) = true := by decide +kernel

theorem strictBool_r23_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (108+i)) 23 (108+i) = true := by decide +kernel

theorem strictBool_r23_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (109+i)) 23 (109+i) = true := by decide +kernel

theorem strictBool_r23_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (110+i)) 23 (110+i) = true := by decide +kernel

theorem strictBool_r23_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (111+i)) 23 (111+i) = true := by decide +kernel

theorem strictBool_r23_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (112+i)) 23 (112+i) = true := by decide +kernel

theorem strictBool_r23_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (113+i)) 23 (113+i) = true := by decide +kernel

theorem strictBool_r23_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (114+i)) 23 (114+i) = true := by decide +kernel

theorem strictBool_r23_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (115+i)) 23 (115+i) = true := by decide +kernel

theorem strictBool_r23_part116 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (116+i)) 23 (116+i) = true := by decide +kernel

theorem strictBool_r23_part117 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (117+i)) 23 (117+i) = true := by decide +kernel

theorem strictBool_r23_part118 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (118+i)) 23 (118+i) = true := by decide +kernel

theorem strictBool_r23_part119 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 23 (119+i)) 23 (119+i) = true := by decide +kernel

theorem strictBool_r23 (V : ℕ) (hV : V ∈ List.range 120) : strictBool (BoundaryTailBaseFastData.row 23 V) 23 V = true := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 60
  · by_cases h0_60 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r23_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r23_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r23_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r23_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have hi := strictBool_r23_part7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
            · by_cases h9_11 : V < 10
              · have hi := strictBool_r23_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have hi := strictBool_r23_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
            · by_cases h13_15 : V < 14
              · have hi := strictBool_r23_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have hi := strictBool_r23_part15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
            · by_cases h16_18 : V < 17
              · have hi := strictBool_r23_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have hi := strictBool_r23_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
            · by_cases h20_22 : V < 21
              · have hi := strictBool_r23_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r23_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r23_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r23_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
            · by_cases h28_30 : V < 29
              · have hi := strictBool_r23_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
    · by_cases h30_60 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have hi := strictBool_r23_part30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r23_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r23_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
            · by_cases h35_37 : V < 36
              · have hi := strictBool_r23_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r23_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r23_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r23_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r23_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
      · by_cases h45_60 : V < 52
        · by_cases h45_52 : V < 48
          · by_cases h45_48 : V < 46
            · have hi := strictBool_r23_part45 (V-45) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r23_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r23_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r23_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
        · by_cases h52_60 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r23_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r23_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r23_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
            · by_cases h58_60 : V < 59
              · have hi := strictBool_r23_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
  · by_cases h60_120 : V < 90
    · by_cases h60_90 : V < 75
      · by_cases h60_75 : V < 67
        · by_cases h60_67 : V < 63
          · by_cases h60_63 : V < 61
            · have hi := strictBool_r23_part60 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r23_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r23_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
            · by_cases h65_67 : V < 66
              · have hi := strictBool_r23_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have hi := strictBool_r23_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
            · by_cases h69_71 : V < 70
              · have hi := strictBool_r23_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r23_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r23_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
      · by_cases h75_90 : V < 82
        · by_cases h75_82 : V < 78
          · by_cases h75_78 : V < 76
            · have hi := strictBool_r23_part75 (V-75) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
            · by_cases h76_78 : V < 77
              · have hi := strictBool_r23_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r23_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r23_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r23_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
            · by_cases h84_86 : V < 85
              · have hi := strictBool_r23_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have hi := strictBool_r23_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r23_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
    · by_cases h90_120 : V < 105
      · by_cases h90_105 : V < 97
        · by_cases h90_97 : V < 93
          · by_cases h90_93 : V < 91
            · have hi := strictBool_r23_part90 (V-90) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
            · by_cases h91_93 : V < 92
              · have hi := strictBool_r23_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have hi := strictBool_r23_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r23_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r23_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r23_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r23_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r23_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h105_120 : V < 112
        · by_cases h105_112 : V < 108
          · by_cases h105_108 : V < 106
            · have hi := strictBool_r23_part105 (V-105) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r23_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r23_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r23_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
        · by_cases h112_120 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r23_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r23_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have hi := strictBool_r23_part116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using hi
            · by_cases h118_120 : V < 119
              · have hi := strictBool_r23_part118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using hi
              · have hi := strictBool_r23_part119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using hi

theorem strictFast_r23 (V : ℕ) (hV : V ∈ List.range 120) : StrictAtFast (BoundaryTailBaseFastData.row 23 V) 23 V :=
  strictBool_sound _ _ _ (strictBool_r23 V hV)

theorem strict_r23 (V : ℕ) (hV : V ∈ List.range 120) : StrictCheckAt 23 V :=
  strictAtFast_sound _ _ _ (valid_r23 V hV) (strictFast_r23 V hV)

theorem zeroCertificate_r23_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (0+i)) 23 (0+i) := by decide +kernel

theorem zeroCertificate_r23_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (8+i)) 23 (8+i) := by decide +kernel

theorem zeroCertificate_r23_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (16+i)) 23 (16+i) := by decide +kernel

theorem zeroCertificate_r23_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (24+i)) 23 (24+i) := by decide +kernel

theorem zeroCertificate_r23_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (32+i)) 23 (32+i) := by decide +kernel

theorem zeroCertificate_r23_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (40+i)) 23 (40+i) := by decide +kernel

theorem zeroCertificate_r23_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (48+i)) 23 (48+i) := by decide +kernel

theorem zeroCertificate_r23_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (56+i)) 23 (56+i) := by decide +kernel

theorem zeroCertificate_r23_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (64+i)) 23 (64+i) := by decide +kernel

theorem zeroCertificate_r23_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (72+i)) 23 (72+i) := by decide +kernel

theorem zeroCertificate_r23_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (80+i)) 23 (80+i) := by decide +kernel

theorem zeroCertificate_r23_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (88+i)) 23 (88+i) := by decide +kernel

theorem zeroCertificate_r23_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (96+i)) 23 (96+i) := by decide +kernel

theorem zeroCertificate_r23_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (104+i)) 23 (104+i) := by decide +kernel

theorem zeroCertificate_r23_part112 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 23 (112+i)) 23 (112+i) := by decide +kernel

theorem zeroCertificate_r23 (V : ℕ) (hV : V ∈ List.range 120) : ZeroCertificate (BoundaryTailBaseFastData.row 23 V) 23 V := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := zeroCertificate_r23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r23 (V : ℕ) (hV : V ∈ List.range 120) : ZeroAtFast 23 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r23 V hV) (zeroCertificate_r23 V hV)

theorem zero_r23 (V : ℕ) (hV : V ∈ List.range 120) : ZeroCheckAt 23 V :=
  zeroAtFast_sound _ _ (zeroFast_r23 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r27_part0 : ∀ i ∈ List.range 8, CorrectAt 27 (0+i) := by decide +kernel

theorem correct_r27_part8 : ∀ i ∈ List.range 8, CorrectAt 27 (8+i) := by decide +kernel

theorem correct_r27_part16 : ∀ i ∈ List.range 8, CorrectAt 27 (16+i) := by decide +kernel

theorem correct_r27_part24 : ∀ i ∈ List.range 8, CorrectAt 27 (24+i) := by decide +kernel

theorem correct_r27_part32 : ∀ i ∈ List.range 8, CorrectAt 27 (32+i) := by decide +kernel

theorem correct_r27_part40 : ∀ i ∈ List.range 8, CorrectAt 27 (40+i) := by decide +kernel

theorem correct_r27_part48 : ∀ i ∈ List.range 8, CorrectAt 27 (48+i) := by decide +kernel

theorem correct_r27_part56 : ∀ i ∈ List.range 8, CorrectAt 27 (56+i) := by decide +kernel

theorem correct_r27_part64 : ∀ i ∈ List.range 8, CorrectAt 27 (64+i) := by decide +kernel

theorem correct_r27_part72 : ∀ i ∈ List.range 8, CorrectAt 27 (72+i) := by decide +kernel

theorem correct_r27_part80 : ∀ i ∈ List.range 8, CorrectAt 27 (80+i) := by decide +kernel

theorem correct_r27_part88 : ∀ i ∈ List.range 8, CorrectAt 27 (88+i) := by decide +kernel

theorem correct_r27_part96 : ∀ i ∈ List.range 8, CorrectAt 27 (96+i) := by decide +kernel

theorem correct_r27_part104 : ∀ i ∈ List.range 8, CorrectAt 27 (104+i) := by decide +kernel

theorem correct_r27_part112 : ∀ i ∈ List.range 4, CorrectAt 27 (112+i) := by decide +kernel

theorem correct_r27 (V : ℕ) (hV : V ∈ List.range 116) : CorrectAt 27 V := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := correct_r27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := correct_r27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := correct_r27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := correct_r27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := correct_r27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := correct_r27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := correct_r27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := correct_r27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem base_r27_part0 : ∀ i ∈ List.range 8, BaseCheckAt 27 (0+i) := by decide +kernel

theorem base_r27_part8 : ∀ i ∈ List.range 8, BaseCheckAt 27 (8+i) := by decide +kernel

theorem base_r27_part16 : ∀ i ∈ List.range 8, BaseCheckAt 27 (16+i) := by decide +kernel

theorem base_r27_part24 : ∀ i ∈ List.range 8, BaseCheckAt 27 (24+i) := by decide +kernel

theorem base_r27_part32 : ∀ i ∈ List.range 8, BaseCheckAt 27 (32+i) := by decide +kernel

theorem base_r27_part40 : ∀ i ∈ List.range 8, BaseCheckAt 27 (40+i) := by decide +kernel

theorem base_r27_part48 : ∀ i ∈ List.range 8, BaseCheckAt 27 (48+i) := by decide +kernel

theorem base_r27_part56 : ∀ i ∈ List.range 8, BaseCheckAt 27 (56+i) := by decide +kernel

theorem base_r27_part64 : ∀ i ∈ List.range 8, BaseCheckAt 27 (64+i) := by decide +kernel

theorem base_r27_part72 : ∀ i ∈ List.range 8, BaseCheckAt 27 (72+i) := by decide +kernel

theorem base_r27_part80 : ∀ i ∈ List.range 8, BaseCheckAt 27 (80+i) := by decide +kernel

theorem base_r27_part88 : ∀ i ∈ List.range 8, BaseCheckAt 27 (88+i) := by decide +kernel

theorem base_r27_part96 : ∀ i ∈ List.range 8, BaseCheckAt 27 (96+i) := by decide +kernel

theorem base_r27_part104 : ∀ i ∈ List.range 8, BaseCheckAt 27 (104+i) := by decide +kernel

theorem base_r27_part112 : ∀ i ∈ List.range 4, BaseCheckAt 27 (112+i) := by decide +kernel

theorem base_r27 (V : ℕ) (hV : V ∈ List.range 116) : BaseCheckAt 27 V := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := base_r27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := base_r27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := base_r27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := base_r27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := base_r27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := base_r27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := base_r27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := base_r27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem valid_r27_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (0+i)) 27 (0+i) := by decide +kernel

theorem valid_r27_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (8+i)) 27 (8+i) := by decide +kernel

theorem valid_r27_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (16+i)) 27 (16+i) := by decide +kernel

theorem valid_r27_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (24+i)) 27 (24+i) := by decide +kernel

theorem valid_r27_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (32+i)) 27 (32+i) := by decide +kernel

theorem valid_r27_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (40+i)) 27 (40+i) := by decide +kernel

theorem valid_r27_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (48+i)) 27 (48+i) := by decide +kernel

theorem valid_r27_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (56+i)) 27 (56+i) := by decide +kernel

theorem valid_r27_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (64+i)) 27 (64+i) := by decide +kernel

theorem valid_r27_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (72+i)) 27 (72+i) := by decide +kernel

theorem valid_r27_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (80+i)) 27 (80+i) := by decide +kernel

theorem valid_r27_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (88+i)) 27 (88+i) := by decide +kernel

theorem valid_r27_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (96+i)) 27 (96+i) := by decide +kernel

theorem valid_r27_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 27 (104+i)) 27 (104+i) := by decide +kernel

theorem valid_r27_part112 : ∀ i ∈ List.range 4, Valid (BoundaryTailBaseFastData.row 27 (112+i)) 27 (112+i) := by decide +kernel

theorem valid_r27 (V : ℕ) (hV : V ∈ List.range 116) : Valid (BoundaryTailBaseFastData.row 27 V) 27 V := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := valid_r27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := valid_r27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := valid_r27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := valid_r27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := valid_r27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := valid_r27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := valid_r27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := valid_r27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem strictBool_r27_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (0+i)) 27 (0+i) = true := by decide +kernel

theorem strictBool_r27_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (1+i)) 27 (1+i) = true := by decide +kernel

theorem strictBool_r27_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (2+i)) 27 (2+i) = true := by decide +kernel

theorem strictBool_r27_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (3+i)) 27 (3+i) = true := by decide +kernel

theorem strictBool_r27_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (4+i)) 27 (4+i) = true := by decide +kernel

theorem strictBool_r27_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (5+i)) 27 (5+i) = true := by decide +kernel

theorem strictBool_r27_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (6+i)) 27 (6+i) = true := by decide +kernel

theorem strictBool_r27_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (7+i)) 27 (7+i) = true := by decide +kernel

theorem strictBool_r27_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (8+i)) 27 (8+i) = true := by decide +kernel

theorem strictBool_r27_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (9+i)) 27 (9+i) = true := by decide +kernel

theorem strictBool_r27_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (10+i)) 27 (10+i) = true := by decide +kernel

theorem strictBool_r27_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (11+i)) 27 (11+i) = true := by decide +kernel

theorem strictBool_r27_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (12+i)) 27 (12+i) = true := by decide +kernel

theorem strictBool_r27_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (13+i)) 27 (13+i) = true := by decide +kernel

theorem strictBool_r27_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (14+i)) 27 (14+i) = true := by decide +kernel

theorem strictBool_r27_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (15+i)) 27 (15+i) = true := by decide +kernel

theorem strictBool_r27_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (16+i)) 27 (16+i) = true := by decide +kernel

theorem strictBool_r27_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (17+i)) 27 (17+i) = true := by decide +kernel

theorem strictBool_r27_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (18+i)) 27 (18+i) = true := by decide +kernel

theorem strictBool_r27_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (19+i)) 27 (19+i) = true := by decide +kernel

theorem strictBool_r27_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (20+i)) 27 (20+i) = true := by decide +kernel

theorem strictBool_r27_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (21+i)) 27 (21+i) = true := by decide +kernel

theorem strictBool_r27_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (22+i)) 27 (22+i) = true := by decide +kernel

theorem strictBool_r27_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (23+i)) 27 (23+i) = true := by decide +kernel

theorem strictBool_r27_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (24+i)) 27 (24+i) = true := by decide +kernel

theorem strictBool_r27_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (25+i)) 27 (25+i) = true := by decide +kernel

theorem strictBool_r27_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (26+i)) 27 (26+i) = true := by decide +kernel

theorem strictBool_r27_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (27+i)) 27 (27+i) = true := by decide +kernel

theorem strictBool_r27_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (28+i)) 27 (28+i) = true := by decide +kernel

theorem strictBool_r27_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (29+i)) 27 (29+i) = true := by decide +kernel

theorem strictBool_r27_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (30+i)) 27 (30+i) = true := by decide +kernel

theorem strictBool_r27_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (31+i)) 27 (31+i) = true := by decide +kernel

theorem strictBool_r27_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (32+i)) 27 (32+i) = true := by decide +kernel

theorem strictBool_r27_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (33+i)) 27 (33+i) = true := by decide +kernel

theorem strictBool_r27_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (34+i)) 27 (34+i) = true := by decide +kernel

theorem strictBool_r27_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (35+i)) 27 (35+i) = true := by decide +kernel

theorem strictBool_r27_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (36+i)) 27 (36+i) = true := by decide +kernel

theorem strictBool_r27_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (37+i)) 27 (37+i) = true := by decide +kernel

theorem strictBool_r27_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (38+i)) 27 (38+i) = true := by decide +kernel

theorem strictBool_r27_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (39+i)) 27 (39+i) = true := by decide +kernel

theorem strictBool_r27_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (40+i)) 27 (40+i) = true := by decide +kernel

theorem strictBool_r27_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (41+i)) 27 (41+i) = true := by decide +kernel

theorem strictBool_r27_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (42+i)) 27 (42+i) = true := by decide +kernel

theorem strictBool_r27_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (43+i)) 27 (43+i) = true := by decide +kernel

theorem strictBool_r27_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (44+i)) 27 (44+i) = true := by decide +kernel

theorem strictBool_r27_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (45+i)) 27 (45+i) = true := by decide +kernel

theorem strictBool_r27_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (46+i)) 27 (46+i) = true := by decide +kernel

theorem strictBool_r27_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (47+i)) 27 (47+i) = true := by decide +kernel

theorem strictBool_r27_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (48+i)) 27 (48+i) = true := by decide +kernel

theorem strictBool_r27_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (49+i)) 27 (49+i) = true := by decide +kernel

theorem strictBool_r27_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (50+i)) 27 (50+i) = true := by decide +kernel

theorem strictBool_r27_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (51+i)) 27 (51+i) = true := by decide +kernel

theorem strictBool_r27_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (52+i)) 27 (52+i) = true := by decide +kernel

theorem strictBool_r27_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (53+i)) 27 (53+i) = true := by decide +kernel

theorem strictBool_r27_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (54+i)) 27 (54+i) = true := by decide +kernel

theorem strictBool_r27_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (55+i)) 27 (55+i) = true := by decide +kernel

theorem strictBool_r27_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (56+i)) 27 (56+i) = true := by decide +kernel

theorem strictBool_r27_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (57+i)) 27 (57+i) = true := by decide +kernel

theorem strictBool_r27_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (58+i)) 27 (58+i) = true := by decide +kernel

theorem strictBool_r27_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (59+i)) 27 (59+i) = true := by decide +kernel

theorem strictBool_r27_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (60+i)) 27 (60+i) = true := by decide +kernel

theorem strictBool_r27_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (61+i)) 27 (61+i) = true := by decide +kernel

theorem strictBool_r27_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (62+i)) 27 (62+i) = true := by decide +kernel

theorem strictBool_r27_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (63+i)) 27 (63+i) = true := by decide +kernel

theorem strictBool_r27_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (64+i)) 27 (64+i) = true := by decide +kernel

theorem strictBool_r27_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (65+i)) 27 (65+i) = true := by decide +kernel

theorem strictBool_r27_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (66+i)) 27 (66+i) = true := by decide +kernel

theorem strictBool_r27_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (67+i)) 27 (67+i) = true := by decide +kernel

theorem strictBool_r27_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (68+i)) 27 (68+i) = true := by decide +kernel

theorem strictBool_r27_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (69+i)) 27 (69+i) = true := by decide +kernel

theorem strictBool_r27_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (70+i)) 27 (70+i) = true := by decide +kernel

theorem strictBool_r27_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (71+i)) 27 (71+i) = true := by decide +kernel

theorem strictBool_r27_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (72+i)) 27 (72+i) = true := by decide +kernel

theorem strictBool_r27_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (73+i)) 27 (73+i) = true := by decide +kernel

theorem strictBool_r27_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (74+i)) 27 (74+i) = true := by decide +kernel

theorem strictBool_r27_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (75+i)) 27 (75+i) = true := by decide +kernel

theorem strictBool_r27_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (76+i)) 27 (76+i) = true := by decide +kernel

theorem strictBool_r27_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (77+i)) 27 (77+i) = true := by decide +kernel

theorem strictBool_r27_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (78+i)) 27 (78+i) = true := by decide +kernel

theorem strictBool_r27_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (79+i)) 27 (79+i) = true := by decide +kernel

theorem strictBool_r27_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (80+i)) 27 (80+i) = true := by decide +kernel

theorem strictBool_r27_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (81+i)) 27 (81+i) = true := by decide +kernel

theorem strictBool_r27_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (82+i)) 27 (82+i) = true := by decide +kernel

theorem strictBool_r27_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (83+i)) 27 (83+i) = true := by decide +kernel

theorem strictBool_r27_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (84+i)) 27 (84+i) = true := by decide +kernel

theorem strictBool_r27_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (85+i)) 27 (85+i) = true := by decide +kernel

theorem strictBool_r27_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (86+i)) 27 (86+i) = true := by decide +kernel

theorem strictBool_r27_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (87+i)) 27 (87+i) = true := by decide +kernel

theorem strictBool_r27_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (88+i)) 27 (88+i) = true := by decide +kernel

theorem strictBool_r27_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (89+i)) 27 (89+i) = true := by decide +kernel

theorem strictBool_r27_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (90+i)) 27 (90+i) = true := by decide +kernel

theorem strictBool_r27_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (91+i)) 27 (91+i) = true := by decide +kernel

theorem strictBool_r27_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (92+i)) 27 (92+i) = true := by decide +kernel

theorem strictBool_r27_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (93+i)) 27 (93+i) = true := by decide +kernel

theorem strictBool_r27_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (94+i)) 27 (94+i) = true := by decide +kernel

theorem strictBool_r27_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (95+i)) 27 (95+i) = true := by decide +kernel

theorem strictBool_r27_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (96+i)) 27 (96+i) = true := by decide +kernel

theorem strictBool_r27_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (97+i)) 27 (97+i) = true := by decide +kernel

theorem strictBool_r27_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (98+i)) 27 (98+i) = true := by decide +kernel

theorem strictBool_r27_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (99+i)) 27 (99+i) = true := by decide +kernel

theorem strictBool_r27_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (100+i)) 27 (100+i) = true := by decide +kernel

theorem strictBool_r27_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (101+i)) 27 (101+i) = true := by decide +kernel

theorem strictBool_r27_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (102+i)) 27 (102+i) = true := by decide +kernel

theorem strictBool_r27_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (103+i)) 27 (103+i) = true := by decide +kernel

theorem strictBool_r27_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (104+i)) 27 (104+i) = true := by decide +kernel

theorem strictBool_r27_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (105+i)) 27 (105+i) = true := by decide +kernel

theorem strictBool_r27_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (106+i)) 27 (106+i) = true := by decide +kernel

theorem strictBool_r27_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (107+i)) 27 (107+i) = true := by decide +kernel

theorem strictBool_r27_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (108+i)) 27 (108+i) = true := by decide +kernel

theorem strictBool_r27_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (109+i)) 27 (109+i) = true := by decide +kernel

theorem strictBool_r27_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (110+i)) 27 (110+i) = true := by decide +kernel

theorem strictBool_r27_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (111+i)) 27 (111+i) = true := by decide +kernel

theorem strictBool_r27_part112 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (112+i)) 27 (112+i) = true := by decide +kernel

theorem strictBool_r27_part113 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (113+i)) 27 (113+i) = true := by decide +kernel

theorem strictBool_r27_part114 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (114+i)) 27 (114+i) = true := by decide +kernel

theorem strictBool_r27_part115 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 27 (115+i)) 27 (115+i) = true := by decide +kernel

theorem strictBool_r27 (V : ℕ) (hV : V ∈ List.range 116) : strictBool (BoundaryTailBaseFastData.row 27 V) 27 V = true := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 58
  · by_cases h0_58 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r27_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r27_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r27_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r27_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r27_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r27_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r27_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r27_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r27_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r27_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r27_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r27_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have hi := strictBool_r27_part21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
            · by_cases h23_25 : V < 24
              · have hi := strictBool_r27_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have hi := strictBool_r27_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
            · by_cases h27_29 : V < 28
              · have hi := strictBool_r27_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
    · by_cases h29_58 : V < 43
      · by_cases h29_43 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have hi := strictBool_r27_part29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
            · by_cases h30_32 : V < 31
              · have hi := strictBool_r27_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have hi := strictBool_r27_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
            · by_cases h34_36 : V < 35
              · have hi := strictBool_r27_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
        · by_cases h36_43 : V < 39
          · by_cases h36_39 : V < 37
            · have hi := strictBool_r27_part36 (V-36) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
            · by_cases h37_39 : V < 38
              · have hi := strictBool_r27_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have hi := strictBool_r27_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            · by_cases h41_43 : V < 42
              · have hi := strictBool_r27_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
      · by_cases h43_58 : V < 50
        · by_cases h43_50 : V < 46
          · by_cases h43_46 : V < 44
            · have hi := strictBool_r27_part43 (V-43) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
            · by_cases h44_46 : V < 45
              · have hi := strictBool_r27_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have hi := strictBool_r27_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
            · by_cases h48_50 : V < 49
              · have hi := strictBool_r27_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r27_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r27_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r27_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
            · by_cases h56_58 : V < 57
              · have hi := strictBool_r27_part56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
  · by_cases h58_116 : V < 87
    · by_cases h58_87 : V < 72
      · by_cases h58_72 : V < 65
        · by_cases h58_65 : V < 61
          · by_cases h58_61 : V < 59
            · have hi := strictBool_r27_part58 (V-58) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r27_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r27_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
            · by_cases h63_65 : V < 64
              · have hi := strictBool_r27_part63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · by_cases h65_72 : V < 68
          · by_cases h65_68 : V < 66
            · have hi := strictBool_r27_part65 (V-65) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r27_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r27_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
            · by_cases h70_72 : V < 71
              · have hi := strictBool_r27_part70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
      · by_cases h72_87 : V < 79
        · by_cases h72_79 : V < 75
          · by_cases h72_75 : V < 73
            · have hi := strictBool_r27_part72 (V-72) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r27_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r27_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
            · by_cases h77_79 : V < 78
              · have hi := strictBool_r27_part77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have hi := strictBool_r27_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
            · by_cases h81_83 : V < 82
              · have hi := strictBool_r27_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have hi := strictBool_r27_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r27_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
    · by_cases h87_116 : V < 101
      · by_cases h87_101 : V < 94
        · by_cases h87_94 : V < 90
          · by_cases h87_90 : V < 88
            · have hi := strictBool_r27_part87 (V-87) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
            · by_cases h88_90 : V < 89
              · have hi := strictBool_r27_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have hi := strictBool_r27_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r27_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
        · by_cases h94_101 : V < 97
          · by_cases h94_97 : V < 95
            · have hi := strictBool_r27_part94 (V-94) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
            · by_cases h95_97 : V < 96
              · have hi := strictBool_r27_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have hi := strictBool_r27_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r27_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
      · by_cases h101_116 : V < 108
        · by_cases h101_108 : V < 104
          · by_cases h101_104 : V < 102
            · have hi := strictBool_r27_part101 (V-101) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
            · by_cases h102_104 : V < 103
              · have hi := strictBool_r27_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have hi := strictBool_r27_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r27_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
        · by_cases h108_116 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r27_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r27_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have hi := strictBool_r27_part112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using hi
            · by_cases h114_116 : V < 115
              · have hi := strictBool_r27_part114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using hi
              · have hi := strictBool_r27_part115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using hi

theorem strictFast_r27 (V : ℕ) (hV : V ∈ List.range 116) : StrictAtFast (BoundaryTailBaseFastData.row 27 V) 27 V :=
  strictBool_sound _ _ _ (strictBool_r27 V hV)

theorem strict_r27 (V : ℕ) (hV : V ∈ List.range 116) : StrictCheckAt 27 V :=
  strictAtFast_sound _ _ _ (valid_r27 V hV) (strictFast_r27 V hV)

theorem zeroCertificate_r27_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (0+i)) 27 (0+i) := by decide +kernel

theorem zeroCertificate_r27_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (8+i)) 27 (8+i) := by decide +kernel

theorem zeroCertificate_r27_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (16+i)) 27 (16+i) := by decide +kernel

theorem zeroCertificate_r27_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (24+i)) 27 (24+i) := by decide +kernel

theorem zeroCertificate_r27_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (32+i)) 27 (32+i) := by decide +kernel

theorem zeroCertificate_r27_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (40+i)) 27 (40+i) := by decide +kernel

theorem zeroCertificate_r27_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (48+i)) 27 (48+i) := by decide +kernel

theorem zeroCertificate_r27_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (56+i)) 27 (56+i) := by decide +kernel

theorem zeroCertificate_r27_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (64+i)) 27 (64+i) := by decide +kernel

theorem zeroCertificate_r27_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (72+i)) 27 (72+i) := by decide +kernel

theorem zeroCertificate_r27_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (80+i)) 27 (80+i) := by decide +kernel

theorem zeroCertificate_r27_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (88+i)) 27 (88+i) := by decide +kernel

theorem zeroCertificate_r27_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (96+i)) 27 (96+i) := by decide +kernel

theorem zeroCertificate_r27_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 27 (104+i)) 27 (104+i) := by decide +kernel

theorem zeroCertificate_r27_part112 : ∀ i ∈ List.range 4, ZeroCertificate (BoundaryTailBaseFastData.row 27 (112+i)) 27 (112+i) := by decide +kernel

theorem zeroCertificate_r27 (V : ℕ) (hV : V ∈ List.range 116) : ZeroCertificate (BoundaryTailBaseFastData.row 27 V) 27 V := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := zeroCertificate_r27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := zeroCertificate_r27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := zeroCertificate_r27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := zeroCertificate_r27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi

theorem zeroFast_r27 (V : ℕ) (hV : V ∈ List.range 116) : ZeroAtFast 27 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r27 V hV) (zeroCertificate_r27 V hV)

theorem zero_r27 (V : ℕ) (hV : V ∈ List.range 116) : ZeroCheckAt 27 V :=
  zeroAtFast_sound _ _ (zeroFast_r27 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correct_r31_part0 : ∀ i ∈ List.range 8, CorrectAt 31 (0+i) := by decide +kernel

theorem correct_r31_part8 : ∀ i ∈ List.range 8, CorrectAt 31 (8+i) := by decide +kernel

theorem correct_r31_part16 : ∀ i ∈ List.range 8, CorrectAt 31 (16+i) := by decide +kernel

theorem correct_r31_part24 : ∀ i ∈ List.range 8, CorrectAt 31 (24+i) := by decide +kernel

theorem correct_r31_part32 : ∀ i ∈ List.range 8, CorrectAt 31 (32+i) := by decide +kernel

theorem correct_r31_part40 : ∀ i ∈ List.range 8, CorrectAt 31 (40+i) := by decide +kernel

theorem correct_r31_part48 : ∀ i ∈ List.range 8, CorrectAt 31 (48+i) := by decide +kernel

theorem correct_r31_part56 : ∀ i ∈ List.range 8, CorrectAt 31 (56+i) := by decide +kernel

theorem correct_r31_part64 : ∀ i ∈ List.range 8, CorrectAt 31 (64+i) := by decide +kernel

theorem correct_r31_part72 : ∀ i ∈ List.range 8, CorrectAt 31 (72+i) := by decide +kernel

theorem correct_r31_part80 : ∀ i ∈ List.range 8, CorrectAt 31 (80+i) := by decide +kernel

theorem correct_r31_part88 : ∀ i ∈ List.range 8, CorrectAt 31 (88+i) := by decide +kernel

theorem correct_r31_part96 : ∀ i ∈ List.range 8, CorrectAt 31 (96+i) := by decide +kernel

theorem correct_r31_part104 : ∀ i ∈ List.range 8, CorrectAt 31 (104+i) := by decide +kernel

theorem correct_r31 (V : ℕ) (hV : V ∈ List.range 112) : CorrectAt 31 V := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := correct_r31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := correct_r31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := correct_r31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := correct_r31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := correct_r31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := correct_r31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := correct_r31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := correct_r31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := correct_r31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := correct_r31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := correct_r31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := correct_r31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := correct_r31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := correct_r31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem base_r31_part0 : ∀ i ∈ List.range 8, BaseCheckAt 31 (0+i) := by decide +kernel

theorem base_r31_part8 : ∀ i ∈ List.range 8, BaseCheckAt 31 (8+i) := by decide +kernel

theorem base_r31_part16 : ∀ i ∈ List.range 8, BaseCheckAt 31 (16+i) := by decide +kernel

theorem base_r31_part24 : ∀ i ∈ List.range 8, BaseCheckAt 31 (24+i) := by decide +kernel

theorem base_r31_part32 : ∀ i ∈ List.range 8, BaseCheckAt 31 (32+i) := by decide +kernel

theorem base_r31_part40 : ∀ i ∈ List.range 8, BaseCheckAt 31 (40+i) := by decide +kernel

theorem base_r31_part48 : ∀ i ∈ List.range 8, BaseCheckAt 31 (48+i) := by decide +kernel

theorem base_r31_part56 : ∀ i ∈ List.range 8, BaseCheckAt 31 (56+i) := by decide +kernel

theorem base_r31_part64 : ∀ i ∈ List.range 8, BaseCheckAt 31 (64+i) := by decide +kernel

theorem base_r31_part72 : ∀ i ∈ List.range 8, BaseCheckAt 31 (72+i) := by decide +kernel

theorem base_r31_part80 : ∀ i ∈ List.range 8, BaseCheckAt 31 (80+i) := by decide +kernel

theorem base_r31_part88 : ∀ i ∈ List.range 8, BaseCheckAt 31 (88+i) := by decide +kernel

theorem base_r31_part96 : ∀ i ∈ List.range 8, BaseCheckAt 31 (96+i) := by decide +kernel

theorem base_r31_part104 : ∀ i ∈ List.range 8, BaseCheckAt 31 (104+i) := by decide +kernel

theorem base_r31 (V : ℕ) (hV : V ∈ List.range 112) : BaseCheckAt 31 V := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := base_r31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := base_r31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := base_r31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := base_r31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := base_r31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := base_r31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := base_r31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := base_r31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := base_r31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := base_r31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := base_r31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := base_r31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := base_r31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := base_r31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem valid_r31_part0 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (0+i)) 31 (0+i) := by decide +kernel

theorem valid_r31_part8 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (8+i)) 31 (8+i) := by decide +kernel

theorem valid_r31_part16 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (16+i)) 31 (16+i) := by decide +kernel

theorem valid_r31_part24 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (24+i)) 31 (24+i) := by decide +kernel

theorem valid_r31_part32 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (32+i)) 31 (32+i) := by decide +kernel

theorem valid_r31_part40 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (40+i)) 31 (40+i) := by decide +kernel

theorem valid_r31_part48 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (48+i)) 31 (48+i) := by decide +kernel

theorem valid_r31_part56 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (56+i)) 31 (56+i) := by decide +kernel

theorem valid_r31_part64 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (64+i)) 31 (64+i) := by decide +kernel

theorem valid_r31_part72 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (72+i)) 31 (72+i) := by decide +kernel

theorem valid_r31_part80 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (80+i)) 31 (80+i) := by decide +kernel

theorem valid_r31_part88 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (88+i)) 31 (88+i) := by decide +kernel

theorem valid_r31_part96 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (96+i)) 31 (96+i) := by decide +kernel

theorem valid_r31_part104 : ∀ i ∈ List.range 8, Valid (BoundaryTailBaseFastData.row 31 (104+i)) 31 (104+i) := by decide +kernel

theorem valid_r31 (V : ℕ) (hV : V ∈ List.range 112) : Valid (BoundaryTailBaseFastData.row 31 V) 31 V := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := valid_r31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := valid_r31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := valid_r31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := valid_r31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := valid_r31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := valid_r31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := valid_r31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := valid_r31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := valid_r31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := valid_r31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := valid_r31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := valid_r31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := valid_r31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := valid_r31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem strictBool_r31_part0 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (0+i)) 31 (0+i) = true := by decide +kernel

theorem strictBool_r31_part1 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (1+i)) 31 (1+i) = true := by decide +kernel

theorem strictBool_r31_part2 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (2+i)) 31 (2+i) = true := by decide +kernel

theorem strictBool_r31_part3 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (3+i)) 31 (3+i) = true := by decide +kernel

theorem strictBool_r31_part4 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (4+i)) 31 (4+i) = true := by decide +kernel

theorem strictBool_r31_part5 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (5+i)) 31 (5+i) = true := by decide +kernel

theorem strictBool_r31_part6 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (6+i)) 31 (6+i) = true := by decide +kernel

theorem strictBool_r31_part7 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (7+i)) 31 (7+i) = true := by decide +kernel

theorem strictBool_r31_part8 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (8+i)) 31 (8+i) = true := by decide +kernel

theorem strictBool_r31_part9 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (9+i)) 31 (9+i) = true := by decide +kernel

theorem strictBool_r31_part10 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (10+i)) 31 (10+i) = true := by decide +kernel

theorem strictBool_r31_part11 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (11+i)) 31 (11+i) = true := by decide +kernel

theorem strictBool_r31_part12 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (12+i)) 31 (12+i) = true := by decide +kernel

theorem strictBool_r31_part13 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (13+i)) 31 (13+i) = true := by decide +kernel

theorem strictBool_r31_part14 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (14+i)) 31 (14+i) = true := by decide +kernel

theorem strictBool_r31_part15 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (15+i)) 31 (15+i) = true := by decide +kernel

theorem strictBool_r31_part16 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (16+i)) 31 (16+i) = true := by decide +kernel

theorem strictBool_r31_part17 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (17+i)) 31 (17+i) = true := by decide +kernel

theorem strictBool_r31_part18 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (18+i)) 31 (18+i) = true := by decide +kernel

theorem strictBool_r31_part19 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (19+i)) 31 (19+i) = true := by decide +kernel

theorem strictBool_r31_part20 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (20+i)) 31 (20+i) = true := by decide +kernel

theorem strictBool_r31_part21 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (21+i)) 31 (21+i) = true := by decide +kernel

theorem strictBool_r31_part22 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (22+i)) 31 (22+i) = true := by decide +kernel

theorem strictBool_r31_part23 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (23+i)) 31 (23+i) = true := by decide +kernel

theorem strictBool_r31_part24 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (24+i)) 31 (24+i) = true := by decide +kernel

theorem strictBool_r31_part25 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (25+i)) 31 (25+i) = true := by decide +kernel

theorem strictBool_r31_part26 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (26+i)) 31 (26+i) = true := by decide +kernel

theorem strictBool_r31_part27 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (27+i)) 31 (27+i) = true := by decide +kernel

theorem strictBool_r31_part28 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (28+i)) 31 (28+i) = true := by decide +kernel

theorem strictBool_r31_part29 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (29+i)) 31 (29+i) = true := by decide +kernel

theorem strictBool_r31_part30 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (30+i)) 31 (30+i) = true := by decide +kernel

theorem strictBool_r31_part31 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (31+i)) 31 (31+i) = true := by decide +kernel

theorem strictBool_r31_part32 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (32+i)) 31 (32+i) = true := by decide +kernel

theorem strictBool_r31_part33 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (33+i)) 31 (33+i) = true := by decide +kernel

theorem strictBool_r31_part34 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (34+i)) 31 (34+i) = true := by decide +kernel

theorem strictBool_r31_part35 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (35+i)) 31 (35+i) = true := by decide +kernel

theorem strictBool_r31_part36 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (36+i)) 31 (36+i) = true := by decide +kernel

theorem strictBool_r31_part37 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (37+i)) 31 (37+i) = true := by decide +kernel

theorem strictBool_r31_part38 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (38+i)) 31 (38+i) = true := by decide +kernel

theorem strictBool_r31_part39 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (39+i)) 31 (39+i) = true := by decide +kernel

theorem strictBool_r31_part40 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (40+i)) 31 (40+i) = true := by decide +kernel

theorem strictBool_r31_part41 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (41+i)) 31 (41+i) = true := by decide +kernel

theorem strictBool_r31_part42 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (42+i)) 31 (42+i) = true := by decide +kernel

theorem strictBool_r31_part43 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (43+i)) 31 (43+i) = true := by decide +kernel

theorem strictBool_r31_part44 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (44+i)) 31 (44+i) = true := by decide +kernel

theorem strictBool_r31_part45 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (45+i)) 31 (45+i) = true := by decide +kernel

theorem strictBool_r31_part46 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (46+i)) 31 (46+i) = true := by decide +kernel

theorem strictBool_r31_part47 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (47+i)) 31 (47+i) = true := by decide +kernel

theorem strictBool_r31_part48 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (48+i)) 31 (48+i) = true := by decide +kernel

theorem strictBool_r31_part49 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (49+i)) 31 (49+i) = true := by decide +kernel

theorem strictBool_r31_part50 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (50+i)) 31 (50+i) = true := by decide +kernel

theorem strictBool_r31_part51 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (51+i)) 31 (51+i) = true := by decide +kernel

theorem strictBool_r31_part52 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (52+i)) 31 (52+i) = true := by decide +kernel

theorem strictBool_r31_part53 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (53+i)) 31 (53+i) = true := by decide +kernel

theorem strictBool_r31_part54 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (54+i)) 31 (54+i) = true := by decide +kernel

theorem strictBool_r31_part55 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (55+i)) 31 (55+i) = true := by decide +kernel

theorem strictBool_r31_part56 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (56+i)) 31 (56+i) = true := by decide +kernel

theorem strictBool_r31_part57 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (57+i)) 31 (57+i) = true := by decide +kernel

theorem strictBool_r31_part58 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (58+i)) 31 (58+i) = true := by decide +kernel

theorem strictBool_r31_part59 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (59+i)) 31 (59+i) = true := by decide +kernel

theorem strictBool_r31_part60 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (60+i)) 31 (60+i) = true := by decide +kernel

theorem strictBool_r31_part61 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (61+i)) 31 (61+i) = true := by decide +kernel

theorem strictBool_r31_part62 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (62+i)) 31 (62+i) = true := by decide +kernel

theorem strictBool_r31_part63 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (63+i)) 31 (63+i) = true := by decide +kernel

theorem strictBool_r31_part64 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (64+i)) 31 (64+i) = true := by decide +kernel

theorem strictBool_r31_part65 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (65+i)) 31 (65+i) = true := by decide +kernel

theorem strictBool_r31_part66 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (66+i)) 31 (66+i) = true := by decide +kernel

theorem strictBool_r31_part67 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (67+i)) 31 (67+i) = true := by decide +kernel

theorem strictBool_r31_part68 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (68+i)) 31 (68+i) = true := by decide +kernel

theorem strictBool_r31_part69 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (69+i)) 31 (69+i) = true := by decide +kernel

theorem strictBool_r31_part70 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (70+i)) 31 (70+i) = true := by decide +kernel

theorem strictBool_r31_part71 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (71+i)) 31 (71+i) = true := by decide +kernel

theorem strictBool_r31_part72 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (72+i)) 31 (72+i) = true := by decide +kernel

theorem strictBool_r31_part73 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (73+i)) 31 (73+i) = true := by decide +kernel

theorem strictBool_r31_part74 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (74+i)) 31 (74+i) = true := by decide +kernel

theorem strictBool_r31_part75 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (75+i)) 31 (75+i) = true := by decide +kernel

theorem strictBool_r31_part76 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (76+i)) 31 (76+i) = true := by decide +kernel

theorem strictBool_r31_part77 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (77+i)) 31 (77+i) = true := by decide +kernel

theorem strictBool_r31_part78 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (78+i)) 31 (78+i) = true := by decide +kernel

theorem strictBool_r31_part79 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (79+i)) 31 (79+i) = true := by decide +kernel

theorem strictBool_r31_part80 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (80+i)) 31 (80+i) = true := by decide +kernel

theorem strictBool_r31_part81 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (81+i)) 31 (81+i) = true := by decide +kernel

theorem strictBool_r31_part82 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (82+i)) 31 (82+i) = true := by decide +kernel

theorem strictBool_r31_part83 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (83+i)) 31 (83+i) = true := by decide +kernel

theorem strictBool_r31_part84 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (84+i)) 31 (84+i) = true := by decide +kernel

theorem strictBool_r31_part85 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (85+i)) 31 (85+i) = true := by decide +kernel

theorem strictBool_r31_part86 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (86+i)) 31 (86+i) = true := by decide +kernel

theorem strictBool_r31_part87 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (87+i)) 31 (87+i) = true := by decide +kernel

theorem strictBool_r31_part88 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (88+i)) 31 (88+i) = true := by decide +kernel

theorem strictBool_r31_part89 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (89+i)) 31 (89+i) = true := by decide +kernel

theorem strictBool_r31_part90 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (90+i)) 31 (90+i) = true := by decide +kernel

theorem strictBool_r31_part91 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (91+i)) 31 (91+i) = true := by decide +kernel

theorem strictBool_r31_part92 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (92+i)) 31 (92+i) = true := by decide +kernel

theorem strictBool_r31_part93 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (93+i)) 31 (93+i) = true := by decide +kernel

theorem strictBool_r31_part94 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (94+i)) 31 (94+i) = true := by decide +kernel

theorem strictBool_r31_part95 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (95+i)) 31 (95+i) = true := by decide +kernel

theorem strictBool_r31_part96 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (96+i)) 31 (96+i) = true := by decide +kernel

theorem strictBool_r31_part97 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (97+i)) 31 (97+i) = true := by decide +kernel

theorem strictBool_r31_part98 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (98+i)) 31 (98+i) = true := by decide +kernel

theorem strictBool_r31_part99 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (99+i)) 31 (99+i) = true := by decide +kernel

theorem strictBool_r31_part100 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (100+i)) 31 (100+i) = true := by decide +kernel

theorem strictBool_r31_part101 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (101+i)) 31 (101+i) = true := by decide +kernel

theorem strictBool_r31_part102 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (102+i)) 31 (102+i) = true := by decide +kernel

theorem strictBool_r31_part103 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (103+i)) 31 (103+i) = true := by decide +kernel

theorem strictBool_r31_part104 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (104+i)) 31 (104+i) = true := by decide +kernel

theorem strictBool_r31_part105 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (105+i)) 31 (105+i) = true := by decide +kernel

theorem strictBool_r31_part106 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (106+i)) 31 (106+i) = true := by decide +kernel

theorem strictBool_r31_part107 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (107+i)) 31 (107+i) = true := by decide +kernel

theorem strictBool_r31_part108 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (108+i)) 31 (108+i) = true := by decide +kernel

theorem strictBool_r31_part109 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (109+i)) 31 (109+i) = true := by decide +kernel

theorem strictBool_r31_part110 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (110+i)) 31 (110+i) = true := by decide +kernel

theorem strictBool_r31_part111 : ∀ i ∈ List.range 1, strictBool (BoundaryTailBaseFastData.row 31 (111+i)) 31 (111+i) = true := by decide +kernel

theorem strictBool_r31 (V : ℕ) (hV : V ∈ List.range 112) : strictBool (BoundaryTailBaseFastData.row 31 V) 31 V = true := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have hi := strictBool_r31_part0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
            · by_cases h1_3 : V < 2
              · have hi := strictBool_r31_part1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using hi
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have hi := strictBool_r31_part3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hi
            · by_cases h5_7 : V < 6
              · have hi := strictBool_r31_part5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using hi
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have hi := strictBool_r31_part7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using hi
            · by_cases h8_10 : V < 9
              · have hi := strictBool_r31_part8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using hi
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have hi := strictBool_r31_part10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using hi
            · by_cases h12_14 : V < 13
              · have hi := strictBool_r31_part12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using hi
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have hi := strictBool_r31_part14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using hi
            · by_cases h15_17 : V < 16
              · have hi := strictBool_r31_part15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have hi := strictBool_r31_part17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using hi
            · by_cases h19_21 : V < 20
              · have hi := strictBool_r31_part19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hi
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have hi := strictBool_r31_part21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using hi
            · by_cases h22_24 : V < 23
              · have hi := strictBool_r31_part22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using hi
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have hi := strictBool_r31_part24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using hi
            · by_cases h26_28 : V < 27
              · have hi := strictBool_r31_part26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using hi
    · by_cases h28_56 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have hi := strictBool_r31_part28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hi
            · by_cases h29_31 : V < 30
              · have hi := strictBool_r31_part29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using hi
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have hi := strictBool_r31_part31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
            · by_cases h33_35 : V < 34
              · have hi := strictBool_r31_part33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using hi
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have hi := strictBool_r31_part35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using hi
            · by_cases h36_38 : V < 37
              · have hi := strictBool_r31_part36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using hi
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have hi := strictBool_r31_part38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using hi
            · by_cases h40_42 : V < 41
              · have hi := strictBool_r31_part40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using hi
      · by_cases h42_56 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have hi := strictBool_r31_part42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using hi
            · by_cases h43_45 : V < 44
              · have hi := strictBool_r31_part43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hi
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have hi := strictBool_r31_part45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using hi
            · by_cases h47_49 : V < 48
              · have hi := strictBool_r31_part47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h49_56 : V < 52
          · by_cases h49_52 : V < 50
            · have hi := strictBool_r31_part49 (V-49) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using hi
            · by_cases h50_52 : V < 51
              · have hi := strictBool_r31_part50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using hi
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have hi := strictBool_r31_part52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using hi
            · by_cases h54_56 : V < 55
              · have hi := strictBool_r31_part54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 84
    · by_cases h56_84 : V < 70
      · by_cases h56_70 : V < 63
        · by_cases h56_63 : V < 59
          · by_cases h56_59 : V < 57
            · have hi := strictBool_r31_part56 (V-56) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
            · by_cases h57_59 : V < 58
              · have hi := strictBool_r31_part57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using hi
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have hi := strictBool_r31_part59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hi
            · by_cases h61_63 : V < 62
              · have hi := strictBool_r31_part61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using hi
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have hi := strictBool_r31_part63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using hi
            · by_cases h64_66 : V < 65
              · have hi := strictBool_r31_part64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using hi
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have hi := strictBool_r31_part66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using hi
            · by_cases h68_70 : V < 69
              · have hi := strictBool_r31_part68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using hi
      · by_cases h70_84 : V < 77
        · by_cases h70_77 : V < 73
          · by_cases h70_73 : V < 71
            · have hi := strictBool_r31_part70 (V-70) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using hi
            · by_cases h71_73 : V < 72
              · have hi := strictBool_r31_part71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have hi := strictBool_r31_part73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using hi
            · by_cases h75_77 : V < 76
              · have hi := strictBool_r31_part75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hi
        · by_cases h77_84 : V < 80
          · by_cases h77_80 : V < 78
            · have hi := strictBool_r31_part77 (V-77) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using hi
            · by_cases h78_80 : V < 79
              · have hi := strictBool_r31_part78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using hi
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have hi := strictBool_r31_part80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using hi
            · by_cases h82_84 : V < 83
              · have hi := strictBool_r31_part82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using hi
    · by_cases h84_112 : V < 98
      · by_cases h84_98 : V < 91
        · by_cases h84_91 : V < 87
          · by_cases h84_87 : V < 85
            · have hi := strictBool_r31_part84 (V-84) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hi
            · by_cases h85_87 : V < 86
              · have hi := strictBool_r31_part85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using hi
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have hi := strictBool_r31_part87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
            · by_cases h89_91 : V < 90
              · have hi := strictBool_r31_part89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using hi
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have hi := strictBool_r31_part91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using hi
            · by_cases h92_94 : V < 93
              · have hi := strictBool_r31_part92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using hi
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have hi := strictBool_r31_part94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using hi
            · by_cases h96_98 : V < 97
              · have hi := strictBool_r31_part96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using hi
      · by_cases h98_112 : V < 105
        · by_cases h98_105 : V < 101
          · by_cases h98_101 : V < 99
            · have hi := strictBool_r31_part98 (V-98) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using hi
            · by_cases h99_101 : V < 100
              · have hi := strictBool_r31_part99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hi
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have hi := strictBool_r31_part101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using hi
            · by_cases h103_105 : V < 104
              · have hi := strictBool_r31_part103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · by_cases h105_112 : V < 108
          · by_cases h105_108 : V < 106
            · have hi := strictBool_r31_part105 (V-105) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using hi
            · by_cases h106_108 : V < 107
              · have hi := strictBool_r31_part106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using hi
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have hi := strictBool_r31_part108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using hi
            · by_cases h110_112 : V < 111
              · have hi := strictBool_r31_part110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using hi
              · have hi := strictBool_r31_part111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using hi

theorem strictFast_r31 (V : ℕ) (hV : V ∈ List.range 112) : StrictAtFast (BoundaryTailBaseFastData.row 31 V) 31 V :=
  strictBool_sound _ _ _ (strictBool_r31 V hV)

theorem strict_r31 (V : ℕ) (hV : V ∈ List.range 112) : StrictCheckAt 31 V :=
  strictAtFast_sound _ _ _ (valid_r31 V hV) (strictFast_r31 V hV)

theorem zeroCertificate_r31_part0 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (0+i)) 31 (0+i) := by decide +kernel

theorem zeroCertificate_r31_part8 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (8+i)) 31 (8+i) := by decide +kernel

theorem zeroCertificate_r31_part16 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (16+i)) 31 (16+i) := by decide +kernel

theorem zeroCertificate_r31_part24 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (24+i)) 31 (24+i) := by decide +kernel

theorem zeroCertificate_r31_part32 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (32+i)) 31 (32+i) := by decide +kernel

theorem zeroCertificate_r31_part40 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (40+i)) 31 (40+i) := by decide +kernel

theorem zeroCertificate_r31_part48 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (48+i)) 31 (48+i) := by decide +kernel

theorem zeroCertificate_r31_part56 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (56+i)) 31 (56+i) := by decide +kernel

theorem zeroCertificate_r31_part64 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (64+i)) 31 (64+i) := by decide +kernel

theorem zeroCertificate_r31_part72 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (72+i)) 31 (72+i) := by decide +kernel

theorem zeroCertificate_r31_part80 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (80+i)) 31 (80+i) := by decide +kernel

theorem zeroCertificate_r31_part88 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (88+i)) 31 (88+i) := by decide +kernel

theorem zeroCertificate_r31_part96 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (96+i)) 31 (96+i) := by decide +kernel

theorem zeroCertificate_r31_part104 : ∀ i ∈ List.range 8, ZeroCertificate (BoundaryTailBaseFastData.row 31 (104+i)) 31 (104+i) := by decide +kernel

theorem zeroCertificate_r31 (V : ℕ) (hV : V ∈ List.range 112) : ZeroCertificate (BoundaryTailBaseFastData.row 31 V) 31 V := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := zeroCertificate_r31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := zeroCertificate_r31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := zeroCertificate_r31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := zeroCertificate_r31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := zeroCertificate_r31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := zeroCertificate_r31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := zeroCertificate_r31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := zeroCertificate_r31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := zeroCertificate_r31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

theorem zeroFast_r31 (V : ℕ) (hV : V ∈ List.range 112) : ZeroAtFast 31 V :=
  zeroAtFast_of_strict _ _ _ (strictFast_r31 V hV) (zeroCertificate_r31 V hV)

theorem zero_r31 (V : ℕ) (hV : V ∈ List.range 112) : ZeroCheckAt 31 V :=
  zeroAtFast_sound _ _ (zeroFast_r31 V hV)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
