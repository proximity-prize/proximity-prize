import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r1_part0 : ∀ i ∈ List.range 8, RunsAt 1 (0+i) := by decide +kernel

theorem runs_r1_part8 : ∀ i ∈ List.range 8, RunsAt 1 (8+i) := by decide +kernel

theorem runs_r1_part16 : ∀ i ∈ List.range 8, RunsAt 1 (16+i) := by decide +kernel

theorem runs_r1_part24 : ∀ i ∈ List.range 8, RunsAt 1 (24+i) := by decide +kernel

theorem runs_r1_part32 : ∀ i ∈ List.range 8, RunsAt 1 (32+i) := by decide +kernel

theorem runs_r1_part40 : ∀ i ∈ List.range 8, RunsAt 1 (40+i) := by decide +kernel

theorem runs_r1_part48 : ∀ i ∈ List.range 8, RunsAt 1 (48+i) := by decide +kernel

theorem runs_r1_part56 : ∀ i ∈ List.range 8, RunsAt 1 (56+i) := by decide +kernel

theorem runs_r1_part64 : ∀ i ∈ List.range 8, RunsAt 1 (64+i) := by decide +kernel

theorem runs_r1_part72 : ∀ i ∈ List.range 8, RunsAt 1 (72+i) := by decide +kernel

theorem runs_r1_part80 : ∀ i ∈ List.range 8, RunsAt 1 (80+i) := by decide +kernel

theorem runs_r1_part88 : ∀ i ∈ List.range 8, RunsAt 1 (88+i) := by decide +kernel

theorem runs_r1_part96 : ∀ i ∈ List.range 8, RunsAt 1 (96+i) := by decide +kernel

theorem runs_r1_part104 : ∀ i ∈ List.range 8, RunsAt 1 (104+i) := by decide +kernel

theorem runs_r1_part112 : ∀ i ∈ List.range 8, RunsAt 1 (112+i) := by decide +kernel

theorem runs_r1_part120 : ∀ i ∈ List.range 8, RunsAt 1 (120+i) := by decide +kernel

theorem runs_r1_part128 : ∀ i ∈ List.range 8, RunsAt 1 (128+i) := by decide +kernel

theorem runs_r1_part136 : ∀ i ∈ List.range 6, RunsAt 1 (136+i) := by decide +kernel

theorem runs_r1 (V : ℕ) (hV : V ∈ List.range 142) : RunsAt 1 V := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := runs_r1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := runs_r1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r2_part0 : ∀ i ∈ List.range 8, RunsAt 2 (0+i) := by decide +kernel

theorem runs_r2_part8 : ∀ i ∈ List.range 8, RunsAt 2 (8+i) := by decide +kernel

theorem runs_r2_part16 : ∀ i ∈ List.range 8, RunsAt 2 (16+i) := by decide +kernel

theorem runs_r2_part24 : ∀ i ∈ List.range 8, RunsAt 2 (24+i) := by decide +kernel

theorem runs_r2_part32 : ∀ i ∈ List.range 8, RunsAt 2 (32+i) := by decide +kernel

theorem runs_r2_part40 : ∀ i ∈ List.range 8, RunsAt 2 (40+i) := by decide +kernel

theorem runs_r2_part48 : ∀ i ∈ List.range 8, RunsAt 2 (48+i) := by decide +kernel

theorem runs_r2_part56 : ∀ i ∈ List.range 8, RunsAt 2 (56+i) := by decide +kernel

theorem runs_r2_part64 : ∀ i ∈ List.range 8, RunsAt 2 (64+i) := by decide +kernel

theorem runs_r2_part72 : ∀ i ∈ List.range 8, RunsAt 2 (72+i) := by decide +kernel

theorem runs_r2_part80 : ∀ i ∈ List.range 8, RunsAt 2 (80+i) := by decide +kernel

theorem runs_r2_part88 : ∀ i ∈ List.range 8, RunsAt 2 (88+i) := by decide +kernel

theorem runs_r2_part96 : ∀ i ∈ List.range 8, RunsAt 2 (96+i) := by decide +kernel

theorem runs_r2_part104 : ∀ i ∈ List.range 8, RunsAt 2 (104+i) := by decide +kernel

theorem runs_r2_part112 : ∀ i ∈ List.range 8, RunsAt 2 (112+i) := by decide +kernel

theorem runs_r2_part120 : ∀ i ∈ List.range 8, RunsAt 2 (120+i) := by decide +kernel

theorem runs_r2_part128 : ∀ i ∈ List.range 8, RunsAt 2 (128+i) := by decide +kernel

theorem runs_r2_part136 : ∀ i ∈ List.range 5, RunsAt 2 (136+i) := by decide +kernel

theorem runs_r2 (V : ℕ) (hV : V ∈ List.range 141) : RunsAt 2 V := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := runs_r2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := runs_r2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r3_part0 : ∀ i ∈ List.range 8, RunsAt 3 (0+i) := by decide +kernel

theorem runs_r3_part8 : ∀ i ∈ List.range 8, RunsAt 3 (8+i) := by decide +kernel

theorem runs_r3_part16 : ∀ i ∈ List.range 8, RunsAt 3 (16+i) := by decide +kernel

theorem runs_r3_part24 : ∀ i ∈ List.range 8, RunsAt 3 (24+i) := by decide +kernel

theorem runs_r3_part32 : ∀ i ∈ List.range 8, RunsAt 3 (32+i) := by decide +kernel

theorem runs_r3_part40 : ∀ i ∈ List.range 8, RunsAt 3 (40+i) := by decide +kernel

theorem runs_r3_part48 : ∀ i ∈ List.range 8, RunsAt 3 (48+i) := by decide +kernel

theorem runs_r3_part56 : ∀ i ∈ List.range 8, RunsAt 3 (56+i) := by decide +kernel

theorem runs_r3_part64 : ∀ i ∈ List.range 8, RunsAt 3 (64+i) := by decide +kernel

theorem runs_r3_part72 : ∀ i ∈ List.range 8, RunsAt 3 (72+i) := by decide +kernel

theorem runs_r3_part80 : ∀ i ∈ List.range 8, RunsAt 3 (80+i) := by decide +kernel

theorem runs_r3_part88 : ∀ i ∈ List.range 8, RunsAt 3 (88+i) := by decide +kernel

theorem runs_r3_part96 : ∀ i ∈ List.range 8, RunsAt 3 (96+i) := by decide +kernel

theorem runs_r3_part104 : ∀ i ∈ List.range 8, RunsAt 3 (104+i) := by decide +kernel

theorem runs_r3_part112 : ∀ i ∈ List.range 8, RunsAt 3 (112+i) := by decide +kernel

theorem runs_r3_part120 : ∀ i ∈ List.range 8, RunsAt 3 (120+i) := by decide +kernel

theorem runs_r3_part128 : ∀ i ∈ List.range 8, RunsAt 3 (128+i) := by decide +kernel

theorem runs_r3_part136 : ∀ i ∈ List.range 4, RunsAt 3 (136+i) := by decide +kernel

theorem runs_r3 (V : ℕ) (hV : V ∈ List.range 140) : RunsAt 3 V := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := runs_r3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := runs_r3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r4_part0 : ∀ i ∈ List.range 8, RunsAt 4 (0+i) := by decide +kernel

theorem runs_r4_part8 : ∀ i ∈ List.range 8, RunsAt 4 (8+i) := by decide +kernel

theorem runs_r4_part16 : ∀ i ∈ List.range 8, RunsAt 4 (16+i) := by decide +kernel

theorem runs_r4_part24 : ∀ i ∈ List.range 8, RunsAt 4 (24+i) := by decide +kernel

theorem runs_r4_part32 : ∀ i ∈ List.range 8, RunsAt 4 (32+i) := by decide +kernel

theorem runs_r4_part40 : ∀ i ∈ List.range 8, RunsAt 4 (40+i) := by decide +kernel

theorem runs_r4_part48 : ∀ i ∈ List.range 8, RunsAt 4 (48+i) := by decide +kernel

theorem runs_r4_part56 : ∀ i ∈ List.range 8, RunsAt 4 (56+i) := by decide +kernel

theorem runs_r4_part64 : ∀ i ∈ List.range 8, RunsAt 4 (64+i) := by decide +kernel

theorem runs_r4_part72 : ∀ i ∈ List.range 8, RunsAt 4 (72+i) := by decide +kernel

theorem runs_r4_part80 : ∀ i ∈ List.range 8, RunsAt 4 (80+i) := by decide +kernel

theorem runs_r4_part88 : ∀ i ∈ List.range 8, RunsAt 4 (88+i) := by decide +kernel

theorem runs_r4_part96 : ∀ i ∈ List.range 8, RunsAt 4 (96+i) := by decide +kernel

theorem runs_r4_part104 : ∀ i ∈ List.range 8, RunsAt 4 (104+i) := by decide +kernel

theorem runs_r4_part112 : ∀ i ∈ List.range 8, RunsAt 4 (112+i) := by decide +kernel

theorem runs_r4_part120 : ∀ i ∈ List.range 8, RunsAt 4 (120+i) := by decide +kernel

theorem runs_r4_part128 : ∀ i ∈ List.range 8, RunsAt 4 (128+i) := by decide +kernel

theorem runs_r4_part136 : ∀ i ∈ List.range 3, RunsAt 4 (136+i) := by decide +kernel

theorem runs_r4 (V : ℕ) (hV : V ∈ List.range 139) : RunsAt 4 V := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := runs_r4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := runs_r4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r5_part0 : ∀ i ∈ List.range 8, RunsAt 5 (0+i) := by decide +kernel

theorem runs_r5_part8 : ∀ i ∈ List.range 8, RunsAt 5 (8+i) := by decide +kernel

theorem runs_r5_part16 : ∀ i ∈ List.range 8, RunsAt 5 (16+i) := by decide +kernel

theorem runs_r5_part24 : ∀ i ∈ List.range 8, RunsAt 5 (24+i) := by decide +kernel

theorem runs_r5_part32 : ∀ i ∈ List.range 8, RunsAt 5 (32+i) := by decide +kernel

theorem runs_r5_part40 : ∀ i ∈ List.range 8, RunsAt 5 (40+i) := by decide +kernel

theorem runs_r5_part48 : ∀ i ∈ List.range 8, RunsAt 5 (48+i) := by decide +kernel

theorem runs_r5_part56 : ∀ i ∈ List.range 8, RunsAt 5 (56+i) := by decide +kernel

theorem runs_r5_part64 : ∀ i ∈ List.range 8, RunsAt 5 (64+i) := by decide +kernel

theorem runs_r5_part72 : ∀ i ∈ List.range 8, RunsAt 5 (72+i) := by decide +kernel

theorem runs_r5_part80 : ∀ i ∈ List.range 8, RunsAt 5 (80+i) := by decide +kernel

theorem runs_r5_part88 : ∀ i ∈ List.range 8, RunsAt 5 (88+i) := by decide +kernel

theorem runs_r5_part96 : ∀ i ∈ List.range 8, RunsAt 5 (96+i) := by decide +kernel

theorem runs_r5_part104 : ∀ i ∈ List.range 8, RunsAt 5 (104+i) := by decide +kernel

theorem runs_r5_part112 : ∀ i ∈ List.range 8, RunsAt 5 (112+i) := by decide +kernel

theorem runs_r5_part120 : ∀ i ∈ List.range 8, RunsAt 5 (120+i) := by decide +kernel

theorem runs_r5_part128 : ∀ i ∈ List.range 8, RunsAt 5 (128+i) := by decide +kernel

theorem runs_r5_part136 : ∀ i ∈ List.range 2, RunsAt 5 (136+i) := by decide +kernel

theorem runs_r5 (V : ℕ) (hV : V ∈ List.range 138) : RunsAt 5 V := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := runs_r5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := runs_r5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r6_part0 : ∀ i ∈ List.range 8, RunsAt 6 (0+i) := by decide +kernel

theorem runs_r6_part8 : ∀ i ∈ List.range 8, RunsAt 6 (8+i) := by decide +kernel

theorem runs_r6_part16 : ∀ i ∈ List.range 8, RunsAt 6 (16+i) := by decide +kernel

theorem runs_r6_part24 : ∀ i ∈ List.range 8, RunsAt 6 (24+i) := by decide +kernel

theorem runs_r6_part32 : ∀ i ∈ List.range 8, RunsAt 6 (32+i) := by decide +kernel

theorem runs_r6_part40 : ∀ i ∈ List.range 8, RunsAt 6 (40+i) := by decide +kernel

theorem runs_r6_part48 : ∀ i ∈ List.range 8, RunsAt 6 (48+i) := by decide +kernel

theorem runs_r6_part56 : ∀ i ∈ List.range 8, RunsAt 6 (56+i) := by decide +kernel

theorem runs_r6_part64 : ∀ i ∈ List.range 8, RunsAt 6 (64+i) := by decide +kernel

theorem runs_r6_part72 : ∀ i ∈ List.range 8, RunsAt 6 (72+i) := by decide +kernel

theorem runs_r6_part80 : ∀ i ∈ List.range 8, RunsAt 6 (80+i) := by decide +kernel

theorem runs_r6_part88 : ∀ i ∈ List.range 8, RunsAt 6 (88+i) := by decide +kernel

theorem runs_r6_part96 : ∀ i ∈ List.range 8, RunsAt 6 (96+i) := by decide +kernel

theorem runs_r6_part104 : ∀ i ∈ List.range 8, RunsAt 6 (104+i) := by decide +kernel

theorem runs_r6_part112 : ∀ i ∈ List.range 8, RunsAt 6 (112+i) := by decide +kernel

theorem runs_r6_part120 : ∀ i ∈ List.range 8, RunsAt 6 (120+i) := by decide +kernel

theorem runs_r6_part128 : ∀ i ∈ List.range 8, RunsAt 6 (128+i) := by decide +kernel

theorem runs_r6_part136 : ∀ i ∈ List.range 1, RunsAt 6 (136+i) := by decide +kernel

theorem runs_r6 (V : ℕ) (hV : V ∈ List.range 137) : RunsAt 6 V := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := runs_r6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := runs_r6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := runs_r6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := runs_r6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := runs_r6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := runs_r6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := runs_r6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := runs_r6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := runs_r6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r7_part0 : ∀ i ∈ List.range 8, RunsAt 7 (0+i) := by decide +kernel

theorem runs_r7_part8 : ∀ i ∈ List.range 8, RunsAt 7 (8+i) := by decide +kernel

theorem runs_r7_part16 : ∀ i ∈ List.range 8, RunsAt 7 (16+i) := by decide +kernel

theorem runs_r7_part24 : ∀ i ∈ List.range 8, RunsAt 7 (24+i) := by decide +kernel

theorem runs_r7_part32 : ∀ i ∈ List.range 8, RunsAt 7 (32+i) := by decide +kernel

theorem runs_r7_part40 : ∀ i ∈ List.range 8, RunsAt 7 (40+i) := by decide +kernel

theorem runs_r7_part48 : ∀ i ∈ List.range 8, RunsAt 7 (48+i) := by decide +kernel

theorem runs_r7_part56 : ∀ i ∈ List.range 8, RunsAt 7 (56+i) := by decide +kernel

theorem runs_r7_part64 : ∀ i ∈ List.range 8, RunsAt 7 (64+i) := by decide +kernel

theorem runs_r7_part72 : ∀ i ∈ List.range 8, RunsAt 7 (72+i) := by decide +kernel

theorem runs_r7_part80 : ∀ i ∈ List.range 8, RunsAt 7 (80+i) := by decide +kernel

theorem runs_r7_part88 : ∀ i ∈ List.range 8, RunsAt 7 (88+i) := by decide +kernel

theorem runs_r7_part96 : ∀ i ∈ List.range 8, RunsAt 7 (96+i) := by decide +kernel

theorem runs_r7_part104 : ∀ i ∈ List.range 8, RunsAt 7 (104+i) := by decide +kernel

theorem runs_r7_part112 : ∀ i ∈ List.range 8, RunsAt 7 (112+i) := by decide +kernel

theorem runs_r7_part120 : ∀ i ∈ List.range 8, RunsAt 7 (120+i) := by decide +kernel

theorem runs_r7_part128 : ∀ i ∈ List.range 8, RunsAt 7 (128+i) := by decide +kernel

theorem runs_r7 (V : ℕ) (hV : V ∈ List.range 136) : RunsAt 7 V := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := runs_r7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := runs_r7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r8_part0 : ∀ i ∈ List.range 8, RunsAt 8 (0+i) := by decide +kernel

theorem runs_r8_part8 : ∀ i ∈ List.range 8, RunsAt 8 (8+i) := by decide +kernel

theorem runs_r8_part16 : ∀ i ∈ List.range 8, RunsAt 8 (16+i) := by decide +kernel

theorem runs_r8_part24 : ∀ i ∈ List.range 8, RunsAt 8 (24+i) := by decide +kernel

theorem runs_r8_part32 : ∀ i ∈ List.range 8, RunsAt 8 (32+i) := by decide +kernel

theorem runs_r8_part40 : ∀ i ∈ List.range 8, RunsAt 8 (40+i) := by decide +kernel

theorem runs_r8_part48 : ∀ i ∈ List.range 8, RunsAt 8 (48+i) := by decide +kernel

theorem runs_r8_part56 : ∀ i ∈ List.range 8, RunsAt 8 (56+i) := by decide +kernel

theorem runs_r8_part64 : ∀ i ∈ List.range 8, RunsAt 8 (64+i) := by decide +kernel

theorem runs_r8_part72 : ∀ i ∈ List.range 8, RunsAt 8 (72+i) := by decide +kernel

theorem runs_r8_part80 : ∀ i ∈ List.range 8, RunsAt 8 (80+i) := by decide +kernel

theorem runs_r8_part88 : ∀ i ∈ List.range 8, RunsAt 8 (88+i) := by decide +kernel

theorem runs_r8_part96 : ∀ i ∈ List.range 8, RunsAt 8 (96+i) := by decide +kernel

theorem runs_r8_part104 : ∀ i ∈ List.range 8, RunsAt 8 (104+i) := by decide +kernel

theorem runs_r8_part112 : ∀ i ∈ List.range 8, RunsAt 8 (112+i) := by decide +kernel

theorem runs_r8_part120 : ∀ i ∈ List.range 8, RunsAt 8 (120+i) := by decide +kernel

theorem runs_r8_part128 : ∀ i ∈ List.range 7, RunsAt 8 (128+i) := by decide +kernel

theorem runs_r8 (V : ℕ) (hV : V ∈ List.range 135) : RunsAt 8 V := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := runs_r8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := runs_r8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r9_part0 : ∀ i ∈ List.range 8, RunsAt 9 (0+i) := by decide +kernel

theorem runs_r9_part8 : ∀ i ∈ List.range 8, RunsAt 9 (8+i) := by decide +kernel

theorem runs_r9_part16 : ∀ i ∈ List.range 8, RunsAt 9 (16+i) := by decide +kernel

theorem runs_r9_part24 : ∀ i ∈ List.range 8, RunsAt 9 (24+i) := by decide +kernel

theorem runs_r9_part32 : ∀ i ∈ List.range 8, RunsAt 9 (32+i) := by decide +kernel

theorem runs_r9_part40 : ∀ i ∈ List.range 8, RunsAt 9 (40+i) := by decide +kernel

theorem runs_r9_part48 : ∀ i ∈ List.range 8, RunsAt 9 (48+i) := by decide +kernel

theorem runs_r9_part56 : ∀ i ∈ List.range 8, RunsAt 9 (56+i) := by decide +kernel

theorem runs_r9_part64 : ∀ i ∈ List.range 8, RunsAt 9 (64+i) := by decide +kernel

theorem runs_r9_part72 : ∀ i ∈ List.range 8, RunsAt 9 (72+i) := by decide +kernel

theorem runs_r9_part80 : ∀ i ∈ List.range 8, RunsAt 9 (80+i) := by decide +kernel

theorem runs_r9_part88 : ∀ i ∈ List.range 8, RunsAt 9 (88+i) := by decide +kernel

theorem runs_r9_part96 : ∀ i ∈ List.range 8, RunsAt 9 (96+i) := by decide +kernel

theorem runs_r9_part104 : ∀ i ∈ List.range 8, RunsAt 9 (104+i) := by decide +kernel

theorem runs_r9_part112 : ∀ i ∈ List.range 8, RunsAt 9 (112+i) := by decide +kernel

theorem runs_r9_part120 : ∀ i ∈ List.range 8, RunsAt 9 (120+i) := by decide +kernel

theorem runs_r9_part128 : ∀ i ∈ List.range 6, RunsAt 9 (128+i) := by decide +kernel

theorem runs_r9 (V : ℕ) (hV : V ∈ List.range 134) : RunsAt 9 V := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := runs_r9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := runs_r9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r10_part0 : ∀ i ∈ List.range 8, RunsAt 10 (0+i) := by decide +kernel

theorem runs_r10_part8 : ∀ i ∈ List.range 8, RunsAt 10 (8+i) := by decide +kernel

theorem runs_r10_part16 : ∀ i ∈ List.range 8, RunsAt 10 (16+i) := by decide +kernel

theorem runs_r10_part24 : ∀ i ∈ List.range 8, RunsAt 10 (24+i) := by decide +kernel

theorem runs_r10_part32 : ∀ i ∈ List.range 8, RunsAt 10 (32+i) := by decide +kernel

theorem runs_r10_part40 : ∀ i ∈ List.range 8, RunsAt 10 (40+i) := by decide +kernel

theorem runs_r10_part48 : ∀ i ∈ List.range 8, RunsAt 10 (48+i) := by decide +kernel

theorem runs_r10_part56 : ∀ i ∈ List.range 8, RunsAt 10 (56+i) := by decide +kernel

theorem runs_r10_part64 : ∀ i ∈ List.range 8, RunsAt 10 (64+i) := by decide +kernel

theorem runs_r10_part72 : ∀ i ∈ List.range 8, RunsAt 10 (72+i) := by decide +kernel

theorem runs_r10_part80 : ∀ i ∈ List.range 8, RunsAt 10 (80+i) := by decide +kernel

theorem runs_r10_part88 : ∀ i ∈ List.range 8, RunsAt 10 (88+i) := by decide +kernel

theorem runs_r10_part96 : ∀ i ∈ List.range 8, RunsAt 10 (96+i) := by decide +kernel

theorem runs_r10_part104 : ∀ i ∈ List.range 8, RunsAt 10 (104+i) := by decide +kernel

theorem runs_r10_part112 : ∀ i ∈ List.range 8, RunsAt 10 (112+i) := by decide +kernel

theorem runs_r10_part120 : ∀ i ∈ List.range 8, RunsAt 10 (120+i) := by decide +kernel

theorem runs_r10_part128 : ∀ i ∈ List.range 5, RunsAt 10 (128+i) := by decide +kernel

theorem runs_r10 (V : ℕ) (hV : V ∈ List.range 133) : RunsAt 10 V := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := runs_r10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := runs_r10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r11_part0 : ∀ i ∈ List.range 8, RunsAt 11 (0+i) := by decide +kernel

theorem runs_r11_part8 : ∀ i ∈ List.range 8, RunsAt 11 (8+i) := by decide +kernel

theorem runs_r11_part16 : ∀ i ∈ List.range 8, RunsAt 11 (16+i) := by decide +kernel

theorem runs_r11_part24 : ∀ i ∈ List.range 8, RunsAt 11 (24+i) := by decide +kernel

theorem runs_r11_part32 : ∀ i ∈ List.range 8, RunsAt 11 (32+i) := by decide +kernel

theorem runs_r11_part40 : ∀ i ∈ List.range 8, RunsAt 11 (40+i) := by decide +kernel

theorem runs_r11_part48 : ∀ i ∈ List.range 8, RunsAt 11 (48+i) := by decide +kernel

theorem runs_r11_part56 : ∀ i ∈ List.range 8, RunsAt 11 (56+i) := by decide +kernel

theorem runs_r11_part64 : ∀ i ∈ List.range 8, RunsAt 11 (64+i) := by decide +kernel

theorem runs_r11_part72 : ∀ i ∈ List.range 8, RunsAt 11 (72+i) := by decide +kernel

theorem runs_r11_part80 : ∀ i ∈ List.range 8, RunsAt 11 (80+i) := by decide +kernel

theorem runs_r11_part88 : ∀ i ∈ List.range 8, RunsAt 11 (88+i) := by decide +kernel

theorem runs_r11_part96 : ∀ i ∈ List.range 8, RunsAt 11 (96+i) := by decide +kernel

theorem runs_r11_part104 : ∀ i ∈ List.range 8, RunsAt 11 (104+i) := by decide +kernel

theorem runs_r11_part112 : ∀ i ∈ List.range 8, RunsAt 11 (112+i) := by decide +kernel

theorem runs_r11_part120 : ∀ i ∈ List.range 8, RunsAt 11 (120+i) := by decide +kernel

theorem runs_r11_part128 : ∀ i ∈ List.range 4, RunsAt 11 (128+i) := by decide +kernel

theorem runs_r11 (V : ℕ) (hV : V ∈ List.range 132) : RunsAt 11 V := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := runs_r11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := runs_r11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r12_part0 : ∀ i ∈ List.range 8, RunsAt 12 (0+i) := by decide +kernel

theorem runs_r12_part8 : ∀ i ∈ List.range 8, RunsAt 12 (8+i) := by decide +kernel

theorem runs_r12_part16 : ∀ i ∈ List.range 8, RunsAt 12 (16+i) := by decide +kernel

theorem runs_r12_part24 : ∀ i ∈ List.range 8, RunsAt 12 (24+i) := by decide +kernel

theorem runs_r12_part32 : ∀ i ∈ List.range 8, RunsAt 12 (32+i) := by decide +kernel

theorem runs_r12_part40 : ∀ i ∈ List.range 8, RunsAt 12 (40+i) := by decide +kernel

theorem runs_r12_part48 : ∀ i ∈ List.range 8, RunsAt 12 (48+i) := by decide +kernel

theorem runs_r12_part56 : ∀ i ∈ List.range 8, RunsAt 12 (56+i) := by decide +kernel

theorem runs_r12_part64 : ∀ i ∈ List.range 8, RunsAt 12 (64+i) := by decide +kernel

theorem runs_r12_part72 : ∀ i ∈ List.range 8, RunsAt 12 (72+i) := by decide +kernel

theorem runs_r12_part80 : ∀ i ∈ List.range 8, RunsAt 12 (80+i) := by decide +kernel

theorem runs_r12_part88 : ∀ i ∈ List.range 8, RunsAt 12 (88+i) := by decide +kernel

theorem runs_r12_part96 : ∀ i ∈ List.range 8, RunsAt 12 (96+i) := by decide +kernel

theorem runs_r12_part104 : ∀ i ∈ List.range 8, RunsAt 12 (104+i) := by decide +kernel

theorem runs_r12_part112 : ∀ i ∈ List.range 8, RunsAt 12 (112+i) := by decide +kernel

theorem runs_r12_part120 : ∀ i ∈ List.range 8, RunsAt 12 (120+i) := by decide +kernel

theorem runs_r12_part128 : ∀ i ∈ List.range 3, RunsAt 12 (128+i) := by decide +kernel

theorem runs_r12 (V : ℕ) (hV : V ∈ List.range 131) : RunsAt 12 V := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := runs_r12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := runs_r12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r13_part0 : ∀ i ∈ List.range 8, RunsAt 13 (0+i) := by decide +kernel

theorem runs_r13_part8 : ∀ i ∈ List.range 8, RunsAt 13 (8+i) := by decide +kernel

theorem runs_r13_part16 : ∀ i ∈ List.range 8, RunsAt 13 (16+i) := by decide +kernel

theorem runs_r13_part24 : ∀ i ∈ List.range 8, RunsAt 13 (24+i) := by decide +kernel

theorem runs_r13_part32 : ∀ i ∈ List.range 8, RunsAt 13 (32+i) := by decide +kernel

theorem runs_r13_part40 : ∀ i ∈ List.range 8, RunsAt 13 (40+i) := by decide +kernel

theorem runs_r13_part48 : ∀ i ∈ List.range 8, RunsAt 13 (48+i) := by decide +kernel

theorem runs_r13_part56 : ∀ i ∈ List.range 8, RunsAt 13 (56+i) := by decide +kernel

theorem runs_r13_part64 : ∀ i ∈ List.range 8, RunsAt 13 (64+i) := by decide +kernel

theorem runs_r13_part72 : ∀ i ∈ List.range 8, RunsAt 13 (72+i) := by decide +kernel

theorem runs_r13_part80 : ∀ i ∈ List.range 8, RunsAt 13 (80+i) := by decide +kernel

theorem runs_r13_part88 : ∀ i ∈ List.range 8, RunsAt 13 (88+i) := by decide +kernel

theorem runs_r13_part96 : ∀ i ∈ List.range 8, RunsAt 13 (96+i) := by decide +kernel

theorem runs_r13_part104 : ∀ i ∈ List.range 8, RunsAt 13 (104+i) := by decide +kernel

theorem runs_r13_part112 : ∀ i ∈ List.range 8, RunsAt 13 (112+i) := by decide +kernel

theorem runs_r13_part120 : ∀ i ∈ List.range 8, RunsAt 13 (120+i) := by decide +kernel

theorem runs_r13_part128 : ∀ i ∈ List.range 2, RunsAt 13 (128+i) := by decide +kernel

theorem runs_r13 (V : ℕ) (hV : V ∈ List.range 130) : RunsAt 13 V := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := runs_r13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := runs_r13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r14_part0 : ∀ i ∈ List.range 8, RunsAt 14 (0+i) := by decide +kernel

theorem runs_r14_part8 : ∀ i ∈ List.range 8, RunsAt 14 (8+i) := by decide +kernel

theorem runs_r14_part16 : ∀ i ∈ List.range 8, RunsAt 14 (16+i) := by decide +kernel

theorem runs_r14_part24 : ∀ i ∈ List.range 8, RunsAt 14 (24+i) := by decide +kernel

theorem runs_r14_part32 : ∀ i ∈ List.range 8, RunsAt 14 (32+i) := by decide +kernel

theorem runs_r14_part40 : ∀ i ∈ List.range 8, RunsAt 14 (40+i) := by decide +kernel

theorem runs_r14_part48 : ∀ i ∈ List.range 8, RunsAt 14 (48+i) := by decide +kernel

theorem runs_r14_part56 : ∀ i ∈ List.range 8, RunsAt 14 (56+i) := by decide +kernel

theorem runs_r14_part64 : ∀ i ∈ List.range 8, RunsAt 14 (64+i) := by decide +kernel

theorem runs_r14_part72 : ∀ i ∈ List.range 8, RunsAt 14 (72+i) := by decide +kernel

theorem runs_r14_part80 : ∀ i ∈ List.range 8, RunsAt 14 (80+i) := by decide +kernel

theorem runs_r14_part88 : ∀ i ∈ List.range 8, RunsAt 14 (88+i) := by decide +kernel

theorem runs_r14_part96 : ∀ i ∈ List.range 8, RunsAt 14 (96+i) := by decide +kernel

theorem runs_r14_part104 : ∀ i ∈ List.range 8, RunsAt 14 (104+i) := by decide +kernel

theorem runs_r14_part112 : ∀ i ∈ List.range 8, RunsAt 14 (112+i) := by decide +kernel

theorem runs_r14_part120 : ∀ i ∈ List.range 8, RunsAt 14 (120+i) := by decide +kernel

theorem runs_r14_part128 : ∀ i ∈ List.range 1, RunsAt 14 (128+i) := by decide +kernel

theorem runs_r14 (V : ℕ) (hV : V ∈ List.range 129) : RunsAt 14 V := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := runs_r14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := runs_r14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := runs_r14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r15_part0 : ∀ i ∈ List.range 8, RunsAt 15 (0+i) := by decide +kernel

theorem runs_r15_part8 : ∀ i ∈ List.range 8, RunsAt 15 (8+i) := by decide +kernel

theorem runs_r15_part16 : ∀ i ∈ List.range 8, RunsAt 15 (16+i) := by decide +kernel

theorem runs_r15_part24 : ∀ i ∈ List.range 8, RunsAt 15 (24+i) := by decide +kernel

theorem runs_r15_part32 : ∀ i ∈ List.range 8, RunsAt 15 (32+i) := by decide +kernel

theorem runs_r15_part40 : ∀ i ∈ List.range 8, RunsAt 15 (40+i) := by decide +kernel

theorem runs_r15_part48 : ∀ i ∈ List.range 8, RunsAt 15 (48+i) := by decide +kernel

theorem runs_r15_part56 : ∀ i ∈ List.range 8, RunsAt 15 (56+i) := by decide +kernel

theorem runs_r15_part64 : ∀ i ∈ List.range 8, RunsAt 15 (64+i) := by decide +kernel

theorem runs_r15_part72 : ∀ i ∈ List.range 8, RunsAt 15 (72+i) := by decide +kernel

theorem runs_r15_part80 : ∀ i ∈ List.range 8, RunsAt 15 (80+i) := by decide +kernel

theorem runs_r15_part88 : ∀ i ∈ List.range 8, RunsAt 15 (88+i) := by decide +kernel

theorem runs_r15_part96 : ∀ i ∈ List.range 8, RunsAt 15 (96+i) := by decide +kernel

theorem runs_r15_part104 : ∀ i ∈ List.range 8, RunsAt 15 (104+i) := by decide +kernel

theorem runs_r15_part112 : ∀ i ∈ List.range 8, RunsAt 15 (112+i) := by decide +kernel

theorem runs_r15_part120 : ∀ i ∈ List.range 8, RunsAt 15 (120+i) := by decide +kernel

theorem runs_r15 (V : ℕ) (hV : V ∈ List.range 128) : RunsAt 15 V := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := runs_r15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r16_part0 : ∀ i ∈ List.range 8, RunsAt 16 (0+i) := by decide +kernel

theorem runs_r16_part8 : ∀ i ∈ List.range 8, RunsAt 16 (8+i) := by decide +kernel

theorem runs_r16_part16 : ∀ i ∈ List.range 8, RunsAt 16 (16+i) := by decide +kernel

theorem runs_r16_part24 : ∀ i ∈ List.range 8, RunsAt 16 (24+i) := by decide +kernel

theorem runs_r16_part32 : ∀ i ∈ List.range 8, RunsAt 16 (32+i) := by decide +kernel

theorem runs_r16_part40 : ∀ i ∈ List.range 8, RunsAt 16 (40+i) := by decide +kernel

theorem runs_r16_part48 : ∀ i ∈ List.range 8, RunsAt 16 (48+i) := by decide +kernel

theorem runs_r16_part56 : ∀ i ∈ List.range 8, RunsAt 16 (56+i) := by decide +kernel

theorem runs_r16_part64 : ∀ i ∈ List.range 8, RunsAt 16 (64+i) := by decide +kernel

theorem runs_r16_part72 : ∀ i ∈ List.range 8, RunsAt 16 (72+i) := by decide +kernel

theorem runs_r16_part80 : ∀ i ∈ List.range 8, RunsAt 16 (80+i) := by decide +kernel

theorem runs_r16_part88 : ∀ i ∈ List.range 8, RunsAt 16 (88+i) := by decide +kernel

theorem runs_r16_part96 : ∀ i ∈ List.range 8, RunsAt 16 (96+i) := by decide +kernel

theorem runs_r16_part104 : ∀ i ∈ List.range 8, RunsAt 16 (104+i) := by decide +kernel

theorem runs_r16_part112 : ∀ i ∈ List.range 8, RunsAt 16 (112+i) := by decide +kernel

theorem runs_r16_part120 : ∀ i ∈ List.range 7, RunsAt 16 (120+i) := by decide +kernel

theorem runs_r16 (V : ℕ) (hV : V ∈ List.range 127) : RunsAt 16 V := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := runs_r16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r17_part0 : ∀ i ∈ List.range 8, RunsAt 17 (0+i) := by decide +kernel

theorem runs_r17_part8 : ∀ i ∈ List.range 8, RunsAt 17 (8+i) := by decide +kernel

theorem runs_r17_part16 : ∀ i ∈ List.range 8, RunsAt 17 (16+i) := by decide +kernel

theorem runs_r17_part24 : ∀ i ∈ List.range 8, RunsAt 17 (24+i) := by decide +kernel

theorem runs_r17_part32 : ∀ i ∈ List.range 8, RunsAt 17 (32+i) := by decide +kernel

theorem runs_r17_part40 : ∀ i ∈ List.range 8, RunsAt 17 (40+i) := by decide +kernel

theorem runs_r17_part48 : ∀ i ∈ List.range 8, RunsAt 17 (48+i) := by decide +kernel

theorem runs_r17_part56 : ∀ i ∈ List.range 8, RunsAt 17 (56+i) := by decide +kernel

theorem runs_r17_part64 : ∀ i ∈ List.range 8, RunsAt 17 (64+i) := by decide +kernel

theorem runs_r17_part72 : ∀ i ∈ List.range 8, RunsAt 17 (72+i) := by decide +kernel

theorem runs_r17_part80 : ∀ i ∈ List.range 8, RunsAt 17 (80+i) := by decide +kernel

theorem runs_r17_part88 : ∀ i ∈ List.range 8, RunsAt 17 (88+i) := by decide +kernel

theorem runs_r17_part96 : ∀ i ∈ List.range 8, RunsAt 17 (96+i) := by decide +kernel

theorem runs_r17_part104 : ∀ i ∈ List.range 8, RunsAt 17 (104+i) := by decide +kernel

theorem runs_r17_part112 : ∀ i ∈ List.range 8, RunsAt 17 (112+i) := by decide +kernel

theorem runs_r17_part120 : ∀ i ∈ List.range 6, RunsAt 17 (120+i) := by decide +kernel

theorem runs_r17 (V : ℕ) (hV : V ∈ List.range 126) : RunsAt 17 V := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := runs_r17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r18_part0 : ∀ i ∈ List.range 8, RunsAt 18 (0+i) := by decide +kernel

theorem runs_r18_part8 : ∀ i ∈ List.range 8, RunsAt 18 (8+i) := by decide +kernel

theorem runs_r18_part16 : ∀ i ∈ List.range 8, RunsAt 18 (16+i) := by decide +kernel

theorem runs_r18_part24 : ∀ i ∈ List.range 8, RunsAt 18 (24+i) := by decide +kernel

theorem runs_r18_part32 : ∀ i ∈ List.range 8, RunsAt 18 (32+i) := by decide +kernel

theorem runs_r18_part40 : ∀ i ∈ List.range 8, RunsAt 18 (40+i) := by decide +kernel

theorem runs_r18_part48 : ∀ i ∈ List.range 8, RunsAt 18 (48+i) := by decide +kernel

theorem runs_r18_part56 : ∀ i ∈ List.range 8, RunsAt 18 (56+i) := by decide +kernel

theorem runs_r18_part64 : ∀ i ∈ List.range 8, RunsAt 18 (64+i) := by decide +kernel

theorem runs_r18_part72 : ∀ i ∈ List.range 8, RunsAt 18 (72+i) := by decide +kernel

theorem runs_r18_part80 : ∀ i ∈ List.range 8, RunsAt 18 (80+i) := by decide +kernel

theorem runs_r18_part88 : ∀ i ∈ List.range 8, RunsAt 18 (88+i) := by decide +kernel

theorem runs_r18_part96 : ∀ i ∈ List.range 8, RunsAt 18 (96+i) := by decide +kernel

theorem runs_r18_part104 : ∀ i ∈ List.range 8, RunsAt 18 (104+i) := by decide +kernel

theorem runs_r18_part112 : ∀ i ∈ List.range 8, RunsAt 18 (112+i) := by decide +kernel

theorem runs_r18_part120 : ∀ i ∈ List.range 5, RunsAt 18 (120+i) := by decide +kernel

theorem runs_r18 (V : ℕ) (hV : V ∈ List.range 125) : RunsAt 18 V := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := runs_r18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r19_part0 : ∀ i ∈ List.range 8, RunsAt 19 (0+i) := by decide +kernel

theorem runs_r19_part8 : ∀ i ∈ List.range 8, RunsAt 19 (8+i) := by decide +kernel

theorem runs_r19_part16 : ∀ i ∈ List.range 8, RunsAt 19 (16+i) := by decide +kernel

theorem runs_r19_part24 : ∀ i ∈ List.range 8, RunsAt 19 (24+i) := by decide +kernel

theorem runs_r19_part32 : ∀ i ∈ List.range 8, RunsAt 19 (32+i) := by decide +kernel

theorem runs_r19_part40 : ∀ i ∈ List.range 8, RunsAt 19 (40+i) := by decide +kernel

theorem runs_r19_part48 : ∀ i ∈ List.range 8, RunsAt 19 (48+i) := by decide +kernel

theorem runs_r19_part56 : ∀ i ∈ List.range 8, RunsAt 19 (56+i) := by decide +kernel

theorem runs_r19_part64 : ∀ i ∈ List.range 8, RunsAt 19 (64+i) := by decide +kernel

theorem runs_r19_part72 : ∀ i ∈ List.range 8, RunsAt 19 (72+i) := by decide +kernel

theorem runs_r19_part80 : ∀ i ∈ List.range 8, RunsAt 19 (80+i) := by decide +kernel

theorem runs_r19_part88 : ∀ i ∈ List.range 8, RunsAt 19 (88+i) := by decide +kernel

theorem runs_r19_part96 : ∀ i ∈ List.range 8, RunsAt 19 (96+i) := by decide +kernel

theorem runs_r19_part104 : ∀ i ∈ List.range 8, RunsAt 19 (104+i) := by decide +kernel

theorem runs_r19_part112 : ∀ i ∈ List.range 8, RunsAt 19 (112+i) := by decide +kernel

theorem runs_r19_part120 : ∀ i ∈ List.range 4, RunsAt 19 (120+i) := by decide +kernel

theorem runs_r19 (V : ℕ) (hV : V ∈ List.range 124) : RunsAt 19 V := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := runs_r19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r20_part0 : ∀ i ∈ List.range 8, RunsAt 20 (0+i) := by decide +kernel

theorem runs_r20_part8 : ∀ i ∈ List.range 8, RunsAt 20 (8+i) := by decide +kernel

theorem runs_r20_part16 : ∀ i ∈ List.range 8, RunsAt 20 (16+i) := by decide +kernel

theorem runs_r20_part24 : ∀ i ∈ List.range 8, RunsAt 20 (24+i) := by decide +kernel

theorem runs_r20_part32 : ∀ i ∈ List.range 8, RunsAt 20 (32+i) := by decide +kernel

theorem runs_r20_part40 : ∀ i ∈ List.range 8, RunsAt 20 (40+i) := by decide +kernel

theorem runs_r20_part48 : ∀ i ∈ List.range 8, RunsAt 20 (48+i) := by decide +kernel

theorem runs_r20_part56 : ∀ i ∈ List.range 8, RunsAt 20 (56+i) := by decide +kernel

theorem runs_r20_part64 : ∀ i ∈ List.range 8, RunsAt 20 (64+i) := by decide +kernel

theorem runs_r20_part72 : ∀ i ∈ List.range 8, RunsAt 20 (72+i) := by decide +kernel

theorem runs_r20_part80 : ∀ i ∈ List.range 8, RunsAt 20 (80+i) := by decide +kernel

theorem runs_r20_part88 : ∀ i ∈ List.range 8, RunsAt 20 (88+i) := by decide +kernel

theorem runs_r20_part96 : ∀ i ∈ List.range 8, RunsAt 20 (96+i) := by decide +kernel

theorem runs_r20_part104 : ∀ i ∈ List.range 8, RunsAt 20 (104+i) := by decide +kernel

theorem runs_r20_part112 : ∀ i ∈ List.range 8, RunsAt 20 (112+i) := by decide +kernel

theorem runs_r20_part120 : ∀ i ∈ List.range 3, RunsAt 20 (120+i) := by decide +kernel

theorem runs_r20 (V : ℕ) (hV : V ∈ List.range 123) : RunsAt 20 V := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := runs_r20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r21_part0 : ∀ i ∈ List.range 8, RunsAt 21 (0+i) := by decide +kernel

theorem runs_r21_part8 : ∀ i ∈ List.range 8, RunsAt 21 (8+i) := by decide +kernel

theorem runs_r21_part16 : ∀ i ∈ List.range 8, RunsAt 21 (16+i) := by decide +kernel

theorem runs_r21_part24 : ∀ i ∈ List.range 8, RunsAt 21 (24+i) := by decide +kernel

theorem runs_r21_part32 : ∀ i ∈ List.range 8, RunsAt 21 (32+i) := by decide +kernel

theorem runs_r21_part40 : ∀ i ∈ List.range 8, RunsAt 21 (40+i) := by decide +kernel

theorem runs_r21_part48 : ∀ i ∈ List.range 8, RunsAt 21 (48+i) := by decide +kernel

theorem runs_r21_part56 : ∀ i ∈ List.range 8, RunsAt 21 (56+i) := by decide +kernel

theorem runs_r21_part64 : ∀ i ∈ List.range 8, RunsAt 21 (64+i) := by decide +kernel

theorem runs_r21_part72 : ∀ i ∈ List.range 8, RunsAt 21 (72+i) := by decide +kernel

theorem runs_r21_part80 : ∀ i ∈ List.range 8, RunsAt 21 (80+i) := by decide +kernel

theorem runs_r21_part88 : ∀ i ∈ List.range 8, RunsAt 21 (88+i) := by decide +kernel

theorem runs_r21_part96 : ∀ i ∈ List.range 8, RunsAt 21 (96+i) := by decide +kernel

theorem runs_r21_part104 : ∀ i ∈ List.range 8, RunsAt 21 (104+i) := by decide +kernel

theorem runs_r21_part112 : ∀ i ∈ List.range 8, RunsAt 21 (112+i) := by decide +kernel

theorem runs_r21_part120 : ∀ i ∈ List.range 2, RunsAt 21 (120+i) := by decide +kernel

theorem runs_r21 (V : ℕ) (hV : V ∈ List.range 122) : RunsAt 21 V := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := runs_r21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r22_part0 : ∀ i ∈ List.range 8, RunsAt 22 (0+i) := by decide +kernel

theorem runs_r22_part8 : ∀ i ∈ List.range 8, RunsAt 22 (8+i) := by decide +kernel

theorem runs_r22_part16 : ∀ i ∈ List.range 8, RunsAt 22 (16+i) := by decide +kernel

theorem runs_r22_part24 : ∀ i ∈ List.range 8, RunsAt 22 (24+i) := by decide +kernel

theorem runs_r22_part32 : ∀ i ∈ List.range 8, RunsAt 22 (32+i) := by decide +kernel

theorem runs_r22_part40 : ∀ i ∈ List.range 8, RunsAt 22 (40+i) := by decide +kernel

theorem runs_r22_part48 : ∀ i ∈ List.range 8, RunsAt 22 (48+i) := by decide +kernel

theorem runs_r22_part56 : ∀ i ∈ List.range 8, RunsAt 22 (56+i) := by decide +kernel

theorem runs_r22_part64 : ∀ i ∈ List.range 8, RunsAt 22 (64+i) := by decide +kernel

theorem runs_r22_part72 : ∀ i ∈ List.range 8, RunsAt 22 (72+i) := by decide +kernel

theorem runs_r22_part80 : ∀ i ∈ List.range 8, RunsAt 22 (80+i) := by decide +kernel

theorem runs_r22_part88 : ∀ i ∈ List.range 8, RunsAt 22 (88+i) := by decide +kernel

theorem runs_r22_part96 : ∀ i ∈ List.range 8, RunsAt 22 (96+i) := by decide +kernel

theorem runs_r22_part104 : ∀ i ∈ List.range 8, RunsAt 22 (104+i) := by decide +kernel

theorem runs_r22_part112 : ∀ i ∈ List.range 8, RunsAt 22 (112+i) := by decide +kernel

theorem runs_r22_part120 : ∀ i ∈ List.range 1, RunsAt 22 (120+i) := by decide +kernel

theorem runs_r22 (V : ℕ) (hV : V ∈ List.range 121) : RunsAt 22 V := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := runs_r22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := runs_r22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := runs_r22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := runs_r22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := runs_r22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := runs_r22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := runs_r22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := runs_r22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := runs_r22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := runs_r22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := runs_r22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := runs_r22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := runs_r22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r23_part0 : ∀ i ∈ List.range 8, RunsAt 23 (0+i) := by decide +kernel

theorem runs_r23_part8 : ∀ i ∈ List.range 8, RunsAt 23 (8+i) := by decide +kernel

theorem runs_r23_part16 : ∀ i ∈ List.range 8, RunsAt 23 (16+i) := by decide +kernel

theorem runs_r23_part24 : ∀ i ∈ List.range 8, RunsAt 23 (24+i) := by decide +kernel

theorem runs_r23_part32 : ∀ i ∈ List.range 8, RunsAt 23 (32+i) := by decide +kernel

theorem runs_r23_part40 : ∀ i ∈ List.range 8, RunsAt 23 (40+i) := by decide +kernel

theorem runs_r23_part48 : ∀ i ∈ List.range 8, RunsAt 23 (48+i) := by decide +kernel

theorem runs_r23_part56 : ∀ i ∈ List.range 8, RunsAt 23 (56+i) := by decide +kernel

theorem runs_r23_part64 : ∀ i ∈ List.range 8, RunsAt 23 (64+i) := by decide +kernel

theorem runs_r23_part72 : ∀ i ∈ List.range 8, RunsAt 23 (72+i) := by decide +kernel

theorem runs_r23_part80 : ∀ i ∈ List.range 8, RunsAt 23 (80+i) := by decide +kernel

theorem runs_r23_part88 : ∀ i ∈ List.range 8, RunsAt 23 (88+i) := by decide +kernel

theorem runs_r23_part96 : ∀ i ∈ List.range 8, RunsAt 23 (96+i) := by decide +kernel

theorem runs_r23_part104 : ∀ i ∈ List.range 8, RunsAt 23 (104+i) := by decide +kernel

theorem runs_r23_part112 : ∀ i ∈ List.range 8, RunsAt 23 (112+i) := by decide +kernel

theorem runs_r23 (V : ℕ) (hV : V ∈ List.range 120) : RunsAt 23 V := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := runs_r23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r24_part0 : ∀ i ∈ List.range 8, RunsAt 24 (0+i) := by decide +kernel

theorem runs_r24_part8 : ∀ i ∈ List.range 8, RunsAt 24 (8+i) := by decide +kernel

theorem runs_r24_part16 : ∀ i ∈ List.range 8, RunsAt 24 (16+i) := by decide +kernel

theorem runs_r24_part24 : ∀ i ∈ List.range 8, RunsAt 24 (24+i) := by decide +kernel

theorem runs_r24_part32 : ∀ i ∈ List.range 8, RunsAt 24 (32+i) := by decide +kernel

theorem runs_r24_part40 : ∀ i ∈ List.range 8, RunsAt 24 (40+i) := by decide +kernel

theorem runs_r24_part48 : ∀ i ∈ List.range 8, RunsAt 24 (48+i) := by decide +kernel

theorem runs_r24_part56 : ∀ i ∈ List.range 8, RunsAt 24 (56+i) := by decide +kernel

theorem runs_r24_part64 : ∀ i ∈ List.range 8, RunsAt 24 (64+i) := by decide +kernel

theorem runs_r24_part72 : ∀ i ∈ List.range 8, RunsAt 24 (72+i) := by decide +kernel

theorem runs_r24_part80 : ∀ i ∈ List.range 8, RunsAt 24 (80+i) := by decide +kernel

theorem runs_r24_part88 : ∀ i ∈ List.range 8, RunsAt 24 (88+i) := by decide +kernel

theorem runs_r24_part96 : ∀ i ∈ List.range 8, RunsAt 24 (96+i) := by decide +kernel

theorem runs_r24_part104 : ∀ i ∈ List.range 8, RunsAt 24 (104+i) := by decide +kernel

theorem runs_r24_part112 : ∀ i ∈ List.range 7, RunsAt 24 (112+i) := by decide +kernel

theorem runs_r24 (V : ℕ) (hV : V ∈ List.range 119) : RunsAt 24 V := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := runs_r24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r25_part0 : ∀ i ∈ List.range 8, RunsAt 25 (0+i) := by decide +kernel

theorem runs_r25_part8 : ∀ i ∈ List.range 8, RunsAt 25 (8+i) := by decide +kernel

theorem runs_r25_part16 : ∀ i ∈ List.range 8, RunsAt 25 (16+i) := by decide +kernel

theorem runs_r25_part24 : ∀ i ∈ List.range 8, RunsAt 25 (24+i) := by decide +kernel

theorem runs_r25_part32 : ∀ i ∈ List.range 8, RunsAt 25 (32+i) := by decide +kernel

theorem runs_r25_part40 : ∀ i ∈ List.range 8, RunsAt 25 (40+i) := by decide +kernel

theorem runs_r25_part48 : ∀ i ∈ List.range 8, RunsAt 25 (48+i) := by decide +kernel

theorem runs_r25_part56 : ∀ i ∈ List.range 8, RunsAt 25 (56+i) := by decide +kernel

theorem runs_r25_part64 : ∀ i ∈ List.range 8, RunsAt 25 (64+i) := by decide +kernel

theorem runs_r25_part72 : ∀ i ∈ List.range 8, RunsAt 25 (72+i) := by decide +kernel

theorem runs_r25_part80 : ∀ i ∈ List.range 8, RunsAt 25 (80+i) := by decide +kernel

theorem runs_r25_part88 : ∀ i ∈ List.range 8, RunsAt 25 (88+i) := by decide +kernel

theorem runs_r25_part96 : ∀ i ∈ List.range 8, RunsAt 25 (96+i) := by decide +kernel

theorem runs_r25_part104 : ∀ i ∈ List.range 8, RunsAt 25 (104+i) := by decide +kernel

theorem runs_r25_part112 : ∀ i ∈ List.range 6, RunsAt 25 (112+i) := by decide +kernel

theorem runs_r25 (V : ℕ) (hV : V ∈ List.range 118) : RunsAt 25 V := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := runs_r25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r26_part0 : ∀ i ∈ List.range 8, RunsAt 26 (0+i) := by decide +kernel

theorem runs_r26_part8 : ∀ i ∈ List.range 8, RunsAt 26 (8+i) := by decide +kernel

theorem runs_r26_part16 : ∀ i ∈ List.range 8, RunsAt 26 (16+i) := by decide +kernel

theorem runs_r26_part24 : ∀ i ∈ List.range 8, RunsAt 26 (24+i) := by decide +kernel

theorem runs_r26_part32 : ∀ i ∈ List.range 8, RunsAt 26 (32+i) := by decide +kernel

theorem runs_r26_part40 : ∀ i ∈ List.range 8, RunsAt 26 (40+i) := by decide +kernel

theorem runs_r26_part48 : ∀ i ∈ List.range 8, RunsAt 26 (48+i) := by decide +kernel

theorem runs_r26_part56 : ∀ i ∈ List.range 8, RunsAt 26 (56+i) := by decide +kernel

theorem runs_r26_part64 : ∀ i ∈ List.range 8, RunsAt 26 (64+i) := by decide +kernel

theorem runs_r26_part72 : ∀ i ∈ List.range 8, RunsAt 26 (72+i) := by decide +kernel

theorem runs_r26_part80 : ∀ i ∈ List.range 8, RunsAt 26 (80+i) := by decide +kernel

theorem runs_r26_part88 : ∀ i ∈ List.range 8, RunsAt 26 (88+i) := by decide +kernel

theorem runs_r26_part96 : ∀ i ∈ List.range 8, RunsAt 26 (96+i) := by decide +kernel

theorem runs_r26_part104 : ∀ i ∈ List.range 8, RunsAt 26 (104+i) := by decide +kernel

theorem runs_r26_part112 : ∀ i ∈ List.range 5, RunsAt 26 (112+i) := by decide +kernel

theorem runs_r26 (V : ℕ) (hV : V ∈ List.range 117) : RunsAt 26 V := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := runs_r26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r27_part0 : ∀ i ∈ List.range 8, RunsAt 27 (0+i) := by decide +kernel

theorem runs_r27_part8 : ∀ i ∈ List.range 8, RunsAt 27 (8+i) := by decide +kernel

theorem runs_r27_part16 : ∀ i ∈ List.range 8, RunsAt 27 (16+i) := by decide +kernel

theorem runs_r27_part24 : ∀ i ∈ List.range 8, RunsAt 27 (24+i) := by decide +kernel

theorem runs_r27_part32 : ∀ i ∈ List.range 8, RunsAt 27 (32+i) := by decide +kernel

theorem runs_r27_part40 : ∀ i ∈ List.range 8, RunsAt 27 (40+i) := by decide +kernel

theorem runs_r27_part48 : ∀ i ∈ List.range 8, RunsAt 27 (48+i) := by decide +kernel

theorem runs_r27_part56 : ∀ i ∈ List.range 8, RunsAt 27 (56+i) := by decide +kernel

theorem runs_r27_part64 : ∀ i ∈ List.range 8, RunsAt 27 (64+i) := by decide +kernel

theorem runs_r27_part72 : ∀ i ∈ List.range 8, RunsAt 27 (72+i) := by decide +kernel

theorem runs_r27_part80 : ∀ i ∈ List.range 8, RunsAt 27 (80+i) := by decide +kernel

theorem runs_r27_part88 : ∀ i ∈ List.range 8, RunsAt 27 (88+i) := by decide +kernel

theorem runs_r27_part96 : ∀ i ∈ List.range 8, RunsAt 27 (96+i) := by decide +kernel

theorem runs_r27_part104 : ∀ i ∈ List.range 8, RunsAt 27 (104+i) := by decide +kernel

theorem runs_r27_part112 : ∀ i ∈ List.range 4, RunsAt 27 (112+i) := by decide +kernel

theorem runs_r27 (V : ℕ) (hV : V ∈ List.range 116) : RunsAt 27 V := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := runs_r27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r28_part0 : ∀ i ∈ List.range 8, RunsAt 28 (0+i) := by decide +kernel

theorem runs_r28_part8 : ∀ i ∈ List.range 8, RunsAt 28 (8+i) := by decide +kernel

theorem runs_r28_part16 : ∀ i ∈ List.range 8, RunsAt 28 (16+i) := by decide +kernel

theorem runs_r28_part24 : ∀ i ∈ List.range 8, RunsAt 28 (24+i) := by decide +kernel

theorem runs_r28_part32 : ∀ i ∈ List.range 8, RunsAt 28 (32+i) := by decide +kernel

theorem runs_r28_part40 : ∀ i ∈ List.range 8, RunsAt 28 (40+i) := by decide +kernel

theorem runs_r28_part48 : ∀ i ∈ List.range 8, RunsAt 28 (48+i) := by decide +kernel

theorem runs_r28_part56 : ∀ i ∈ List.range 8, RunsAt 28 (56+i) := by decide +kernel

theorem runs_r28_part64 : ∀ i ∈ List.range 8, RunsAt 28 (64+i) := by decide +kernel

theorem runs_r28_part72 : ∀ i ∈ List.range 8, RunsAt 28 (72+i) := by decide +kernel

theorem runs_r28_part80 : ∀ i ∈ List.range 8, RunsAt 28 (80+i) := by decide +kernel

theorem runs_r28_part88 : ∀ i ∈ List.range 8, RunsAt 28 (88+i) := by decide +kernel

theorem runs_r28_part96 : ∀ i ∈ List.range 8, RunsAt 28 (96+i) := by decide +kernel

theorem runs_r28_part104 : ∀ i ∈ List.range 8, RunsAt 28 (104+i) := by decide +kernel

theorem runs_r28_part112 : ∀ i ∈ List.range 3, RunsAt 28 (112+i) := by decide +kernel

theorem runs_r28 (V : ℕ) (hV : V ∈ List.range 115) : RunsAt 28 V := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := runs_r28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r29_part0 : ∀ i ∈ List.range 8, RunsAt 29 (0+i) := by decide +kernel

theorem runs_r29_part8 : ∀ i ∈ List.range 8, RunsAt 29 (8+i) := by decide +kernel

theorem runs_r29_part16 : ∀ i ∈ List.range 8, RunsAt 29 (16+i) := by decide +kernel

theorem runs_r29_part24 : ∀ i ∈ List.range 8, RunsAt 29 (24+i) := by decide +kernel

theorem runs_r29_part32 : ∀ i ∈ List.range 8, RunsAt 29 (32+i) := by decide +kernel

theorem runs_r29_part40 : ∀ i ∈ List.range 8, RunsAt 29 (40+i) := by decide +kernel

theorem runs_r29_part48 : ∀ i ∈ List.range 8, RunsAt 29 (48+i) := by decide +kernel

theorem runs_r29_part56 : ∀ i ∈ List.range 8, RunsAt 29 (56+i) := by decide +kernel

theorem runs_r29_part64 : ∀ i ∈ List.range 8, RunsAt 29 (64+i) := by decide +kernel

theorem runs_r29_part72 : ∀ i ∈ List.range 8, RunsAt 29 (72+i) := by decide +kernel

theorem runs_r29_part80 : ∀ i ∈ List.range 8, RunsAt 29 (80+i) := by decide +kernel

theorem runs_r29_part88 : ∀ i ∈ List.range 8, RunsAt 29 (88+i) := by decide +kernel

theorem runs_r29_part96 : ∀ i ∈ List.range 8, RunsAt 29 (96+i) := by decide +kernel

theorem runs_r29_part104 : ∀ i ∈ List.range 8, RunsAt 29 (104+i) := by decide +kernel

theorem runs_r29_part112 : ∀ i ∈ List.range 2, RunsAt 29 (112+i) := by decide +kernel

theorem runs_r29 (V : ℕ) (hV : V ∈ List.range 114) : RunsAt 29 V := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := runs_r29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r30_part0 : ∀ i ∈ List.range 8, RunsAt 30 (0+i) := by decide +kernel

theorem runs_r30_part8 : ∀ i ∈ List.range 8, RunsAt 30 (8+i) := by decide +kernel

theorem runs_r30_part16 : ∀ i ∈ List.range 8, RunsAt 30 (16+i) := by decide +kernel

theorem runs_r30_part24 : ∀ i ∈ List.range 8, RunsAt 30 (24+i) := by decide +kernel

theorem runs_r30_part32 : ∀ i ∈ List.range 8, RunsAt 30 (32+i) := by decide +kernel

theorem runs_r30_part40 : ∀ i ∈ List.range 8, RunsAt 30 (40+i) := by decide +kernel

theorem runs_r30_part48 : ∀ i ∈ List.range 8, RunsAt 30 (48+i) := by decide +kernel

theorem runs_r30_part56 : ∀ i ∈ List.range 8, RunsAt 30 (56+i) := by decide +kernel

theorem runs_r30_part64 : ∀ i ∈ List.range 8, RunsAt 30 (64+i) := by decide +kernel

theorem runs_r30_part72 : ∀ i ∈ List.range 8, RunsAt 30 (72+i) := by decide +kernel

theorem runs_r30_part80 : ∀ i ∈ List.range 8, RunsAt 30 (80+i) := by decide +kernel

theorem runs_r30_part88 : ∀ i ∈ List.range 8, RunsAt 30 (88+i) := by decide +kernel

theorem runs_r30_part96 : ∀ i ∈ List.range 8, RunsAt 30 (96+i) := by decide +kernel

theorem runs_r30_part104 : ∀ i ∈ List.range 8, RunsAt 30 (104+i) := by decide +kernel

theorem runs_r30_part112 : ∀ i ∈ List.range 1, RunsAt 30 (112+i) := by decide +kernel

theorem runs_r30 (V : ℕ) (hV : V ∈ List.range 113) : RunsAt 30 V := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := runs_r30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := runs_r30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := runs_r30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := runs_r30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := runs_r30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := runs_r30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := runs_r30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := runs_r30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runs_r31_part0 : ∀ i ∈ List.range 8, RunsAt 31 (0+i) := by decide +kernel

theorem runs_r31_part8 : ∀ i ∈ List.range 8, RunsAt 31 (8+i) := by decide +kernel

theorem runs_r31_part16 : ∀ i ∈ List.range 8, RunsAt 31 (16+i) := by decide +kernel

theorem runs_r31_part24 : ∀ i ∈ List.range 8, RunsAt 31 (24+i) := by decide +kernel

theorem runs_r31_part32 : ∀ i ∈ List.range 8, RunsAt 31 (32+i) := by decide +kernel

theorem runs_r31_part40 : ∀ i ∈ List.range 8, RunsAt 31 (40+i) := by decide +kernel

theorem runs_r31_part48 : ∀ i ∈ List.range 8, RunsAt 31 (48+i) := by decide +kernel

theorem runs_r31_part56 : ∀ i ∈ List.range 8, RunsAt 31 (56+i) := by decide +kernel

theorem runs_r31_part64 : ∀ i ∈ List.range 8, RunsAt 31 (64+i) := by decide +kernel

theorem runs_r31_part72 : ∀ i ∈ List.range 8, RunsAt 31 (72+i) := by decide +kernel

theorem runs_r31_part80 : ∀ i ∈ List.range 8, RunsAt 31 (80+i) := by decide +kernel

theorem runs_r31_part88 : ∀ i ∈ List.range 8, RunsAt 31 (88+i) := by decide +kernel

theorem runs_r31_part96 : ∀ i ∈ List.range 8, RunsAt 31 (96+i) := by decide +kernel

theorem runs_r31_part104 : ∀ i ∈ List.range 8, RunsAt 31 (104+i) := by decide +kernel

theorem runs_r31 (V : ℕ) (hV : V ∈ List.range 112) : RunsAt 31 V := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := runs_r31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := runs_r31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := runs_r31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := runs_r31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := runs_r31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := runs_r31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := runs_r31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := runs_r31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := runs_r31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := runs_r31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := runs_r31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := runs_r31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := runs_r31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := runs_r31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem runsReceipt : RunReceiptSound := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact runs_r1 V (List.mem_range.mpr (by omega))
    | exact runs_r2 V (List.mem_range.mpr (by omega))
    | exact runs_r3 V (List.mem_range.mpr (by omega))
    | exact runs_r4 V (List.mem_range.mpr (by omega))
    | exact runs_r5 V (List.mem_range.mpr (by omega))
    | exact runs_r6 V (List.mem_range.mpr (by omega))
    | exact runs_r7 V (List.mem_range.mpr (by omega))
    | exact runs_r8 V (List.mem_range.mpr (by omega))
    | exact runs_r9 V (List.mem_range.mpr (by omega))
    | exact runs_r10 V (List.mem_range.mpr (by omega))
    | exact runs_r11 V (List.mem_range.mpr (by omega))
    | exact runs_r12 V (List.mem_range.mpr (by omega))
    | exact runs_r13 V (List.mem_range.mpr (by omega))
    | exact runs_r14 V (List.mem_range.mpr (by omega))
    | exact runs_r15 V (List.mem_range.mpr (by omega))
    | exact runs_r16 V (List.mem_range.mpr (by omega))
    | exact runs_r17 V (List.mem_range.mpr (by omega))
    | exact runs_r18 V (List.mem_range.mpr (by omega))
    | exact runs_r19 V (List.mem_range.mpr (by omega))
    | exact runs_r20 V (List.mem_range.mpr (by omega))
    | exact runs_r21 V (List.mem_range.mpr (by omega))
    | exact runs_r22 V (List.mem_range.mpr (by omega))
    | exact runs_r23 V (List.mem_range.mpr (by omega))
    | exact runs_r24 V (List.mem_range.mpr (by omega))
    | exact runs_r25 V (List.mem_range.mpr (by omega))
    | exact runs_r26 V (List.mem_range.mpr (by omega))
    | exact runs_r27 V (List.mem_range.mpr (by omega))
    | exact runs_r28 V (List.mem_range.mpr (by omega))
    | exact runs_r29 V (List.mem_range.mpr (by omega))
    | exact runs_r30 V (List.mem_range.mpr (by omega))
    | exact runs_r31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
