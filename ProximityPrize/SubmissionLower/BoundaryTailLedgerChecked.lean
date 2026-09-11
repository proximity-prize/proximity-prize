import ProximityPrize.SubmissionLower.BoundaryTailLedgerData

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR1_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (0+i)) 0 (Lower80811.LedgerData.lookup 1 (0+i)) := by decide +kernel

theorem checkedR1_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (8+i)) 0 (Lower80811.LedgerData.lookup 1 (8+i)) := by decide +kernel

theorem checkedR1_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (16+i)) 0 (Lower80811.LedgerData.lookup 1 (16+i)) := by decide +kernel

theorem checkedR1_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (24+i)) 0 (Lower80811.LedgerData.lookup 1 (24+i)) := by decide +kernel

theorem checkedR1_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (32+i)) 0 (Lower80811.LedgerData.lookup 1 (32+i)) := by decide +kernel

theorem checkedR1_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (40+i)) 0 (Lower80811.LedgerData.lookup 1 (40+i)) := by decide +kernel

theorem checkedR1_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (48+i)) 0 (Lower80811.LedgerData.lookup 1 (48+i)) := by decide +kernel

theorem checkedR1_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (56+i)) 0 (Lower80811.LedgerData.lookup 1 (56+i)) := by decide +kernel

theorem checkedR1_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (64+i)) 0 (Lower80811.LedgerData.lookup 1 (64+i)) := by decide +kernel

theorem checkedR1_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (72+i)) 0 (Lower80811.LedgerData.lookup 1 (72+i)) := by decide +kernel

theorem checkedR1_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (80+i)) 0 (Lower80811.LedgerData.lookup 1 (80+i)) := by decide +kernel

theorem checkedR1_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (88+i)) 0 (Lower80811.LedgerData.lookup 1 (88+i)) := by decide +kernel

theorem checkedR1_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (96+i)) 0 (Lower80811.LedgerData.lookup 1 (96+i)) := by decide +kernel

theorem checkedR1_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (104+i)) 0 (Lower80811.LedgerData.lookup 1 (104+i)) := by decide +kernel

theorem checkedR1_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (112+i)) 0 (Lower80811.LedgerData.lookup 1 (112+i)) := by decide +kernel

theorem checkedR1_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (120+i)) 0 (Lower80811.LedgerData.lookup 1 (120+i)) := by decide +kernel

theorem checkedR1_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 1 (128+i)) 0 (Lower80811.LedgerData.lookup 1 (128+i)) := by decide +kernel

theorem checkedR1_part136 : ∀ i ∈ List.range 6, RunsValid (rowContext 1 (136+i)) 0 (Lower80811.LedgerData.lookup 1 (136+i)) := by decide +kernel

theorem checkedR1 (V : ℕ) (hV : V ∈ List.range 142) : RunsValid (rowContext 1 V) 0 (Lower80811.LedgerData.lookup 1 V) := by
  have hv : V < 142 := List.mem_range.mp hV
  by_cases h0_142 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR1_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR1_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR1_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR1_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR1_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR1_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR1_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR1_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR1_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_142 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR1_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR1_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR1_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR1_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_142 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR1_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR1_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_142 : V < 128
        · have hi := checkedR1_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_142 : V < 136
          · have hi := checkedR1_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR1_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR2_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (0+i)) 0 (Lower80811.LedgerData.lookup 2 (0+i)) := by decide +kernel

theorem checkedR2_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (8+i)) 0 (Lower80811.LedgerData.lookup 2 (8+i)) := by decide +kernel

theorem checkedR2_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (16+i)) 0 (Lower80811.LedgerData.lookup 2 (16+i)) := by decide +kernel

theorem checkedR2_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (24+i)) 0 (Lower80811.LedgerData.lookup 2 (24+i)) := by decide +kernel

theorem checkedR2_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (32+i)) 0 (Lower80811.LedgerData.lookup 2 (32+i)) := by decide +kernel

theorem checkedR2_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (40+i)) 0 (Lower80811.LedgerData.lookup 2 (40+i)) := by decide +kernel

theorem checkedR2_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (48+i)) 0 (Lower80811.LedgerData.lookup 2 (48+i)) := by decide +kernel

theorem checkedR2_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (56+i)) 0 (Lower80811.LedgerData.lookup 2 (56+i)) := by decide +kernel

theorem checkedR2_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (64+i)) 0 (Lower80811.LedgerData.lookup 2 (64+i)) := by decide +kernel

theorem checkedR2_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (72+i)) 0 (Lower80811.LedgerData.lookup 2 (72+i)) := by decide +kernel

theorem checkedR2_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (80+i)) 0 (Lower80811.LedgerData.lookup 2 (80+i)) := by decide +kernel

theorem checkedR2_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (88+i)) 0 (Lower80811.LedgerData.lookup 2 (88+i)) := by decide +kernel

theorem checkedR2_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (96+i)) 0 (Lower80811.LedgerData.lookup 2 (96+i)) := by decide +kernel

theorem checkedR2_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (104+i)) 0 (Lower80811.LedgerData.lookup 2 (104+i)) := by decide +kernel

theorem checkedR2_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (112+i)) 0 (Lower80811.LedgerData.lookup 2 (112+i)) := by decide +kernel

theorem checkedR2_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (120+i)) 0 (Lower80811.LedgerData.lookup 2 (120+i)) := by decide +kernel

theorem checkedR2_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 2 (128+i)) 0 (Lower80811.LedgerData.lookup 2 (128+i)) := by decide +kernel

theorem checkedR2_part136 : ∀ i ∈ List.range 5, RunsValid (rowContext 2 (136+i)) 0 (Lower80811.LedgerData.lookup 2 (136+i)) := by decide +kernel

theorem checkedR2 (V : ℕ) (hV : V ∈ List.range 141) : RunsValid (rowContext 2 V) 0 (Lower80811.LedgerData.lookup 2 V) := by
  have hv : V < 141 := List.mem_range.mp hV
  by_cases h0_141 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR2_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR2_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR2_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR2_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR2_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR2_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR2_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR2_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR2_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_141 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR2_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR2_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR2_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR2_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_141 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR2_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR2_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_141 : V < 128
        · have hi := checkedR2_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_141 : V < 136
          · have hi := checkedR2_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR2_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR3_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (0+i)) 0 (Lower80811.LedgerData.lookup 3 (0+i)) := by decide +kernel

theorem checkedR3_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (8+i)) 0 (Lower80811.LedgerData.lookup 3 (8+i)) := by decide +kernel

theorem checkedR3_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (16+i)) 0 (Lower80811.LedgerData.lookup 3 (16+i)) := by decide +kernel

theorem checkedR3_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (24+i)) 0 (Lower80811.LedgerData.lookup 3 (24+i)) := by decide +kernel

theorem checkedR3_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (32+i)) 0 (Lower80811.LedgerData.lookup 3 (32+i)) := by decide +kernel

theorem checkedR3_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (40+i)) 0 (Lower80811.LedgerData.lookup 3 (40+i)) := by decide +kernel

theorem checkedR3_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (48+i)) 0 (Lower80811.LedgerData.lookup 3 (48+i)) := by decide +kernel

theorem checkedR3_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (56+i)) 0 (Lower80811.LedgerData.lookup 3 (56+i)) := by decide +kernel

theorem checkedR3_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (64+i)) 0 (Lower80811.LedgerData.lookup 3 (64+i)) := by decide +kernel

theorem checkedR3_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (72+i)) 0 (Lower80811.LedgerData.lookup 3 (72+i)) := by decide +kernel

theorem checkedR3_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (80+i)) 0 (Lower80811.LedgerData.lookup 3 (80+i)) := by decide +kernel

theorem checkedR3_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (88+i)) 0 (Lower80811.LedgerData.lookup 3 (88+i)) := by decide +kernel

theorem checkedR3_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (96+i)) 0 (Lower80811.LedgerData.lookup 3 (96+i)) := by decide +kernel

theorem checkedR3_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (104+i)) 0 (Lower80811.LedgerData.lookup 3 (104+i)) := by decide +kernel

theorem checkedR3_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (112+i)) 0 (Lower80811.LedgerData.lookup 3 (112+i)) := by decide +kernel

theorem checkedR3_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (120+i)) 0 (Lower80811.LedgerData.lookup 3 (120+i)) := by decide +kernel

theorem checkedR3_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 3 (128+i)) 0 (Lower80811.LedgerData.lookup 3 (128+i)) := by decide +kernel

theorem checkedR3_part136 : ∀ i ∈ List.range 4, RunsValid (rowContext 3 (136+i)) 0 (Lower80811.LedgerData.lookup 3 (136+i)) := by decide +kernel

theorem checkedR3 (V : ℕ) (hV : V ∈ List.range 140) : RunsValid (rowContext 3 V) 0 (Lower80811.LedgerData.lookup 3 V) := by
  have hv : V < 140 := List.mem_range.mp hV
  by_cases h0_140 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR3_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR3_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR3_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR3_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR3_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR3_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR3_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR3_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR3_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_140 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR3_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR3_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR3_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR3_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_140 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR3_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR3_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_140 : V < 128
        · have hi := checkedR3_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_140 : V < 136
          · have hi := checkedR3_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR3_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR4_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (0+i)) 0 (Lower80811.LedgerData.lookup 4 (0+i)) := by decide +kernel

theorem checkedR4_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (8+i)) 0 (Lower80811.LedgerData.lookup 4 (8+i)) := by decide +kernel

theorem checkedR4_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (16+i)) 0 (Lower80811.LedgerData.lookup 4 (16+i)) := by decide +kernel

theorem checkedR4_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (24+i)) 0 (Lower80811.LedgerData.lookup 4 (24+i)) := by decide +kernel

theorem checkedR4_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (32+i)) 0 (Lower80811.LedgerData.lookup 4 (32+i)) := by decide +kernel

theorem checkedR4_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (40+i)) 0 (Lower80811.LedgerData.lookup 4 (40+i)) := by decide +kernel

theorem checkedR4_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (48+i)) 0 (Lower80811.LedgerData.lookup 4 (48+i)) := by decide +kernel

theorem checkedR4_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (56+i)) 0 (Lower80811.LedgerData.lookup 4 (56+i)) := by decide +kernel

theorem checkedR4_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (64+i)) 0 (Lower80811.LedgerData.lookup 4 (64+i)) := by decide +kernel

theorem checkedR4_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (72+i)) 0 (Lower80811.LedgerData.lookup 4 (72+i)) := by decide +kernel

theorem checkedR4_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (80+i)) 0 (Lower80811.LedgerData.lookup 4 (80+i)) := by decide +kernel

theorem checkedR4_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (88+i)) 0 (Lower80811.LedgerData.lookup 4 (88+i)) := by decide +kernel

theorem checkedR4_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (96+i)) 0 (Lower80811.LedgerData.lookup 4 (96+i)) := by decide +kernel

theorem checkedR4_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (104+i)) 0 (Lower80811.LedgerData.lookup 4 (104+i)) := by decide +kernel

theorem checkedR4_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (112+i)) 0 (Lower80811.LedgerData.lookup 4 (112+i)) := by decide +kernel

theorem checkedR4_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (120+i)) 0 (Lower80811.LedgerData.lookup 4 (120+i)) := by decide +kernel

theorem checkedR4_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 4 (128+i)) 0 (Lower80811.LedgerData.lookup 4 (128+i)) := by decide +kernel

theorem checkedR4_part136 : ∀ i ∈ List.range 3, RunsValid (rowContext 4 (136+i)) 0 (Lower80811.LedgerData.lookup 4 (136+i)) := by decide +kernel

theorem checkedR4 (V : ℕ) (hV : V ∈ List.range 139) : RunsValid (rowContext 4 V) 0 (Lower80811.LedgerData.lookup 4 V) := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR4_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR4_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR4_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR4_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR4_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR4_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR4_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR4_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR4_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_139 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR4_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR4_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR4_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR4_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_139 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR4_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR4_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_139 : V < 128
        · have hi := checkedR4_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_139 : V < 136
          · have hi := checkedR4_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR4_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR5_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (0+i)) 0 (Lower80811.LedgerData.lookup 5 (0+i)) := by decide +kernel

theorem checkedR5_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (8+i)) 0 (Lower80811.LedgerData.lookup 5 (8+i)) := by decide +kernel

theorem checkedR5_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (16+i)) 0 (Lower80811.LedgerData.lookup 5 (16+i)) := by decide +kernel

theorem checkedR5_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (24+i)) 0 (Lower80811.LedgerData.lookup 5 (24+i)) := by decide +kernel

theorem checkedR5_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (32+i)) 0 (Lower80811.LedgerData.lookup 5 (32+i)) := by decide +kernel

theorem checkedR5_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (40+i)) 0 (Lower80811.LedgerData.lookup 5 (40+i)) := by decide +kernel

theorem checkedR5_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (48+i)) 0 (Lower80811.LedgerData.lookup 5 (48+i)) := by decide +kernel

theorem checkedR5_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (56+i)) 0 (Lower80811.LedgerData.lookup 5 (56+i)) := by decide +kernel

theorem checkedR5_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (64+i)) 0 (Lower80811.LedgerData.lookup 5 (64+i)) := by decide +kernel

theorem checkedR5_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (72+i)) 0 (Lower80811.LedgerData.lookup 5 (72+i)) := by decide +kernel

theorem checkedR5_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (80+i)) 0 (Lower80811.LedgerData.lookup 5 (80+i)) := by decide +kernel

theorem checkedR5_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (88+i)) 0 (Lower80811.LedgerData.lookup 5 (88+i)) := by decide +kernel

theorem checkedR5_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (96+i)) 0 (Lower80811.LedgerData.lookup 5 (96+i)) := by decide +kernel

theorem checkedR5_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (104+i)) 0 (Lower80811.LedgerData.lookup 5 (104+i)) := by decide +kernel

theorem checkedR5_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (112+i)) 0 (Lower80811.LedgerData.lookup 5 (112+i)) := by decide +kernel

theorem checkedR5_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (120+i)) 0 (Lower80811.LedgerData.lookup 5 (120+i)) := by decide +kernel

theorem checkedR5_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 5 (128+i)) 0 (Lower80811.LedgerData.lookup 5 (128+i)) := by decide +kernel

theorem checkedR5_part136 : ∀ i ∈ List.range 2, RunsValid (rowContext 5 (136+i)) 0 (Lower80811.LedgerData.lookup 5 (136+i)) := by decide +kernel

theorem checkedR5 (V : ℕ) (hV : V ∈ List.range 138) : RunsValid (rowContext 5 V) 0 (Lower80811.LedgerData.lookup 5 V) := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR5_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR5_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR5_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR5_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR5_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR5_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR5_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR5_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR5_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_138 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR5_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR5_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR5_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR5_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_138 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR5_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR5_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_138 : V < 128
        · have hi := checkedR5_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_138 : V < 136
          · have hi := checkedR5_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR5_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR6_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (0+i)) 0 (Lower80811.LedgerData.lookup 6 (0+i)) := by decide +kernel

theorem checkedR6_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (8+i)) 0 (Lower80811.LedgerData.lookup 6 (8+i)) := by decide +kernel

theorem checkedR6_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (16+i)) 0 (Lower80811.LedgerData.lookup 6 (16+i)) := by decide +kernel

theorem checkedR6_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (24+i)) 0 (Lower80811.LedgerData.lookup 6 (24+i)) := by decide +kernel

theorem checkedR6_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (32+i)) 0 (Lower80811.LedgerData.lookup 6 (32+i)) := by decide +kernel

theorem checkedR6_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (40+i)) 0 (Lower80811.LedgerData.lookup 6 (40+i)) := by decide +kernel

theorem checkedR6_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (48+i)) 0 (Lower80811.LedgerData.lookup 6 (48+i)) := by decide +kernel

theorem checkedR6_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (56+i)) 0 (Lower80811.LedgerData.lookup 6 (56+i)) := by decide +kernel

theorem checkedR6_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (64+i)) 0 (Lower80811.LedgerData.lookup 6 (64+i)) := by decide +kernel

theorem checkedR6_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (72+i)) 0 (Lower80811.LedgerData.lookup 6 (72+i)) := by decide +kernel

theorem checkedR6_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (80+i)) 0 (Lower80811.LedgerData.lookup 6 (80+i)) := by decide +kernel

theorem checkedR6_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (88+i)) 0 (Lower80811.LedgerData.lookup 6 (88+i)) := by decide +kernel

theorem checkedR6_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (96+i)) 0 (Lower80811.LedgerData.lookup 6 (96+i)) := by decide +kernel

theorem checkedR6_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (104+i)) 0 (Lower80811.LedgerData.lookup 6 (104+i)) := by decide +kernel

theorem checkedR6_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (112+i)) 0 (Lower80811.LedgerData.lookup 6 (112+i)) := by decide +kernel

theorem checkedR6_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (120+i)) 0 (Lower80811.LedgerData.lookup 6 (120+i)) := by decide +kernel

theorem checkedR6_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 6 (128+i)) 0 (Lower80811.LedgerData.lookup 6 (128+i)) := by decide +kernel

theorem checkedR6_part136 : ∀ i ∈ List.range 1, RunsValid (rowContext 6 (136+i)) 0 (Lower80811.LedgerData.lookup 6 (136+i)) := by decide +kernel

theorem checkedR6 (V : ℕ) (hV : V ∈ List.range 137) : RunsValid (rowContext 6 V) 0 (Lower80811.LedgerData.lookup 6 V) := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 72
  · by_cases h0_72 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR6_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR6_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR6_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR6_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_72 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR6_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR6_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_72 : V < 56
        · have hi := checkedR6_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · by_cases h56_72 : V < 64
          · have hi := checkedR6_part56 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
          · have hi := checkedR6_part64 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
  · by_cases h72_137 : V < 104
    · by_cases h72_104 : V < 88
      · by_cases h72_88 : V < 80
        · have hi := checkedR6_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR6_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
      · by_cases h88_104 : V < 96
        · have hi := checkedR6_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR6_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
    · by_cases h104_137 : V < 120
      · by_cases h104_120 : V < 112
        · have hi := checkedR6_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR6_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
      · by_cases h120_137 : V < 128
        · have hi := checkedR6_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
        · by_cases h128_137 : V < 136
          · have hi := checkedR6_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi
          · have hi := checkedR6_part136 (V-136) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR7_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (0+i)) 0 (Lower80811.LedgerData.lookup 7 (0+i)) := by decide +kernel

theorem checkedR7_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (8+i)) 0 (Lower80811.LedgerData.lookup 7 (8+i)) := by decide +kernel

theorem checkedR7_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (16+i)) 0 (Lower80811.LedgerData.lookup 7 (16+i)) := by decide +kernel

theorem checkedR7_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (24+i)) 0 (Lower80811.LedgerData.lookup 7 (24+i)) := by decide +kernel

theorem checkedR7_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (32+i)) 0 (Lower80811.LedgerData.lookup 7 (32+i)) := by decide +kernel

theorem checkedR7_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (40+i)) 0 (Lower80811.LedgerData.lookup 7 (40+i)) := by decide +kernel

theorem checkedR7_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (48+i)) 0 (Lower80811.LedgerData.lookup 7 (48+i)) := by decide +kernel

theorem checkedR7_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (56+i)) 0 (Lower80811.LedgerData.lookup 7 (56+i)) := by decide +kernel

theorem checkedR7_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (64+i)) 0 (Lower80811.LedgerData.lookup 7 (64+i)) := by decide +kernel

theorem checkedR7_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (72+i)) 0 (Lower80811.LedgerData.lookup 7 (72+i)) := by decide +kernel

theorem checkedR7_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (80+i)) 0 (Lower80811.LedgerData.lookup 7 (80+i)) := by decide +kernel

theorem checkedR7_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (88+i)) 0 (Lower80811.LedgerData.lookup 7 (88+i)) := by decide +kernel

theorem checkedR7_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (96+i)) 0 (Lower80811.LedgerData.lookup 7 (96+i)) := by decide +kernel

theorem checkedR7_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (104+i)) 0 (Lower80811.LedgerData.lookup 7 (104+i)) := by decide +kernel

theorem checkedR7_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (112+i)) 0 (Lower80811.LedgerData.lookup 7 (112+i)) := by decide +kernel

theorem checkedR7_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (120+i)) 0 (Lower80811.LedgerData.lookup 7 (120+i)) := by decide +kernel

theorem checkedR7_part128 : ∀ i ∈ List.range 8, RunsValid (rowContext 7 (128+i)) 0 (Lower80811.LedgerData.lookup 7 (128+i)) := by decide +kernel

theorem checkedR7 (V : ℕ) (hV : V ∈ List.range 136) : RunsValid (rowContext 7 V) 0 (Lower80811.LedgerData.lookup 7 V) := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR7_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR7_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR7_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR7_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR7_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR7_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR7_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR7_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_136 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR7_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR7_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR7_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR7_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_136 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR7_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR7_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_136 : V < 120
        · have hi := checkedR7_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_136 : V < 128
          · have hi := checkedR7_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR7_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR8_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (0+i)) 0 (Lower80811.LedgerData.lookup 8 (0+i)) := by decide +kernel

theorem checkedR8_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (8+i)) 0 (Lower80811.LedgerData.lookup 8 (8+i)) := by decide +kernel

theorem checkedR8_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (16+i)) 0 (Lower80811.LedgerData.lookup 8 (16+i)) := by decide +kernel

theorem checkedR8_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (24+i)) 0 (Lower80811.LedgerData.lookup 8 (24+i)) := by decide +kernel

theorem checkedR8_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (32+i)) 0 (Lower80811.LedgerData.lookup 8 (32+i)) := by decide +kernel

theorem checkedR8_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (40+i)) 0 (Lower80811.LedgerData.lookup 8 (40+i)) := by decide +kernel

theorem checkedR8_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (48+i)) 0 (Lower80811.LedgerData.lookup 8 (48+i)) := by decide +kernel

theorem checkedR8_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (56+i)) 0 (Lower80811.LedgerData.lookup 8 (56+i)) := by decide +kernel

theorem checkedR8_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (64+i)) 0 (Lower80811.LedgerData.lookup 8 (64+i)) := by decide +kernel

theorem checkedR8_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (72+i)) 0 (Lower80811.LedgerData.lookup 8 (72+i)) := by decide +kernel

theorem checkedR8_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (80+i)) 0 (Lower80811.LedgerData.lookup 8 (80+i)) := by decide +kernel

theorem checkedR8_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (88+i)) 0 (Lower80811.LedgerData.lookup 8 (88+i)) := by decide +kernel

theorem checkedR8_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (96+i)) 0 (Lower80811.LedgerData.lookup 8 (96+i)) := by decide +kernel

theorem checkedR8_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (104+i)) 0 (Lower80811.LedgerData.lookup 8 (104+i)) := by decide +kernel

theorem checkedR8_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (112+i)) 0 (Lower80811.LedgerData.lookup 8 (112+i)) := by decide +kernel

theorem checkedR8_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 8 (120+i)) 0 (Lower80811.LedgerData.lookup 8 (120+i)) := by decide +kernel

theorem checkedR8_part128 : ∀ i ∈ List.range 7, RunsValid (rowContext 8 (128+i)) 0 (Lower80811.LedgerData.lookup 8 (128+i)) := by decide +kernel

theorem checkedR8 (V : ℕ) (hV : V ∈ List.range 135) : RunsValid (rowContext 8 V) 0 (Lower80811.LedgerData.lookup 8 V) := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR8_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR8_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR8_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR8_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR8_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR8_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR8_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR8_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_135 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR8_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR8_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR8_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR8_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_135 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR8_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR8_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_135 : V < 120
        · have hi := checkedR8_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_135 : V < 128
          · have hi := checkedR8_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR8_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR9_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (0+i)) 0 (Lower80811.LedgerData.lookup 9 (0+i)) := by decide +kernel

theorem checkedR9_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (8+i)) 0 (Lower80811.LedgerData.lookup 9 (8+i)) := by decide +kernel

theorem checkedR9_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (16+i)) 0 (Lower80811.LedgerData.lookup 9 (16+i)) := by decide +kernel

theorem checkedR9_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (24+i)) 0 (Lower80811.LedgerData.lookup 9 (24+i)) := by decide +kernel

theorem checkedR9_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (32+i)) 0 (Lower80811.LedgerData.lookup 9 (32+i)) := by decide +kernel

theorem checkedR9_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (40+i)) 0 (Lower80811.LedgerData.lookup 9 (40+i)) := by decide +kernel

theorem checkedR9_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (48+i)) 0 (Lower80811.LedgerData.lookup 9 (48+i)) := by decide +kernel

theorem checkedR9_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (56+i)) 0 (Lower80811.LedgerData.lookup 9 (56+i)) := by decide +kernel

theorem checkedR9_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (64+i)) 0 (Lower80811.LedgerData.lookup 9 (64+i)) := by decide +kernel

theorem checkedR9_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (72+i)) 0 (Lower80811.LedgerData.lookup 9 (72+i)) := by decide +kernel

theorem checkedR9_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (80+i)) 0 (Lower80811.LedgerData.lookup 9 (80+i)) := by decide +kernel

theorem checkedR9_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (88+i)) 0 (Lower80811.LedgerData.lookup 9 (88+i)) := by decide +kernel

theorem checkedR9_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (96+i)) 0 (Lower80811.LedgerData.lookup 9 (96+i)) := by decide +kernel

theorem checkedR9_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (104+i)) 0 (Lower80811.LedgerData.lookup 9 (104+i)) := by decide +kernel

theorem checkedR9_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (112+i)) 0 (Lower80811.LedgerData.lookup 9 (112+i)) := by decide +kernel

theorem checkedR9_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 9 (120+i)) 0 (Lower80811.LedgerData.lookup 9 (120+i)) := by decide +kernel

theorem checkedR9_part128 : ∀ i ∈ List.range 6, RunsValid (rowContext 9 (128+i)) 0 (Lower80811.LedgerData.lookup 9 (128+i)) := by decide +kernel

theorem checkedR9 (V : ℕ) (hV : V ∈ List.range 134) : RunsValid (rowContext 9 V) 0 (Lower80811.LedgerData.lookup 9 V) := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR9_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR9_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR9_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR9_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR9_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR9_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR9_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR9_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_134 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR9_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR9_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR9_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR9_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_134 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR9_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR9_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_134 : V < 120
        · have hi := checkedR9_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_134 : V < 128
          · have hi := checkedR9_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR9_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR10_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (0+i)) 0 (Lower80811.LedgerData.lookup 10 (0+i)) := by decide +kernel

theorem checkedR10_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (8+i)) 0 (Lower80811.LedgerData.lookup 10 (8+i)) := by decide +kernel

theorem checkedR10_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (16+i)) 0 (Lower80811.LedgerData.lookup 10 (16+i)) := by decide +kernel

theorem checkedR10_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (24+i)) 0 (Lower80811.LedgerData.lookup 10 (24+i)) := by decide +kernel

theorem checkedR10_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (32+i)) 0 (Lower80811.LedgerData.lookup 10 (32+i)) := by decide +kernel

theorem checkedR10_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (40+i)) 0 (Lower80811.LedgerData.lookup 10 (40+i)) := by decide +kernel

theorem checkedR10_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (48+i)) 0 (Lower80811.LedgerData.lookup 10 (48+i)) := by decide +kernel

theorem checkedR10_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (56+i)) 0 (Lower80811.LedgerData.lookup 10 (56+i)) := by decide +kernel

theorem checkedR10_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (64+i)) 0 (Lower80811.LedgerData.lookup 10 (64+i)) := by decide +kernel

theorem checkedR10_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (72+i)) 0 (Lower80811.LedgerData.lookup 10 (72+i)) := by decide +kernel

theorem checkedR10_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (80+i)) 0 (Lower80811.LedgerData.lookup 10 (80+i)) := by decide +kernel

theorem checkedR10_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (88+i)) 0 (Lower80811.LedgerData.lookup 10 (88+i)) := by decide +kernel

theorem checkedR10_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (96+i)) 0 (Lower80811.LedgerData.lookup 10 (96+i)) := by decide +kernel

theorem checkedR10_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (104+i)) 0 (Lower80811.LedgerData.lookup 10 (104+i)) := by decide +kernel

theorem checkedR10_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (112+i)) 0 (Lower80811.LedgerData.lookup 10 (112+i)) := by decide +kernel

theorem checkedR10_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 10 (120+i)) 0 (Lower80811.LedgerData.lookup 10 (120+i)) := by decide +kernel

theorem checkedR10_part128 : ∀ i ∈ List.range 5, RunsValid (rowContext 10 (128+i)) 0 (Lower80811.LedgerData.lookup 10 (128+i)) := by decide +kernel

theorem checkedR10 (V : ℕ) (hV : V ∈ List.range 133) : RunsValid (rowContext 10 V) 0 (Lower80811.LedgerData.lookup 10 V) := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR10_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR10_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR10_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR10_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR10_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR10_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR10_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR10_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_133 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR10_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR10_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR10_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR10_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_133 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR10_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR10_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_133 : V < 120
        · have hi := checkedR10_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_133 : V < 128
          · have hi := checkedR10_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR10_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR11_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (0+i)) 0 (Lower80811.LedgerData.lookup 11 (0+i)) := by decide +kernel

theorem checkedR11_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (8+i)) 0 (Lower80811.LedgerData.lookup 11 (8+i)) := by decide +kernel

theorem checkedR11_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (16+i)) 0 (Lower80811.LedgerData.lookup 11 (16+i)) := by decide +kernel

theorem checkedR11_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (24+i)) 0 (Lower80811.LedgerData.lookup 11 (24+i)) := by decide +kernel

theorem checkedR11_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (32+i)) 0 (Lower80811.LedgerData.lookup 11 (32+i)) := by decide +kernel

theorem checkedR11_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (40+i)) 0 (Lower80811.LedgerData.lookup 11 (40+i)) := by decide +kernel

theorem checkedR11_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (48+i)) 0 (Lower80811.LedgerData.lookup 11 (48+i)) := by decide +kernel

theorem checkedR11_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (56+i)) 0 (Lower80811.LedgerData.lookup 11 (56+i)) := by decide +kernel

theorem checkedR11_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (64+i)) 0 (Lower80811.LedgerData.lookup 11 (64+i)) := by decide +kernel

theorem checkedR11_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (72+i)) 0 (Lower80811.LedgerData.lookup 11 (72+i)) := by decide +kernel

theorem checkedR11_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (80+i)) 0 (Lower80811.LedgerData.lookup 11 (80+i)) := by decide +kernel

theorem checkedR11_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (88+i)) 0 (Lower80811.LedgerData.lookup 11 (88+i)) := by decide +kernel

theorem checkedR11_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (96+i)) 0 (Lower80811.LedgerData.lookup 11 (96+i)) := by decide +kernel

theorem checkedR11_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (104+i)) 0 (Lower80811.LedgerData.lookup 11 (104+i)) := by decide +kernel

theorem checkedR11_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (112+i)) 0 (Lower80811.LedgerData.lookup 11 (112+i)) := by decide +kernel

theorem checkedR11_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 11 (120+i)) 0 (Lower80811.LedgerData.lookup 11 (120+i)) := by decide +kernel

theorem checkedR11_part128 : ∀ i ∈ List.range 4, RunsValid (rowContext 11 (128+i)) 0 (Lower80811.LedgerData.lookup 11 (128+i)) := by decide +kernel

theorem checkedR11 (V : ℕ) (hV : V ∈ List.range 132) : RunsValid (rowContext 11 V) 0 (Lower80811.LedgerData.lookup 11 V) := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR11_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR11_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR11_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR11_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR11_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR11_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR11_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR11_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_132 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR11_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR11_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR11_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR11_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_132 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR11_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR11_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_132 : V < 120
        · have hi := checkedR11_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_132 : V < 128
          · have hi := checkedR11_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR11_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR12_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (0+i)) 0 (Lower80811.LedgerData.lookup 12 (0+i)) := by decide +kernel

theorem checkedR12_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (8+i)) 0 (Lower80811.LedgerData.lookup 12 (8+i)) := by decide +kernel

theorem checkedR12_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (16+i)) 0 (Lower80811.LedgerData.lookup 12 (16+i)) := by decide +kernel

theorem checkedR12_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (24+i)) 0 (Lower80811.LedgerData.lookup 12 (24+i)) := by decide +kernel

theorem checkedR12_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (32+i)) 0 (Lower80811.LedgerData.lookup 12 (32+i)) := by decide +kernel

theorem checkedR12_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (40+i)) 0 (Lower80811.LedgerData.lookup 12 (40+i)) := by decide +kernel

theorem checkedR12_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (48+i)) 0 (Lower80811.LedgerData.lookup 12 (48+i)) := by decide +kernel

theorem checkedR12_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (56+i)) 0 (Lower80811.LedgerData.lookup 12 (56+i)) := by decide +kernel

theorem checkedR12_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (64+i)) 0 (Lower80811.LedgerData.lookup 12 (64+i)) := by decide +kernel

theorem checkedR12_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (72+i)) 0 (Lower80811.LedgerData.lookup 12 (72+i)) := by decide +kernel

theorem checkedR12_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (80+i)) 0 (Lower80811.LedgerData.lookup 12 (80+i)) := by decide +kernel

theorem checkedR12_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (88+i)) 0 (Lower80811.LedgerData.lookup 12 (88+i)) := by decide +kernel

theorem checkedR12_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (96+i)) 0 (Lower80811.LedgerData.lookup 12 (96+i)) := by decide +kernel

theorem checkedR12_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (104+i)) 0 (Lower80811.LedgerData.lookup 12 (104+i)) := by decide +kernel

theorem checkedR12_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (112+i)) 0 (Lower80811.LedgerData.lookup 12 (112+i)) := by decide +kernel

theorem checkedR12_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 12 (120+i)) 0 (Lower80811.LedgerData.lookup 12 (120+i)) := by decide +kernel

theorem checkedR12_part128 : ∀ i ∈ List.range 3, RunsValid (rowContext 12 (128+i)) 0 (Lower80811.LedgerData.lookup 12 (128+i)) := by decide +kernel

theorem checkedR12 (V : ℕ) (hV : V ∈ List.range 131) : RunsValid (rowContext 12 V) 0 (Lower80811.LedgerData.lookup 12 V) := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR12_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR12_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR12_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR12_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR12_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR12_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR12_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR12_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_131 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR12_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR12_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR12_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR12_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_131 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR12_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR12_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_131 : V < 120
        · have hi := checkedR12_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_131 : V < 128
          · have hi := checkedR12_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR12_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR13_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (0+i)) 0 (Lower80811.LedgerData.lookup 13 (0+i)) := by decide +kernel

theorem checkedR13_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (8+i)) 0 (Lower80811.LedgerData.lookup 13 (8+i)) := by decide +kernel

theorem checkedR13_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (16+i)) 0 (Lower80811.LedgerData.lookup 13 (16+i)) := by decide +kernel

theorem checkedR13_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (24+i)) 0 (Lower80811.LedgerData.lookup 13 (24+i)) := by decide +kernel

theorem checkedR13_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (32+i)) 0 (Lower80811.LedgerData.lookup 13 (32+i)) := by decide +kernel

theorem checkedR13_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (40+i)) 0 (Lower80811.LedgerData.lookup 13 (40+i)) := by decide +kernel

theorem checkedR13_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (48+i)) 0 (Lower80811.LedgerData.lookup 13 (48+i)) := by decide +kernel

theorem checkedR13_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (56+i)) 0 (Lower80811.LedgerData.lookup 13 (56+i)) := by decide +kernel

theorem checkedR13_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (64+i)) 0 (Lower80811.LedgerData.lookup 13 (64+i)) := by decide +kernel

theorem checkedR13_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (72+i)) 0 (Lower80811.LedgerData.lookup 13 (72+i)) := by decide +kernel

theorem checkedR13_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (80+i)) 0 (Lower80811.LedgerData.lookup 13 (80+i)) := by decide +kernel

theorem checkedR13_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (88+i)) 0 (Lower80811.LedgerData.lookup 13 (88+i)) := by decide +kernel

theorem checkedR13_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (96+i)) 0 (Lower80811.LedgerData.lookup 13 (96+i)) := by decide +kernel

theorem checkedR13_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (104+i)) 0 (Lower80811.LedgerData.lookup 13 (104+i)) := by decide +kernel

theorem checkedR13_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (112+i)) 0 (Lower80811.LedgerData.lookup 13 (112+i)) := by decide +kernel

theorem checkedR13_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 13 (120+i)) 0 (Lower80811.LedgerData.lookup 13 (120+i)) := by decide +kernel

theorem checkedR13_part128 : ∀ i ∈ List.range 2, RunsValid (rowContext 13 (128+i)) 0 (Lower80811.LedgerData.lookup 13 (128+i)) := by decide +kernel

theorem checkedR13 (V : ℕ) (hV : V ∈ List.range 130) : RunsValid (rowContext 13 V) 0 (Lower80811.LedgerData.lookup 13 V) := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR13_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR13_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR13_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR13_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR13_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR13_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR13_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR13_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_130 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR13_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR13_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR13_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR13_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_130 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR13_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR13_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_130 : V < 120
        · have hi := checkedR13_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_130 : V < 128
          · have hi := checkedR13_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR13_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR14_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (0+i)) 0 (Lower80811.LedgerData.lookup 14 (0+i)) := by decide +kernel

theorem checkedR14_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (8+i)) 0 (Lower80811.LedgerData.lookup 14 (8+i)) := by decide +kernel

theorem checkedR14_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (16+i)) 0 (Lower80811.LedgerData.lookup 14 (16+i)) := by decide +kernel

theorem checkedR14_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (24+i)) 0 (Lower80811.LedgerData.lookup 14 (24+i)) := by decide +kernel

theorem checkedR14_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (32+i)) 0 (Lower80811.LedgerData.lookup 14 (32+i)) := by decide +kernel

theorem checkedR14_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (40+i)) 0 (Lower80811.LedgerData.lookup 14 (40+i)) := by decide +kernel

theorem checkedR14_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (48+i)) 0 (Lower80811.LedgerData.lookup 14 (48+i)) := by decide +kernel

theorem checkedR14_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (56+i)) 0 (Lower80811.LedgerData.lookup 14 (56+i)) := by decide +kernel

theorem checkedR14_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (64+i)) 0 (Lower80811.LedgerData.lookup 14 (64+i)) := by decide +kernel

theorem checkedR14_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (72+i)) 0 (Lower80811.LedgerData.lookup 14 (72+i)) := by decide +kernel

theorem checkedR14_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (80+i)) 0 (Lower80811.LedgerData.lookup 14 (80+i)) := by decide +kernel

theorem checkedR14_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (88+i)) 0 (Lower80811.LedgerData.lookup 14 (88+i)) := by decide +kernel

theorem checkedR14_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (96+i)) 0 (Lower80811.LedgerData.lookup 14 (96+i)) := by decide +kernel

theorem checkedR14_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (104+i)) 0 (Lower80811.LedgerData.lookup 14 (104+i)) := by decide +kernel

theorem checkedR14_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (112+i)) 0 (Lower80811.LedgerData.lookup 14 (112+i)) := by decide +kernel

theorem checkedR14_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 14 (120+i)) 0 (Lower80811.LedgerData.lookup 14 (120+i)) := by decide +kernel

theorem checkedR14_part128 : ∀ i ∈ List.range 1, RunsValid (rowContext 14 (128+i)) 0 (Lower80811.LedgerData.lookup 14 (128+i)) := by decide +kernel

theorem checkedR14 (V : ℕ) (hV : V ∈ List.range 129) : RunsValid (rowContext 14 V) 0 (Lower80811.LedgerData.lookup 14 V) := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0_129 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR14_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR14_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR14_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR14_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR14_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR14_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR14_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR14_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_129 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR14_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR14_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR14_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR14_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_129 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR14_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR14_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_129 : V < 120
        · have hi := checkedR14_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · by_cases h120_129 : V < 128
          · have hi := checkedR14_part120 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi
          · have hi := checkedR14_part128 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR15_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (0+i)) 0 (Lower80811.LedgerData.lookup 15 (0+i)) := by decide +kernel

theorem checkedR15_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (8+i)) 0 (Lower80811.LedgerData.lookup 15 (8+i)) := by decide +kernel

theorem checkedR15_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (16+i)) 0 (Lower80811.LedgerData.lookup 15 (16+i)) := by decide +kernel

theorem checkedR15_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (24+i)) 0 (Lower80811.LedgerData.lookup 15 (24+i)) := by decide +kernel

theorem checkedR15_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (32+i)) 0 (Lower80811.LedgerData.lookup 15 (32+i)) := by decide +kernel

theorem checkedR15_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (40+i)) 0 (Lower80811.LedgerData.lookup 15 (40+i)) := by decide +kernel

theorem checkedR15_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (48+i)) 0 (Lower80811.LedgerData.lookup 15 (48+i)) := by decide +kernel

theorem checkedR15_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (56+i)) 0 (Lower80811.LedgerData.lookup 15 (56+i)) := by decide +kernel

theorem checkedR15_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (64+i)) 0 (Lower80811.LedgerData.lookup 15 (64+i)) := by decide +kernel

theorem checkedR15_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (72+i)) 0 (Lower80811.LedgerData.lookup 15 (72+i)) := by decide +kernel

theorem checkedR15_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (80+i)) 0 (Lower80811.LedgerData.lookup 15 (80+i)) := by decide +kernel

theorem checkedR15_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (88+i)) 0 (Lower80811.LedgerData.lookup 15 (88+i)) := by decide +kernel

theorem checkedR15_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (96+i)) 0 (Lower80811.LedgerData.lookup 15 (96+i)) := by decide +kernel

theorem checkedR15_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (104+i)) 0 (Lower80811.LedgerData.lookup 15 (104+i)) := by decide +kernel

theorem checkedR15_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (112+i)) 0 (Lower80811.LedgerData.lookup 15 (112+i)) := by decide +kernel

theorem checkedR15_part120 : ∀ i ∈ List.range 8, RunsValid (rowContext 15 (120+i)) 0 (Lower80811.LedgerData.lookup 15 (120+i)) := by decide +kernel

theorem checkedR15 (V : ℕ) (hV : V ∈ List.range 128) : RunsValid (rowContext 15 V) 0 (Lower80811.LedgerData.lookup 15 V) := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR15_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR15_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR15_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR15_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR15_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR15_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR15_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR15_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR15_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR15_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR15_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR15_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR15_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR15_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_128 : V < 120
        · have hi := checkedR15_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR15_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR16_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (0+i)) 0 (Lower80811.LedgerData.lookup 16 (0+i)) := by decide +kernel

theorem checkedR16_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (8+i)) 0 (Lower80811.LedgerData.lookup 16 (8+i)) := by decide +kernel

theorem checkedR16_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (16+i)) 0 (Lower80811.LedgerData.lookup 16 (16+i)) := by decide +kernel

theorem checkedR16_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (24+i)) 0 (Lower80811.LedgerData.lookup 16 (24+i)) := by decide +kernel

theorem checkedR16_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (32+i)) 0 (Lower80811.LedgerData.lookup 16 (32+i)) := by decide +kernel

theorem checkedR16_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (40+i)) 0 (Lower80811.LedgerData.lookup 16 (40+i)) := by decide +kernel

theorem checkedR16_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (48+i)) 0 (Lower80811.LedgerData.lookup 16 (48+i)) := by decide +kernel

theorem checkedR16_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (56+i)) 0 (Lower80811.LedgerData.lookup 16 (56+i)) := by decide +kernel

theorem checkedR16_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (64+i)) 0 (Lower80811.LedgerData.lookup 16 (64+i)) := by decide +kernel

theorem checkedR16_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (72+i)) 0 (Lower80811.LedgerData.lookup 16 (72+i)) := by decide +kernel

theorem checkedR16_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (80+i)) 0 (Lower80811.LedgerData.lookup 16 (80+i)) := by decide +kernel

theorem checkedR16_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (88+i)) 0 (Lower80811.LedgerData.lookup 16 (88+i)) := by decide +kernel

theorem checkedR16_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (96+i)) 0 (Lower80811.LedgerData.lookup 16 (96+i)) := by decide +kernel

theorem checkedR16_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (104+i)) 0 (Lower80811.LedgerData.lookup 16 (104+i)) := by decide +kernel

theorem checkedR16_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 16 (112+i)) 0 (Lower80811.LedgerData.lookup 16 (112+i)) := by decide +kernel

theorem checkedR16_part120 : ∀ i ∈ List.range 7, RunsValid (rowContext 16 (120+i)) 0 (Lower80811.LedgerData.lookup 16 (120+i)) := by decide +kernel

theorem checkedR16 (V : ℕ) (hV : V ∈ List.range 127) : RunsValid (rowContext 16 V) 0 (Lower80811.LedgerData.lookup 16 V) := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR16_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR16_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR16_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR16_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR16_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR16_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR16_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR16_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_127 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR16_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR16_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR16_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR16_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_127 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR16_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR16_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_127 : V < 120
        · have hi := checkedR16_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR16_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR17_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (0+i)) 0 (Lower80811.LedgerData.lookup 17 (0+i)) := by decide +kernel

theorem checkedR17_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (8+i)) 0 (Lower80811.LedgerData.lookup 17 (8+i)) := by decide +kernel

theorem checkedR17_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (16+i)) 0 (Lower80811.LedgerData.lookup 17 (16+i)) := by decide +kernel

theorem checkedR17_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (24+i)) 0 (Lower80811.LedgerData.lookup 17 (24+i)) := by decide +kernel

theorem checkedR17_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (32+i)) 0 (Lower80811.LedgerData.lookup 17 (32+i)) := by decide +kernel

theorem checkedR17_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (40+i)) 0 (Lower80811.LedgerData.lookup 17 (40+i)) := by decide +kernel

theorem checkedR17_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (48+i)) 0 (Lower80811.LedgerData.lookup 17 (48+i)) := by decide +kernel

theorem checkedR17_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (56+i)) 0 (Lower80811.LedgerData.lookup 17 (56+i)) := by decide +kernel

theorem checkedR17_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (64+i)) 0 (Lower80811.LedgerData.lookup 17 (64+i)) := by decide +kernel

theorem checkedR17_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (72+i)) 0 (Lower80811.LedgerData.lookup 17 (72+i)) := by decide +kernel

theorem checkedR17_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (80+i)) 0 (Lower80811.LedgerData.lookup 17 (80+i)) := by decide +kernel

theorem checkedR17_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (88+i)) 0 (Lower80811.LedgerData.lookup 17 (88+i)) := by decide +kernel

theorem checkedR17_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (96+i)) 0 (Lower80811.LedgerData.lookup 17 (96+i)) := by decide +kernel

theorem checkedR17_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (104+i)) 0 (Lower80811.LedgerData.lookup 17 (104+i)) := by decide +kernel

theorem checkedR17_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 17 (112+i)) 0 (Lower80811.LedgerData.lookup 17 (112+i)) := by decide +kernel

theorem checkedR17_part120 : ∀ i ∈ List.range 6, RunsValid (rowContext 17 (120+i)) 0 (Lower80811.LedgerData.lookup 17 (120+i)) := by decide +kernel

theorem checkedR17 (V : ℕ) (hV : V ∈ List.range 126) : RunsValid (rowContext 17 V) 0 (Lower80811.LedgerData.lookup 17 V) := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR17_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR17_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR17_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR17_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR17_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR17_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR17_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR17_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_126 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR17_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR17_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR17_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR17_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_126 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR17_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR17_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_126 : V < 120
        · have hi := checkedR17_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR17_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR18_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (0+i)) 0 (Lower80811.LedgerData.lookup 18 (0+i)) := by decide +kernel

theorem checkedR18_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (8+i)) 0 (Lower80811.LedgerData.lookup 18 (8+i)) := by decide +kernel

theorem checkedR18_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (16+i)) 0 (Lower80811.LedgerData.lookup 18 (16+i)) := by decide +kernel

theorem checkedR18_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (24+i)) 0 (Lower80811.LedgerData.lookup 18 (24+i)) := by decide +kernel

theorem checkedR18_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (32+i)) 0 (Lower80811.LedgerData.lookup 18 (32+i)) := by decide +kernel

theorem checkedR18_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (40+i)) 0 (Lower80811.LedgerData.lookup 18 (40+i)) := by decide +kernel

theorem checkedR18_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (48+i)) 0 (Lower80811.LedgerData.lookup 18 (48+i)) := by decide +kernel

theorem checkedR18_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (56+i)) 0 (Lower80811.LedgerData.lookup 18 (56+i)) := by decide +kernel

theorem checkedR18_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (64+i)) 0 (Lower80811.LedgerData.lookup 18 (64+i)) := by decide +kernel

theorem checkedR18_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (72+i)) 0 (Lower80811.LedgerData.lookup 18 (72+i)) := by decide +kernel

theorem checkedR18_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (80+i)) 0 (Lower80811.LedgerData.lookup 18 (80+i)) := by decide +kernel

theorem checkedR18_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (88+i)) 0 (Lower80811.LedgerData.lookup 18 (88+i)) := by decide +kernel

theorem checkedR18_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (96+i)) 0 (Lower80811.LedgerData.lookup 18 (96+i)) := by decide +kernel

theorem checkedR18_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (104+i)) 0 (Lower80811.LedgerData.lookup 18 (104+i)) := by decide +kernel

theorem checkedR18_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 18 (112+i)) 0 (Lower80811.LedgerData.lookup 18 (112+i)) := by decide +kernel

theorem checkedR18_part120 : ∀ i ∈ List.range 5, RunsValid (rowContext 18 (120+i)) 0 (Lower80811.LedgerData.lookup 18 (120+i)) := by decide +kernel

theorem checkedR18 (V : ℕ) (hV : V ∈ List.range 125) : RunsValid (rowContext 18 V) 0 (Lower80811.LedgerData.lookup 18 V) := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR18_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR18_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR18_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR18_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR18_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR18_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR18_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR18_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_125 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR18_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR18_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR18_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR18_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_125 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR18_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR18_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_125 : V < 120
        · have hi := checkedR18_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR18_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR19_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (0+i)) 0 (Lower80811.LedgerData.lookup 19 (0+i)) := by decide +kernel

theorem checkedR19_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (8+i)) 0 (Lower80811.LedgerData.lookup 19 (8+i)) := by decide +kernel

theorem checkedR19_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (16+i)) 0 (Lower80811.LedgerData.lookup 19 (16+i)) := by decide +kernel

theorem checkedR19_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (24+i)) 0 (Lower80811.LedgerData.lookup 19 (24+i)) := by decide +kernel

theorem checkedR19_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (32+i)) 0 (Lower80811.LedgerData.lookup 19 (32+i)) := by decide +kernel

theorem checkedR19_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (40+i)) 0 (Lower80811.LedgerData.lookup 19 (40+i)) := by decide +kernel

theorem checkedR19_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (48+i)) 0 (Lower80811.LedgerData.lookup 19 (48+i)) := by decide +kernel

theorem checkedR19_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (56+i)) 0 (Lower80811.LedgerData.lookup 19 (56+i)) := by decide +kernel

theorem checkedR19_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (64+i)) 0 (Lower80811.LedgerData.lookup 19 (64+i)) := by decide +kernel

theorem checkedR19_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (72+i)) 0 (Lower80811.LedgerData.lookup 19 (72+i)) := by decide +kernel

theorem checkedR19_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (80+i)) 0 (Lower80811.LedgerData.lookup 19 (80+i)) := by decide +kernel

theorem checkedR19_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (88+i)) 0 (Lower80811.LedgerData.lookup 19 (88+i)) := by decide +kernel

theorem checkedR19_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (96+i)) 0 (Lower80811.LedgerData.lookup 19 (96+i)) := by decide +kernel

theorem checkedR19_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (104+i)) 0 (Lower80811.LedgerData.lookup 19 (104+i)) := by decide +kernel

theorem checkedR19_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 19 (112+i)) 0 (Lower80811.LedgerData.lookup 19 (112+i)) := by decide +kernel

theorem checkedR19_part120 : ∀ i ∈ List.range 4, RunsValid (rowContext 19 (120+i)) 0 (Lower80811.LedgerData.lookup 19 (120+i)) := by decide +kernel

theorem checkedR19 (V : ℕ) (hV : V ∈ List.range 124) : RunsValid (rowContext 19 V) 0 (Lower80811.LedgerData.lookup 19 V) := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR19_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR19_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR19_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR19_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR19_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR19_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR19_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR19_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_124 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR19_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR19_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR19_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR19_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_124 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR19_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR19_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_124 : V < 120
        · have hi := checkedR19_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR19_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR20_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (0+i)) 0 (Lower80811.LedgerData.lookup 20 (0+i)) := by decide +kernel

theorem checkedR20_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (8+i)) 0 (Lower80811.LedgerData.lookup 20 (8+i)) := by decide +kernel

theorem checkedR20_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (16+i)) 0 (Lower80811.LedgerData.lookup 20 (16+i)) := by decide +kernel

theorem checkedR20_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (24+i)) 0 (Lower80811.LedgerData.lookup 20 (24+i)) := by decide +kernel

theorem checkedR20_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (32+i)) 0 (Lower80811.LedgerData.lookup 20 (32+i)) := by decide +kernel

theorem checkedR20_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (40+i)) 0 (Lower80811.LedgerData.lookup 20 (40+i)) := by decide +kernel

theorem checkedR20_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (48+i)) 0 (Lower80811.LedgerData.lookup 20 (48+i)) := by decide +kernel

theorem checkedR20_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (56+i)) 0 (Lower80811.LedgerData.lookup 20 (56+i)) := by decide +kernel

theorem checkedR20_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (64+i)) 0 (Lower80811.LedgerData.lookup 20 (64+i)) := by decide +kernel

theorem checkedR20_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (72+i)) 0 (Lower80811.LedgerData.lookup 20 (72+i)) := by decide +kernel

theorem checkedR20_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (80+i)) 0 (Lower80811.LedgerData.lookup 20 (80+i)) := by decide +kernel

theorem checkedR20_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (88+i)) 0 (Lower80811.LedgerData.lookup 20 (88+i)) := by decide +kernel

theorem checkedR20_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (96+i)) 0 (Lower80811.LedgerData.lookup 20 (96+i)) := by decide +kernel

theorem checkedR20_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (104+i)) 0 (Lower80811.LedgerData.lookup 20 (104+i)) := by decide +kernel

theorem checkedR20_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 20 (112+i)) 0 (Lower80811.LedgerData.lookup 20 (112+i)) := by decide +kernel

theorem checkedR20_part120 : ∀ i ∈ List.range 3, RunsValid (rowContext 20 (120+i)) 0 (Lower80811.LedgerData.lookup 20 (120+i)) := by decide +kernel

theorem checkedR20 (V : ℕ) (hV : V ∈ List.range 123) : RunsValid (rowContext 20 V) 0 (Lower80811.LedgerData.lookup 20 V) := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR20_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR20_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR20_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR20_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR20_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR20_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR20_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR20_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_123 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR20_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR20_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR20_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR20_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_123 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR20_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR20_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_123 : V < 120
        · have hi := checkedR20_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR20_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR21_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (0+i)) 0 (Lower80811.LedgerData.lookup 21 (0+i)) := by decide +kernel

theorem checkedR21_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (8+i)) 0 (Lower80811.LedgerData.lookup 21 (8+i)) := by decide +kernel

theorem checkedR21_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (16+i)) 0 (Lower80811.LedgerData.lookup 21 (16+i)) := by decide +kernel

theorem checkedR21_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (24+i)) 0 (Lower80811.LedgerData.lookup 21 (24+i)) := by decide +kernel

theorem checkedR21_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (32+i)) 0 (Lower80811.LedgerData.lookup 21 (32+i)) := by decide +kernel

theorem checkedR21_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (40+i)) 0 (Lower80811.LedgerData.lookup 21 (40+i)) := by decide +kernel

theorem checkedR21_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (48+i)) 0 (Lower80811.LedgerData.lookup 21 (48+i)) := by decide +kernel

theorem checkedR21_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (56+i)) 0 (Lower80811.LedgerData.lookup 21 (56+i)) := by decide +kernel

theorem checkedR21_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (64+i)) 0 (Lower80811.LedgerData.lookup 21 (64+i)) := by decide +kernel

theorem checkedR21_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (72+i)) 0 (Lower80811.LedgerData.lookup 21 (72+i)) := by decide +kernel

theorem checkedR21_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (80+i)) 0 (Lower80811.LedgerData.lookup 21 (80+i)) := by decide +kernel

theorem checkedR21_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (88+i)) 0 (Lower80811.LedgerData.lookup 21 (88+i)) := by decide +kernel

theorem checkedR21_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (96+i)) 0 (Lower80811.LedgerData.lookup 21 (96+i)) := by decide +kernel

theorem checkedR21_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (104+i)) 0 (Lower80811.LedgerData.lookup 21 (104+i)) := by decide +kernel

theorem checkedR21_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 21 (112+i)) 0 (Lower80811.LedgerData.lookup 21 (112+i)) := by decide +kernel

theorem checkedR21_part120 : ∀ i ∈ List.range 2, RunsValid (rowContext 21 (120+i)) 0 (Lower80811.LedgerData.lookup 21 (120+i)) := by decide +kernel

theorem checkedR21 (V : ℕ) (hV : V ∈ List.range 122) : RunsValid (rowContext 21 V) 0 (Lower80811.LedgerData.lookup 21 V) := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR21_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR21_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR21_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR21_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR21_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR21_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR21_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR21_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_122 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR21_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR21_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR21_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR21_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_122 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR21_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR21_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_122 : V < 120
        · have hi := checkedR21_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR21_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR22_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (0+i)) 0 (Lower80811.LedgerData.lookup 22 (0+i)) := by decide +kernel

theorem checkedR22_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (8+i)) 0 (Lower80811.LedgerData.lookup 22 (8+i)) := by decide +kernel

theorem checkedR22_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (16+i)) 0 (Lower80811.LedgerData.lookup 22 (16+i)) := by decide +kernel

theorem checkedR22_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (24+i)) 0 (Lower80811.LedgerData.lookup 22 (24+i)) := by decide +kernel

theorem checkedR22_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (32+i)) 0 (Lower80811.LedgerData.lookup 22 (32+i)) := by decide +kernel

theorem checkedR22_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (40+i)) 0 (Lower80811.LedgerData.lookup 22 (40+i)) := by decide +kernel

theorem checkedR22_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (48+i)) 0 (Lower80811.LedgerData.lookup 22 (48+i)) := by decide +kernel

theorem checkedR22_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (56+i)) 0 (Lower80811.LedgerData.lookup 22 (56+i)) := by decide +kernel

theorem checkedR22_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (64+i)) 0 (Lower80811.LedgerData.lookup 22 (64+i)) := by decide +kernel

theorem checkedR22_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (72+i)) 0 (Lower80811.LedgerData.lookup 22 (72+i)) := by decide +kernel

theorem checkedR22_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (80+i)) 0 (Lower80811.LedgerData.lookup 22 (80+i)) := by decide +kernel

theorem checkedR22_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (88+i)) 0 (Lower80811.LedgerData.lookup 22 (88+i)) := by decide +kernel

theorem checkedR22_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (96+i)) 0 (Lower80811.LedgerData.lookup 22 (96+i)) := by decide +kernel

theorem checkedR22_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (104+i)) 0 (Lower80811.LedgerData.lookup 22 (104+i)) := by decide +kernel

theorem checkedR22_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 22 (112+i)) 0 (Lower80811.LedgerData.lookup 22 (112+i)) := by decide +kernel

theorem checkedR22_part120 : ∀ i ∈ List.range 1, RunsValid (rowContext 22 (120+i)) 0 (Lower80811.LedgerData.lookup 22 (120+i)) := by decide +kernel

theorem checkedR22 (V : ℕ) (hV : V ∈ List.range 121) : RunsValid (rowContext 22 V) 0 (Lower80811.LedgerData.lookup 22 V) := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · have hi := checkedR22_part0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
        · have hi := checkedR22_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
      · by_cases h16_32 : V < 24
        · have hi := checkedR22_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
        · have hi := checkedR22_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · have hi := checkedR22_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
        · have hi := checkedR22_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
      · by_cases h48_64 : V < 56
        · have hi := checkedR22_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
        · have hi := checkedR22_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
  · by_cases h64_121 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · have hi := checkedR22_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR22_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
      · by_cases h80_96 : V < 88
        · have hi := checkedR22_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR22_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
    · by_cases h96_121 : V < 112
      · by_cases h96_112 : V < 104
        · have hi := checkedR22_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR22_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
      · by_cases h112_121 : V < 120
        · have hi := checkedR22_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi
        · have hi := checkedR22_part120 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR23_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (0+i)) 0 (Lower80811.LedgerData.lookup 23 (0+i)) := by decide +kernel

theorem checkedR23_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (8+i)) 0 (Lower80811.LedgerData.lookup 23 (8+i)) := by decide +kernel

theorem checkedR23_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (16+i)) 0 (Lower80811.LedgerData.lookup 23 (16+i)) := by decide +kernel

theorem checkedR23_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (24+i)) 0 (Lower80811.LedgerData.lookup 23 (24+i)) := by decide +kernel

theorem checkedR23_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (32+i)) 0 (Lower80811.LedgerData.lookup 23 (32+i)) := by decide +kernel

theorem checkedR23_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (40+i)) 0 (Lower80811.LedgerData.lookup 23 (40+i)) := by decide +kernel

theorem checkedR23_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (48+i)) 0 (Lower80811.LedgerData.lookup 23 (48+i)) := by decide +kernel

theorem checkedR23_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (56+i)) 0 (Lower80811.LedgerData.lookup 23 (56+i)) := by decide +kernel

theorem checkedR23_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (64+i)) 0 (Lower80811.LedgerData.lookup 23 (64+i)) := by decide +kernel

theorem checkedR23_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (72+i)) 0 (Lower80811.LedgerData.lookup 23 (72+i)) := by decide +kernel

theorem checkedR23_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (80+i)) 0 (Lower80811.LedgerData.lookup 23 (80+i)) := by decide +kernel

theorem checkedR23_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (88+i)) 0 (Lower80811.LedgerData.lookup 23 (88+i)) := by decide +kernel

theorem checkedR23_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (96+i)) 0 (Lower80811.LedgerData.lookup 23 (96+i)) := by decide +kernel

theorem checkedR23_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (104+i)) 0 (Lower80811.LedgerData.lookup 23 (104+i)) := by decide +kernel

theorem checkedR23_part112 : ∀ i ∈ List.range 8, RunsValid (rowContext 23 (112+i)) 0 (Lower80811.LedgerData.lookup 23 (112+i)) := by decide +kernel

theorem checkedR23 (V : ℕ) (hV : V ∈ List.range 120) : RunsValid (rowContext 23 V) 0 (Lower80811.LedgerData.lookup 23 V) := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR23_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR23_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR23_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR23_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR23_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR23_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR23_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_120 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR23_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR23_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR23_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR23_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_120 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR23_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR23_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_120 : V < 112
        · have hi := checkedR23_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR23_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR24_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (0+i)) 0 (Lower80811.LedgerData.lookup 24 (0+i)) := by decide +kernel

theorem checkedR24_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (8+i)) 0 (Lower80811.LedgerData.lookup 24 (8+i)) := by decide +kernel

theorem checkedR24_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (16+i)) 0 (Lower80811.LedgerData.lookup 24 (16+i)) := by decide +kernel

theorem checkedR24_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (24+i)) 0 (Lower80811.LedgerData.lookup 24 (24+i)) := by decide +kernel

theorem checkedR24_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (32+i)) 0 (Lower80811.LedgerData.lookup 24 (32+i)) := by decide +kernel

theorem checkedR24_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (40+i)) 0 (Lower80811.LedgerData.lookup 24 (40+i)) := by decide +kernel

theorem checkedR24_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (48+i)) 0 (Lower80811.LedgerData.lookup 24 (48+i)) := by decide +kernel

theorem checkedR24_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (56+i)) 0 (Lower80811.LedgerData.lookup 24 (56+i)) := by decide +kernel

theorem checkedR24_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (64+i)) 0 (Lower80811.LedgerData.lookup 24 (64+i)) := by decide +kernel

theorem checkedR24_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (72+i)) 0 (Lower80811.LedgerData.lookup 24 (72+i)) := by decide +kernel

theorem checkedR24_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (80+i)) 0 (Lower80811.LedgerData.lookup 24 (80+i)) := by decide +kernel

theorem checkedR24_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (88+i)) 0 (Lower80811.LedgerData.lookup 24 (88+i)) := by decide +kernel

theorem checkedR24_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (96+i)) 0 (Lower80811.LedgerData.lookup 24 (96+i)) := by decide +kernel

theorem checkedR24_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 24 (104+i)) 0 (Lower80811.LedgerData.lookup 24 (104+i)) := by decide +kernel

theorem checkedR24_part112 : ∀ i ∈ List.range 7, RunsValid (rowContext 24 (112+i)) 0 (Lower80811.LedgerData.lookup 24 (112+i)) := by decide +kernel

theorem checkedR24 (V : ℕ) (hV : V ∈ List.range 119) : RunsValid (rowContext 24 V) 0 (Lower80811.LedgerData.lookup 24 V) := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR24_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR24_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR24_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR24_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR24_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR24_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR24_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_119 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR24_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR24_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR24_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR24_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_119 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR24_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR24_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_119 : V < 112
        · have hi := checkedR24_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR24_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR25_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (0+i)) 0 (Lower80811.LedgerData.lookup 25 (0+i)) := by decide +kernel

theorem checkedR25_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (8+i)) 0 (Lower80811.LedgerData.lookup 25 (8+i)) := by decide +kernel

theorem checkedR25_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (16+i)) 0 (Lower80811.LedgerData.lookup 25 (16+i)) := by decide +kernel

theorem checkedR25_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (24+i)) 0 (Lower80811.LedgerData.lookup 25 (24+i)) := by decide +kernel

theorem checkedR25_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (32+i)) 0 (Lower80811.LedgerData.lookup 25 (32+i)) := by decide +kernel

theorem checkedR25_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (40+i)) 0 (Lower80811.LedgerData.lookup 25 (40+i)) := by decide +kernel

theorem checkedR25_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (48+i)) 0 (Lower80811.LedgerData.lookup 25 (48+i)) := by decide +kernel

theorem checkedR25_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (56+i)) 0 (Lower80811.LedgerData.lookup 25 (56+i)) := by decide +kernel

theorem checkedR25_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (64+i)) 0 (Lower80811.LedgerData.lookup 25 (64+i)) := by decide +kernel

theorem checkedR25_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (72+i)) 0 (Lower80811.LedgerData.lookup 25 (72+i)) := by decide +kernel

theorem checkedR25_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (80+i)) 0 (Lower80811.LedgerData.lookup 25 (80+i)) := by decide +kernel

theorem checkedR25_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (88+i)) 0 (Lower80811.LedgerData.lookup 25 (88+i)) := by decide +kernel

theorem checkedR25_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (96+i)) 0 (Lower80811.LedgerData.lookup 25 (96+i)) := by decide +kernel

theorem checkedR25_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 25 (104+i)) 0 (Lower80811.LedgerData.lookup 25 (104+i)) := by decide +kernel

theorem checkedR25_part112 : ∀ i ∈ List.range 6, RunsValid (rowContext 25 (112+i)) 0 (Lower80811.LedgerData.lookup 25 (112+i)) := by decide +kernel

theorem checkedR25 (V : ℕ) (hV : V ∈ List.range 118) : RunsValid (rowContext 25 V) 0 (Lower80811.LedgerData.lookup 25 V) := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR25_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR25_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR25_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR25_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR25_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR25_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR25_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_118 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR25_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR25_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR25_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR25_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_118 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR25_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR25_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_118 : V < 112
        · have hi := checkedR25_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR25_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR26_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (0+i)) 0 (Lower80811.LedgerData.lookup 26 (0+i)) := by decide +kernel

theorem checkedR26_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (8+i)) 0 (Lower80811.LedgerData.lookup 26 (8+i)) := by decide +kernel

theorem checkedR26_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (16+i)) 0 (Lower80811.LedgerData.lookup 26 (16+i)) := by decide +kernel

theorem checkedR26_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (24+i)) 0 (Lower80811.LedgerData.lookup 26 (24+i)) := by decide +kernel

theorem checkedR26_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (32+i)) 0 (Lower80811.LedgerData.lookup 26 (32+i)) := by decide +kernel

theorem checkedR26_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (40+i)) 0 (Lower80811.LedgerData.lookup 26 (40+i)) := by decide +kernel

theorem checkedR26_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (48+i)) 0 (Lower80811.LedgerData.lookup 26 (48+i)) := by decide +kernel

theorem checkedR26_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (56+i)) 0 (Lower80811.LedgerData.lookup 26 (56+i)) := by decide +kernel

theorem checkedR26_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (64+i)) 0 (Lower80811.LedgerData.lookup 26 (64+i)) := by decide +kernel

theorem checkedR26_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (72+i)) 0 (Lower80811.LedgerData.lookup 26 (72+i)) := by decide +kernel

theorem checkedR26_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (80+i)) 0 (Lower80811.LedgerData.lookup 26 (80+i)) := by decide +kernel

theorem checkedR26_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (88+i)) 0 (Lower80811.LedgerData.lookup 26 (88+i)) := by decide +kernel

theorem checkedR26_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (96+i)) 0 (Lower80811.LedgerData.lookup 26 (96+i)) := by decide +kernel

theorem checkedR26_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 26 (104+i)) 0 (Lower80811.LedgerData.lookup 26 (104+i)) := by decide +kernel

theorem checkedR26_part112 : ∀ i ∈ List.range 5, RunsValid (rowContext 26 (112+i)) 0 (Lower80811.LedgerData.lookup 26 (112+i)) := by decide +kernel

theorem checkedR26 (V : ℕ) (hV : V ∈ List.range 117) : RunsValid (rowContext 26 V) 0 (Lower80811.LedgerData.lookup 26 V) := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR26_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR26_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR26_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR26_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR26_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR26_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR26_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_117 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR26_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR26_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR26_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR26_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_117 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR26_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR26_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_117 : V < 112
        · have hi := checkedR26_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR26_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR27_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (0+i)) 0 (Lower80811.LedgerData.lookup 27 (0+i)) := by decide +kernel

theorem checkedR27_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (8+i)) 0 (Lower80811.LedgerData.lookup 27 (8+i)) := by decide +kernel

theorem checkedR27_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (16+i)) 0 (Lower80811.LedgerData.lookup 27 (16+i)) := by decide +kernel

theorem checkedR27_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (24+i)) 0 (Lower80811.LedgerData.lookup 27 (24+i)) := by decide +kernel

theorem checkedR27_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (32+i)) 0 (Lower80811.LedgerData.lookup 27 (32+i)) := by decide +kernel

theorem checkedR27_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (40+i)) 0 (Lower80811.LedgerData.lookup 27 (40+i)) := by decide +kernel

theorem checkedR27_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (48+i)) 0 (Lower80811.LedgerData.lookup 27 (48+i)) := by decide +kernel

theorem checkedR27_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (56+i)) 0 (Lower80811.LedgerData.lookup 27 (56+i)) := by decide +kernel

theorem checkedR27_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (64+i)) 0 (Lower80811.LedgerData.lookup 27 (64+i)) := by decide +kernel

theorem checkedR27_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (72+i)) 0 (Lower80811.LedgerData.lookup 27 (72+i)) := by decide +kernel

theorem checkedR27_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (80+i)) 0 (Lower80811.LedgerData.lookup 27 (80+i)) := by decide +kernel

theorem checkedR27_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (88+i)) 0 (Lower80811.LedgerData.lookup 27 (88+i)) := by decide +kernel

theorem checkedR27_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (96+i)) 0 (Lower80811.LedgerData.lookup 27 (96+i)) := by decide +kernel

theorem checkedR27_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 27 (104+i)) 0 (Lower80811.LedgerData.lookup 27 (104+i)) := by decide +kernel

theorem checkedR27_part112 : ∀ i ∈ List.range 4, RunsValid (rowContext 27 (112+i)) 0 (Lower80811.LedgerData.lookup 27 (112+i)) := by decide +kernel

theorem checkedR27 (V : ℕ) (hV : V ∈ List.range 116) : RunsValid (rowContext 27 V) 0 (Lower80811.LedgerData.lookup 27 V) := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR27_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR27_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR27_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR27_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR27_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR27_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR27_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_116 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR27_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR27_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR27_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR27_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_116 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR27_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR27_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_116 : V < 112
        · have hi := checkedR27_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR27_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR28_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (0+i)) 0 (Lower80811.LedgerData.lookup 28 (0+i)) := by decide +kernel

theorem checkedR28_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (8+i)) 0 (Lower80811.LedgerData.lookup 28 (8+i)) := by decide +kernel

theorem checkedR28_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (16+i)) 0 (Lower80811.LedgerData.lookup 28 (16+i)) := by decide +kernel

theorem checkedR28_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (24+i)) 0 (Lower80811.LedgerData.lookup 28 (24+i)) := by decide +kernel

theorem checkedR28_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (32+i)) 0 (Lower80811.LedgerData.lookup 28 (32+i)) := by decide +kernel

theorem checkedR28_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (40+i)) 0 (Lower80811.LedgerData.lookup 28 (40+i)) := by decide +kernel

theorem checkedR28_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (48+i)) 0 (Lower80811.LedgerData.lookup 28 (48+i)) := by decide +kernel

theorem checkedR28_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (56+i)) 0 (Lower80811.LedgerData.lookup 28 (56+i)) := by decide +kernel

theorem checkedR28_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (64+i)) 0 (Lower80811.LedgerData.lookup 28 (64+i)) := by decide +kernel

theorem checkedR28_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (72+i)) 0 (Lower80811.LedgerData.lookup 28 (72+i)) := by decide +kernel

theorem checkedR28_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (80+i)) 0 (Lower80811.LedgerData.lookup 28 (80+i)) := by decide +kernel

theorem checkedR28_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (88+i)) 0 (Lower80811.LedgerData.lookup 28 (88+i)) := by decide +kernel

theorem checkedR28_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (96+i)) 0 (Lower80811.LedgerData.lookup 28 (96+i)) := by decide +kernel

theorem checkedR28_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 28 (104+i)) 0 (Lower80811.LedgerData.lookup 28 (104+i)) := by decide +kernel

theorem checkedR28_part112 : ∀ i ∈ List.range 3, RunsValid (rowContext 28 (112+i)) 0 (Lower80811.LedgerData.lookup 28 (112+i)) := by decide +kernel

theorem checkedR28 (V : ℕ) (hV : V ∈ List.range 115) : RunsValid (rowContext 28 V) 0 (Lower80811.LedgerData.lookup 28 V) := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR28_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR28_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR28_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR28_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR28_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR28_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR28_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_115 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR28_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR28_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR28_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR28_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_115 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR28_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR28_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_115 : V < 112
        · have hi := checkedR28_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR28_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR29_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (0+i)) 0 (Lower80811.LedgerData.lookup 29 (0+i)) := by decide +kernel

theorem checkedR29_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (8+i)) 0 (Lower80811.LedgerData.lookup 29 (8+i)) := by decide +kernel

theorem checkedR29_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (16+i)) 0 (Lower80811.LedgerData.lookup 29 (16+i)) := by decide +kernel

theorem checkedR29_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (24+i)) 0 (Lower80811.LedgerData.lookup 29 (24+i)) := by decide +kernel

theorem checkedR29_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (32+i)) 0 (Lower80811.LedgerData.lookup 29 (32+i)) := by decide +kernel

theorem checkedR29_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (40+i)) 0 (Lower80811.LedgerData.lookup 29 (40+i)) := by decide +kernel

theorem checkedR29_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (48+i)) 0 (Lower80811.LedgerData.lookup 29 (48+i)) := by decide +kernel

theorem checkedR29_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (56+i)) 0 (Lower80811.LedgerData.lookup 29 (56+i)) := by decide +kernel

theorem checkedR29_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (64+i)) 0 (Lower80811.LedgerData.lookup 29 (64+i)) := by decide +kernel

theorem checkedR29_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (72+i)) 0 (Lower80811.LedgerData.lookup 29 (72+i)) := by decide +kernel

theorem checkedR29_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (80+i)) 0 (Lower80811.LedgerData.lookup 29 (80+i)) := by decide +kernel

theorem checkedR29_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (88+i)) 0 (Lower80811.LedgerData.lookup 29 (88+i)) := by decide +kernel

theorem checkedR29_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (96+i)) 0 (Lower80811.LedgerData.lookup 29 (96+i)) := by decide +kernel

theorem checkedR29_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 29 (104+i)) 0 (Lower80811.LedgerData.lookup 29 (104+i)) := by decide +kernel

theorem checkedR29_part112 : ∀ i ∈ List.range 2, RunsValid (rowContext 29 (112+i)) 0 (Lower80811.LedgerData.lookup 29 (112+i)) := by decide +kernel

theorem checkedR29 (V : ℕ) (hV : V ∈ List.range 114) : RunsValid (rowContext 29 V) 0 (Lower80811.LedgerData.lookup 29 V) := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR29_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR29_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR29_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR29_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR29_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR29_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR29_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_114 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR29_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR29_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR29_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR29_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_114 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR29_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR29_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_114 : V < 112
        · have hi := checkedR29_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR29_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR30_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (0+i)) 0 (Lower80811.LedgerData.lookup 30 (0+i)) := by decide +kernel

theorem checkedR30_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (8+i)) 0 (Lower80811.LedgerData.lookup 30 (8+i)) := by decide +kernel

theorem checkedR30_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (16+i)) 0 (Lower80811.LedgerData.lookup 30 (16+i)) := by decide +kernel

theorem checkedR30_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (24+i)) 0 (Lower80811.LedgerData.lookup 30 (24+i)) := by decide +kernel

theorem checkedR30_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (32+i)) 0 (Lower80811.LedgerData.lookup 30 (32+i)) := by decide +kernel

theorem checkedR30_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (40+i)) 0 (Lower80811.LedgerData.lookup 30 (40+i)) := by decide +kernel

theorem checkedR30_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (48+i)) 0 (Lower80811.LedgerData.lookup 30 (48+i)) := by decide +kernel

theorem checkedR30_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (56+i)) 0 (Lower80811.LedgerData.lookup 30 (56+i)) := by decide +kernel

theorem checkedR30_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (64+i)) 0 (Lower80811.LedgerData.lookup 30 (64+i)) := by decide +kernel

theorem checkedR30_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (72+i)) 0 (Lower80811.LedgerData.lookup 30 (72+i)) := by decide +kernel

theorem checkedR30_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (80+i)) 0 (Lower80811.LedgerData.lookup 30 (80+i)) := by decide +kernel

theorem checkedR30_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (88+i)) 0 (Lower80811.LedgerData.lookup 30 (88+i)) := by decide +kernel

theorem checkedR30_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (96+i)) 0 (Lower80811.LedgerData.lookup 30 (96+i)) := by decide +kernel

theorem checkedR30_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 30 (104+i)) 0 (Lower80811.LedgerData.lookup 30 (104+i)) := by decide +kernel

theorem checkedR30_part112 : ∀ i ∈ List.range 1, RunsValid (rowContext 30 (112+i)) 0 (Lower80811.LedgerData.lookup 30 (112+i)) := by decide +kernel

theorem checkedR30 (V : ℕ) (hV : V ∈ List.range 113) : RunsValid (rowContext 30 V) 0 (Lower80811.LedgerData.lookup 30 V) := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR30_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR30_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR30_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR30_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR30_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR30_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR30_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_113 : V < 88
    · by_cases h56_88 : V < 72
      · by_cases h56_72 : V < 64
        · have hi := checkedR30_part56 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
        · have hi := checkedR30_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
      · by_cases h72_88 : V < 80
        · have hi := checkedR30_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
        · have hi := checkedR30_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
    · by_cases h88_113 : V < 104
      · by_cases h88_104 : V < 96
        · have hi := checkedR30_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
        · have hi := checkedR30_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
      · by_cases h104_113 : V < 112
        · have hi := checkedR30_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi
        · have hi := checkedR30_part112 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem checkedR31_part0 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (0+i)) 0 (Lower80811.LedgerData.lookup 31 (0+i)) := by decide +kernel

theorem checkedR31_part8 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (8+i)) 0 (Lower80811.LedgerData.lookup 31 (8+i)) := by decide +kernel

theorem checkedR31_part16 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (16+i)) 0 (Lower80811.LedgerData.lookup 31 (16+i)) := by decide +kernel

theorem checkedR31_part24 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (24+i)) 0 (Lower80811.LedgerData.lookup 31 (24+i)) := by decide +kernel

theorem checkedR31_part32 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (32+i)) 0 (Lower80811.LedgerData.lookup 31 (32+i)) := by decide +kernel

theorem checkedR31_part40 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (40+i)) 0 (Lower80811.LedgerData.lookup 31 (40+i)) := by decide +kernel

theorem checkedR31_part48 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (48+i)) 0 (Lower80811.LedgerData.lookup 31 (48+i)) := by decide +kernel

theorem checkedR31_part56 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (56+i)) 0 (Lower80811.LedgerData.lookup 31 (56+i)) := by decide +kernel

theorem checkedR31_part64 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (64+i)) 0 (Lower80811.LedgerData.lookup 31 (64+i)) := by decide +kernel

theorem checkedR31_part72 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (72+i)) 0 (Lower80811.LedgerData.lookup 31 (72+i)) := by decide +kernel

theorem checkedR31_part80 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (80+i)) 0 (Lower80811.LedgerData.lookup 31 (80+i)) := by decide +kernel

theorem checkedR31_part88 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (88+i)) 0 (Lower80811.LedgerData.lookup 31 (88+i)) := by decide +kernel

theorem checkedR31_part96 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (96+i)) 0 (Lower80811.LedgerData.lookup 31 (96+i)) := by decide +kernel

theorem checkedR31_part104 : ∀ i ∈ List.range 8, RunsValid (rowContext 31 (104+i)) 0 (Lower80811.LedgerData.lookup 31 (104+i)) := by decide +kernel

theorem checkedR31 (V : ℕ) (hV : V ∈ List.range 112) : RunsValid (rowContext 31 V) 0 (Lower80811.LedgerData.lookup 31 V) := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 24
    · by_cases h0_24 : V < 8
      · have hi := checkedR31_part0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
      · by_cases h8_24 : V < 16
        · have hi := checkedR31_part8 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
        · have hi := checkedR31_part16 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
    · by_cases h24_56 : V < 40
      · by_cases h24_40 : V < 32
        · have hi := checkedR31_part24 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        · have hi := checkedR31_part32 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
      · by_cases h40_56 : V < 48
        · have hi := checkedR31_part40 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
        · have hi := checkedR31_part48 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
  · by_cases h56_112 : V < 80
    · by_cases h56_80 : V < 64
      · have hi := checkedR31_part56 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
      · by_cases h64_80 : V < 72
        · have hi := checkedR31_part64 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
        · have hi := checkedR31_part72 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
    · by_cases h80_112 : V < 96
      · by_cases h80_96 : V < 88
        · have hi := checkedR31_part80 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
        · have hi := checkedR31_part88 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
      · by_cases h96_112 : V < 104
        · have hi := checkedR31_part96 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
        · have hi := checkedR31_part104 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi


end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked

namespace ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
open Lower80811.LedgerData Lower80811.LedgerAudit Lower80811.PhaseData
open ProximityPrize.SubmissionLower.Lower80811.Assembly
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem checked (r v z : ℕ) (hr : 1 ≤ r) (hr30 : r ≤ 31)
    (hy : r+v ≤ 142) (ht : r+v+z ≤ 7501) :
    ledger (rowContext r v) z ≤ bound := by
  have hv : v ∈ List.range (143-r) := List.mem_range.mpr (by omega)
  have hc : RunsValid (rowContext r v) 0 (lookup r v) := by
    interval_cases r <;> first
      | exact checkedR1 v hv
      | exact checkedR2 v hv
      | exact checkedR3 v hv
      | exact checkedR4 v hv
      | exact checkedR5 v hv
      | exact checkedR6 v hv
      | exact checkedR7 v hv
      | exact checkedR8 v hv
      | exact checkedR9 v hv
      | exact checkedR10 v hv
      | exact checkedR11 v hv
      | exact checkedR12 v hv
      | exact checkedR13 v hv
      | exact checkedR14 v hv
      | exact checkedR15 v hv
      | exact checkedR16 v hv
      | exact checkedR17 v hv
      | exact checkedR18 v hv
      | exact checkedR19 v hv
      | exact checkedR20 v hv
      | exact checkedR21 v hv
      | exact checkedR22 v hv
      | exact checkedR23 v hv
      | exact checkedR24 v hv
      | exact checkedR25 v hv
      | exact checkedR26 v hv
      | exact checkedR27 v hv
      | exact checkedR28 v hv
      | exact checkedR29 v hv
      | exact checkedR30 v hv
      | exact checkedR31 v hv
  exact RunsValid.sound _ _ 0 z hc (Nat.zero_le _) (by dsimp [rowContext]; omega)

theorem ledgerReceipt : Assembly.LedgerReceiptSound 274976539400589696 := by
  constructor
  · decide +kernel
  · intro r v z hr hr30 hy ht
    have h := checked r v z hr hr30 hy ht
    simpa only [Assembly.LedgerReceiptSound, Assembly.combined, LedgerAudit.ledger, LedgerAudit.bound,
      PhaseSemantics.phaseCap, PhaseData.rowContext, middle, total, rawFlag,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
end ProximityPrize.SubmissionLower.Lower80811.LedgerChecked
