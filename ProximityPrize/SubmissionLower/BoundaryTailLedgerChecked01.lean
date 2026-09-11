import ProximityPrize.SubmissionLower.BoundaryTailLedgerData

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r1part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (0+k)) 0 (lookup 1 (0+k)) := by decide +kernel
theorem r1part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (8+k)) 0 (lookup 1 (8+k)) := by decide +kernel
theorem r1part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (16+k)) 0 (lookup 1 (16+k)) := by decide +kernel
theorem r1part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (24+k)) 0 (lookup 1 (24+k)) := by decide +kernel
theorem r1part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (32+k)) 0 (lookup 1 (32+k)) := by decide +kernel
theorem r1part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (40+k)) 0 (lookup 1 (40+k)) := by decide +kernel
theorem r1part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (48+k)) 0 (lookup 1 (48+k)) := by decide +kernel
theorem r1part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (56+k)) 0 (lookup 1 (56+k)) := by decide +kernel
theorem r1part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (64+k)) 0 (lookup 1 (64+k)) := by decide +kernel
theorem r1part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (72+k)) 0 (lookup 1 (72+k)) := by decide +kernel
theorem r1part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (80+k)) 0 (lookup 1 (80+k)) := by decide +kernel
theorem r1part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (88+k)) 0 (lookup 1 (88+k)) := by decide +kernel
theorem r1part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (96+k)) 0 (lookup 1 (96+k)) := by decide +kernel
theorem r1part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (104+k)) 0 (lookup 1 (104+k)) := by decide +kernel
theorem r1part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (112+k)) 0 (lookup 1 (112+k)) := by decide +kernel
theorem r1part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (120+k)) 0 (lookup 1 (120+k)) := by decide +kernel
theorem r1part128 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (128+k)) 0 (lookup 1 (128+k)) := by decide +kernel
theorem r1part136 : ∀ k ∈ List.range 3, RunsValid (rowContext 1 (136+k)) 0 (lookup 1 (136+k)) := by decide +kernel

theorem checkedR1 (V : ℕ) (hV : V ∈ List.range 139) : RunsValid (rowContext 1 V) 0 (lookup 1 V) := by
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 136
  · have hp := r1part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r1part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r2part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (0+k)) 0 (lookup 2 (0+k)) := by decide +kernel
theorem r2part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (8+k)) 0 (lookup 2 (8+k)) := by decide +kernel
theorem r2part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (16+k)) 0 (lookup 2 (16+k)) := by decide +kernel
theorem r2part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (24+k)) 0 (lookup 2 (24+k)) := by decide +kernel
theorem r2part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (32+k)) 0 (lookup 2 (32+k)) := by decide +kernel
theorem r2part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (40+k)) 0 (lookup 2 (40+k)) := by decide +kernel
theorem r2part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (48+k)) 0 (lookup 2 (48+k)) := by decide +kernel
theorem r2part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (56+k)) 0 (lookup 2 (56+k)) := by decide +kernel
theorem r2part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (64+k)) 0 (lookup 2 (64+k)) := by decide +kernel
theorem r2part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (72+k)) 0 (lookup 2 (72+k)) := by decide +kernel
theorem r2part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (80+k)) 0 (lookup 2 (80+k)) := by decide +kernel
theorem r2part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (88+k)) 0 (lookup 2 (88+k)) := by decide +kernel
theorem r2part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (96+k)) 0 (lookup 2 (96+k)) := by decide +kernel
theorem r2part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (104+k)) 0 (lookup 2 (104+k)) := by decide +kernel
theorem r2part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (112+k)) 0 (lookup 2 (112+k)) := by decide +kernel
theorem r2part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (120+k)) 0 (lookup 2 (120+k)) := by decide +kernel
theorem r2part128 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (128+k)) 0 (lookup 2 (128+k)) := by decide +kernel
theorem r2part136 : ∀ k ∈ List.range 2, RunsValid (rowContext 2 (136+k)) 0 (lookup 2 (136+k)) := by decide +kernel

theorem checkedR2 (V : ℕ) (hV : V ∈ List.range 138) : RunsValid (rowContext 2 V) 0 (lookup 2 V) := by
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 136
  · have hp := r2part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r2part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r3part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (0+k)) 0 (lookup 3 (0+k)) := by decide +kernel
theorem r3part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (8+k)) 0 (lookup 3 (8+k)) := by decide +kernel
theorem r3part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (16+k)) 0 (lookup 3 (16+k)) := by decide +kernel
theorem r3part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (24+k)) 0 (lookup 3 (24+k)) := by decide +kernel
theorem r3part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (32+k)) 0 (lookup 3 (32+k)) := by decide +kernel
theorem r3part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (40+k)) 0 (lookup 3 (40+k)) := by decide +kernel
theorem r3part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (48+k)) 0 (lookup 3 (48+k)) := by decide +kernel
theorem r3part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (56+k)) 0 (lookup 3 (56+k)) := by decide +kernel
theorem r3part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (64+k)) 0 (lookup 3 (64+k)) := by decide +kernel
theorem r3part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (72+k)) 0 (lookup 3 (72+k)) := by decide +kernel
theorem r3part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (80+k)) 0 (lookup 3 (80+k)) := by decide +kernel
theorem r3part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (88+k)) 0 (lookup 3 (88+k)) := by decide +kernel
theorem r3part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (96+k)) 0 (lookup 3 (96+k)) := by decide +kernel
theorem r3part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (104+k)) 0 (lookup 3 (104+k)) := by decide +kernel
theorem r3part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (112+k)) 0 (lookup 3 (112+k)) := by decide +kernel
theorem r3part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (120+k)) 0 (lookup 3 (120+k)) := by decide +kernel
theorem r3part128 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (128+k)) 0 (lookup 3 (128+k)) := by decide +kernel
theorem r3part136 : ∀ k ∈ List.range 1, RunsValid (rowContext 3 (136+k)) 0 (lookup 3 (136+k)) := by decide +kernel

theorem checkedR3 (V : ℕ) (hV : V ∈ List.range 137) : RunsValid (rowContext 3 V) 0 (lookup 3 V) := by
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 136
  · have hp := r3part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r3part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r4part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (0+k)) 0 (lookup 4 (0+k)) := by decide +kernel
theorem r4part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (8+k)) 0 (lookup 4 (8+k)) := by decide +kernel
theorem r4part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (16+k)) 0 (lookup 4 (16+k)) := by decide +kernel
theorem r4part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (24+k)) 0 (lookup 4 (24+k)) := by decide +kernel
theorem r4part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (32+k)) 0 (lookup 4 (32+k)) := by decide +kernel
theorem r4part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (40+k)) 0 (lookup 4 (40+k)) := by decide +kernel
theorem r4part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (48+k)) 0 (lookup 4 (48+k)) := by decide +kernel
theorem r4part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (56+k)) 0 (lookup 4 (56+k)) := by decide +kernel
theorem r4part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (64+k)) 0 (lookup 4 (64+k)) := by decide +kernel
theorem r4part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (72+k)) 0 (lookup 4 (72+k)) := by decide +kernel
theorem r4part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (80+k)) 0 (lookup 4 (80+k)) := by decide +kernel
theorem r4part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (88+k)) 0 (lookup 4 (88+k)) := by decide +kernel
theorem r4part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (96+k)) 0 (lookup 4 (96+k)) := by decide +kernel
theorem r4part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (104+k)) 0 (lookup 4 (104+k)) := by decide +kernel
theorem r4part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (112+k)) 0 (lookup 4 (112+k)) := by decide +kernel
theorem r4part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (120+k)) 0 (lookup 4 (120+k)) := by decide +kernel
theorem r4part128 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (128+k)) 0 (lookup 4 (128+k)) := by decide +kernel

theorem checkedR4 (V : ℕ) (hV : V ∈ List.range 136) : RunsValid (rowContext 4 V) 0 (lookup 4 V) := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r4part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r5part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (0+k)) 0 (lookup 5 (0+k)) := by decide +kernel
theorem r5part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (8+k)) 0 (lookup 5 (8+k)) := by decide +kernel
theorem r5part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (16+k)) 0 (lookup 5 (16+k)) := by decide +kernel
theorem r5part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (24+k)) 0 (lookup 5 (24+k)) := by decide +kernel
theorem r5part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (32+k)) 0 (lookup 5 (32+k)) := by decide +kernel
theorem r5part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (40+k)) 0 (lookup 5 (40+k)) := by decide +kernel
theorem r5part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (48+k)) 0 (lookup 5 (48+k)) := by decide +kernel
theorem r5part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (56+k)) 0 (lookup 5 (56+k)) := by decide +kernel
theorem r5part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (64+k)) 0 (lookup 5 (64+k)) := by decide +kernel
theorem r5part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (72+k)) 0 (lookup 5 (72+k)) := by decide +kernel
theorem r5part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (80+k)) 0 (lookup 5 (80+k)) := by decide +kernel
theorem r5part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (88+k)) 0 (lookup 5 (88+k)) := by decide +kernel
theorem r5part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (96+k)) 0 (lookup 5 (96+k)) := by decide +kernel
theorem r5part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (104+k)) 0 (lookup 5 (104+k)) := by decide +kernel
theorem r5part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (112+k)) 0 (lookup 5 (112+k)) := by decide +kernel
theorem r5part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (120+k)) 0 (lookup 5 (120+k)) := by decide +kernel
theorem r5part128 : ∀ k ∈ List.range 7, RunsValid (rowContext 5 (128+k)) 0 (lookup 5 (128+k)) := by decide +kernel

theorem checkedR5 (V : ℕ) (hV : V ∈ List.range 135) : RunsValid (rowContext 5 V) 0 (lookup 5 V) := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r5part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
