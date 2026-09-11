import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked04

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r21part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (0+k)) 0 (lookup 21 (0+k)) := by decide +kernel
theorem r21part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (8+k)) 0 (lookup 21 (8+k)) := by decide +kernel
theorem r21part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (16+k)) 0 (lookup 21 (16+k)) := by decide +kernel
theorem r21part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (24+k)) 0 (lookup 21 (24+k)) := by decide +kernel
theorem r21part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (32+k)) 0 (lookup 21 (32+k)) := by decide +kernel
theorem r21part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (40+k)) 0 (lookup 21 (40+k)) := by decide +kernel
theorem r21part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (48+k)) 0 (lookup 21 (48+k)) := by decide +kernel
theorem r21part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (56+k)) 0 (lookup 21 (56+k)) := by decide +kernel
theorem r21part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (64+k)) 0 (lookup 21 (64+k)) := by decide +kernel
theorem r21part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (72+k)) 0 (lookup 21 (72+k)) := by decide +kernel
theorem r21part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (80+k)) 0 (lookup 21 (80+k)) := by decide +kernel
theorem r21part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (88+k)) 0 (lookup 21 (88+k)) := by decide +kernel
theorem r21part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (96+k)) 0 (lookup 21 (96+k)) := by decide +kernel
theorem r21part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (104+k)) 0 (lookup 21 (104+k)) := by decide +kernel
theorem r21part112 : ∀ k ∈ List.range 7, RunsValid (rowContext 21 (112+k)) 0 (lookup 21 (112+k)) := by decide +kernel

theorem checkedR21 (V : ℕ) (hV : V ∈ List.range 119) : RunsValid (rowContext 21 V) 0 (lookup 21 V) := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r21part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r22part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (0+k)) 0 (lookup 22 (0+k)) := by decide +kernel
theorem r22part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (8+k)) 0 (lookup 22 (8+k)) := by decide +kernel
theorem r22part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (16+k)) 0 (lookup 22 (16+k)) := by decide +kernel
theorem r22part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (24+k)) 0 (lookup 22 (24+k)) := by decide +kernel
theorem r22part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (32+k)) 0 (lookup 22 (32+k)) := by decide +kernel
theorem r22part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (40+k)) 0 (lookup 22 (40+k)) := by decide +kernel
theorem r22part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (48+k)) 0 (lookup 22 (48+k)) := by decide +kernel
theorem r22part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (56+k)) 0 (lookup 22 (56+k)) := by decide +kernel
theorem r22part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (64+k)) 0 (lookup 22 (64+k)) := by decide +kernel
theorem r22part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (72+k)) 0 (lookup 22 (72+k)) := by decide +kernel
theorem r22part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (80+k)) 0 (lookup 22 (80+k)) := by decide +kernel
theorem r22part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (88+k)) 0 (lookup 22 (88+k)) := by decide +kernel
theorem r22part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (96+k)) 0 (lookup 22 (96+k)) := by decide +kernel
theorem r22part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (104+k)) 0 (lookup 22 (104+k)) := by decide +kernel
theorem r22part112 : ∀ k ∈ List.range 6, RunsValid (rowContext 22 (112+k)) 0 (lookup 22 (112+k)) := by decide +kernel

theorem checkedR22 (V : ℕ) (hV : V ∈ List.range 118) : RunsValid (rowContext 22 V) 0 (lookup 22 V) := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r22part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r23part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (0+k)) 0 (lookup 23 (0+k)) := by decide +kernel
theorem r23part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (8+k)) 0 (lookup 23 (8+k)) := by decide +kernel
theorem r23part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (16+k)) 0 (lookup 23 (16+k)) := by decide +kernel
theorem r23part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (24+k)) 0 (lookup 23 (24+k)) := by decide +kernel
theorem r23part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (32+k)) 0 (lookup 23 (32+k)) := by decide +kernel
theorem r23part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (40+k)) 0 (lookup 23 (40+k)) := by decide +kernel
theorem r23part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (48+k)) 0 (lookup 23 (48+k)) := by decide +kernel
theorem r23part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (56+k)) 0 (lookup 23 (56+k)) := by decide +kernel
theorem r23part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (64+k)) 0 (lookup 23 (64+k)) := by decide +kernel
theorem r23part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (72+k)) 0 (lookup 23 (72+k)) := by decide +kernel
theorem r23part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (80+k)) 0 (lookup 23 (80+k)) := by decide +kernel
theorem r23part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (88+k)) 0 (lookup 23 (88+k)) := by decide +kernel
theorem r23part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (96+k)) 0 (lookup 23 (96+k)) := by decide +kernel
theorem r23part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (104+k)) 0 (lookup 23 (104+k)) := by decide +kernel
theorem r23part112 : ∀ k ∈ List.range 5, RunsValid (rowContext 23 (112+k)) 0 (lookup 23 (112+k)) := by decide +kernel

theorem checkedR23 (V : ℕ) (hV : V ∈ List.range 117) : RunsValid (rowContext 23 V) 0 (lookup 23 V) := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r24part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (0+k)) 0 (lookup 24 (0+k)) := by decide +kernel
theorem r24part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (8+k)) 0 (lookup 24 (8+k)) := by decide +kernel
theorem r24part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (16+k)) 0 (lookup 24 (16+k)) := by decide +kernel
theorem r24part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (24+k)) 0 (lookup 24 (24+k)) := by decide +kernel
theorem r24part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (32+k)) 0 (lookup 24 (32+k)) := by decide +kernel
theorem r24part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (40+k)) 0 (lookup 24 (40+k)) := by decide +kernel
theorem r24part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (48+k)) 0 (lookup 24 (48+k)) := by decide +kernel
theorem r24part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (56+k)) 0 (lookup 24 (56+k)) := by decide +kernel
theorem r24part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (64+k)) 0 (lookup 24 (64+k)) := by decide +kernel
theorem r24part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (72+k)) 0 (lookup 24 (72+k)) := by decide +kernel
theorem r24part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (80+k)) 0 (lookup 24 (80+k)) := by decide +kernel
theorem r24part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (88+k)) 0 (lookup 24 (88+k)) := by decide +kernel
theorem r24part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (96+k)) 0 (lookup 24 (96+k)) := by decide +kernel
theorem r24part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (104+k)) 0 (lookup 24 (104+k)) := by decide +kernel
theorem r24part112 : ∀ k ∈ List.range 4, RunsValid (rowContext 24 (112+k)) 0 (lookup 24 (112+k)) := by decide +kernel

theorem checkedR24 (V : ℕ) (hV : V ∈ List.range 116) : RunsValid (rowContext 24 V) 0 (lookup 24 V) := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r25part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (0+k)) 0 (lookup 25 (0+k)) := by decide +kernel
theorem r25part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (8+k)) 0 (lookup 25 (8+k)) := by decide +kernel
theorem r25part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (16+k)) 0 (lookup 25 (16+k)) := by decide +kernel
theorem r25part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (24+k)) 0 (lookup 25 (24+k)) := by decide +kernel
theorem r25part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (32+k)) 0 (lookup 25 (32+k)) := by decide +kernel
theorem r25part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (40+k)) 0 (lookup 25 (40+k)) := by decide +kernel
theorem r25part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (48+k)) 0 (lookup 25 (48+k)) := by decide +kernel
theorem r25part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (56+k)) 0 (lookup 25 (56+k)) := by decide +kernel
theorem r25part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (64+k)) 0 (lookup 25 (64+k)) := by decide +kernel
theorem r25part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (72+k)) 0 (lookup 25 (72+k)) := by decide +kernel
theorem r25part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (80+k)) 0 (lookup 25 (80+k)) := by decide +kernel
theorem r25part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (88+k)) 0 (lookup 25 (88+k)) := by decide +kernel
theorem r25part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (96+k)) 0 (lookup 25 (96+k)) := by decide +kernel
theorem r25part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (104+k)) 0 (lookup 25 (104+k)) := by decide +kernel
theorem r25part112 : ∀ k ∈ List.range 3, RunsValid (rowContext 25 (112+k)) 0 (lookup 25 (112+k)) := by decide +kernel

theorem checkedR25 (V : ℕ) (hV : V ∈ List.range 115) : RunsValid (rowContext 25 V) 0 (lookup 25 V) := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r25part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r25part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
