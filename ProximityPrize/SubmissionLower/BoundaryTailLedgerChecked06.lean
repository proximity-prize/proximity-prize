import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked05

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r26part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (0+k)) 0 (lookup 26 (0+k)) := by decide +kernel
theorem r26part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (8+k)) 0 (lookup 26 (8+k)) := by decide +kernel
theorem r26part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (16+k)) 0 (lookup 26 (16+k)) := by decide +kernel
theorem r26part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (24+k)) 0 (lookup 26 (24+k)) := by decide +kernel
theorem r26part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (32+k)) 0 (lookup 26 (32+k)) := by decide +kernel
theorem r26part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (40+k)) 0 (lookup 26 (40+k)) := by decide +kernel
theorem r26part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (48+k)) 0 (lookup 26 (48+k)) := by decide +kernel
theorem r26part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (56+k)) 0 (lookup 26 (56+k)) := by decide +kernel
theorem r26part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (64+k)) 0 (lookup 26 (64+k)) := by decide +kernel
theorem r26part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (72+k)) 0 (lookup 26 (72+k)) := by decide +kernel
theorem r26part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (80+k)) 0 (lookup 26 (80+k)) := by decide +kernel
theorem r26part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (88+k)) 0 (lookup 26 (88+k)) := by decide +kernel
theorem r26part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (96+k)) 0 (lookup 26 (96+k)) := by decide +kernel
theorem r26part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (104+k)) 0 (lookup 26 (104+k)) := by decide +kernel
theorem r26part112 : ∀ k ∈ List.range 2, RunsValid (rowContext 26 (112+k)) 0 (lookup 26 (112+k)) := by decide +kernel

theorem checkedR26 (V : ℕ) (hV : V ∈ List.range 114) : RunsValid (rowContext 26 V) 0 (lookup 26 V) := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r26part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r26part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r27part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (0+k)) 0 (lookup 27 (0+k)) := by decide +kernel
theorem r27part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (8+k)) 0 (lookup 27 (8+k)) := by decide +kernel
theorem r27part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (16+k)) 0 (lookup 27 (16+k)) := by decide +kernel
theorem r27part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (24+k)) 0 (lookup 27 (24+k)) := by decide +kernel
theorem r27part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (32+k)) 0 (lookup 27 (32+k)) := by decide +kernel
theorem r27part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (40+k)) 0 (lookup 27 (40+k)) := by decide +kernel
theorem r27part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (48+k)) 0 (lookup 27 (48+k)) := by decide +kernel
theorem r27part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (56+k)) 0 (lookup 27 (56+k)) := by decide +kernel
theorem r27part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (64+k)) 0 (lookup 27 (64+k)) := by decide +kernel
theorem r27part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (72+k)) 0 (lookup 27 (72+k)) := by decide +kernel
theorem r27part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (80+k)) 0 (lookup 27 (80+k)) := by decide +kernel
theorem r27part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (88+k)) 0 (lookup 27 (88+k)) := by decide +kernel
theorem r27part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (96+k)) 0 (lookup 27 (96+k)) := by decide +kernel
theorem r27part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (104+k)) 0 (lookup 27 (104+k)) := by decide +kernel
theorem r27part112 : ∀ k ∈ List.range 1, RunsValid (rowContext 27 (112+k)) 0 (lookup 27 (112+k)) := by decide +kernel

theorem checkedR27 (V : ℕ) (hV : V ∈ List.range 113) : RunsValid (rowContext 27 V) 0 (lookup 27 V) := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r27part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r27part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r28part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (0+k)) 0 (lookup 28 (0+k)) := by decide +kernel
theorem r28part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (8+k)) 0 (lookup 28 (8+k)) := by decide +kernel
theorem r28part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (16+k)) 0 (lookup 28 (16+k)) := by decide +kernel
theorem r28part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (24+k)) 0 (lookup 28 (24+k)) := by decide +kernel
theorem r28part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (32+k)) 0 (lookup 28 (32+k)) := by decide +kernel
theorem r28part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (40+k)) 0 (lookup 28 (40+k)) := by decide +kernel
theorem r28part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (48+k)) 0 (lookup 28 (48+k)) := by decide +kernel
theorem r28part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (56+k)) 0 (lookup 28 (56+k)) := by decide +kernel
theorem r28part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (64+k)) 0 (lookup 28 (64+k)) := by decide +kernel
theorem r28part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (72+k)) 0 (lookup 28 (72+k)) := by decide +kernel
theorem r28part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (80+k)) 0 (lookup 28 (80+k)) := by decide +kernel
theorem r28part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (88+k)) 0 (lookup 28 (88+k)) := by decide +kernel
theorem r28part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (96+k)) 0 (lookup 28 (96+k)) := by decide +kernel
theorem r28part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (104+k)) 0 (lookup 28 (104+k)) := by decide +kernel

theorem checkedR28 (V : ℕ) (hV : V ∈ List.range 112) : RunsValid (rowContext 28 V) 0 (lookup 28 V) := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r28part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem r29part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (0+k)) 0 (lookup 29 (0+k)) := by decide +kernel
theorem r29part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (8+k)) 0 (lookup 29 (8+k)) := by decide +kernel
theorem r29part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (16+k)) 0 (lookup 29 (16+k)) := by decide +kernel
theorem r29part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (24+k)) 0 (lookup 29 (24+k)) := by decide +kernel
theorem r29part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (32+k)) 0 (lookup 29 (32+k)) := by decide +kernel
theorem r29part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (40+k)) 0 (lookup 29 (40+k)) := by decide +kernel
theorem r29part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (48+k)) 0 (lookup 29 (48+k)) := by decide +kernel
theorem r29part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (56+k)) 0 (lookup 29 (56+k)) := by decide +kernel
theorem r29part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (64+k)) 0 (lookup 29 (64+k)) := by decide +kernel
theorem r29part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (72+k)) 0 (lookup 29 (72+k)) := by decide +kernel
theorem r29part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (80+k)) 0 (lookup 29 (80+k)) := by decide +kernel
theorem r29part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (88+k)) 0 (lookup 29 (88+k)) := by decide +kernel
theorem r29part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (96+k)) 0 (lookup 29 (96+k)) := by decide +kernel
theorem r29part104 : ∀ k ∈ List.range 7, RunsValid (rowContext 29 (104+k)) 0 (lookup 29 (104+k)) := by decide +kernel

theorem checkedR29 (V : ℕ) (hV : V ∈ List.range 111) : RunsValid (rowContext 29 V) 0 (lookup 29 V) := by
  have hv : V < 111 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r29part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem r30part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (0+k)) 0 (lookup 30 (0+k)) := by decide +kernel
theorem r30part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (8+k)) 0 (lookup 30 (8+k)) := by decide +kernel
theorem r30part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (16+k)) 0 (lookup 30 (16+k)) := by decide +kernel
theorem r30part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (24+k)) 0 (lookup 30 (24+k)) := by decide +kernel
theorem r30part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (32+k)) 0 (lookup 30 (32+k)) := by decide +kernel
theorem r30part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (40+k)) 0 (lookup 30 (40+k)) := by decide +kernel
theorem r30part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (48+k)) 0 (lookup 30 (48+k)) := by decide +kernel
theorem r30part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (56+k)) 0 (lookup 30 (56+k)) := by decide +kernel
theorem r30part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (64+k)) 0 (lookup 30 (64+k)) := by decide +kernel
theorem r30part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (72+k)) 0 (lookup 30 (72+k)) := by decide +kernel
theorem r30part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (80+k)) 0 (lookup 30 (80+k)) := by decide +kernel
theorem r30part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (88+k)) 0 (lookup 30 (88+k)) := by decide +kernel
theorem r30part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (96+k)) 0 (lookup 30 (96+k)) := by decide +kernel
theorem r30part104 : ∀ k ∈ List.range 6, RunsValid (rowContext 30 (104+k)) 0 (lookup 30 (104+k)) := by decide +kernel

theorem checkedR30 (V : ℕ) (hV : V ∈ List.range 110) : RunsValid (rowContext 30 V) 0 (lookup 30 V) := by
  have hv : V < 110 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r30part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
