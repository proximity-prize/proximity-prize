import ProximityPrize.SubmissionLower.Lower6805Fast7

/- Packed from the boundary-tail candidate in PR #535 by @0xLucqs. -/
set_option Elab.async false

section P679
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

end P679

section P680
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

end P680

section P681
namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
open ProximityPrize.SubmissionLower.Lower80801.Assembly
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem checked (r v z : ℕ) (hr : 1 ≤ r) (hr30 : r ≤ 30)
    (hy : r+v ≤ 139) (ht : r+v+z ≤ 7199) :
    ledger (rowContext r v) z ≤ bound := by
  have hv : v ∈ List.range (140-r) := List.mem_range.mpr (by omega)
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
  exact RunsValid.sound _ _ 0 z hc (Nat.zero_le _) (by dsimp [rowContext]; omega)

theorem ledgerReceipt : Assembly.LedgerReceiptSound 253080253061200723 := by
  constructor
  · decide +kernel
  · intro r v z hr hr30 hy ht
    have h := checked r v z hr hr30 hy ht
    simpa only [Assembly.LedgerReceiptSound, Assembly.combined, LedgerAudit.ledger, LedgerAudit.bound,
      PhaseSemantics.phaseCap, PhaseData.rowContext, middle, total, rawFlag,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked

end P681

section P682
section Compact_Scalar6805
/-! A seedless interpolation kernel for error cell 80801, the first cell
capable of supporting a 68.05 score. This is one ingredient only; it does
not establish the MCA bound or a ProtocolClaim. -/
namespace ProximityPrize.SubmissionLower.Scalar6805
open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact : coefficientCount 18315643 131071 139 30 = 32027390685 := by decide +kernel

theorem localRankBound_exact : localRankBound 101 139 30 = 122171 := by decide +kernel

theorem nullity_exact :
    coefficientCount 18315643 131071 139 30 -
      262144 * localRankBound 101 139 30 = 996061 := by
  norm_num only [coefficientCount_exact, localRankBound_exact]

theorem interpolation_gate :
    262144 * localRankBound 101 139 30 < coefficientCount 18315643 131071 139 30 := by
  norm_num only [coefficientCount_exact, localRankBound_exact]

theorem exists_frozen_seedless_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       18315643 131071 139 30∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       RCN119.slopeDifference IRSProfile.Field^(101-r)∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field 18315643 131071 139 30 101
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=262144 by
       norm_num [IRSProfile.Index]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field 18315643 131071 139 30 theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   18315643 131071 139 30 101 IRSProfile.domain received
   theta hzero i r
 rw [←translation_reconstruct_coeff IRSProfile.Field 18315643 131071
   139 30 (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv

end ProximityPrize.SubmissionLower.Scalar6805

end Compact_Scalar6805

section Compact_ScalarList6805
/-! Scalar list arm for error cell 80801. The counting argument is adapted
from the promoted 68.03 submission's LocatorScalar module; only its numerical
profile changes here. This module alone is not a ProtocolClaim. -/
namespace ProximityPrize.SubmissionLower.ScalarList6805Arithmetic
open ProximityPrize.Benchmark
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80801
def agreements : ℕ := n-errors
def gap : ℕ := agreements-w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 101
def yTotalCap : ℕ := 139
def slopeCap : ℕ := 30
def weightedCap : ℕ := multiplicity*agreements
def listBudget : ℕ := 5652701949
def capY : ℕ := 1+2*w*yTotalCap
def capR : ℕ := w*(2*slopeCap-1)
def regularListNumerator : ℕ := (n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap : ℕ := (2*slopeCap-1)*yTotalCap
def listNumerator : ℕ := regularListNumerator+singularListCap*gap

theorem list_numerator_fits : listNumerator < listBudget*gap := by decide

theorem exists_seedless_interpolant (received : IRSProfile.Index → IRSProfile.Field) :
   ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ RCN279.globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i : IRSProfile.Index) (r : ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r :=
  Scalar6805.exists_frozen_seedless_interpolant received
end
end ProximityPrize.SubmissionLower.ScalarList6805Arithmetic

namespace ProximityPrize.SubmissionLower.ScalarList6805
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001 RCN281 RCN019 RCN018
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
private abbrev n:=ScalarList6805Arithmetic.n
private abbrev w:=ScalarList6805Arithmetic.w
private abbrev errors:=ScalarList6805Arithmetic.errors
private abbrev agreements:=ScalarList6805Arithmetic.agreements
private abbrev gap:=ScalarList6805Arithmetic.gap
private abbrev prime:=ScalarList6805Arithmetic.prime
private abbrev multiplicity:=ScalarList6805Arithmetic.multiplicity
private abbrev yTotalCap:=ScalarList6805Arithmetic.yTotalCap
private abbrev slopeCap:=ScalarList6805Arithmetic.slopeCap
private abbrev weightedCap:=ScalarList6805Arithmetic.weightedCap
private abbrev listBudget:=ScalarList6805Arithmetic.listBudget
private abbrev capY:=ScalarList6805Arithmetic.capY
private abbrev capR:=ScalarList6805Arithmetic.capR
private abbrev regularListNumerator :=
 ScalarList6805Arithmetic.regularListNumerator
private abbrev singularListCap:=ScalarList6805Arithmetic.singularListCap
private abbrev listNumerator:=ScalarList6805Arithmetic.listNumerator
private theorem list_numerator_fits:listNumerator < listBudget * gap :=
 ScalarList6805Arithmetic.list_numerator_fits
private theorem w_pos:0 < w:=by decide
private theorem prime_pos:0 < prime:=by decide
private theorem w_lt_prime:w < prime:=by decide
private theorem w_lt_agreements:w < agreements:=by decide
private theorem agreements_le_n:agreements ≤ n:=by decide
private theorem yTotalCap_lt_prime:yTotalCap < prime:=by decide
private theorem slopeCap_lt_prime:slopeCap < prime:=by decide
private theorem slopeCap_pos:0 < slopeCap:=by decide
private theorem weightedCap_pos:0 < weightedCap:=by decide
private theorem gap_pos:0 < gap:=by decide
private theorem base_dimension_exact:IRSProfile.baseDimension = w + 1:=by
 norm_num [IRSProfile.baseDimension, w, ScalarList6805Arithmetic.w]
private theorem index_card_exact:Fintype.card IRSProfile.Index = n:=by
 norm_num [IRSProfile.Index, n, ScalarList6805Arithmetic.n]
section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
private def agreementCap:Fin 3 → ℕ:=![capY, capR, 1]
private theorem seedless_degree_caps
   (Q:MvPolynomial (Fin 4) K)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap) :
   Q.degreeOf 1 ≤ yTotalCap ∧ Q.degreeOf 2 ≤ slopeCap ∧
     Q.degreeOf 3 = 0:=by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_, ?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
private theorem agreement_cap
   (phi:Polynomial K →+* GenericField K)
   (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 = 0) (x u:K) :
   ∀ j, (agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j:=by
 have hb:=agreementNumerator_degree_bounds F yTotalCap slopeCap 0
   slopeCap_pos hY hR hZ.le w
     (fun j => (j.factorial:K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (surfaceMap_degreeOf_le phi _ 0).trans
     (by simpa [agreementCap, capY, ScalarList6805Arithmetic.capY]
       using hb.1)
 · exact (surfaceMap_degreeOf_le phi _ 1).trans
     (by simpa [agreementCap, capR, ScalarList6805Arithmetic.capR]
       using hb.2.1)
 · exact (surfaceMap_degreeOf_le phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
private theorem original_regular_seedless_bound
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf 2)
   (hbox:F ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 = 0)
   (Gamma:Finset (Polynomial K))
   (hdegree:∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions:∀ S ∈ Gamma, specialization K S 0 F = 0)
   (hregular:∀ S ∈ Gamma,
     specialization K S 0 (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card = n)
   (hagreement:∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card * gap ≤
     (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1):=by
 classical
 letI:CharP (GenericField K) prime:=genericField_charP K prime
 have hsmall:F.degreeOf 2 < prime:=hR.trans_lt slopeCap_lt_prime
 have hcount (g:RCN281.GeometricFactor K F) :
     (RCN281.geometricPolynomials K F Gamma g).card * gap ≤
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0):=by
   obtain ⟨hgirred, hgdiv⟩ :=
     surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate:=geometric_factor_regular_gate K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hproper:=RCN281.geometric_seedless_cut_proper
     K g.1 hgate.1
   have hgY:=(geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
   have hgR:=(geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
   have hgZ:g.1.degreeOf 2 = 0:=Nat.eq_zero_of_le_zero
     ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree:∀ j:Fin 3, g.1.degreeOf j < prime:=by
     intro j
     fin_cases j
     · exact hgY.trans_lt yTotalCap_lt_prime
     · exact hgR.trans_lt slopeCap_lt_prime
     · simpa [hgZ] using prime_pos
   have hcutDegree:∀ j k:Fin 3, j ≠ k →
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j *
           g.1.degreeOf k +
         g.1.degreeOf j *
           (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime:=by
     intro j k hjk
     have h0:=hGdegree 0
     have h1:=hGdegree 1
     have h2:=hGdegree 2
     fin_cases j <;> fin_cases k <;>
       simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub:=RCN281.geometricPolynomials_subset K F Gamma g
   have hraw:=seedless_proper_cut_bound (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
     (RCN281.geometricPolynomials K F Gamma g)
     nodes x received hinj prime w agreements
     w_pos w_lt_prime w_lt_agreements
     (by rw [hnodes]; exact agreements_le_n)
     hGdegree hcutDegree
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolutions S (hsub hS))
     (fun S hS => selectedPoint_regular_of_specialization K F
       (fun _:K => S) 0 (hregular S (hsub hS)))
     (fun S hS => (Finset.mem_filter.mp hS).2)
     (fun S hS => hagreement S (hsub hS)) agreementCap
     (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
       (x i) (received i))
   have hx0 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0 = 0:=by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3) ≠ 2)]
   have hx1 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1 = 0:=by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3) ≠ 2)]
   have hx2 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2 = 1:=by
     simp [seedlessCut]
   have hm0:coordinateMixedDegree (GenericField K) g.1 seedlessCut 0 =
       g.1.degreeOf 1:=by
     rw [RCN001.coordinateMixedDegree_zero, hx1, hx2]
     omega
   have hm1:coordinateMixedDegree (GenericField K) g.1 seedlessCut 1 =
       g.1.degreeOf 0:=by
     rw [RCN001.coordinateMixedDegree_one, hx0, hx2]
     omega
   have hm2:coordinateMixedDegree (GenericField K) g.1 seedlessCut 2 = 0:=by
     rw [RCN001.coordinateMixedDegree_two, hx0, hx1]
     omega
   have hcost :
       (∑ i:Fin 3, agreementCap i *
         coordinateMixedDegree (GenericField K) g.1 seedlessCut i) =
       capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0:=by
     simp [Fin.sum_univ_succ, agreementCap, hm0, hm1, hm2]
   rw [hnodes, hcost] at hraw
   change (RCN281.geometricPolynomials K F Gamma g).card *
       (agreements - w) ≤
     (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card * gap ≤
       (∑ g:RCN281.GeometricFactor K F,
         (RCN281.geometricPolynomials K F Gamma g).card) * gap :=
     Nat.mul_le_mul_right _
       (RCN281.card_le_sum_geometricPolynomials
         K F hF.ne_zero Gamma hsolutions)
   _ = ∑ g:RCN281.GeometricFactor K F,
       (RCN281.geometricPolynomials K F Gamma g).card * gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:RCN281.GeometricFactor K F,
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0) :=
     Finset.sum_le_sum (fun g _ => hcount g)
   _ = (n - w) *
       (capY * (∑ g:RCN281.GeometricFactor K F,
         g.1.degreeOf 1) +
       capR * (∑ g:RCN281.GeometricFactor K F,
         g.1.degreeOf 0)):=by
     rw [← Finset.mul_sum, Finset.sum_add_distrib,
       ← Finset.mul_sum, ← Finset.mul_sum]
   _ ≤ (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1):=by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
private theorem singular_seedless_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S ∈ Gamma,
     specialization K S 0 (singularAuxiliary Q) = 0) :
   Gamma.card ≤ singularListCap:=by
 classical
 let phi:=polynomialEmbedding K
 let J:=singularAuxiliary Q
 have hcaps:=seedless_degree_caps K Q hbox
 have hJne:J ≠ 0:=singularAuxiliary_nonzero Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hJR:J.degreeOf 2 = 0:=singularAuxiliary_R_degree Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hQY:MvPolynomial.weightedTotalDegree
     RCN281.yWeights Q ≤ yTotalCap:=by
   apply (weightedTotalDegree_le_iff
     RCN281.yWeights Q yTotalCap).mpr
   intro d hd
   have hh:=(hbox hd).1
   rw [weight_fin4]
   simpa [RCN281.yWeights] using
     (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ:MvPolynomial.weightedTotalDegree
     RCN281.zWeights Q ≤ 0:=by
   apply (weightedTotalDegree_le_iff
     RCN281.zWeights Q 0).mpr
   intro d hd
   have hh:=(hbox hd).2.2.1
   rw [weight_fin4]
   simpa [RCN281.zWeights, hh]
 have hJYw:=singularAuxiliary_weight_le
   RCN281.yWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJZw:=singularAuxiliary_weight_le
   RCN281.zWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJY:J.degreeOf 1 ≤ singularListCap :=
   (RCN281.degreeY_le_yWeight K J).trans
     (hJYw.trans (by
       simp only [singularListCap, ScalarList6805Arithmetic.singularListCap]
       exact Nat.mul_le_mul_left _ hQY))
 have hJZ:J.degreeOf 3 = 0:=Nat.eq_zero_of_le_zero
   ((RCN281.degreeZ_le_zWeight K J).trans
     (hJZw.trans (by
       simpa only [Nat.mul_zero] using
         Nat.mul_le_mul_left (2 * slopeCap - 1) hQZ)))
 let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
 have hAne:A ≠ 0:=surfaceMap_ne_zero phi
   (polynomialEmbedding_injective K) J hJne
 have hAR:A.degreeOf 1 = 0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
 have hAZ:A.degreeOf 2 = 0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
 let q:Polynomial (GenericField K) :=
   RCN281.yProjection (GenericField K) A
 have hq:q ≠ 0 :=
   RCN281.yProjection_nonzero A hAne hAR hAZ
 have hroots:∀ z ∈ Gamma.image phi, z ∈ q.roots:=by
   intro z hz
   obtain ⟨S, hS, rfl⟩:=Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S) = 0
   have hv:seedlessPoint phi S 0 = phi S:=by
     simp [seedlessPoint_value]
   change (RCN281.yProjection (GenericField K) A).eval
     (phi S) = 0
   rw [← hv, RCN281.yProjection_eval A hAR hAZ
     (seedlessPoint phi S)]
   rw [seedlessPoint_surface_evaluation, eval_polynomialPoint_eq_specialization,
     hsolutions S hS]
   simp
 have hcard:(Gamma.image phi).card = Gamma.card :=
   Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
 rw [← hcard]
 calc
   (Gamma.image phi).card ≤ q.roots.toFinset.card:=by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _ ≤ q.roots.card:=Multiset.toFinset_card_le _
   _ ≤ q.natDegree:=Polynomial.card_roots' q
   _ ≤ A.degreeOf 0:=RCN281.yProjection_natDegree_le A
   _ ≤ J.degreeOf 1:=surfaceMap_degreeOf_le phi J 0
   _ ≤ singularListCap:=hJY
theorem seedless_list_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hlegacy:Q ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card = n)
   (hdegree:∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions:∀ S ∈ Gamma, specialization K S 0 Q = 0)
   (hagreement:∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card ≤ listBudget:=by
 classical
 have hcaps:=seedless_degree_caps K Q hbox
 have hsing:(singularPolynomials K Q Gamma).card ≤ singularListCap :=
   singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
     (fun S hS => (Finset.mem_filter.mp hS).2)
 have hreg (F:↥(positiveRFactors Q)) :
     (regularPolynomials K Q Gamma F).card * gap ≤
       (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1):=by
   have hdata:=directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF:=(positiveRFactors_spec Q F.1 F.2).2.1
   have hFZ:F.1.degreeOf 3 = 0:=Nat.eq_zero_of_le_zero
     ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub:regularPolynomials K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
   exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (regularPolynomials K Q Gamma F)
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => (Finset.mem_filter.mp hS).2.1)
     (fun S hS => (Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
 have hsumY:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
 have hsumR:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
 have hsumY':(∑ F:↥(positiveRFactors Q), F.1.degreeOf 1) ≤ Q.degreeOf 1:=by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumY
 have hsumR':(∑ F:↥(positiveRFactors Q), F.1.degreeOf 2) ≤ Q.degreeOf 2:=by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumR
 have hregularScaled :
     (∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap ≤
       regularListNumerator:=by
   calc
     _ = ∑ F:↥(positiveRFactors Q),
         (regularPolynomials K Q Gamma F).card * gap:=by rw [Finset.sum_mul]
     _ ≤ ∑ F:↥(positiveRFactors Q),
         (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1) :=
       Finset.sum_le_sum (fun F _ => hreg F)
     _ = (n - w) * (capY * (∑ F:↥(positiveRFactors Q), F.1.degreeOf 2) +
         capR * (∑ F:↥(positiveRFactors Q), F.1.degreeOf 1)):=by
       rw [← Finset.mul_sum, Finset.sum_add_distrib,
         ← Finset.mul_sum, ← Finset.mul_sum]
     _ ≤ (n - w) * (capY * slopeCap + capR * yTotalCap):=by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _ = regularListNumerator:=rfl
 have hcover:=seedless_solution_cover K Q hQ Gamma hsolutions
 have hscaled:=Nat.mul_le_mul_right gap hcover
 have htotal:Gamma.card * gap ≤ listNumerator:=by
   calc
     Gamma.card * gap ≤
         ((singularPolynomials K Q Gamma).card +
           ∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap :=
       hscaled
     _ = (singularPolynomials K Q Gamma).card * gap +
         (∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap:=by
       ring
     _ ≤ singularListCap * gap + regularListNumerator :=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _ = listNumerator:=by
       simp only [listNumerator, ScalarList6805Arithmetic.listNumerator,
         regularListNumerator, singularListCap, gap]
       omega
 by_contra hnot
 have hlarge:listBudget < Gamma.card:=Nat.lt_of_not_ge hnot
 have hgap:0 < gap:=gap_pos
 have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra:listBudget * gap < listNumerator:=hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem exists_seedless_vanishing_interpolant
   (received:IRSProfile.Index → IRSProfile.Field) :
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧
     Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     ∀ (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i ∈ support, P.eval (IRSProfile.domain i) = received i) →
       RCN319.specialization IRSProfile.Field P 0 Q = 0:=by
 classical
 obtain ⟨Q, hQ, hbox, hcontact⟩ :=
   ScalarList6805Arithmetic.exists_seedless_interpolant received
 change Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
   weightedCap w yTotalCap slopeCap at hbox
 have hlegacy:Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
     weightedCap w yTotalCap slopeCap:=by
   intro d hd
   obtain ⟨hYR, hR, hZ, hweight⟩:=hbox hd
   exact ⟨by omega, hR, hweight⟩
 refine ⟨Q, hQ, hbox, hlegacy, ?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero, add_zero] using hvalues i hi
 · have hdeg:=RCN319.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     weightedCap_pos
     hlegacy hdegree
   have hbound:weightedCap ≤ multiplicity * support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
theorem irs_scalar_finite_list_card_le
   (received:IRSProfile.Index → IRSProfile.Field)
   (L:Finset (IRSProfile.Index → IRSProfile.Field))
   (hcode:∀ c ∈ L, c ∈ IRSProfile.baseCode)
   (hclose:∀ c ∈ L, agreements ≤
     (Finset.univ.filter (fun i => c i = received i)).card) :
   L.card ≤ listBudget:=by
 classical
 let D:=↥L
 let codeword:D → IRSProfile.baseCode:=fun c => ⟨c.1, hcode c.1 c.2⟩
 let selected:D → Polynomial IRSProfile.Field:=fun c => ReedSolomon.toPolynomial (codeword c)
 let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
 have hselected:Function.Injective selected:=by
   intro c d h
   apply Subtype.ext
   funext i
   have hh:=congrArg (fun P:Polynomial IRSProfile.Field =>
     P.eval (IRSProfile.domain i)) h
   simpa only [selected, ReedSolomon.toPolynomial_eval_at_domain] using hh
 have hcard:Gamma.card = L.card:=by
   rw [show Gamma = Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected, Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q, hQ, hbox, hlegacy, hvanish⟩ :=
   exists_seedless_vanishing_interpolant received
 have hdegree:∀ P ∈ Gamma, P.natDegree ≤ w:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg:(selected c).degree < ((w + 1:ℕ):WithBot ℕ):=by
     have hh:=Polynomial.mem_degreeLT.mp hp
     change (selected c).degree <
       ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
     rw [base_dimension_exact] at hh
     exact hh
   by_cases hz:selected c = 0
   · simp [hz]
   · rw [← Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution:∀ P ∈ Gamma, specialization IRSProfile.Field P 0 Q = 0:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   let A:=Finset.univ.filter (fun i => c.1 i = received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement:∀ P ∈ Gamma, agreements ≤
     (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i) = received i)).card:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   have heq:Finset.univ.filter
       (fun i => (selected c).eval (IRSProfile.domain i) = received i) =
       Finset.univ.filter (fun i => c.1 i = received i):=by
     apply Finset.filter_congr
     intro i hi
     rw [ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound:=seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by simpa using index_card_exact) hdegree hsolution hagreement
 rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.ScalarList6805

end Compact_ScalarList6805

end P682

section P683
section Compact_Profile6805
/-! The exact 68.05 profile and its remaining proof obligation.
The scalar list arm, radius, score conversion and final extractor arithmetic
are checked here. The final theorem is conditional on AffineLineAlignmentBound;
that hypothesis has NOT been established. The proof template is adapted from
the promoted 68.03 LocatorProtocol and LocatorArithmetic modules. -/
namespace ProximityPrize.SubmissionLower.Profile6805Arithmetic
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false
def errors : ℕ := 80801
def radiusNumerator:ℕ:=10342655
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
theorem radius_floor:
    ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors:=by
  norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    errors,IRSProfile.Index]
theorem radius_admissible:
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ)^5 * 100000000^100 ≤ 103526493^100:=by decide
theorem score_radius_integer:
    (23211777:ℕ)^128 * (2^68 * 103526493) ≤ 100000000 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((5:ℝ)/100) ≤ (103526493:ℝ≥0)/100000000:=by
  have hroot:((2:ℝ≥0)^(5:ℕ))^((100:ℝ)⁻¹) ≤ (103526493:ℝ≥0)/100000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((5:ℝ)/100) = ((2:ℝ≥0)^(5:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/103526493):=by
  have hsub:(1 - radius:ℝ≥0) =23211777/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/103526493)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6805:=by
  have hscale:(100000000:ℝ≥0)/103526493 ≤ (2:ℝ≥0)^(-((5:ℝ)/100)):=by
    calc
      (100000000:ℝ≥0)/103526493=1/((103526493:ℝ≥0)/100000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((5:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/103526493):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (2:ℝ≥0)^(-((5:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6805:=by
      unfold claimedError
      rw [show -((((6805:ℕ):ℝ)/100)) =
          -((68:ℕ):ℝ) + -((5:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end ProximityPrize.SubmissionLower.Profile6805Arithmetic

namespace ProximityPrize.SubmissionLower.Profile6805
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
def errors:ℕ:=80801
def agreements:ℕ:=n-errors
def listBudget:ℕ:=5652701949
def mcaBudget:ℕ:=274980722458693138
def radius:ℝ≥0:=Profile6805Arithmetic.radius
theorem sixteen_row_separation:
   15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field= (2130706433:ℕ) ^ 6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_new
   (delta:ℝ)
   (hcell:(delta:ℝ) * (Fintype.card IRSProfile.Index:ℝ) <
     ((errors + 1:ℕ):ℝ)) :
   Code.Lambda
     (((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin 8 → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
     delta ≤ (listBudget:ℕ∞):=by
 apply RCN280.squared_eight_lambda_le_of_interleaved_list
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀ v ∈ L,agreements ≤
     (Finset.univ.filter (fun i=> v i=received i)).card:=by
   intro v hv
   have hc : Fintype.card IRSProfile.Index = n := Fintype.card_fin _
   have he : n - errors = agreements := by decide +kernel
   have hh := hclose v hv
   rw [hc, he] at hh
   exact hh
 classical
 letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩ :=
   Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
 have hsepD:15 * D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact sixteen_row_separation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field) :=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c ∈ projected,c ∈ IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c ∈ projected,agreements ≤
     (Finset.univ.filter (fun i=> c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=ScalarList6805.irs_scalar_finite_list_card_le
   (momentProjection t received) projected hcode hnear
 change projected.card ≤ listBudget at hbound
 rw [hprojcard,hDcard] at hbound
 omega
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (radius:ℝ) ≤ (listBudget:ℕ∞):=by
 rw [irs_squared_carrier_eq]
 apply squared_eight_lambda_new (radius:ℝ)
 norm_num [radius,Profile6805Arithmetic.radius,claimedRadius,
   Profile6805Arithmetic.radiusNumerator,
   Profile6805Arithmetic.radiusDenominator,
   errors,IRSProfile.Index]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors by
     simpa only [radius,errors,Profile6805Arithmetic.errors] using
       Profile6805Arithmetic.radius_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,Profile6805Arithmetic.errors] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [RCN284.irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,Profile6805Arithmetic.radius,
         claimedRadius,Profile6805Arithmetic.radiusNumerator,
         Profile6805Arithmetic.radiusDenominator])
       (by norm_num [radius,Profile6805Arithmetic.radius,
         claimedRadius,Profile6805Arithmetic.radiusNumerator,
         Profile6805Arithmetic.radiusDenominator])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field) :=
     base_mca_le_of_alignment halign
   _= (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem field_capacity_split:
   2 ^ (128:ℕ) * (mcaBudget + listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [RCN284.field_cardinality]
 norm_num [mcaBudget,listBudget]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0) / 2 ^ (128:ℕ):=by
 rw [← ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code ^⋈ (Fin 2) :
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) +
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
     add_le_add (mca_le_of_alignment halign) hList
   _= ((mcaBudget + listBudget:ℕ):ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [← ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal) / 2 ^ (128:ℕ):=by
     apply RCN284.nat_div_le_inv_pow
     · norm_num [mcaBudget,listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6805_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   ProtocolClaim 6805 10342655 33554432 where
 admissible:=Profile6805Arithmetic.radius_admissible
 reduction:=by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   simpa [reductionTarget,ProximityGap.prizeThreshold] using
     certifiedGammaError_le_of_alignment halign
 score:=by
   change (1 - Profile6805Arithmetic.radius) ^
     IRSProfile.repetitions ≤ claimedError 6805
   exact Profile6805Arithmetic.score_target_le
end
end ProximityPrize.SubmissionLower.Profile6805

end Compact_Profile6805

section Compact_Protocol80801
/-! Reuse the checked scalar-list reduction and 68.05 score arithmetic at
this exact radius. The new work supplies its alignment hypothesis. -/
namespace ProximityPrize.SubmissionLower.Lower80801.Protocol
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280

abbrev protocolClaim6805_of_alignment :=
  Profile6805.protocolClaim6805_of_alignment

end ProximityPrize.SubmissionLower.Lower80801.Protocol

end Compact_Protocol80801

end P683

section P684
/-! The 68.05 closure is conditional only on the finite numerical receipts.
It is deliberately not installed as Benchmark.candidate before those receipts
have been discharged. The MCA allowance below uses the corrected scalar-list
budget from BoundaryTailProtocol. -/
namespace ProximityPrize.SubmissionLower.Lower80801.Closure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80801.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := 253080253061200723

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ Profile6805.mcaBudget := by
  decide +kernel

variable {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ}
variable (hbase : BoundaryTailBaseOracle.Receipt zero split (PhaseSemantics.phaseCap 0))
  (hpref : PhaseSemantics.PrefixReceiptSound)
  (hthreshold : PhaseSemantics.ThresholdReceiptSound)
  (hruns : PhaseSemantics.RunReceiptSound)
  (hledger : Assembly.LedgerReceiptSound ledgerBudget)
include hbase hpref hthreshold hruns hledger

/-- Actual selected-count bound, retaining the full ledger margin. -/
theorem selectedNoLargePencilBound6805_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80801 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80801 = 181343 := by decide +kernel
  have hs : Fintype.card I - 80801 = 181343 :=
    (congrArg (fun n : ℕ => n - 80801) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181343 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80801 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Assembly.selected_pair_count_le hbase hpref hthreshold hruns hledger
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

/-- The scalar-list budget reserves 5652701949 challenges, leaving the exact
MCA allowance 274980722458693138 checked by the protocol module. -/
theorem selectedNoLargePencilBound6805 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80801 Profile6805.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6805_tight hbase hpref hthreshold hruns hledger
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6805_tight :
    AffineLineAlignmentBound IRSProfile.baseCode 80801 ledgerBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80801
    ledgerBudget (selectedNoLargePencilBound6805_tight hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem alignmentBound6805 :
    AffineLineAlignmentBound IRSProfile.baseCode Profile6805.errors Profile6805.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80801
    Profile6805.mcaBudget (selectedNoLargePencilBound6805 hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, Profile6805.errors] using h

theorem protocolClaim6805 : ProtocolClaim 6805 10342655 33554432 :=
  Profile6805.protocolClaim6805_of_alignment
    (alignmentBound6805 hbase hpref hthreshold hruns hledger)

end
end ProximityPrize.SubmissionLower.Lower80801.Closure

end P684

section P685
namespace ProximityPrize.SubmissionLower.Lower80801.Claim

open ProximityPrize.Benchmark
open Lower80801
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem protocolClaim : ProtocolClaim 6805 10342655 33554432 := by
  exact Closure.protocolClaim6805
    BoundaryTailBaseChecked.phaseReceipt
    PhaseChecked.prefixReceipt
    ThresholdCompressed.thresholdReceipt
    PhaseChecked.runsReceipt
    LedgerChecked.ledgerReceipt

end ProximityPrize.SubmissionLower.Lower80801.Claim

end P685

