import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked06

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r31part0:∀ k ∈ List.range 8,RunsValid (rowContext 31 (0+k)) 0 (lookup 31 (0+k)):=by decide +kernel
theorem r31part8:∀ k ∈ List.range 8,RunsValid (rowContext 31 (8+k)) 0 (lookup 31 (8+k)):=by decide +kernel
theorem r31part16:∀ k ∈ List.range 8,RunsValid (rowContext 31 (16+k)) 0 (lookup 31 (16+k)):=by decide +kernel
theorem r31part24:∀ k ∈ List.range 8,RunsValid (rowContext 31 (24+k)) 0 (lookup 31 (24+k)):=by decide +kernel
theorem r31part32:∀ k ∈ List.range 8,RunsValid (rowContext 31 (32+k)) 0 (lookup 31 (32+k)):=by decide +kernel
theorem r31part40:∀ k ∈ List.range 8,RunsValid (rowContext 31 (40+k)) 0 (lookup 31 (40+k)):=by decide +kernel
theorem r31part48:∀ k ∈ List.range 8,RunsValid (rowContext 31 (48+k)) 0 (lookup 31 (48+k)):=by decide +kernel
theorem r31part56:∀ k ∈ List.range 8,RunsValid (rowContext 31 (56+k)) 0 (lookup 31 (56+k)):=by decide +kernel
theorem r31part64:∀ k ∈ List.range 8,RunsValid (rowContext 31 (64+k)) 0 (lookup 31 (64+k)):=by decide +kernel
theorem r31part72:∀ k ∈ List.range 8,RunsValid (rowContext 31 (72+k)) 0 (lookup 31 (72+k)):=by decide +kernel
theorem r31part80:∀ k ∈ List.range 8,RunsValid (rowContext 31 (80+k)) 0 (lookup 31 (80+k)):=by decide +kernel
theorem r31part88:∀ k ∈ List.range 8,RunsValid (rowContext 31 (88+k)) 0 (lookup 31 (88+k)):=by decide +kernel
theorem r31part96:∀ k ∈ List.range 8,RunsValid (rowContext 31 (96+k)) 0 (lookup 31 (96+k)):=by decide +kernel
theorem r31part104:∀ k ∈ List.range 8,RunsValid (rowContext 31 (104+k)) 0 (lookup 31 (104+k)):=by decide +kernel

theorem checkedR31 (V:ℕ) (hV:V ∈ List.range 112):RunsValid (rowContext 31 V) 0 (lookup 31 V):=by
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r31part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r31part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r31part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r31part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r31part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r31part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r31part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r31part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r31part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r31part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r31part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r31part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r31part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp:=r31part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
