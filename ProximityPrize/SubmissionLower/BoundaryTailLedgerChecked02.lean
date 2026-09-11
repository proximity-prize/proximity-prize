import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked01

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r6part0:∀ k ∈ List.range 8,RunsValid (rowContext 6 (0+k)) 0 (lookup 6 (0+k)):=by decide +kernel
theorem r6part8:∀ k ∈ List.range 8,RunsValid (rowContext 6 (8+k)) 0 (lookup 6 (8+k)):=by decide +kernel
theorem r6part16:∀ k ∈ List.range 8,RunsValid (rowContext 6 (16+k)) 0 (lookup 6 (16+k)):=by decide +kernel
theorem r6part24:∀ k ∈ List.range 8,RunsValid (rowContext 6 (24+k)) 0 (lookup 6 (24+k)):=by decide +kernel
theorem r6part32:∀ k ∈ List.range 8,RunsValid (rowContext 6 (32+k)) 0 (lookup 6 (32+k)):=by decide +kernel
theorem r6part40:∀ k ∈ List.range 8,RunsValid (rowContext 6 (40+k)) 0 (lookup 6 (40+k)):=by decide +kernel
theorem r6part48:∀ k ∈ List.range 8,RunsValid (rowContext 6 (48+k)) 0 (lookup 6 (48+k)):=by decide +kernel
theorem r6part56:∀ k ∈ List.range 8,RunsValid (rowContext 6 (56+k)) 0 (lookup 6 (56+k)):=by decide +kernel
theorem r6part64:∀ k ∈ List.range 8,RunsValid (rowContext 6 (64+k)) 0 (lookup 6 (64+k)):=by decide +kernel
theorem r6part72:∀ k ∈ List.range 8,RunsValid (rowContext 6 (72+k)) 0 (lookup 6 (72+k)):=by decide +kernel
theorem r6part80:∀ k ∈ List.range 8,RunsValid (rowContext 6 (80+k)) 0 (lookup 6 (80+k)):=by decide +kernel
theorem r6part88:∀ k ∈ List.range 8,RunsValid (rowContext 6 (88+k)) 0 (lookup 6 (88+k)):=by decide +kernel
theorem r6part96:∀ k ∈ List.range 8,RunsValid (rowContext 6 (96+k)) 0 (lookup 6 (96+k)):=by decide +kernel
theorem r6part104:∀ k ∈ List.range 8,RunsValid (rowContext 6 (104+k)) 0 (lookup 6 (104+k)):=by decide +kernel
theorem r6part112:∀ k ∈ List.range 8,RunsValid (rowContext 6 (112+k)) 0 (lookup 6 (112+k)):=by decide +kernel
theorem r6part120:∀ k ∈ List.range 8,RunsValid (rowContext 6 (120+k)) 0 (lookup 6 (120+k)):=by decide +kernel
theorem r6part128:∀ k ∈ List.range 8,RunsValid (rowContext 6 (128+k)) 0 (lookup 6 (128+k)):=by decide +kernel
theorem r6part136:∀ k ∈ List.range 1,RunsValid (rowContext 6 (136+k)) 0 (lookup 6 (136+k)):=by decide +kernel

theorem checkedR6 (V:ℕ) (hV:V ∈ List.range 137):RunsValid (rowContext 6 V) 0 (lookup 6 V):=by
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r6part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r6part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r6part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r6part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r6part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r6part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r6part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r6part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r6part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r6part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r6part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r6part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r6part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r6part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r6part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r6part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r6part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r6part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r7part0:∀ k ∈ List.range 8,RunsValid (rowContext 7 (0+k)) 0 (lookup 7 (0+k)):=by decide +kernel
theorem r7part8:∀ k ∈ List.range 8,RunsValid (rowContext 7 (8+k)) 0 (lookup 7 (8+k)):=by decide +kernel
theorem r7part16:∀ k ∈ List.range 8,RunsValid (rowContext 7 (16+k)) 0 (lookup 7 (16+k)):=by decide +kernel
theorem r7part24:∀ k ∈ List.range 8,RunsValid (rowContext 7 (24+k)) 0 (lookup 7 (24+k)):=by decide +kernel
theorem r7part32:∀ k ∈ List.range 8,RunsValid (rowContext 7 (32+k)) 0 (lookup 7 (32+k)):=by decide +kernel
theorem r7part40:∀ k ∈ List.range 8,RunsValid (rowContext 7 (40+k)) 0 (lookup 7 (40+k)):=by decide +kernel
theorem r7part48:∀ k ∈ List.range 8,RunsValid (rowContext 7 (48+k)) 0 (lookup 7 (48+k)):=by decide +kernel
theorem r7part56:∀ k ∈ List.range 8,RunsValid (rowContext 7 (56+k)) 0 (lookup 7 (56+k)):=by decide +kernel
theorem r7part64:∀ k ∈ List.range 8,RunsValid (rowContext 7 (64+k)) 0 (lookup 7 (64+k)):=by decide +kernel
theorem r7part72:∀ k ∈ List.range 8,RunsValid (rowContext 7 (72+k)) 0 (lookup 7 (72+k)):=by decide +kernel
theorem r7part80:∀ k ∈ List.range 8,RunsValid (rowContext 7 (80+k)) 0 (lookup 7 (80+k)):=by decide +kernel
theorem r7part88:∀ k ∈ List.range 8,RunsValid (rowContext 7 (88+k)) 0 (lookup 7 (88+k)):=by decide +kernel
theorem r7part96:∀ k ∈ List.range 8,RunsValid (rowContext 7 (96+k)) 0 (lookup 7 (96+k)):=by decide +kernel
theorem r7part104:∀ k ∈ List.range 8,RunsValid (rowContext 7 (104+k)) 0 (lookup 7 (104+k)):=by decide +kernel
theorem r7part112:∀ k ∈ List.range 8,RunsValid (rowContext 7 (112+k)) 0 (lookup 7 (112+k)):=by decide +kernel
theorem r7part120:∀ k ∈ List.range 8,RunsValid (rowContext 7 (120+k)) 0 (lookup 7 (120+k)):=by decide +kernel
theorem r7part128:∀ k ∈ List.range 8,RunsValid (rowContext 7 (128+k)) 0 (lookup 7 (128+k)):=by decide +kernel

theorem checkedR7 (V:ℕ) (hV:V ∈ List.range 136):RunsValid (rowContext 7 V) 0 (lookup 7 V):=by
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r7part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r7part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r7part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r7part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r7part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r7part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r7part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r7part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r7part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r7part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r7part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r7part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r7part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r7part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r7part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r7part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r7part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r8part0:∀ k ∈ List.range 8,RunsValid (rowContext 8 (0+k)) 0 (lookup 8 (0+k)):=by decide +kernel
theorem r8part8:∀ k ∈ List.range 8,RunsValid (rowContext 8 (8+k)) 0 (lookup 8 (8+k)):=by decide +kernel
theorem r8part16:∀ k ∈ List.range 8,RunsValid (rowContext 8 (16+k)) 0 (lookup 8 (16+k)):=by decide +kernel
theorem r8part24:∀ k ∈ List.range 8,RunsValid (rowContext 8 (24+k)) 0 (lookup 8 (24+k)):=by decide +kernel
theorem r8part32:∀ k ∈ List.range 8,RunsValid (rowContext 8 (32+k)) 0 (lookup 8 (32+k)):=by decide +kernel
theorem r8part40:∀ k ∈ List.range 8,RunsValid (rowContext 8 (40+k)) 0 (lookup 8 (40+k)):=by decide +kernel
theorem r8part48:∀ k ∈ List.range 8,RunsValid (rowContext 8 (48+k)) 0 (lookup 8 (48+k)):=by decide +kernel
theorem r8part56:∀ k ∈ List.range 8,RunsValid (rowContext 8 (56+k)) 0 (lookup 8 (56+k)):=by decide +kernel
theorem r8part64:∀ k ∈ List.range 8,RunsValid (rowContext 8 (64+k)) 0 (lookup 8 (64+k)):=by decide +kernel
theorem r8part72:∀ k ∈ List.range 8,RunsValid (rowContext 8 (72+k)) 0 (lookup 8 (72+k)):=by decide +kernel
theorem r8part80:∀ k ∈ List.range 8,RunsValid (rowContext 8 (80+k)) 0 (lookup 8 (80+k)):=by decide +kernel
theorem r8part88:∀ k ∈ List.range 8,RunsValid (rowContext 8 (88+k)) 0 (lookup 8 (88+k)):=by decide +kernel
theorem r8part96:∀ k ∈ List.range 8,RunsValid (rowContext 8 (96+k)) 0 (lookup 8 (96+k)):=by decide +kernel
theorem r8part104:∀ k ∈ List.range 8,RunsValid (rowContext 8 (104+k)) 0 (lookup 8 (104+k)):=by decide +kernel
theorem r8part112:∀ k ∈ List.range 8,RunsValid (rowContext 8 (112+k)) 0 (lookup 8 (112+k)):=by decide +kernel
theorem r8part120:∀ k ∈ List.range 8,RunsValid (rowContext 8 (120+k)) 0 (lookup 8 (120+k)):=by decide +kernel
theorem r8part128:∀ k ∈ List.range 7,RunsValid (rowContext 8 (128+k)) 0 (lookup 8 (128+k)):=by decide +kernel

theorem checkedR8 (V:ℕ) (hV:V ∈ List.range 135):RunsValid (rowContext 8 V) 0 (lookup 8 V):=by
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r8part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r8part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r8part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r8part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r8part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r8part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r8part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r8part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r8part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r8part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r8part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r8part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r8part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r8part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r8part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r8part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r8part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r9part0:∀ k ∈ List.range 8,RunsValid (rowContext 9 (0+k)) 0 (lookup 9 (0+k)):=by decide +kernel
theorem r9part8:∀ k ∈ List.range 8,RunsValid (rowContext 9 (8+k)) 0 (lookup 9 (8+k)):=by decide +kernel
theorem r9part16:∀ k ∈ List.range 8,RunsValid (rowContext 9 (16+k)) 0 (lookup 9 (16+k)):=by decide +kernel
theorem r9part24:∀ k ∈ List.range 8,RunsValid (rowContext 9 (24+k)) 0 (lookup 9 (24+k)):=by decide +kernel
theorem r9part32:∀ k ∈ List.range 8,RunsValid (rowContext 9 (32+k)) 0 (lookup 9 (32+k)):=by decide +kernel
theorem r9part40:∀ k ∈ List.range 8,RunsValid (rowContext 9 (40+k)) 0 (lookup 9 (40+k)):=by decide +kernel
theorem r9part48:∀ k ∈ List.range 8,RunsValid (rowContext 9 (48+k)) 0 (lookup 9 (48+k)):=by decide +kernel
theorem r9part56:∀ k ∈ List.range 8,RunsValid (rowContext 9 (56+k)) 0 (lookup 9 (56+k)):=by decide +kernel
theorem r9part64:∀ k ∈ List.range 8,RunsValid (rowContext 9 (64+k)) 0 (lookup 9 (64+k)):=by decide +kernel
theorem r9part72:∀ k ∈ List.range 8,RunsValid (rowContext 9 (72+k)) 0 (lookup 9 (72+k)):=by decide +kernel
theorem r9part80:∀ k ∈ List.range 8,RunsValid (rowContext 9 (80+k)) 0 (lookup 9 (80+k)):=by decide +kernel
theorem r9part88:∀ k ∈ List.range 8,RunsValid (rowContext 9 (88+k)) 0 (lookup 9 (88+k)):=by decide +kernel
theorem r9part96:∀ k ∈ List.range 8,RunsValid (rowContext 9 (96+k)) 0 (lookup 9 (96+k)):=by decide +kernel
theorem r9part104:∀ k ∈ List.range 8,RunsValid (rowContext 9 (104+k)) 0 (lookup 9 (104+k)):=by decide +kernel
theorem r9part112:∀ k ∈ List.range 8,RunsValid (rowContext 9 (112+k)) 0 (lookup 9 (112+k)):=by decide +kernel
theorem r9part120:∀ k ∈ List.range 8,RunsValid (rowContext 9 (120+k)) 0 (lookup 9 (120+k)):=by decide +kernel
theorem r9part128:∀ k ∈ List.range 6,RunsValid (rowContext 9 (128+k)) 0 (lookup 9 (128+k)):=by decide +kernel

theorem checkedR9 (V:ℕ) (hV:V ∈ List.range 134):RunsValid (rowContext 9 V) 0 (lookup 9 V):=by
  have hv:V < 134:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r9part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r9part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r9part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r9part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r9part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r9part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r9part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r9part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r9part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r9part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r9part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r9part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r9part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r9part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r9part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r9part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r9part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r10part0:∀ k ∈ List.range 8,RunsValid (rowContext 10 (0+k)) 0 (lookup 10 (0+k)):=by decide +kernel
theorem r10part8:∀ k ∈ List.range 8,RunsValid (rowContext 10 (8+k)) 0 (lookup 10 (8+k)):=by decide +kernel
theorem r10part16:∀ k ∈ List.range 8,RunsValid (rowContext 10 (16+k)) 0 (lookup 10 (16+k)):=by decide +kernel
theorem r10part24:∀ k ∈ List.range 8,RunsValid (rowContext 10 (24+k)) 0 (lookup 10 (24+k)):=by decide +kernel
theorem r10part32:∀ k ∈ List.range 8,RunsValid (rowContext 10 (32+k)) 0 (lookup 10 (32+k)):=by decide +kernel
theorem r10part40:∀ k ∈ List.range 8,RunsValid (rowContext 10 (40+k)) 0 (lookup 10 (40+k)):=by decide +kernel
theorem r10part48:∀ k ∈ List.range 8,RunsValid (rowContext 10 (48+k)) 0 (lookup 10 (48+k)):=by decide +kernel
theorem r10part56:∀ k ∈ List.range 8,RunsValid (rowContext 10 (56+k)) 0 (lookup 10 (56+k)):=by decide +kernel
theorem r10part64:∀ k ∈ List.range 8,RunsValid (rowContext 10 (64+k)) 0 (lookup 10 (64+k)):=by decide +kernel
theorem r10part72:∀ k ∈ List.range 8,RunsValid (rowContext 10 (72+k)) 0 (lookup 10 (72+k)):=by decide +kernel
theorem r10part80:∀ k ∈ List.range 8,RunsValid (rowContext 10 (80+k)) 0 (lookup 10 (80+k)):=by decide +kernel
theorem r10part88:∀ k ∈ List.range 8,RunsValid (rowContext 10 (88+k)) 0 (lookup 10 (88+k)):=by decide +kernel
theorem r10part96:∀ k ∈ List.range 8,RunsValid (rowContext 10 (96+k)) 0 (lookup 10 (96+k)):=by decide +kernel
theorem r10part104:∀ k ∈ List.range 8,RunsValid (rowContext 10 (104+k)) 0 (lookup 10 (104+k)):=by decide +kernel
theorem r10part112:∀ k ∈ List.range 8,RunsValid (rowContext 10 (112+k)) 0 (lookup 10 (112+k)):=by decide +kernel
theorem r10part120:∀ k ∈ List.range 8,RunsValid (rowContext 10 (120+k)) 0 (lookup 10 (120+k)):=by decide +kernel
theorem r10part128:∀ k ∈ List.range 5,RunsValid (rowContext 10 (128+k)) 0 (lookup 10 (128+k)):=by decide +kernel

theorem checkedR10 (V:ℕ) (hV:V ∈ List.range 133):RunsValid (rowContext 10 V) 0 (lookup 10 V):=by
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r10part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r10part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r10part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r10part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r10part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r10part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r10part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r10part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r10part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r10part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r10part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r10part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r10part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r10part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r10part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r10part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r10part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
