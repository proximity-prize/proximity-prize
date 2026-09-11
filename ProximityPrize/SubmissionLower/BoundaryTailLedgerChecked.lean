import ProximityPrize.SubmissionLower.BoundaryTailLedgerData

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
open ProximityPrize.SubmissionLower.Lower80801.Assembly
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem r1part0:∀ k ∈ List.range 8,RunsValid (rowContext 1 (0+k)) 0 (lookup 1 (0+k)):=by decide +kernel
theorem r1part8:∀ k ∈ List.range 8,RunsValid (rowContext 1 (8+k)) 0 (lookup 1 (8+k)):=by decide +kernel
theorem r1part16:∀ k ∈ List.range 8,RunsValid (rowContext 1 (16+k)) 0 (lookup 1 (16+k)):=by decide +kernel
theorem r1part24:∀ k ∈ List.range 8,RunsValid (rowContext 1 (24+k)) 0 (lookup 1 (24+k)):=by decide +kernel
theorem r1part32:∀ k ∈ List.range 8,RunsValid (rowContext 1 (32+k)) 0 (lookup 1 (32+k)):=by decide +kernel
theorem r1part40:∀ k ∈ List.range 8,RunsValid (rowContext 1 (40+k)) 0 (lookup 1 (40+k)):=by decide +kernel
theorem r1part48:∀ k ∈ List.range 8,RunsValid (rowContext 1 (48+k)) 0 (lookup 1 (48+k)):=by decide +kernel
theorem r1part56:∀ k ∈ List.range 8,RunsValid (rowContext 1 (56+k)) 0 (lookup 1 (56+k)):=by decide +kernel
theorem r1part64:∀ k ∈ List.range 8,RunsValid (rowContext 1 (64+k)) 0 (lookup 1 (64+k)):=by decide +kernel
theorem r1part72:∀ k ∈ List.range 8,RunsValid (rowContext 1 (72+k)) 0 (lookup 1 (72+k)):=by decide +kernel
theorem r1part80:∀ k ∈ List.range 8,RunsValid (rowContext 1 (80+k)) 0 (lookup 1 (80+k)):=by decide +kernel
theorem r1part88:∀ k ∈ List.range 8,RunsValid (rowContext 1 (88+k)) 0 (lookup 1 (88+k)):=by decide +kernel
theorem r1part96:∀ k ∈ List.range 8,RunsValid (rowContext 1 (96+k)) 0 (lookup 1 (96+k)):=by decide +kernel
theorem r1part104:∀ k ∈ List.range 8,RunsValid (rowContext 1 (104+k)) 0 (lookup 1 (104+k)):=by decide +kernel
theorem r1part112:∀ k ∈ List.range 8,RunsValid (rowContext 1 (112+k)) 0 (lookup 1 (112+k)):=by decide +kernel
theorem r1part120:∀ k ∈ List.range 8,RunsValid (rowContext 1 (120+k)) 0 (lookup 1 (120+k)):=by decide +kernel
theorem r1part128:∀ k ∈ List.range 8,RunsValid (rowContext 1 (128+k)) 0 (lookup 1 (128+k)):=by decide +kernel
theorem r1part136:∀ k ∈ List.range 6,RunsValid (rowContext 1 (136+k)) 0 (lookup 1 (136+k)):=by decide +kernel

theorem checkedR1 (V:ℕ) (hV:V ∈ List.range 142):RunsValid (rowContext 1 V) 0 (lookup 1 V):=by
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r1part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r1part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r2part0:∀ k ∈ List.range 8,RunsValid (rowContext 2 (0+k)) 0 (lookup 2 (0+k)):=by decide +kernel
theorem r2part8:∀ k ∈ List.range 8,RunsValid (rowContext 2 (8+k)) 0 (lookup 2 (8+k)):=by decide +kernel
theorem r2part16:∀ k ∈ List.range 8,RunsValid (rowContext 2 (16+k)) 0 (lookup 2 (16+k)):=by decide +kernel
theorem r2part24:∀ k ∈ List.range 8,RunsValid (rowContext 2 (24+k)) 0 (lookup 2 (24+k)):=by decide +kernel
theorem r2part32:∀ k ∈ List.range 8,RunsValid (rowContext 2 (32+k)) 0 (lookup 2 (32+k)):=by decide +kernel
theorem r2part40:∀ k ∈ List.range 8,RunsValid (rowContext 2 (40+k)) 0 (lookup 2 (40+k)):=by decide +kernel
theorem r2part48:∀ k ∈ List.range 8,RunsValid (rowContext 2 (48+k)) 0 (lookup 2 (48+k)):=by decide +kernel
theorem r2part56:∀ k ∈ List.range 8,RunsValid (rowContext 2 (56+k)) 0 (lookup 2 (56+k)):=by decide +kernel
theorem r2part64:∀ k ∈ List.range 8,RunsValid (rowContext 2 (64+k)) 0 (lookup 2 (64+k)):=by decide +kernel
theorem r2part72:∀ k ∈ List.range 8,RunsValid (rowContext 2 (72+k)) 0 (lookup 2 (72+k)):=by decide +kernel
theorem r2part80:∀ k ∈ List.range 8,RunsValid (rowContext 2 (80+k)) 0 (lookup 2 (80+k)):=by decide +kernel
theorem r2part88:∀ k ∈ List.range 8,RunsValid (rowContext 2 (88+k)) 0 (lookup 2 (88+k)):=by decide +kernel
theorem r2part96:∀ k ∈ List.range 8,RunsValid (rowContext 2 (96+k)) 0 (lookup 2 (96+k)):=by decide +kernel
theorem r2part104:∀ k ∈ List.range 8,RunsValid (rowContext 2 (104+k)) 0 (lookup 2 (104+k)):=by decide +kernel
theorem r2part112:∀ k ∈ List.range 8,RunsValid (rowContext 2 (112+k)) 0 (lookup 2 (112+k)):=by decide +kernel
theorem r2part120:∀ k ∈ List.range 8,RunsValid (rowContext 2 (120+k)) 0 (lookup 2 (120+k)):=by decide +kernel
theorem r2part128:∀ k ∈ List.range 8,RunsValid (rowContext 2 (128+k)) 0 (lookup 2 (128+k)):=by decide +kernel
theorem r2part136:∀ k ∈ List.range 5,RunsValid (rowContext 2 (136+k)) 0 (lookup 2 (136+k)):=by decide +kernel

theorem checkedR2 (V:ℕ) (hV:V ∈ List.range 141):RunsValid (rowContext 2 V) 0 (lookup 2 V):=by
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r2part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r2part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r3part0:∀ k ∈ List.range 8,RunsValid (rowContext 3 (0+k)) 0 (lookup 3 (0+k)):=by decide +kernel
theorem r3part8:∀ k ∈ List.range 8,RunsValid (rowContext 3 (8+k)) 0 (lookup 3 (8+k)):=by decide +kernel
theorem r3part16:∀ k ∈ List.range 8,RunsValid (rowContext 3 (16+k)) 0 (lookup 3 (16+k)):=by decide +kernel
theorem r3part24:∀ k ∈ List.range 8,RunsValid (rowContext 3 (24+k)) 0 (lookup 3 (24+k)):=by decide +kernel
theorem r3part32:∀ k ∈ List.range 8,RunsValid (rowContext 3 (32+k)) 0 (lookup 3 (32+k)):=by decide +kernel
theorem r3part40:∀ k ∈ List.range 8,RunsValid (rowContext 3 (40+k)) 0 (lookup 3 (40+k)):=by decide +kernel
theorem r3part48:∀ k ∈ List.range 8,RunsValid (rowContext 3 (48+k)) 0 (lookup 3 (48+k)):=by decide +kernel
theorem r3part56:∀ k ∈ List.range 8,RunsValid (rowContext 3 (56+k)) 0 (lookup 3 (56+k)):=by decide +kernel
theorem r3part64:∀ k ∈ List.range 8,RunsValid (rowContext 3 (64+k)) 0 (lookup 3 (64+k)):=by decide +kernel
theorem r3part72:∀ k ∈ List.range 8,RunsValid (rowContext 3 (72+k)) 0 (lookup 3 (72+k)):=by decide +kernel
theorem r3part80:∀ k ∈ List.range 8,RunsValid (rowContext 3 (80+k)) 0 (lookup 3 (80+k)):=by decide +kernel
theorem r3part88:∀ k ∈ List.range 8,RunsValid (rowContext 3 (88+k)) 0 (lookup 3 (88+k)):=by decide +kernel
theorem r3part96:∀ k ∈ List.range 8,RunsValid (rowContext 3 (96+k)) 0 (lookup 3 (96+k)):=by decide +kernel
theorem r3part104:∀ k ∈ List.range 8,RunsValid (rowContext 3 (104+k)) 0 (lookup 3 (104+k)):=by decide +kernel
theorem r3part112:∀ k ∈ List.range 8,RunsValid (rowContext 3 (112+k)) 0 (lookup 3 (112+k)):=by decide +kernel
theorem r3part120:∀ k ∈ List.range 8,RunsValid (rowContext 3 (120+k)) 0 (lookup 3 (120+k)):=by decide +kernel
theorem r3part128:∀ k ∈ List.range 8,RunsValid (rowContext 3 (128+k)) 0 (lookup 3 (128+k)):=by decide +kernel
theorem r3part136:∀ k ∈ List.range 4,RunsValid (rowContext 3 (136+k)) 0 (lookup 3 (136+k)):=by decide +kernel

theorem checkedR3 (V:ℕ) (hV:V ∈ List.range 140):RunsValid (rowContext 3 V) 0 (lookup 3 V):=by
  have hv:V < 140:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r3part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r3part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r4part0:∀ k ∈ List.range 8,RunsValid (rowContext 4 (0+k)) 0 (lookup 4 (0+k)):=by decide +kernel
theorem r4part8:∀ k ∈ List.range 8,RunsValid (rowContext 4 (8+k)) 0 (lookup 4 (8+k)):=by decide +kernel
theorem r4part16:∀ k ∈ List.range 8,RunsValid (rowContext 4 (16+k)) 0 (lookup 4 (16+k)):=by decide +kernel
theorem r4part24:∀ k ∈ List.range 8,RunsValid (rowContext 4 (24+k)) 0 (lookup 4 (24+k)):=by decide +kernel
theorem r4part32:∀ k ∈ List.range 8,RunsValid (rowContext 4 (32+k)) 0 (lookup 4 (32+k)):=by decide +kernel
theorem r4part40:∀ k ∈ List.range 8,RunsValid (rowContext 4 (40+k)) 0 (lookup 4 (40+k)):=by decide +kernel
theorem r4part48:∀ k ∈ List.range 8,RunsValid (rowContext 4 (48+k)) 0 (lookup 4 (48+k)):=by decide +kernel
theorem r4part56:∀ k ∈ List.range 8,RunsValid (rowContext 4 (56+k)) 0 (lookup 4 (56+k)):=by decide +kernel
theorem r4part64:∀ k ∈ List.range 8,RunsValid (rowContext 4 (64+k)) 0 (lookup 4 (64+k)):=by decide +kernel
theorem r4part72:∀ k ∈ List.range 8,RunsValid (rowContext 4 (72+k)) 0 (lookup 4 (72+k)):=by decide +kernel
theorem r4part80:∀ k ∈ List.range 8,RunsValid (rowContext 4 (80+k)) 0 (lookup 4 (80+k)):=by decide +kernel
theorem r4part88:∀ k ∈ List.range 8,RunsValid (rowContext 4 (88+k)) 0 (lookup 4 (88+k)):=by decide +kernel
theorem r4part96:∀ k ∈ List.range 8,RunsValid (rowContext 4 (96+k)) 0 (lookup 4 (96+k)):=by decide +kernel
theorem r4part104:∀ k ∈ List.range 8,RunsValid (rowContext 4 (104+k)) 0 (lookup 4 (104+k)):=by decide +kernel
theorem r4part112:∀ k ∈ List.range 8,RunsValid (rowContext 4 (112+k)) 0 (lookup 4 (112+k)):=by decide +kernel
theorem r4part120:∀ k ∈ List.range 8,RunsValid (rowContext 4 (120+k)) 0 (lookup 4 (120+k)):=by decide +kernel
theorem r4part128:∀ k ∈ List.range 8,RunsValid (rowContext 4 (128+k)) 0 (lookup 4 (128+k)):=by decide +kernel
theorem r4part136:∀ k ∈ List.range 3,RunsValid (rowContext 4 (136+k)) 0 (lookup 4 (136+k)):=by decide +kernel

theorem checkedR4 (V:ℕ) (hV:V ∈ List.range 139):RunsValid (rowContext 4 V) 0 (lookup 4 V):=by
  have hv:V < 139:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r4part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r4part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

theorem r5part0:∀ k ∈ List.range 8,RunsValid (rowContext 5 (0+k)) 0 (lookup 5 (0+k)):=by decide +kernel
theorem r5part8:∀ k ∈ List.range 8,RunsValid (rowContext 5 (8+k)) 0 (lookup 5 (8+k)):=by decide +kernel
theorem r5part16:∀ k ∈ List.range 8,RunsValid (rowContext 5 (16+k)) 0 (lookup 5 (16+k)):=by decide +kernel
theorem r5part24:∀ k ∈ List.range 8,RunsValid (rowContext 5 (24+k)) 0 (lookup 5 (24+k)):=by decide +kernel
theorem r5part32:∀ k ∈ List.range 8,RunsValid (rowContext 5 (32+k)) 0 (lookup 5 (32+k)):=by decide +kernel
theorem r5part40:∀ k ∈ List.range 8,RunsValid (rowContext 5 (40+k)) 0 (lookup 5 (40+k)):=by decide +kernel
theorem r5part48:∀ k ∈ List.range 8,RunsValid (rowContext 5 (48+k)) 0 (lookup 5 (48+k)):=by decide +kernel
theorem r5part56:∀ k ∈ List.range 8,RunsValid (rowContext 5 (56+k)) 0 (lookup 5 (56+k)):=by decide +kernel
theorem r5part64:∀ k ∈ List.range 8,RunsValid (rowContext 5 (64+k)) 0 (lookup 5 (64+k)):=by decide +kernel
theorem r5part72:∀ k ∈ List.range 8,RunsValid (rowContext 5 (72+k)) 0 (lookup 5 (72+k)):=by decide +kernel
theorem r5part80:∀ k ∈ List.range 8,RunsValid (rowContext 5 (80+k)) 0 (lookup 5 (80+k)):=by decide +kernel
theorem r5part88:∀ k ∈ List.range 8,RunsValid (rowContext 5 (88+k)) 0 (lookup 5 (88+k)):=by decide +kernel
theorem r5part96:∀ k ∈ List.range 8,RunsValid (rowContext 5 (96+k)) 0 (lookup 5 (96+k)):=by decide +kernel
theorem r5part104:∀ k ∈ List.range 8,RunsValid (rowContext 5 (104+k)) 0 (lookup 5 (104+k)):=by decide +kernel
theorem r5part112:∀ k ∈ List.range 8,RunsValid (rowContext 5 (112+k)) 0 (lookup 5 (112+k)):=by decide +kernel
theorem r5part120:∀ k ∈ List.range 8,RunsValid (rowContext 5 (120+k)) 0 (lookup 5 (120+k)):=by decide +kernel
theorem r5part128:∀ k ∈ List.range 8,RunsValid (rowContext 5 (128+k)) 0 (lookup 5 (128+k)):=by decide +kernel
theorem r5part136:∀ k ∈ List.range 2,RunsValid (rowContext 5 (136+k)) 0 (lookup 5 (136+k)):=by decide +kernel

theorem checkedR5 (V:ℕ) (hV:V ∈ List.range 138):RunsValid (rowContext 5 V) 0 (lookup 5 V):=by
  have hv:V < 138:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128:V < 136
  · have hp:=r5part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp:=r5part136 (V-136) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 136 ≤ V by omega)] using hp

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

theorem r11part0:∀ k ∈ List.range 8,RunsValid (rowContext 11 (0+k)) 0 (lookup 11 (0+k)):=by decide +kernel
theorem r11part8:∀ k ∈ List.range 8,RunsValid (rowContext 11 (8+k)) 0 (lookup 11 (8+k)):=by decide +kernel
theorem r11part16:∀ k ∈ List.range 8,RunsValid (rowContext 11 (16+k)) 0 (lookup 11 (16+k)):=by decide +kernel
theorem r11part24:∀ k ∈ List.range 8,RunsValid (rowContext 11 (24+k)) 0 (lookup 11 (24+k)):=by decide +kernel
theorem r11part32:∀ k ∈ List.range 8,RunsValid (rowContext 11 (32+k)) 0 (lookup 11 (32+k)):=by decide +kernel
theorem r11part40:∀ k ∈ List.range 8,RunsValid (rowContext 11 (40+k)) 0 (lookup 11 (40+k)):=by decide +kernel
theorem r11part48:∀ k ∈ List.range 8,RunsValid (rowContext 11 (48+k)) 0 (lookup 11 (48+k)):=by decide +kernel
theorem r11part56:∀ k ∈ List.range 8,RunsValid (rowContext 11 (56+k)) 0 (lookup 11 (56+k)):=by decide +kernel
theorem r11part64:∀ k ∈ List.range 8,RunsValid (rowContext 11 (64+k)) 0 (lookup 11 (64+k)):=by decide +kernel
theorem r11part72:∀ k ∈ List.range 8,RunsValid (rowContext 11 (72+k)) 0 (lookup 11 (72+k)):=by decide +kernel
theorem r11part80:∀ k ∈ List.range 8,RunsValid (rowContext 11 (80+k)) 0 (lookup 11 (80+k)):=by decide +kernel
theorem r11part88:∀ k ∈ List.range 8,RunsValid (rowContext 11 (88+k)) 0 (lookup 11 (88+k)):=by decide +kernel
theorem r11part96:∀ k ∈ List.range 8,RunsValid (rowContext 11 (96+k)) 0 (lookup 11 (96+k)):=by decide +kernel
theorem r11part104:∀ k ∈ List.range 8,RunsValid (rowContext 11 (104+k)) 0 (lookup 11 (104+k)):=by decide +kernel
theorem r11part112:∀ k ∈ List.range 8,RunsValid (rowContext 11 (112+k)) 0 (lookup 11 (112+k)):=by decide +kernel
theorem r11part120:∀ k ∈ List.range 8,RunsValid (rowContext 11 (120+k)) 0 (lookup 11 (120+k)):=by decide +kernel
theorem r11part128:∀ k ∈ List.range 4,RunsValid (rowContext 11 (128+k)) 0 (lookup 11 (128+k)):=by decide +kernel

theorem checkedR11 (V:ℕ) (hV:V ∈ List.range 132):RunsValid (rowContext 11 V) 0 (lookup 11 V):=by
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r11part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r11part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r11part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r11part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r11part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r11part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r11part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r11part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r11part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r11part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r11part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r11part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r11part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r11part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r11part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r11part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r11part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r12part0:∀ k ∈ List.range 8,RunsValid (rowContext 12 (0+k)) 0 (lookup 12 (0+k)):=by decide +kernel
theorem r12part8:∀ k ∈ List.range 8,RunsValid (rowContext 12 (8+k)) 0 (lookup 12 (8+k)):=by decide +kernel
theorem r12part16:∀ k ∈ List.range 8,RunsValid (rowContext 12 (16+k)) 0 (lookup 12 (16+k)):=by decide +kernel
theorem r12part24:∀ k ∈ List.range 8,RunsValid (rowContext 12 (24+k)) 0 (lookup 12 (24+k)):=by decide +kernel
theorem r12part32:∀ k ∈ List.range 8,RunsValid (rowContext 12 (32+k)) 0 (lookup 12 (32+k)):=by decide +kernel
theorem r12part40:∀ k ∈ List.range 8,RunsValid (rowContext 12 (40+k)) 0 (lookup 12 (40+k)):=by decide +kernel
theorem r12part48:∀ k ∈ List.range 8,RunsValid (rowContext 12 (48+k)) 0 (lookup 12 (48+k)):=by decide +kernel
theorem r12part56:∀ k ∈ List.range 8,RunsValid (rowContext 12 (56+k)) 0 (lookup 12 (56+k)):=by decide +kernel
theorem r12part64:∀ k ∈ List.range 8,RunsValid (rowContext 12 (64+k)) 0 (lookup 12 (64+k)):=by decide +kernel
theorem r12part72:∀ k ∈ List.range 8,RunsValid (rowContext 12 (72+k)) 0 (lookup 12 (72+k)):=by decide +kernel
theorem r12part80:∀ k ∈ List.range 8,RunsValid (rowContext 12 (80+k)) 0 (lookup 12 (80+k)):=by decide +kernel
theorem r12part88:∀ k ∈ List.range 8,RunsValid (rowContext 12 (88+k)) 0 (lookup 12 (88+k)):=by decide +kernel
theorem r12part96:∀ k ∈ List.range 8,RunsValid (rowContext 12 (96+k)) 0 (lookup 12 (96+k)):=by decide +kernel
theorem r12part104:∀ k ∈ List.range 8,RunsValid (rowContext 12 (104+k)) 0 (lookup 12 (104+k)):=by decide +kernel
theorem r12part112:∀ k ∈ List.range 8,RunsValid (rowContext 12 (112+k)) 0 (lookup 12 (112+k)):=by decide +kernel
theorem r12part120:∀ k ∈ List.range 8,RunsValid (rowContext 12 (120+k)) 0 (lookup 12 (120+k)):=by decide +kernel
theorem r12part128:∀ k ∈ List.range 3,RunsValid (rowContext 12 (128+k)) 0 (lookup 12 (128+k)):=by decide +kernel

theorem checkedR12 (V:ℕ) (hV:V ∈ List.range 131):RunsValid (rowContext 12 V) 0 (lookup 12 V):=by
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r12part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r12part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r12part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r12part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r12part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r12part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r12part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r12part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r12part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r12part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r12part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r12part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r12part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r12part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r12part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r12part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r12part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r13part0:∀ k ∈ List.range 8,RunsValid (rowContext 13 (0+k)) 0 (lookup 13 (0+k)):=by decide +kernel
theorem r13part8:∀ k ∈ List.range 8,RunsValid (rowContext 13 (8+k)) 0 (lookup 13 (8+k)):=by decide +kernel
theorem r13part16:∀ k ∈ List.range 8,RunsValid (rowContext 13 (16+k)) 0 (lookup 13 (16+k)):=by decide +kernel
theorem r13part24:∀ k ∈ List.range 8,RunsValid (rowContext 13 (24+k)) 0 (lookup 13 (24+k)):=by decide +kernel
theorem r13part32:∀ k ∈ List.range 8,RunsValid (rowContext 13 (32+k)) 0 (lookup 13 (32+k)):=by decide +kernel
theorem r13part40:∀ k ∈ List.range 8,RunsValid (rowContext 13 (40+k)) 0 (lookup 13 (40+k)):=by decide +kernel
theorem r13part48:∀ k ∈ List.range 8,RunsValid (rowContext 13 (48+k)) 0 (lookup 13 (48+k)):=by decide +kernel
theorem r13part56:∀ k ∈ List.range 8,RunsValid (rowContext 13 (56+k)) 0 (lookup 13 (56+k)):=by decide +kernel
theorem r13part64:∀ k ∈ List.range 8,RunsValid (rowContext 13 (64+k)) 0 (lookup 13 (64+k)):=by decide +kernel
theorem r13part72:∀ k ∈ List.range 8,RunsValid (rowContext 13 (72+k)) 0 (lookup 13 (72+k)):=by decide +kernel
theorem r13part80:∀ k ∈ List.range 8,RunsValid (rowContext 13 (80+k)) 0 (lookup 13 (80+k)):=by decide +kernel
theorem r13part88:∀ k ∈ List.range 8,RunsValid (rowContext 13 (88+k)) 0 (lookup 13 (88+k)):=by decide +kernel
theorem r13part96:∀ k ∈ List.range 8,RunsValid (rowContext 13 (96+k)) 0 (lookup 13 (96+k)):=by decide +kernel
theorem r13part104:∀ k ∈ List.range 8,RunsValid (rowContext 13 (104+k)) 0 (lookup 13 (104+k)):=by decide +kernel
theorem r13part112:∀ k ∈ List.range 8,RunsValid (rowContext 13 (112+k)) 0 (lookup 13 (112+k)):=by decide +kernel
theorem r13part120:∀ k ∈ List.range 8,RunsValid (rowContext 13 (120+k)) 0 (lookup 13 (120+k)):=by decide +kernel
theorem r13part128:∀ k ∈ List.range 2,RunsValid (rowContext 13 (128+k)) 0 (lookup 13 (128+k)):=by decide +kernel

theorem checkedR13 (V:ℕ) (hV:V ∈ List.range 130):RunsValid (rowContext 13 V) 0 (lookup 13 V):=by
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r13part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r13part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r13part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r13part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r13part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r13part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r13part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r13part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r13part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r13part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r13part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r13part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r13part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r13part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r13part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r13part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r13part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r14part0:∀ k ∈ List.range 8,RunsValid (rowContext 14 (0+k)) 0 (lookup 14 (0+k)):=by decide +kernel
theorem r14part8:∀ k ∈ List.range 8,RunsValid (rowContext 14 (8+k)) 0 (lookup 14 (8+k)):=by decide +kernel
theorem r14part16:∀ k ∈ List.range 8,RunsValid (rowContext 14 (16+k)) 0 (lookup 14 (16+k)):=by decide +kernel
theorem r14part24:∀ k ∈ List.range 8,RunsValid (rowContext 14 (24+k)) 0 (lookup 14 (24+k)):=by decide +kernel
theorem r14part32:∀ k ∈ List.range 8,RunsValid (rowContext 14 (32+k)) 0 (lookup 14 (32+k)):=by decide +kernel
theorem r14part40:∀ k ∈ List.range 8,RunsValid (rowContext 14 (40+k)) 0 (lookup 14 (40+k)):=by decide +kernel
theorem r14part48:∀ k ∈ List.range 8,RunsValid (rowContext 14 (48+k)) 0 (lookup 14 (48+k)):=by decide +kernel
theorem r14part56:∀ k ∈ List.range 8,RunsValid (rowContext 14 (56+k)) 0 (lookup 14 (56+k)):=by decide +kernel
theorem r14part64:∀ k ∈ List.range 8,RunsValid (rowContext 14 (64+k)) 0 (lookup 14 (64+k)):=by decide +kernel
theorem r14part72:∀ k ∈ List.range 8,RunsValid (rowContext 14 (72+k)) 0 (lookup 14 (72+k)):=by decide +kernel
theorem r14part80:∀ k ∈ List.range 8,RunsValid (rowContext 14 (80+k)) 0 (lookup 14 (80+k)):=by decide +kernel
theorem r14part88:∀ k ∈ List.range 8,RunsValid (rowContext 14 (88+k)) 0 (lookup 14 (88+k)):=by decide +kernel
theorem r14part96:∀ k ∈ List.range 8,RunsValid (rowContext 14 (96+k)) 0 (lookup 14 (96+k)):=by decide +kernel
theorem r14part104:∀ k ∈ List.range 8,RunsValid (rowContext 14 (104+k)) 0 (lookup 14 (104+k)):=by decide +kernel
theorem r14part112:∀ k ∈ List.range 8,RunsValid (rowContext 14 (112+k)) 0 (lookup 14 (112+k)):=by decide +kernel
theorem r14part120:∀ k ∈ List.range 8,RunsValid (rowContext 14 (120+k)) 0 (lookup 14 (120+k)):=by decide +kernel
theorem r14part128:∀ k ∈ List.range 1,RunsValid (rowContext 14 (128+k)) 0 (lookup 14 (128+k)):=by decide +kernel

theorem checkedR14 (V:ℕ) (hV:V ∈ List.range 129):RunsValid (rowContext 14 V) 0 (lookup 14 V):=by
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r14part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r14part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r14part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r14part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r14part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r14part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r14part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r14part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r14part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r14part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r14part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r14part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r14part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r14part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r14part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120:V < 128
  · have hp:=r14part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp:=r14part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

theorem r15part0:∀ k ∈ List.range 8,RunsValid (rowContext 15 (0+k)) 0 (lookup 15 (0+k)):=by decide +kernel
theorem r15part8:∀ k ∈ List.range 8,RunsValid (rowContext 15 (8+k)) 0 (lookup 15 (8+k)):=by decide +kernel
theorem r15part16:∀ k ∈ List.range 8,RunsValid (rowContext 15 (16+k)) 0 (lookup 15 (16+k)):=by decide +kernel
theorem r15part24:∀ k ∈ List.range 8,RunsValid (rowContext 15 (24+k)) 0 (lookup 15 (24+k)):=by decide +kernel
theorem r15part32:∀ k ∈ List.range 8,RunsValid (rowContext 15 (32+k)) 0 (lookup 15 (32+k)):=by decide +kernel
theorem r15part40:∀ k ∈ List.range 8,RunsValid (rowContext 15 (40+k)) 0 (lookup 15 (40+k)):=by decide +kernel
theorem r15part48:∀ k ∈ List.range 8,RunsValid (rowContext 15 (48+k)) 0 (lookup 15 (48+k)):=by decide +kernel
theorem r15part56:∀ k ∈ List.range 8,RunsValid (rowContext 15 (56+k)) 0 (lookup 15 (56+k)):=by decide +kernel
theorem r15part64:∀ k ∈ List.range 8,RunsValid (rowContext 15 (64+k)) 0 (lookup 15 (64+k)):=by decide +kernel
theorem r15part72:∀ k ∈ List.range 8,RunsValid (rowContext 15 (72+k)) 0 (lookup 15 (72+k)):=by decide +kernel
theorem r15part80:∀ k ∈ List.range 8,RunsValid (rowContext 15 (80+k)) 0 (lookup 15 (80+k)):=by decide +kernel
theorem r15part88:∀ k ∈ List.range 8,RunsValid (rowContext 15 (88+k)) 0 (lookup 15 (88+k)):=by decide +kernel
theorem r15part96:∀ k ∈ List.range 8,RunsValid (rowContext 15 (96+k)) 0 (lookup 15 (96+k)):=by decide +kernel
theorem r15part104:∀ k ∈ List.range 8,RunsValid (rowContext 15 (104+k)) 0 (lookup 15 (104+k)):=by decide +kernel
theorem r15part112:∀ k ∈ List.range 8,RunsValid (rowContext 15 (112+k)) 0 (lookup 15 (112+k)):=by decide +kernel
theorem r15part120:∀ k ∈ List.range 8,RunsValid (rowContext 15 (120+k)) 0 (lookup 15 (120+k)):=by decide +kernel

theorem checkedR15 (V:ℕ) (hV:V ∈ List.range 128):RunsValid (rowContext 15 V) 0 (lookup 15 V):=by
  have hv:V < 128:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r15part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r15part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r15part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r15part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r15part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r15part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r15part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r15part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r15part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r15part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r15part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r15part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r15part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r15part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r15part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r15part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r16part0:∀ k ∈ List.range 8,RunsValid (rowContext 16 (0+k)) 0 (lookup 16 (0+k)):=by decide +kernel
theorem r16part8:∀ k ∈ List.range 8,RunsValid (rowContext 16 (8+k)) 0 (lookup 16 (8+k)):=by decide +kernel
theorem r16part16:∀ k ∈ List.range 8,RunsValid (rowContext 16 (16+k)) 0 (lookup 16 (16+k)):=by decide +kernel
theorem r16part24:∀ k ∈ List.range 8,RunsValid (rowContext 16 (24+k)) 0 (lookup 16 (24+k)):=by decide +kernel
theorem r16part32:∀ k ∈ List.range 8,RunsValid (rowContext 16 (32+k)) 0 (lookup 16 (32+k)):=by decide +kernel
theorem r16part40:∀ k ∈ List.range 8,RunsValid (rowContext 16 (40+k)) 0 (lookup 16 (40+k)):=by decide +kernel
theorem r16part48:∀ k ∈ List.range 8,RunsValid (rowContext 16 (48+k)) 0 (lookup 16 (48+k)):=by decide +kernel
theorem r16part56:∀ k ∈ List.range 8,RunsValid (rowContext 16 (56+k)) 0 (lookup 16 (56+k)):=by decide +kernel
theorem r16part64:∀ k ∈ List.range 8,RunsValid (rowContext 16 (64+k)) 0 (lookup 16 (64+k)):=by decide +kernel
theorem r16part72:∀ k ∈ List.range 8,RunsValid (rowContext 16 (72+k)) 0 (lookup 16 (72+k)):=by decide +kernel
theorem r16part80:∀ k ∈ List.range 8,RunsValid (rowContext 16 (80+k)) 0 (lookup 16 (80+k)):=by decide +kernel
theorem r16part88:∀ k ∈ List.range 8,RunsValid (rowContext 16 (88+k)) 0 (lookup 16 (88+k)):=by decide +kernel
theorem r16part96:∀ k ∈ List.range 8,RunsValid (rowContext 16 (96+k)) 0 (lookup 16 (96+k)):=by decide +kernel
theorem r16part104:∀ k ∈ List.range 8,RunsValid (rowContext 16 (104+k)) 0 (lookup 16 (104+k)):=by decide +kernel
theorem r16part112:∀ k ∈ List.range 8,RunsValid (rowContext 16 (112+k)) 0 (lookup 16 (112+k)):=by decide +kernel
theorem r16part120:∀ k ∈ List.range 7,RunsValid (rowContext 16 (120+k)) 0 (lookup 16 (120+k)):=by decide +kernel

theorem checkedR16 (V:ℕ) (hV:V ∈ List.range 127):RunsValid (rowContext 16 V) 0 (lookup 16 V):=by
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r16part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r16part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r16part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r16part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r16part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r16part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r16part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r16part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r16part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r16part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r16part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r16part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r16part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r16part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r16part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r16part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r17part0:∀ k ∈ List.range 8,RunsValid (rowContext 17 (0+k)) 0 (lookup 17 (0+k)):=by decide +kernel
theorem r17part8:∀ k ∈ List.range 8,RunsValid (rowContext 17 (8+k)) 0 (lookup 17 (8+k)):=by decide +kernel
theorem r17part16:∀ k ∈ List.range 8,RunsValid (rowContext 17 (16+k)) 0 (lookup 17 (16+k)):=by decide +kernel
theorem r17part24:∀ k ∈ List.range 8,RunsValid (rowContext 17 (24+k)) 0 (lookup 17 (24+k)):=by decide +kernel
theorem r17part32:∀ k ∈ List.range 8,RunsValid (rowContext 17 (32+k)) 0 (lookup 17 (32+k)):=by decide +kernel
theorem r17part40:∀ k ∈ List.range 8,RunsValid (rowContext 17 (40+k)) 0 (lookup 17 (40+k)):=by decide +kernel
theorem r17part48:∀ k ∈ List.range 8,RunsValid (rowContext 17 (48+k)) 0 (lookup 17 (48+k)):=by decide +kernel
theorem r17part56:∀ k ∈ List.range 8,RunsValid (rowContext 17 (56+k)) 0 (lookup 17 (56+k)):=by decide +kernel
theorem r17part64:∀ k ∈ List.range 8,RunsValid (rowContext 17 (64+k)) 0 (lookup 17 (64+k)):=by decide +kernel
theorem r17part72:∀ k ∈ List.range 8,RunsValid (rowContext 17 (72+k)) 0 (lookup 17 (72+k)):=by decide +kernel
theorem r17part80:∀ k ∈ List.range 8,RunsValid (rowContext 17 (80+k)) 0 (lookup 17 (80+k)):=by decide +kernel
theorem r17part88:∀ k ∈ List.range 8,RunsValid (rowContext 17 (88+k)) 0 (lookup 17 (88+k)):=by decide +kernel
theorem r17part96:∀ k ∈ List.range 8,RunsValid (rowContext 17 (96+k)) 0 (lookup 17 (96+k)):=by decide +kernel
theorem r17part104:∀ k ∈ List.range 8,RunsValid (rowContext 17 (104+k)) 0 (lookup 17 (104+k)):=by decide +kernel
theorem r17part112:∀ k ∈ List.range 8,RunsValid (rowContext 17 (112+k)) 0 (lookup 17 (112+k)):=by decide +kernel
theorem r17part120:∀ k ∈ List.range 6,RunsValid (rowContext 17 (120+k)) 0 (lookup 17 (120+k)):=by decide +kernel

theorem checkedR17 (V:ℕ) (hV:V ∈ List.range 126):RunsValid (rowContext 17 V) 0 (lookup 17 V):=by
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r17part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r17part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r17part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r17part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r17part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r17part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r17part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r17part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r17part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r17part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r17part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r17part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r17part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r17part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r17part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r17part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r18part0:∀ k ∈ List.range 8,RunsValid (rowContext 18 (0+k)) 0 (lookup 18 (0+k)):=by decide +kernel
theorem r18part8:∀ k ∈ List.range 8,RunsValid (rowContext 18 (8+k)) 0 (lookup 18 (8+k)):=by decide +kernel
theorem r18part16:∀ k ∈ List.range 8,RunsValid (rowContext 18 (16+k)) 0 (lookup 18 (16+k)):=by decide +kernel
theorem r18part24:∀ k ∈ List.range 8,RunsValid (rowContext 18 (24+k)) 0 (lookup 18 (24+k)):=by decide +kernel
theorem r18part32:∀ k ∈ List.range 8,RunsValid (rowContext 18 (32+k)) 0 (lookup 18 (32+k)):=by decide +kernel
theorem r18part40:∀ k ∈ List.range 8,RunsValid (rowContext 18 (40+k)) 0 (lookup 18 (40+k)):=by decide +kernel
theorem r18part48:∀ k ∈ List.range 8,RunsValid (rowContext 18 (48+k)) 0 (lookup 18 (48+k)):=by decide +kernel
theorem r18part56:∀ k ∈ List.range 8,RunsValid (rowContext 18 (56+k)) 0 (lookup 18 (56+k)):=by decide +kernel
theorem r18part64:∀ k ∈ List.range 8,RunsValid (rowContext 18 (64+k)) 0 (lookup 18 (64+k)):=by decide +kernel
theorem r18part72:∀ k ∈ List.range 8,RunsValid (rowContext 18 (72+k)) 0 (lookup 18 (72+k)):=by decide +kernel
theorem r18part80:∀ k ∈ List.range 8,RunsValid (rowContext 18 (80+k)) 0 (lookup 18 (80+k)):=by decide +kernel
theorem r18part88:∀ k ∈ List.range 8,RunsValid (rowContext 18 (88+k)) 0 (lookup 18 (88+k)):=by decide +kernel
theorem r18part96:∀ k ∈ List.range 8,RunsValid (rowContext 18 (96+k)) 0 (lookup 18 (96+k)):=by decide +kernel
theorem r18part104:∀ k ∈ List.range 8,RunsValid (rowContext 18 (104+k)) 0 (lookup 18 (104+k)):=by decide +kernel
theorem r18part112:∀ k ∈ List.range 8,RunsValid (rowContext 18 (112+k)) 0 (lookup 18 (112+k)):=by decide +kernel
theorem r18part120:∀ k ∈ List.range 5,RunsValid (rowContext 18 (120+k)) 0 (lookup 18 (120+k)):=by decide +kernel

theorem checkedR18 (V:ℕ) (hV:V ∈ List.range 125):RunsValid (rowContext 18 V) 0 (lookup 18 V):=by
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r18part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r18part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r18part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r18part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r18part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r18part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r18part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r18part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r18part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r18part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r18part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r18part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r18part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r18part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r18part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r18part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r19part0:∀ k ∈ List.range 8,RunsValid (rowContext 19 (0+k)) 0 (lookup 19 (0+k)):=by decide +kernel
theorem r19part8:∀ k ∈ List.range 8,RunsValid (rowContext 19 (8+k)) 0 (lookup 19 (8+k)):=by decide +kernel
theorem r19part16:∀ k ∈ List.range 8,RunsValid (rowContext 19 (16+k)) 0 (lookup 19 (16+k)):=by decide +kernel
theorem r19part24:∀ k ∈ List.range 8,RunsValid (rowContext 19 (24+k)) 0 (lookup 19 (24+k)):=by decide +kernel
theorem r19part32:∀ k ∈ List.range 8,RunsValid (rowContext 19 (32+k)) 0 (lookup 19 (32+k)):=by decide +kernel
theorem r19part40:∀ k ∈ List.range 8,RunsValid (rowContext 19 (40+k)) 0 (lookup 19 (40+k)):=by decide +kernel
theorem r19part48:∀ k ∈ List.range 8,RunsValid (rowContext 19 (48+k)) 0 (lookup 19 (48+k)):=by decide +kernel
theorem r19part56:∀ k ∈ List.range 8,RunsValid (rowContext 19 (56+k)) 0 (lookup 19 (56+k)):=by decide +kernel
theorem r19part64:∀ k ∈ List.range 8,RunsValid (rowContext 19 (64+k)) 0 (lookup 19 (64+k)):=by decide +kernel
theorem r19part72:∀ k ∈ List.range 8,RunsValid (rowContext 19 (72+k)) 0 (lookup 19 (72+k)):=by decide +kernel
theorem r19part80:∀ k ∈ List.range 8,RunsValid (rowContext 19 (80+k)) 0 (lookup 19 (80+k)):=by decide +kernel
theorem r19part88:∀ k ∈ List.range 8,RunsValid (rowContext 19 (88+k)) 0 (lookup 19 (88+k)):=by decide +kernel
theorem r19part96:∀ k ∈ List.range 8,RunsValid (rowContext 19 (96+k)) 0 (lookup 19 (96+k)):=by decide +kernel
theorem r19part104:∀ k ∈ List.range 8,RunsValid (rowContext 19 (104+k)) 0 (lookup 19 (104+k)):=by decide +kernel
theorem r19part112:∀ k ∈ List.range 8,RunsValid (rowContext 19 (112+k)) 0 (lookup 19 (112+k)):=by decide +kernel
theorem r19part120:∀ k ∈ List.range 4,RunsValid (rowContext 19 (120+k)) 0 (lookup 19 (120+k)):=by decide +kernel

theorem checkedR19 (V:ℕ) (hV:V ∈ List.range 124):RunsValid (rowContext 19 V) 0 (lookup 19 V):=by
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r19part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r19part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r19part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r19part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r19part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r19part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r19part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r19part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r19part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r19part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r19part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r19part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r19part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r19part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r19part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r19part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r20part0:∀ k ∈ List.range 8,RunsValid (rowContext 20 (0+k)) 0 (lookup 20 (0+k)):=by decide +kernel
theorem r20part8:∀ k ∈ List.range 8,RunsValid (rowContext 20 (8+k)) 0 (lookup 20 (8+k)):=by decide +kernel
theorem r20part16:∀ k ∈ List.range 8,RunsValid (rowContext 20 (16+k)) 0 (lookup 20 (16+k)):=by decide +kernel
theorem r20part24:∀ k ∈ List.range 8,RunsValid (rowContext 20 (24+k)) 0 (lookup 20 (24+k)):=by decide +kernel
theorem r20part32:∀ k ∈ List.range 8,RunsValid (rowContext 20 (32+k)) 0 (lookup 20 (32+k)):=by decide +kernel
theorem r20part40:∀ k ∈ List.range 8,RunsValid (rowContext 20 (40+k)) 0 (lookup 20 (40+k)):=by decide +kernel
theorem r20part48:∀ k ∈ List.range 8,RunsValid (rowContext 20 (48+k)) 0 (lookup 20 (48+k)):=by decide +kernel
theorem r20part56:∀ k ∈ List.range 8,RunsValid (rowContext 20 (56+k)) 0 (lookup 20 (56+k)):=by decide +kernel
theorem r20part64:∀ k ∈ List.range 8,RunsValid (rowContext 20 (64+k)) 0 (lookup 20 (64+k)):=by decide +kernel
theorem r20part72:∀ k ∈ List.range 8,RunsValid (rowContext 20 (72+k)) 0 (lookup 20 (72+k)):=by decide +kernel
theorem r20part80:∀ k ∈ List.range 8,RunsValid (rowContext 20 (80+k)) 0 (lookup 20 (80+k)):=by decide +kernel
theorem r20part88:∀ k ∈ List.range 8,RunsValid (rowContext 20 (88+k)) 0 (lookup 20 (88+k)):=by decide +kernel
theorem r20part96:∀ k ∈ List.range 8,RunsValid (rowContext 20 (96+k)) 0 (lookup 20 (96+k)):=by decide +kernel
theorem r20part104:∀ k ∈ List.range 8,RunsValid (rowContext 20 (104+k)) 0 (lookup 20 (104+k)):=by decide +kernel
theorem r20part112:∀ k ∈ List.range 8,RunsValid (rowContext 20 (112+k)) 0 (lookup 20 (112+k)):=by decide +kernel
theorem r20part120:∀ k ∈ List.range 3,RunsValid (rowContext 20 (120+k)) 0 (lookup 20 (120+k)):=by decide +kernel

theorem checkedR20 (V:ℕ) (hV:V ∈ List.range 123):RunsValid (rowContext 20 V) 0 (lookup 20 V):=by
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r20part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r20part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r20part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r20part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r20part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r20part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r20part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r20part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r20part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r20part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r20part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r20part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r20part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r20part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r20part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r20part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r21part0:∀ k ∈ List.range 8,RunsValid (rowContext 21 (0+k)) 0 (lookup 21 (0+k)):=by decide +kernel
theorem r21part8:∀ k ∈ List.range 8,RunsValid (rowContext 21 (8+k)) 0 (lookup 21 (8+k)):=by decide +kernel
theorem r21part16:∀ k ∈ List.range 8,RunsValid (rowContext 21 (16+k)) 0 (lookup 21 (16+k)):=by decide +kernel
theorem r21part24:∀ k ∈ List.range 8,RunsValid (rowContext 21 (24+k)) 0 (lookup 21 (24+k)):=by decide +kernel
theorem r21part32:∀ k ∈ List.range 8,RunsValid (rowContext 21 (32+k)) 0 (lookup 21 (32+k)):=by decide +kernel
theorem r21part40:∀ k ∈ List.range 8,RunsValid (rowContext 21 (40+k)) 0 (lookup 21 (40+k)):=by decide +kernel
theorem r21part48:∀ k ∈ List.range 8,RunsValid (rowContext 21 (48+k)) 0 (lookup 21 (48+k)):=by decide +kernel
theorem r21part56:∀ k ∈ List.range 8,RunsValid (rowContext 21 (56+k)) 0 (lookup 21 (56+k)):=by decide +kernel
theorem r21part64:∀ k ∈ List.range 8,RunsValid (rowContext 21 (64+k)) 0 (lookup 21 (64+k)):=by decide +kernel
theorem r21part72:∀ k ∈ List.range 8,RunsValid (rowContext 21 (72+k)) 0 (lookup 21 (72+k)):=by decide +kernel
theorem r21part80:∀ k ∈ List.range 8,RunsValid (rowContext 21 (80+k)) 0 (lookup 21 (80+k)):=by decide +kernel
theorem r21part88:∀ k ∈ List.range 8,RunsValid (rowContext 21 (88+k)) 0 (lookup 21 (88+k)):=by decide +kernel
theorem r21part96:∀ k ∈ List.range 8,RunsValid (rowContext 21 (96+k)) 0 (lookup 21 (96+k)):=by decide +kernel
theorem r21part104:∀ k ∈ List.range 8,RunsValid (rowContext 21 (104+k)) 0 (lookup 21 (104+k)):=by decide +kernel
theorem r21part112:∀ k ∈ List.range 8,RunsValid (rowContext 21 (112+k)) 0 (lookup 21 (112+k)):=by decide +kernel
theorem r21part120:∀ k ∈ List.range 2,RunsValid (rowContext 21 (120+k)) 0 (lookup 21 (120+k)):=by decide +kernel

theorem checkedR21 (V:ℕ) (hV:V ∈ List.range 122):RunsValid (rowContext 21 V) 0 (lookup 21 V):=by
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r21part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r21part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r22part0:∀ k ∈ List.range 8,RunsValid (rowContext 22 (0+k)) 0 (lookup 22 (0+k)):=by decide +kernel
theorem r22part8:∀ k ∈ List.range 8,RunsValid (rowContext 22 (8+k)) 0 (lookup 22 (8+k)):=by decide +kernel
theorem r22part16:∀ k ∈ List.range 8,RunsValid (rowContext 22 (16+k)) 0 (lookup 22 (16+k)):=by decide +kernel
theorem r22part24:∀ k ∈ List.range 8,RunsValid (rowContext 22 (24+k)) 0 (lookup 22 (24+k)):=by decide +kernel
theorem r22part32:∀ k ∈ List.range 8,RunsValid (rowContext 22 (32+k)) 0 (lookup 22 (32+k)):=by decide +kernel
theorem r22part40:∀ k ∈ List.range 8,RunsValid (rowContext 22 (40+k)) 0 (lookup 22 (40+k)):=by decide +kernel
theorem r22part48:∀ k ∈ List.range 8,RunsValid (rowContext 22 (48+k)) 0 (lookup 22 (48+k)):=by decide +kernel
theorem r22part56:∀ k ∈ List.range 8,RunsValid (rowContext 22 (56+k)) 0 (lookup 22 (56+k)):=by decide +kernel
theorem r22part64:∀ k ∈ List.range 8,RunsValid (rowContext 22 (64+k)) 0 (lookup 22 (64+k)):=by decide +kernel
theorem r22part72:∀ k ∈ List.range 8,RunsValid (rowContext 22 (72+k)) 0 (lookup 22 (72+k)):=by decide +kernel
theorem r22part80:∀ k ∈ List.range 8,RunsValid (rowContext 22 (80+k)) 0 (lookup 22 (80+k)):=by decide +kernel
theorem r22part88:∀ k ∈ List.range 8,RunsValid (rowContext 22 (88+k)) 0 (lookup 22 (88+k)):=by decide +kernel
theorem r22part96:∀ k ∈ List.range 8,RunsValid (rowContext 22 (96+k)) 0 (lookup 22 (96+k)):=by decide +kernel
theorem r22part104:∀ k ∈ List.range 8,RunsValid (rowContext 22 (104+k)) 0 (lookup 22 (104+k)):=by decide +kernel
theorem r22part112:∀ k ∈ List.range 8,RunsValid (rowContext 22 (112+k)) 0 (lookup 22 (112+k)):=by decide +kernel
theorem r22part120:∀ k ∈ List.range 1,RunsValid (rowContext 22 (120+k)) 0 (lookup 22 (120+k)):=by decide +kernel

theorem checkedR22 (V:ℕ) (hV:V ∈ List.range 121):RunsValid (rowContext 22 V) 0 (lookup 22 V):=by
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112:V < 120
  · have hp:=r22part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp:=r22part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

theorem r23part0:∀ k ∈ List.range 8,RunsValid (rowContext 23 (0+k)) 0 (lookup 23 (0+k)):=by decide +kernel
theorem r23part8:∀ k ∈ List.range 8,RunsValid (rowContext 23 (8+k)) 0 (lookup 23 (8+k)):=by decide +kernel
theorem r23part16:∀ k ∈ List.range 8,RunsValid (rowContext 23 (16+k)) 0 (lookup 23 (16+k)):=by decide +kernel
theorem r23part24:∀ k ∈ List.range 8,RunsValid (rowContext 23 (24+k)) 0 (lookup 23 (24+k)):=by decide +kernel
theorem r23part32:∀ k ∈ List.range 8,RunsValid (rowContext 23 (32+k)) 0 (lookup 23 (32+k)):=by decide +kernel
theorem r23part40:∀ k ∈ List.range 8,RunsValid (rowContext 23 (40+k)) 0 (lookup 23 (40+k)):=by decide +kernel
theorem r23part48:∀ k ∈ List.range 8,RunsValid (rowContext 23 (48+k)) 0 (lookup 23 (48+k)):=by decide +kernel
theorem r23part56:∀ k ∈ List.range 8,RunsValid (rowContext 23 (56+k)) 0 (lookup 23 (56+k)):=by decide +kernel
theorem r23part64:∀ k ∈ List.range 8,RunsValid (rowContext 23 (64+k)) 0 (lookup 23 (64+k)):=by decide +kernel
theorem r23part72:∀ k ∈ List.range 8,RunsValid (rowContext 23 (72+k)) 0 (lookup 23 (72+k)):=by decide +kernel
theorem r23part80:∀ k ∈ List.range 8,RunsValid (rowContext 23 (80+k)) 0 (lookup 23 (80+k)):=by decide +kernel
theorem r23part88:∀ k ∈ List.range 8,RunsValid (rowContext 23 (88+k)) 0 (lookup 23 (88+k)):=by decide +kernel
theorem r23part96:∀ k ∈ List.range 8,RunsValid (rowContext 23 (96+k)) 0 (lookup 23 (96+k)):=by decide +kernel
theorem r23part104:∀ k ∈ List.range 8,RunsValid (rowContext 23 (104+k)) 0 (lookup 23 (104+k)):=by decide +kernel
theorem r23part112:∀ k ∈ List.range 8,RunsValid (rowContext 23 (112+k)) 0 (lookup 23 (112+k)):=by decide +kernel

theorem checkedR23 (V:ℕ) (hV:V ∈ List.range 120):RunsValid (rowContext 23 V) 0 (lookup 23 V):=by
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r24part0:∀ k ∈ List.range 8,RunsValid (rowContext 24 (0+k)) 0 (lookup 24 (0+k)):=by decide +kernel
theorem r24part8:∀ k ∈ List.range 8,RunsValid (rowContext 24 (8+k)) 0 (lookup 24 (8+k)):=by decide +kernel
theorem r24part16:∀ k ∈ List.range 8,RunsValid (rowContext 24 (16+k)) 0 (lookup 24 (16+k)):=by decide +kernel
theorem r24part24:∀ k ∈ List.range 8,RunsValid (rowContext 24 (24+k)) 0 (lookup 24 (24+k)):=by decide +kernel
theorem r24part32:∀ k ∈ List.range 8,RunsValid (rowContext 24 (32+k)) 0 (lookup 24 (32+k)):=by decide +kernel
theorem r24part40:∀ k ∈ List.range 8,RunsValid (rowContext 24 (40+k)) 0 (lookup 24 (40+k)):=by decide +kernel
theorem r24part48:∀ k ∈ List.range 8,RunsValid (rowContext 24 (48+k)) 0 (lookup 24 (48+k)):=by decide +kernel
theorem r24part56:∀ k ∈ List.range 8,RunsValid (rowContext 24 (56+k)) 0 (lookup 24 (56+k)):=by decide +kernel
theorem r24part64:∀ k ∈ List.range 8,RunsValid (rowContext 24 (64+k)) 0 (lookup 24 (64+k)):=by decide +kernel
theorem r24part72:∀ k ∈ List.range 8,RunsValid (rowContext 24 (72+k)) 0 (lookup 24 (72+k)):=by decide +kernel
theorem r24part80:∀ k ∈ List.range 8,RunsValid (rowContext 24 (80+k)) 0 (lookup 24 (80+k)):=by decide +kernel
theorem r24part88:∀ k ∈ List.range 8,RunsValid (rowContext 24 (88+k)) 0 (lookup 24 (88+k)):=by decide +kernel
theorem r24part96:∀ k ∈ List.range 8,RunsValid (rowContext 24 (96+k)) 0 (lookup 24 (96+k)):=by decide +kernel
theorem r24part104:∀ k ∈ List.range 8,RunsValid (rowContext 24 (104+k)) 0 (lookup 24 (104+k)):=by decide +kernel
theorem r24part112:∀ k ∈ List.range 7,RunsValid (rowContext 24 (112+k)) 0 (lookup 24 (112+k)):=by decide +kernel

theorem checkedR24 (V:ℕ) (hV:V ∈ List.range 119):RunsValid (rowContext 24 V) 0 (lookup 24 V):=by
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r25part0:∀ k ∈ List.range 8,RunsValid (rowContext 25 (0+k)) 0 (lookup 25 (0+k)):=by decide +kernel
theorem r25part8:∀ k ∈ List.range 8,RunsValid (rowContext 25 (8+k)) 0 (lookup 25 (8+k)):=by decide +kernel
theorem r25part16:∀ k ∈ List.range 8,RunsValid (rowContext 25 (16+k)) 0 (lookup 25 (16+k)):=by decide +kernel
theorem r25part24:∀ k ∈ List.range 8,RunsValid (rowContext 25 (24+k)) 0 (lookup 25 (24+k)):=by decide +kernel
theorem r25part32:∀ k ∈ List.range 8,RunsValid (rowContext 25 (32+k)) 0 (lookup 25 (32+k)):=by decide +kernel
theorem r25part40:∀ k ∈ List.range 8,RunsValid (rowContext 25 (40+k)) 0 (lookup 25 (40+k)):=by decide +kernel
theorem r25part48:∀ k ∈ List.range 8,RunsValid (rowContext 25 (48+k)) 0 (lookup 25 (48+k)):=by decide +kernel
theorem r25part56:∀ k ∈ List.range 8,RunsValid (rowContext 25 (56+k)) 0 (lookup 25 (56+k)):=by decide +kernel
theorem r25part64:∀ k ∈ List.range 8,RunsValid (rowContext 25 (64+k)) 0 (lookup 25 (64+k)):=by decide +kernel
theorem r25part72:∀ k ∈ List.range 8,RunsValid (rowContext 25 (72+k)) 0 (lookup 25 (72+k)):=by decide +kernel
theorem r25part80:∀ k ∈ List.range 8,RunsValid (rowContext 25 (80+k)) 0 (lookup 25 (80+k)):=by decide +kernel
theorem r25part88:∀ k ∈ List.range 8,RunsValid (rowContext 25 (88+k)) 0 (lookup 25 (88+k)):=by decide +kernel
theorem r25part96:∀ k ∈ List.range 8,RunsValid (rowContext 25 (96+k)) 0 (lookup 25 (96+k)):=by decide +kernel
theorem r25part104:∀ k ∈ List.range 8,RunsValid (rowContext 25 (104+k)) 0 (lookup 25 (104+k)):=by decide +kernel
theorem r25part112:∀ k ∈ List.range 6,RunsValid (rowContext 25 (112+k)) 0 (lookup 25 (112+k)):=by decide +kernel

theorem checkedR25 (V:ℕ) (hV:V ∈ List.range 118):RunsValid (rowContext 25 V) 0 (lookup 25 V):=by
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r25part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r25part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r26part0:∀ k ∈ List.range 8,RunsValid (rowContext 26 (0+k)) 0 (lookup 26 (0+k)):=by decide +kernel
theorem r26part8:∀ k ∈ List.range 8,RunsValid (rowContext 26 (8+k)) 0 (lookup 26 (8+k)):=by decide +kernel
theorem r26part16:∀ k ∈ List.range 8,RunsValid (rowContext 26 (16+k)) 0 (lookup 26 (16+k)):=by decide +kernel
theorem r26part24:∀ k ∈ List.range 8,RunsValid (rowContext 26 (24+k)) 0 (lookup 26 (24+k)):=by decide +kernel
theorem r26part32:∀ k ∈ List.range 8,RunsValid (rowContext 26 (32+k)) 0 (lookup 26 (32+k)):=by decide +kernel
theorem r26part40:∀ k ∈ List.range 8,RunsValid (rowContext 26 (40+k)) 0 (lookup 26 (40+k)):=by decide +kernel
theorem r26part48:∀ k ∈ List.range 8,RunsValid (rowContext 26 (48+k)) 0 (lookup 26 (48+k)):=by decide +kernel
theorem r26part56:∀ k ∈ List.range 8,RunsValid (rowContext 26 (56+k)) 0 (lookup 26 (56+k)):=by decide +kernel
theorem r26part64:∀ k ∈ List.range 8,RunsValid (rowContext 26 (64+k)) 0 (lookup 26 (64+k)):=by decide +kernel
theorem r26part72:∀ k ∈ List.range 8,RunsValid (rowContext 26 (72+k)) 0 (lookup 26 (72+k)):=by decide +kernel
theorem r26part80:∀ k ∈ List.range 8,RunsValid (rowContext 26 (80+k)) 0 (lookup 26 (80+k)):=by decide +kernel
theorem r26part88:∀ k ∈ List.range 8,RunsValid (rowContext 26 (88+k)) 0 (lookup 26 (88+k)):=by decide +kernel
theorem r26part96:∀ k ∈ List.range 8,RunsValid (rowContext 26 (96+k)) 0 (lookup 26 (96+k)):=by decide +kernel
theorem r26part104:∀ k ∈ List.range 8,RunsValid (rowContext 26 (104+k)) 0 (lookup 26 (104+k)):=by decide +kernel
theorem r26part112:∀ k ∈ List.range 5,RunsValid (rowContext 26 (112+k)) 0 (lookup 26 (112+k)):=by decide +kernel

theorem checkedR26 (V:ℕ) (hV:V ∈ List.range 117):RunsValid (rowContext 26 V) 0 (lookup 26 V):=by
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r26part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r26part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r27part0:∀ k ∈ List.range 8,RunsValid (rowContext 27 (0+k)) 0 (lookup 27 (0+k)):=by decide +kernel
theorem r27part8:∀ k ∈ List.range 8,RunsValid (rowContext 27 (8+k)) 0 (lookup 27 (8+k)):=by decide +kernel
theorem r27part16:∀ k ∈ List.range 8,RunsValid (rowContext 27 (16+k)) 0 (lookup 27 (16+k)):=by decide +kernel
theorem r27part24:∀ k ∈ List.range 8,RunsValid (rowContext 27 (24+k)) 0 (lookup 27 (24+k)):=by decide +kernel
theorem r27part32:∀ k ∈ List.range 8,RunsValid (rowContext 27 (32+k)) 0 (lookup 27 (32+k)):=by decide +kernel
theorem r27part40:∀ k ∈ List.range 8,RunsValid (rowContext 27 (40+k)) 0 (lookup 27 (40+k)):=by decide +kernel
theorem r27part48:∀ k ∈ List.range 8,RunsValid (rowContext 27 (48+k)) 0 (lookup 27 (48+k)):=by decide +kernel
theorem r27part56:∀ k ∈ List.range 8,RunsValid (rowContext 27 (56+k)) 0 (lookup 27 (56+k)):=by decide +kernel
theorem r27part64:∀ k ∈ List.range 8,RunsValid (rowContext 27 (64+k)) 0 (lookup 27 (64+k)):=by decide +kernel
theorem r27part72:∀ k ∈ List.range 8,RunsValid (rowContext 27 (72+k)) 0 (lookup 27 (72+k)):=by decide +kernel
theorem r27part80:∀ k ∈ List.range 8,RunsValid (rowContext 27 (80+k)) 0 (lookup 27 (80+k)):=by decide +kernel
theorem r27part88:∀ k ∈ List.range 8,RunsValid (rowContext 27 (88+k)) 0 (lookup 27 (88+k)):=by decide +kernel
theorem r27part96:∀ k ∈ List.range 8,RunsValid (rowContext 27 (96+k)) 0 (lookup 27 (96+k)):=by decide +kernel
theorem r27part104:∀ k ∈ List.range 8,RunsValid (rowContext 27 (104+k)) 0 (lookup 27 (104+k)):=by decide +kernel
theorem r27part112:∀ k ∈ List.range 4,RunsValid (rowContext 27 (112+k)) 0 (lookup 27 (112+k)):=by decide +kernel

theorem checkedR27 (V:ℕ) (hV:V ∈ List.range 116):RunsValid (rowContext 27 V) 0 (lookup 27 V):=by
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r27part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r27part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r28part0:∀ k ∈ List.range 8,RunsValid (rowContext 28 (0+k)) 0 (lookup 28 (0+k)):=by decide +kernel
theorem r28part8:∀ k ∈ List.range 8,RunsValid (rowContext 28 (8+k)) 0 (lookup 28 (8+k)):=by decide +kernel
theorem r28part16:∀ k ∈ List.range 8,RunsValid (rowContext 28 (16+k)) 0 (lookup 28 (16+k)):=by decide +kernel
theorem r28part24:∀ k ∈ List.range 8,RunsValid (rowContext 28 (24+k)) 0 (lookup 28 (24+k)):=by decide +kernel
theorem r28part32:∀ k ∈ List.range 8,RunsValid (rowContext 28 (32+k)) 0 (lookup 28 (32+k)):=by decide +kernel
theorem r28part40:∀ k ∈ List.range 8,RunsValid (rowContext 28 (40+k)) 0 (lookup 28 (40+k)):=by decide +kernel
theorem r28part48:∀ k ∈ List.range 8,RunsValid (rowContext 28 (48+k)) 0 (lookup 28 (48+k)):=by decide +kernel
theorem r28part56:∀ k ∈ List.range 8,RunsValid (rowContext 28 (56+k)) 0 (lookup 28 (56+k)):=by decide +kernel
theorem r28part64:∀ k ∈ List.range 8,RunsValid (rowContext 28 (64+k)) 0 (lookup 28 (64+k)):=by decide +kernel
theorem r28part72:∀ k ∈ List.range 8,RunsValid (rowContext 28 (72+k)) 0 (lookup 28 (72+k)):=by decide +kernel
theorem r28part80:∀ k ∈ List.range 8,RunsValid (rowContext 28 (80+k)) 0 (lookup 28 (80+k)):=by decide +kernel
theorem r28part88:∀ k ∈ List.range 8,RunsValid (rowContext 28 (88+k)) 0 (lookup 28 (88+k)):=by decide +kernel
theorem r28part96:∀ k ∈ List.range 8,RunsValid (rowContext 28 (96+k)) 0 (lookup 28 (96+k)):=by decide +kernel
theorem r28part104:∀ k ∈ List.range 8,RunsValid (rowContext 28 (104+k)) 0 (lookup 28 (104+k)):=by decide +kernel
theorem r28part112:∀ k ∈ List.range 3,RunsValid (rowContext 28 (112+k)) 0 (lookup 28 (112+k)):=by decide +kernel

theorem checkedR28 (V:ℕ) (hV:V ∈ List.range 115):RunsValid (rowContext 28 V) 0 (lookup 28 V):=by
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r28part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r28part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r29part0:∀ k ∈ List.range 8,RunsValid (rowContext 29 (0+k)) 0 (lookup 29 (0+k)):=by decide +kernel
theorem r29part8:∀ k ∈ List.range 8,RunsValid (rowContext 29 (8+k)) 0 (lookup 29 (8+k)):=by decide +kernel
theorem r29part16:∀ k ∈ List.range 8,RunsValid (rowContext 29 (16+k)) 0 (lookup 29 (16+k)):=by decide +kernel
theorem r29part24:∀ k ∈ List.range 8,RunsValid (rowContext 29 (24+k)) 0 (lookup 29 (24+k)):=by decide +kernel
theorem r29part32:∀ k ∈ List.range 8,RunsValid (rowContext 29 (32+k)) 0 (lookup 29 (32+k)):=by decide +kernel
theorem r29part40:∀ k ∈ List.range 8,RunsValid (rowContext 29 (40+k)) 0 (lookup 29 (40+k)):=by decide +kernel
theorem r29part48:∀ k ∈ List.range 8,RunsValid (rowContext 29 (48+k)) 0 (lookup 29 (48+k)):=by decide +kernel
theorem r29part56:∀ k ∈ List.range 8,RunsValid (rowContext 29 (56+k)) 0 (lookup 29 (56+k)):=by decide +kernel
theorem r29part64:∀ k ∈ List.range 8,RunsValid (rowContext 29 (64+k)) 0 (lookup 29 (64+k)):=by decide +kernel
theorem r29part72:∀ k ∈ List.range 8,RunsValid (rowContext 29 (72+k)) 0 (lookup 29 (72+k)):=by decide +kernel
theorem r29part80:∀ k ∈ List.range 8,RunsValid (rowContext 29 (80+k)) 0 (lookup 29 (80+k)):=by decide +kernel
theorem r29part88:∀ k ∈ List.range 8,RunsValid (rowContext 29 (88+k)) 0 (lookup 29 (88+k)):=by decide +kernel
theorem r29part96:∀ k ∈ List.range 8,RunsValid (rowContext 29 (96+k)) 0 (lookup 29 (96+k)):=by decide +kernel
theorem r29part104:∀ k ∈ List.range 8,RunsValid (rowContext 29 (104+k)) 0 (lookup 29 (104+k)):=by decide +kernel
theorem r29part112:∀ k ∈ List.range 2,RunsValid (rowContext 29 (112+k)) 0 (lookup 29 (112+k)):=by decide +kernel

theorem checkedR29 (V:ℕ) (hV:V ∈ List.range 114):RunsValid (rowContext 29 V) 0 (lookup 29 V):=by
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r29part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r29part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

theorem r30part0:∀ k ∈ List.range 8,RunsValid (rowContext 30 (0+k)) 0 (lookup 30 (0+k)):=by decide +kernel
theorem r30part8:∀ k ∈ List.range 8,RunsValid (rowContext 30 (8+k)) 0 (lookup 30 (8+k)):=by decide +kernel
theorem r30part16:∀ k ∈ List.range 8,RunsValid (rowContext 30 (16+k)) 0 (lookup 30 (16+k)):=by decide +kernel
theorem r30part24:∀ k ∈ List.range 8,RunsValid (rowContext 30 (24+k)) 0 (lookup 30 (24+k)):=by decide +kernel
theorem r30part32:∀ k ∈ List.range 8,RunsValid (rowContext 30 (32+k)) 0 (lookup 30 (32+k)):=by decide +kernel
theorem r30part40:∀ k ∈ List.range 8,RunsValid (rowContext 30 (40+k)) 0 (lookup 30 (40+k)):=by decide +kernel
theorem r30part48:∀ k ∈ List.range 8,RunsValid (rowContext 30 (48+k)) 0 (lookup 30 (48+k)):=by decide +kernel
theorem r30part56:∀ k ∈ List.range 8,RunsValid (rowContext 30 (56+k)) 0 (lookup 30 (56+k)):=by decide +kernel
theorem r30part64:∀ k ∈ List.range 8,RunsValid (rowContext 30 (64+k)) 0 (lookup 30 (64+k)):=by decide +kernel
theorem r30part72:∀ k ∈ List.range 8,RunsValid (rowContext 30 (72+k)) 0 (lookup 30 (72+k)):=by decide +kernel
theorem r30part80:∀ k ∈ List.range 8,RunsValid (rowContext 30 (80+k)) 0 (lookup 30 (80+k)):=by decide +kernel
theorem r30part88:∀ k ∈ List.range 8,RunsValid (rowContext 30 (88+k)) 0 (lookup 30 (88+k)):=by decide +kernel
theorem r30part96:∀ k ∈ List.range 8,RunsValid (rowContext 30 (96+k)) 0 (lookup 30 (96+k)):=by decide +kernel
theorem r30part104:∀ k ∈ List.range 8,RunsValid (rowContext 30 (104+k)) 0 (lookup 30 (104+k)):=by decide +kernel
theorem r30part112:∀ k ∈ List.range 1,RunsValid (rowContext 30 (112+k)) 0 (lookup 30 (112+k)):=by decide +kernel

theorem checkedR30 (V:ℕ) (hV:V ∈ List.range 113):RunsValid (rowContext 30 V) 0 (lookup 30 V):=by
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hp:=r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8:V < 16
  · have hp:=r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16:V < 24
  · have hp:=r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24:V < 32
  · have hp:=r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32:V < 40
  · have hp:=r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40:V < 48
  · have hp:=r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48:V < 56
  · have hp:=r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56:V < 64
  · have hp:=r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64:V < 72
  · have hp:=r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72:V < 80
  · have hp:=r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80:V < 88
  · have hp:=r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88:V < 96
  · have hp:=r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96:V < 104
  · have hp:=r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104:V < 112
  · have hp:=r30part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp:=r30part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

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

theorem checked (r v z:ℕ) (hr:1 ≤ r) (hr30:r ≤ 31)
    (hy:r+v ≤ 142) (ht:r+v+z ≤ 7501):
    ledger (rowContext r v) z ≤ bound:=by
  have hv:v ∈ List.range (143-r):=List.mem_range.mpr (by omega)
  have hc:RunsValid (rowContext r v) 0 (lookup r v):=by
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

theorem ledgerReceipt:Assembly.LedgerReceiptSound 274975000000000000:=by
  constructor
  · decide +kernel
  · intro r v z hr hr30 hy ht
    have h:=checked r v z hr hr30 hy ht
    simpa only [Assembly.LedgerReceiptSound,Assembly.combined,LedgerAudit.ledger,LedgerAudit.bound,
      PhaseSemantics.phaseCap,PhaseData.rowContext,middle,total,rawFlag,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
