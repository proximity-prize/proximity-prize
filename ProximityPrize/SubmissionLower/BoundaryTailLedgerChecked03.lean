import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked02

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

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

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
