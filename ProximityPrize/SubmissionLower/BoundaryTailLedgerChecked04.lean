import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked03

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

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

end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
