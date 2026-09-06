import ProximityPrize.SubmissionLower.LowerAssembly

section Compact_RunsChecked80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.RunsChecked
open Lower80791.PhaseRows Lower80791.PhaseData
open Lower80791.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open Lower80791.PhaseChecks

private theorem r1part0 : ∀ i ∈ List.range 4, RunsAt 1 (0+i) := by decide +kernel

private theorem r1part4 : ∀ i ∈ List.range 4, RunsAt 1 (4+i) := by decide +kernel

private theorem r1part8 : ∀ i ∈ List.range 4, RunsAt 1 (8+i) := by decide +kernel

private theorem r1part12 : ∀ i ∈ List.range 4, RunsAt 1 (12+i) := by decide +kernel

private theorem r1part16 : ∀ i ∈ List.range 4, RunsAt 1 (16+i) := by decide +kernel

private theorem r1part20 : ∀ i ∈ List.range 4, RunsAt 1 (20+i) := by decide +kernel

private theorem r1part24 : ∀ i ∈ List.range 4, RunsAt 1 (24+i) := by decide +kernel

private theorem r1part28 : ∀ i ∈ List.range 4, RunsAt 1 (28+i) := by decide +kernel

private theorem r1part32 : ∀ i ∈ List.range 4, RunsAt 1 (32+i) := by decide +kernel

private theorem r1part36 : ∀ i ∈ List.range 4, RunsAt 1 (36+i) := by decide +kernel

private theorem r1part40 : ∀ i ∈ List.range 4, RunsAt 1 (40+i) := by decide +kernel

private theorem r1part44 : ∀ i ∈ List.range 4, RunsAt 1 (44+i) := by decide +kernel

private theorem r1part48 : ∀ i ∈ List.range 4, RunsAt 1 (48+i) := by decide +kernel

private theorem r1part52 : ∀ i ∈ List.range 4, RunsAt 1 (52+i) := by decide +kernel

private theorem r1part56 : ∀ i ∈ List.range 4, RunsAt 1 (56+i) := by decide +kernel

private theorem r1part60 : ∀ i ∈ List.range 4, RunsAt 1 (60+i) := by decide +kernel

private theorem r1part64 : ∀ i ∈ List.range 4, RunsAt 1 (64+i) := by decide +kernel

private theorem r1part68 : ∀ i ∈ List.range 4, RunsAt 1 (68+i) := by decide +kernel

private theorem r1part72 : ∀ i ∈ List.range 4, RunsAt 1 (72+i) := by decide +kernel

private theorem r1part76 : ∀ i ∈ List.range 4, RunsAt 1 (76+i) := by decide +kernel

private theorem r1part80 : ∀ i ∈ List.range 4, RunsAt 1 (80+i) := by decide +kernel

private theorem r1part84 : ∀ i ∈ List.range 4, RunsAt 1 (84+i) := by decide +kernel

private theorem r1part88 : ∀ i ∈ List.range 4, RunsAt 1 (88+i) := by decide +kernel

private theorem r1part92 : ∀ i ∈ List.range 4, RunsAt 1 (92+i) := by decide +kernel

private theorem r1part96 : ∀ i ∈ List.range 4, RunsAt 1 (96+i) := by decide +kernel

private theorem r1part100 : ∀ i ∈ List.range 4, RunsAt 1 (100+i) := by decide +kernel

private theorem r1part104 : ∀ i ∈ List.range 4, RunsAt 1 (104+i) := by decide +kernel

private theorem r1part108 : ∀ i ∈ List.range 4, RunsAt 1 (108+i) := by decide +kernel

private theorem r1part112 : ∀ i ∈ List.range 4, RunsAt 1 (112+i) := by decide +kernel

private theorem r1part116 : ∀ i ∈ List.range 4, RunsAt 1 (116+i) := by decide +kernel

private theorem r1part120 : ∀ i ∈ List.range 4, RunsAt 1 (120+i) := by decide +kernel

private theorem r1part124 : ∀ i ∈ List.range 4, RunsAt 1 (124+i) := by decide +kernel

private theorem r1part128 : ∀ i ∈ List.range 4, RunsAt 1 (128+i) := by decide +kernel

private theorem r1part132 : ∀ i ∈ List.range 4, RunsAt 1 (132+i) := by decide +kernel

theorem checkedR1 : ∀ V ∈ List.range 136, RunsAt 1 V := by
  intro V hV
  have hlt : V < 136 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r1part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r1part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r1part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r1part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r1part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r1part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r1part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r1part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r1part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r1part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r1part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r1part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r1part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r1part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r1part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r1part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r1part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r1part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r2part0 : ∀ i ∈ List.range 4, RunsAt 2 (0+i) := by decide +kernel

private theorem r2part4 : ∀ i ∈ List.range 4, RunsAt 2 (4+i) := by decide +kernel

private theorem r2part8 : ∀ i ∈ List.range 4, RunsAt 2 (8+i) := by decide +kernel

private theorem r2part12 : ∀ i ∈ List.range 4, RunsAt 2 (12+i) := by decide +kernel

private theorem r2part16 : ∀ i ∈ List.range 4, RunsAt 2 (16+i) := by decide +kernel

private theorem r2part20 : ∀ i ∈ List.range 4, RunsAt 2 (20+i) := by decide +kernel

private theorem r2part24 : ∀ i ∈ List.range 4, RunsAt 2 (24+i) := by decide +kernel

private theorem r2part28 : ∀ i ∈ List.range 4, RunsAt 2 (28+i) := by decide +kernel

private theorem r2part32 : ∀ i ∈ List.range 4, RunsAt 2 (32+i) := by decide +kernel

private theorem r2part36 : ∀ i ∈ List.range 4, RunsAt 2 (36+i) := by decide +kernel

private theorem r2part40 : ∀ i ∈ List.range 4, RunsAt 2 (40+i) := by decide +kernel

private theorem r2part44 : ∀ i ∈ List.range 4, RunsAt 2 (44+i) := by decide +kernel

private theorem r2part48 : ∀ i ∈ List.range 4, RunsAt 2 (48+i) := by decide +kernel

private theorem r2part52 : ∀ i ∈ List.range 4, RunsAt 2 (52+i) := by decide +kernel

private theorem r2part56 : ∀ i ∈ List.range 4, RunsAt 2 (56+i) := by decide +kernel

private theorem r2part60 : ∀ i ∈ List.range 4, RunsAt 2 (60+i) := by decide +kernel

private theorem r2part64 : ∀ i ∈ List.range 4, RunsAt 2 (64+i) := by decide +kernel

private theorem r2part68 : ∀ i ∈ List.range 4, RunsAt 2 (68+i) := by decide +kernel

private theorem r2part72 : ∀ i ∈ List.range 4, RunsAt 2 (72+i) := by decide +kernel

private theorem r2part76 : ∀ i ∈ List.range 4, RunsAt 2 (76+i) := by decide +kernel

private theorem r2part80 : ∀ i ∈ List.range 4, RunsAt 2 (80+i) := by decide +kernel

private theorem r2part84 : ∀ i ∈ List.range 4, RunsAt 2 (84+i) := by decide +kernel

private theorem r2part88 : ∀ i ∈ List.range 4, RunsAt 2 (88+i) := by decide +kernel

private theorem r2part92 : ∀ i ∈ List.range 4, RunsAt 2 (92+i) := by decide +kernel

private theorem r2part96 : ∀ i ∈ List.range 4, RunsAt 2 (96+i) := by decide +kernel

private theorem r2part100 : ∀ i ∈ List.range 4, RunsAt 2 (100+i) := by decide +kernel

private theorem r2part104 : ∀ i ∈ List.range 4, RunsAt 2 (104+i) := by decide +kernel

private theorem r2part108 : ∀ i ∈ List.range 4, RunsAt 2 (108+i) := by decide +kernel

private theorem r2part112 : ∀ i ∈ List.range 4, RunsAt 2 (112+i) := by decide +kernel

private theorem r2part116 : ∀ i ∈ List.range 4, RunsAt 2 (116+i) := by decide +kernel

private theorem r2part120 : ∀ i ∈ List.range 4, RunsAt 2 (120+i) := by decide +kernel

private theorem r2part124 : ∀ i ∈ List.range 4, RunsAt 2 (124+i) := by decide +kernel

private theorem r2part128 : ∀ i ∈ List.range 4, RunsAt 2 (128+i) := by decide +kernel

private theorem r2part132 : ∀ i ∈ List.range 3, RunsAt 2 (132+i) := by decide +kernel

theorem checkedR2 : ∀ V ∈ List.range 135, RunsAt 2 V := by
  intro V hV
  have hlt : V < 135 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r2part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r2part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r2part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r2part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r2part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r2part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r2part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r2part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r2part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r2part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r2part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r2part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r2part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r2part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r2part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r2part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r2part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r2part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r3part0 : ∀ i ∈ List.range 4, RunsAt 3 (0+i) := by decide +kernel

private theorem r3part4 : ∀ i ∈ List.range 4, RunsAt 3 (4+i) := by decide +kernel

private theorem r3part8 : ∀ i ∈ List.range 4, RunsAt 3 (8+i) := by decide +kernel

private theorem r3part12 : ∀ i ∈ List.range 4, RunsAt 3 (12+i) := by decide +kernel

private theorem r3part16 : ∀ i ∈ List.range 4, RunsAt 3 (16+i) := by decide +kernel

private theorem r3part20 : ∀ i ∈ List.range 4, RunsAt 3 (20+i) := by decide +kernel

private theorem r3part24 : ∀ i ∈ List.range 4, RunsAt 3 (24+i) := by decide +kernel

private theorem r3part28 : ∀ i ∈ List.range 4, RunsAt 3 (28+i) := by decide +kernel

private theorem r3part32 : ∀ i ∈ List.range 4, RunsAt 3 (32+i) := by decide +kernel

private theorem r3part36 : ∀ i ∈ List.range 4, RunsAt 3 (36+i) := by decide +kernel

private theorem r3part40 : ∀ i ∈ List.range 4, RunsAt 3 (40+i) := by decide +kernel

private theorem r3part44 : ∀ i ∈ List.range 4, RunsAt 3 (44+i) := by decide +kernel

private theorem r3part48 : ∀ i ∈ List.range 4, RunsAt 3 (48+i) := by decide +kernel

private theorem r3part52 : ∀ i ∈ List.range 4, RunsAt 3 (52+i) := by decide +kernel

private theorem r3part56 : ∀ i ∈ List.range 4, RunsAt 3 (56+i) := by decide +kernel

private theorem r3part60 : ∀ i ∈ List.range 4, RunsAt 3 (60+i) := by decide +kernel

private theorem r3part64 : ∀ i ∈ List.range 4, RunsAt 3 (64+i) := by decide +kernel

private theorem r3part68 : ∀ i ∈ List.range 4, RunsAt 3 (68+i) := by decide +kernel

private theorem r3part72 : ∀ i ∈ List.range 4, RunsAt 3 (72+i) := by decide +kernel

private theorem r3part76 : ∀ i ∈ List.range 4, RunsAt 3 (76+i) := by decide +kernel

private theorem r3part80 : ∀ i ∈ List.range 4, RunsAt 3 (80+i) := by decide +kernel

private theorem r3part84 : ∀ i ∈ List.range 4, RunsAt 3 (84+i) := by decide +kernel

private theorem r3part88 : ∀ i ∈ List.range 4, RunsAt 3 (88+i) := by decide +kernel

private theorem r3part92 : ∀ i ∈ List.range 4, RunsAt 3 (92+i) := by decide +kernel

private theorem r3part96 : ∀ i ∈ List.range 4, RunsAt 3 (96+i) := by decide +kernel

private theorem r3part100 : ∀ i ∈ List.range 4, RunsAt 3 (100+i) := by decide +kernel

private theorem r3part104 : ∀ i ∈ List.range 4, RunsAt 3 (104+i) := by decide +kernel

private theorem r3part108 : ∀ i ∈ List.range 4, RunsAt 3 (108+i) := by decide +kernel

private theorem r3part112 : ∀ i ∈ List.range 4, RunsAt 3 (112+i) := by decide +kernel

private theorem r3part116 : ∀ i ∈ List.range 4, RunsAt 3 (116+i) := by decide +kernel

private theorem r3part120 : ∀ i ∈ List.range 4, RunsAt 3 (120+i) := by decide +kernel

private theorem r3part124 : ∀ i ∈ List.range 4, RunsAt 3 (124+i) := by decide +kernel

private theorem r3part128 : ∀ i ∈ List.range 4, RunsAt 3 (128+i) := by decide +kernel

private theorem r3part132 : ∀ i ∈ List.range 2, RunsAt 3 (132+i) := by decide +kernel

theorem checkedR3 : ∀ V ∈ List.range 134, RunsAt 3 V := by
  intro V hV
  have hlt : V < 134 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r3part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r3part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r3part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r3part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r3part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r3part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r3part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r3part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r3part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r3part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r3part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r3part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r3part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r3part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r3part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r3part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r3part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r3part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r4part0 : ∀ i ∈ List.range 4, RunsAt 4 (0+i) := by decide +kernel

private theorem r4part4 : ∀ i ∈ List.range 4, RunsAt 4 (4+i) := by decide +kernel

private theorem r4part8 : ∀ i ∈ List.range 4, RunsAt 4 (8+i) := by decide +kernel

private theorem r4part12 : ∀ i ∈ List.range 4, RunsAt 4 (12+i) := by decide +kernel

private theorem r4part16 : ∀ i ∈ List.range 4, RunsAt 4 (16+i) := by decide +kernel

private theorem r4part20 : ∀ i ∈ List.range 4, RunsAt 4 (20+i) := by decide +kernel

private theorem r4part24 : ∀ i ∈ List.range 4, RunsAt 4 (24+i) := by decide +kernel

private theorem r4part28 : ∀ i ∈ List.range 4, RunsAt 4 (28+i) := by decide +kernel

private theorem r4part32 : ∀ i ∈ List.range 4, RunsAt 4 (32+i) := by decide +kernel

private theorem r4part36 : ∀ i ∈ List.range 4, RunsAt 4 (36+i) := by decide +kernel

private theorem r4part40 : ∀ i ∈ List.range 4, RunsAt 4 (40+i) := by decide +kernel

private theorem r4part44 : ∀ i ∈ List.range 4, RunsAt 4 (44+i) := by decide +kernel

private theorem r4part48 : ∀ i ∈ List.range 4, RunsAt 4 (48+i) := by decide +kernel

private theorem r4part52 : ∀ i ∈ List.range 4, RunsAt 4 (52+i) := by decide +kernel

private theorem r4part56 : ∀ i ∈ List.range 4, RunsAt 4 (56+i) := by decide +kernel

private theorem r4part60 : ∀ i ∈ List.range 4, RunsAt 4 (60+i) := by decide +kernel

private theorem r4part64 : ∀ i ∈ List.range 4, RunsAt 4 (64+i) := by decide +kernel

private theorem r4part68 : ∀ i ∈ List.range 4, RunsAt 4 (68+i) := by decide +kernel

private theorem r4part72 : ∀ i ∈ List.range 4, RunsAt 4 (72+i) := by decide +kernel

private theorem r4part76 : ∀ i ∈ List.range 4, RunsAt 4 (76+i) := by decide +kernel

private theorem r4part80 : ∀ i ∈ List.range 4, RunsAt 4 (80+i) := by decide +kernel

private theorem r4part84 : ∀ i ∈ List.range 4, RunsAt 4 (84+i) := by decide +kernel

private theorem r4part88 : ∀ i ∈ List.range 4, RunsAt 4 (88+i) := by decide +kernel

private theorem r4part92 : ∀ i ∈ List.range 4, RunsAt 4 (92+i) := by decide +kernel

private theorem r4part96 : ∀ i ∈ List.range 4, RunsAt 4 (96+i) := by decide +kernel

private theorem r4part100 : ∀ i ∈ List.range 4, RunsAt 4 (100+i) := by decide +kernel

private theorem r4part104 : ∀ i ∈ List.range 4, RunsAt 4 (104+i) := by decide +kernel

private theorem r4part108 : ∀ i ∈ List.range 4, RunsAt 4 (108+i) := by decide +kernel

private theorem r4part112 : ∀ i ∈ List.range 4, RunsAt 4 (112+i) := by decide +kernel

private theorem r4part116 : ∀ i ∈ List.range 4, RunsAt 4 (116+i) := by decide +kernel

private theorem r4part120 : ∀ i ∈ List.range 4, RunsAt 4 (120+i) := by decide +kernel

private theorem r4part124 : ∀ i ∈ List.range 4, RunsAt 4 (124+i) := by decide +kernel

private theorem r4part128 : ∀ i ∈ List.range 4, RunsAt 4 (128+i) := by decide +kernel

private theorem r4part132 : ∀ i ∈ List.range 1, RunsAt 4 (132+i) := by decide +kernel

theorem checkedR4 : ∀ V ∈ List.range 133, RunsAt 4 V := by
  intro V hV
  have hlt : V < 133 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r4part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r4part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r4part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r4part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r4part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r4part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r4part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r4part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r4part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r4part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r4part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r4part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r4part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r4part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r4part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r4part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r4part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r4part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r5part0 : ∀ i ∈ List.range 4, RunsAt 5 (0+i) := by decide +kernel

private theorem r5part4 : ∀ i ∈ List.range 4, RunsAt 5 (4+i) := by decide +kernel

private theorem r5part8 : ∀ i ∈ List.range 4, RunsAt 5 (8+i) := by decide +kernel

private theorem r5part12 : ∀ i ∈ List.range 4, RunsAt 5 (12+i) := by decide +kernel

private theorem r5part16 : ∀ i ∈ List.range 4, RunsAt 5 (16+i) := by decide +kernel

private theorem r5part20 : ∀ i ∈ List.range 4, RunsAt 5 (20+i) := by decide +kernel

private theorem r5part24 : ∀ i ∈ List.range 4, RunsAt 5 (24+i) := by decide +kernel

private theorem r5part28 : ∀ i ∈ List.range 4, RunsAt 5 (28+i) := by decide +kernel

private theorem r5part32 : ∀ i ∈ List.range 4, RunsAt 5 (32+i) := by decide +kernel

private theorem r5part36 : ∀ i ∈ List.range 4, RunsAt 5 (36+i) := by decide +kernel

private theorem r5part40 : ∀ i ∈ List.range 4, RunsAt 5 (40+i) := by decide +kernel

private theorem r5part44 : ∀ i ∈ List.range 4, RunsAt 5 (44+i) := by decide +kernel

private theorem r5part48 : ∀ i ∈ List.range 4, RunsAt 5 (48+i) := by decide +kernel

private theorem r5part52 : ∀ i ∈ List.range 4, RunsAt 5 (52+i) := by decide +kernel

private theorem r5part56 : ∀ i ∈ List.range 4, RunsAt 5 (56+i) := by decide +kernel

private theorem r5part60 : ∀ i ∈ List.range 4, RunsAt 5 (60+i) := by decide +kernel

private theorem r5part64 : ∀ i ∈ List.range 4, RunsAt 5 (64+i) := by decide +kernel

private theorem r5part68 : ∀ i ∈ List.range 4, RunsAt 5 (68+i) := by decide +kernel

private theorem r5part72 : ∀ i ∈ List.range 4, RunsAt 5 (72+i) := by decide +kernel

private theorem r5part76 : ∀ i ∈ List.range 4, RunsAt 5 (76+i) := by decide +kernel

private theorem r5part80 : ∀ i ∈ List.range 4, RunsAt 5 (80+i) := by decide +kernel

private theorem r5part84 : ∀ i ∈ List.range 4, RunsAt 5 (84+i) := by decide +kernel

private theorem r5part88 : ∀ i ∈ List.range 4, RunsAt 5 (88+i) := by decide +kernel

private theorem r5part92 : ∀ i ∈ List.range 4, RunsAt 5 (92+i) := by decide +kernel

private theorem r5part96 : ∀ i ∈ List.range 4, RunsAt 5 (96+i) := by decide +kernel

private theorem r5part100 : ∀ i ∈ List.range 4, RunsAt 5 (100+i) := by decide +kernel

private theorem r5part104 : ∀ i ∈ List.range 4, RunsAt 5 (104+i) := by decide +kernel

private theorem r5part108 : ∀ i ∈ List.range 4, RunsAt 5 (108+i) := by decide +kernel

private theorem r5part112 : ∀ i ∈ List.range 4, RunsAt 5 (112+i) := by decide +kernel

private theorem r5part116 : ∀ i ∈ List.range 4, RunsAt 5 (116+i) := by decide +kernel

private theorem r5part120 : ∀ i ∈ List.range 4, RunsAt 5 (120+i) := by decide +kernel

private theorem r5part124 : ∀ i ∈ List.range 4, RunsAt 5 (124+i) := by decide +kernel

private theorem r5part128 : ∀ i ∈ List.range 4, RunsAt 5 (128+i) := by decide +kernel

theorem checkedR5 : ∀ V ∈ List.range 132, RunsAt 5 V := by
  intro V hV
  have hlt : V < 132 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r5part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r5part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r5part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r5part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r5part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r5part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r5part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r5part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r5part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r5part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r5part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r5part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r5part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r5part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r5part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r5part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r5part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r6part0 : ∀ i ∈ List.range 4, RunsAt 6 (0+i) := by decide +kernel

private theorem r6part4 : ∀ i ∈ List.range 4, RunsAt 6 (4+i) := by decide +kernel

private theorem r6part8 : ∀ i ∈ List.range 4, RunsAt 6 (8+i) := by decide +kernel

private theorem r6part12 : ∀ i ∈ List.range 4, RunsAt 6 (12+i) := by decide +kernel

private theorem r6part16 : ∀ i ∈ List.range 4, RunsAt 6 (16+i) := by decide +kernel

private theorem r6part20 : ∀ i ∈ List.range 4, RunsAt 6 (20+i) := by decide +kernel

private theorem r6part24 : ∀ i ∈ List.range 4, RunsAt 6 (24+i) := by decide +kernel

private theorem r6part28 : ∀ i ∈ List.range 4, RunsAt 6 (28+i) := by decide +kernel

private theorem r6part32 : ∀ i ∈ List.range 4, RunsAt 6 (32+i) := by decide +kernel

private theorem r6part36 : ∀ i ∈ List.range 4, RunsAt 6 (36+i) := by decide +kernel

private theorem r6part40 : ∀ i ∈ List.range 4, RunsAt 6 (40+i) := by decide +kernel

private theorem r6part44 : ∀ i ∈ List.range 4, RunsAt 6 (44+i) := by decide +kernel

private theorem r6part48 : ∀ i ∈ List.range 4, RunsAt 6 (48+i) := by decide +kernel

private theorem r6part52 : ∀ i ∈ List.range 4, RunsAt 6 (52+i) := by decide +kernel

private theorem r6part56 : ∀ i ∈ List.range 4, RunsAt 6 (56+i) := by decide +kernel

private theorem r6part60 : ∀ i ∈ List.range 4, RunsAt 6 (60+i) := by decide +kernel

private theorem r6part64 : ∀ i ∈ List.range 4, RunsAt 6 (64+i) := by decide +kernel

private theorem r6part68 : ∀ i ∈ List.range 4, RunsAt 6 (68+i) := by decide +kernel

private theorem r6part72 : ∀ i ∈ List.range 4, RunsAt 6 (72+i) := by decide +kernel

private theorem r6part76 : ∀ i ∈ List.range 4, RunsAt 6 (76+i) := by decide +kernel

private theorem r6part80 : ∀ i ∈ List.range 4, RunsAt 6 (80+i) := by decide +kernel

private theorem r6part84 : ∀ i ∈ List.range 4, RunsAt 6 (84+i) := by decide +kernel

private theorem r6part88 : ∀ i ∈ List.range 4, RunsAt 6 (88+i) := by decide +kernel

private theorem r6part92 : ∀ i ∈ List.range 4, RunsAt 6 (92+i) := by decide +kernel

private theorem r6part96 : ∀ i ∈ List.range 4, RunsAt 6 (96+i) := by decide +kernel

private theorem r6part100 : ∀ i ∈ List.range 4, RunsAt 6 (100+i) := by decide +kernel

private theorem r6part104 : ∀ i ∈ List.range 4, RunsAt 6 (104+i) := by decide +kernel

private theorem r6part108 : ∀ i ∈ List.range 4, RunsAt 6 (108+i) := by decide +kernel

private theorem r6part112 : ∀ i ∈ List.range 4, RunsAt 6 (112+i) := by decide +kernel

private theorem r6part116 : ∀ i ∈ List.range 4, RunsAt 6 (116+i) := by decide +kernel

private theorem r6part120 : ∀ i ∈ List.range 4, RunsAt 6 (120+i) := by decide +kernel

private theorem r6part124 : ∀ i ∈ List.range 4, RunsAt 6 (124+i) := by decide +kernel

private theorem r6part128 : ∀ i ∈ List.range 3, RunsAt 6 (128+i) := by decide +kernel

theorem checkedR6 : ∀ V ∈ List.range 131, RunsAt 6 V := by
  intro V hV
  have hlt : V < 131 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r6part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r6part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r6part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r6part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r6part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r6part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r6part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r6part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r6part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r6part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r6part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r6part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r6part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r6part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r6part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r6part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r6part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r6part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r6part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r6part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r6part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r6part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r6part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r6part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r6part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r6part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r6part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r6part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r6part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r6part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r6part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r6part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r6part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r7part0 : ∀ i ∈ List.range 4, RunsAt 7 (0+i) := by decide +kernel

private theorem r7part4 : ∀ i ∈ List.range 4, RunsAt 7 (4+i) := by decide +kernel

private theorem r7part8 : ∀ i ∈ List.range 4, RunsAt 7 (8+i) := by decide +kernel

private theorem r7part12 : ∀ i ∈ List.range 4, RunsAt 7 (12+i) := by decide +kernel

private theorem r7part16 : ∀ i ∈ List.range 4, RunsAt 7 (16+i) := by decide +kernel

private theorem r7part20 : ∀ i ∈ List.range 4, RunsAt 7 (20+i) := by decide +kernel

private theorem r7part24 : ∀ i ∈ List.range 4, RunsAt 7 (24+i) := by decide +kernel

private theorem r7part28 : ∀ i ∈ List.range 4, RunsAt 7 (28+i) := by decide +kernel

private theorem r7part32 : ∀ i ∈ List.range 4, RunsAt 7 (32+i) := by decide +kernel

private theorem r7part36 : ∀ i ∈ List.range 4, RunsAt 7 (36+i) := by decide +kernel

private theorem r7part40 : ∀ i ∈ List.range 4, RunsAt 7 (40+i) := by decide +kernel

private theorem r7part44 : ∀ i ∈ List.range 4, RunsAt 7 (44+i) := by decide +kernel

private theorem r7part48 : ∀ i ∈ List.range 4, RunsAt 7 (48+i) := by decide +kernel

private theorem r7part52 : ∀ i ∈ List.range 4, RunsAt 7 (52+i) := by decide +kernel

private theorem r7part56 : ∀ i ∈ List.range 4, RunsAt 7 (56+i) := by decide +kernel

private theorem r7part60 : ∀ i ∈ List.range 4, RunsAt 7 (60+i) := by decide +kernel

private theorem r7part64 : ∀ i ∈ List.range 4, RunsAt 7 (64+i) := by decide +kernel

private theorem r7part68 : ∀ i ∈ List.range 4, RunsAt 7 (68+i) := by decide +kernel

private theorem r7part72 : ∀ i ∈ List.range 4, RunsAt 7 (72+i) := by decide +kernel

private theorem r7part76 : ∀ i ∈ List.range 4, RunsAt 7 (76+i) := by decide +kernel

private theorem r7part80 : ∀ i ∈ List.range 4, RunsAt 7 (80+i) := by decide +kernel

private theorem r7part84 : ∀ i ∈ List.range 4, RunsAt 7 (84+i) := by decide +kernel

private theorem r7part88 : ∀ i ∈ List.range 4, RunsAt 7 (88+i) := by decide +kernel

private theorem r7part92 : ∀ i ∈ List.range 4, RunsAt 7 (92+i) := by decide +kernel

private theorem r7part96 : ∀ i ∈ List.range 4, RunsAt 7 (96+i) := by decide +kernel

private theorem r7part100 : ∀ i ∈ List.range 4, RunsAt 7 (100+i) := by decide +kernel

private theorem r7part104 : ∀ i ∈ List.range 4, RunsAt 7 (104+i) := by decide +kernel

private theorem r7part108 : ∀ i ∈ List.range 4, RunsAt 7 (108+i) := by decide +kernel

private theorem r7part112 : ∀ i ∈ List.range 4, RunsAt 7 (112+i) := by decide +kernel

private theorem r7part116 : ∀ i ∈ List.range 4, RunsAt 7 (116+i) := by decide +kernel

private theorem r7part120 : ∀ i ∈ List.range 4, RunsAt 7 (120+i) := by decide +kernel

private theorem r7part124 : ∀ i ∈ List.range 4, RunsAt 7 (124+i) := by decide +kernel

private theorem r7part128 : ∀ i ∈ List.range 2, RunsAt 7 (128+i) := by decide +kernel

theorem checkedR7 : ∀ V ∈ List.range 130, RunsAt 7 V := by
  intro V hV
  have hlt : V < 130 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r7part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r7part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r7part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r7part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r7part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r7part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r7part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r7part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r7part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r7part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r7part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r7part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r7part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r7part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r7part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r7part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r7part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r7part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r7part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r7part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r7part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r7part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r7part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r7part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r7part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r7part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r7part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r7part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r7part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r7part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r7part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r7part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r7part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r8part0 : ∀ i ∈ List.range 4, RunsAt 8 (0+i) := by decide +kernel

private theorem r8part4 : ∀ i ∈ List.range 4, RunsAt 8 (4+i) := by decide +kernel

private theorem r8part8 : ∀ i ∈ List.range 4, RunsAt 8 (8+i) := by decide +kernel

private theorem r8part12 : ∀ i ∈ List.range 4, RunsAt 8 (12+i) := by decide +kernel

private theorem r8part16 : ∀ i ∈ List.range 4, RunsAt 8 (16+i) := by decide +kernel

private theorem r8part20 : ∀ i ∈ List.range 4, RunsAt 8 (20+i) := by decide +kernel

private theorem r8part24 : ∀ i ∈ List.range 4, RunsAt 8 (24+i) := by decide +kernel

private theorem r8part28 : ∀ i ∈ List.range 4, RunsAt 8 (28+i) := by decide +kernel

private theorem r8part32 : ∀ i ∈ List.range 4, RunsAt 8 (32+i) := by decide +kernel

private theorem r8part36 : ∀ i ∈ List.range 4, RunsAt 8 (36+i) := by decide +kernel

private theorem r8part40 : ∀ i ∈ List.range 4, RunsAt 8 (40+i) := by decide +kernel

private theorem r8part44 : ∀ i ∈ List.range 4, RunsAt 8 (44+i) := by decide +kernel

private theorem r8part48 : ∀ i ∈ List.range 4, RunsAt 8 (48+i) := by decide +kernel

private theorem r8part52 : ∀ i ∈ List.range 4, RunsAt 8 (52+i) := by decide +kernel

private theorem r8part56 : ∀ i ∈ List.range 4, RunsAt 8 (56+i) := by decide +kernel

private theorem r8part60 : ∀ i ∈ List.range 4, RunsAt 8 (60+i) := by decide +kernel

private theorem r8part64 : ∀ i ∈ List.range 4, RunsAt 8 (64+i) := by decide +kernel

private theorem r8part68 : ∀ i ∈ List.range 4, RunsAt 8 (68+i) := by decide +kernel

private theorem r8part72 : ∀ i ∈ List.range 4, RunsAt 8 (72+i) := by decide +kernel

private theorem r8part76 : ∀ i ∈ List.range 4, RunsAt 8 (76+i) := by decide +kernel

private theorem r8part80 : ∀ i ∈ List.range 4, RunsAt 8 (80+i) := by decide +kernel

private theorem r8part84 : ∀ i ∈ List.range 4, RunsAt 8 (84+i) := by decide +kernel

private theorem r8part88 : ∀ i ∈ List.range 4, RunsAt 8 (88+i) := by decide +kernel

private theorem r8part92 : ∀ i ∈ List.range 4, RunsAt 8 (92+i) := by decide +kernel

private theorem r8part96 : ∀ i ∈ List.range 4, RunsAt 8 (96+i) := by decide +kernel

private theorem r8part100 : ∀ i ∈ List.range 4, RunsAt 8 (100+i) := by decide +kernel

private theorem r8part104 : ∀ i ∈ List.range 4, RunsAt 8 (104+i) := by decide +kernel

private theorem r8part108 : ∀ i ∈ List.range 4, RunsAt 8 (108+i) := by decide +kernel

private theorem r8part112 : ∀ i ∈ List.range 4, RunsAt 8 (112+i) := by decide +kernel

private theorem r8part116 : ∀ i ∈ List.range 4, RunsAt 8 (116+i) := by decide +kernel

private theorem r8part120 : ∀ i ∈ List.range 4, RunsAt 8 (120+i) := by decide +kernel

private theorem r8part124 : ∀ i ∈ List.range 4, RunsAt 8 (124+i) := by decide +kernel

private theorem r8part128 : ∀ i ∈ List.range 1, RunsAt 8 (128+i) := by decide +kernel

theorem checkedR8 : ∀ V ∈ List.range 129, RunsAt 8 V := by
  intro V hV
  have hlt : V < 129 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r8part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r8part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r8part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r8part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r8part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r8part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r8part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r8part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r8part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r8part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r8part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r8part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r8part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r8part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r8part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r8part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r8part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r8part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r8part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r8part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r8part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r8part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r8part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r8part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r8part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r8part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r8part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r8part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r8part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r8part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r8part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r8part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r8part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r9part0 : ∀ i ∈ List.range 4, RunsAt 9 (0+i) := by decide +kernel

private theorem r9part4 : ∀ i ∈ List.range 4, RunsAt 9 (4+i) := by decide +kernel

private theorem r9part8 : ∀ i ∈ List.range 4, RunsAt 9 (8+i) := by decide +kernel

private theorem r9part12 : ∀ i ∈ List.range 4, RunsAt 9 (12+i) := by decide +kernel

private theorem r9part16 : ∀ i ∈ List.range 4, RunsAt 9 (16+i) := by decide +kernel

private theorem r9part20 : ∀ i ∈ List.range 4, RunsAt 9 (20+i) := by decide +kernel

private theorem r9part24 : ∀ i ∈ List.range 4, RunsAt 9 (24+i) := by decide +kernel

private theorem r9part28 : ∀ i ∈ List.range 4, RunsAt 9 (28+i) := by decide +kernel

private theorem r9part32 : ∀ i ∈ List.range 4, RunsAt 9 (32+i) := by decide +kernel

private theorem r9part36 : ∀ i ∈ List.range 4, RunsAt 9 (36+i) := by decide +kernel

private theorem r9part40 : ∀ i ∈ List.range 4, RunsAt 9 (40+i) := by decide +kernel

private theorem r9part44 : ∀ i ∈ List.range 4, RunsAt 9 (44+i) := by decide +kernel

private theorem r9part48 : ∀ i ∈ List.range 4, RunsAt 9 (48+i) := by decide +kernel

private theorem r9part52 : ∀ i ∈ List.range 4, RunsAt 9 (52+i) := by decide +kernel

private theorem r9part56 : ∀ i ∈ List.range 4, RunsAt 9 (56+i) := by decide +kernel

private theorem r9part60 : ∀ i ∈ List.range 4, RunsAt 9 (60+i) := by decide +kernel

private theorem r9part64 : ∀ i ∈ List.range 4, RunsAt 9 (64+i) := by decide +kernel

private theorem r9part68 : ∀ i ∈ List.range 4, RunsAt 9 (68+i) := by decide +kernel

private theorem r9part72 : ∀ i ∈ List.range 4, RunsAt 9 (72+i) := by decide +kernel

private theorem r9part76 : ∀ i ∈ List.range 4, RunsAt 9 (76+i) := by decide +kernel

private theorem r9part80 : ∀ i ∈ List.range 4, RunsAt 9 (80+i) := by decide +kernel

private theorem r9part84 : ∀ i ∈ List.range 4, RunsAt 9 (84+i) := by decide +kernel

private theorem r9part88 : ∀ i ∈ List.range 4, RunsAt 9 (88+i) := by decide +kernel

private theorem r9part92 : ∀ i ∈ List.range 4, RunsAt 9 (92+i) := by decide +kernel

private theorem r9part96 : ∀ i ∈ List.range 4, RunsAt 9 (96+i) := by decide +kernel

private theorem r9part100 : ∀ i ∈ List.range 4, RunsAt 9 (100+i) := by decide +kernel

private theorem r9part104 : ∀ i ∈ List.range 4, RunsAt 9 (104+i) := by decide +kernel

private theorem r9part108 : ∀ i ∈ List.range 4, RunsAt 9 (108+i) := by decide +kernel

private theorem r9part112 : ∀ i ∈ List.range 4, RunsAt 9 (112+i) := by decide +kernel

private theorem r9part116 : ∀ i ∈ List.range 4, RunsAt 9 (116+i) := by decide +kernel

private theorem r9part120 : ∀ i ∈ List.range 4, RunsAt 9 (120+i) := by decide +kernel

private theorem r9part124 : ∀ i ∈ List.range 4, RunsAt 9 (124+i) := by decide +kernel

theorem checkedR9 : ∀ V ∈ List.range 128, RunsAt 9 V := by
  intro V hV
  have hlt : V < 128 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r9part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r9part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r9part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r9part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r9part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r9part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r9part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r9part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r9part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r9part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r9part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r9part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r9part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r9part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r9part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r9part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r9part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r9part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r9part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r9part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r9part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r9part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r9part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r9part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r9part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r9part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r9part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r9part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r9part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r9part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r9part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r9part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r10part0 : ∀ i ∈ List.range 4, RunsAt 10 (0+i) := by decide +kernel

private theorem r10part4 : ∀ i ∈ List.range 4, RunsAt 10 (4+i) := by decide +kernel

private theorem r10part8 : ∀ i ∈ List.range 4, RunsAt 10 (8+i) := by decide +kernel

private theorem r10part12 : ∀ i ∈ List.range 4, RunsAt 10 (12+i) := by decide +kernel

private theorem r10part16 : ∀ i ∈ List.range 4, RunsAt 10 (16+i) := by decide +kernel

private theorem r10part20 : ∀ i ∈ List.range 4, RunsAt 10 (20+i) := by decide +kernel

private theorem r10part24 : ∀ i ∈ List.range 4, RunsAt 10 (24+i) := by decide +kernel

private theorem r10part28 : ∀ i ∈ List.range 4, RunsAt 10 (28+i) := by decide +kernel

private theorem r10part32 : ∀ i ∈ List.range 4, RunsAt 10 (32+i) := by decide +kernel

private theorem r10part36 : ∀ i ∈ List.range 4, RunsAt 10 (36+i) := by decide +kernel

private theorem r10part40 : ∀ i ∈ List.range 4, RunsAt 10 (40+i) := by decide +kernel

private theorem r10part44 : ∀ i ∈ List.range 4, RunsAt 10 (44+i) := by decide +kernel

private theorem r10part48 : ∀ i ∈ List.range 4, RunsAt 10 (48+i) := by decide +kernel

private theorem r10part52 : ∀ i ∈ List.range 4, RunsAt 10 (52+i) := by decide +kernel

private theorem r10part56 : ∀ i ∈ List.range 4, RunsAt 10 (56+i) := by decide +kernel

private theorem r10part60 : ∀ i ∈ List.range 4, RunsAt 10 (60+i) := by decide +kernel

private theorem r10part64 : ∀ i ∈ List.range 4, RunsAt 10 (64+i) := by decide +kernel

private theorem r10part68 : ∀ i ∈ List.range 4, RunsAt 10 (68+i) := by decide +kernel

private theorem r10part72 : ∀ i ∈ List.range 4, RunsAt 10 (72+i) := by decide +kernel

private theorem r10part76 : ∀ i ∈ List.range 4, RunsAt 10 (76+i) := by decide +kernel

private theorem r10part80 : ∀ i ∈ List.range 4, RunsAt 10 (80+i) := by decide +kernel

private theorem r10part84 : ∀ i ∈ List.range 4, RunsAt 10 (84+i) := by decide +kernel

private theorem r10part88 : ∀ i ∈ List.range 4, RunsAt 10 (88+i) := by decide +kernel

private theorem r10part92 : ∀ i ∈ List.range 4, RunsAt 10 (92+i) := by decide +kernel

private theorem r10part96 : ∀ i ∈ List.range 4, RunsAt 10 (96+i) := by decide +kernel

private theorem r10part100 : ∀ i ∈ List.range 4, RunsAt 10 (100+i) := by decide +kernel

private theorem r10part104 : ∀ i ∈ List.range 4, RunsAt 10 (104+i) := by decide +kernel

private theorem r10part108 : ∀ i ∈ List.range 4, RunsAt 10 (108+i) := by decide +kernel

private theorem r10part112 : ∀ i ∈ List.range 4, RunsAt 10 (112+i) := by decide +kernel

private theorem r10part116 : ∀ i ∈ List.range 4, RunsAt 10 (116+i) := by decide +kernel

private theorem r10part120 : ∀ i ∈ List.range 4, RunsAt 10 (120+i) := by decide +kernel

private theorem r10part124 : ∀ i ∈ List.range 3, RunsAt 10 (124+i) := by decide +kernel

theorem checkedR10 : ∀ V ∈ List.range 127, RunsAt 10 V := by
  intro V hV
  have hlt : V < 127 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r10part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r10part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r10part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r10part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r10part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r10part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r10part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r10part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r10part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r10part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r10part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r10part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r10part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r10part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r10part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r10part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r10part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r10part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r10part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r10part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r10part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r10part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r10part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r10part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r10part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r10part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r10part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r10part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r10part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r10part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r10part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r10part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r11part0 : ∀ i ∈ List.range 4, RunsAt 11 (0+i) := by decide +kernel

private theorem r11part4 : ∀ i ∈ List.range 4, RunsAt 11 (4+i) := by decide +kernel

private theorem r11part8 : ∀ i ∈ List.range 4, RunsAt 11 (8+i) := by decide +kernel

private theorem r11part12 : ∀ i ∈ List.range 4, RunsAt 11 (12+i) := by decide +kernel

private theorem r11part16 : ∀ i ∈ List.range 4, RunsAt 11 (16+i) := by decide +kernel

private theorem r11part20 : ∀ i ∈ List.range 4, RunsAt 11 (20+i) := by decide +kernel

private theorem r11part24 : ∀ i ∈ List.range 4, RunsAt 11 (24+i) := by decide +kernel

private theorem r11part28 : ∀ i ∈ List.range 4, RunsAt 11 (28+i) := by decide +kernel

private theorem r11part32 : ∀ i ∈ List.range 4, RunsAt 11 (32+i) := by decide +kernel

private theorem r11part36 : ∀ i ∈ List.range 4, RunsAt 11 (36+i) := by decide +kernel

private theorem r11part40 : ∀ i ∈ List.range 4, RunsAt 11 (40+i) := by decide +kernel

private theorem r11part44 : ∀ i ∈ List.range 4, RunsAt 11 (44+i) := by decide +kernel

private theorem r11part48 : ∀ i ∈ List.range 4, RunsAt 11 (48+i) := by decide +kernel

private theorem r11part52 : ∀ i ∈ List.range 4, RunsAt 11 (52+i) := by decide +kernel

private theorem r11part56 : ∀ i ∈ List.range 4, RunsAt 11 (56+i) := by decide +kernel

private theorem r11part60 : ∀ i ∈ List.range 4, RunsAt 11 (60+i) := by decide +kernel

private theorem r11part64 : ∀ i ∈ List.range 4, RunsAt 11 (64+i) := by decide +kernel

private theorem r11part68 : ∀ i ∈ List.range 4, RunsAt 11 (68+i) := by decide +kernel

private theorem r11part72 : ∀ i ∈ List.range 4, RunsAt 11 (72+i) := by decide +kernel

private theorem r11part76 : ∀ i ∈ List.range 4, RunsAt 11 (76+i) := by decide +kernel

private theorem r11part80 : ∀ i ∈ List.range 4, RunsAt 11 (80+i) := by decide +kernel

private theorem r11part84 : ∀ i ∈ List.range 4, RunsAt 11 (84+i) := by decide +kernel

private theorem r11part88 : ∀ i ∈ List.range 4, RunsAt 11 (88+i) := by decide +kernel

private theorem r11part92 : ∀ i ∈ List.range 4, RunsAt 11 (92+i) := by decide +kernel

private theorem r11part96 : ∀ i ∈ List.range 4, RunsAt 11 (96+i) := by decide +kernel

private theorem r11part100 : ∀ i ∈ List.range 4, RunsAt 11 (100+i) := by decide +kernel

private theorem r11part104 : ∀ i ∈ List.range 4, RunsAt 11 (104+i) := by decide +kernel

private theorem r11part108 : ∀ i ∈ List.range 4, RunsAt 11 (108+i) := by decide +kernel

private theorem r11part112 : ∀ i ∈ List.range 4, RunsAt 11 (112+i) := by decide +kernel

private theorem r11part116 : ∀ i ∈ List.range 4, RunsAt 11 (116+i) := by decide +kernel

private theorem r11part120 : ∀ i ∈ List.range 4, RunsAt 11 (120+i) := by decide +kernel

private theorem r11part124 : ∀ i ∈ List.range 2, RunsAt 11 (124+i) := by decide +kernel

theorem checkedR11 : ∀ V ∈ List.range 126, RunsAt 11 V := by
  intro V hV
  have hlt : V < 126 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r11part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r11part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r11part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r11part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r11part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r11part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r11part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r11part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r11part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r11part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r11part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r11part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r11part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r11part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r11part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r11part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r11part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r11part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r11part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r11part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r11part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r11part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r11part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r11part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r11part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r11part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r11part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r11part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r11part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r11part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r11part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r11part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r12part0 : ∀ i ∈ List.range 4, RunsAt 12 (0+i) := by decide +kernel

private theorem r12part4 : ∀ i ∈ List.range 4, RunsAt 12 (4+i) := by decide +kernel

private theorem r12part8 : ∀ i ∈ List.range 4, RunsAt 12 (8+i) := by decide +kernel

private theorem r12part12 : ∀ i ∈ List.range 4, RunsAt 12 (12+i) := by decide +kernel

private theorem r12part16 : ∀ i ∈ List.range 4, RunsAt 12 (16+i) := by decide +kernel

private theorem r12part20 : ∀ i ∈ List.range 4, RunsAt 12 (20+i) := by decide +kernel

private theorem r12part24 : ∀ i ∈ List.range 4, RunsAt 12 (24+i) := by decide +kernel

private theorem r12part28 : ∀ i ∈ List.range 4, RunsAt 12 (28+i) := by decide +kernel

private theorem r12part32 : ∀ i ∈ List.range 4, RunsAt 12 (32+i) := by decide +kernel

private theorem r12part36 : ∀ i ∈ List.range 4, RunsAt 12 (36+i) := by decide +kernel

private theorem r12part40 : ∀ i ∈ List.range 4, RunsAt 12 (40+i) := by decide +kernel

private theorem r12part44 : ∀ i ∈ List.range 4, RunsAt 12 (44+i) := by decide +kernel

private theorem r12part48 : ∀ i ∈ List.range 4, RunsAt 12 (48+i) := by decide +kernel

private theorem r12part52 : ∀ i ∈ List.range 4, RunsAt 12 (52+i) := by decide +kernel

private theorem r12part56 : ∀ i ∈ List.range 4, RunsAt 12 (56+i) := by decide +kernel

private theorem r12part60 : ∀ i ∈ List.range 4, RunsAt 12 (60+i) := by decide +kernel

private theorem r12part64 : ∀ i ∈ List.range 4, RunsAt 12 (64+i) := by decide +kernel

private theorem r12part68 : ∀ i ∈ List.range 4, RunsAt 12 (68+i) := by decide +kernel

private theorem r12part72 : ∀ i ∈ List.range 4, RunsAt 12 (72+i) := by decide +kernel

private theorem r12part76 : ∀ i ∈ List.range 4, RunsAt 12 (76+i) := by decide +kernel

private theorem r12part80 : ∀ i ∈ List.range 4, RunsAt 12 (80+i) := by decide +kernel

private theorem r12part84 : ∀ i ∈ List.range 4, RunsAt 12 (84+i) := by decide +kernel

private theorem r12part88 : ∀ i ∈ List.range 4, RunsAt 12 (88+i) := by decide +kernel

private theorem r12part92 : ∀ i ∈ List.range 4, RunsAt 12 (92+i) := by decide +kernel

private theorem r12part96 : ∀ i ∈ List.range 4, RunsAt 12 (96+i) := by decide +kernel

private theorem r12part100 : ∀ i ∈ List.range 4, RunsAt 12 (100+i) := by decide +kernel

private theorem r12part104 : ∀ i ∈ List.range 4, RunsAt 12 (104+i) := by decide +kernel

private theorem r12part108 : ∀ i ∈ List.range 4, RunsAt 12 (108+i) := by decide +kernel

private theorem r12part112 : ∀ i ∈ List.range 4, RunsAt 12 (112+i) := by decide +kernel

private theorem r12part116 : ∀ i ∈ List.range 4, RunsAt 12 (116+i) := by decide +kernel

private theorem r12part120 : ∀ i ∈ List.range 4, RunsAt 12 (120+i) := by decide +kernel

private theorem r12part124 : ∀ i ∈ List.range 1, RunsAt 12 (124+i) := by decide +kernel

theorem checkedR12 : ∀ V ∈ List.range 125, RunsAt 12 V := by
  intro V hV
  have hlt : V < 125 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r12part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r12part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r12part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r12part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r12part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r12part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r12part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r12part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r12part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r12part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r12part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r12part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r12part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r12part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r12part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r12part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r12part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r12part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r12part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r12part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r12part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r12part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r12part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r12part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r12part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r12part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r12part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r12part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r12part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r12part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r12part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r12part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r13part0 : ∀ i ∈ List.range 4, RunsAt 13 (0+i) := by decide +kernel

private theorem r13part4 : ∀ i ∈ List.range 4, RunsAt 13 (4+i) := by decide +kernel

private theorem r13part8 : ∀ i ∈ List.range 4, RunsAt 13 (8+i) := by decide +kernel

private theorem r13part12 : ∀ i ∈ List.range 4, RunsAt 13 (12+i) := by decide +kernel

private theorem r13part16 : ∀ i ∈ List.range 4, RunsAt 13 (16+i) := by decide +kernel

private theorem r13part20 : ∀ i ∈ List.range 4, RunsAt 13 (20+i) := by decide +kernel

private theorem r13part24 : ∀ i ∈ List.range 4, RunsAt 13 (24+i) := by decide +kernel

private theorem r13part28 : ∀ i ∈ List.range 4, RunsAt 13 (28+i) := by decide +kernel

private theorem r13part32 : ∀ i ∈ List.range 4, RunsAt 13 (32+i) := by decide +kernel

private theorem r13part36 : ∀ i ∈ List.range 4, RunsAt 13 (36+i) := by decide +kernel

private theorem r13part40 : ∀ i ∈ List.range 4, RunsAt 13 (40+i) := by decide +kernel

private theorem r13part44 : ∀ i ∈ List.range 4, RunsAt 13 (44+i) := by decide +kernel

private theorem r13part48 : ∀ i ∈ List.range 4, RunsAt 13 (48+i) := by decide +kernel

private theorem r13part52 : ∀ i ∈ List.range 4, RunsAt 13 (52+i) := by decide +kernel

private theorem r13part56 : ∀ i ∈ List.range 4, RunsAt 13 (56+i) := by decide +kernel

private theorem r13part60 : ∀ i ∈ List.range 4, RunsAt 13 (60+i) := by decide +kernel

private theorem r13part64 : ∀ i ∈ List.range 4, RunsAt 13 (64+i) := by decide +kernel

private theorem r13part68 : ∀ i ∈ List.range 4, RunsAt 13 (68+i) := by decide +kernel

private theorem r13part72 : ∀ i ∈ List.range 4, RunsAt 13 (72+i) := by decide +kernel

private theorem r13part76 : ∀ i ∈ List.range 4, RunsAt 13 (76+i) := by decide +kernel

private theorem r13part80 : ∀ i ∈ List.range 4, RunsAt 13 (80+i) := by decide +kernel

private theorem r13part84 : ∀ i ∈ List.range 4, RunsAt 13 (84+i) := by decide +kernel

private theorem r13part88 : ∀ i ∈ List.range 4, RunsAt 13 (88+i) := by decide +kernel

private theorem r13part92 : ∀ i ∈ List.range 4, RunsAt 13 (92+i) := by decide +kernel

private theorem r13part96 : ∀ i ∈ List.range 4, RunsAt 13 (96+i) := by decide +kernel

private theorem r13part100 : ∀ i ∈ List.range 4, RunsAt 13 (100+i) := by decide +kernel

private theorem r13part104 : ∀ i ∈ List.range 4, RunsAt 13 (104+i) := by decide +kernel

private theorem r13part108 : ∀ i ∈ List.range 4, RunsAt 13 (108+i) := by decide +kernel

private theorem r13part112 : ∀ i ∈ List.range 4, RunsAt 13 (112+i) := by decide +kernel

private theorem r13part116 : ∀ i ∈ List.range 4, RunsAt 13 (116+i) := by decide +kernel

private theorem r13part120 : ∀ i ∈ List.range 4, RunsAt 13 (120+i) := by decide +kernel

theorem checkedR13 : ∀ V ∈ List.range 124, RunsAt 13 V := by
  intro V hV
  have hlt : V < 124 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r13part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r13part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r13part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r13part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r13part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r13part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r13part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r13part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r13part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r13part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r13part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r13part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r13part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r13part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r13part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r13part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r13part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r13part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r13part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r13part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r13part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r13part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r13part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r13part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r13part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r13part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r13part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r13part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r13part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r13part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r13part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r14part0 : ∀ i ∈ List.range 4, RunsAt 14 (0+i) := by decide +kernel

private theorem r14part4 : ∀ i ∈ List.range 4, RunsAt 14 (4+i) := by decide +kernel

private theorem r14part8 : ∀ i ∈ List.range 4, RunsAt 14 (8+i) := by decide +kernel

private theorem r14part12 : ∀ i ∈ List.range 4, RunsAt 14 (12+i) := by decide +kernel

private theorem r14part16 : ∀ i ∈ List.range 4, RunsAt 14 (16+i) := by decide +kernel

private theorem r14part20 : ∀ i ∈ List.range 4, RunsAt 14 (20+i) := by decide +kernel

private theorem r14part24 : ∀ i ∈ List.range 4, RunsAt 14 (24+i) := by decide +kernel

private theorem r14part28 : ∀ i ∈ List.range 4, RunsAt 14 (28+i) := by decide +kernel

private theorem r14part32 : ∀ i ∈ List.range 4, RunsAt 14 (32+i) := by decide +kernel

private theorem r14part36 : ∀ i ∈ List.range 4, RunsAt 14 (36+i) := by decide +kernel

private theorem r14part40 : ∀ i ∈ List.range 4, RunsAt 14 (40+i) := by decide +kernel

private theorem r14part44 : ∀ i ∈ List.range 4, RunsAt 14 (44+i) := by decide +kernel

private theorem r14part48 : ∀ i ∈ List.range 4, RunsAt 14 (48+i) := by decide +kernel

private theorem r14part52 : ∀ i ∈ List.range 4, RunsAt 14 (52+i) := by decide +kernel

private theorem r14part56 : ∀ i ∈ List.range 4, RunsAt 14 (56+i) := by decide +kernel

private theorem r14part60 : ∀ i ∈ List.range 4, RunsAt 14 (60+i) := by decide +kernel

private theorem r14part64 : ∀ i ∈ List.range 4, RunsAt 14 (64+i) := by decide +kernel

private theorem r14part68 : ∀ i ∈ List.range 4, RunsAt 14 (68+i) := by decide +kernel

private theorem r14part72 : ∀ i ∈ List.range 4, RunsAt 14 (72+i) := by decide +kernel

private theorem r14part76 : ∀ i ∈ List.range 4, RunsAt 14 (76+i) := by decide +kernel

private theorem r14part80 : ∀ i ∈ List.range 4, RunsAt 14 (80+i) := by decide +kernel

private theorem r14part84 : ∀ i ∈ List.range 4, RunsAt 14 (84+i) := by decide +kernel

private theorem r14part88 : ∀ i ∈ List.range 4, RunsAt 14 (88+i) := by decide +kernel

private theorem r14part92 : ∀ i ∈ List.range 4, RunsAt 14 (92+i) := by decide +kernel

private theorem r14part96 : ∀ i ∈ List.range 4, RunsAt 14 (96+i) := by decide +kernel

private theorem r14part100 : ∀ i ∈ List.range 4, RunsAt 14 (100+i) := by decide +kernel

private theorem r14part104 : ∀ i ∈ List.range 4, RunsAt 14 (104+i) := by decide +kernel

private theorem r14part108 : ∀ i ∈ List.range 4, RunsAt 14 (108+i) := by decide +kernel

private theorem r14part112 : ∀ i ∈ List.range 4, RunsAt 14 (112+i) := by decide +kernel

private theorem r14part116 : ∀ i ∈ List.range 4, RunsAt 14 (116+i) := by decide +kernel

private theorem r14part120 : ∀ i ∈ List.range 3, RunsAt 14 (120+i) := by decide +kernel

theorem checkedR14 : ∀ V ∈ List.range 123, RunsAt 14 V := by
  intro V hV
  have hlt : V < 123 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r14part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r14part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r14part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r14part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r14part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r14part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r14part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r14part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r14part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r14part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r14part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r14part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r14part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r14part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r14part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r14part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r14part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r14part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r14part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r14part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r14part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r14part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r14part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r14part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r14part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r14part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r14part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r14part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r14part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r14part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r14part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r15part0 : ∀ i ∈ List.range 4, RunsAt 15 (0+i) := by decide +kernel

private theorem r15part4 : ∀ i ∈ List.range 4, RunsAt 15 (4+i) := by decide +kernel

private theorem r15part8 : ∀ i ∈ List.range 4, RunsAt 15 (8+i) := by decide +kernel

private theorem r15part12 : ∀ i ∈ List.range 4, RunsAt 15 (12+i) := by decide +kernel

private theorem r15part16 : ∀ i ∈ List.range 4, RunsAt 15 (16+i) := by decide +kernel

private theorem r15part20 : ∀ i ∈ List.range 4, RunsAt 15 (20+i) := by decide +kernel

private theorem r15part24 : ∀ i ∈ List.range 4, RunsAt 15 (24+i) := by decide +kernel

private theorem r15part28 : ∀ i ∈ List.range 4, RunsAt 15 (28+i) := by decide +kernel

private theorem r15part32 : ∀ i ∈ List.range 4, RunsAt 15 (32+i) := by decide +kernel

private theorem r15part36 : ∀ i ∈ List.range 4, RunsAt 15 (36+i) := by decide +kernel

private theorem r15part40 : ∀ i ∈ List.range 4, RunsAt 15 (40+i) := by decide +kernel

private theorem r15part44 : ∀ i ∈ List.range 4, RunsAt 15 (44+i) := by decide +kernel

private theorem r15part48 : ∀ i ∈ List.range 4, RunsAt 15 (48+i) := by decide +kernel

private theorem r15part52 : ∀ i ∈ List.range 4, RunsAt 15 (52+i) := by decide +kernel

private theorem r15part56 : ∀ i ∈ List.range 4, RunsAt 15 (56+i) := by decide +kernel

private theorem r15part60 : ∀ i ∈ List.range 4, RunsAt 15 (60+i) := by decide +kernel

private theorem r15part64 : ∀ i ∈ List.range 4, RunsAt 15 (64+i) := by decide +kernel

private theorem r15part68 : ∀ i ∈ List.range 4, RunsAt 15 (68+i) := by decide +kernel

private theorem r15part72 : ∀ i ∈ List.range 4, RunsAt 15 (72+i) := by decide +kernel

private theorem r15part76 : ∀ i ∈ List.range 4, RunsAt 15 (76+i) := by decide +kernel

private theorem r15part80 : ∀ i ∈ List.range 4, RunsAt 15 (80+i) := by decide +kernel

private theorem r15part84 : ∀ i ∈ List.range 4, RunsAt 15 (84+i) := by decide +kernel

private theorem r15part88 : ∀ i ∈ List.range 4, RunsAt 15 (88+i) := by decide +kernel

private theorem r15part92 : ∀ i ∈ List.range 4, RunsAt 15 (92+i) := by decide +kernel

private theorem r15part96 : ∀ i ∈ List.range 4, RunsAt 15 (96+i) := by decide +kernel

private theorem r15part100 : ∀ i ∈ List.range 4, RunsAt 15 (100+i) := by decide +kernel

private theorem r15part104 : ∀ i ∈ List.range 4, RunsAt 15 (104+i) := by decide +kernel

private theorem r15part108 : ∀ i ∈ List.range 4, RunsAt 15 (108+i) := by decide +kernel

private theorem r15part112 : ∀ i ∈ List.range 4, RunsAt 15 (112+i) := by decide +kernel

private theorem r15part116 : ∀ i ∈ List.range 4, RunsAt 15 (116+i) := by decide +kernel

private theorem r15part120 : ∀ i ∈ List.range 2, RunsAt 15 (120+i) := by decide +kernel

theorem checkedR15 : ∀ V ∈ List.range 122, RunsAt 15 V := by
  intro V hV
  have hlt : V < 122 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r15part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r15part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r15part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r15part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r15part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r15part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r15part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r15part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r15part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r15part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r15part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r15part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r15part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r15part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r15part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r15part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r15part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r15part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r15part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r15part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r15part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r15part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r15part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r15part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r15part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r15part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r15part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r15part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r15part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r15part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r15part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r16part0 : ∀ i ∈ List.range 4, RunsAt 16 (0+i) := by decide +kernel

private theorem r16part4 : ∀ i ∈ List.range 4, RunsAt 16 (4+i) := by decide +kernel

private theorem r16part8 : ∀ i ∈ List.range 4, RunsAt 16 (8+i) := by decide +kernel

private theorem r16part12 : ∀ i ∈ List.range 4, RunsAt 16 (12+i) := by decide +kernel

private theorem r16part16 : ∀ i ∈ List.range 4, RunsAt 16 (16+i) := by decide +kernel

private theorem r16part20 : ∀ i ∈ List.range 4, RunsAt 16 (20+i) := by decide +kernel

private theorem r16part24 : ∀ i ∈ List.range 4, RunsAt 16 (24+i) := by decide +kernel

private theorem r16part28 : ∀ i ∈ List.range 4, RunsAt 16 (28+i) := by decide +kernel

private theorem r16part32 : ∀ i ∈ List.range 4, RunsAt 16 (32+i) := by decide +kernel

private theorem r16part36 : ∀ i ∈ List.range 4, RunsAt 16 (36+i) := by decide +kernel

private theorem r16part40 : ∀ i ∈ List.range 4, RunsAt 16 (40+i) := by decide +kernel

private theorem r16part44 : ∀ i ∈ List.range 4, RunsAt 16 (44+i) := by decide +kernel

private theorem r16part48 : ∀ i ∈ List.range 4, RunsAt 16 (48+i) := by decide +kernel

private theorem r16part52 : ∀ i ∈ List.range 4, RunsAt 16 (52+i) := by decide +kernel

private theorem r16part56 : ∀ i ∈ List.range 4, RunsAt 16 (56+i) := by decide +kernel

private theorem r16part60 : ∀ i ∈ List.range 4, RunsAt 16 (60+i) := by decide +kernel

private theorem r16part64 : ∀ i ∈ List.range 4, RunsAt 16 (64+i) := by decide +kernel

private theorem r16part68 : ∀ i ∈ List.range 4, RunsAt 16 (68+i) := by decide +kernel

private theorem r16part72 : ∀ i ∈ List.range 4, RunsAt 16 (72+i) := by decide +kernel

private theorem r16part76 : ∀ i ∈ List.range 4, RunsAt 16 (76+i) := by decide +kernel

private theorem r16part80 : ∀ i ∈ List.range 4, RunsAt 16 (80+i) := by decide +kernel

private theorem r16part84 : ∀ i ∈ List.range 4, RunsAt 16 (84+i) := by decide +kernel

private theorem r16part88 : ∀ i ∈ List.range 4, RunsAt 16 (88+i) := by decide +kernel

private theorem r16part92 : ∀ i ∈ List.range 4, RunsAt 16 (92+i) := by decide +kernel

private theorem r16part96 : ∀ i ∈ List.range 4, RunsAt 16 (96+i) := by decide +kernel

private theorem r16part100 : ∀ i ∈ List.range 4, RunsAt 16 (100+i) := by decide +kernel

private theorem r16part104 : ∀ i ∈ List.range 4, RunsAt 16 (104+i) := by decide +kernel

private theorem r16part108 : ∀ i ∈ List.range 4, RunsAt 16 (108+i) := by decide +kernel

private theorem r16part112 : ∀ i ∈ List.range 4, RunsAt 16 (112+i) := by decide +kernel

private theorem r16part116 : ∀ i ∈ List.range 4, RunsAt 16 (116+i) := by decide +kernel

private theorem r16part120 : ∀ i ∈ List.range 1, RunsAt 16 (120+i) := by decide +kernel

theorem checkedR16 : ∀ V ∈ List.range 121, RunsAt 16 V := by
  intro V hV
  have hlt : V < 121 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r16part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r16part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r16part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r16part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r16part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r16part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r16part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r16part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r16part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r16part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r16part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r16part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r16part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r16part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r16part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r16part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r16part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r16part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r16part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r16part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r16part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r16part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r16part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r16part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r16part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r16part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r16part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r16part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r16part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r16part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r16part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r17part0 : ∀ i ∈ List.range 4, RunsAt 17 (0+i) := by decide +kernel

private theorem r17part4 : ∀ i ∈ List.range 4, RunsAt 17 (4+i) := by decide +kernel

private theorem r17part8 : ∀ i ∈ List.range 4, RunsAt 17 (8+i) := by decide +kernel

private theorem r17part12 : ∀ i ∈ List.range 4, RunsAt 17 (12+i) := by decide +kernel

private theorem r17part16 : ∀ i ∈ List.range 4, RunsAt 17 (16+i) := by decide +kernel

private theorem r17part20 : ∀ i ∈ List.range 4, RunsAt 17 (20+i) := by decide +kernel

private theorem r17part24 : ∀ i ∈ List.range 4, RunsAt 17 (24+i) := by decide +kernel

private theorem r17part28 : ∀ i ∈ List.range 4, RunsAt 17 (28+i) := by decide +kernel

private theorem r17part32 : ∀ i ∈ List.range 4, RunsAt 17 (32+i) := by decide +kernel

private theorem r17part36 : ∀ i ∈ List.range 4, RunsAt 17 (36+i) := by decide +kernel

private theorem r17part40 : ∀ i ∈ List.range 4, RunsAt 17 (40+i) := by decide +kernel

private theorem r17part44 : ∀ i ∈ List.range 4, RunsAt 17 (44+i) := by decide +kernel

private theorem r17part48 : ∀ i ∈ List.range 4, RunsAt 17 (48+i) := by decide +kernel

private theorem r17part52 : ∀ i ∈ List.range 4, RunsAt 17 (52+i) := by decide +kernel

private theorem r17part56 : ∀ i ∈ List.range 4, RunsAt 17 (56+i) := by decide +kernel

private theorem r17part60 : ∀ i ∈ List.range 4, RunsAt 17 (60+i) := by decide +kernel

private theorem r17part64 : ∀ i ∈ List.range 4, RunsAt 17 (64+i) := by decide +kernel

private theorem r17part68 : ∀ i ∈ List.range 4, RunsAt 17 (68+i) := by decide +kernel

private theorem r17part72 : ∀ i ∈ List.range 4, RunsAt 17 (72+i) := by decide +kernel

private theorem r17part76 : ∀ i ∈ List.range 4, RunsAt 17 (76+i) := by decide +kernel

private theorem r17part80 : ∀ i ∈ List.range 4, RunsAt 17 (80+i) := by decide +kernel

private theorem r17part84 : ∀ i ∈ List.range 4, RunsAt 17 (84+i) := by decide +kernel

private theorem r17part88 : ∀ i ∈ List.range 4, RunsAt 17 (88+i) := by decide +kernel

private theorem r17part92 : ∀ i ∈ List.range 4, RunsAt 17 (92+i) := by decide +kernel

private theorem r17part96 : ∀ i ∈ List.range 4, RunsAt 17 (96+i) := by decide +kernel

private theorem r17part100 : ∀ i ∈ List.range 4, RunsAt 17 (100+i) := by decide +kernel

private theorem r17part104 : ∀ i ∈ List.range 4, RunsAt 17 (104+i) := by decide +kernel

private theorem r17part108 : ∀ i ∈ List.range 4, RunsAt 17 (108+i) := by decide +kernel

private theorem r17part112 : ∀ i ∈ List.range 4, RunsAt 17 (112+i) := by decide +kernel

private theorem r17part116 : ∀ i ∈ List.range 4, RunsAt 17 (116+i) := by decide +kernel

theorem checkedR17 : ∀ V ∈ List.range 120, RunsAt 17 V := by
  intro V hV
  have hlt : V < 120 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r17part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r17part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r17part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r17part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r17part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r17part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r17part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r17part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r17part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r17part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r17part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r17part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r17part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r17part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r17part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r17part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r17part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r17part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r17part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r17part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r17part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r17part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r17part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r17part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r17part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r17part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r17part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r17part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r17part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r17part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r18part0 : ∀ i ∈ List.range 4, RunsAt 18 (0+i) := by decide +kernel

private theorem r18part4 : ∀ i ∈ List.range 4, RunsAt 18 (4+i) := by decide +kernel

private theorem r18part8 : ∀ i ∈ List.range 4, RunsAt 18 (8+i) := by decide +kernel

private theorem r18part12 : ∀ i ∈ List.range 4, RunsAt 18 (12+i) := by decide +kernel

private theorem r18part16 : ∀ i ∈ List.range 4, RunsAt 18 (16+i) := by decide +kernel

private theorem r18part20 : ∀ i ∈ List.range 4, RunsAt 18 (20+i) := by decide +kernel

private theorem r18part24 : ∀ i ∈ List.range 4, RunsAt 18 (24+i) := by decide +kernel

private theorem r18part28 : ∀ i ∈ List.range 4, RunsAt 18 (28+i) := by decide +kernel

private theorem r18part32 : ∀ i ∈ List.range 4, RunsAt 18 (32+i) := by decide +kernel

private theorem r18part36 : ∀ i ∈ List.range 4, RunsAt 18 (36+i) := by decide +kernel

private theorem r18part40 : ∀ i ∈ List.range 4, RunsAt 18 (40+i) := by decide +kernel

private theorem r18part44 : ∀ i ∈ List.range 4, RunsAt 18 (44+i) := by decide +kernel

private theorem r18part48 : ∀ i ∈ List.range 4, RunsAt 18 (48+i) := by decide +kernel

private theorem r18part52 : ∀ i ∈ List.range 4, RunsAt 18 (52+i) := by decide +kernel

private theorem r18part56 : ∀ i ∈ List.range 4, RunsAt 18 (56+i) := by decide +kernel

private theorem r18part60 : ∀ i ∈ List.range 4, RunsAt 18 (60+i) := by decide +kernel

private theorem r18part64 : ∀ i ∈ List.range 4, RunsAt 18 (64+i) := by decide +kernel

private theorem r18part68 : ∀ i ∈ List.range 4, RunsAt 18 (68+i) := by decide +kernel

private theorem r18part72 : ∀ i ∈ List.range 4, RunsAt 18 (72+i) := by decide +kernel

private theorem r18part76 : ∀ i ∈ List.range 4, RunsAt 18 (76+i) := by decide +kernel

private theorem r18part80 : ∀ i ∈ List.range 4, RunsAt 18 (80+i) := by decide +kernel

private theorem r18part84 : ∀ i ∈ List.range 4, RunsAt 18 (84+i) := by decide +kernel

private theorem r18part88 : ∀ i ∈ List.range 4, RunsAt 18 (88+i) := by decide +kernel

private theorem r18part92 : ∀ i ∈ List.range 4, RunsAt 18 (92+i) := by decide +kernel

private theorem r18part96 : ∀ i ∈ List.range 4, RunsAt 18 (96+i) := by decide +kernel

private theorem r18part100 : ∀ i ∈ List.range 4, RunsAt 18 (100+i) := by decide +kernel

private theorem r18part104 : ∀ i ∈ List.range 4, RunsAt 18 (104+i) := by decide +kernel

private theorem r18part108 : ∀ i ∈ List.range 4, RunsAt 18 (108+i) := by decide +kernel

private theorem r18part112 : ∀ i ∈ List.range 4, RunsAt 18 (112+i) := by decide +kernel

private theorem r18part116 : ∀ i ∈ List.range 3, RunsAt 18 (116+i) := by decide +kernel

theorem checkedR18 : ∀ V ∈ List.range 119, RunsAt 18 V := by
  intro V hV
  have hlt : V < 119 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r18part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r18part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r18part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r18part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r18part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r18part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r18part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r18part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r18part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r18part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r18part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r18part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r18part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r18part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r18part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r18part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r18part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r18part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r18part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r18part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r18part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r18part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r18part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r18part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r18part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r18part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r18part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r18part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r18part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r18part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r19part0 : ∀ i ∈ List.range 4, RunsAt 19 (0+i) := by decide +kernel

private theorem r19part4 : ∀ i ∈ List.range 4, RunsAt 19 (4+i) := by decide +kernel

private theorem r19part8 : ∀ i ∈ List.range 4, RunsAt 19 (8+i) := by decide +kernel

private theorem r19part12 : ∀ i ∈ List.range 4, RunsAt 19 (12+i) := by decide +kernel

private theorem r19part16 : ∀ i ∈ List.range 4, RunsAt 19 (16+i) := by decide +kernel

private theorem r19part20 : ∀ i ∈ List.range 4, RunsAt 19 (20+i) := by decide +kernel

private theorem r19part24 : ∀ i ∈ List.range 4, RunsAt 19 (24+i) := by decide +kernel

private theorem r19part28 : ∀ i ∈ List.range 4, RunsAt 19 (28+i) := by decide +kernel

private theorem r19part32 : ∀ i ∈ List.range 4, RunsAt 19 (32+i) := by decide +kernel

private theorem r19part36 : ∀ i ∈ List.range 4, RunsAt 19 (36+i) := by decide +kernel

private theorem r19part40 : ∀ i ∈ List.range 4, RunsAt 19 (40+i) := by decide +kernel

private theorem r19part44 : ∀ i ∈ List.range 4, RunsAt 19 (44+i) := by decide +kernel

private theorem r19part48 : ∀ i ∈ List.range 4, RunsAt 19 (48+i) := by decide +kernel

private theorem r19part52 : ∀ i ∈ List.range 4, RunsAt 19 (52+i) := by decide +kernel

private theorem r19part56 : ∀ i ∈ List.range 4, RunsAt 19 (56+i) := by decide +kernel

private theorem r19part60 : ∀ i ∈ List.range 4, RunsAt 19 (60+i) := by decide +kernel

private theorem r19part64 : ∀ i ∈ List.range 4, RunsAt 19 (64+i) := by decide +kernel

private theorem r19part68 : ∀ i ∈ List.range 4, RunsAt 19 (68+i) := by decide +kernel

private theorem r19part72 : ∀ i ∈ List.range 4, RunsAt 19 (72+i) := by decide +kernel

private theorem r19part76 : ∀ i ∈ List.range 4, RunsAt 19 (76+i) := by decide +kernel

private theorem r19part80 : ∀ i ∈ List.range 4, RunsAt 19 (80+i) := by decide +kernel

private theorem r19part84 : ∀ i ∈ List.range 4, RunsAt 19 (84+i) := by decide +kernel

private theorem r19part88 : ∀ i ∈ List.range 4, RunsAt 19 (88+i) := by decide +kernel

private theorem r19part92 : ∀ i ∈ List.range 4, RunsAt 19 (92+i) := by decide +kernel

private theorem r19part96 : ∀ i ∈ List.range 4, RunsAt 19 (96+i) := by decide +kernel

private theorem r19part100 : ∀ i ∈ List.range 4, RunsAt 19 (100+i) := by decide +kernel

private theorem r19part104 : ∀ i ∈ List.range 4, RunsAt 19 (104+i) := by decide +kernel

private theorem r19part108 : ∀ i ∈ List.range 4, RunsAt 19 (108+i) := by decide +kernel

private theorem r19part112 : ∀ i ∈ List.range 4, RunsAt 19 (112+i) := by decide +kernel

private theorem r19part116 : ∀ i ∈ List.range 2, RunsAt 19 (116+i) := by decide +kernel

theorem checkedR19 : ∀ V ∈ List.range 118, RunsAt 19 V := by
  intro V hV
  have hlt : V < 118 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r19part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r19part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r19part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r19part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r19part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r19part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r19part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r19part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r19part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r19part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r19part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r19part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r19part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r19part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r19part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r19part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r19part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r19part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r19part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r19part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r19part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r19part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r19part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r19part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r19part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r19part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r19part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r19part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r19part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r19part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r20part0 : ∀ i ∈ List.range 4, RunsAt 20 (0+i) := by decide +kernel

private theorem r20part4 : ∀ i ∈ List.range 4, RunsAt 20 (4+i) := by decide +kernel

private theorem r20part8 : ∀ i ∈ List.range 4, RunsAt 20 (8+i) := by decide +kernel

private theorem r20part12 : ∀ i ∈ List.range 4, RunsAt 20 (12+i) := by decide +kernel

private theorem r20part16 : ∀ i ∈ List.range 4, RunsAt 20 (16+i) := by decide +kernel

private theorem r20part20 : ∀ i ∈ List.range 4, RunsAt 20 (20+i) := by decide +kernel

private theorem r20part24 : ∀ i ∈ List.range 4, RunsAt 20 (24+i) := by decide +kernel

private theorem r20part28 : ∀ i ∈ List.range 4, RunsAt 20 (28+i) := by decide +kernel

private theorem r20part32 : ∀ i ∈ List.range 4, RunsAt 20 (32+i) := by decide +kernel

private theorem r20part36 : ∀ i ∈ List.range 4, RunsAt 20 (36+i) := by decide +kernel

private theorem r20part40 : ∀ i ∈ List.range 4, RunsAt 20 (40+i) := by decide +kernel

private theorem r20part44 : ∀ i ∈ List.range 4, RunsAt 20 (44+i) := by decide +kernel

private theorem r20part48 : ∀ i ∈ List.range 4, RunsAt 20 (48+i) := by decide +kernel

private theorem r20part52 : ∀ i ∈ List.range 4, RunsAt 20 (52+i) := by decide +kernel

private theorem r20part56 : ∀ i ∈ List.range 4, RunsAt 20 (56+i) := by decide +kernel

private theorem r20part60 : ∀ i ∈ List.range 4, RunsAt 20 (60+i) := by decide +kernel

private theorem r20part64 : ∀ i ∈ List.range 4, RunsAt 20 (64+i) := by decide +kernel

private theorem r20part68 : ∀ i ∈ List.range 4, RunsAt 20 (68+i) := by decide +kernel

private theorem r20part72 : ∀ i ∈ List.range 4, RunsAt 20 (72+i) := by decide +kernel

private theorem r20part76 : ∀ i ∈ List.range 4, RunsAt 20 (76+i) := by decide +kernel

private theorem r20part80 : ∀ i ∈ List.range 4, RunsAt 20 (80+i) := by decide +kernel

private theorem r20part84 : ∀ i ∈ List.range 4, RunsAt 20 (84+i) := by decide +kernel

private theorem r20part88 : ∀ i ∈ List.range 4, RunsAt 20 (88+i) := by decide +kernel

private theorem r20part92 : ∀ i ∈ List.range 4, RunsAt 20 (92+i) := by decide +kernel

private theorem r20part96 : ∀ i ∈ List.range 4, RunsAt 20 (96+i) := by decide +kernel

private theorem r20part100 : ∀ i ∈ List.range 4, RunsAt 20 (100+i) := by decide +kernel

private theorem r20part104 : ∀ i ∈ List.range 4, RunsAt 20 (104+i) := by decide +kernel

private theorem r20part108 : ∀ i ∈ List.range 4, RunsAt 20 (108+i) := by decide +kernel

private theorem r20part112 : ∀ i ∈ List.range 4, RunsAt 20 (112+i) := by decide +kernel

private theorem r20part116 : ∀ i ∈ List.range 1, RunsAt 20 (116+i) := by decide +kernel

theorem checkedR20 : ∀ V ∈ List.range 117, RunsAt 20 V := by
  intro V hV
  have hlt : V < 117 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r20part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r20part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r20part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r20part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r20part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r20part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r20part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r20part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r20part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r20part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r20part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r20part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r20part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r20part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r20part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r20part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r20part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r20part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r20part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r20part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r20part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r20part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r20part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r20part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r20part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r20part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r20part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r20part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r20part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r20part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r21part0 : ∀ i ∈ List.range 4, RunsAt 21 (0+i) := by decide +kernel

private theorem r21part4 : ∀ i ∈ List.range 4, RunsAt 21 (4+i) := by decide +kernel

private theorem r21part8 : ∀ i ∈ List.range 4, RunsAt 21 (8+i) := by decide +kernel

private theorem r21part12 : ∀ i ∈ List.range 4, RunsAt 21 (12+i) := by decide +kernel

private theorem r21part16 : ∀ i ∈ List.range 4, RunsAt 21 (16+i) := by decide +kernel

private theorem r21part20 : ∀ i ∈ List.range 4, RunsAt 21 (20+i) := by decide +kernel

private theorem r21part24 : ∀ i ∈ List.range 4, RunsAt 21 (24+i) := by decide +kernel

private theorem r21part28 : ∀ i ∈ List.range 4, RunsAt 21 (28+i) := by decide +kernel

private theorem r21part32 : ∀ i ∈ List.range 4, RunsAt 21 (32+i) := by decide +kernel

private theorem r21part36 : ∀ i ∈ List.range 4, RunsAt 21 (36+i) := by decide +kernel

private theorem r21part40 : ∀ i ∈ List.range 4, RunsAt 21 (40+i) := by decide +kernel

private theorem r21part44 : ∀ i ∈ List.range 4, RunsAt 21 (44+i) := by decide +kernel

private theorem r21part48 : ∀ i ∈ List.range 4, RunsAt 21 (48+i) := by decide +kernel

private theorem r21part52 : ∀ i ∈ List.range 4, RunsAt 21 (52+i) := by decide +kernel

private theorem r21part56 : ∀ i ∈ List.range 4, RunsAt 21 (56+i) := by decide +kernel

private theorem r21part60 : ∀ i ∈ List.range 4, RunsAt 21 (60+i) := by decide +kernel

private theorem r21part64 : ∀ i ∈ List.range 4, RunsAt 21 (64+i) := by decide +kernel

private theorem r21part68 : ∀ i ∈ List.range 4, RunsAt 21 (68+i) := by decide +kernel

private theorem r21part72 : ∀ i ∈ List.range 4, RunsAt 21 (72+i) := by decide +kernel

private theorem r21part76 : ∀ i ∈ List.range 4, RunsAt 21 (76+i) := by decide +kernel

private theorem r21part80 : ∀ i ∈ List.range 4, RunsAt 21 (80+i) := by decide +kernel

private theorem r21part84 : ∀ i ∈ List.range 4, RunsAt 21 (84+i) := by decide +kernel

private theorem r21part88 : ∀ i ∈ List.range 4, RunsAt 21 (88+i) := by decide +kernel

private theorem r21part92 : ∀ i ∈ List.range 4, RunsAt 21 (92+i) := by decide +kernel

private theorem r21part96 : ∀ i ∈ List.range 4, RunsAt 21 (96+i) := by decide +kernel

private theorem r21part100 : ∀ i ∈ List.range 4, RunsAt 21 (100+i) := by decide +kernel

private theorem r21part104 : ∀ i ∈ List.range 4, RunsAt 21 (104+i) := by decide +kernel

private theorem r21part108 : ∀ i ∈ List.range 4, RunsAt 21 (108+i) := by decide +kernel

private theorem r21part112 : ∀ i ∈ List.range 4, RunsAt 21 (112+i) := by decide +kernel

theorem checkedR21 : ∀ V ∈ List.range 116, RunsAt 21 V := by
  intro V hV
  have hlt : V < 116 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r21part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r21part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r21part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r21part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r21part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r21part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r21part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r21part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r21part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r21part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r21part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r21part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r21part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r21part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r21part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r22part0 : ∀ i ∈ List.range 4, RunsAt 22 (0+i) := by decide +kernel

private theorem r22part4 : ∀ i ∈ List.range 4, RunsAt 22 (4+i) := by decide +kernel

private theorem r22part8 : ∀ i ∈ List.range 4, RunsAt 22 (8+i) := by decide +kernel

private theorem r22part12 : ∀ i ∈ List.range 4, RunsAt 22 (12+i) := by decide +kernel

private theorem r22part16 : ∀ i ∈ List.range 4, RunsAt 22 (16+i) := by decide +kernel

private theorem r22part20 : ∀ i ∈ List.range 4, RunsAt 22 (20+i) := by decide +kernel

private theorem r22part24 : ∀ i ∈ List.range 4, RunsAt 22 (24+i) := by decide +kernel

private theorem r22part28 : ∀ i ∈ List.range 4, RunsAt 22 (28+i) := by decide +kernel

private theorem r22part32 : ∀ i ∈ List.range 4, RunsAt 22 (32+i) := by decide +kernel

private theorem r22part36 : ∀ i ∈ List.range 4, RunsAt 22 (36+i) := by decide +kernel

private theorem r22part40 : ∀ i ∈ List.range 4, RunsAt 22 (40+i) := by decide +kernel

private theorem r22part44 : ∀ i ∈ List.range 4, RunsAt 22 (44+i) := by decide +kernel

private theorem r22part48 : ∀ i ∈ List.range 4, RunsAt 22 (48+i) := by decide +kernel

private theorem r22part52 : ∀ i ∈ List.range 4, RunsAt 22 (52+i) := by decide +kernel

private theorem r22part56 : ∀ i ∈ List.range 4, RunsAt 22 (56+i) := by decide +kernel

private theorem r22part60 : ∀ i ∈ List.range 4, RunsAt 22 (60+i) := by decide +kernel

private theorem r22part64 : ∀ i ∈ List.range 4, RunsAt 22 (64+i) := by decide +kernel

private theorem r22part68 : ∀ i ∈ List.range 4, RunsAt 22 (68+i) := by decide +kernel

private theorem r22part72 : ∀ i ∈ List.range 4, RunsAt 22 (72+i) := by decide +kernel

private theorem r22part76 : ∀ i ∈ List.range 4, RunsAt 22 (76+i) := by decide +kernel

private theorem r22part80 : ∀ i ∈ List.range 4, RunsAt 22 (80+i) := by decide +kernel

private theorem r22part84 : ∀ i ∈ List.range 4, RunsAt 22 (84+i) := by decide +kernel

private theorem r22part88 : ∀ i ∈ List.range 4, RunsAt 22 (88+i) := by decide +kernel

private theorem r22part92 : ∀ i ∈ List.range 4, RunsAt 22 (92+i) := by decide +kernel

private theorem r22part96 : ∀ i ∈ List.range 4, RunsAt 22 (96+i) := by decide +kernel

private theorem r22part100 : ∀ i ∈ List.range 4, RunsAt 22 (100+i) := by decide +kernel

private theorem r22part104 : ∀ i ∈ List.range 4, RunsAt 22 (104+i) := by decide +kernel

private theorem r22part108 : ∀ i ∈ List.range 4, RunsAt 22 (108+i) := by decide +kernel

private theorem r22part112 : ∀ i ∈ List.range 3, RunsAt 22 (112+i) := by decide +kernel

theorem checkedR22 : ∀ V ∈ List.range 115, RunsAt 22 V := by
  intro V hV
  have hlt : V < 115 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r22part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r22part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r22part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r22part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r22part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r22part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r22part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r22part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r22part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r22part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r22part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r22part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r22part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r22part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r22part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r23part0 : ∀ i ∈ List.range 4, RunsAt 23 (0+i) := by decide +kernel

private theorem r23part4 : ∀ i ∈ List.range 4, RunsAt 23 (4+i) := by decide +kernel

private theorem r23part8 : ∀ i ∈ List.range 4, RunsAt 23 (8+i) := by decide +kernel

private theorem r23part12 : ∀ i ∈ List.range 4, RunsAt 23 (12+i) := by decide +kernel

private theorem r23part16 : ∀ i ∈ List.range 4, RunsAt 23 (16+i) := by decide +kernel

private theorem r23part20 : ∀ i ∈ List.range 4, RunsAt 23 (20+i) := by decide +kernel

private theorem r23part24 : ∀ i ∈ List.range 4, RunsAt 23 (24+i) := by decide +kernel

private theorem r23part28 : ∀ i ∈ List.range 4, RunsAt 23 (28+i) := by decide +kernel

private theorem r23part32 : ∀ i ∈ List.range 4, RunsAt 23 (32+i) := by decide +kernel

private theorem r23part36 : ∀ i ∈ List.range 4, RunsAt 23 (36+i) := by decide +kernel

private theorem r23part40 : ∀ i ∈ List.range 4, RunsAt 23 (40+i) := by decide +kernel

private theorem r23part44 : ∀ i ∈ List.range 4, RunsAt 23 (44+i) := by decide +kernel

private theorem r23part48 : ∀ i ∈ List.range 4, RunsAt 23 (48+i) := by decide +kernel

private theorem r23part52 : ∀ i ∈ List.range 4, RunsAt 23 (52+i) := by decide +kernel

private theorem r23part56 : ∀ i ∈ List.range 4, RunsAt 23 (56+i) := by decide +kernel

private theorem r23part60 : ∀ i ∈ List.range 4, RunsAt 23 (60+i) := by decide +kernel

private theorem r23part64 : ∀ i ∈ List.range 4, RunsAt 23 (64+i) := by decide +kernel

private theorem r23part68 : ∀ i ∈ List.range 4, RunsAt 23 (68+i) := by decide +kernel

private theorem r23part72 : ∀ i ∈ List.range 4, RunsAt 23 (72+i) := by decide +kernel

private theorem r23part76 : ∀ i ∈ List.range 4, RunsAt 23 (76+i) := by decide +kernel

private theorem r23part80 : ∀ i ∈ List.range 4, RunsAt 23 (80+i) := by decide +kernel

private theorem r23part84 : ∀ i ∈ List.range 4, RunsAt 23 (84+i) := by decide +kernel

private theorem r23part88 : ∀ i ∈ List.range 4, RunsAt 23 (88+i) := by decide +kernel

private theorem r23part92 : ∀ i ∈ List.range 4, RunsAt 23 (92+i) := by decide +kernel

private theorem r23part96 : ∀ i ∈ List.range 4, RunsAt 23 (96+i) := by decide +kernel

private theorem r23part100 : ∀ i ∈ List.range 4, RunsAt 23 (100+i) := by decide +kernel

private theorem r23part104 : ∀ i ∈ List.range 4, RunsAt 23 (104+i) := by decide +kernel

private theorem r23part108 : ∀ i ∈ List.range 4, RunsAt 23 (108+i) := by decide +kernel

private theorem r23part112 : ∀ i ∈ List.range 2, RunsAt 23 (112+i) := by decide +kernel

theorem checkedR23 : ∀ V ∈ List.range 114, RunsAt 23 V := by
  intro V hV
  have hlt : V < 114 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r23part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r23part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r23part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r23part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r23part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r23part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r23part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r23part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r23part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r23part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r23part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r23part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r23part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r23part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r24part0 : ∀ i ∈ List.range 4, RunsAt 24 (0+i) := by decide +kernel

private theorem r24part4 : ∀ i ∈ List.range 4, RunsAt 24 (4+i) := by decide +kernel

private theorem r24part8 : ∀ i ∈ List.range 4, RunsAt 24 (8+i) := by decide +kernel

private theorem r24part12 : ∀ i ∈ List.range 4, RunsAt 24 (12+i) := by decide +kernel

private theorem r24part16 : ∀ i ∈ List.range 4, RunsAt 24 (16+i) := by decide +kernel

private theorem r24part20 : ∀ i ∈ List.range 4, RunsAt 24 (20+i) := by decide +kernel

private theorem r24part24 : ∀ i ∈ List.range 4, RunsAt 24 (24+i) := by decide +kernel

private theorem r24part28 : ∀ i ∈ List.range 4, RunsAt 24 (28+i) := by decide +kernel

private theorem r24part32 : ∀ i ∈ List.range 4, RunsAt 24 (32+i) := by decide +kernel

private theorem r24part36 : ∀ i ∈ List.range 4, RunsAt 24 (36+i) := by decide +kernel

private theorem r24part40 : ∀ i ∈ List.range 4, RunsAt 24 (40+i) := by decide +kernel

private theorem r24part44 : ∀ i ∈ List.range 4, RunsAt 24 (44+i) := by decide +kernel

private theorem r24part48 : ∀ i ∈ List.range 4, RunsAt 24 (48+i) := by decide +kernel

private theorem r24part52 : ∀ i ∈ List.range 4, RunsAt 24 (52+i) := by decide +kernel

private theorem r24part56 : ∀ i ∈ List.range 4, RunsAt 24 (56+i) := by decide +kernel

private theorem r24part60 : ∀ i ∈ List.range 4, RunsAt 24 (60+i) := by decide +kernel

private theorem r24part64 : ∀ i ∈ List.range 4, RunsAt 24 (64+i) := by decide +kernel

private theorem r24part68 : ∀ i ∈ List.range 4, RunsAt 24 (68+i) := by decide +kernel

private theorem r24part72 : ∀ i ∈ List.range 4, RunsAt 24 (72+i) := by decide +kernel

private theorem r24part76 : ∀ i ∈ List.range 4, RunsAt 24 (76+i) := by decide +kernel

private theorem r24part80 : ∀ i ∈ List.range 4, RunsAt 24 (80+i) := by decide +kernel

private theorem r24part84 : ∀ i ∈ List.range 4, RunsAt 24 (84+i) := by decide +kernel

private theorem r24part88 : ∀ i ∈ List.range 4, RunsAt 24 (88+i) := by decide +kernel

private theorem r24part92 : ∀ i ∈ List.range 4, RunsAt 24 (92+i) := by decide +kernel

private theorem r24part96 : ∀ i ∈ List.range 4, RunsAt 24 (96+i) := by decide +kernel

private theorem r24part100 : ∀ i ∈ List.range 4, RunsAt 24 (100+i) := by decide +kernel

private theorem r24part104 : ∀ i ∈ List.range 4, RunsAt 24 (104+i) := by decide +kernel

private theorem r24part108 : ∀ i ∈ List.range 4, RunsAt 24 (108+i) := by decide +kernel

private theorem r24part112 : ∀ i ∈ List.range 1, RunsAt 24 (112+i) := by decide +kernel

theorem checkedR24 : ∀ V ∈ List.range 113, RunsAt 24 V := by
  intro V hV
  have hlt : V < 113 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r24part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r24part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r24part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r24part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r24part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r24part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r24part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r24part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r24part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r24part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r24part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r24part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r24part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r24part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r25part0 : ∀ i ∈ List.range 4, RunsAt 25 (0+i) := by decide +kernel

private theorem r25part4 : ∀ i ∈ List.range 4, RunsAt 25 (4+i) := by decide +kernel

private theorem r25part8 : ∀ i ∈ List.range 4, RunsAt 25 (8+i) := by decide +kernel

private theorem r25part12 : ∀ i ∈ List.range 4, RunsAt 25 (12+i) := by decide +kernel

private theorem r25part16 : ∀ i ∈ List.range 4, RunsAt 25 (16+i) := by decide +kernel

private theorem r25part20 : ∀ i ∈ List.range 4, RunsAt 25 (20+i) := by decide +kernel

private theorem r25part24 : ∀ i ∈ List.range 4, RunsAt 25 (24+i) := by decide +kernel

private theorem r25part28 : ∀ i ∈ List.range 4, RunsAt 25 (28+i) := by decide +kernel

private theorem r25part32 : ∀ i ∈ List.range 4, RunsAt 25 (32+i) := by decide +kernel

private theorem r25part36 : ∀ i ∈ List.range 4, RunsAt 25 (36+i) := by decide +kernel

private theorem r25part40 : ∀ i ∈ List.range 4, RunsAt 25 (40+i) := by decide +kernel

private theorem r25part44 : ∀ i ∈ List.range 4, RunsAt 25 (44+i) := by decide +kernel

private theorem r25part48 : ∀ i ∈ List.range 4, RunsAt 25 (48+i) := by decide +kernel

private theorem r25part52 : ∀ i ∈ List.range 4, RunsAt 25 (52+i) := by decide +kernel

private theorem r25part56 : ∀ i ∈ List.range 4, RunsAt 25 (56+i) := by decide +kernel

private theorem r25part60 : ∀ i ∈ List.range 4, RunsAt 25 (60+i) := by decide +kernel

private theorem r25part64 : ∀ i ∈ List.range 4, RunsAt 25 (64+i) := by decide +kernel

private theorem r25part68 : ∀ i ∈ List.range 4, RunsAt 25 (68+i) := by decide +kernel

private theorem r25part72 : ∀ i ∈ List.range 4, RunsAt 25 (72+i) := by decide +kernel

private theorem r25part76 : ∀ i ∈ List.range 4, RunsAt 25 (76+i) := by decide +kernel

private theorem r25part80 : ∀ i ∈ List.range 4, RunsAt 25 (80+i) := by decide +kernel

private theorem r25part84 : ∀ i ∈ List.range 4, RunsAt 25 (84+i) := by decide +kernel

private theorem r25part88 : ∀ i ∈ List.range 4, RunsAt 25 (88+i) := by decide +kernel

private theorem r25part92 : ∀ i ∈ List.range 4, RunsAt 25 (92+i) := by decide +kernel

private theorem r25part96 : ∀ i ∈ List.range 4, RunsAt 25 (96+i) := by decide +kernel

private theorem r25part100 : ∀ i ∈ List.range 4, RunsAt 25 (100+i) := by decide +kernel

private theorem r25part104 : ∀ i ∈ List.range 4, RunsAt 25 (104+i) := by decide +kernel

private theorem r25part108 : ∀ i ∈ List.range 4, RunsAt 25 (108+i) := by decide +kernel

theorem checkedR25 : ∀ V ∈ List.range 112, RunsAt 25 V := by
  intro V hV
  have hlt : V < 112 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r25part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r25part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r25part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r25part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r25part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r25part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r25part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r25part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r25part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r25part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r25part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r25part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r25part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r25part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r25part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r26part0 : ∀ i ∈ List.range 4, RunsAt 26 (0+i) := by decide +kernel

private theorem r26part4 : ∀ i ∈ List.range 4, RunsAt 26 (4+i) := by decide +kernel

private theorem r26part8 : ∀ i ∈ List.range 4, RunsAt 26 (8+i) := by decide +kernel

private theorem r26part12 : ∀ i ∈ List.range 4, RunsAt 26 (12+i) := by decide +kernel

private theorem r26part16 : ∀ i ∈ List.range 4, RunsAt 26 (16+i) := by decide +kernel

private theorem r26part20 : ∀ i ∈ List.range 4, RunsAt 26 (20+i) := by decide +kernel

private theorem r26part24 : ∀ i ∈ List.range 4, RunsAt 26 (24+i) := by decide +kernel

private theorem r26part28 : ∀ i ∈ List.range 4, RunsAt 26 (28+i) := by decide +kernel

private theorem r26part32 : ∀ i ∈ List.range 4, RunsAt 26 (32+i) := by decide +kernel

private theorem r26part36 : ∀ i ∈ List.range 4, RunsAt 26 (36+i) := by decide +kernel

private theorem r26part40 : ∀ i ∈ List.range 4, RunsAt 26 (40+i) := by decide +kernel

private theorem r26part44 : ∀ i ∈ List.range 4, RunsAt 26 (44+i) := by decide +kernel

private theorem r26part48 : ∀ i ∈ List.range 4, RunsAt 26 (48+i) := by decide +kernel

private theorem r26part52 : ∀ i ∈ List.range 4, RunsAt 26 (52+i) := by decide +kernel

private theorem r26part56 : ∀ i ∈ List.range 4, RunsAt 26 (56+i) := by decide +kernel

private theorem r26part60 : ∀ i ∈ List.range 4, RunsAt 26 (60+i) := by decide +kernel

private theorem r26part64 : ∀ i ∈ List.range 4, RunsAt 26 (64+i) := by decide +kernel

private theorem r26part68 : ∀ i ∈ List.range 4, RunsAt 26 (68+i) := by decide +kernel

private theorem r26part72 : ∀ i ∈ List.range 4, RunsAt 26 (72+i) := by decide +kernel

private theorem r26part76 : ∀ i ∈ List.range 4, RunsAt 26 (76+i) := by decide +kernel

private theorem r26part80 : ∀ i ∈ List.range 4, RunsAt 26 (80+i) := by decide +kernel

private theorem r26part84 : ∀ i ∈ List.range 4, RunsAt 26 (84+i) := by decide +kernel

private theorem r26part88 : ∀ i ∈ List.range 4, RunsAt 26 (88+i) := by decide +kernel

private theorem r26part92 : ∀ i ∈ List.range 4, RunsAt 26 (92+i) := by decide +kernel

private theorem r26part96 : ∀ i ∈ List.range 4, RunsAt 26 (96+i) := by decide +kernel

private theorem r26part100 : ∀ i ∈ List.range 4, RunsAt 26 (100+i) := by decide +kernel

private theorem r26part104 : ∀ i ∈ List.range 4, RunsAt 26 (104+i) := by decide +kernel

private theorem r26part108 : ∀ i ∈ List.range 3, RunsAt 26 (108+i) := by decide +kernel

theorem checkedR26 : ∀ V ∈ List.range 111, RunsAt 26 V := by
  intro V hV
  have hlt : V < 111 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r26part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r26part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r26part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r26part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r26part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r26part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r26part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r26part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r26part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r26part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r26part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r26part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r26part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r26part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r26part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r27part0 : ∀ i ∈ List.range 4, RunsAt 27 (0+i) := by decide +kernel

private theorem r27part4 : ∀ i ∈ List.range 4, RunsAt 27 (4+i) := by decide +kernel

private theorem r27part8 : ∀ i ∈ List.range 4, RunsAt 27 (8+i) := by decide +kernel

private theorem r27part12 : ∀ i ∈ List.range 4, RunsAt 27 (12+i) := by decide +kernel

private theorem r27part16 : ∀ i ∈ List.range 4, RunsAt 27 (16+i) := by decide +kernel

private theorem r27part20 : ∀ i ∈ List.range 4, RunsAt 27 (20+i) := by decide +kernel

private theorem r27part24 : ∀ i ∈ List.range 4, RunsAt 27 (24+i) := by decide +kernel

private theorem r27part28 : ∀ i ∈ List.range 4, RunsAt 27 (28+i) := by decide +kernel

private theorem r27part32 : ∀ i ∈ List.range 4, RunsAt 27 (32+i) := by decide +kernel

private theorem r27part36 : ∀ i ∈ List.range 4, RunsAt 27 (36+i) := by decide +kernel

private theorem r27part40 : ∀ i ∈ List.range 4, RunsAt 27 (40+i) := by decide +kernel

private theorem r27part44 : ∀ i ∈ List.range 4, RunsAt 27 (44+i) := by decide +kernel

private theorem r27part48 : ∀ i ∈ List.range 4, RunsAt 27 (48+i) := by decide +kernel

private theorem r27part52 : ∀ i ∈ List.range 4, RunsAt 27 (52+i) := by decide +kernel

private theorem r27part56 : ∀ i ∈ List.range 4, RunsAt 27 (56+i) := by decide +kernel

private theorem r27part60 : ∀ i ∈ List.range 4, RunsAt 27 (60+i) := by decide +kernel

private theorem r27part64 : ∀ i ∈ List.range 4, RunsAt 27 (64+i) := by decide +kernel

private theorem r27part68 : ∀ i ∈ List.range 4, RunsAt 27 (68+i) := by decide +kernel

private theorem r27part72 : ∀ i ∈ List.range 4, RunsAt 27 (72+i) := by decide +kernel

private theorem r27part76 : ∀ i ∈ List.range 4, RunsAt 27 (76+i) := by decide +kernel

private theorem r27part80 : ∀ i ∈ List.range 4, RunsAt 27 (80+i) := by decide +kernel

private theorem r27part84 : ∀ i ∈ List.range 4, RunsAt 27 (84+i) := by decide +kernel

private theorem r27part88 : ∀ i ∈ List.range 4, RunsAt 27 (88+i) := by decide +kernel

private theorem r27part92 : ∀ i ∈ List.range 4, RunsAt 27 (92+i) := by decide +kernel

private theorem r27part96 : ∀ i ∈ List.range 4, RunsAt 27 (96+i) := by decide +kernel

private theorem r27part100 : ∀ i ∈ List.range 4, RunsAt 27 (100+i) := by decide +kernel

private theorem r27part104 : ∀ i ∈ List.range 4, RunsAt 27 (104+i) := by decide +kernel

private theorem r27part108 : ∀ i ∈ List.range 2, RunsAt 27 (108+i) := by decide +kernel

theorem checkedR27 : ∀ V ∈ List.range 110, RunsAt 27 V := by
  intro V hV
  have hlt : V < 110 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r27part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r27part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r27part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r27part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r27part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r27part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r27part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r27part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r27part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r27part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r27part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r27part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r27part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r27part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r27part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r28part0 : ∀ i ∈ List.range 4, RunsAt 28 (0+i) := by decide +kernel

private theorem r28part4 : ∀ i ∈ List.range 4, RunsAt 28 (4+i) := by decide +kernel

private theorem r28part8 : ∀ i ∈ List.range 4, RunsAt 28 (8+i) := by decide +kernel

private theorem r28part12 : ∀ i ∈ List.range 4, RunsAt 28 (12+i) := by decide +kernel

private theorem r28part16 : ∀ i ∈ List.range 4, RunsAt 28 (16+i) := by decide +kernel

private theorem r28part20 : ∀ i ∈ List.range 4, RunsAt 28 (20+i) := by decide +kernel

private theorem r28part24 : ∀ i ∈ List.range 4, RunsAt 28 (24+i) := by decide +kernel

private theorem r28part28 : ∀ i ∈ List.range 4, RunsAt 28 (28+i) := by decide +kernel

private theorem r28part32 : ∀ i ∈ List.range 4, RunsAt 28 (32+i) := by decide +kernel

private theorem r28part36 : ∀ i ∈ List.range 4, RunsAt 28 (36+i) := by decide +kernel

private theorem r28part40 : ∀ i ∈ List.range 4, RunsAt 28 (40+i) := by decide +kernel

private theorem r28part44 : ∀ i ∈ List.range 4, RunsAt 28 (44+i) := by decide +kernel

private theorem r28part48 : ∀ i ∈ List.range 4, RunsAt 28 (48+i) := by decide +kernel

private theorem r28part52 : ∀ i ∈ List.range 4, RunsAt 28 (52+i) := by decide +kernel

private theorem r28part56 : ∀ i ∈ List.range 4, RunsAt 28 (56+i) := by decide +kernel

private theorem r28part60 : ∀ i ∈ List.range 4, RunsAt 28 (60+i) := by decide +kernel

private theorem r28part64 : ∀ i ∈ List.range 4, RunsAt 28 (64+i) := by decide +kernel

private theorem r28part68 : ∀ i ∈ List.range 4, RunsAt 28 (68+i) := by decide +kernel

private theorem r28part72 : ∀ i ∈ List.range 4, RunsAt 28 (72+i) := by decide +kernel

private theorem r28part76 : ∀ i ∈ List.range 4, RunsAt 28 (76+i) := by decide +kernel

private theorem r28part80 : ∀ i ∈ List.range 4, RunsAt 28 (80+i) := by decide +kernel

private theorem r28part84 : ∀ i ∈ List.range 4, RunsAt 28 (84+i) := by decide +kernel

private theorem r28part88 : ∀ i ∈ List.range 4, RunsAt 28 (88+i) := by decide +kernel

private theorem r28part92 : ∀ i ∈ List.range 4, RunsAt 28 (92+i) := by decide +kernel

private theorem r28part96 : ∀ i ∈ List.range 4, RunsAt 28 (96+i) := by decide +kernel

private theorem r28part100 : ∀ i ∈ List.range 4, RunsAt 28 (100+i) := by decide +kernel

private theorem r28part104 : ∀ i ∈ List.range 4, RunsAt 28 (104+i) := by decide +kernel

private theorem r28part108 : ∀ i ∈ List.range 1, RunsAt 28 (108+i) := by decide +kernel

theorem checkedR28 : ∀ V ∈ List.range 109, RunsAt 28 V := by
  intro V hV
  have hlt : V < 109 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r28part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r28part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r28part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r28part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r28part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r28part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r28part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r28part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r28part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r28part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r28part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r28part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r28part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r28part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r28part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r29part0 : ∀ i ∈ List.range 4, RunsAt 29 (0+i) := by decide +kernel

private theorem r29part4 : ∀ i ∈ List.range 4, RunsAt 29 (4+i) := by decide +kernel

private theorem r29part8 : ∀ i ∈ List.range 4, RunsAt 29 (8+i) := by decide +kernel

private theorem r29part12 : ∀ i ∈ List.range 4, RunsAt 29 (12+i) := by decide +kernel

private theorem r29part16 : ∀ i ∈ List.range 4, RunsAt 29 (16+i) := by decide +kernel

private theorem r29part20 : ∀ i ∈ List.range 4, RunsAt 29 (20+i) := by decide +kernel

private theorem r29part24 : ∀ i ∈ List.range 4, RunsAt 29 (24+i) := by decide +kernel

private theorem r29part28 : ∀ i ∈ List.range 4, RunsAt 29 (28+i) := by decide +kernel

private theorem r29part32 : ∀ i ∈ List.range 4, RunsAt 29 (32+i) := by decide +kernel

private theorem r29part36 : ∀ i ∈ List.range 4, RunsAt 29 (36+i) := by decide +kernel

private theorem r29part40 : ∀ i ∈ List.range 4, RunsAt 29 (40+i) := by decide +kernel

private theorem r29part44 : ∀ i ∈ List.range 4, RunsAt 29 (44+i) := by decide +kernel

private theorem r29part48 : ∀ i ∈ List.range 4, RunsAt 29 (48+i) := by decide +kernel

private theorem r29part52 : ∀ i ∈ List.range 4, RunsAt 29 (52+i) := by decide +kernel

private theorem r29part56 : ∀ i ∈ List.range 4, RunsAt 29 (56+i) := by decide +kernel

private theorem r29part60 : ∀ i ∈ List.range 4, RunsAt 29 (60+i) := by decide +kernel

private theorem r29part64 : ∀ i ∈ List.range 4, RunsAt 29 (64+i) := by decide +kernel

private theorem r29part68 : ∀ i ∈ List.range 4, RunsAt 29 (68+i) := by decide +kernel

private theorem r29part72 : ∀ i ∈ List.range 4, RunsAt 29 (72+i) := by decide +kernel

private theorem r29part76 : ∀ i ∈ List.range 4, RunsAt 29 (76+i) := by decide +kernel

private theorem r29part80 : ∀ i ∈ List.range 4, RunsAt 29 (80+i) := by decide +kernel

private theorem r29part84 : ∀ i ∈ List.range 4, RunsAt 29 (84+i) := by decide +kernel

private theorem r29part88 : ∀ i ∈ List.range 4, RunsAt 29 (88+i) := by decide +kernel

private theorem r29part92 : ∀ i ∈ List.range 4, RunsAt 29 (92+i) := by decide +kernel

private theorem r29part96 : ∀ i ∈ List.range 4, RunsAt 29 (96+i) := by decide +kernel

private theorem r29part100 : ∀ i ∈ List.range 4, RunsAt 29 (100+i) := by decide +kernel

private theorem r29part104 : ∀ i ∈ List.range 4, RunsAt 29 (104+i) := by decide +kernel

theorem checkedR29 : ∀ V ∈ List.range 108, RunsAt 29 V := by
  intro V hV
  have hlt : V < 108 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r29part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r29part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r29part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r29part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r29part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r29part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r29part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r29part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r29part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r29part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r29part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r29part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r29part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  have hp := r29part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r30part0 : ∀ i ∈ List.range 4, RunsAt 30 (0+i) := by decide +kernel

private theorem r30part4 : ∀ i ∈ List.range 4, RunsAt 30 (4+i) := by decide +kernel

private theorem r30part8 : ∀ i ∈ List.range 4, RunsAt 30 (8+i) := by decide +kernel

private theorem r30part12 : ∀ i ∈ List.range 4, RunsAt 30 (12+i) := by decide +kernel

private theorem r30part16 : ∀ i ∈ List.range 4, RunsAt 30 (16+i) := by decide +kernel

private theorem r30part20 : ∀ i ∈ List.range 4, RunsAt 30 (20+i) := by decide +kernel

private theorem r30part24 : ∀ i ∈ List.range 4, RunsAt 30 (24+i) := by decide +kernel

private theorem r30part28 : ∀ i ∈ List.range 4, RunsAt 30 (28+i) := by decide +kernel

private theorem r30part32 : ∀ i ∈ List.range 4, RunsAt 30 (32+i) := by decide +kernel

private theorem r30part36 : ∀ i ∈ List.range 4, RunsAt 30 (36+i) := by decide +kernel

private theorem r30part40 : ∀ i ∈ List.range 4, RunsAt 30 (40+i) := by decide +kernel

private theorem r30part44 : ∀ i ∈ List.range 4, RunsAt 30 (44+i) := by decide +kernel

private theorem r30part48 : ∀ i ∈ List.range 4, RunsAt 30 (48+i) := by decide +kernel

private theorem r30part52 : ∀ i ∈ List.range 4, RunsAt 30 (52+i) := by decide +kernel

private theorem r30part56 : ∀ i ∈ List.range 4, RunsAt 30 (56+i) := by decide +kernel

private theorem r30part60 : ∀ i ∈ List.range 4, RunsAt 30 (60+i) := by decide +kernel

private theorem r30part64 : ∀ i ∈ List.range 4, RunsAt 30 (64+i) := by decide +kernel

private theorem r30part68 : ∀ i ∈ List.range 4, RunsAt 30 (68+i) := by decide +kernel

private theorem r30part72 : ∀ i ∈ List.range 4, RunsAt 30 (72+i) := by decide +kernel

private theorem r30part76 : ∀ i ∈ List.range 4, RunsAt 30 (76+i) := by decide +kernel

private theorem r30part80 : ∀ i ∈ List.range 4, RunsAt 30 (80+i) := by decide +kernel

private theorem r30part84 : ∀ i ∈ List.range 4, RunsAt 30 (84+i) := by decide +kernel

private theorem r30part88 : ∀ i ∈ List.range 4, RunsAt 30 (88+i) := by decide +kernel

private theorem r30part92 : ∀ i ∈ List.range 4, RunsAt 30 (92+i) := by decide +kernel

private theorem r30part96 : ∀ i ∈ List.range 4, RunsAt 30 (96+i) := by decide +kernel

private theorem r30part100 : ∀ i ∈ List.range 4, RunsAt 30 (100+i) := by decide +kernel

private theorem r30part104 : ∀ i ∈ List.range 3, RunsAt 30 (104+i) := by decide +kernel

theorem checkedR30 : ∀ V ∈ List.range 107, RunsAt 30 V := by
  intro V hV
  have hlt : V < 107 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r30part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r30part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r30part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r30part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r30part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r30part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r30part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r30part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r30part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r30part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r30part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r30part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r30part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  have hp := r30part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem checked : ∀ r ∈ List.range 31, 1 ≤ r →
    ∀ v ∈ List.range (137-r), RunsAt r v := by
  intro r hr hpos
  have hlt : r < 31 := List.mem_range.mp hr
  interval_cases r <;> first
    | exact checkedR1
    | exact checkedR2
    | exact checkedR3
    | exact checkedR4
    | exact checkedR5
    | exact checkedR6
    | exact checkedR7
    | exact checkedR8
    | exact checkedR9
    | exact checkedR10
    | exact checkedR11
    | exact checkedR12
    | exact checkedR13
    | exact checkedR14
    | exact checkedR15
    | exact checkedR16
    | exact checkedR17
    | exact checkedR18
    | exact checkedR19
    | exact checkedR20
    | exact checkedR21
    | exact checkedR22
    | exact checkedR23
    | exact checkedR24
    | exact checkedR25
    | exact checkedR26
    | exact checkedR27
    | exact checkedR28
    | exact checkedR29
    | exact checkedR30

end ProximityPrize.SubmissionLower.Lower80791.RunsChecked

end Compact_RunsChecked80791
