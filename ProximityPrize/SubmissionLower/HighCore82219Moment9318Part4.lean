import ProximityPrize.SubmissionLower.UpperBranch1
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part3

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


private theorem block9318_20 : blockEstimate 9318 1962 8362 320 = 0x8c9c4bd5ba0 := by decide +kernel

private theorem block9318_21 : blockEstimate 9318 1962 8682 320 = 0x836c3c96ba0 := by decide +kernel

private theorem block9318_22 : blockEstimate 9318 1962 9002 320 = 0x785cede0f3b := by decide +kernel

private theorem block9318_23 : blockEstimate 9318 1962 9322 320 = 0x6bab6a2e1b2 := by decide +kernel

private theorem block9318_24 : blockEstimate 9318 1962 9642 320 = 0x5e5eb6c3998 := by decide +kernel

theorem sum9318_8362_640 : blockEstimate 9318 1962 8362 640 = 0x11008886c740 :=
  block_append (B := 9318) (J := 1962) (start := 8362) (next := 8682)
    (a := 320) (b := 320) (n := 640) (x := 0x8c9c4bd5ba0) (y := 0x836c3c96ba0) (z := 0x11008886c740)
    block9318_20 block9318_21 rfl rfl rfl

theorem sum9318_9322_640 : blockEstimate 9318 1962 9322 640 = 0xca0a20f1b4a :=
  block_append (B := 9318) (J := 1962) (start := 9322) (next := 9642)
    (a := 320) (b := 320) (n := 640) (x := 0x6bab6a2e1b2) (y := 0x5e5eb6c3998) (z := 0xca0a20f1b4a)
    block9318_23 block9318_24 rfl rfl rfl

theorem sum9318_9002_960 : blockEstimate 9318 1962 9002 960 = 0x142670ed2a85 :=
  block_append (B := 9318) (J := 1962) (start := 9002) (next := 9322)
    (a := 320) (b := 640) (n := 960) (x := 0x785cede0f3b) (y := 0xca0a20f1b4a) (z := 0x142670ed2a85)
    block9318_22 sum9318_9322_640 rfl rfl rfl

theorem moment9318_group4 : blockEstimate 9318 1962 8362 1600 = 0x2526f973f1c5 :=
  block_append (B := 9318) (J := 1962) (start := 8362) (next := 9002)
    (a := 640) (b := 960) (n := 1600) (x := 0x11008886c740) (y := 0x142670ed2a85) (z := 0x2526f973f1c5)
    sum9318_8362_640 sum9318_9002_960 rfl rfl rfl

end HighCore82219BankProof
