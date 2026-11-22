import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem block9318_0 : blockEstimate 9318 1962 1962 320 = 0xba7160cd0 := by decide +kernel

theorem block9318_1 : blockEstimate 9318 1962 2282 320 = 0x4eae7fd0d0 := by decide +kernel

theorem block9318_2 : blockEstimate 9318 1962 2602 320 = 0xcdcdb394d0 := by decide +kernel

theorem block9318_3 : blockEstimate 9318 1962 2922 320 = 0x181b1b158d0 := by decide +kernel

theorem block9318_4 : blockEstimate 9318 1962 3242 320 = 0x26307791cd0 := by decide +kernel

theorem sum9318_1962_640 : blockEstimate 9318 1962 1962 640 = 0x5a5595dda0 :=
  block_append (B := 9318) (J := 1962) (start := 1962) (next := 2282)
    (a := 320) (b := 320) (n := 640) (x := 0xba7160cd0) (y := 0x4eae7fd0d0) (z := 0x5a5595dda0)
    block9318_0 block9318_1 rfl rfl rfl

theorem sum9318_2922_640 : blockEstimate 9318 1962 2922 640 = 0x3e4b92a75a0 :=
  block_append (B := 9318) (J := 1962) (start := 2922) (next := 3242)
    (a := 320) (b := 320) (n := 640) (x := 0x181b1b158d0) (y := 0x26307791cd0) (z := 0x3e4b92a75a0)
    block9318_3 block9318_4 rfl rfl rfl

theorem sum9318_2602_960 : blockEstimate 9318 1962 2602 960 = 0x4b286de0a70 :=
  block_append (B := 9318) (J := 1962) (start := 2602) (next := 2922)
    (a := 320) (b := 640) (n := 960) (x := 0xcdcdb394d0) (y := 0x3e4b92a75a0) (z := 0x4b286de0a70)
    block9318_2 sum9318_2922_640 rfl rfl rfl

theorem moment9318_group0 : blockEstimate 9318 1962 1962 1600 = 0x50cdc73e810 :=
  block_append (B := 9318) (J := 1962) (start := 1962) (next := 2602)
    (a := 640) (b := 960) (n := 1600) (x := 0x5a5595dda0) (y := 0x4b286de0a70) (z := 0x50cdc73e810)
    sum9318_1962_640 sum9318_2602_960 rfl rfl rfl

end HighCore82219BankProof
