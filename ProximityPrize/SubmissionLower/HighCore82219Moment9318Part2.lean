import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem block9318_10 : blockEstimate 9318 1962 5162 320 = 0x81863fcbba0 := by decide +kernel

theorem block9318_11 : blockEstimate 9318 1962 5482 320 = 0x8b0eab8cba0 := by decide +kernel

theorem block9318_12 : blockEstimate 9318 1962 5802 320 = 0x92b7d7cdba0 := by decide +kernel

theorem block9318_13 : blockEstimate 9318 1962 6122 320 = 0x9881c48eba0 := by decide +kernel

theorem block9318_14 : blockEstimate 9318 1962 6442 320 = 0x9c6c71cfba0 := by decide +kernel

theorem sum9318_5162_640 : blockEstimate 9318 1962 5162 640 = 0x10c94eb58740 :=
  block_append (B := 9318) (J := 1962) (start := 5162) (next := 5482)
    (a := 320) (b := 320) (n := 640) (x := 0x81863fcbba0) (y := 0x8b0eab8cba0) (z := 0x10c94eb58740)
    block9318_10 block9318_11 rfl rfl rfl

theorem sum9318_6122_640 : blockEstimate 9318 1962 6122 640 = 0x134ee365e740 :=
  block_append (B := 9318) (J := 1962) (start := 6122) (next := 6442)
    (a := 320) (b := 320) (n := 640) (x := 0x9881c48eba0) (y := 0x9c6c71cfba0) (z := 0x134ee365e740)
    block9318_13 block9318_14 rfl rfl rfl

theorem sum9318_5802_960 : blockEstimate 9318 1962 5802 960 = 0x1c7a60e2c2e0 :=
  block_append (B := 9318) (J := 1962) (start := 5802) (next := 6122)
    (a := 320) (b := 640) (n := 960) (x := 0x92b7d7cdba0) (y := 0x134ee365e740) (z := 0x1c7a60e2c2e0)
    block9318_12 sum9318_6122_640 rfl rfl rfl

theorem moment9318_group2 : blockEstimate 9318 1962 5162 1600 = 0x2d43af984a20 :=
  block_append (B := 9318) (J := 1962) (start := 5162) (next := 5802)
    (a := 640) (b := 960) (n := 1600) (x := 0x10c94eb58740) (y := 0x1c7a60e2c2e0) (z := 0x2d43af984a20)
    sum9318_5162_640 sum9318_5802_960 rfl rfl rfl

end HighCore82219BankProof
