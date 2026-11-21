import ProximityPrize.SubmissionLower.UpperBranch1
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part2

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


private theorem block9318_15 : blockEstimate 9318 1962 6762 320 = 0x9e77df90ba0 := by decide +kernel

private theorem block9318_16 : blockEstimate 9318 1962 7082 320 = 0x9ea40dd1ba0 := by decide +kernel

private theorem block9318_17 : blockEstimate 9318 1962 7402 320 = 0x9cf0fc92ba0 := by decide +kernel

private theorem block9318_18 : blockEstimate 9318 1962 7722 320 = 0x995eabd3ba0 := by decide +kernel

private theorem block9318_19 : blockEstimate 9318 1962 8042 320 = 0x93ed1b94ba0 := by decide +kernel

theorem sum9318_6762_640 : blockEstimate 9318 1962 6762 640 = 0x13d1bed62740 :=
  block_append (B := 9318) (J := 1962) (start := 6762) (next := 7082)
    (a := 320) (b := 320) (n := 640) (x := 0x9e77df90ba0) (y := 0x9ea40dd1ba0) (z := 0x13d1bed62740)
    block9318_15 block9318_16 rfl rfl rfl

theorem sum9318_7722_640 : blockEstimate 9318 1962 7722 640 = 0x12d4bc768740 :=
  block_append (B := 9318) (J := 1962) (start := 7722) (next := 8042)
    (a := 320) (b := 320) (n := 640) (x := 0x995eabd3ba0) (y := 0x93ed1b94ba0) (z := 0x12d4bc768740)
    block9318_18 block9318_19 rfl rfl rfl

theorem sum9318_7402_960 : blockEstimate 9318 1962 7402 960 = 0x1ca3cc3fb2e0 :=
  block_append (B := 9318) (J := 1962) (start := 7402) (next := 7722)
    (a := 320) (b := 640) (n := 960) (x := 0x9cf0fc92ba0) (y := 0x12d4bc768740) (z := 0x1ca3cc3fb2e0)
    block9318_17 sum9318_7722_640 rfl rfl rfl

theorem moment9318_group3 : blockEstimate 9318 1962 6762 1600 = 0x30758b15da20 :=
  block_append (B := 9318) (J := 1962) (start := 6762) (next := 7402)
    (a := 640) (b := 960) (n := 1600) (x := 0x13d1bed62740) (y := 0x1ca3cc3fb2e0) (z := 0x30758b15da20)
    sum9318_6762_640 sum9318_7402_960 rfl rfl rfl

end HighCore82219BankProof
