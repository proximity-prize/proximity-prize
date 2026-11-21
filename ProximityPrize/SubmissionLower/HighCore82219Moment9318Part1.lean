import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem block9318_5 : blockEstimate 9318 1962 3562 320 = 0x36a7c0ae0d0 := by decide +kernel

theorem block9318_6 : blockEstimate 9318 1962 3882 320 = 0x48ac6cbb52c := by decide +kernel

theorem block9318_7 : blockEstimate 9318 1962 4202 320 = 0x59b17f88ba0 := by decide +kernel

theorem block9318_8 : blockEstimate 9318 1962 4522 320 = 0x68d7a9c9ba0 := by decide +kernel

theorem block9318_9 : blockEstimate 9318 1962 4842 320 = 0x761e948aba0 := by decide +kernel

theorem sum9318_3562_640 : blockEstimate 9318 1962 3562 640 = 0x7f542d695fc :=
  block_append (B := 9318) (J := 1962) (start := 3562) (next := 3882)
    (a := 320) (b := 320) (n := 640) (x := 0x36a7c0ae0d0) (y := 0x48ac6cbb52c) (z := 0x7f542d695fc)
    block9318_5 block9318_6 rfl rfl rfl

theorem sum9318_4522_640 : blockEstimate 9318 1962 4522 640 = 0xdef63e54740 :=
  block_append (B := 9318) (J := 1962) (start := 4522) (next := 4842)
    (a := 320) (b := 320) (n := 640) (x := 0x68d7a9c9ba0) (y := 0x761e948aba0) (z := 0xdef63e54740)
    block9318_8 block9318_9 rfl rfl rfl

theorem sum9318_4202_960 : blockEstimate 9318 1962 4202 960 = 0x138a7bddd2e0 :=
  block_append (B := 9318) (J := 1962) (start := 4202) (next := 4522)
    (a := 320) (b := 640) (n := 960) (x := 0x59b17f88ba0) (y := 0xdef63e54740) (z := 0x138a7bddd2e0)
    block9318_7 sum9318_4522_640 rfl rfl rfl

theorem moment9318_group1 : blockEstimate 9318 1962 3562 1600 = 0x1b7fbeb468dc :=
  block_append (B := 9318) (J := 1962) (start := 3562) (next := 4202)
    (a := 640) (b := 960) (n := 1600) (x := 0x7f542d695fc) (y := 0x138a7bddd2e0) (z := 0x1b7fbeb468dc)
    sum9318_3562_640 sum9318_4202_960 rfl rfl rfl

end HighCore82219BankProof
