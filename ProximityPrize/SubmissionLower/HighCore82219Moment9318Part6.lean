import ProximityPrize.SubmissionLower.UpperBranch1
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part5

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


private theorem block9318_30 : blockEstimate 9318 1962 11562 320 = 0x169deef8f00 := by decide +kernel

private theorem block9318_31 : blockEstimate 9318 1962 11882 320 = 0xe7857bdf00 := by decide +kernel

private theorem block9318_32 : blockEstimate 9318 1962 12202 320 = 0x8020f8cf00 := by decide +kernel

private theorem block9318_33 : blockEstimate 9318 1962 12522 320 = 0x35fb565f00 := by decide +kernel

private theorem block9318_34 : blockEstimate 9318 1962 12842 320 = 0xb5e848f00 := by decide +kernel

theorem sum9318_11562_640 : blockEstimate 9318 1962 11562 640 = 0x251646b6e00 :=
  block_append (B := 9318) (J := 1962) (start := 11562) (next := 11882)
    (a := 320) (b := 320) (n := 640) (x := 0x169deef8f00) (y := 0xe7857bdf00) (z := 0x251646b6e00)
    block9318_30 block9318_31 rfl rfl rfl

theorem sum9318_12522_640 : blockEstimate 9318 1962 12522 640 = 0x4159daee00 :=
  block_append (B := 9318) (J := 1962) (start := 12522) (next := 12842)
    (a := 320) (b := 320) (n := 640) (x := 0x35fb565f00) (y := 0xb5e848f00) (z := 0x4159daee00)
    block9318_33 block9318_34 rfl rfl rfl

theorem sum9318_12202_960 : blockEstimate 9318 1962 12202 960 = 0xc17ad3bd00 :=
  block_append (B := 9318) (J := 1962) (start := 12202) (next := 12522)
    (a := 320) (b := 640) (n := 960) (x := 0x8020f8cf00) (y := 0x4159daee00) (z := 0xc17ad3bd00)
    block9318_32 sum9318_12522_640 rfl rfl rfl

theorem moment9318_group6 : blockEstimate 9318 1962 11562 1600 = 0x312df3f2b00 :=
  block_append (B := 9318) (J := 1962) (start := 11562) (next := 12202)
    (a := 640) (b := 960) (n := 1600) (x := 0x251646b6e00) (y := 0xc17ad3bd00) (z := 0x312df3f2b00)
    sum9318_11562_640 sum9318_12202_960 rfl rfl rfl

end HighCore82219BankProof
