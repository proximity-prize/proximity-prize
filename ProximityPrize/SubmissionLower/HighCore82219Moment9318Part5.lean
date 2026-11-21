import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem block9318_25 : blockEstimate 9318 1962 9962 320 = 0x50faf5831d7 := by decide +kernel

theorem block9318_26 : blockEstimate 9318 1962 10282 320 = 0x43ce6bfdeb6 := by decide +kernel

theorem block9318_27 : blockEstimate 9318 1962 10602 320 = 0x37229927a3c := by decide +kernel

theorem block9318_28 : blockEstimate 9318 1962 10922 320 = 0x2b3c3555ade := by decide +kernel

theorem block9318_29 : blockEstimate 9318 1962 11242 320 = 0x204de23623b := by decide +kernel

theorem sum9318_9962_640 : blockEstimate 9318 1962 9962 640 = 0x94c9618108d :=
  block_append (B := 9318) (J := 1962) (start := 9962) (next := 10282)
    (a := 320) (b := 320) (n := 640) (x := 0x50faf5831d7) (y := 0x43ce6bfdeb6) (z := 0x94c9618108d)
    block9318_25 block9318_26 rfl rfl rfl

theorem sum9318_10922_640 : blockEstimate 9318 1962 10922 640 = 0x4b8a178bd19 :=
  block_append (B := 9318) (J := 1962) (start := 10922) (next := 11242)
    (a := 320) (b := 320) (n := 640) (x := 0x2b3c3555ade) (y := 0x204de23623b) (z := 0x4b8a178bd19)
    block9318_28 block9318_29 rfl rfl rfl

theorem sum9318_10602_960 : blockEstimate 9318 1962 10602 960 = 0x82acb0b3755 :=
  block_append (B := 9318) (J := 1962) (start := 10602) (next := 10922)
    (a := 320) (b := 640) (n := 960) (x := 0x37229927a3c) (y := 0x4b8a178bd19) (z := 0x82acb0b3755)
    block9318_27 sum9318_10922_640 rfl rfl rfl

theorem moment9318_group5 : blockEstimate 9318 1962 9962 1600 = 0x1177612347e2 :=
  block_append (B := 9318) (J := 1962) (start := 9962) (next := 10602)
    (a := 640) (b := 960) (n := 1600) (x := 0x94c9618108d) (y := 0x82acb0b3755) (z := 0x1177612347e2)
    sum9318_9962_640 sum9318_10602_960 rfl rfl rfl

end HighCore82219BankProof
