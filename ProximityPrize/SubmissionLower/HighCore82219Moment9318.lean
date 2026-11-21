import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part0
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part1
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part2
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part3
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part4
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part5
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part6
import ProximityPrize.SubmissionLower.HighCore82219Moment9318Part7
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)


theorem sum9318_1962_3200 : blockEstimate 9318 1962 1962 3200 = 0x208c9b2850ec :=
  block_append (B := 9318) (J := 1962) (start := 1962) (next := 3562)
    (a := 1600) (b := 1600) (n := 3200) (x := 0x50cdc73e810) (y := 0x1b7fbeb468dc) (z := 0x208c9b2850ec)
    moment9318_group0 moment9318_group1 rfl rfl rfl

theorem sum9318_5162_3200 : blockEstimate 9318 1962 5162 3200 = 0x5db93aae2440 :=
  block_append (B := 9318) (J := 1962) (start := 5162) (next := 6762)
    (a := 1600) (b := 1600) (n := 3200) (x := 0x2d43af984a20) (y := 0x30758b15da20) (z := 0x5db93aae2440)
    moment9318_group2 moment9318_group3 rfl rfl rfl

theorem sum9318_1962_6400 : blockEstimate 9318 1962 1962 6400 = 0x7e45d5d6752c :=
  block_append (B := 9318) (J := 1962) (start := 1962) (next := 5162)
    (a := 3200) (b := 3200) (n := 6400) (x := 0x208c9b2850ec) (y := 0x5db93aae2440) (z := 0x7e45d5d6752c)
    sum9318_1962_3200 sum9318_5162_3200 rfl rfl rfl

theorem sum9318_8362_3200 : blockEstimate 9318 1962 8362 3200 = 0x369e5a9739a7 :=
  block_append (B := 9318) (J := 1962) (start := 8362) (next := 9962)
    (a := 1600) (b := 1600) (n := 3200) (x := 0x2526f973f1c5) (y := 0x1177612347e2) (z := 0x369e5a9739a7)
    moment9318_group4 moment9318_group5 rfl rfl rfl

theorem sum9318_11562_1680 : blockEstimate 9318 1962 11562 1680 = 0x312f8323300 :=
  block_append (B := 9318) (J := 1962) (start := 11562) (next := 13162)
    (a := 1600) (b := 80) (n := 1680) (x := 0x312df3f2b00) (y := 0x18f30800) (z := 0x312f8323300)
    moment9318_group6 moment9318_group7 rfl rfl rfl

theorem sum9318_8362_4880 : blockEstimate 9318 1962 8362 4880 = 0x39b152c96ca7 :=
  block_append (B := 9318) (J := 1962) (start := 8362) (next := 11562)
    (a := 3200) (b := 1680) (n := 4880) (x := 0x369e5a9739a7) (y := 0x312f8323300) (z := 0x39b152c96ca7)
    sum9318_8362_3200 sum9318_11562_1680 rfl rfl rfl

theorem sum9318_1962_11280 : blockEstimate 9318 1962 1962 11280 = 0xb7f7289fe1d3 :=
  block_append (B := 9318) (J := 1962) (start := 1962) (next := 8362)
    (a := 6400) (b := 4880) (n := 11280) (x := 0x7e45d5d6752c) (y := 0x39b152c96ca7) (z := 0xb7f7289fe1d3)
    sum9318_1962_6400 sum9318_8362_4880 rfl rfl rfl

theorem moment9318_1962 : momentEstimate 9318 1962 = 0xb7f7289fe1d3 := sum9318_1962_11280

#print axioms moment9318_1962
end HighCore82219BankProof
