import ProximityPrize.SubmissionLower.HighCore82219Moment9318
import ProximityPrize.SubmissionLower.HighCore82219Moments4

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000


private theorem part9814_2080_0 : blockEstimate 9814 2080 2080 220 = 0x40ab238b1 := by decide +kernel
private theorem part9814_2080_1 : blockEstimate 9814 2080 2300 220 = 0x1b865ce175 := by decide +kernel
private theorem part9814_2080_2 : blockEstimate 9814 2080 2520 220 = 0x48e1686599 := by decide +kernel
private theorem part9814_2080_3 : blockEstimate 9814 2080 2740 220 = 0x8a78f2e21d := by decide +kernel
private theorem part9814_2080_4 : blockEstimate 9814 2080 2960 220 = 0xdeaa1a7401 := by decide +kernel
private theorem part9814_2080_5 : blockEstimate 9814 2080 3180 220 = 0x143d1fd3845 := by decide +kernel
private theorem part9814_2080_6 : blockEstimate 9814 2080 3400 220 = 0x1b84db94be9 := by decide +kernel
private theorem part9814_2080_7 : blockEstimate 9814 2080 3620 220 = 0x23a7a6ccbed := by decide +kernel
private theorem part9814_2080_8 : blockEstimate 9814 2080 3840 220 = 0x2c8b535d551 := by decide +kernel
private theorem part9814_2080_9 : blockEstimate 9814 2080 4060 220 = 0x360d7fadbcf := by decide +kernel
private theorem part9814_2080_10 : blockEstimate 9814 2080 4280 220 = 0x3f7e45fdfb8 := by decide +kernel
private theorem part9814_2080_11 : blockEstimate 9814 2080 4500 220 = 0x484ecd81998 := by decide +kernel
private theorem part9814_2080_12 : blockEstimate 9814 2080 4720 220 = 0x507a3d0eff8 := by decide +kernel
private theorem part9814_2080_13 : blockEstimate 9814 2080 4940 220 = 0x580094a62d8 := by decide +kernel
private theorem part9814_2080_14 : blockEstimate 9814 2080 5160 220 = 0x5ee1d447238 := by decide +kernel
private theorem part9814_2080_15 : blockEstimate 9814 2080 5380 220 = 0x651dfbf1e18 := by decide +kernel
private theorem part9814_2080_16 : blockEstimate 9814 2080 5600 220 = 0x6ab50ba6678 := by decide +kernel
private theorem part9814_2080_17 : blockEstimate 9814 2080 5820 220 = 0x6fa70364b58 := by decide +kernel
private theorem part9814_2080_18 : blockEstimate 9814 2080 6040 220 = 0x73f3e32ccb8 := by decide +kernel
private theorem part9814_2080_19 : blockEstimate 9814 2080 6260 220 = 0x779baafea98 := by decide +kernel
private theorem part9814_2080_20 : blockEstimate 9814 2080 6480 220 = 0x7a9e5ada4f8 := by decide +kernel
private theorem part9814_2080_21 : blockEstimate 9814 2080 6700 220 = 0x7cfbf2bfbd8 := by decide +kernel
private theorem part9814_2080_22 : blockEstimate 9814 2080 6920 220 = 0x7eb472aef38 := by decide +kernel
private theorem part9814_2080_23 : blockEstimate 9814 2080 7140 220 = 0x7fc7daa7f18 := by decide +kernel
private theorem part9814_2080_24 : blockEstimate 9814 2080 7360 220 = 0x80362aaab78 := by decide +kernel
private theorem part9814_2080_25 : blockEstimate 9814 2080 7580 220 = 0x7fff62b7458 := by decide +kernel
private theorem part9814_2080_26 : blockEstimate 9814 2080 7800 220 = 0x7f2382cd9b8 := by decide +kernel
private theorem part9814_2080_27 : blockEstimate 9814 2080 8020 220 = 0x7da28aedb98 := by decide +kernel
private theorem part9814_2080_28 : blockEstimate 9814 2080 8240 220 = 0x7b7c7b179f8 := by decide +kernel
private theorem part9814_2080_29 : blockEstimate 9814 2080 8460 220 = 0x78b1534b4d8 := by decide +kernel
private theorem part9814_2080_30 : blockEstimate 9814 2080 8680 220 = 0x75411388c38 := by decide +kernel
private theorem part9814_2080_31 : blockEstimate 9814 2080 8900 220 = 0x712bbbd0018 := by decide +kernel
private theorem part9814_2080_32 : blockEstimate 9814 2080 9120 220 = 0x6c714c21078 := by decide +kernel
private theorem part9814_2080_33 : blockEstimate 9814 2080 9340 220 = 0x6711c47bd58 := by decide +kernel
private theorem part9814_2080_34 : blockEstimate 9814 2080 9560 220 = 0x610d24e06b8 := by decide +kernel
private theorem part9814_2080_35 : blockEstimate 9814 2080 9780 220 = 0x5a6f3b34db4 := by decide +kernel
private theorem part9814_2080_36 : blockEstimate 9814 2080 10000 220 = 0x53881cd8677 := by decide +kernel
private theorem part9814_2080_37 : blockEstimate 9814 2080 10220 220 = 0x4c85b61aeb1 := by decide +kernel
private theorem part9814_2080_38 : blockEstimate 9814 2080 10440 220 = 0x457a7304efe := by decide +kernel
private theorem part9814_2080_39 : blockEstimate 9814 2080 10660 220 = 0x3e77fdbf67d := by decide +kernel
private theorem part9814_2080_40 : blockEstimate 9814 2080 10880 220 = 0x378f4f50528 := by decide +kernel
private theorem part9814_2080_41 : blockEstimate 9814 2080 11100 220 = 0x30d0af9b61e := by decide +kernel
private theorem part9814_2080_42 : blockEstimate 9814 2080 11320 220 = 0x2a4bb56233a := by decide +kernel
private theorem part9814_2080_43 : blockEstimate 9814 2080 11540 220 = 0x240f46437b8 := by decide +kernel
private theorem part9814_2080_44 : blockEstimate 9814 2080 11760 220 = 0x1e27d9f0ece := by decide +kernel
private theorem part9814_2080_45 : blockEstimate 9814 2080 11980 220 = 0x18986b8b3f0 := by decide +kernel
private theorem part9814_2080_46 : blockEstimate 9814 2080 12200 220 = 0x1380700d6bb := by decide +kernel
private theorem part9814_2080_47 : blockEstimate 9814 2080 12420 220 = 0xeed311fb44 := by decide +kernel
private theorem part9814_2080_48 : blockEstimate 9814 2080 12640 220 = 0xae6dd2b87b := by decide +kernel
private theorem part9814_2080_49 : blockEstimate 9814 2080 12860 220 = 0x775a29a550 := by decide +kernel
private theorem part9814_2080_50 : blockEstimate 9814 2080 13080 220 = 0x4a1afd58b3 := by decide +kernel
private theorem part9814_2080_51 : blockEstimate 9814 2080 13300 220 = 0x2733346994 := by decide +kernel
private theorem part9814_2080_52 : blockEstimate 9814 2080 13520 220 = 0xf25b56ee3 := by decide +kernel
private theorem part9814_2080_53 : blockEstimate 9814 2080 13740 220 = 0x27566ff90 := by decide +kernel
private theorem part9814_2080_54 : blockEstimate 9814 2080 13960 14 = 0x2e1856 := by decide +kernel

private theorem sum9814_2080_2300_440 : blockEstimate 9814 2080 2300 440 = 0x6467c5470e :=
  block_append (B := 9814) (J := 2080) (start := 2300) (next := 2520)
    (a := 220) (b := 220) (n := 440) (x := 0x1b865ce175) (y := 0x48e1686599) (z := 0x6467c5470e)
    part9814_2080_1 part9814_2080_2 rfl rfl rfl

private theorem sum9814_2080_2080_660 : blockEstimate 9814 2080 2080 660 = 0x6872777fbf :=
  block_append (B := 9814) (J := 2080) (start := 2080) (next := 2300)
    (a := 220) (b := 440) (n := 660) (x := 0x40ab238b1) (y := 0x6467c5470e) (z := 0x6872777fbf)
    part9814_2080_0 sum9814_2080_2300_440 rfl rfl rfl

private theorem sum9814_2080_2960_440 : blockEstimate 9814 2080 2960 440 = 0x2227c17ac46 :=
  block_append (B := 9814) (J := 2080) (start := 2960) (next := 3180)
    (a := 220) (b := 220) (n := 440) (x := 0xdeaa1a7401) (y := 0x143d1fd3845) (z := 0x2227c17ac46)
    part9814_2080_4 part9814_2080_5 rfl rfl rfl

private theorem sum9814_2080_2740_660 : blockEstimate 9814 2080 2740 660 = 0x2acf50a8e63 :=
  block_append (B := 9814) (J := 2080) (start := 2740) (next := 2960)
    (a := 220) (b := 440) (n := 660) (x := 0x8a78f2e21d) (y := 0x2227c17ac46) (z := 0x2acf50a8e63)
    part9814_2080_3 sum9814_2080_2960_440 rfl rfl rfl

private theorem sum9814_2080_2080_1320 : blockEstimate 9814 2080 2080 1320 = 0x31567820e22 :=
  block_append (B := 9814) (J := 2080) (start := 2080) (next := 2740)
    (a := 660) (b := 660) (n := 1320) (x := 0x6872777fbf) (y := 0x2acf50a8e63) (z := 0x31567820e22)
    sum9814_2080_2080_660 sum9814_2080_2740_660 rfl rfl rfl

private theorem sum9814_2080_3620_440 : blockEstimate 9814 2080 3620 440 = 0x5032fa2a13e :=
  block_append (B := 9814) (J := 2080) (start := 3620) (next := 3840)
    (a := 220) (b := 220) (n := 440) (x := 0x23a7a6ccbed) (y := 0x2c8b535d551) (z := 0x5032fa2a13e)
    part9814_2080_7 part9814_2080_8 rfl rfl rfl

private theorem sum9814_2080_3400_660 : blockEstimate 9814 2080 3400 660 = 0x6bb7d5bed27 :=
  block_append (B := 9814) (J := 2080) (start := 3400) (next := 3620)
    (a := 220) (b := 440) (n := 660) (x := 0x1b84db94be9) (y := 0x5032fa2a13e) (z := 0x6bb7d5bed27)
    part9814_2080_6 sum9814_2080_3620_440 rfl rfl rfl

private theorem sum9814_2080_4060_440 : blockEstimate 9814 2080 4060 440 = 0x758bc5abb87 :=
  block_append (B := 9814) (J := 2080) (start := 4060) (next := 4280)
    (a := 220) (b := 220) (n := 440) (x := 0x360d7fadbcf) (y := 0x3f7e45fdfb8) (z := 0x758bc5abb87)
    part9814_2080_9 part9814_2080_10 rfl rfl rfl

private theorem sum9814_2080_4500_440 : blockEstimate 9814 2080 4500 440 = 0x98c90a90990 :=
  block_append (B := 9814) (J := 2080) (start := 4500) (next := 4720)
    (a := 220) (b := 220) (n := 440) (x := 0x484ecd81998) (y := 0x507a3d0eff8) (z := 0x98c90a90990)
    part9814_2080_11 part9814_2080_12 rfl rfl rfl

private theorem sum9814_2080_4060_880 : blockEstimate 9814 2080 4060 880 = 0x10e54d03c517 :=
  block_append (B := 9814) (J := 2080) (start := 4060) (next := 4500)
    (a := 440) (b := 440) (n := 880) (x := 0x758bc5abb87) (y := 0x98c90a90990) (z := 0x10e54d03c517)
    sum9814_2080_4060_440 sum9814_2080_4500_440 rfl rfl rfl

private theorem sum9814_2080_3400_1540 : blockEstimate 9814 2080 3400 1540 = 0x17a0ca5fb23e :=
  block_append (B := 9814) (J := 2080) (start := 3400) (next := 4060)
    (a := 660) (b := 880) (n := 1540) (x := 0x6bb7d5bed27) (y := 0x10e54d03c517) (z := 0x17a0ca5fb23e)
    sum9814_2080_3400_660 sum9814_2080_4060_880 rfl rfl rfl

private theorem sum9814_2080_2080_2860 : blockEstimate 9814 2080 2080 2860 = 0x1ab631e1c060 :=
  block_append (B := 9814) (J := 2080) (start := 2080) (next := 3400)
    (a := 1320) (b := 1540) (n := 2860) (x := 0x31567820e22) (y := 0x17a0ca5fb23e) (z := 0x1ab631e1c060)
    sum9814_2080_2080_1320 sum9814_2080_3400_1540 rfl rfl rfl

private theorem sum9814_2080_5160_440 : blockEstimate 9814 2080 5160 440 = 0xc3ffd039050 :=
  block_append (B := 9814) (J := 2080) (start := 5160) (next := 5380)
    (a := 220) (b := 220) (n := 440) (x := 0x5ee1d447238) (y := 0x651dfbf1e18) (z := 0xc3ffd039050)
    part9814_2080_14 part9814_2080_15 rfl rfl rfl

private theorem sum9814_2080_4940_660 : blockEstimate 9814 2080 4940 660 = 0x11c0064df328 :=
  block_append (B := 9814) (J := 2080) (start := 4940) (next := 5160)
    (a := 220) (b := 440) (n := 660) (x := 0x580094a62d8) (y := 0xc3ffd039050) (z := 0x11c0064df328)
    part9814_2080_13 sum9814_2080_5160_440 rfl rfl rfl

private theorem sum9814_2080_5600_440 : blockEstimate 9814 2080 5600 440 = 0xda5c0f0b1d0 :=
  block_append (B := 9814) (J := 2080) (start := 5600) (next := 5820)
    (a := 220) (b := 220) (n := 440) (x := 0x6ab50ba6678) (y := 0x6fa70364b58) (z := 0xda5c0f0b1d0)
    part9814_2080_16 part9814_2080_17 rfl rfl rfl

private theorem sum9814_2080_6040_440 : blockEstimate 9814 2080 6040 440 = 0xeb8f8e2b750 :=
  block_append (B := 9814) (J := 2080) (start := 6040) (next := 6260)
    (a := 220) (b := 220) (n := 440) (x := 0x73f3e32ccb8) (y := 0x779baafea98) (z := 0xeb8f8e2b750)
    part9814_2080_18 part9814_2080_19 rfl rfl rfl

private theorem sum9814_2080_5600_880 : blockEstimate 9814 2080 5600 880 = 0x1c5eb9d36920 :=
  block_append (B := 9814) (J := 2080) (start := 5600) (next := 6040)
    (a := 440) (b := 440) (n := 880) (x := 0xda5c0f0b1d0) (y := 0xeb8f8e2b750) (z := 0x1c5eb9d36920)
    sum9814_2080_5600_440 sum9814_2080_6040_440 rfl rfl rfl

private theorem sum9814_2080_4940_1540 : blockEstimate 9814 2080 4940 1540 = 0x2e1ec0215c48 :=
  block_append (B := 9814) (J := 2080) (start := 4940) (next := 5600)
    (a := 660) (b := 880) (n := 1540) (x := 0x11c0064df328) (y := 0x1c5eb9d36920) (z := 0x2e1ec0215c48)
    sum9814_2080_4940_660 sum9814_2080_5600_880 rfl rfl rfl

private theorem sum9814_2080_6700_440 : blockEstimate 9814 2080 6700 440 = 0xfbb0656eb10 :=
  block_append (B := 9814) (J := 2080) (start := 6700) (next := 6920)
    (a := 220) (b := 220) (n := 440) (x := 0x7cfbf2bfbd8) (y := 0x7eb472aef38) (z := 0xfbb0656eb10)
    part9814_2080_21 part9814_2080_22 rfl rfl rfl

private theorem sum9814_2080_6480_660 : blockEstimate 9814 2080 6480 660 = 0x1764ec049008 :=
  block_append (B := 9814) (J := 2080) (start := 6480) (next := 6700)
    (a := 220) (b := 440) (n := 660) (x := 0x7a9e5ada4f8) (y := 0xfbb0656eb10) (z := 0x1764ec049008)
    part9814_2080_20 sum9814_2080_6700_440 rfl rfl rfl

private theorem sum9814_2080_7140_440 : blockEstimate 9814 2080 7140 440 = 0xfffe0552a90 :=
  block_append (B := 9814) (J := 2080) (start := 7140) (next := 7360)
    (a := 220) (b := 220) (n := 440) (x := 0x7fc7daa7f18) (y := 0x80362aaab78) (z := 0xfffe0552a90)
    part9814_2080_23 part9814_2080_24 rfl rfl rfl

private theorem sum9814_2080_7580_440 : blockEstimate 9814 2080 7580 440 = 0xff22e584e10 :=
  block_append (B := 9814) (J := 2080) (start := 7580) (next := 7800)
    (a := 220) (b := 220) (n := 440) (x := 0x7fff62b7458) (y := 0x7f2382cd9b8) (z := 0xff22e584e10)
    part9814_2080_25 part9814_2080_26 rfl rfl rfl

private theorem sum9814_2080_7140_880 : blockEstimate 9814 2080 7140 880 = 0x1ff20ead78a0 :=
  block_append (B := 9814) (J := 2080) (start := 7140) (next := 7580)
    (a := 440) (b := 440) (n := 880) (x := 0xfffe0552a90) (y := 0xff22e584e10) (z := 0x1ff20ead78a0)
    sum9814_2080_7140_440 sum9814_2080_7580_440 rfl rfl rfl

private theorem sum9814_2080_6480_1540 : blockEstimate 9814 2080 6480 1540 = 0x3756fab208a8 :=
  block_append (B := 9814) (J := 2080) (start := 6480) (next := 7140)
    (a := 660) (b := 880) (n := 1540) (x := 0x1764ec049008) (y := 0x1ff20ead78a0) (z := 0x3756fab208a8)
    sum9814_2080_6480_660 sum9814_2080_7140_880 rfl rfl rfl

private theorem sum9814_2080_4940_3080 : blockEstimate 9814 2080 4940 3080 = 0x6575bad364f0 :=
  block_append (B := 9814) (J := 2080) (start := 4940) (next := 6480)
    (a := 1540) (b := 1540) (n := 3080) (x := 0x2e1ec0215c48) (y := 0x3756fab208a8) (z := 0x6575bad364f0)
    sum9814_2080_4940_1540 sum9814_2080_6480_1540 rfl rfl rfl

private theorem sum9814_2080_2080_5940 : blockEstimate 9814 2080 2080 5940 = 0x802becb52550 :=
  block_append (B := 9814) (J := 2080) (start := 2080) (next := 4940)
    (a := 2860) (b := 3080) (n := 5940) (x := 0x1ab631e1c060) (y := 0x6575bad364f0) (z := 0x802becb52550)
    sum9814_2080_2080_2860 sum9814_2080_4940_3080 rfl rfl rfl

private theorem sum9814_2080_8240_440 : blockEstimate 9814 2080 8240 440 = 0xf42dce62ed0 :=
  block_append (B := 9814) (J := 2080) (start := 8240) (next := 8460)
    (a := 220) (b := 220) (n := 440) (x := 0x7b7c7b179f8) (y := 0x78b1534b4d8) (z := 0xf42dce62ed0)
    part9814_2080_28 part9814_2080_29 rfl rfl rfl

private theorem sum9814_2080_8020_660 : blockEstimate 9814 2080 8020 660 = 0x171d05950a68 :=
  block_append (B := 9814) (J := 2080) (start := 8020) (next := 8240)
    (a := 220) (b := 440) (n := 660) (x := 0x7da28aedb98) (y := 0xf42dce62ed0) (z := 0x171d05950a68)
    part9814_2080_27 sum9814_2080_8240_440 rfl rfl rfl

private theorem sum9814_2080_8680_440 : blockEstimate 9814 2080 8680 440 = 0xe66ccf58c50 :=
  block_append (B := 9814) (J := 2080) (start := 8680) (next := 8900)
    (a := 220) (b := 220) (n := 440) (x := 0x75411388c38) (y := 0x712bbbd0018) (z := 0xe66ccf58c50)
    part9814_2080_30 part9814_2080_31 rfl rfl rfl

private theorem sum9814_2080_9120_440 : blockEstimate 9814 2080 9120 440 = 0xd383109cdd0 :=
  block_append (B := 9814) (J := 2080) (start := 9120) (next := 9340)
    (a := 220) (b := 220) (n := 440) (x := 0x6c714c21078) (y := 0x6711c47bd58) (z := 0xd383109cdd0)
    part9814_2080_32 part9814_2080_33 rfl rfl rfl

private theorem sum9814_2080_8680_880 : blockEstimate 9814 2080 8680 880 = 0x1b9efdff5a20 :=
  block_append (B := 9814) (J := 2080) (start := 8680) (next := 9120)
    (a := 440) (b := 440) (n := 880) (x := 0xe66ccf58c50) (y := 0xd383109cdd0) (z := 0x1b9efdff5a20)
    sum9814_2080_8680_440 sum9814_2080_9120_440 rfl rfl rfl

private theorem sum9814_2080_8020_1540 : blockEstimate 9814 2080 8020 1540 = 0x32bc03946488 :=
  block_append (B := 9814) (J := 2080) (start := 8020) (next := 8680)
    (a := 660) (b := 880) (n := 1540) (x := 0x171d05950a68) (y := 0x1b9efdff5a20) (z := 0x32bc03946488)
    sum9814_2080_8020_660 sum9814_2080_8680_880 rfl rfl rfl

private theorem sum9814_2080_9780_440 : blockEstimate 9814 2080 9780 440 = 0xadf7580d42b :=
  block_append (B := 9814) (J := 2080) (start := 9780) (next := 10000)
    (a := 220) (b := 220) (n := 440) (x := 0x5a6f3b34db4) (y := 0x53881cd8677) (z := 0xadf7580d42b)
    part9814_2080_35 part9814_2080_36 rfl rfl rfl

private theorem sum9814_2080_9560_660 : blockEstimate 9814 2080 9560 660 = 0x10f047cedae3 :=
  block_append (B := 9814) (J := 2080) (start := 9560) (next := 9780)
    (a := 220) (b := 440) (n := 660) (x := 0x610d24e06b8) (y := 0xadf7580d42b) (z := 0x10f047cedae3)
    part9814_2080_34 sum9814_2080_9780_440 rfl rfl rfl

private theorem sum9814_2080_10220_440 : blockEstimate 9814 2080 10220 440 = 0x9200291fdaf :=
  block_append (B := 9814) (J := 2080) (start := 10220) (next := 10440)
    (a := 220) (b := 220) (n := 440) (x := 0x4c85b61aeb1) (y := 0x457a7304efe) (z := 0x9200291fdaf)
    part9814_2080_37 part9814_2080_38 rfl rfl rfl

private theorem sum9814_2080_10660_440 : blockEstimate 9814 2080 10660 440 = 0x76074d0fba5 :=
  block_append (B := 9814) (J := 2080) (start := 10660) (next := 10880)
    (a := 220) (b := 220) (n := 440) (x := 0x3e77fdbf67d) (y := 0x378f4f50528) (z := 0x76074d0fba5)
    part9814_2080_39 part9814_2080_40 rfl rfl rfl

private theorem sum9814_2080_10220_880 : blockEstimate 9814 2080 10220 880 = 0x10807762f954 :=
  block_append (B := 9814) (J := 2080) (start := 10220) (next := 10660)
    (a := 440) (b := 440) (n := 880) (x := 0x9200291fdaf) (y := 0x76074d0fba5) (z := 0x10807762f954)
    sum9814_2080_10220_440 sum9814_2080_10660_440 rfl rfl rfl

private theorem sum9814_2080_9560_1540 : blockEstimate 9814 2080 9560 1540 = 0x2170bf31d437 :=
  block_append (B := 9814) (J := 2080) (start := 9560) (next := 10220)
    (a := 660) (b := 880) (n := 1540) (x := 0x10f047cedae3) (y := 0x10807762f954) (z := 0x2170bf31d437)
    sum9814_2080_9560_660 sum9814_2080_10220_880 rfl rfl rfl

private theorem sum9814_2080_8020_3080 : blockEstimate 9814 2080 8020 3080 = 0x542cc2c638bf :=
  block_append (B := 9814) (J := 2080) (start := 8020) (next := 9560)
    (a := 1540) (b := 1540) (n := 3080) (x := 0x32bc03946488) (y := 0x2170bf31d437) (z := 0x542cc2c638bf)
    sum9814_2080_8020_1540 sum9814_2080_9560_1540 rfl rfl rfl

private theorem sum9814_2080_11320_440 : blockEstimate 9814 2080 11320 440 = 0x4e5afba5af2 :=
  block_append (B := 9814) (J := 2080) (start := 11320) (next := 11540)
    (a := 220) (b := 220) (n := 440) (x := 0x2a4bb56233a) (y := 0x240f46437b8) (z := 0x4e5afba5af2)
    part9814_2080_42 part9814_2080_43 rfl rfl rfl

private theorem sum9814_2080_11100_660 : blockEstimate 9814 2080 11100 660 = 0x7f2bab41110 :=
  block_append (B := 9814) (J := 2080) (start := 11100) (next := 11320)
    (a := 220) (b := 440) (n := 660) (x := 0x30d0af9b61e) (y := 0x4e5afba5af2) (z := 0x7f2bab41110)
    part9814_2080_41 sum9814_2080_11320_440 rfl rfl rfl

private theorem sum9814_2080_11760_440 : blockEstimate 9814 2080 11760 440 = 0x36c0457c2be :=
  block_append (B := 9814) (J := 2080) (start := 11760) (next := 11980)
    (a := 220) (b := 220) (n := 440) (x := 0x1e27d9f0ece) (y := 0x18986b8b3f0) (z := 0x36c0457c2be)
    part9814_2080_44 part9814_2080_45 rfl rfl rfl

private theorem sum9814_2080_12200_440 : blockEstimate 9814 2080 12200 440 = 0x226da12d1ff :=
  block_append (B := 9814) (J := 2080) (start := 12200) (next := 12420)
    (a := 220) (b := 220) (n := 440) (x := 0x1380700d6bb) (y := 0xeed311fb44) (z := 0x226da12d1ff)
    part9814_2080_46 part9814_2080_47 rfl rfl rfl

private theorem sum9814_2080_11760_880 : blockEstimate 9814 2080 11760 880 = 0x592de6a94bd :=
  block_append (B := 9814) (J := 2080) (start := 11760) (next := 12200)
    (a := 440) (b := 440) (n := 880) (x := 0x36c0457c2be) (y := 0x226da12d1ff) (z := 0x592de6a94bd)
    sum9814_2080_11760_440 sum9814_2080_12200_440 rfl rfl rfl

private theorem sum9814_2080_11100_1540 : blockEstimate 9814 2080 11100 1540 = 0xd85991ea5cd :=
  block_append (B := 9814) (J := 2080) (start := 11100) (next := 11760)
    (a := 660) (b := 880) (n := 1540) (x := 0x7f2bab41110) (y := 0x592de6a94bd) (z := 0xd85991ea5cd)
    sum9814_2080_11100_660 sum9814_2080_11760_880 rfl rfl rfl

private theorem sum9814_2080_12860_440 : blockEstimate 9814 2080 12860 440 = 0xc17526fe03 :=
  block_append (B := 9814) (J := 2080) (start := 12860) (next := 13080)
    (a := 220) (b := 220) (n := 440) (x := 0x775a29a550) (y := 0x4a1afd58b3) (z := 0xc17526fe03)
    part9814_2080_49 part9814_2080_50 rfl rfl rfl

private theorem sum9814_2080_12640_660 : blockEstimate 9814 2080 12640 660 = 0x16fe2f9b67e :=
  block_append (B := 9814) (J := 2080) (start := 12640) (next := 12860)
    (a := 220) (b := 440) (n := 660) (x := 0xae6dd2b87b) (y := 0xc17526fe03) (z := 0x16fe2f9b67e)
    part9814_2080_48 sum9814_2080_12860_440 rfl rfl rfl

private theorem sum9814_2080_13300_440 : blockEstimate 9814 2080 13300 440 = 0x3658e9d877 :=
  block_append (B := 9814) (J := 2080) (start := 13300) (next := 13520)
    (a := 220) (b := 220) (n := 440) (x := 0x2733346994) (y := 0xf25b56ee3) (z := 0x3658e9d877)
    part9814_2080_51 part9814_2080_52 rfl rfl rfl

private theorem sum9814_2080_13740_234 : blockEstimate 9814 2080 13740 234 = 0x2759517e6 :=
  block_append (B := 9814) (J := 2080) (start := 13740) (next := 13960)
    (a := 220) (b := 14) (n := 234) (x := 0x27566ff90) (y := 0x2e1856) (z := 0x2759517e6)
    part9814_2080_53 part9814_2080_54 rfl rfl rfl

private theorem sum9814_2080_13300_674 : blockEstimate 9814 2080 13300 674 = 0x38ce7ef05d :=
  block_append (B := 9814) (J := 2080) (start := 13300) (next := 13740)
    (a := 440) (b := 234) (n := 674) (x := 0x3658e9d877) (y := 0x2759517e6) (z := 0x38ce7ef05d)
    sum9814_2080_13300_440 sum9814_2080_13740_234 rfl rfl rfl

private theorem sum9814_2080_12640_1334 : blockEstimate 9814 2080 12640 1334 = 0x1a8b178a6db :=
  block_append (B := 9814) (J := 2080) (start := 12640) (next := 13300)
    (a := 660) (b := 674) (n := 1334) (x := 0x16fe2f9b67e) (y := 0x38ce7ef05d) (z := 0x1a8b178a6db)
    sum9814_2080_12640_660 sum9814_2080_13300_674 rfl rfl rfl

private theorem sum9814_2080_11100_2874 : blockEstimate 9814 2080 11100 2874 = 0xf2e4a974ca8 :=
  block_append (B := 9814) (J := 2080) (start := 11100) (next := 12640)
    (a := 1540) (b := 1334) (n := 2874) (x := 0xd85991ea5cd) (y := 0x1a8b178a6db) (z := 0xf2e4a974ca8)
    sum9814_2080_11100_1540 sum9814_2080_12640_1334 rfl rfl rfl

private theorem sum9814_2080_8020_5954 : blockEstimate 9814 2080 8020 5954 = 0x635b0d5d8567 :=
  block_append (B := 9814) (J := 2080) (start := 8020) (next := 11100)
    (a := 3080) (b := 2874) (n := 5954) (x := 0x542cc2c638bf) (y := 0xf2e4a974ca8) (z := 0x635b0d5d8567)
    sum9814_2080_8020_3080 sum9814_2080_11100_2874 rfl rfl rfl

private theorem sum9814_2080_2080_11894 : blockEstimate 9814 2080 2080 11894 = 0xe386fa12aab7 :=
  block_append (B := 9814) (J := 2080) (start := 2080) (next := 8020)
    (a := 5940) (b := 5954) (n := 11894) (x := 0x802becb52550) (y := 0x635b0d5d8567) (z := 0xe386fa12aab7)
    sum9814_2080_2080_5940 sum9814_2080_8020_5954 rfl rfl rfl

theorem moment9814_2080 : momentEstimate 9814 2080 = 0xe386fa12aab7 := sum9814_2080_2080_11894

theorem moment10506_2218 : momentEstimate 10506 2218 = 0x129e297a45c0c := P1_7_1_3_6.moment10506

theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := by
  exact moment_from_blocks [⟨140,0x4ed4ac⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment127_28 : momentEstimate 127 28 = 0x75b415 := by
  exact moment_from_blocks [⟨155,0x75b415⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment161_35 : momentEstimate 161 35 = 0x128bb48 := by
  exact moment_from_blocks [⟨196,0x128bb48⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment237_50 : momentEstimate 237 50 = 0x53b7f45 := by
  exact moment_from_blocks [⟨287,0x53b7f45⟩]
    ⟨(by decide +kernel), trivial⟩ rfl rfl

theorem moment275_61 : momentEstimate 275 61 = 0x9cf007b := by
  exact moment_from_blocks [⟨320,0x9cd2f6f⟩, ⟨16,0x1d10c⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment359_80 : momentEstimate 359 80 = 0x1c63733f := by
  exact moment_from_blocks [⟨320,0x19c50aee⟩, ⟨119,0x29e6851⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment389_86 : momentEstimate 389 86 = 0x26d3f271 := by
  exact moment_from_blocks [⟨320,0x20eb355c⟩, ⟨155,0x5e8bd15⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment510_115 : momentEstimate 510 115 = 0x73e3968f := by
  exact moment_from_blocks [⟨320,0x4445fe63⟩, ⟨305,0x2f9d982c⟩]
    ⟨(by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment556_117 : momentEstimate 556 117 = 0x9afa738a := by
  exact moment_from_blocks [⟨320,0x5034e465⟩, ⟨320,0x4aa9579d⟩, ⟨33,0x1c3788⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment560_118 : momentEstimate 560 118 = 0x9fa2a66a := by
  exact moment_from_blocks [⟨320,0x51909ea1⟩, ⟨320,0x4de789b8⟩, ⟨38,0x2a7e11⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment616_139 : momentEstimate 616 139 = 0xf61a28de := by
  exact moment_from_blocks [⟨320,0x67a94fd1⟩, ⟨320,0x8a05882b⟩, ⟨115,0x46b50e2⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment695_146 : momentEstimate 695 146 = 0x178b58789 := by
  exact moment_from_blocks [⟨320,0x7fd2b06b⟩, ⟨320,0xe0334cdd⟩, ⟨201,0x18af8a41⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment803_168 : momentEstimate 803 168 = 0x29c15d15d := by
  exact moment_from_blocks [⟨320,0xa70b3456⟩, ⟨320,0x181f4711b⟩, ⟨320,0x731435c3⟩, ⟨11,0x1f629⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment905_191 : momentEstimate 905 191 = 0x43bec1daa := by
  exact moment_from_blocks [⟨320,0xcd941470⟩, ⟨320,0x238aafc00⟩, ⟨320,0x12ace4a80⟩, ⟨136,0xadec2ba⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1070_226 : momentEstimate 1070 226 = 0x84449c619 := by
  exact moment_from_blocks [⟨320,0x10a94d1b6⟩, ⟨320,0x386a1eb20⟩, ⟨320,0x306150650⟩, ⟨320,0xacf6cf13⟩, ⟨16,0x733e0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1126_252 : momentEstimate 1126 252 = 0xa99a27482 := by
  exact moment_from_blocks [⟨320,0x120cbaff5⟩, ⟨320,0x428c58ec0⟩, ⟨320,0x3ffd66340⟩, ⟨320,0x14af15b58⟩, ⟨98,0x5497735⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1363_286 : momentEstimate 1363 286 = 0x159e2d5716 := by
  exact moment_from_blocks [⟨320,0x170d487b4⟩, ⟨320,0x6318f3400⟩, ⟨320,0x7bd721400⟩, ⟨320,0x51274bf6b⟩, ⟨320,0x12b076066⟩, ⟨49,0xdb6791⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1364_286 : momentEstimate 1364 286 = 0x15ab3b8fbf := by
  exact moment_from_blocks [⟨320,0x171288be3⟩, ⟨320,0x633682a20⟩, ⟨320,0x7c10b7a20⟩, ⟨320,0x5172fd597⟩, ⟨320,0x12d86beb8⟩, ⟨50,0xe8cb4d⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1672_376 : momentEstimate 1672 376 = 0x339a80c8e3 := by
  exact moment_from_blocks [⟨320,0x1d6c58050⟩, ⟨320,0x991230d9e⟩, ⟨320,0xec565b340⟩, ⟨320,0xe3b55f340⟩, ⟨320,0x89f03be35⟩, ⟨320,0x28173e480⟩, ⟨128,0x1164f1c0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1818_382 : momentEstimate 1818 382 = 0x4463d9bf23 := by
  exact moment_from_blocks [⟨320,0x206be77d0⟩, ⟨320,0xad3e2e575⟩, ⟨320,0x11788538e0⟩, ⟨320,0x12489228e0⟩, ⟨320,0xd5bcb2cdb⟩, ⟨320,0x5b1603263⟩, ⟨280,0xbaf5a0e0⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment1989_418 : momentEstimate 1989 418 = 0x61f51befe2 := by
  exact moment_from_blocks [⟨320,0x23eee5710⟩, ⟨320,0xc9673e15d⟩, ⟨320,0x15b2bdfc00⟩, ⟨320,0x1879b11c00⟩, ⟨320,0x14dc12d85b⟩, ⟨320,0xc1c68416a⟩, ⟨320,0x3cd64b7ac⟩, ⟨167,0x2d6ace04⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment2112_447 : momentEstimate 2112 447 = 0x7d30624510 := by
  exact moment_from_blocks [⟨320,0x26758a250⟩, ⟨320,0xddbf45420⟩, ⟨320,0x18fe429c00⟩, ⟨320,0x1d6e649c00⟩, ⟨320,0x1b08869c00⟩, ⟨320,0x12486d727d⟩, ⟨320,0x7ee75f793⟩, ⟨319,0x141041090⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment2669_560 : momentEstimate 2669 560 = 0x13cdc61e0d1 := by
  exact moment_from_blocks [⟨320,0x31e5d5d10⟩, ⟨320,0x133871dd24⟩, ⟨320,0x2850cfd6e0⟩, ⟨320,0x36142ea6e0⟩, ⟨320,0x3b482576e0⟩, ⟨320,0x37ecb446e0⟩, ⟨320,0x2c14fcfed0⟩, ⟨320,0x1b14215427⟩, ⟨320,0xbaaa0723a⟩, ⟨320,0x2179c0068⟩, ⟨29,0x5fa584⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment3427_717 : momentEstimate 3427 717 = 0x35abaf976d5 := by
  exact moment_from_blocks [⟨320,0x4176d7390⟩, ⟨320,0x1a09068790⟩, ⟨320,0x3db82c66ab⟩, ⟨320,0x5d9ad8c0a0⟩, ⟨320,0x72956290a0⟩, ⟨320,0x7c9b3c60a0⟩, ⟨320,0x7bac6630a0⟩, ⟨320,0x6fc8e000a0⟩, ⟨320,0x59265c519d⟩, ⟨320,0x3cb2b275c8⟩, ⟨320,0x21e589eb31⟩, ⟨320,0xd11c3a870⟩, ⟨304,0x1d13ed6e4⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment5137_1083 : momentEstimate 5137 1083 = 0x1105d97d500b := by
  exact moment_from_blocks [⟨320,0x6494c2c10⟩, ⟨320,0x29512d2010⟩, ⟨320,0x688ad41410⟩, ⟨320,0xbb7a8b4f69⟩, ⟨320,0x10bc68bc7c0⟩, ⟨320,0x14bd4d327c0⟩, ⟨320,0x17b58ba87c0⟩, ⟨320,0x19a5241e7c0⟩, ⟨320,0x1a8c16947c0⟩, ⟨320,0x1a6a630a7c0⟩, ⟨320,0x194009807c0⟩, ⟨320,0x170d09f67c0⟩, ⟨320,0x13d28cf66b0⟩, ⟨320,0xfdebbca392⟩, ⟨320,0xbd4734a675⟩, ⟨320,0x8084db61d3⟩, ⟨320,0x4ba88fd2e4⟩, ⟨320,0x22ce48ce20⟩, ⟨320,0x91ba49420⟩, ⟨140,0x475e9ac4⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl

theorem moment6667_1405 : momentEstimate 6667 1405 = 0x304357eb723c := by
  exact moment_from_blocks [⟨320,0x84005f990⟩, ⟨320,0x36fd858d90⟩, ⟨320,0x8d99132190⟩, ⟨320,0x104bfaeb590⟩, ⟨320,0x193a57dafcf⟩, ⟨320,0x21f0250eba0⟩, ⟨320,0x29552df3ba0⟩, ⟨320,0x2f62f3d8ba0⟩, ⟨320,0x341976bdba0⟩, ⟨320,0x3778b6a2ba0⟩, ⟨320,0x3980b387ba0⟩, ⟨320,0x3a316d6cba0⟩, ⟨320,0x398ae451ba0⟩, ⟨320,0x378d1836ba0⟩, ⟨320,0x3438091bba0⟩, ⟨320,0x2f8bb700ba0⟩, ⟨320,0x298f4ae5403⟩, ⟨320,0x22cf7e3d680⟩, ⟨320,0x1bf8f8a3073⟩, ⟨320,0x155c7b18d94⟩, ⟨320,0xf408d366ed⟩, ⟨320,0x9dd70e67b0⟩, ⟨320,0x57cfce9fb0⟩, ⟨320,0x24f93777b0⟩, ⟨320,0x79d38efb0⟩, ⟨72,0xd145616⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩ rfl rfl


end HighCore82219BankProof
