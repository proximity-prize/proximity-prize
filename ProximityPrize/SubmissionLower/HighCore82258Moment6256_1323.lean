import ProximityPrize.SubmissionLower.HighCore82258Moments4
import ProximityPrize.SubmissionLower.HighCore82258Moment4863_1027
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

private theorem p6256_1323_1323_220 : blockEstimate 6256 1323 1323 220 = 0x28d306189 := by decide +kernel
private theorem p6256_1323_1543_220 : blockEstimate 6256 1323 1543 220 = 0x112c6f3b6d := by decide +kernel
private theorem p6256_1323_1763_220 : blockEstimate 6256 1323 1763 220 = 0x2cd8e6ce31 := by decide +kernel
private theorem p6256_1323_1983_220 : blockEstimate 6256 1323 1983 220 = 0x53efb536d5 := by decide +kernel
private theorem p6256_1323_2203_220 : blockEstimate 6256 1323 2203 220 = 0x84cdf89259 := by decide +kernel
private theorem p6256_1323_2423_220 : blockEstimate 6256 1323 2423 220 = 0xbdd0cefdbd := by decide +kernel
private theorem p6256_1323_2643_220 : blockEstimate 6256 1323 2643 220 = 0xfb71120ee3 := by decide +kernel
private theorem p6256_1323_2863_220 : blockEstimate 6256 1323 2863 220 = 0x134b2a27ce4 := by decide +kernel
private theorem p6256_1323_3083_220 : blockEstimate 6256 1323 3083 220 = 0x1676397de04 := by decide +kernel
private theorem p6256_1323_3303_220 : blockEstimate 6256 1323 3303 220 = 0x19383f1e524 := by decide +kernel
private theorem p6256_1323_3523_220 : blockEstimate 6256 1323 3523 220 = 0x1b913b09244 := by decide +kernel
private theorem p6256_1323_3743_220 : blockEstimate 6256 1323 3743 220 = 0x1d812d3e564 := by decide +kernel
private theorem p6256_1323_3963_220 : blockEstimate 6256 1323 3963 220 = 0x1f0815bde84 := by decide +kernel
private theorem p6256_1323_4183_220 : blockEstimate 6256 1323 4183 220 = 0x2025f487da4 := by decide +kernel
private theorem p6256_1323_4403_220 : blockEstimate 6256 1323 4403 220 = 0x20dac99c2c4 := by decide +kernel
private theorem p6256_1323_4623_220 : blockEstimate 6256 1323 4623 220 = 0x212694fade4 := by decide +kernel
private theorem p6256_1323_4843_220 : blockEstimate 6256 1323 4843 220 = 0x210956a3f04 := by decide +kernel
private theorem p6256_1323_5063_220 : blockEstimate 6256 1323 5063 220 = 0x20830e97624 := by decide +kernel
private theorem p6256_1323_5283_220 : blockEstimate 6256 1323 5283 220 = 0x1f93bcd5344 := by decide +kernel
private theorem p6256_1323_5503_220 : blockEstimate 6256 1323 5503 220 = 0x1e3b615d664 := by decide +kernel
private theorem p6256_1323_5723_220 : blockEstimate 6256 1323 5723 220 = 0x1c79fc2ff84 := by decide +kernel
private theorem p6256_1323_5943_220 : blockEstimate 6256 1323 5943 220 = 0x1a4f8d4cea4 := by decide +kernel
private theorem p6256_1323_6163_220 : blockEstimate 6256 1323 6163 220 = 0x17be7ea9974 := by decide +kernel
private theorem p6256_1323_6383_220 : blockEstimate 6256 1323 6383 220 = 0x14f12e79991 := by decide +kernel
private theorem p6256_1323_6603_220 : blockEstimate 6256 1323 6603 220 = 0x1215fc4ff6f := by decide +kernel
private theorem p6256_1323_6823_220 : blockEstimate 6256 1323 6823 220 = 0xf3faf66aa5 := by decide +kernel
private theorem p6256_1323_7043_220 : blockEstimate 6256 1323 7043 220 = 0xc7f1c2794f := by decide +kernel
private theorem p6256_1323_7263_220 : blockEstimate 6256 1323 7263 220 = 0x9e400939f7 := by decide +kernel
private theorem p6256_1323_7483_220 : blockEstimate 6256 1323 7483 220 = 0x77bb536104 := by decide +kernel
private theorem p6256_1323_7703_220 : blockEstimate 6256 1323 7703 220 = 0x5520d30a02 := by decide +kernel
private theorem p6256_1323_7923_220 : blockEstimate 6256 1323 7923 220 = 0x37adf3a784 := by decide +kernel
private theorem p6256_1323_8143_220 : blockEstimate 6256 1323 8143 220 = 0x1ff6d04b50 := by decide +kernel
private theorem p6256_1323_8363_220 : blockEstimate 6256 1323 8363 220 = 0xe7e4f8c56 := by decide +kernel
private theorem p6256_1323_8583_220 : blockEstimate 6256 1323 8583 220 = 0x3c7580186 := by decide +kernel
private theorem p6256_1323_8803_99 : blockEstimate 6256 1323 8803 99 = 0x1f4e6a0a := by decide +kernel
private theorem p6256_1323_1323_440 : blockEstimate 6256 1323 1323 440 = 0x13b99f9cf6 :=
  block_append (B := 6256) (J := 1323) (start := 1323) (next := 1543)
    (a := 220) (b := 220) (n := 440) (x := 0x28d306189) (y := 0x112c6f3b6d) (z := 0x13b99f9cf6)
    p6256_1323_1323_220 p6256_1323_1543_220 rfl rfl rfl
private theorem p6256_1323_1763_440 : blockEstimate 6256 1323 1763 440 = 0x80c89c0506 :=
  block_append (B := 6256) (J := 1323) (start := 1763) (next := 1983)
    (a := 220) (b := 220) (n := 440) (x := 0x2cd8e6ce31) (y := 0x53efb536d5) (z := 0x80c89c0506)
    p6256_1323_1763_220 p6256_1323_1983_220 rfl rfl rfl
private theorem p6256_1323_1323_880 : blockEstimate 6256 1323 1323 880 = 0x94823ba1fc :=
  block_append (B := 6256) (J := 1323) (start := 1323) (next := 1763)
    (a := 440) (b := 440) (n := 880) (x := 0x13b99f9cf6) (y := 0x80c89c0506) (z := 0x94823ba1fc)
    p6256_1323_1323_440 p6256_1323_1763_440 rfl rfl rfl
private theorem p6256_1323_2203_440 : blockEstimate 6256 1323 2203 440 = 0x1429ec79016 :=
  block_append (B := 6256) (J := 1323) (start := 2203) (next := 2423)
    (a := 220) (b := 220) (n := 440) (x := 0x84cdf89259) (y := 0xbdd0cefdbd) (z := 0x1429ec79016)
    p6256_1323_2203_220 p6256_1323_2423_220 rfl rfl rfl
private theorem p6256_1323_2643_440 : blockEstimate 6256 1323 2643 440 = 0x23023b48bc7 :=
  block_append (B := 6256) (J := 1323) (start := 2643) (next := 2863)
    (a := 220) (b := 220) (n := 440) (x := 0xfb71120ee3) (y := 0x134b2a27ce4) (z := 0x23023b48bc7)
    p6256_1323_2643_220 p6256_1323_2863_220 rfl rfl rfl
private theorem p6256_1323_2203_880 : blockEstimate 6256 1323 2203 880 = 0x372c27c1bdd :=
  block_append (B := 6256) (J := 1323) (start := 2203) (next := 2643)
    (a := 440) (b := 440) (n := 880) (x := 0x1429ec79016) (y := 0x23023b48bc7) (z := 0x372c27c1bdd)
    p6256_1323_2203_440 p6256_1323_2643_440 rfl rfl rfl
private theorem p6256_1323_1323_1760 : blockEstimate 6256 1323 1323 1760 = 0x40744b7bdd9 :=
  block_append (B := 6256) (J := 1323) (start := 1323) (next := 2203)
    (a := 880) (b := 880) (n := 1760) (x := 0x94823ba1fc) (y := 0x372c27c1bdd) (z := 0x40744b7bdd9)
    p6256_1323_1323_880 p6256_1323_2203_880 rfl rfl rfl
private theorem p6256_1323_3083_440 : blockEstimate 6256 1323 3083 440 = 0x2fae789c328 :=
  block_append (B := 6256) (J := 1323) (start := 3083) (next := 3303)
    (a := 220) (b := 220) (n := 440) (x := 0x1676397de04) (y := 0x19383f1e524) (z := 0x2fae789c328)
    p6256_1323_3083_220 p6256_1323_3303_220 rfl rfl rfl
private theorem p6256_1323_3523_440 : blockEstimate 6256 1323 3523 440 = 0x391268477a8 :=
  block_append (B := 6256) (J := 1323) (start := 3523) (next := 3743)
    (a := 220) (b := 220) (n := 440) (x := 0x1b913b09244) (y := 0x1d812d3e564) (z := 0x391268477a8)
    p6256_1323_3523_220 p6256_1323_3743_220 rfl rfl rfl
private theorem p6256_1323_3083_880 : blockEstimate 6256 1323 3083 880 = 0x68c0e0e3ad0 :=
  block_append (B := 6256) (J := 1323) (start := 3083) (next := 3523)
    (a := 440) (b := 440) (n := 880) (x := 0x2fae789c328) (y := 0x391268477a8) (z := 0x68c0e0e3ad0)
    p6256_1323_3083_440 p6256_1323_3523_440 rfl rfl rfl
private theorem p6256_1323_3963_440 : blockEstimate 6256 1323 3963 440 = 0x3f2e0a45c28 :=
  block_append (B := 6256) (J := 1323) (start := 3963) (next := 4183)
    (a := 220) (b := 220) (n := 440) (x := 0x1f0815bde84) (y := 0x2025f487da4) (z := 0x3f2e0a45c28)
    p6256_1323_3963_220 p6256_1323_4183_220 rfl rfl rfl
private theorem p6256_1323_4623_440 : blockEstimate 6256 1323 4623 440 = 0x422feb9ece8 :=
  block_append (B := 6256) (J := 1323) (start := 4623) (next := 4843)
    (a := 220) (b := 220) (n := 440) (x := 0x212694fade4) (y := 0x210956a3f04) (z := 0x422feb9ece8)
    p6256_1323_4623_220 p6256_1323_4843_220 rfl rfl rfl
private theorem p6256_1323_4403_660 : blockEstimate 6256 1323 4403 660 = 0x630ab53afac :=
  block_append (B := 6256) (J := 1323) (start := 4403) (next := 4623)
    (a := 220) (b := 440) (n := 660) (x := 0x20dac99c2c4) (y := 0x422feb9ece8) (z := 0x630ab53afac)
    p6256_1323_4403_220 p6256_1323_4623_440 rfl rfl rfl
private theorem p6256_1323_3963_1100 : blockEstimate 6256 1323 3963 1100 = 0xa238bf80bd4 :=
  block_append (B := 6256) (J := 1323) (start := 3963) (next := 4403)
    (a := 440) (b := 660) (n := 1100) (x := 0x3f2e0a45c28) (y := 0x630ab53afac) (z := 0xa238bf80bd4)
    p6256_1323_3963_440 p6256_1323_4403_660 rfl rfl rfl
private theorem p6256_1323_3083_1980 : blockEstimate 6256 1323 3083 1980 = 0x10af9a0646a4 :=
  block_append (B := 6256) (J := 1323) (start := 3083) (next := 3963)
    (a := 880) (b := 1100) (n := 1980) (x := 0x68c0e0e3ad0) (y := 0xa238bf80bd4) (z := 0x10af9a0646a4)
    p6256_1323_3083_880 p6256_1323_3963_1100 rfl rfl rfl
private theorem p6256_1323_1323_3740 : blockEstimate 6256 1323 1323 3740 = 0x14b6debe047d :=
  block_append (B := 6256) (J := 1323) (start := 1323) (next := 3083)
    (a := 1760) (b := 1980) (n := 3740) (x := 0x40744b7bdd9) (y := 0x10af9a0646a4) (z := 0x14b6debe047d)
    p6256_1323_1323_1760 p6256_1323_3083_1980 rfl rfl rfl
private theorem p6256_1323_5063_440 : blockEstimate 6256 1323 5063 440 = 0x4016cb6c968 :=
  block_append (B := 6256) (J := 1323) (start := 5063) (next := 5283)
    (a := 220) (b := 220) (n := 440) (x := 0x20830e97624) (y := 0x1f93bcd5344) (z := 0x4016cb6c968)
    p6256_1323_5063_220 p6256_1323_5283_220 rfl rfl rfl
private theorem p6256_1323_5503_440 : blockEstimate 6256 1323 5503 440 = 0x3ab55d8d5e8 :=
  block_append (B := 6256) (J := 1323) (start := 5503) (next := 5723)
    (a := 220) (b := 220) (n := 440) (x := 0x1e3b615d664) (y := 0x1c79fc2ff84) (z := 0x3ab55d8d5e8)
    p6256_1323_5503_220 p6256_1323_5723_220 rfl rfl rfl
private theorem p6256_1323_5063_880 : blockEstimate 6256 1323 5063 880 = 0x7acc28f9f50 :=
  block_append (B := 6256) (J := 1323) (start := 5063) (next := 5503)
    (a := 440) (b := 440) (n := 880) (x := 0x4016cb6c968) (y := 0x3ab55d8d5e8) (z := 0x7acc28f9f50)
    p6256_1323_5063_440 p6256_1323_5503_440 rfl rfl rfl
private theorem p6256_1323_5943_440 : blockEstimate 6256 1323 5943 440 = 0x320e0bf6818 :=
  block_append (B := 6256) (J := 1323) (start := 5943) (next := 6163)
    (a := 220) (b := 220) (n := 440) (x := 0x1a4f8d4cea4) (y := 0x17be7ea9974) (z := 0x320e0bf6818)
    p6256_1323_5943_220 p6256_1323_6163_220 rfl rfl rfl
private theorem p6256_1323_6603_440 : blockEstimate 6256 1323 6603 440 = 0x2155abb6a14 :=
  block_append (B := 6256) (J := 1323) (start := 6603) (next := 6823)
    (a := 220) (b := 220) (n := 440) (x := 0x1215fc4ff6f) (y := 0xf3faf66aa5) (z := 0x2155abb6a14)
    p6256_1323_6603_220 p6256_1323_6823_220 rfl rfl rfl
private theorem p6256_1323_6383_660 : blockEstimate 6256 1323 6383 660 = 0x3646da303a5 :=
  block_append (B := 6256) (J := 1323) (start := 6383) (next := 6603)
    (a := 220) (b := 440) (n := 660) (x := 0x14f12e79991) (y := 0x2155abb6a14) (z := 0x3646da303a5)
    p6256_1323_6383_220 p6256_1323_6603_440 rfl rfl rfl
private theorem p6256_1323_5943_1100 : blockEstimate 6256 1323 5943 1100 = 0x6854e626bbd :=
  block_append (B := 6256) (J := 1323) (start := 5943) (next := 6383)
    (a := 440) (b := 660) (n := 1100) (x := 0x320e0bf6818) (y := 0x3646da303a5) (z := 0x6854e626bbd)
    p6256_1323_5943_440 p6256_1323_6383_660 rfl rfl rfl
private theorem p6256_1323_5063_1980 : blockEstimate 6256 1323 5063 1980 = 0xe3210f20b0d :=
  block_append (B := 6256) (J := 1323) (start := 5063) (next := 5943)
    (a := 880) (b := 1100) (n := 1980) (x := 0x7acc28f9f50) (y := 0x6854e626bbd) (z := 0xe3210f20b0d)
    p6256_1323_5063_880 p6256_1323_5943_1100 rfl rfl rfl
private theorem p6256_1323_7043_440 : blockEstimate 6256 1323 7043 440 = 0x16631cbb346 :=
  block_append (B := 6256) (J := 1323) (start := 7043) (next := 7263)
    (a := 220) (b := 220) (n := 440) (x := 0xc7f1c2794f) (y := 0x9e400939f7) (z := 0x16631cbb346)
    p6256_1323_7043_220 p6256_1323_7263_220 rfl rfl rfl
private theorem p6256_1323_7483_440 : blockEstimate 6256 1323 7483 440 = 0xccdc266b06 :=
  block_append (B := 6256) (J := 1323) (start := 7483) (next := 7703)
    (a := 220) (b := 220) (n := 440) (x := 0x77bb536104) (y := 0x5520d30a02) (z := 0xccdc266b06)
    p6256_1323_7483_220 p6256_1323_7703_220 rfl rfl rfl
private theorem p6256_1323_7043_880 : blockEstimate 6256 1323 7043 880 = 0x2330df21e4c :=
  block_append (B := 6256) (J := 1323) (start := 7043) (next := 7483)
    (a := 440) (b := 440) (n := 880) (x := 0x16631cbb346) (y := 0xccdc266b06) (z := 0x2330df21e4c)
    p6256_1323_7043_440 p6256_1323_7483_440 rfl rfl rfl
private theorem p6256_1323_7923_440 : blockEstimate 6256 1323 7923 440 = 0x57a4c3f2d4 :=
  block_append (B := 6256) (J := 1323) (start := 7923) (next := 8143)
    (a := 220) (b := 220) (n := 440) (x := 0x37adf3a784) (y := 0x1ff6d04b50) (z := 0x57a4c3f2d4)
    p6256_1323_7923_220 p6256_1323_8143_220 rfl rfl rfl
private theorem p6256_1323_8583_319 : blockEstimate 6256 1323 8583 319 = 0x3e6a66b90 :=
  block_append (B := 6256) (J := 1323) (start := 8583) (next := 8803)
    (a := 220) (b := 99) (n := 319) (x := 0x3c7580186) (y := 0x1f4e6a0a) (z := 0x3e6a66b90)
    p6256_1323_8583_220 p6256_1323_8803_99 rfl rfl rfl
private theorem p6256_1323_8363_539 : blockEstimate 6256 1323 8363 539 = 0x1264f5f7e6 :=
  block_append (B := 6256) (J := 1323) (start := 8363) (next := 8583)
    (a := 220) (b := 319) (n := 539) (x := 0xe7e4f8c56) (y := 0x3e6a66b90) (z := 0x1264f5f7e6)
    p6256_1323_8363_220 p6256_1323_8583_319 rfl rfl rfl
private theorem p6256_1323_7923_979 : blockEstimate 6256 1323 7923 979 = 0x6a09b9eaba :=
  block_append (B := 6256) (J := 1323) (start := 7923) (next := 8363)
    (a := 440) (b := 539) (n := 979) (x := 0x57a4c3f2d4) (y := 0x1264f5f7e6) (z := 0x6a09b9eaba)
    p6256_1323_7923_440 p6256_1323_8363_539 rfl rfl rfl
private theorem p6256_1323_7043_1859 : blockEstimate 6256 1323 7043 1859 = 0x29d17ac0906 :=
  block_append (B := 6256) (J := 1323) (start := 7043) (next := 7923)
    (a := 880) (b := 979) (n := 1859) (x := 0x2330df21e4c) (y := 0x6a09b9eaba) (z := 0x29d17ac0906)
    p6256_1323_7043_880 p6256_1323_7923_979 rfl rfl rfl
private theorem p6256_1323_5063_3839 : blockEstimate 6256 1323 5063 3839 = 0x10cf289e1413 :=
  block_append (B := 6256) (J := 1323) (start := 5063) (next := 7043)
    (a := 1980) (b := 1859) (n := 3839) (x := 0xe3210f20b0d) (y := 0x29d17ac0906) (z := 0x10cf289e1413)
    p6256_1323_5063_1980 p6256_1323_7043_1859 rfl rfl rfl
private theorem p6256_1323_1323_7579 : blockEstimate 6256 1323 1323 7579 = 0x2586075c1890 :=
  block_append (B := 6256) (J := 1323) (start := 1323) (next := 5063)
    (a := 3740) (b := 3839) (n := 7579) (x := 0x14b6debe047d) (y := 0x10cf289e1413) (z := 0x2586075c1890)
    p6256_1323_1323_3740 p6256_1323_5063_3839 rfl rfl rfl

theorem moment6256_1323 : momentEstimate 6256 1323 = 0x2586075c1890 := p6256_1323_1323_7579
end HighCore82258BankProof
