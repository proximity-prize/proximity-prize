import ProximityPrize.SubmissionLower.HighCore82258Moments3

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b3926_832_832 : blockEstimate 3926 832 832 660 = 0x2675baa3bf := by decide +kernel
private theorem b3926_832_1492 : blockEstimate 3926 832 1492 660 = 0xd3f01731c1 := by decide +kernel
private theorem b3926_832_2152 : blockEstimate 3926 832 2152 660 = 0x16317b84e28 := by decide +kernel
private theorem b3926_832_2812 : blockEstimate 3926 832 2812 660 = 0x1835d8d3308 := by decide +kernel
private theorem b3926_832_3472 : blockEstimate 3926 832 3472 660 = 0x1348b8c02ca := by decide +kernel
private theorem b3926_832_4132 : blockEstimate 3926 832 4132 660 = 0x9ced10853a := by decide +kernel
private theorem b3926_832_4792 : blockEstimate 3926 832 4792 660 = 0x2305b9d16a := by decide +kernel
private theorem b3926_832_5452 : blockEstimate 3926 832 5452 138 = 0x34121072 := by decide +kernel
private theorem s3926_832_832_1320 : blockEstimate 3926 832 832 1320 = 0xfa65d1d580 :=
  append (B := 3926) (J := 832) (start := 832) (a := 660) (x := 0x2675baa3bf)
    b3926_832_832 1492 660 0xd3f01731c1 1320 0xfa65d1d580 rfl rfl rfl b3926_832_1492
private theorem s3926_832_2152_1320 : blockEstimate 3926 832 2152 1320 = 0x2e675458130 :=
  append (B := 3926) (J := 832) (start := 2152) (a := 660) (x := 0x16317b84e28)
    b3926_832_2152 2812 660 0x1835d8d3308 1320 0x2e675458130 rfl rfl rfl b3926_832_2812
private theorem s3926_832_3472_1320 : blockEstimate 3926 832 3472 1320 = 0x1d1789c8804 :=
  append (B := 3926) (J := 832) (start := 3472) (a := 660) (x := 0x1348b8c02ca)
    b3926_832_3472 4132 660 0x9ced10853a 1320 0x1d1789c8804 rfl rfl rfl b3926_832_4132
private theorem s3926_832_4792_798 : blockEstimate 3926 832 4792 798 = 0x2339cbe1dc :=
  append (B := 3926) (J := 832) (start := 4792) (a := 660) (x := 0x2305b9d16a)
    b3926_832_4792 5452 138 0x34121072 798 0x2339cbe1dc rfl rfl rfl b3926_832_5452
private theorem s3926_832_832_2640 : blockEstimate 3926 832 832 2640 = 0x3e0db1756b0 :=
  append (B := 3926) (J := 832) (start := 832) (a := 1320) (x := 0xfa65d1d580)
    s3926_832_832_1320 2152 1320 0x2e675458130 2640 0x3e0db1756b0 rfl rfl rfl s3926_832_2152_1320
private theorem s3926_832_3472_2118 : blockEstimate 3926 832 3472 2118 = 0x1f4b26869e0 :=
  append (B := 3926) (J := 832) (start := 3472) (a := 1320) (x := 0x1d1789c8804)
    s3926_832_3472_1320 4792 798 0x2339cbe1dc 2118 0x1f4b26869e0 rfl rfl rfl s3926_832_4792_798
private theorem s3926_832_832_4758 : blockEstimate 3926 832 832 4758 = 0x5d58d7fc090 :=
  append (B := 3926) (J := 832) (start := 832) (a := 2640) (x := 0x3e0db1756b0)
    s3926_832_832_2640 3472 2118 0x1f4b26869e0 4758 0x5d58d7fc090 rfl rfl rfl s3926_832_3472_2118
theorem moment3926_832 : momentEstimate 3926 832 = 0x5d58d7fc090 := by
  change blockEstimate 3926 832 832 4758 = 0x5d58d7fc090
  exact s3926_832_832_4758

private theorem b2864_605_605 : blockEstimate 2864 605 605 660 = 0x1a8b2c9345 := by decide +kernel
private theorem b2864_605_1265 : blockEstimate 2864 605 1265 660 = 0x74b7597352 := by decide +kernel
private theorem b2864_605_1925 : blockEstimate 2864 605 1925 660 = 0x9513540102 := by decide +kernel
private theorem b2864_605_2585 : blockEstimate 2864 605 2585 660 = 0x6687c5808e := by decide +kernel
private theorem b2864_605_3245 : blockEstimate 2864 605 3245 660 = 0x1b1ebc6691 := by decide +kernel
private theorem b2864_605_3905 : blockEstimate 2864 605 3905 169 = 0x44923415 := by decide +kernel
private theorem s2864_605_605_1320 : blockEstimate 2864 605 605 1320 = 0x8f42860697 :=
  append (B := 2864) (J := 605) (start := 605) (a := 660) (x := 0x1a8b2c9345)
    b2864_605_605 1265 660 0x74b7597352 1320 0x8f42860697 rfl rfl rfl b2864_605_1265
private theorem s2864_605_1925_1320 : blockEstimate 2864 605 1925 1320 = 0xfb9b198190 :=
  append (B := 2864) (J := 605) (start := 1925) (a := 660) (x := 0x9513540102)
    b2864_605_1925 2585 660 0x6687c5808e 1320 0xfb9b198190 rfl rfl rfl b2864_605_2585
private theorem s2864_605_3245_829 : blockEstimate 2864 605 3245 829 = 0x1b634e9aa6 :=
  append (B := 2864) (J := 605) (start := 3245) (a := 660) (x := 0x1b1ebc6691)
    b2864_605_3245 3905 169 0x44923415 829 0x1b634e9aa6 rfl rfl rfl b2864_605_3905
private theorem s2864_605_605_2640 : blockEstimate 2864 605 605 2640 = 0x18add9f8827 :=
  append (B := 2864) (J := 605) (start := 605) (a := 1320) (x := 0x8f42860697)
    s2864_605_605_1320 1925 1320 0xfb9b198190 2640 0x18add9f8827 rfl rfl rfl s2864_605_1925_1320
private theorem s2864_605_605_3469 : blockEstimate 2864 605 605 3469 = 0x1a640ee22cd :=
  append (B := 2864) (J := 605) (start := 605) (a := 2640) (x := 0x18add9f8827)
    s2864_605_605_2640 3245 829 0x1b634e9aa6 3469 0x1a640ee22cd rfl rfl rfl s2864_605_3245_829
theorem moment2864_605 : momentEstimate 2864 605 = 0x1a640ee22cd := by
  change blockEstimate 2864 605 605 3469 = 0x1a640ee22cd
  exact s2864_605_605_3469

private theorem b1878_396_396 : blockEstimate 1878 396 396 660 = 0xe9735cf05 := by decide +kernel
private theorem b1878_396_1056 : blockEstimate 1878 396 1056 660 = 0x28be01ba1c := by decide +kernel
private theorem b1878_396_1716 : blockEstimate 1878 396 1716 660 = 0x15dfb51087 := by decide +kernel
private theorem b1878_396_2376 : blockEstimate 1878 396 2376 294 = 0xdf1d09ed := by decide +kernel
private theorem s1878_396_396_1320 : blockEstimate 1878 396 396 1320 = 0x3755378921 :=
  append (B := 1878) (J := 396) (start := 396) (a := 660) (x := 0xe9735cf05)
    b1878_396_396 1056 660 0x28be01ba1c 1320 0x3755378921 rfl rfl rfl b1878_396_1056
private theorem s1878_396_1716_954 : blockEstimate 1878 396 1716 954 = 0x16bed21a74 :=
  append (B := 1878) (J := 396) (start := 1716) (a := 660) (x := 0x15dfb51087)
    b1878_396_1716 2376 294 0xdf1d09ed 954 0x16bed21a74 rfl rfl rfl b1878_396_2376
private theorem s1878_396_396_2274 : blockEstimate 1878 396 396 2274 = 0x4e1409a395 :=
  append (B := 1878) (J := 396) (start := 396) (a := 1320) (x := 0x3755378921)
    s1878_396_396_1320 1716 954 0x16bed21a74 2274 0x4e1409a395 rfl rfl rfl s1878_396_1716_954
theorem moment1878_396 : momentEstimate 1878 396 = 0x4e1409a395 := by
  change blockEstimate 1878 396 396 2274 = 0x4e1409a395
  exact s1878_396_396_2274

private theorem b794_177_177 : blockEstimate 794 177 177 660 = 0x23e783341 := by decide +kernel
private theorem b794_177_837 : blockEstimate 794 177 837 311 = 0x607bee5e := by decide +kernel
private theorem s794_177_177_971 : blockEstimate 794 177 177 971 = 0x29ef4219f :=
  append (B := 794) (J := 177) (start := 177) (a := 660) (x := 0x23e783341)
    b794_177_177 837 311 0x607bee5e 971 0x29ef4219f rfl rfl rfl b794_177_837
theorem moment794_177 : momentEstimate 794 177 = 0x29ef4219f := by
  change blockEstimate 794 177 177 971 = 0x29ef4219f
  exact s794_177_177_971

private theorem b584_129_129 : blockEstimate 584 129 129 660 = 0xc3437143 := by decide +kernel
private theorem b584_129_789 : blockEstimate 584 129 789 53 = 0x732a2b := by decide +kernel
private theorem s584_129_129_713 : blockEstimate 584 129 129 713 = 0xc3b69b6e :=
  append (B := 584) (J := 129) (start := 129) (a := 660) (x := 0xc3437143)
    b584_129_129 789 53 0x732a2b 713 0xc3b69b6e rfl rfl rfl b584_129_789
theorem moment584_129 : momentEstimate 584 129 = 0xc3b69b6e := by
  change blockEstimate 584 129 129 713 = 0xc3b69b6e
  exact s584_129_129_713

private theorem b471_104_104 : blockEstimate 471 104 104 575 = 0x53100efb := by decide +kernel
theorem moment471_104 : momentEstimate 471 104 = 0x53100efb := by
  change blockEstimate 471 104 104 575 = 0x53100efb
  exact b471_104_104

private theorem b197_43_43 : blockEstimate 197 43 43 240 = 0x294fec6 := by decide +kernel
theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := by
  change blockEstimate 197 43 43 240 = 0x294fec6
  exact b197_43_43

private theorem b119_26_26 : blockEstimate 119 26 26 145 = 0x5a8245 := by decide +kernel
theorem moment119_26 : momentEstimate 119 26 = 0x5a8245 := by
  change blockEstimate 119 26 26 145 = 0x5a8245
  exact b119_26_26

end HighCore82258BankProof
