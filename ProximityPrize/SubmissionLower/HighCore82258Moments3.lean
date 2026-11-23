import ProximityPrize.SubmissionLower.HighCore82258Moments2

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b4851_1023_1023 : blockEstimate 4851 1023 1023 660 = 0x30d3907bb3 := by decide +kernel
private theorem b4851_1023_1683 : blockEstimate 4851 1023 1683 660 = 0x124f46df14d := by decide +kernel
private theorem b4851_1023_2343 : blockEstimate 4851 1023 2343 660 = 0x23816c40400 := by decide +kernel
private theorem b4851_1023_3003 : blockEstimate 4851 1023 3003 660 = 0x2c9bee9a400 := by decide +kernel
private theorem b4851_1023_3663 : blockEstimate 4851 1023 3663 660 = 0x2d250554400 := by decide +kernel
private theorem b4851_1023_4323 : blockEstimate 4851 1023 4323 660 = 0x251ed227983 := by decide +kernel
private theorem b4851_1023_4983 : blockEstimate 4851 1023 4983 660 = 0x16b4cd05c05 := by decide +kernel
private theorem b4851_1023_5643 : blockEstimate 4851 1023 5643 660 = 0x90ac9b554e := by decide +kernel
private theorem b4851_1023_6303 : blockEstimate 4851 1023 6303 594 = 0x12bcf3ae72 := by decide +kernel
private theorem s4851_1023_1023_1320 : blockEstimate 4851 1023 1023 1320 = 0x155c7fe6d00 :=
  append (B := 4851) (J := 1023) (start := 1023) (a := 660) (x := 0x30d3907bb3)
    b4851_1023_1023 1683 660 0x124f46df14d 1320 0x155c7fe6d00 rfl rfl rfl b4851_1023_1683
private theorem s4851_1023_2343_1320 : blockEstimate 4851 1023 2343 1320 = 0x501d5ada800 :=
  append (B := 4851) (J := 1023) (start := 2343) (a := 660) (x := 0x23816c40400)
    b4851_1023_2343 3003 660 0x2c9bee9a400 1320 0x501d5ada800 rfl rfl rfl b4851_1023_3003
private theorem s4851_1023_3663_1320 : blockEstimate 4851 1023 3663 1320 = 0x5243d77bd83 :=
  append (B := 4851) (J := 1023) (start := 3663) (a := 660) (x := 0x2d250554400)
    b4851_1023_3663 4323 660 0x251ed227983 1320 0x5243d77bd83 rfl rfl rfl b4851_1023_4323
private theorem s4851_1023_4983_1320 : blockEstimate 4851 1023 4983 1320 = 0x1fbf96bb153 :=
  append (B := 4851) (J := 1023) (start := 4983) (a := 660) (x := 0x16b4cd05c05)
    b4851_1023_4983 5643 660 0x90ac9b554e 1320 0x1fbf96bb153 rfl rfl rfl b4851_1023_5643
private theorem s4851_1023_1023_2640 : blockEstimate 4851 1023 1023 2640 = 0x6579dac1500 :=
  append (B := 4851) (J := 1023) (start := 1023) (a := 1320) (x := 0x155c7fe6d00)
    s4851_1023_1023_1320 2343 1320 0x501d5ada800 2640 0x6579dac1500 rfl rfl rfl s4851_1023_2343_1320
private theorem s4851_1023_3663_2640 : blockEstimate 4851 1023 3663 2640 = 0x72036e36ed6 :=
  append (B := 4851) (J := 1023) (start := 3663) (a := 1320) (x := 0x5243d77bd83)
    s4851_1023_3663_1320 4983 1320 0x1fbf96bb153 2640 0x72036e36ed6 rfl rfl rfl s4851_1023_4983_1320
private theorem s4851_1023_1023_5280 : blockEstimate 4851 1023 1023 5280 = 0xd77d48f83d6 :=
  append (B := 4851) (J := 1023) (start := 1023) (a := 2640) (x := 0x6579dac1500)
    s4851_1023_1023_2640 3663 2640 0x72036e36ed6 5280 0xd77d48f83d6 rfl rfl rfl s4851_1023_3663_2640
private theorem s4851_1023_1023_5874 : blockEstimate 4851 1023 1023 5874 = 0xd8a91833248 :=
  append (B := 4851) (J := 1023) (start := 1023) (a := 5280) (x := 0xd77d48f83d6)
    s4851_1023_1023_5280 6303 594 0x12bcf3ae72 5874 0xd8a91833248 rfl rfl rfl b4851_1023_6303
theorem moment4851_1023 : momentEstimate 4851 1023 = 0xd8a91833248 := by
  change blockEstimate 4851 1023 1023 5874 = 0xd8a91833248
  exact s4851_1023_1023_5874

private theorem b2489_526_526 : blockEstimate 2489 526 526 660 = 0x162e6ea156 := by decide +kernel
private theorem b2489_526_1186 : blockEstimate 2489 526 1186 660 = 0x55675ab6dc := by decide +kernel
private theorem b2489_526_1846 : blockEstimate 2489 526 1846 660 = 0x5b63e11498 := by decide +kernel
private theorem b2489_526_2506 : blockEstimate 2489 526 2506 660 = 0x27aedf2a7e := by decide +kernel
private theorem b2489_526_3166 : blockEstimate 2489 526 3166 375 = 0x26561c204 := by decide +kernel
private theorem s2489_526_526_1320 : blockEstimate 2489 526 526 1320 = 0x6b95c95832 :=
  append (B := 2489) (J := 526) (start := 526) (a := 660) (x := 0x162e6ea156)
    b2489_526_526 1186 660 0x55675ab6dc 1320 0x6b95c95832 rfl rfl rfl b2489_526_1186
private theorem s2489_526_1846_1320 : blockEstimate 2489 526 1846 1320 = 0x8312c03f16 :=
  append (B := 2489) (J := 526) (start := 1846) (a := 660) (x := 0x5b63e11498)
    b2489_526_1846 2506 660 0x27aedf2a7e 1320 0x8312c03f16 rfl rfl rfl b2489_526_2506
private theorem s2489_526_526_2640 : blockEstimate 2489 526 526 2640 = 0xeea8899748 :=
  append (B := 2489) (J := 526) (start := 526) (a := 1320) (x := 0x6b95c95832)
    s2489_526_526_1320 1846 1320 0x8312c03f16 2640 0xeea8899748 rfl rfl rfl s2489_526_1846_1320
private theorem s2489_526_526_3015 : blockEstimate 2489 526 526 3015 = 0xf10deb594c :=
  append (B := 2489) (J := 526) (start := 526) (a := 2640) (x := 0xeea8899748)
    s2489_526_526_2640 3166 375 0x26561c204 3015 0xf10deb594c rfl rfl rfl b2489_526_3166
theorem moment2489_526 : momentEstimate 2489 526 = 0xf10deb594c := by
  change blockEstimate 2489 526 526 3015 = 0xf10deb594c
  exact s2489_526_526_3015

private theorem b1202_254_254 : blockEstimate 1202 254 254 660 = 0x64265f903 := by decide +kernel
private theorem b1202_254_914 : blockEstimate 1202 254 914 660 = 0x6d768c715 := by decide +kernel
private theorem b1202_254_1574 : blockEstimate 1202 254 1574 136 = 0xeb46cd0 := by decide +kernel
private theorem s1202_254_254_1320 : blockEstimate 1202 254 254 1320 = 0xd19cec018 :=
  append (B := 1202) (J := 254) (start := 254) (a := 660) (x := 0x64265f903)
    b1202_254_254 914 660 0x6d768c715 1320 0xd19cec018 rfl rfl rfl b1202_254_914
private theorem s1202_254_254_1456 : blockEstimate 1202 254 254 1456 = 0xd28832ce8 :=
  append (B := 1202) (J := 254) (start := 254) (a := 1320) (x := 0xd19cec018)
    s1202_254_254_1320 1574 136 0xeb46cd0 1456 0xd28832ce8 rfl rfl rfl b1202_254_1574
theorem moment1202_254 : momentEstimate 1202 254 = 0xd28832ce8 := by
  change blockEstimate 1202 254 254 1456 = 0xd28832ce8
  exact s1202_254_254_1456

private theorem b906_191_191 : blockEstimate 906 191 191 660 = 0x32889f870 := by decide +kernel
private theorem b906_191_851 : blockEstimate 906 191 851 437 = 0x1173c1a5a := by decide +kernel
private theorem s906_191_191_1097 : blockEstimate 906 191 191 1097 = 0x43fc612ca :=
  append (B := 906) (J := 191) (start := 191) (a := 660) (x := 0x32889f870)
    b906_191_191 851 437 0x1173c1a5a 1097 0x43fc612ca rfl rfl rfl b906_191_851
theorem moment906_191 : momentEstimate 906 191 = 0x43fc612ca := by
  change blockEstimate 906 191 191 1097 = 0x43fc612ca
  exact s906_191_191_1097

private theorem b606_128_128 : blockEstimate 606 128 128 660 = 0xd9d869d0 := by decide +kernel
private theorem b606_128_788 : blockEstimate 606 128 788 74 = 0x138e9a2 := by decide +kernel
private theorem s606_128_128_734 : blockEstimate 606 128 128 734 = 0xdb115372 :=
  append (B := 606) (J := 128) (start := 128) (a := 660) (x := 0xd9d869d0)
    b606_128_128 788 74 0x138e9a2 734 0xdb115372 rfl rfl rfl b606_128_788
theorem moment606_128 : momentEstimate 606 128 = 0xdb115372 := by
  change blockEstimate 606 128 128 734 = 0xdb115372
  exact s606_128_128_734

private theorem b554_118_118 : blockEstimate 554 118 118 660 = 0x9a3463f2 := by decide +kernel
private theorem b554_118_778 : blockEstimate 554 118 778 12 = 0x1b357 := by decide +kernel
private theorem s554_118_118_672 : blockEstimate 554 118 118 672 = 0x9a361749 :=
  append (B := 554) (J := 118) (start := 118) (a := 660) (x := 0x9a3463f2)
    b554_118_118 778 12 0x1b357 672 0x9a361749 rfl rfl rfl b554_118_778
theorem moment554_118 : momentEstimate 554 118 = 0x9a361749 := by
  change blockEstimate 554 118 118 672 = 0x9a361749
  exact s554_118_118_672

private theorem b175_39_39 : blockEstimate 175 39 39 214 = 0x1a458a5 := by decide +kernel
theorem moment175_39 : momentEstimate 175 39 = 0x1a458a5 := by
  change blockEstimate 175 39 39 214 = 0x1a458a5
  exact b175_39_39

private theorem b97_21_21 : blockEstimate 97 21 21 118 = 0x284e2c := by decide +kernel
theorem moment97_21 : momentEstimate 97 21 = 0x284e2c := by
  change blockEstimate 97 21 21 118 = 0x284e2c
  exact b97_21_21

end HighCore82258BankProof
