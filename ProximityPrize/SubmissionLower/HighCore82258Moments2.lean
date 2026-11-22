import ProximityPrize.SubmissionLower.HighCore82258Moments1

set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem moment1412_298 : momentEstimate 1412 298 = 0x1901657cf3 := by
  exact moment_from_blocks [⟨220,0x85ca4bb9⟩, ⟨220,0x2f80c624d⟩, ⟨220,0x53deec90a⟩, ⟨220,0x60dd02fba⟩, ⟨220,0x562292fea⟩, ⟨220,0x36855c5aa⟩, ⟨220,0x14beb9b41⟩, ⟨170,0x21654554⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment1443_329 : momentEstimate 1443 329 = 0x1cf53a5560 := by
  exact moment_from_blocks [⟨220,0x891d3c1d⟩, ⟨220,0x31dcc1aad⟩, ⟨220,0x5c2fe278a⟩, ⟨220,0x6d4b1c03a⟩, ⟨220,0x6438375ea⟩, ⟨220,0x43b7f6bae⟩, ⟨220,0x1e334ebfc⟩, ⟨220,0x5464d4f4⟩, ⟨12,0x4744a⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

private theorem part1550_329_0 : blockEstimate 1550 329 329 220 = 0x949658d1 := by decide +kernel
private theorem part1550_329_1 : blockEstimate 1550 329 549 220 = 0x36c0900e1 := by decide +kernel
private theorem part1550_329_2 : blockEstimate 1550 329 769 220 = 0x675b8049a := by decide +kernel
private theorem part1550_329_3 : blockEstimate 1550 329 989 220 = 0x7ed48f22a := by decide +kernel
private theorem part1550_329_4 : blockEstimate 1550 329 1209 220 = 0x7c1f7fcba := by decide +kernel
private theorem part1550_329_5 : blockEstimate 1550 329 1429 220 = 0x5f8aaf58a := by decide +kernel
private theorem part1550_329_6 : blockEstimate 1550 329 1649 220 = 0x344adf0aa := by decide +kernel
private theorem part1550_329_7 : blockEstimate 1550 329 1869 220 = 0x103e74f26 := by decide +kernel
private theorem part1550_329_8 : blockEstimate 1550 329 2089 119 = 0xcfd7d5a := by decide +kernel
theorem moment1550_329 : momentEstimate 1550 329 = 0x2473d5ffe4 := by
  exact moment_from_blocks [⟨220,0x949658d1⟩, ⟨220,0x36c0900e1⟩, ⟨220,0x675b8049a⟩, ⟨220,0x7ed48f22a⟩, ⟨220,0x7c1f7fcba⟩, ⟨220,0x5f8aaf58a⟩, ⟨220,0x344adf0aa⟩, ⟨220,0x103e74f26⟩, ⟨119,0xcfd7d5a⟩]
    ⟨part1550_329_0, part1550_329_1, part1550_329_2, part1550_329_3, part1550_329_4, part1550_329_5, part1550_329_6, part1550_329_7, part1550_329_8,trivial⟩ rfl rfl

private theorem part1696_357_0 : blockEstimate 1696 357 357 220 = 0xa43dfec9 := by decide +kernel
private theorem part1696_357_1 : blockEstimate 1696 357 577 220 = 0x3e0fb7b3c := by decide +kernel
private theorem part1696_357_2 : blockEstimate 1696 357 797 220 = 0x7bf3ea0be := by decide +kernel
private theorem part1696_357_3 : blockEstimate 1696 357 1017 220 = 0x9fbec0aae := by decide +kernel
private theorem part1696_357_4 : blockEstimate 1696 357 1237 220 = 0xa722cef9e := by decide +kernel
private theorem part1696_357_5 : blockEstimate 1696 357 1457 220 = 0x922014f8e := by decide +kernel
private theorem part1696_357_6 : blockEstimate 1696 357 1677 220 = 0x63c28fec3 := by decide +kernel
private theorem part1696_357_7 : blockEstimate 1696 357 1897 220 = 0x30ce67a41 := by decide +kernel
private theorem part1696_357_8 : blockEstimate 1696 357 2117 220 = 0xc26995d4 := by decide +kernel
private theorem part1696_357_9 : blockEstimate 1696 357 2337 73 = 0x369d021 := by decide +kernel
theorem moment1696_357 : momentEstimate 1696 357 = 0x33e3754396 := by
  exact moment_from_blocks [⟨220,0xa43dfec9⟩, ⟨220,0x3e0fb7b3c⟩, ⟨220,0x7bf3ea0be⟩, ⟨220,0x9fbec0aae⟩, ⟨220,0xa722cef9e⟩, ⟨220,0x922014f8e⟩, ⟨220,0x63c28fec3⟩, ⟨220,0x30ce67a41⟩, ⟨220,0xc26995d4⟩, ⟨73,0x369d021⟩]
    ⟨part1696_357_0, part1696_357_1, part1696_357_2, part1696_357_3, part1696_357_4, part1696_357_5, part1696_357_6, part1696_357_7, part1696_357_8, part1696_357_9,trivial⟩ rfl rfl

private theorem part1725_359_0 : blockEstimate 1725 359 359 220 = 0xa75a08f5 := by decide +kernel
private theorem part1725_359_1 : blockEstimate 1725 359 579 220 = 0x3f6f14385 := by decide +kernel
private theorem part1725_359_2 : blockEstimate 1725 359 799 220 = 0x7f7b3ab38 := by decide +kernel
private theorem part1725_359_3 : blockEstimate 1725 359 1019 220 = 0xa56bc2e78 := by decide +kernel
private theorem part1725_359_4 : blockEstimate 1725 359 1239 220 = 0xaecce45b8 := by decide +kernel
private theorem part1725_359_5 : blockEstimate 1725 359 1459 220 = 0x9b9e9f0f8 := by decide +kernel
private theorem part1725_359_6 : blockEstimate 1725 359 1679 220 = 0x6dda2a9f6 := by decide +kernel
private theorem part1725_359_7 : blockEstimate 1725 359 1899 220 = 0x389ee88a9 := by decide +kernel
private theorem part1725_359_8 : blockEstimate 1725 359 2119 220 = 0x103cdd6de := by decide +kernel
private theorem part1725_359_9 : blockEstimate 1725 359 2339 104 = 0x9c7730a := by decide +kernel
theorem moment1725_359 : momentEstimate 1725 359 = 0x370899d961 := by
  exact moment_from_blocks [⟨220,0xa75a08f5⟩, ⟨220,0x3f6f14385⟩, ⟨220,0x7f7b3ab38⟩, ⟨220,0xa56bc2e78⟩, ⟨220,0xaecce45b8⟩, ⟨220,0x9b9e9f0f8⟩, ⟨220,0x6dda2a9f6⟩, ⟨220,0x389ee88a9⟩, ⟨220,0x103cdd6de⟩, ⟨104,0x9c7730a⟩]
    ⟨part1725_359_0, part1725_359_1, part1725_359_2, part1725_359_3, part1725_359_4, part1725_359_5, part1725_359_6, part1725_359_7, part1725_359_8, part1725_359_9,trivial⟩ rfl rfl

private theorem part1815_383_0 : blockEstimate 1815 383 383 220 = 0xb10080cd := by decide +kernel
private theorem part1815_383_1 : blockEstimate 1815 383 603 220 = 0x43e4f2813 := by decide +kernel
private theorem part1815_383_2 : blockEstimate 1815 383 823 220 = 0x8db58ac80 := by decide +kernel
private theorem part1815_383_3 : blockEstimate 1815 383 1043 220 = 0xbd3d7c880 := by decide +kernel
private theorem part1815_383_4 : blockEstimate 1815 383 1263 220 = 0xce4e9a480 := by decide +kernel
private theorem part1815_383_5 : blockEstimate 1815 383 1483 220 = 0xc0e8e4080 := by decide +kernel
private theorem part1815_383_6 : blockEstimate 1815 383 1703 220 = 0x9582eba84 := by decide +kernel
private theorem part1815_383_7 : blockEstimate 1815 383 1923 220 = 0x59a1ff296 := by decide +kernel
private theorem part1815_383_8 : blockEstimate 1815 383 2143 220 = 0x24c7dcb97 := by decide +kernel
private theorem part1815_383_9 : blockEstimate 1815 383 2363 218 = 0x5a013f01 := by decide +kernel
theorem moment1815_383 : momentEstimate 1815 383 = 0x442ac5ba92 := by
  exact moment_from_blocks [⟨220,0xb10080cd⟩, ⟨220,0x43e4f2813⟩, ⟨220,0x8db58ac80⟩, ⟨220,0xbd3d7c880⟩, ⟨220,0xce4e9a480⟩, ⟨220,0xc0e8e4080⟩, ⟨220,0x9582eba84⟩, ⟨220,0x59a1ff296⟩, ⟨220,0x24c7dcb97⟩, ⟨218,0x5a013f01⟩]
    ⟨part1815_383_0, part1815_383_1, part1815_383_2, part1815_383_3, part1815_383_4, part1815_383_5, part1815_383_6, part1815_383_7, part1815_383_8, part1815_383_9,trivial⟩ rfl rfl

private theorem part2034_430_0 : blockEstimate 2034 430 430 220 = 0xc87bf9c1 := by decide +kernel
private theorem part2034_430_1 : blockEstimate 2034 430 650 220 = 0x4e3f4d3f4 := by decide +kernel
private theorem part2034_430_2 : blockEstimate 2034 430 870 220 = 0xae80a0832 := by decide +kernel
private theorem part2034_430_3 : blockEstimate 2034 430 1090 220 = 0xf6b22dc22 := by decide +kernel
private theorem part2034_430_4 : blockEstimate 2034 430 1310 220 = 0x11cb25bb92 := by decide +kernel
private theorem part2034_430_5 : blockEstimate 2034 430 1530 220 = 0x120812a682 := by decide +kernel
private theorem part2034_430_6 : blockEstimate 2034 430 1750 220 = 0x1021e99cf2 := by decide +kernel
private theorem part2034_430_7 : blockEstimate 2034 430 1970 220 = 0xc32470568 := by decide +kernel
private theorem part2034_430_8 : blockEstimate 2034 430 2190 220 = 0x7738b7944 := by decide +kernel
private theorem part2034_430_9 : blockEstimate 2034 430 2410 220 = 0x3514df015 := by decide +kernel
private theorem part2034_430_10 : blockEstimate 2034 430 2630 220 = 0xb0b10df9 := by decide +kernel
private theorem part2034_430_11 : blockEstimate 2034 430 2850 44 = 0xf10757 := by decide +kernel
theorem moment2034_430 : momentEstimate 2034 430 = 0x6b9d823520 := by
  exact moment_from_blocks [⟨220,0xc87bf9c1⟩, ⟨220,0x4e3f4d3f4⟩, ⟨220,0xae80a0832⟩, ⟨220,0xf6b22dc22⟩, ⟨220,0x11cb25bb92⟩, ⟨220,0x120812a682⟩, ⟨220,0x1021e99cf2⟩, ⟨220,0xc32470568⟩, ⟨220,0x7738b7944⟩, ⟨220,0x3514df015⟩, ⟨220,0xb0b10df9⟩, ⟨44,0xf10757⟩]
    ⟨part2034_430_0, part2034_430_1, part2034_430_2, part2034_430_3, part2034_430_4, part2034_430_5, part2034_430_6, part2034_430_7, part2034_430_8, part2034_430_9, part2034_430_10, part2034_430_11,trivial⟩ rfl rfl

private theorem part2035_429_0 : blockEstimate 2035 429 429 220 = 0xc8976cdd := by decide +kernel
private theorem part2035_429_1 : blockEstimate 2035 429 649 220 = 0x4e4b225b2 := by decide +kernel
private theorem part2035_429_2 : blockEstimate 2035 429 869 220 = 0xae7a415d6 := by decide +kernel
private theorem part2035_429_3 : blockEstimate 2035 429 1089 220 = 0xf68ad9b26 := by decide +kernel
private theorem part2035_429_4 : blockEstimate 2035 429 1309 220 = 0x11c7e61f76 := by decide +kernel
private theorem part2035_429_5 : blockEstimate 2035 429 1529 220 = 0x12054da2c6 := by decide +kernel
private theorem part2035_429_6 : blockEstimate 2035 429 1749 220 = 0x1020e42516 := by decide +kernel
private theorem part2035_429_7 : blockEstimate 2035 429 1969 220 = 0xc3351d9bf := by decide +kernel
private theorem part2035_429_8 : blockEstimate 2035 429 2189 220 = 0x7746c6985 := by decide +kernel
private theorem part2035_429_9 : blockEstimate 2035 429 2409 220 = 0x351c17911 := by decide +kernel
private theorem part2035_429_10 : blockEstimate 2035 429 2629 220 = 0xb0c8bb5c := by decide +kernel
private theorem part2035_429_11 : blockEstimate 2035 429 2849 44 = 0xf125fa := by decide +kernel
theorem moment2035_429 : momentEstimate 2035 429 = 0x6b96ecc888 := by
  exact moment_from_blocks [⟨220,0xc8976cdd⟩, ⟨220,0x4e4b225b2⟩, ⟨220,0xae7a415d6⟩, ⟨220,0xf68ad9b26⟩, ⟨220,0x11c7e61f76⟩, ⟨220,0x12054da2c6⟩, ⟨220,0x1020e42516⟩, ⟨220,0xc3351d9bf⟩, ⟨220,0x7746c6985⟩, ⟨220,0x351c17911⟩, ⟨220,0xb0c8bb5c⟩, ⟨44,0xf125fa⟩]
    ⟨part2035_429_0, part2035_429_1, part2035_429_2, part2035_429_3, part2035_429_4, part2035_429_5, part2035_429_6, part2035_429_7, part2035_429_8, part2035_429_9, part2035_429_10, part2035_429_11,trivial⟩ rfl rfl


end HighCore82258BankProof
