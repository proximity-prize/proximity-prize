import ProximityPrize.SubmissionLower.HighCore82258Moments1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem moment1412_298 : momentEstimate 1412 298 = 0x1901657cf3 := by
  exact moment_from_blocks [⟨220,0x85ca4bb9⟩, ⟨220,0x2f80c624d⟩, ⟨220,0x53deec90a⟩, ⟨220,0x60dd02fba⟩, ⟨220,0x562292fea⟩, ⟨220,0x36855c5aa⟩, ⟨220,0x14beb9b41⟩, ⟨170,0x21654554⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

theorem moment1443_329 : momentEstimate 1443 329 = 0x1cf53a5560 :=
  P1_7_1_3_3.moment1443_329

theorem moment1550_329 : momentEstimate 1550 329 = 0x2473d5ffe4 :=
  P1_7_1_3_3.moment1550_329

theorem moment1696_357 : momentEstimate 1696 357 = 0x33e3754396 :=
  P1_7_1_3_3.moment1696_357

theorem moment1725_359 : momentEstimate 1725 359 = 0x370899d961 :=
  P1_7_1_3_3.moment1725_359

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
