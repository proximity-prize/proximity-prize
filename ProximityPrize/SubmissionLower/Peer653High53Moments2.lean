-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moments2.lean.
import ProximityPrize.SubmissionLower.Peer653High53Moments1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem moment1412_298 : momentEstimate 1412 298 = 0x1901657cf3 := by
  exact moment_from_blocks [⟨220,0x85ca4bb9⟩, ⟨220,0x2f80c624d⟩, ⟨220,0x53deec90a⟩, ⟨220,0x60dd02fba⟩, ⟨220,0x562292fea⟩, ⟨220,0x36855c5aa⟩, ⟨220,0x14beb9b41⟩, ⟨170,0x21654554⟩]
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel),trivial⟩ rfl rfl

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


end Peer653High53BankProof
