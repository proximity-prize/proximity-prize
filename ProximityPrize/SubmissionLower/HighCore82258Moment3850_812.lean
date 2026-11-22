import ProximityPrize.SubmissionLower.HighCore82258Moments4

set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem part3850_812_0 : blockEstimate 3850 812 812 220 = 0x18b348861 := by decide +kernel
private theorem part3850_812_1 : blockEstimate 3850 812 1032 220 = 0xa2c7e3b65 := by decide +kernel
private theorem part3850_812_2 : blockEstimate 3850 812 1252 220 = 0x19e3fc64c9 := by decide +kernel
private theorem part3850_812_3 : blockEstimate 3850 812 1472 220 = 0x2f0578b7aa := by decide +kernel
private theorem part3850_812_4 : blockEstimate 3850 812 1692 220 = 0x45759a29cc := by decide +kernel
private theorem part3850_812_5 : blockEstimate 3850 812 1912 220 = 0x584bbc084c := by decide +kernel
private theorem part3850_812_6 : blockEstimate 3850 812 2132 220 = 0x6719e4994c := by decide +kernel
private theorem part3850_812_7 : blockEstimate 3850 812 2352 220 = 0x71e013dccc := by decide +kernel
private theorem part3850_812_8 : blockEstimate 3850 812 2572 220 = 0x789e49d2cc := by decide +kernel
private theorem part3850_812_9 : blockEstimate 3850 812 2792 220 = 0x7b54867b4c := by decide +kernel
private theorem part3850_812_10 : blockEstimate 3850 812 3012 220 = 0x7a02c9d64c := by decide +kernel
private theorem part3850_812_11 : blockEstimate 3850 812 3232 220 = 0x74a913e3cc := by decide +kernel
private theorem part3850_812_12 : blockEstimate 3850 812 3452 220 = 0x6b4764a3cc := by decide +kernel
private theorem part3850_812_13 : blockEstimate 3850 812 3672 220 = 0x5dde99bae0 := by decide +kernel
private theorem part3850_812_14 : blockEstimate 3850 812 3892 220 = 0x4d4d233ab2 := by decide +kernel
private theorem part3850_812_15 : blockEstimate 3850 812 4112 220 = 0x3c0d29e8e4 := by decide +kernel
private theorem part3850_812_16 : blockEstimate 3850 812 4332 220 = 0x2b6f374ee1 := by decide +kernel
private theorem part3850_812_17 : blockEstimate 3850 812 4552 220 = 0x1c699a31db := by decide +kernel
private theorem part3850_812_18 : blockEstimate 3850 812 4772 220 = 0xfd7341e17 := by decide +kernel
private theorem part3850_812_19 : blockEstimate 3850 812 4992 220 = 0x6a03a0b28 := by decide +kernel
private theorem part3850_812_20 : blockEstimate 3850 812 5212 220 = 0x151315527 := by decide +kernel
private theorem part3850_812_21 : blockEstimate 3850 812 5432 42 = 0x1909942 := by decide +kernel
theorem moment3850_812 : momentEstimate 3850 812 = 0x5601e71ab3f := by
  exact moment_from_blocks [⟨220,0x18b348861⟩, ⟨220,0xa2c7e3b65⟩, ⟨220,0x19e3fc64c9⟩, ⟨220,0x2f0578b7aa⟩, ⟨220,0x45759a29cc⟩, ⟨220,0x584bbc084c⟩, ⟨220,0x6719e4994c⟩, ⟨220,0x71e013dccc⟩, ⟨220,0x789e49d2cc⟩, ⟨220,0x7b54867b4c⟩, ⟨220,0x7a02c9d64c⟩, ⟨220,0x74a913e3cc⟩, ⟨220,0x6b4764a3cc⟩, ⟨220,0x5dde99bae0⟩, ⟨220,0x4d4d233ab2⟩, ⟨220,0x3c0d29e8e4⟩, ⟨220,0x2b6f374ee1⟩, ⟨220,0x1c699a31db⟩, ⟨220,0xfd7341e17⟩, ⟨220,0x6a03a0b28⟩, ⟨220,0x151315527⟩, ⟨42,0x1909942⟩]
    ⟨part3850_812_0, part3850_812_1, part3850_812_2, part3850_812_3, part3850_812_4, part3850_812_5, part3850_812_6, part3850_812_7, part3850_812_8, part3850_812_9, part3850_812_10, part3850_812_11, part3850_812_12, part3850_812_13, part3850_812_14, part3850_812_15, part3850_812_16, part3850_812_17, part3850_812_18, part3850_812_19, part3850_812_20, part3850_812_21,trivial⟩ rfl rfl

end HighCore82258BankProof
