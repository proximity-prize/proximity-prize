import ProximityPrize.SubmissionLower.HighCore82258Moments4

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem part4863_1027_0 : blockEstimate 4863 1027 1027 220 = 0x1f7d3062d := by decide +kernel
private theorem part4863_1027_1 : blockEstimate 4863 1027 1247 220 = 0xd1ef49e41 := by decide +kernel
private theorem part4863_1027_2 : blockEstimate 4863 1027 1467 220 = 0x21df367175 := by decide +kernel
private theorem part4863_1027_3 : blockEstimate 4863 1027 1687 220 = 0x3e95b69cc9 := by decide +kernel
private theorem part4863_1027_4 : blockEstimate 4863 1027 1907 220 = 0x6190f6933b := by decide +kernel
private theorem part4863_1027_5 : blockEstimate 4863 1027 2127 220 = 0x85e0c8c95c := by decide +kernel
private theorem part4863_1027_6 : blockEstimate 4863 1027 2347 220 = 0xa59442cf7c := by decide +kernel
private theorem part4863_1027_7 : blockEstimate 4863 1027 2567 220 = 0xc02edb079c := by decide +kernel
private theorem part4863_1027_8 : blockEstimate 4863 1027 2787 220 = 0xd5b09171bc := by decide +kernel
private theorem part4863_1027_9 : blockEstimate 4863 1027 3007 220 = 0xe619660ddc := by decide +kernel
private theorem part4863_1027_10 : blockEstimate 4863 1027 3227 220 = 0xf16958dbfc := by decide +kernel
private theorem part4863_1027_11 : blockEstimate 4863 1027 3447 220 = 0xf7a069dc1c := by decide +kernel
private theorem part4863_1027_12 : blockEstimate 4863 1027 3667 220 = 0xf8be990e3c := by decide +kernel
private theorem part4863_1027_13 : blockEstimate 4863 1027 3887 220 = 0xf4c3e6725c := by decide +kernel
private theorem part4863_1027_14 : blockEstimate 4863 1027 4107 220 = 0xebb052087c := by decide +kernel
private theorem part4863_1027_15 : blockEstimate 4863 1027 4327 220 = 0xdd83dbd09c := by decide +kernel
private theorem part4863_1027_16 : blockEstimate 4863 1027 4547 220 = 0xca3e83cabc := by decide +kernel
private theorem part4863_1027_17 : blockEstimate 4863 1027 4767 220 = 0xb1fc898b7c := by decide +kernel
private theorem part4863_1027_18 : blockEstimate 4863 1027 4987 220 = 0x96d437f8b7 := by decide +kernel
private theorem part4863_1027_19 : blockEstimate 4863 1027 5207 220 = 0x7b41e8c38f := by decide +kernel
private theorem part4863_1027_20 : blockEstimate 4863 1027 5427 220 = 0x60685b5f7d := by decide +kernel
private theorem part4863_1027_21 : blockEstimate 4863 1027 5647 220 = 0x47483808a9 := by decide +kernel
private theorem part4863_1027_22 : blockEstimate 4863 1027 5867 220 = 0x30b1f8c7a7 := by decide +kernel
private theorem part4863_1027_23 : blockEstimate 4863 1027 6087 220 = 0x1d9a1cabd0 := by decide +kernel
private theorem part4863_1027_24 : blockEstimate 4863 1027 6307 220 = 0xedc127a15 := by decide +kernel
private theorem part4863_1027_25 : blockEstimate 4863 1027 6527 220 = 0x4fb4675a8 := by decide +kernel
private theorem part4863_1027_26 : blockEstimate 4863 1027 6747 170 = 0x77dac75b := by decide +kernel
theorem moment4863_1027 : momentEstimate 4863 1027 = 0xdb0e8041cee := by
  exact moment_from_blocks [⟨220,0x1f7d3062d⟩, ⟨220,0xd1ef49e41⟩, ⟨220,0x21df367175⟩, ⟨220,0x3e95b69cc9⟩, ⟨220,0x6190f6933b⟩, ⟨220,0x85e0c8c95c⟩, ⟨220,0xa59442cf7c⟩, ⟨220,0xc02edb079c⟩, ⟨220,0xd5b09171bc⟩, ⟨220,0xe619660ddc⟩, ⟨220,0xf16958dbfc⟩, ⟨220,0xf7a069dc1c⟩, ⟨220,0xf8be990e3c⟩, ⟨220,0xf4c3e6725c⟩, ⟨220,0xebb052087c⟩, ⟨220,0xdd83dbd09c⟩, ⟨220,0xca3e83cabc⟩, ⟨220,0xb1fc898b7c⟩, ⟨220,0x96d437f8b7⟩, ⟨220,0x7b41e8c38f⟩, ⟨220,0x60685b5f7d⟩, ⟨220,0x47483808a9⟩, ⟨220,0x30b1f8c7a7⟩, ⟨220,0x1d9a1cabd0⟩, ⟨220,0xedc127a15⟩, ⟨220,0x4fb4675a8⟩, ⟨170,0x77dac75b⟩]
    ⟨part4863_1027_0, part4863_1027_1, part4863_1027_2, part4863_1027_3, part4863_1027_4, part4863_1027_5, part4863_1027_6, part4863_1027_7, part4863_1027_8, part4863_1027_9, part4863_1027_10, part4863_1027_11, part4863_1027_12, part4863_1027_13, part4863_1027_14, part4863_1027_15, part4863_1027_16, part4863_1027_17, part4863_1027_18, part4863_1027_19, part4863_1027_20, part4863_1027_21, part4863_1027_22, part4863_1027_23, part4863_1027_24, part4863_1027_25, part4863_1027_26,trivial⟩ rfl rfl

end HighCore82258BankProof
