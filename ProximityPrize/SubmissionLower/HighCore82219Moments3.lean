import ProximityPrize.SubmissionLower.HighCore82219Moments2

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000
open private r1E r1F from ProximityPrize.SubmissionLower.GoldBranch7N1


theorem moment4705_995 : momentEstimate 4705 995 = 0xc029d47a706 := r1E

theorem moment4830_1019 : momentEstimate 4830 1019 = 0xd5013df2ef9 := P1_7_1_3_5.moment4830

private theorem part5736_1211_0 : blockEstimate 5736 1211 1211 220 = 0x2556e90a9 := by decide +kernel
private theorem part5736_1211_1 : blockEstimate 5736 1211 1431 220 = 0xfa926140d := by decide +kernel
private theorem part5736_1211_2 : blockEstimate 5736 1211 1651 220 = 0x28c00f0251 := by decide +kernel
private theorem part5736_1211_3 : blockEstimate 5736 1211 1871 220 = 0x4bf7477875 := by decide +kernel
private theorem part5736_1211_4 : blockEstimate 5736 1211 2091 220 = 0x77abed9379 := by decide +kernel
private theorem part5736_1211_5 : blockEstimate 5736 1211 2311 220 = 0xaa01f57ed0 := by decide +kernel
private theorem part5736_1211_6 : blockEstimate 5736 1211 2531 220 = 0xdc517b29b4 := by decide +kernel
private theorem part5736_1211_7 : blockEstimate 5736 1211 2751 220 = 0x108dd2c3e54 := by decide +kernel
private theorem part5736_1211_8 : blockEstimate 5736 1211 2971 220 = 0x12f666c80f4 := by decide +kernel
private theorem part5736_1211_9 : blockEstimate 5736 1211 3191 220 = 0x14fed3bf194 := by decide +kernel
private theorem part5736_1211_10 : blockEstimate 5736 1211 3411 220 = 0x16a719a9034 := by decide +kernel
private theorem part5736_1211_11 : blockEstimate 5736 1211 3631 220 = 0x17ef3885cd4 := by decide +kernel
private theorem part5736_1211_12 : blockEstimate 5736 1211 3851 220 = 0x18d73055774 := by decide +kernel
private theorem part5736_1211_13 : blockEstimate 5736 1211 4071 220 = 0x195f0118014 := by decide +kernel
private theorem part5736_1211_14 : blockEstimate 5736 1211 4291 220 = 0x1986aacd6b4 := by decide +kernel
private theorem part5736_1211_15 : blockEstimate 5736 1211 4511 220 = 0x194e2d75b54 := by decide +kernel
private theorem part5736_1211_16 : blockEstimate 5736 1211 4731 220 = 0x18b58910df4 := by decide +kernel
private theorem part5736_1211_17 : blockEstimate 5736 1211 4951 220 = 0x17bcbd9ee94 := by decide +kernel
private theorem part5736_1211_18 : blockEstimate 5736 1211 5171 220 = 0x1663cb1fd34 := by decide +kernel
private theorem part5736_1211_19 : blockEstimate 5736 1211 5391 220 = 0x14aab1939d4 := by decide +kernel
private theorem part5736_1211_20 : blockEstimate 5736 1211 5611 220 = 0x12925dae549 := by decide +kernel
private theorem part5736_1211_21 : blockEstimate 5736 1211 5831 220 = 0x103ad0e664a := by decide +kernel
private theorem part5736_1211_22 : blockEstimate 5736 1211 6051 220 = 0xdd49b0433e := by decide +kernel
private theorem part5736_1211_23 : blockEstimate 5736 1211 6271 220 = 0xb7390ef835 := by decide +kernel
private theorem part5736_1211_24 : blockEstimate 5736 1211 6491 220 = 0x92870f1bb9 := by decide +kernel
private theorem part5736_1211_25 : blockEstimate 5736 1211 6711 220 = 0x702c93065b := by decide +kernel
private theorem part5736_1211_26 : blockEstimate 5736 1211 6931 220 = 0x50e7179846 := by decide +kernel
private theorem part5736_1211_27 : blockEstimate 5736 1211 7151 220 = 0x35b795e60a := by decide +kernel
private theorem part5736_1211_28 : blockEstimate 5736 1211 7371 220 = 0x1f8dcd164c := by decide +kernel
private theorem part5736_1211_29 : blockEstimate 5736 1211 7591 220 = 0xeecfa40d8 := by decide +kernel
private theorem part5736_1211_30 : blockEstimate 5736 1211 7811 220 = 0x45803fc9e := by decide +kernel
private theorem part5736_1211_31 : blockEstimate 5736 1211 8031 127 = 0x3bd383a0 := by decide +kernel

theorem moment5736_1211 : momentEstimate 5736 1211 = 0x1a7cbea93549 := by
  exact moment_from_blocks (B := 5736) (J := 1211) (total := 0x1a7cbea93549)
    [⟨220,0x2556e90a9⟩, ⟨220,0xfa926140d⟩, ⟨220,0x28c00f0251⟩, ⟨220,0x4bf7477875⟩, ⟨220,0x77abed9379⟩, ⟨220,0xaa01f57ed0⟩, ⟨220,0xdc517b29b4⟩, ⟨220,0x108dd2c3e54⟩, ⟨220,0x12f666c80f4⟩, ⟨220,0x14fed3bf194⟩, ⟨220,0x16a719a9034⟩, ⟨220,0x17ef3885cd4⟩, ⟨220,0x18d73055774⟩, ⟨220,0x195f0118014⟩, ⟨220,0x1986aacd6b4⟩, ⟨220,0x194e2d75b54⟩, ⟨220,0x18b58910df4⟩, ⟨220,0x17bcbd9ee94⟩, ⟨220,0x1663cb1fd34⟩, ⟨220,0x14aab1939d4⟩, ⟨220,0x12925dae549⟩, ⟨220,0x103ad0e664a⟩, ⟨220,0xdd49b0433e⟩, ⟨220,0xb7390ef835⟩, ⟨220,0x92870f1bb9⟩, ⟨220,0x702c93065b⟩, ⟨220,0x50e7179846⟩, ⟨220,0x35b795e60a⟩, ⟨220,0x1f8dcd164c⟩, ⟨220,0xeecfa40d8⟩, ⟨220,0x45803fc9e⟩, ⟨127,0x3bd383a0⟩]
    ⟨part5736_1211_0, part5736_1211_1, part5736_1211_2, part5736_1211_3, part5736_1211_4, part5736_1211_5, part5736_1211_6, part5736_1211_7, part5736_1211_8, part5736_1211_9, part5736_1211_10, part5736_1211_11, part5736_1211_12, part5736_1211_13, part5736_1211_14, part5736_1211_15, part5736_1211_16, part5736_1211_17, part5736_1211_18, part5736_1211_19, part5736_1211_20, part5736_1211_21, part5736_1211_22, part5736_1211_23, part5736_1211_24, part5736_1211_25, part5736_1211_26, part5736_1211_27, part5736_1211_28, part5736_1211_29, part5736_1211_30, part5736_1211_31, trivial⟩
    rfl rfl

theorem moment5798_1223 : momentEstimate 5798 1223 = 0x1ba1a89b2ba1 := P1_7_1_3_5.moment5798

theorem moment7341_1556 : momentEstimate 7341 1556 = 0x4741ba66013a := r1F

theorem moment7630_1607 : momentEstimate 7630 1607 = 0x52bdbe618ec3 := P1_7_1_3_5.moment7630

end HighCore82219BankProof
