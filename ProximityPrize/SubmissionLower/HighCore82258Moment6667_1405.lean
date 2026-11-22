import ProximityPrize.SubmissionLower.HighCore82258Moments4
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

private theorem p6667_1405_1405_220 : blockEstimate 6667 1405 1405 220 = 0x2b9422f7d := by decide +kernel
private theorem p6667_1405_1625_220 : blockEstimate 6667 1405 1625 220 = 0x125e8a0951 := by decide +kernel
private theorem p6667_1405_1845_220 : blockEstimate 6667 1405 1845 220 = 0x3015e41345 := by decide +kernel
private theorem p6667_1405_2065_220 : blockEstimate 6667 1405 2065 220 = 0x5a3c6e6a59 := by decide +kernel
private theorem p6667_1405_2285_220 : blockEstimate 6667 1405 2285 220 = 0x8f2f472b8d := by decide +kernel
private theorem p6667_1405_2505_220 : blockEstimate 6667 1405 2505 220 = 0xcd4b8c73e1 := by decide +kernel
private theorem p6667_1405_2725_220 : blockEstimate 6667 1405 2725 220 = 0x1127037e96f := by decide +kernel
private theorem p6667_1405_2945_220 : blockEstimate 6667 1405 2945 220 = 0x15646747a96 := by decide +kernel
private theorem p6667_1405_3165_220 : blockEstimate 6667 1405 3165 220 = 0x193447d1666 := by decide +kernel
private theorem p6667_1405_3385_220 : blockEstimate 6667 1405 3385 220 = 0x1c949d45936 := by decide +kernel
private theorem p6667_1405_3605_220 : blockEstimate 6667 1405 3605 220 = 0x1f8567a4306 := by decide +kernel
private theorem p6667_1405_3825_220 : blockEstimate 6667 1405 3825 220 = 0x2206a6ed3d6 := by decide +kernel
private theorem p6667_1405_4045_220 : blockEstimate 6667 1405 4045 220 = 0x24185b20ba6 := by decide +kernel
private theorem p6667_1405_4265_220 : blockEstimate 6667 1405 4265 220 = 0x25ba843ea76 := by decide +kernel
private theorem p6667_1405_4485_220 : blockEstimate 6667 1405 4485 220 = 0x26ed2247046 := by decide +kernel
private theorem p6667_1405_4705_220 : blockEstimate 6667 1405 4705 220 = 0x27b03539d16 := by decide +kernel
private theorem p6667_1405_4925_220 : blockEstimate 6667 1405 4925 220 = 0x2803bd170e6 := by decide +kernel
private theorem p6667_1405_5145_220 : blockEstimate 6667 1405 5145 220 = 0x27e7b9debb6 := by decide +kernel
private theorem p6667_1405_5365_220 : blockEstimate 6667 1405 5365 220 = 0x275c2b90d86 := by decide +kernel
private theorem p6667_1405_5585_220 : blockEstimate 6667 1405 5585 220 = 0x2661122d656 := by decide +kernel
private theorem p6667_1405_5805_220 : blockEstimate 6667 1405 5805 220 = 0x24f66db4626 := by decide +kernel
private theorem p6667_1405_6025_220 : blockEstimate 6667 1405 6025 220 = 0x231c3e25cf6 := by decide +kernel
private theorem p6667_1405_6245_220 : blockEstimate 6667 1405 6245 220 = 0x20d28381ac6 := by decide +kernel
private theorem p6667_1405_6465_220 : blockEstimate 6667 1405 6465 220 = 0x1e193fb8e1d := by decide +kernel
private theorem p6667_1405_6685_220 : blockEstimate 6667 1405 6685 220 = 0x1b01c6d09be := by decide +kernel
private theorem p6667_1405_6905_220 : blockEstimate 6667 1405 6905 220 = 0x17c9339beaa := by decide +kernel
private theorem p6667_1405_7125_220 : blockEstimate 6667 1405 7125 220 = 0x148b430692a := by decide +kernel
private theorem p6667_1405_7345_220 : blockEstimate 6667 1405 7345 220 = 0x115975423c2 := by decide +kernel
private theorem p6667_1405_7565_220 : blockEstimate 6667 1405 7565 220 = 0xe4444541ef := by decide +kernel
private theorem p6667_1405_7785_220 : blockEstimate 6667 1405 7785 220 = 0xb5b2415044 := by decide +kernel
private theorem p6667_1405_8005_220 : blockEstimate 6667 1405 8005 220 = 0x8aa55ed071 := by decide +kernel
private theorem p6667_1405_8225_220 : blockEstimate 6667 1405 8225 220 = 0x63ed038cd8 := by decide +kernel
private theorem p6667_1405_8445_220 : blockEstimate 6667 1405 8445 220 = 0x42c76abfe4 := by decide +kernel
private theorem p6667_1405_8665_220 : blockEstimate 6667 1405 8665 220 = 0x27c071b366 := by decide +kernel
private theorem p6667_1405_8885_220 : blockEstimate 6667 1405 8885 220 = 0x135afefe4e := by decide +kernel
private theorem p6667_1405_9105_220 : blockEstimate 6667 1405 9105 220 = 0x619f9378c := by decide +kernel
private theorem p6667_1405_9325_152 : blockEstimate 6667 1405 9325 152 = 0x767eb402 := by decide +kernel
private theorem p6667_1405_1405_440 : blockEstimate 6667 1405 1405 440 = 0x1517cc38ce :=
  block_append (B := 6667) (J := 1405) (start := 1405) (next := 1625)
    (a := 220) (b := 220) (n := 440) (x := 0x2b9422f7d) (y := 0x125e8a0951) (z := 0x1517cc38ce)
    p6667_1405_1405_220 p6667_1405_1625_220 rfl rfl rfl
private theorem p6667_1405_1845_440 : blockEstimate 6667 1405 1845 440 = 0x8a52527d9e :=
  block_append (B := 6667) (J := 1405) (start := 1845) (next := 2065)
    (a := 220) (b := 220) (n := 440) (x := 0x3015e41345) (y := 0x5a3c6e6a59) (z := 0x8a52527d9e)
    p6667_1405_1845_220 p6667_1405_2065_220 rfl rfl rfl
private theorem p6667_1405_1405_880 : blockEstimate 6667 1405 1405 880 = 0x9f6a1eb66c :=
  block_append (B := 6667) (J := 1405) (start := 1405) (next := 1845)
    (a := 440) (b := 440) (n := 880) (x := 0x1517cc38ce) (y := 0x8a52527d9e) (z := 0x9f6a1eb66c)
    p6667_1405_1405_440 p6667_1405_1845_440 rfl rfl rfl
private theorem p6667_1405_2285_440 : blockEstimate 6667 1405 2285 440 = 0x15c7ad39f6e :=
  block_append (B := 6667) (J := 1405) (start := 2285) (next := 2505)
    (a := 220) (b := 220) (n := 440) (x := 0x8f2f472b8d) (y := 0xcd4b8c73e1) (z := 0x15c7ad39f6e)
    p6667_1405_2285_220 p6667_1405_2505_220 rfl rfl rfl
private theorem p6667_1405_2945_440 : blockEstimate 6667 1405 2945 440 = 0x2e98af190fc :=
  block_append (B := 6667) (J := 1405) (start := 2945) (next := 3165)
    (a := 220) (b := 220) (n := 440) (x := 0x15646747a96) (y := 0x193447d1666) (z := 0x2e98af190fc)
    p6667_1405_2945_220 p6667_1405_3165_220 rfl rfl rfl
private theorem p6667_1405_2725_660 : blockEstimate 6667 1405 2725 660 = 0x3fbfb297a6b :=
  block_append (B := 6667) (J := 1405) (start := 2725) (next := 2945)
    (a := 220) (b := 440) (n := 660) (x := 0x1127037e96f) (y := 0x2e98af190fc) (z := 0x3fbfb297a6b)
    p6667_1405_2725_220 p6667_1405_2945_440 rfl rfl rfl
private theorem p6667_1405_2285_1100 : blockEstimate 6667 1405 2285 1100 = 0x55875fd19d9 :=
  block_append (B := 6667) (J := 1405) (start := 2285) (next := 2725)
    (a := 440) (b := 660) (n := 1100) (x := 0x15c7ad39f6e) (y := 0x3fbfb297a6b) (z := 0x55875fd19d9)
    p6667_1405_2285_440 p6667_1405_2725_660 rfl rfl rfl
private theorem p6667_1405_1405_1980 : blockEstimate 6667 1405 1405 1980 = 0x5f7e01bd045 :=
  block_append (B := 6667) (J := 1405) (start := 1405) (next := 2285)
    (a := 880) (b := 1100) (n := 1980) (x := 0x9f6a1eb66c) (y := 0x55875fd19d9) (z := 0x5f7e01bd045)
    p6667_1405_1405_880 p6667_1405_2285_1100 rfl rfl rfl
private theorem p6667_1405_3385_440 : blockEstimate 6667 1405 3385 440 = 0x3c1a04e9c3c :=
  block_append (B := 6667) (J := 1405) (start := 3385) (next := 3605)
    (a := 220) (b := 220) (n := 440) (x := 0x1c949d45936) (y := 0x1f8567a4306) (z := 0x3c1a04e9c3c)
    p6667_1405_3385_220 p6667_1405_3605_220 rfl rfl rfl
private theorem p6667_1405_3825_440 : blockEstimate 6667 1405 3825 440 = 0x461f020df7c :=
  block_append (B := 6667) (J := 1405) (start := 3825) (next := 4045)
    (a := 220) (b := 220) (n := 440) (x := 0x2206a6ed3d6) (y := 0x24185b20ba6) (z := 0x461f020df7c)
    p6667_1405_3825_220 p6667_1405_4045_220 rfl rfl rfl
private theorem p6667_1405_3385_880 : blockEstimate 6667 1405 3385 880 = 0x823906f7bb8 :=
  block_append (B := 6667) (J := 1405) (start := 3385) (next := 3825)
    (a := 440) (b := 440) (n := 880) (x := 0x3c1a04e9c3c) (y := 0x461f020df7c) (z := 0x823906f7bb8)
    p6667_1405_3385_440 p6667_1405_3825_440 rfl rfl rfl
private theorem p6667_1405_4265_440 : blockEstimate 6667 1405 4265 440 = 0x4ca7a685abc :=
  block_append (B := 6667) (J := 1405) (start := 4265) (next := 4485)
    (a := 220) (b := 220) (n := 440) (x := 0x25ba843ea76) (y := 0x26ed2247046) (z := 0x4ca7a685abc)
    p6667_1405_4265_220 p6667_1405_4485_220 rfl rfl rfl
private theorem p6667_1405_4925_440 : blockEstimate 6667 1405 4925 440 = 0x4feb76f5c9c :=
  block_append (B := 6667) (J := 1405) (start := 4925) (next := 5145)
    (a := 220) (b := 220) (n := 440) (x := 0x2803bd170e6) (y := 0x27e7b9debb6) (z := 0x4feb76f5c9c)
    p6667_1405_4925_220 p6667_1405_5145_220 rfl rfl rfl
private theorem p6667_1405_4705_660 : blockEstimate 6667 1405 4705 660 = 0x779bac2f9b2 :=
  block_append (B := 6667) (J := 1405) (start := 4705) (next := 4925)
    (a := 220) (b := 440) (n := 660) (x := 0x27b03539d16) (y := 0x4feb76f5c9c) (z := 0x779bac2f9b2)
    p6667_1405_4705_220 p6667_1405_4925_440 rfl rfl rfl
private theorem p6667_1405_4265_1100 : blockEstimate 6667 1405 4265 1100 = 0xc44352b546e :=
  block_append (B := 6667) (J := 1405) (start := 4265) (next := 4705)
    (a := 440) (b := 660) (n := 1100) (x := 0x4ca7a685abc) (y := 0x779bac2f9b2) (z := 0xc44352b546e)
    p6667_1405_4265_440 p6667_1405_4705_660 rfl rfl rfl
private theorem p6667_1405_3385_1980 : blockEstimate 6667 1405 3385 1980 = 0x1467c59ad026 :=
  block_append (B := 6667) (J := 1405) (start := 3385) (next := 4265)
    (a := 880) (b := 1100) (n := 1980) (x := 0x823906f7bb8) (y := 0xc44352b546e) (z := 0x1467c59ad026)
    p6667_1405_3385_880 p6667_1405_4265_1100 rfl rfl rfl
private theorem p6667_1405_1405_3960 : blockEstimate 6667 1405 1405 3960 = 0x1a5fa5b6a06b :=
  block_append (B := 6667) (J := 1405) (start := 1405) (next := 3385)
    (a := 1980) (b := 1980) (n := 3960) (x := 0x5f7e01bd045) (y := 0x1467c59ad026) (z := 0x1a5fa5b6a06b)
    p6667_1405_1405_1980 p6667_1405_3385_1980 rfl rfl rfl
private theorem p6667_1405_5365_440 : blockEstimate 6667 1405 5365 440 = 0x4dbd3dbe3dc :=
  block_append (B := 6667) (J := 1405) (start := 5365) (next := 5585)
    (a := 220) (b := 220) (n := 440) (x := 0x275c2b90d86) (y := 0x2661122d656) (z := 0x4dbd3dbe3dc)
    p6667_1405_5365_220 p6667_1405_5585_220 rfl rfl rfl
private theorem p6667_1405_5805_440 : blockEstimate 6667 1405 5805 440 = 0x4812abda31c :=
  block_append (B := 6667) (J := 1405) (start := 5805) (next := 6025)
    (a := 220) (b := 220) (n := 440) (x := 0x24f66db4626) (y := 0x231c3e25cf6) (z := 0x4812abda31c)
    p6667_1405_5805_220 p6667_1405_6025_220 rfl rfl rfl
private theorem p6667_1405_5365_880 : blockEstimate 6667 1405 5365 880 = 0x95cfe9986f8 :=
  block_append (B := 6667) (J := 1405) (start := 5365) (next := 5805)
    (a := 440) (b := 440) (n := 880) (x := 0x4dbd3dbe3dc) (y := 0x4812abda31c) (z := 0x95cfe9986f8)
    p6667_1405_5365_440 p6667_1405_5805_440 rfl rfl rfl
private theorem p6667_1405_6245_440 : blockEstimate 6667 1405 6245 440 = 0x3eebc33a8e3 :=
  block_append (B := 6667) (J := 1405) (start := 6245) (next := 6465)
    (a := 220) (b := 220) (n := 440) (x := 0x20d28381ac6) (y := 0x1e193fb8e1d) (z := 0x3eebc33a8e3)
    p6667_1405_6245_220 p6667_1405_6465_220 rfl rfl rfl
private theorem p6667_1405_6905_440 : blockEstimate 6667 1405 6905 440 = 0x2c5476a27d4 :=
  block_append (B := 6667) (J := 1405) (start := 6905) (next := 7125)
    (a := 220) (b := 220) (n := 440) (x := 0x17c9339beaa) (y := 0x148b430692a) (z := 0x2c5476a27d4)
    p6667_1405_6905_220 p6667_1405_7125_220 rfl rfl rfl
private theorem p6667_1405_6685_660 : blockEstimate 6667 1405 6685 660 = 0x47563d73192 :=
  block_append (B := 6667) (J := 1405) (start := 6685) (next := 6905)
    (a := 220) (b := 440) (n := 660) (x := 0x1b01c6d09be) (y := 0x2c5476a27d4) (z := 0x47563d73192)
    p6667_1405_6685_220 p6667_1405_6905_440 rfl rfl rfl
private theorem p6667_1405_6245_1100 : blockEstimate 6667 1405 6245 1100 = 0x864200ada75 :=
  block_append (B := 6667) (J := 1405) (start := 6245) (next := 6685)
    (a := 440) (b := 660) (n := 1100) (x := 0x3eebc33a8e3) (y := 0x47563d73192) (z := 0x864200ada75)
    p6667_1405_6245_440 p6667_1405_6685_660 rfl rfl rfl
private theorem p6667_1405_5365_1980 : blockEstimate 6667 1405 5365 1980 = 0x11c11ea4616d :=
  block_append (B := 6667) (J := 1405) (start := 5365) (next := 6245)
    (a := 880) (b := 1100) (n := 1980) (x := 0x95cfe9986f8) (y := 0x864200ada75) (z := 0x11c11ea4616d)
    p6667_1405_5365_880 p6667_1405_6245_1100 rfl rfl rfl
private theorem p6667_1405_7345_440 : blockEstimate 6667 1405 7345 440 = 0x1f9db9965b1 :=
  block_append (B := 6667) (J := 1405) (start := 7345) (next := 7565)
    (a := 220) (b := 220) (n := 440) (x := 0x115975423c2) (y := 0xe4444541ef) (z := 0x1f9db9965b1)
    p6667_1405_7345_220 p6667_1405_7565_220 rfl rfl rfl
private theorem p6667_1405_8005_440 : blockEstimate 6667 1405 8005 440 = 0xee92625d49 :=
  block_append (B := 6667) (J := 1405) (start := 8005) (next := 8225)
    (a := 220) (b := 220) (n := 440) (x := 0x8aa55ed071) (y := 0x63ed038cd8) (z := 0xee92625d49)
    p6667_1405_8005_220 p6667_1405_8225_220 rfl rfl rfl
private theorem p6667_1405_7785_660 : blockEstimate 6667 1405 7785 660 = 0x1a444a3ad8d :=
  block_append (B := 6667) (J := 1405) (start := 7785) (next := 8005)
    (a := 220) (b := 440) (n := 660) (x := 0xb5b2415044) (y := 0xee92625d49) (z := 0x1a444a3ad8d)
    p6667_1405_7785_220 p6667_1405_8005_440 rfl rfl rfl
private theorem p6667_1405_7345_1100 : blockEstimate 6667 1405 7345 1100 = 0x39e203d133e :=
  block_append (B := 6667) (J := 1405) (start := 7345) (next := 7785)
    (a := 440) (b := 660) (n := 1100) (x := 0x1f9db9965b1) (y := 0x1a444a3ad8d) (z := 0x39e203d133e)
    p6667_1405_7345_440 p6667_1405_7785_660 rfl rfl rfl
private theorem p6667_1405_8445_440 : blockEstimate 6667 1405 8445 440 = 0x6a87dc734a :=
  block_append (B := 6667) (J := 1405) (start := 8445) (next := 8665)
    (a := 220) (b := 220) (n := 440) (x := 0x42c76abfe4) (y := 0x27c071b366) (z := 0x6a87dc734a)
    p6667_1405_8445_220 p6667_1405_8665_220 rfl rfl rfl
private theorem p6667_1405_9105_372 : blockEstimate 6667 1405 9105 372 = 0x69077eb8e :=
  block_append (B := 6667) (J := 1405) (start := 9105) (next := 9325)
    (a := 220) (b := 152) (n := 372) (x := 0x619f9378c) (y := 0x767eb402) (z := 0x69077eb8e)
    p6667_1405_9105_220 p6667_1405_9325_152 rfl rfl rfl
private theorem p6667_1405_8885_592 : blockEstimate 6667 1405 8885 592 = 0x19eb76e9dc :=
  block_append (B := 6667) (J := 1405) (start := 8885) (next := 9105)
    (a := 220) (b := 372) (n := 592) (x := 0x135afefe4e) (y := 0x69077eb8e) (z := 0x19eb76e9dc)
    p6667_1405_8885_220 p6667_1405_9105_372 rfl rfl rfl
private theorem p6667_1405_8445_1032 : blockEstimate 6667 1405 8445 1032 = 0x8473535d26 :=
  block_append (B := 6667) (J := 1405) (start := 8445) (next := 8885)
    (a := 440) (b := 592) (n := 1032) (x := 0x6a87dc734a) (y := 0x19eb76e9dc) (z := 0x8473535d26)
    p6667_1405_8445_440 p6667_1405_8885_592 rfl rfl rfl
private theorem p6667_1405_7345_2132 : blockEstimate 6667 1405 7345 2132 = 0x42293907064 :=
  block_append (B := 6667) (J := 1405) (start := 7345) (next := 8445)
    (a := 1100) (b := 1032) (n := 2132) (x := 0x39e203d133e) (y := 0x8473535d26) (z := 0x42293907064)
    p6667_1405_7345_1100 p6667_1405_8445_1032 rfl rfl rfl
private theorem p6667_1405_5365_4112 : blockEstimate 6667 1405 5365 4112 = 0x15e3b234d1d1 :=
  block_append (B := 6667) (J := 1405) (start := 5365) (next := 7345)
    (a := 1980) (b := 2132) (n := 4112) (x := 0x11c11ea4616d) (y := 0x42293907064) (z := 0x15e3b234d1d1)
    p6667_1405_5365_1980 p6667_1405_7345_2132 rfl rfl rfl
private theorem p6667_1405_1405_8072 : blockEstimate 6667 1405 1405 8072 = 0x304357eb723c :=
  block_append (B := 6667) (J := 1405) (start := 1405) (next := 5365)
    (a := 3960) (b := 4112) (n := 8072) (x := 0x1a5fa5b6a06b) (y := 0x15e3b234d1d1) (z := 0x304357eb723c)
    p6667_1405_1405_3960 p6667_1405_5365_4112 rfl rfl rfl

theorem moment6667_1405 : momentEstimate 6667 1405 = 0x304357eb723c := p6667_1405_1405_8072
end HighCore82258BankProof
