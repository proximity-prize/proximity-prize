import ProximityPrize.SubmissionLower.HighCore82229MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82229BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

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
  append_checked p6667_1405_1405_220 p6667_1405_1625_220
private theorem p6667_1405_1845_440 : blockEstimate 6667 1405 1845 440 = 0x8a52527d9e :=
  append_checked p6667_1405_1845_220 p6667_1405_2065_220
private theorem p6667_1405_1405_880 : blockEstimate 6667 1405 1405 880 = 0x9f6a1eb66c :=
  append_checked p6667_1405_1405_440 p6667_1405_1845_440
private theorem p6667_1405_2285_440 : blockEstimate 6667 1405 2285 440 = 0x15c7ad39f6e :=
  append_checked p6667_1405_2285_220 p6667_1405_2505_220
private theorem p6667_1405_2945_440 : blockEstimate 6667 1405 2945 440 = 0x2e98af190fc :=
  append_checked p6667_1405_2945_220 p6667_1405_3165_220
private theorem p6667_1405_2725_660 : blockEstimate 6667 1405 2725 660 = 0x3fbfb297a6b :=
  append_checked p6667_1405_2725_220 p6667_1405_2945_440
private theorem p6667_1405_2285_1100 : blockEstimate 6667 1405 2285 1100 = 0x55875fd19d9 :=
  append_checked p6667_1405_2285_440 p6667_1405_2725_660
private theorem p6667_1405_1405_1980 : blockEstimate 6667 1405 1405 1980 = 0x5f7e01bd045 :=
  append_checked p6667_1405_1405_880 p6667_1405_2285_1100
private theorem p6667_1405_3385_440 : blockEstimate 6667 1405 3385 440 = 0x3c1a04e9c3c :=
  append_checked p6667_1405_3385_220 p6667_1405_3605_220
private theorem p6667_1405_3825_440 : blockEstimate 6667 1405 3825 440 = 0x461f020df7c :=
  append_checked p6667_1405_3825_220 p6667_1405_4045_220
private theorem p6667_1405_3385_880 : blockEstimate 6667 1405 3385 880 = 0x823906f7bb8 :=
  append_checked p6667_1405_3385_440 p6667_1405_3825_440
private theorem p6667_1405_4265_440 : blockEstimate 6667 1405 4265 440 = 0x4ca7a685abc :=
  append_checked p6667_1405_4265_220 p6667_1405_4485_220
private theorem p6667_1405_4925_440 : blockEstimate 6667 1405 4925 440 = 0x4feb76f5c9c :=
  append_checked p6667_1405_4925_220 p6667_1405_5145_220
private theorem p6667_1405_4705_660 : blockEstimate 6667 1405 4705 660 = 0x779bac2f9b2 :=
  append_checked p6667_1405_4705_220 p6667_1405_4925_440
private theorem p6667_1405_4265_1100 : blockEstimate 6667 1405 4265 1100 = 0xc44352b546e :=
  append_checked p6667_1405_4265_440 p6667_1405_4705_660
private theorem p6667_1405_3385_1980 : blockEstimate 6667 1405 3385 1980 = 0x1467c59ad026 :=
  append_checked p6667_1405_3385_880 p6667_1405_4265_1100
private theorem p6667_1405_1405_3960 : blockEstimate 6667 1405 1405 3960 = 0x1a5fa5b6a06b :=
  append_checked p6667_1405_1405_1980 p6667_1405_3385_1980
private theorem p6667_1405_5365_440 : blockEstimate 6667 1405 5365 440 = 0x4dbd3dbe3dc :=
  append_checked p6667_1405_5365_220 p6667_1405_5585_220
private theorem p6667_1405_5805_440 : blockEstimate 6667 1405 5805 440 = 0x4812abda31c :=
  append_checked p6667_1405_5805_220 p6667_1405_6025_220
private theorem p6667_1405_5365_880 : blockEstimate 6667 1405 5365 880 = 0x95cfe9986f8 :=
  append_checked p6667_1405_5365_440 p6667_1405_5805_440
private theorem p6667_1405_6245_440 : blockEstimate 6667 1405 6245 440 = 0x3eebc33a8e3 :=
  append_checked p6667_1405_6245_220 p6667_1405_6465_220
private theorem p6667_1405_6905_440 : blockEstimate 6667 1405 6905 440 = 0x2c5476a27d4 :=
  append_checked p6667_1405_6905_220 p6667_1405_7125_220
private theorem p6667_1405_6685_660 : blockEstimate 6667 1405 6685 660 = 0x47563d73192 :=
  append_checked p6667_1405_6685_220 p6667_1405_6905_440
private theorem p6667_1405_6245_1100 : blockEstimate 6667 1405 6245 1100 = 0x864200ada75 :=
  append_checked p6667_1405_6245_440 p6667_1405_6685_660
private theorem p6667_1405_5365_1980 : blockEstimate 6667 1405 5365 1980 = 0x11c11ea4616d :=
  append_checked p6667_1405_5365_880 p6667_1405_6245_1100
private theorem p6667_1405_7345_440 : blockEstimate 6667 1405 7345 440 = 0x1f9db9965b1 :=
  append_checked p6667_1405_7345_220 p6667_1405_7565_220
private theorem p6667_1405_8005_440 : blockEstimate 6667 1405 8005 440 = 0xee92625d49 :=
  append_checked p6667_1405_8005_220 p6667_1405_8225_220
private theorem p6667_1405_7785_660 : blockEstimate 6667 1405 7785 660 = 0x1a444a3ad8d :=
  append_checked p6667_1405_7785_220 p6667_1405_8005_440
private theorem p6667_1405_7345_1100 : blockEstimate 6667 1405 7345 1100 = 0x39e203d133e :=
  append_checked p6667_1405_7345_440 p6667_1405_7785_660
private theorem p6667_1405_8445_440 : blockEstimate 6667 1405 8445 440 = 0x6a87dc734a :=
  append_checked p6667_1405_8445_220 p6667_1405_8665_220
private theorem p6667_1405_9105_372 : blockEstimate 6667 1405 9105 372 = 0x69077eb8e :=
  append_checked p6667_1405_9105_220 p6667_1405_9325_152
private theorem p6667_1405_8885_592 : blockEstimate 6667 1405 8885 592 = 0x19eb76e9dc :=
  append_checked p6667_1405_8885_220 p6667_1405_9105_372
private theorem p6667_1405_8445_1032 : blockEstimate 6667 1405 8445 1032 = 0x8473535d26 :=
  append_checked p6667_1405_8445_440 p6667_1405_8885_592
private theorem p6667_1405_7345_2132 : blockEstimate 6667 1405 7345 2132 = 0x42293907064 :=
  append_checked p6667_1405_7345_1100 p6667_1405_8445_1032
private theorem p6667_1405_5365_4112 : blockEstimate 6667 1405 5365 4112 = 0x15e3b234d1d1 :=
  append_checked p6667_1405_5365_1980 p6667_1405_7345_2132
private theorem p6667_1405_1405_8072 : blockEstimate 6667 1405 1405 8072 = 0x304357eb723c :=
  append_checked p6667_1405_1405_3960 p6667_1405_5365_4112

theorem moment6667_1405 : momentEstimate 6667 1405 = 0x304357eb723c := p6667_1405_1405_8072
end HighCore82229BankProof
