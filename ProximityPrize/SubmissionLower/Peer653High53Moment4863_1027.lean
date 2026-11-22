-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moment4863_1027.lean.
import ProximityPrize.SubmissionLower.Peer653High53MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

private theorem p4863_1027_1027_220 : blockEstimate 4863 1027 1027 220 = 0x1f7d3062d := by decide +kernel
private theorem p4863_1027_1247_220 : blockEstimate 4863 1027 1247 220 = 0xd1ef49e41 := by decide +kernel
private theorem p4863_1027_1467_220 : blockEstimate 4863 1027 1467 220 = 0x21df367175 := by decide +kernel
private theorem p4863_1027_1687_220 : blockEstimate 4863 1027 1687 220 = 0x3e95b69cc9 := by decide +kernel
private theorem p4863_1027_1907_220 : blockEstimate 4863 1027 1907 220 = 0x6190f6933b := by decide +kernel
private theorem p4863_1027_2127_220 : blockEstimate 4863 1027 2127 220 = 0x85e0c8c95c := by decide +kernel
private theorem p4863_1027_2347_220 : blockEstimate 4863 1027 2347 220 = 0xa59442cf7c := by decide +kernel
private theorem p4863_1027_2567_220 : blockEstimate 4863 1027 2567 220 = 0xc02edb079c := by decide +kernel
private theorem p4863_1027_2787_220 : blockEstimate 4863 1027 2787 220 = 0xd5b09171bc := by decide +kernel
private theorem p4863_1027_3007_220 : blockEstimate 4863 1027 3007 220 = 0xe619660ddc := by decide +kernel
private theorem p4863_1027_3227_220 : blockEstimate 4863 1027 3227 220 = 0xf16958dbfc := by decide +kernel
private theorem p4863_1027_3447_220 : blockEstimate 4863 1027 3447 220 = 0xf7a069dc1c := by decide +kernel
private theorem p4863_1027_3667_220 : blockEstimate 4863 1027 3667 220 = 0xf8be990e3c := by decide +kernel
private theorem p4863_1027_3887_220 : blockEstimate 4863 1027 3887 220 = 0xf4c3e6725c := by decide +kernel
private theorem p4863_1027_4107_220 : blockEstimate 4863 1027 4107 220 = 0xebb052087c := by decide +kernel
private theorem p4863_1027_4327_220 : blockEstimate 4863 1027 4327 220 = 0xdd83dbd09c := by decide +kernel
private theorem p4863_1027_4547_220 : blockEstimate 4863 1027 4547 220 = 0xca3e83cabc := by decide +kernel
private theorem p4863_1027_4767_220 : blockEstimate 4863 1027 4767 220 = 0xb1fc898b7c := by decide +kernel
private theorem p4863_1027_4987_220 : blockEstimate 4863 1027 4987 220 = 0x96d437f8b7 := by decide +kernel
private theorem p4863_1027_5207_220 : blockEstimate 4863 1027 5207 220 = 0x7b41e8c38f := by decide +kernel
private theorem p4863_1027_5427_220 : blockEstimate 4863 1027 5427 220 = 0x60685b5f7d := by decide +kernel
private theorem p4863_1027_5647_220 : blockEstimate 4863 1027 5647 220 = 0x47483808a9 := by decide +kernel
private theorem p4863_1027_5867_220 : blockEstimate 4863 1027 5867 220 = 0x30b1f8c7a7 := by decide +kernel
private theorem p4863_1027_6087_220 : blockEstimate 4863 1027 6087 220 = 0x1d9a1cabd0 := by decide +kernel
private theorem p4863_1027_6307_220 : blockEstimate 4863 1027 6307 220 = 0xedc127a15 := by decide +kernel
private theorem p4863_1027_6527_220 : blockEstimate 4863 1027 6527 220 = 0x4fb4675a8 := by decide +kernel
private theorem p4863_1027_6747_170 : blockEstimate 4863 1027 6747 170 = 0x77dac75b := by decide +kernel
private theorem p4863_1027_1247_440 : blockEstimate 4863 1027 1247 440 = 0x2efe2b0fb6 :=
  append_checked p4863_1027_1247_220 p4863_1027_1467_220
private theorem p4863_1027_1027_660 : blockEstimate 4863 1027 1027 660 = 0x30f5fe15e3 :=
  append_checked p4863_1027_1027_220 p4863_1027_1247_440
private theorem p4863_1027_1907_440 : blockEstimate 4863 1027 1907 440 = 0xe771bf5c97 :=
  append_checked p4863_1027_1907_220 p4863_1027_2127_220
private theorem p4863_1027_1687_660 : blockEstimate 4863 1027 1687 660 = 0x1260775f960 :=
  append_checked p4863_1027_1687_220 p4863_1027_1907_440
private theorem p4863_1027_1027_1320 : blockEstimate 4863 1027 1027 1320 = 0x156fd740f43 :=
  append_checked p4863_1027_1027_660 p4863_1027_1687_660
private theorem p4863_1027_2567_440 : blockEstimate 4863 1027 2567 440 = 0x195df6c7958 :=
  append_checked p4863_1027_2567_220 p4863_1027_2787_220
private theorem p4863_1027_2347_660 : blockEstimate 4863 1027 2347 660 = 0x23b73af48d4 :=
  append_checked p4863_1027_2347_220 p4863_1027_2567_440
private theorem p4863_1027_3007_440 : blockEstimate 4863 1027 3007 440 = 0x1d782bee9d8 :=
  append_checked p4863_1027_3007_220 p4863_1027_3227_220
private theorem p4863_1027_3447_440 : blockEstimate 4863 1027 3447 440 = 0x1f05f02ea58 :=
  append_checked p4863_1027_3447_220 p4863_1027_3667_220
private theorem p4863_1027_3007_880 : blockEstimate 4863 1027 3007 880 = 0x3c7e1c1d430 :=
  append_checked p4863_1027_3007_440 p4863_1027_3447_440
private theorem p4863_1027_2347_1540 : blockEstimate 4863 1027 2347 1540 = 0x60355711d04 :=
  append_checked p4863_1027_2347_660 p4863_1027_3007_880
private theorem p4863_1027_1027_2860 : blockEstimate 4863 1027 1027 2860 = 0x75a52e52c47 :=
  append_checked p4863_1027_1027_1320 p4863_1027_2347_1540
private theorem p4863_1027_4107_440 : blockEstimate 4863 1027 4107 440 = 0x1c9342dd918 :=
  append_checked p4863_1027_4107_220 p4863_1027_4327_220
private theorem p4863_1027_3887_660 : blockEstimate 4863 1027 3887 660 = 0x2bdf8144b74 :=
  append_checked p4863_1027_3887_220 p4863_1027_4107_440
private theorem p4863_1027_4547_440 : blockEstimate 4863 1027 4547 440 = 0x17c3b0d5638 :=
  append_checked p4863_1027_4547_220 p4863_1027_4767_220
private theorem p4863_1027_4987_440 : blockEstimate 4863 1027 4987 440 = 0x1121620bc46 :=
  append_checked p4863_1027_4987_220 p4863_1027_5207_220
private theorem p4863_1027_4547_880 : blockEstimate 4863 1027 4547 880 = 0x28e512e127e :=
  append_checked p4863_1027_4547_440 p4863_1027_4987_440
private theorem p4863_1027_3887_1540 : blockEstimate 4863 1027 3887 1540 = 0x54c49425df2 :=
  append_checked p4863_1027_3887_660 p4863_1027_4547_880
private theorem p4863_1027_5647_440 : blockEstimate 4863 1027 5647 440 = 0x77fa30d050 :=
  append_checked p4863_1027_5647_220 p4863_1027_5867_220
private theorem p4863_1027_5427_660 : blockEstimate 4863 1027 5427 660 = 0xd8628c2fcd :=
  append_checked p4863_1027_5427_220 p4863_1027_5647_440
private theorem p4863_1027_6087_440 : blockEstimate 4863 1027 6087 440 = 0x2c762f25e5 :=
  append_checked p4863_1027_6087_220 p4863_1027_6307_220
private theorem p4863_1027_6527_390 : blockEstimate 4863 1027 6527 390 = 0x573213d03 :=
  append_checked p4863_1027_6527_220 p4863_1027_6747_170
private theorem p4863_1027_6087_830 : blockEstimate 4863 1027 6087 830 = 0x31e95062e8 :=
  append_checked p4863_1027_6087_440 p4863_1027_6527_390
private theorem p4863_1027_5427_1490 : blockEstimate 4863 1027 5427 1490 = 0x10a4bdc92b5 :=
  append_checked p4863_1027_5427_660 p4863_1027_6087_830
private theorem p4863_1027_3887_3030 : blockEstimate 4863 1027 3887 3030 = 0x656951ef0a7 :=
  append_checked p4863_1027_3887_1540 p4863_1027_5427_1490
private theorem p4863_1027_1027_5890 : blockEstimate 4863 1027 1027 5890 = 0xdb0e8041cee :=
  append_checked p4863_1027_1027_2860 p4863_1027_3887_3030

theorem moment4863_1027 : momentEstimate 4863 1027 = 0xdb0e8041cee := p4863_1027_1027_5890
end Peer653High53BankProof
