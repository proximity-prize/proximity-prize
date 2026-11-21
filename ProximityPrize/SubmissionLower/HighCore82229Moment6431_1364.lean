import ProximityPrize.SubmissionLower.HighCore82229MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82229BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

private theorem p6431_1364_1364_220 : blockEstimate 6431 1364 1364 220 = 0x29ff411ad := by decide +kernel
private theorem p6431_1364_1584_220 : blockEstimate 6431 1364 1584 220 = 0x11aec563c1 := by decide +kernel
private theorem p6431_1364_1804_220 : blockEstimate 6431 1364 1804 220 = 0x2e39e0a8f5 := by decide +kernel
private theorem p6431_1364_2024_220 : blockEstimate 6431 1364 2024 220 = 0x569e63fe49 := by decide +kernel
private theorem p6431_1364_2244_220 : blockEstimate 6431 1364 2244 220 = 0x89396d80bd := by decide +kernel
private theorem p6431_1364_2464_220 : blockEstimate 6431 1364 2464 220 = 0xc4681b4d51 := by decide +kernel
private theorem p6431_1364_2684_220 : blockEstimate 6431 1364 2684 220 = 0x1057c410fe1 := by decide +kernel
private theorem p6431_1364_2904_220 : blockEstimate 6431 1364 2904 220 = 0x14381403312 := by decide +kernel
private theorem p6431_1364_3124_220 : blockEstimate 6431 1364 3124 220 = 0x17ac5e95be2 := by decide +kernel
private theorem p6431_1364_3344_220 : blockEstimate 6431 1364 3344 220 = 0x1ab45ec2b32 := by decide +kernel
private theorem p6431_1364_3564_220 : blockEstimate 6431 1364 3564 220 = 0x1d50148a102 := by decide +kernel
private theorem p6431_1364_3784_220 : blockEstimate 6431 1364 3784 220 = 0x1f7f7febd52 := by decide +kernel
private theorem p6431_1364_4004_220 : blockEstimate 6431 1364 4004 220 = 0x2142a0e8022 := by decide +kernel
private theorem p6431_1364_4224_220 : blockEstimate 6431 1364 4224 220 = 0x2299777e972 := by decide +kernel
private theorem p6431_1364_4444_220 : blockEstimate 6431 1364 4444 220 = 0x238403af942 := by decide +kernel
private theorem p6431_1364_4664_220 : blockEstimate 6431 1364 4664 220 = 0x2402457af92 := by decide +kernel
private theorem p6431_1364_4884_220 : blockEstimate 6431 1364 4884 220 = 0x24143ce0c62 := by decide +kernel
private theorem p6431_1364_5104_220 : blockEstimate 6431 1364 5104 220 = 0x23b9e9e0fb2 := by decide +kernel
private theorem p6431_1364_5324_220 : blockEstimate 6431 1364 5324 220 = 0x22f34c7b982 := by decide +kernel
private theorem p6431_1364_5544_220 : blockEstimate 6431 1364 5544 220 = 0x21c064b09d2 := by decide +kernel
private theorem p6431_1364_5764_220 : blockEstimate 6431 1364 5764 220 = 0x202132800a2 := by decide +kernel
private theorem p6431_1364_5984_220 : blockEstimate 6431 1364 5984 220 = 0x1e15b5e9df2 := by decide +kernel
private theorem p6431_1364_6204_220 : blockEstimate 6431 1364 6204 220 = 0x1b9deeee1c2 := by decide +kernel
private theorem p6431_1364_6424_220 : blockEstimate 6431 1364 6424 220 = 0x18c5c4cedcf := by decide +kernel
private theorem p6431_1364_6644_220 : blockEstimate 6431 1364 6644 220 = 0x15c74f7c978 := by decide +kernel
private theorem p6431_1364_6864_220 : blockEstimate 6431 1364 6864 220 = 0x12c1984950e := by decide +kernel
private theorem p6431_1364_7084_220 : blockEstimate 6431 1364 7084 220 = 0xfc62dc0750 := by decide +kernel
private theorem p6431_1364_7304_220 : blockEstimate 6431 1364 7304 220 = 0xce5904ddb9 := by decide +kernel
private theorem p6431_1364_7524_220 : blockEstimate 6431 1364 7524 220 = 0xa2f3250af4 := by decide +kernel
private theorem p6431_1364_7744_220 : blockEstimate 6431 1364 7744 220 = 0x7af0cbce60 := by decide +kernel
private theorem p6431_1364_7964_220 : blockEstimate 6431 1364 7964 220 = 0x5732f9afbd := by decide +kernel
private theorem p6431_1364_8184_220 : blockEstimate 6431 1364 8184 220 = 0x38e32074f9 := by decide +kernel
private theorem p6431_1364_8404_220 : blockEstimate 6431 1364 8404 220 = 0x2088ed262f := by decide +kernel
private theorem p6431_1364_8624_220 : blockEstimate 6431 1364 8624 220 = 0xea7465a4f := by decide +kernel
private theorem p6431_1364_8844_220 : blockEstimate 6431 1364 8844 220 = 0x3c112a849 := by decide +kernel
private theorem p6431_1364_9064_95 : blockEstimate 6431 1364 9064 95 = 0x1c810500 := by decide +kernel
private theorem p6431_1364_1364_440 : blockEstimate 6431 1364 1364 440 = 0x144eb9756e :=
  append_checked p6431_1364_1364_220 p6431_1364_1584_220
private theorem p6431_1364_1804_440 : blockEstimate 6431 1364 1804 440 = 0x84d844a73e :=
  append_checked p6431_1364_1804_220 p6431_1364_2024_220
private theorem p6431_1364_1364_880 : blockEstimate 6431 1364 1364 880 = 0x9926fe1cac :=
  append_checked p6431_1364_1364_440 p6431_1364_1804_440
private theorem p6431_1364_2244_440 : blockEstimate 6431 1364 2244 440 = 0x14da188ce0e :=
  append_checked p6431_1364_2244_220 p6431_1364_2464_220
private theorem p6431_1364_2904_440 : blockEstimate 6431 1364 2904 440 = 0x2be47298ef4 :=
  append_checked p6431_1364_2904_220 p6431_1364_3124_220
private theorem p6431_1364_2684_660 : blockEstimate 6431 1364 2684 660 = 0x3c3c36a9ed5 :=
  append_checked p6431_1364_2684_220 p6431_1364_2904_440
private theorem p6431_1364_2244_1100 : blockEstimate 6431 1364 2244 1100 = 0x51164f36ce3 :=
  append_checked p6431_1364_2244_440 p6431_1364_2684_660
private theorem p6431_1364_1364_1980 : blockEstimate 6431 1364 1364 1980 = 0x5aa8bf1898f :=
  append_checked p6431_1364_1364_880 p6431_1364_2244_1100
private theorem p6431_1364_3344_440 : blockEstimate 6431 1364 3344 440 = 0x3804734cc34 :=
  append_checked p6431_1364_3344_220 p6431_1364_3564_220
private theorem p6431_1364_3784_440 : blockEstimate 6431 1364 3784 440 = 0x40c220d3d74 :=
  append_checked p6431_1364_3784_220 p6431_1364_4004_220
private theorem p6431_1364_3344_880 : blockEstimate 6431 1364 3344 880 = 0x78c694209a8 :=
  append_checked p6431_1364_3344_440 p6431_1364_3784_440
private theorem p6431_1364_4224_440 : blockEstimate 6431 1364 4224 440 = 0x461d7b2e2b4 :=
  append_checked p6431_1364_4224_220 p6431_1364_4444_220
private theorem p6431_1364_4884_440 : blockEstimate 6431 1364 4884 440 = 0x47ce26c1c14 :=
  append_checked p6431_1364_4884_220 p6431_1364_5104_220
private theorem p6431_1364_4664_660 : blockEstimate 6431 1364 4664 660 = 0x6bd06c3cba6 :=
  append_checked p6431_1364_4664_220 p6431_1364_4884_440
private theorem p6431_1364_4224_1100 : blockEstimate 6431 1364 4224 1100 = 0xb1ede76ae5a :=
  append_checked p6431_1364_4224_440 p6431_1364_4664_660
private theorem p6431_1364_3344_1980 : blockEstimate 6431 1364 3344 1980 = 0x12ab47b8b802 :=
  append_checked p6431_1364_3344_880 p6431_1364_4224_1100
private theorem p6431_1364_1364_3960 : blockEstimate 6431 1364 1364 3960 = 0x1855d3aa4191 :=
  append_checked p6431_1364_1364_1980 p6431_1364_3344_1980
private theorem p6431_1364_5324_440 : blockEstimate 6431 1364 5324 440 = 0x44b3b12c354 :=
  append_checked p6431_1364_5324_220 p6431_1364_5544_220
private theorem p6431_1364_5764_440 : blockEstimate 6431 1364 5764 440 = 0x3e36e869e94 :=
  append_checked p6431_1364_5764_220 p6431_1364_5984_220
private theorem p6431_1364_5324_880 : blockEstimate 6431 1364 5324 880 = 0x82ea99961e8 :=
  append_checked p6431_1364_5324_440 p6431_1364_5764_440
private theorem p6431_1364_6204_440 : blockEstimate 6431 1364 6204 440 = 0x3463b3bcf91 :=
  append_checked p6431_1364_6204_220 p6431_1364_6424_220
private theorem p6431_1364_6864_440 : blockEstimate 6431 1364 6864 440 = 0x2287c609c5e :=
  append_checked p6431_1364_6864_220 p6431_1364_7084_220
private theorem p6431_1364_6644_660 : blockEstimate 6431 1364 6644 660 = 0x384f15865d6 :=
  append_checked p6431_1364_6644_220 p6431_1364_6864_440
private theorem p6431_1364_6204_1100 : blockEstimate 6431 1364 6204 1100 = 0x6cb2c943567 :=
  append_checked p6431_1364_6204_440 p6431_1364_6644_660
private theorem p6431_1364_5324_1980 : blockEstimate 6431 1364 5324 1980 = 0xef9d62d974f :=
  append_checked p6431_1364_5324_880 p6431_1364_6204_1100
private theorem p6431_1364_7304_440 : blockEstimate 6431 1364 7304 440 = 0x1714c29e8ad :=
  append_checked p6431_1364_7304_220 p6431_1364_7524_220
private theorem p6431_1364_7744_440 : blockEstimate 6431 1364 7744 440 = 0xd223c57e1d :=
  append_checked p6431_1364_7744_220 p6431_1364_7964_220
private theorem p6431_1364_7304_880 : blockEstimate 6431 1364 7304 880 = 0x2436fef66ca :=
  append_checked p6431_1364_7304_440 p6431_1364_7744_440
private theorem p6431_1364_8184_440 : blockEstimate 6431 1364 8184 440 = 0x596c0d9b28 :=
  append_checked p6431_1364_8184_220 p6431_1364_8404_220
private theorem p6431_1364_8844_315 : blockEstimate 6431 1364 8844 315 = 0x3dd93ad49 :=
  append_checked p6431_1364_8844_220 p6431_1364_9064_95
private theorem p6431_1364_8624_535 : blockEstimate 6431 1364 8624 535 = 0x1284da0798 :=
  append_checked p6431_1364_8624_220 p6431_1364_8844_315
private theorem p6431_1364_8184_975 : blockEstimate 6431 1364 8184 975 = 0x6bf0e7a2c0 :=
  append_checked p6431_1364_8184_440 p6431_1364_8624_535
private theorem p6431_1364_7304_1855 : blockEstimate 6431 1364 7304 1855 = 0x2af60d7098a :=
  append_checked p6431_1364_7304_880 p6431_1364_8184_975
private theorem p6431_1364_5324_3835 : blockEstimate 6431 1364 5324 3835 = 0x11a93704a0d9 :=
  append_checked p6431_1364_5324_1980 p6431_1364_7304_1855
private theorem p6431_1364_1364_7795 : blockEstimate 6431 1364 1364 7795 = 0x29ff0aaee26a :=
  append_checked p6431_1364_1364_3960 p6431_1364_5324_3835

theorem moment6431_1364 : momentEstimate 6431 1364 = 0x29ff0aaee26a := p6431_1364_1364_7795
end HighCore82229BankProof
