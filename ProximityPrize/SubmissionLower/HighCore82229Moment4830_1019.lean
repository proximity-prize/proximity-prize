import ProximityPrize.SubmissionLower.HighCore82229MomentAppend
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82229BankProof
open P1_7_1_3 (momentEstimate blockEstimate)

private theorem p4830_1019_1019_220 : blockEstimate 4830 1019 1019 220 = 0x1f4492f91 := by decide +kernel
private theorem p4830_1019_1239_220 : blockEstimate 4830 1019 1239 220 = 0xd0660b6d5 := by decide +kernel
private theorem p4830_1019_1459_220 : blockEstimate 4830 1019 1459 220 = 0x219ca6c779 := by decide +kernel
private theorem p4830_1019_1679_220 : blockEstimate 4830 1019 1679 220 = 0x3e14397e7d := by decide +kernel
private theorem p4830_1019_1899_220 : blockEstimate 4830 1019 1899 220 = 0x60b66a83cd := by decide +kernel
private theorem p4830_1019_2119_220 : blockEstimate 4830 1019 2119 220 = 0x84642042b4 := by decide +kernel
private theorem p4830_1019_2339_220 : blockEstimate 4830 1019 2339 220 = 0xa36b9289d4 := by decide +kernel
private theorem p4830_1019_2559_220 : blockEstimate 4830 1019 2559 220 = 0xbd644a9ef4 := by decide +kernel
private theorem p4830_1019_2779_220 : blockEstimate 4830 1019 2779 220 = 0xd24e488214 := by decide +kernel
private theorem p4830_1019_2999_220 : blockEstimate 4830 1019 2999 220 = 0xe2298c3334 := by decide +kernel
private theorem p4830_1019_3219_220 : blockEstimate 4830 1019 3219 220 = 0xecf615b254 := by decide +kernel
private theorem p4830_1019_3439_220 : blockEstimate 4830 1019 3439 220 = 0xf2b3e4ff74 := by decide +kernel
private theorem p4830_1019_3659_220 : blockEstimate 4830 1019 3659 220 = 0xf362fa1a94 := by decide +kernel
private theorem p4830_1019_3879_220 : blockEstimate 4830 1019 3879 220 = 0xef035503b4 := by decide +kernel
private theorem p4830_1019_4099_220 : blockEstimate 4830 1019 4099 220 = 0xe594f5bad4 := by decide +kernel
private theorem p4830_1019_4319_220 : blockEstimate 4830 1019 4319 220 = 0xd717dc3ff4 := by decide +kernel
private theorem p4830_1019_4539_220 : blockEstimate 4830 1019 4539 220 = 0xc38c089314 := by decide +kernel
private theorem p4830_1019_4759_220 : blockEstimate 4830 1019 4759 220 = 0xab229192de := by decide +kernel
private theorem p4830_1019_4979_220 : blockEstimate 4830 1019 4979 220 = 0x90383af3ad := by decide +kernel
private theorem p4830_1019_5199_220 : blockEstimate 4830 1019 5199 220 = 0x751051e109 := by decide +kernel
private theorem p4830_1019_5419_220 : blockEstimate 4830 1019 5419 220 = 0x5ac3c80314 := by decide +kernel
private theorem p4830_1019_5639_220 : blockEstimate 4830 1019 5639 220 = 0x4250263828 := by decide +kernel
private theorem p4830_1019_5859_220 : blockEstimate 4830 1019 5859 220 = 0x2c7cd49dd5 := by decide +kernel
private theorem p4830_1019_6079_220 : blockEstimate 4830 1019 6079 220 = 0x1a4fd336be := by decide +kernel
private theorem p4830_1019_6299_220 : blockEstimate 4830 1019 6299 220 = 0xc8b15b4e9 := by decide +kernel
private theorem p4830_1019_6519_220 : blockEstimate 4830 1019 6519 220 = 0x3b182af46 := by decide +kernel
private theorem p4830_1019_6739_129 : blockEstimate 4830 1019 6739 129 = 0x34a7248e := by decide +kernel
private theorem p4830_1019_1239_440 : blockEstimate 4830 1019 1239 440 = 0x2ea3077e4e :=
  append_checked p4830_1019_1239_220 p4830_1019_1459_220
private theorem p4830_1019_1019_660 : blockEstimate 4830 1019 1019 660 = 0x309750addf :=
  append_checked p4830_1019_1019_220 p4830_1019_1239_440
private theorem p4830_1019_1899_440 : blockEstimate 4830 1019 1899 440 = 0xe51a8ac681 :=
  append_checked p4830_1019_1899_220 p4830_1019_2119_220
private theorem p4830_1019_1679_660 : blockEstimate 4830 1019 1679 660 = 0x1232ec444fe :=
  append_checked p4830_1019_1679_220 p4830_1019_1899_440
private theorem p4830_1019_1019_1320 : blockEstimate 4830 1019 1019 1320 = 0x153c614f2dd :=
  append_checked p4830_1019_1019_660 p4830_1019_1679_660
private theorem p4830_1019_2559_440 : blockEstimate 4830 1019 2559 440 = 0x18fb2932108 :=
  append_checked p4830_1019_2559_220 p4830_1019_2779_220
private theorem p4830_1019_2339_660 : blockEstimate 4830 1019 2339 660 = 0x2331e25aadc :=
  append_checked p4830_1019_2339_220 p4830_1019_2559_440
private theorem p4830_1019_2999_440 : blockEstimate 4830 1019 2999 440 = 0x1cf1fa1e588 :=
  append_checked p4830_1019_2999_220 p4830_1019_3219_220
private theorem p4830_1019_3439_440 : blockEstimate 4830 1019 3439 440 = 0x1e616df1a08 :=
  append_checked p4830_1019_3439_220 p4830_1019_3659_220
private theorem p4830_1019_2999_880 : blockEstimate 4830 1019 2999 880 = 0x3b53680ff90 :=
  append_checked p4830_1019_2999_440 p4830_1019_3439_440
private theorem p4830_1019_2339_1540 : blockEstimate 4830 1019 2339 1540 = 0x5e854a6aa6c :=
  append_checked p4830_1019_2339_660 p4830_1019_2999_880
private theorem p4830_1019_1019_2860 : blockEstimate 4830 1019 1019 2860 = 0x73c1abb9d49 :=
  append_checked p4830_1019_1019_1320 p4830_1019_2339_1540
private theorem p4830_1019_4099_440 : blockEstimate 4830 1019 4099 440 = 0x1bcacd1fac8 :=
  append_checked p4830_1019_4099_220 p4830_1019_4319_220
private theorem p4830_1019_3879_660 : blockEstimate 4830 1019 3879 660 = 0x2abb026fe7c :=
  append_checked p4830_1019_3879_220 p4830_1019_4099_440
private theorem p4830_1019_4539_440 : blockEstimate 4830 1019 4539 440 = 0x16eae9a25f2 :=
  append_checked p4830_1019_4539_220 p4830_1019_4759_220
private theorem p4830_1019_4979_440 : blockEstimate 4830 1019 4979 440 = 0x105488cd4b6 :=
  append_checked p4830_1019_4979_220 p4830_1019_5199_220
private theorem p4830_1019_4539_880 : blockEstimate 4830 1019 4539 880 = 0x273f726faa8 :=
  append_checked p4830_1019_4539_440 p4830_1019_4979_440
private theorem p4830_1019_3879_1540 : blockEstimate 4830 1019 3879 1540 = 0x51fa74df924 :=
  append_checked p4830_1019_3879_660 p4830_1019_4539_880
private theorem p4830_1019_5639_440 : blockEstimate 4830 1019 5639 440 = 0x6eccfad5fd :=
  append_checked p4830_1019_5639_220 p4830_1019_5859_220
private theorem p4830_1019_5419_660 : blockEstimate 4830 1019 5419 660 = 0xc990c2d911 :=
  append_checked p4830_1019_5419_220 p4830_1019_5639_440
private theorem p4830_1019_6079_440 : blockEstimate 4830 1019 6079 440 = 0x26dae8eba7 :=
  append_checked p4830_1019_6079_220 p4830_1019_6299_220
private theorem p4830_1019_6519_349 : blockEstimate 4830 1019 6519 349 = 0x3e629d3d4 :=
  append_checked p4830_1019_6519_220 p4830_1019_6739_129
private theorem p4830_1019_6079_789 : blockEstimate 4830 1019 6079 789 = 0x2ac112bf7b :=
  append_checked p4830_1019_6079_440 p4830_1019_6519_349
private theorem p4830_1019_5419_1449 : blockEstimate 4830 1019 5419 1449 = 0xf451d5988c :=
  append_checked p4830_1019_5419_660 p4830_1019_6079_789
private theorem p4830_1019_3879_2989 : blockEstimate 4830 1019 3879 2989 = 0x613f92391b0 :=
  append_checked p4830_1019_3879_1540 p4830_1019_5419_1449
private theorem p4830_1019_1019_5849 : blockEstimate 4830 1019 1019 5849 = 0xd5013df2ef9 :=
  append_checked p4830_1019_1019_2860 p4830_1019_3879_2989

theorem moment4830_1019 : momentEstimate 4830 1019 = 0xd5013df2ef9 := p4830_1019_1019_5849
end HighCore82229BankProof
