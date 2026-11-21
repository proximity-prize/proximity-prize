import ProximityPrize.SubmissionLower.HighCore82219Moments2

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p1388_254_254 : blockEstimate 1388 254 254 215 = 0x7ae2cee2 := by decide +kernel
private theorem p1388_254_469 : blockEstimate 1388 254 469 215 = 0x29edd26f6 := by decide +kernel
private theorem p1388_254_684 : blockEstimate 1388 254 684 215 = 0x46a5eb57d := by decide +kernel
private theorem p1388_254_899 : blockEstimate 1388 254 899 215 = 0x50873730c := by decide +kernel
private theorem p1388_254_1114 : blockEstimate 1388 254 1114 215 = 0x4786bee29 := by decide +kernel
private theorem p1388_254_1329 : blockEstimate 1388 254 1329 215 = 0x2ce3d6820 := by decide +kernel
private theorem p1388_254_1544 : blockEstimate 1388 254 1544 215 = 0xf9d7c61c := by decide +kernel
private theorem p1388_254_1759 : blockEstimate 1388 254 1759 137 = 0x1179df6d := by decide +kernel

private theorem s1388_254_254_430 : blockEstimate 1388 254 254 430 = 0x319bff5d8 :=
  block_append p1388_254_254 p1388_254_469 rfl rfl rfl

private theorem s1388_254_684_430 : blockEstimate 1388 254 684 430 = 0x972d22889 :=
  block_append p1388_254_684 p1388_254_899 rfl rfl rfl

private theorem s1388_254_254_860 : blockEstimate 1388 254 254 860 = 0xc8c921e61 :=
  block_append s1388_254_254_430 s1388_254_684_430 rfl rfl rfl

private theorem s1388_254_1114_430 : blockEstimate 1388 254 1114 430 = 0x746a95649 :=
  block_append p1388_254_1114 p1388_254_1329 rfl rfl rfl

private theorem s1388_254_1544_352 : blockEstimate 1388 254 1544 352 = 0x10b51a589 :=
  block_append p1388_254_1544 p1388_254_1759 rfl rfl rfl

private theorem s1388_254_1114_782 : blockEstimate 1388 254 1114 782 = 0x851fafbd2 :=
  block_append s1388_254_1114_430 s1388_254_1544_352 rfl rfl rfl

private theorem s1388_254_254_1642 : blockEstimate 1388 254 254 1642 = 0x14de8d1a33 :=
  block_append s1388_254_254_860 s1388_254_1114_782 rfl rfl rfl

theorem moment1388_254 : momentEstimate 1388 254 = 0x14de8d1a33 := s1388_254_254_1642

private theorem p1428_311_311 : blockEstimate 1428 311 311 215 = 0x7ee3f142 := by decide +kernel
private theorem p1428_311_526 : blockEstimate 1428 311 526 215 = 0x2dfc0dc80 := by decide +kernel
private theorem p1428_311_741 : blockEstimate 1428 311 741 215 = 0x5433e06dc := by decide +kernel
private theorem p1428_311_956 : blockEstimate 1428 311 956 215 = 0x63f8b31d0 := by decide +kernel
private theorem p1428_311_1171 : blockEstimate 1428 311 1171 215 = 0x5ca3447b4 := by decide +kernel
private theorem p1428_311_1386 : blockEstimate 1428 311 1386 215 = 0x3fcfe69c8 := by decide +kernel
private theorem p1428_311_1601 : blockEstimate 1428 311 1601 215 = 0x1cfd60aad := by decide +kernel
private theorem p1428_311_1816 : blockEstimate 1428 311 1816 215 = 0x55812bf6 := by decide +kernel
private theorem p1428_311_2031 : blockEstimate 1428 311 2031 19 = 0xf7d46 := by decide +kernel

private theorem s1428_311_311_430 : blockEstimate 1428 311 311 430 = 0x35ea4cdc2 :=
  block_append p1428_311_311 p1428_311_526 rfl rfl rfl

private theorem s1428_311_741_430 : blockEstimate 1428 311 741 430 = 0xb82c938ac :=
  block_append p1428_311_741 p1428_311_956 rfl rfl rfl

private theorem s1428_311_311_860 : blockEstimate 1428 311 311 860 = 0xee16e066e :=
  block_append s1428_311_311_430 s1428_311_741_430 rfl rfl rfl

private theorem s1428_311_1171_430 : blockEstimate 1428 311 1171 430 = 0x9c732b17c :=
  block_append p1428_311_1171 p1428_311_1386 rfl rfl rfl

private theorem s1428_311_1816_234 : blockEstimate 1428 311 1816 234 = 0x5590a93c :=
  block_append p1428_311_1816 p1428_311_2031 rfl rfl rfl

private theorem s1428_311_1601_449 : blockEstimate 1428 311 1601 449 = 0x22566b3e9 :=
  block_append p1428_311_1601 s1428_311_1816_234 rfl rfl rfl

private theorem s1428_311_1171_879 : blockEstimate 1428 311 1171 879 = 0xbec996565 :=
  block_append s1428_311_1171_430 s1428_311_1601_449 rfl rfl rfl

private theorem s1428_311_311_1739 : blockEstimate 1428 311 311 1739 = 0x1ace076bd3 :=
  block_append s1428_311_311_860 s1428_311_1171_879 rfl rfl rfl

theorem moment1428_311 : momentEstimate 1428 311 = 0x1ace076bd3 := s1428_311_311_1739

private theorem p1451_305_305 : blockEstimate 1451 305 305 215 = 0x81316506 := by decide +kernel
private theorem p1451_305_520 : blockEstimate 1451 305 520 215 = 0x2ec880961 := by decide +kernel
private theorem p1451_305_735 : blockEstimate 1451 305 735 215 = 0x55695ac62 := by decide +kernel
private theorem p1451_305_950 : blockEstimate 1451 305 950 215 = 0x65ee5684d := by decide +kernel
private theorem p1451_305_1165 : blockEstimate 1451 305 1165 215 = 0x5fcacd47c := by decide +kernel
private theorem p1451_305_1380 : blockEstimate 1451 305 1380 215 = 0x43ee0412e := by decide +kernel
private theorem p1451_305_1595 : blockEstimate 1451 305 1595 215 = 0x2017da5a9 := by decide +kernel
private theorem p1451_305_1810 : blockEstimate 1451 305 1810 215 = 0x6a4abb17 := by decide +kernel
private theorem p1451_305_2025 : blockEstimate 1451 305 2025 36 = 0x60169e := by decide +kernel

private theorem s1451_305_305_430 : blockEstimate 1451 305 305 430 = 0x36db96e67 :=
  block_append p1451_305_305 p1451_305_520 rfl rfl rfl

private theorem s1451_305_735_430 : blockEstimate 1451 305 735 430 = 0xbb57b14af :=
  block_append p1451_305_735 p1451_305_950 rfl rfl rfl

private theorem s1451_305_305_860 : blockEstimate 1451 305 305 860 = 0xf23348316 :=
  block_append s1451_305_305_430 s1451_305_735_430 rfl rfl rfl

private theorem s1451_305_1165_430 : blockEstimate 1451 305 1165 430 = 0xa3b8d15aa :=
  block_append p1451_305_1165 p1451_305_1380 rfl rfl rfl

private theorem s1451_305_1810_251 : blockEstimate 1451 305 1810 251 = 0x6aaad1b5 :=
  block_append p1451_305_1810 p1451_305_2025 rfl rfl rfl

private theorem s1451_305_1595_466 : blockEstimate 1451 305 1595 466 = 0x26c28775e :=
  block_append p1451_305_1595 s1451_305_1810_251 rfl rfl rfl

private theorem s1451_305_1165_896 : blockEstimate 1451 305 1165 896 = 0xca7b58d08 :=
  block_append s1451_305_1165_430 s1451_305_1595_466 rfl rfl rfl

private theorem s1451_305_305_1756 : blockEstimate 1451 305 305 1756 = 0x1bcaea101e :=
  block_append s1451_305_305_860 s1451_305_1165_896 rfl rfl rfl

theorem moment1451_305 : momentEstimate 1451 305 = 0x1bcaea101e := s1451_305_305_1756

private theorem p1507_264_264 : blockEstimate 1507 264 264 215 = 0x86cc9526 := by decide +kernel
private theorem p1507_264_479 : blockEstimate 1507 264 479 215 = 0x2f50ad2c1 := by decide +kernel
private theorem p1507_264_694 : blockEstimate 1507 264 694 215 = 0x52c5249b0 := by decide +kernel
private theorem p1507_264_909 : blockEstimate 1507 264 909 215 = 0x62b236dc5 := by decide +kernel
private theorem p1507_264_1124 : blockEstimate 1507 264 1124 215 = 0x5efff5bdc := by decide +kernel
private theorem p1507_264_1339 : blockEstimate 1507 264 1339 215 = 0x47b727f2a := by decide +kernel
private theorem p1507_264_1554 : blockEstimate 1507 264 1554 215 = 0x23bfb7433 := by decide +kernel
private theorem p1507_264_1769 : blockEstimate 1507 264 1769 215 = 0x826b4692 := by decide +kernel
private theorem p1507_264_1984 : blockEstimate 1507 264 1984 51 = 0x110d683 := by decide +kernel

private theorem s1507_264_264_430 : blockEstimate 1507 264 264 430 = 0x37bd767e7 :=
  block_append p1507_264_264 p1507_264_479 rfl rfl rfl

private theorem s1507_264_694_430 : blockEstimate 1507 264 694 430 = 0xb5775b775 :=
  block_append p1507_264_694 p1507_264_909 rfl rfl rfl

private theorem s1507_264_264_860 : blockEstimate 1507 264 264 860 = 0xed34d1f5c :=
  block_append s1507_264_264_430 s1507_264_694_430 rfl rfl rfl

private theorem s1507_264_1124_430 : blockEstimate 1507 264 1124 430 = 0xa6b71db06 :=
  block_append p1507_264_1124 p1507_264_1339 rfl rfl rfl

private theorem s1507_264_1769_266 : blockEstimate 1507 264 1769 266 = 0x837c1d15 :=
  block_append p1507_264_1769 p1507_264_1984 rfl rfl rfl

private theorem s1507_264_1554_481 : blockEstimate 1507 264 1554 481 = 0x2bf779148 :=
  block_append p1507_264_1554 s1507_264_1769_266 rfl rfl rfl

private theorem s1507_264_1124_911 : blockEstimate 1507 264 1124 911 = 0xd2ae96c4e :=
  block_append s1507_264_1124_430 s1507_264_1554_481 rfl rfl rfl

private theorem s1507_264_264_1771 : blockEstimate 1507 264 264 1771 = 0x1bfe368baa :=
  block_append s1507_264_264_860 s1507_264_1124_911 rfl rfl rfl

theorem moment1507_264 : momentEstimate 1507 264 = 0x1bfe368baa := s1507_264_264_1771

end HighCore82219BankProof
