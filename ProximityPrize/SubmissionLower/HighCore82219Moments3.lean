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
  block_append (B := 1388) (J := 254) (start := 254) (next := 469)
    (a := 215) (b := 215) (n := 430) (x := 0x7ae2cee2) (y := 0x29edd26f6) (z := 0x319bff5d8)
    p1388_254_254 p1388_254_469 rfl rfl rfl

private theorem s1388_254_684_430 : blockEstimate 1388 254 684 430 = 0x972d22889 :=
  block_append (B := 1388) (J := 254) (start := 684) (next := 899)
    (a := 215) (b := 215) (n := 430) (x := 0x46a5eb57d) (y := 0x50873730c) (z := 0x972d22889)
    p1388_254_684 p1388_254_899 rfl rfl rfl

private theorem s1388_254_254_860 : blockEstimate 1388 254 254 860 = 0xc8c921e61 :=
  block_append (B := 1388) (J := 254) (start := 254) (next := 684)
    (a := 430) (b := 430) (n := 860) (x := 0x319bff5d8) (y := 0x972d22889) (z := 0xc8c921e61)
    s1388_254_254_430 s1388_254_684_430 rfl rfl rfl

private theorem s1388_254_1114_430 : blockEstimate 1388 254 1114 430 = 0x746a95649 :=
  block_append (B := 1388) (J := 254) (start := 1114) (next := 1329)
    (a := 215) (b := 215) (n := 430) (x := 0x4786bee29) (y := 0x2ce3d6820) (z := 0x746a95649)
    p1388_254_1114 p1388_254_1329 rfl rfl rfl

private theorem s1388_254_1544_352 : blockEstimate 1388 254 1544 352 = 0x10b51a589 :=
  block_append (B := 1388) (J := 254) (start := 1544) (next := 1759)
    (a := 215) (b := 137) (n := 352) (x := 0xf9d7c61c) (y := 0x1179df6d) (z := 0x10b51a589)
    p1388_254_1544 p1388_254_1759 rfl rfl rfl

private theorem s1388_254_1114_782 : blockEstimate 1388 254 1114 782 = 0x851fafbd2 :=
  block_append (B := 1388) (J := 254) (start := 1114) (next := 1544)
    (a := 430) (b := 352) (n := 782) (x := 0x746a95649) (y := 0x10b51a589) (z := 0x851fafbd2)
    s1388_254_1114_430 s1388_254_1544_352 rfl rfl rfl

private theorem s1388_254_254_1642 : blockEstimate 1388 254 254 1642 = 0x14de8d1a33 :=
  block_append (B := 1388) (J := 254) (start := 254) (next := 1114)
    (a := 860) (b := 782) (n := 1642) (x := 0xc8c921e61) (y := 0x851fafbd2) (z := 0x14de8d1a33)
    s1388_254_254_860 s1388_254_1114_782 rfl rfl rfl

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
  block_append (B := 1428) (J := 311) (start := 311) (next := 526)
    (a := 215) (b := 215) (n := 430) (x := 0x7ee3f142) (y := 0x2dfc0dc80) (z := 0x35ea4cdc2)
    p1428_311_311 p1428_311_526 rfl rfl rfl

private theorem s1428_311_741_430 : blockEstimate 1428 311 741 430 = 0xb82c938ac :=
  block_append (B := 1428) (J := 311) (start := 741) (next := 956)
    (a := 215) (b := 215) (n := 430) (x := 0x5433e06dc) (y := 0x63f8b31d0) (z := 0xb82c938ac)
    p1428_311_741 p1428_311_956 rfl rfl rfl

private theorem s1428_311_311_860 : blockEstimate 1428 311 311 860 = 0xee16e066e :=
  block_append (B := 1428) (J := 311) (start := 311) (next := 741)
    (a := 430) (b := 430) (n := 860) (x := 0x35ea4cdc2) (y := 0xb82c938ac) (z := 0xee16e066e)
    s1428_311_311_430 s1428_311_741_430 rfl rfl rfl

private theorem s1428_311_1171_430 : blockEstimate 1428 311 1171 430 = 0x9c732b17c :=
  block_append (B := 1428) (J := 311) (start := 1171) (next := 1386)
    (a := 215) (b := 215) (n := 430) (x := 0x5ca3447b4) (y := 0x3fcfe69c8) (z := 0x9c732b17c)
    p1428_311_1171 p1428_311_1386 rfl rfl rfl

private theorem s1428_311_1816_234 : blockEstimate 1428 311 1816 234 = 0x5590a93c :=
  block_append (B := 1428) (J := 311) (start := 1816) (next := 2031)
    (a := 215) (b := 19) (n := 234) (x := 0x55812bf6) (y := 0xf7d46) (z := 0x5590a93c)
    p1428_311_1816 p1428_311_2031 rfl rfl rfl

private theorem s1428_311_1601_449 : blockEstimate 1428 311 1601 449 = 0x22566b3e9 :=
  block_append (B := 1428) (J := 311) (start := 1601) (next := 1816)
    (a := 215) (b := 234) (n := 449) (x := 0x1cfd60aad) (y := 0x5590a93c) (z := 0x22566b3e9)
    p1428_311_1601 s1428_311_1816_234 rfl rfl rfl

private theorem s1428_311_1171_879 : blockEstimate 1428 311 1171 879 = 0xbec996565 :=
  block_append (B := 1428) (J := 311) (start := 1171) (next := 1601)
    (a := 430) (b := 449) (n := 879) (x := 0x9c732b17c) (y := 0x22566b3e9) (z := 0xbec996565)
    s1428_311_1171_430 s1428_311_1601_449 rfl rfl rfl

private theorem s1428_311_311_1739 : blockEstimate 1428 311 311 1739 = 0x1ace076bd3 :=
  block_append (B := 1428) (J := 311) (start := 311) (next := 1171)
    (a := 860) (b := 879) (n := 1739) (x := 0xee16e066e) (y := 0xbec996565) (z := 0x1ace076bd3)
    s1428_311_311_860 s1428_311_1171_879 rfl rfl rfl

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
  block_append (B := 1451) (J := 305) (start := 305) (next := 520)
    (a := 215) (b := 215) (n := 430) (x := 0x81316506) (y := 0x2ec880961) (z := 0x36db96e67)
    p1451_305_305 p1451_305_520 rfl rfl rfl

private theorem s1451_305_735_430 : blockEstimate 1451 305 735 430 = 0xbb57b14af :=
  block_append (B := 1451) (J := 305) (start := 735) (next := 950)
    (a := 215) (b := 215) (n := 430) (x := 0x55695ac62) (y := 0x65ee5684d) (z := 0xbb57b14af)
    p1451_305_735 p1451_305_950 rfl rfl rfl

private theorem s1451_305_305_860 : blockEstimate 1451 305 305 860 = 0xf23348316 :=
  block_append (B := 1451) (J := 305) (start := 305) (next := 735)
    (a := 430) (b := 430) (n := 860) (x := 0x36db96e67) (y := 0xbb57b14af) (z := 0xf23348316)
    s1451_305_305_430 s1451_305_735_430 rfl rfl rfl

private theorem s1451_305_1165_430 : blockEstimate 1451 305 1165 430 = 0xa3b8d15aa :=
  block_append (B := 1451) (J := 305) (start := 1165) (next := 1380)
    (a := 215) (b := 215) (n := 430) (x := 0x5fcacd47c) (y := 0x43ee0412e) (z := 0xa3b8d15aa)
    p1451_305_1165 p1451_305_1380 rfl rfl rfl

private theorem s1451_305_1810_251 : blockEstimate 1451 305 1810 251 = 0x6aaad1b5 :=
  block_append (B := 1451) (J := 305) (start := 1810) (next := 2025)
    (a := 215) (b := 36) (n := 251) (x := 0x6a4abb17) (y := 0x60169e) (z := 0x6aaad1b5)
    p1451_305_1810 p1451_305_2025 rfl rfl rfl

private theorem s1451_305_1595_466 : blockEstimate 1451 305 1595 466 = 0x26c28775e :=
  block_append (B := 1451) (J := 305) (start := 1595) (next := 1810)
    (a := 215) (b := 251) (n := 466) (x := 0x2017da5a9) (y := 0x6aaad1b5) (z := 0x26c28775e)
    p1451_305_1595 s1451_305_1810_251 rfl rfl rfl

private theorem s1451_305_1165_896 : blockEstimate 1451 305 1165 896 = 0xca7b58d08 :=
  block_append (B := 1451) (J := 305) (start := 1165) (next := 1595)
    (a := 430) (b := 466) (n := 896) (x := 0xa3b8d15aa) (y := 0x26c28775e) (z := 0xca7b58d08)
    s1451_305_1165_430 s1451_305_1595_466 rfl rfl rfl

private theorem s1451_305_305_1756 : blockEstimate 1451 305 305 1756 = 0x1bcaea101e :=
  block_append (B := 1451) (J := 305) (start := 305) (next := 1165)
    (a := 860) (b := 896) (n := 1756) (x := 0xf23348316) (y := 0xca7b58d08) (z := 0x1bcaea101e)
    s1451_305_305_860 s1451_305_1165_896 rfl rfl rfl

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
  block_append (B := 1507) (J := 264) (start := 264) (next := 479)
    (a := 215) (b := 215) (n := 430) (x := 0x86cc9526) (y := 0x2f50ad2c1) (z := 0x37bd767e7)
    p1507_264_264 p1507_264_479 rfl rfl rfl

private theorem s1507_264_694_430 : blockEstimate 1507 264 694 430 = 0xb5775b775 :=
  block_append (B := 1507) (J := 264) (start := 694) (next := 909)
    (a := 215) (b := 215) (n := 430) (x := 0x52c5249b0) (y := 0x62b236dc5) (z := 0xb5775b775)
    p1507_264_694 p1507_264_909 rfl rfl rfl

private theorem s1507_264_264_860 : blockEstimate 1507 264 264 860 = 0xed34d1f5c :=
  block_append (B := 1507) (J := 264) (start := 264) (next := 694)
    (a := 430) (b := 430) (n := 860) (x := 0x37bd767e7) (y := 0xb5775b775) (z := 0xed34d1f5c)
    s1507_264_264_430 s1507_264_694_430 rfl rfl rfl

private theorem s1507_264_1124_430 : blockEstimate 1507 264 1124 430 = 0xa6b71db06 :=
  block_append (B := 1507) (J := 264) (start := 1124) (next := 1339)
    (a := 215) (b := 215) (n := 430) (x := 0x5efff5bdc) (y := 0x47b727f2a) (z := 0xa6b71db06)
    p1507_264_1124 p1507_264_1339 rfl rfl rfl

private theorem s1507_264_1769_266 : blockEstimate 1507 264 1769 266 = 0x837c1d15 :=
  block_append (B := 1507) (J := 264) (start := 1769) (next := 1984)
    (a := 215) (b := 51) (n := 266) (x := 0x826b4692) (y := 0x110d683) (z := 0x837c1d15)
    p1507_264_1769 p1507_264_1984 rfl rfl rfl

private theorem s1507_264_1554_481 : blockEstimate 1507 264 1554 481 = 0x2bf779148 :=
  block_append (B := 1507) (J := 264) (start := 1554) (next := 1769)
    (a := 215) (b := 266) (n := 481) (x := 0x23bfb7433) (y := 0x837c1d15) (z := 0x2bf779148)
    p1507_264_1554 s1507_264_1769_266 rfl rfl rfl

private theorem s1507_264_1124_911 : blockEstimate 1507 264 1124 911 = 0xd2ae96c4e :=
  block_append (B := 1507) (J := 264) (start := 1124) (next := 1554)
    (a := 430) (b := 481) (n := 911) (x := 0xa6b71db06) (y := 0x2bf779148) (z := 0xd2ae96c4e)
    s1507_264_1124_430 s1507_264_1554_481 rfl rfl rfl

private theorem s1507_264_264_1771 : blockEstimate 1507 264 264 1771 = 0x1bfe368baa :=
  block_append (B := 1507) (J := 264) (start := 264) (next := 1124)
    (a := 860) (b := 911) (n := 1771) (x := 0xed34d1f5c) (y := 0xd2ae96c4e) (z := 0x1bfe368baa)
    s1507_264_264_860 s1507_264_1124_911 rfl rfl rfl

theorem moment1507_264 : momentEstimate 1507 264 = 0x1bfe368baa := s1507_264_264_1771

end HighCore82219BankProof
