import ProximityPrize.SubmissionLower.HighCore82219Moments6

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p2994_634_634 : blockEstimate 2994 634 634 215 = 0x11ba9f30a := by decide +kernel
private theorem p2994_634_849 : blockEstimate 2994 634 849 215 = 0x731b5dafa := by decide +kernel
private theorem p2994_634_1064 : blockEstimate 2994 634 1064 215 = 0x11f7483092 := by decide +kernel
private theorem p2994_634_1279 : blockEstimate 2994 634 1279 215 = 0x1ef32e86ac := by decide +kernel
private theorem p2994_634_1494 : blockEstimate 2994 634 1494 215 = 0x29d2be7269 := by decide +kernel
private theorem p2994_634_1709 : blockEstimate 2994 634 1709 215 = 0x31c1fdf4ec := by decide +kernel
private theorem p2994_634_1924 : blockEstimate 2994 634 1924 215 = 0x36c0ed0e35 := by decide +kernel
private theorem p2994_634_2139 : blockEstimate 2994 634 2139 215 = 0x38cf8bbe44 := by decide +kernel
private theorem p2994_634_2354 : blockEstimate 2994 634 2354 215 = 0x37edda0519 := by decide +kernel
private theorem p2994_634_2569 : blockEstimate 2994 634 2569 215 = 0x341bd7e2b4 := by decide +kernel
private theorem p2994_634_2784 : blockEstimate 2994 634 2784 215 = 0x2d5985aeff := by decide +kernel
private theorem p2994_634_2999 : blockEstimate 2994 634 2999 215 = 0x240faa8ec7 := by decide +kernel
private theorem p2994_634_3214 : blockEstimate 2994 634 3214 215 = 0x1a1edd68a0 := by decide +kernel
private theorem p2994_634_3429 : blockEstimate 2994 634 3429 215 = 0x10c83714c6 := by decide +kernel
private theorem p2994_634_3644 : blockEstimate 2994 634 3644 215 = 0x8e002a2f2 := by decide +kernel
private theorem p2994_634_3859 : blockEstimate 2994 634 3859 215 = 0x3381f5615 := by decide +kernel
private theorem p2994_634_4074 : blockEstimate 2994 634 4074 188 = 0x623d13bb := by decide +kernel

private theorem s2994_634_634_430 : blockEstimate 2994 634 634 430 = 0x84d5fce04 :=
  block_append (B := 2994) (J := 634) (start := 634) (next := 849)
    (a := 215) (b := 215) (n := 430) (x := 0x11ba9f30a) (y := 0x731b5dafa) (z := 0x84d5fce04)
    p2994_634_634 p2994_634_849 rfl rfl rfl

private theorem s2994_634_1064_430 : blockEstimate 2994 634 1064 430 = 0x30ea76b73e :=
  block_append (B := 2994) (J := 634) (start := 1064) (next := 1279)
    (a := 215) (b := 215) (n := 430) (x := 0x11f7483092) (y := 0x1ef32e86ac) (z := 0x30ea76b73e)
    p2994_634_1064 p2994_634_1279 rfl rfl rfl

private theorem s2994_634_634_860 : blockEstimate 2994 634 634 860 = 0x3937d68542 :=
  block_append (B := 2994) (J := 634) (start := 634) (next := 1064)
    (a := 430) (b := 430) (n := 860) (x := 0x84d5fce04) (y := 0x30ea76b73e) (z := 0x3937d68542)
    s2994_634_634_430 s2994_634_1064_430 rfl rfl rfl

private theorem s2994_634_1494_430 : blockEstimate 2994 634 1494 430 = 0x5b94bc6755 :=
  block_append (B := 2994) (J := 634) (start := 1494) (next := 1709)
    (a := 215) (b := 215) (n := 430) (x := 0x29d2be7269) (y := 0x31c1fdf4ec) (z := 0x5b94bc6755)
    p2994_634_1494 p2994_634_1709 rfl rfl rfl

private theorem s2994_634_1924_430 : blockEstimate 2994 634 1924 430 = 0x6f9078cc79 :=
  block_append (B := 2994) (J := 634) (start := 1924) (next := 2139)
    (a := 215) (b := 215) (n := 430) (x := 0x36c0ed0e35) (y := 0x38cf8bbe44) (z := 0x6f9078cc79)
    p2994_634_1924 p2994_634_2139 rfl rfl rfl

private theorem s2994_634_1494_860 : blockEstimate 2994 634 1494 860 = 0xcb253533ce :=
  block_append (B := 2994) (J := 634) (start := 1494) (next := 1924)
    (a := 430) (b := 430) (n := 860) (x := 0x5b94bc6755) (y := 0x6f9078cc79) (z := 0xcb253533ce)
    s2994_634_1494_430 s2994_634_1924_430 rfl rfl rfl

private theorem s2994_634_634_1720 : blockEstimate 2994 634 634 1720 = 0x1045d0bb910 :=
  block_append (B := 2994) (J := 634) (start := 634) (next := 1494)
    (a := 860) (b := 860) (n := 1720) (x := 0x3937d68542) (y := 0xcb253533ce) (z := 0x1045d0bb910)
    s2994_634_634_860 s2994_634_1494_860 rfl rfl rfl

private theorem s2994_634_2354_430 : blockEstimate 2994 634 2354 430 = 0x6c09b1e7cd :=
  block_append (B := 2994) (J := 634) (start := 2354) (next := 2569)
    (a := 215) (b := 215) (n := 430) (x := 0x37edda0519) (y := 0x341bd7e2b4) (z := 0x6c09b1e7cd)
    p2994_634_2354 p2994_634_2569 rfl rfl rfl

private theorem s2994_634_2784_430 : blockEstimate 2994 634 2784 430 = 0x5169303dc6 :=
  block_append (B := 2994) (J := 634) (start := 2784) (next := 2999)
    (a := 215) (b := 215) (n := 430) (x := 0x2d5985aeff) (y := 0x240faa8ec7) (z := 0x5169303dc6)
    p2994_634_2784 p2994_634_2999 rfl rfl rfl

private theorem s2994_634_2354_860 : blockEstimate 2994 634 2354 860 = 0xbd72e22593 :=
  block_append (B := 2994) (J := 634) (start := 2354) (next := 2784)
    (a := 430) (b := 430) (n := 860) (x := 0x6c09b1e7cd) (y := 0x5169303dc6) (z := 0xbd72e22593)
    s2994_634_2354_430 s2994_634_2784_430 rfl rfl rfl

private theorem s2994_634_3214_430 : blockEstimate 2994 634 3214 430 = 0x2ae7147d66 :=
  block_append (B := 2994) (J := 634) (start := 3214) (next := 3429)
    (a := 215) (b := 215) (n := 430) (x := 0x1a1edd68a0) (y := 0x10c83714c6) (z := 0x2ae7147d66)
    p2994_634_3214 p2994_634_3429 rfl rfl rfl

private theorem s2994_634_3859_403 : blockEstimate 2994 634 3859 403 = 0x39a5c69d0 :=
  block_append (B := 2994) (J := 634) (start := 3859) (next := 4074)
    (a := 215) (b := 188) (n := 403) (x := 0x3381f5615) (y := 0x623d13bb) (z := 0x39a5c69d0)
    p2994_634_3859 p2994_634_4074 rfl rfl rfl

private theorem s2994_634_3644_618 : blockEstimate 2994 634 3644 618 = 0xc7a5f0cc2 :=
  block_append (B := 2994) (J := 634) (start := 3644) (next := 3859)
    (a := 215) (b := 403) (n := 618) (x := 0x8e002a2f2) (y := 0x39a5c69d0) (z := 0xc7a5f0cc2)
    p2994_634_3644 s2994_634_3859_403 rfl rfl rfl

private theorem s2994_634_3214_1048 : blockEstimate 2994 634 3214 1048 = 0x3761738a28 :=
  block_append (B := 2994) (J := 634) (start := 3214) (next := 3644)
    (a := 430) (b := 618) (n := 1048) (x := 0x2ae7147d66) (y := 0xc7a5f0cc2) (z := 0x3761738a28)
    s2994_634_3214_430 s2994_634_3644_618 rfl rfl rfl

private theorem s2994_634_2354_1908 : blockEstimate 2994 634 2354 1908 = 0xf4d455afbb :=
  block_append (B := 2994) (J := 634) (start := 2354) (next := 3214)
    (a := 860) (b := 1048) (n := 1908) (x := 0xbd72e22593) (y := 0x3761738a28) (z := 0xf4d455afbb)
    s2994_634_2354_860 s2994_634_3214_1048 rfl rfl rfl

private theorem s2994_634_634_3628 : blockEstimate 2994 634 634 3628 = 0x1f9316168cb :=
  block_append (B := 2994) (J := 634) (start := 634) (next := 2354)
    (a := 1720) (b := 1908) (n := 3628) (x := 0x1045d0bb910) (y := 0xf4d455afbb) (z := 0x1f9316168cb)
    s2994_634_634_1720 s2994_634_2354_1908 rfl rfl rfl

theorem moment2994_634 : momentEstimate 2994 634 = 0x1f9316168cb := s2994_634_634_3628

private theorem p3335_706_706 : blockEstimate 3335 706 706 215 = 0x13dcd3816 := by decide +kernel
private theorem p3335_706_921 : blockEstimate 3335 706 921 215 = 0x81ec9773e := by decide +kernel
private theorem p3335_706_1136 : blockEstimate 3335 706 1136 215 = 0x147953db98 := by decide +kernel
private theorem p3335_706_1351 : blockEstimate 3335 706 1351 215 = 0x24742231d7 := by decide +kernel
private theorem p3335_706_1566 : blockEstimate 3335 706 1566 215 = 0x3367a80b84 := by decide +kernel
private theorem p3335_706_1781 : blockEstimate 3335 706 1781 215 = 0x3f1b98166a := by decide +kernel
private theorem p3335_706_1996 : blockEstimate 3335 706 1996 215 = 0x4789ea7826 := by decide +kernel
private theorem p3335_706_2211 : blockEstimate 3335 706 2211 215 = 0x4cb29f30b8 := by decide +kernel
private theorem p3335_706_2426 : blockEstimate 3335 706 2426 215 = 0x4e95b64020 := by decide +kernel
private theorem p3335_706_2641 : blockEstimate 3335 706 2641 215 = 0x4d332fa65e := by decide +kernel
private theorem p3335_706_2856 : blockEstimate 3335 706 2856 215 = 0x488b0b6372 := by decide +kernel
private theorem p3335_706_3071 : blockEstimate 3335 706 3071 215 = 0x409d49775c := by decide +kernel
private theorem p3335_706_3286 : blockEstimate 3335 706 3286 215 = 0x359a36b34a := by decide +kernel
private theorem p3335_706_3501 : blockEstimate 3335 706 3501 215 = 0x2944ef6a90 := by decide +kernel
private theorem p3335_706_3716 : blockEstimate 3335 706 3716 215 = 0x1d346178ba := by decide +kernel
private theorem p3335_706_3931 : blockEstimate 3335 706 3931 215 = 0x1250ccd3dc := by decide +kernel
private theorem p3335_706_4146 : blockEstimate 3335 706 4146 215 = 0x965e7d948 := by decide +kernel
private theorem p3335_706_4361 : blockEstimate 3335 706 4361 215 = 0x33cbe935f := by decide +kernel
private theorem p3335_706_4576 : blockEstimate 3335 706 4576 171 = 0x52ff1ca5 := by decide +kernel

private theorem s3335_706_706_430 : blockEstimate 3335 706 706 430 = 0x95c96af54 :=
  block_append (B := 3335) (J := 706) (start := 706) (next := 921)
    (a := 215) (b := 215) (n := 430) (x := 0x13dcd3816) (y := 0x81ec9773e) (z := 0x95c96af54)
    p3335_706_706 p3335_706_921 rfl rfl rfl

private theorem s3335_706_1136_430 : blockEstimate 3335 706 1136 430 = 0x38ed760d6f :=
  block_append (B := 3335) (J := 706) (start := 1136) (next := 1351)
    (a := 215) (b := 215) (n := 430) (x := 0x147953db98) (y := 0x24742231d7) (z := 0x38ed760d6f)
    p3335_706_1136 p3335_706_1351 rfl rfl rfl

private theorem s3335_706_706_860 : blockEstimate 3335 706 706 860 = 0x424a0cbcc3 :=
  block_append (B := 3335) (J := 706) (start := 706) (next := 1136)
    (a := 430) (b := 430) (n := 860) (x := 0x95c96af54) (y := 0x38ed760d6f) (z := 0x424a0cbcc3)
    s3335_706_706_430 s3335_706_1136_430 rfl rfl rfl

private theorem s3335_706_1566_430 : blockEstimate 3335 706 1566 430 = 0x72834021ee :=
  block_append (B := 3335) (J := 706) (start := 1566) (next := 1781)
    (a := 215) (b := 215) (n := 430) (x := 0x3367a80b84) (y := 0x3f1b98166a) (z := 0x72834021ee)
    p3335_706_1566 p3335_706_1781 rfl rfl rfl

private theorem s3335_706_2211_430 : blockEstimate 3335 706 2211 430 = 0x9b485570d8 :=
  block_append (B := 3335) (J := 706) (start := 2211) (next := 2426)
    (a := 215) (b := 215) (n := 430) (x := 0x4cb29f30b8) (y := 0x4e95b64020) (z := 0x9b485570d8)
    p3335_706_2211 p3335_706_2426 rfl rfl rfl

private theorem s3335_706_1996_645 : blockEstimate 3335 706 1996 645 = 0xe2d23fe8fe :=
  block_append (B := 3335) (J := 706) (start := 1996) (next := 2211)
    (a := 215) (b := 430) (n := 645) (x := 0x4789ea7826) (y := 0x9b485570d8) (z := 0xe2d23fe8fe)
    p3335_706_1996 s3335_706_2211_430 rfl rfl rfl

private theorem s3335_706_1566_1075 : blockEstimate 3335 706 1566 1075 = 0x15555800aec :=
  block_append (B := 3335) (J := 706) (start := 1566) (next := 1996)
    (a := 430) (b := 645) (n := 1075) (x := 0x72834021ee) (y := 0xe2d23fe8fe) (z := 0x15555800aec)
    s3335_706_1566_430 s3335_706_1996_645 rfl rfl rfl

private theorem s3335_706_706_1935 : blockEstimate 3335 706 706 1935 = 0x1979f8cc7af :=
  block_append (B := 3335) (J := 706) (start := 706) (next := 1566)
    (a := 860) (b := 1075) (n := 1935) (x := 0x424a0cbcc3) (y := 0x15555800aec) (z := 0x1979f8cc7af)
    s3335_706_706_860 s3335_706_1566_1075 rfl rfl rfl

private theorem s3335_706_2641_430 : blockEstimate 3335 706 2641 430 = 0x95be3b09d0 :=
  block_append (B := 3335) (J := 706) (start := 2641) (next := 2856)
    (a := 215) (b := 215) (n := 430) (x := 0x4d332fa65e) (y := 0x488b0b6372) (z := 0x95be3b09d0)
    p3335_706_2641 p3335_706_2856 rfl rfl rfl

private theorem s3335_706_3286_430 : blockEstimate 3335 706 3286 430 = 0x5edf261dda :=
  block_append (B := 3335) (J := 706) (start := 3286) (next := 3501)
    (a := 215) (b := 215) (n := 430) (x := 0x359a36b34a) (y := 0x2944ef6a90) (z := 0x5edf261dda)
    p3335_706_3286 p3335_706_3501 rfl rfl rfl

private theorem s3335_706_3071_645 : blockEstimate 3335 706 3071 645 = 0x9f7c6f9536 :=
  block_append (B := 3335) (J := 706) (start := 3071) (next := 3286)
    (a := 215) (b := 430) (n := 645) (x := 0x409d49775c) (y := 0x5edf261dda) (z := 0x9f7c6f9536)
    p3335_706_3071 s3335_706_3286_430 rfl rfl rfl

private theorem s3335_706_2641_1075 : blockEstimate 3335 706 2641 1075 = 0x1353aaa9f06 :=
  block_append (B := 3335) (J := 706) (start := 2641) (next := 3071)
    (a := 430) (b := 645) (n := 1075) (x := 0x95be3b09d0) (y := 0x9f7c6f9536) (z := 0x1353aaa9f06)
    s3335_706_2641_430 s3335_706_3071_645 rfl rfl rfl

private theorem s3335_706_3716_430 : blockEstimate 3335 706 3716 430 = 0x2f852e4c96 :=
  block_append (B := 3335) (J := 706) (start := 3716) (next := 3931)
    (a := 215) (b := 215) (n := 430) (x := 0x1d346178ba) (y := 0x1250ccd3dc) (z := 0x2f852e4c96)
    p3335_706_3716 p3335_706_3931 rfl rfl rfl

private theorem s3335_706_4361_386 : blockEstimate 3335 706 4361 386 = 0x38fbdb004 :=
  block_append (B := 3335) (J := 706) (start := 4361) (next := 4576)
    (a := 215) (b := 171) (n := 386) (x := 0x33cbe935f) (y := 0x52ff1ca5) (z := 0x38fbdb004)
    p3335_706_4361 p3335_706_4576 rfl rfl rfl

private theorem s3335_706_4146_601 : blockEstimate 3335 706 4146 601 = 0xcf5a5894c :=
  block_append (B := 3335) (J := 706) (start := 4146) (next := 4361)
    (a := 215) (b := 386) (n := 601) (x := 0x965e7d948) (y := 0x38fbdb004) (z := 0xcf5a5894c)
    p3335_706_4146 s3335_706_4361_386 rfl rfl rfl

private theorem s3335_706_3716_1031 : blockEstimate 3335 706 3716 1031 = 0x3c7ad3d5e2 :=
  block_append (B := 3335) (J := 706) (start := 3716) (next := 4146)
    (a := 430) (b := 601) (n := 1031) (x := 0x2f852e4c96) (y := 0xcf5a5894c) (z := 0x3c7ad3d5e2)
    s3335_706_3716_430 s3335_706_4146_601 rfl rfl rfl

private theorem s3335_706_2641_2106 : blockEstimate 3335 706 2641 2106 = 0x171b57e74e8 :=
  block_append (B := 3335) (J := 706) (start := 2641) (next := 3716)
    (a := 1075) (b := 1031) (n := 2106) (x := 0x1353aaa9f06) (y := 0x3c7ad3d5e2) (z := 0x171b57e74e8)
    s3335_706_2641_1075 s3335_706_3716_1031 rfl rfl rfl

private theorem s3335_706_706_4041 : blockEstimate 3335 706 706 4041 = 0x309550b3c97 :=
  block_append (B := 3335) (J := 706) (start := 706) (next := 2641)
    (a := 1935) (b := 2106) (n := 4041) (x := 0x1979f8cc7af) (y := 0x171b57e74e8) (z := 0x309550b3c97)
    s3335_706_706_1935 s3335_706_2641_2106 rfl rfl rfl

theorem moment3335_706 : momentEstimate 3335 706 = 0x309550b3c97 := s3335_706_706_4041

end HighCore82219BankProof
