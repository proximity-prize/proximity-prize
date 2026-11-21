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
  block_append p2994_634_634 p2994_634_849 rfl rfl rfl

private theorem s2994_634_1064_430 : blockEstimate 2994 634 1064 430 = 0x30ea76b73e :=
  block_append p2994_634_1064 p2994_634_1279 rfl rfl rfl

private theorem s2994_634_634_860 : blockEstimate 2994 634 634 860 = 0x3937d68542 :=
  block_append s2994_634_634_430 s2994_634_1064_430 rfl rfl rfl

private theorem s2994_634_1494_430 : blockEstimate 2994 634 1494 430 = 0x5b94bc6755 :=
  block_append p2994_634_1494 p2994_634_1709 rfl rfl rfl

private theorem s2994_634_1924_430 : blockEstimate 2994 634 1924 430 = 0x6f9078cc79 :=
  block_append p2994_634_1924 p2994_634_2139 rfl rfl rfl

private theorem s2994_634_1494_860 : blockEstimate 2994 634 1494 860 = 0xcb253533ce :=
  block_append s2994_634_1494_430 s2994_634_1924_430 rfl rfl rfl

private theorem s2994_634_634_1720 : blockEstimate 2994 634 634 1720 = 0x1045d0bb910 :=
  block_append s2994_634_634_860 s2994_634_1494_860 rfl rfl rfl

private theorem s2994_634_2354_430 : blockEstimate 2994 634 2354 430 = 0x6c09b1e7cd :=
  block_append p2994_634_2354 p2994_634_2569 rfl rfl rfl

private theorem s2994_634_2784_430 : blockEstimate 2994 634 2784 430 = 0x5169303dc6 :=
  block_append p2994_634_2784 p2994_634_2999 rfl rfl rfl

private theorem s2994_634_2354_860 : blockEstimate 2994 634 2354 860 = 0xbd72e22593 :=
  block_append s2994_634_2354_430 s2994_634_2784_430 rfl rfl rfl

private theorem s2994_634_3214_430 : blockEstimate 2994 634 3214 430 = 0x2ae7147d66 :=
  block_append p2994_634_3214 p2994_634_3429 rfl rfl rfl

private theorem s2994_634_3859_403 : blockEstimate 2994 634 3859 403 = 0x39a5c69d0 :=
  block_append p2994_634_3859 p2994_634_4074 rfl rfl rfl

private theorem s2994_634_3644_618 : blockEstimate 2994 634 3644 618 = 0xc7a5f0cc2 :=
  block_append p2994_634_3644 s2994_634_3859_403 rfl rfl rfl

private theorem s2994_634_3214_1048 : blockEstimate 2994 634 3214 1048 = 0x3761738a28 :=
  block_append s2994_634_3214_430 s2994_634_3644_618 rfl rfl rfl

private theorem s2994_634_2354_1908 : blockEstimate 2994 634 2354 1908 = 0xf4d455afbb :=
  block_append s2994_634_2354_860 s2994_634_3214_1048 rfl rfl rfl

private theorem s2994_634_634_3628 : blockEstimate 2994 634 634 3628 = 0x1f9316168cb :=
  block_append s2994_634_634_1720 s2994_634_2354_1908 rfl rfl rfl

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
  block_append p3335_706_706 p3335_706_921 rfl rfl rfl

private theorem s3335_706_1136_430 : blockEstimate 3335 706 1136 430 = 0x38ed760d6f :=
  block_append p3335_706_1136 p3335_706_1351 rfl rfl rfl

private theorem s3335_706_706_860 : blockEstimate 3335 706 706 860 = 0x424a0cbcc3 :=
  block_append s3335_706_706_430 s3335_706_1136_430 rfl rfl rfl

private theorem s3335_706_1566_430 : blockEstimate 3335 706 1566 430 = 0x72834021ee :=
  block_append p3335_706_1566 p3335_706_1781 rfl rfl rfl

private theorem s3335_706_2211_430 : blockEstimate 3335 706 2211 430 = 0x9b485570d8 :=
  block_append p3335_706_2211 p3335_706_2426 rfl rfl rfl

private theorem s3335_706_1996_645 : blockEstimate 3335 706 1996 645 = 0xe2d23fe8fe :=
  block_append p3335_706_1996 s3335_706_2211_430 rfl rfl rfl

private theorem s3335_706_1566_1075 : blockEstimate 3335 706 1566 1075 = 0x15555800aec :=
  block_append s3335_706_1566_430 s3335_706_1996_645 rfl rfl rfl

private theorem s3335_706_706_1935 : blockEstimate 3335 706 706 1935 = 0x1979f8cc7af :=
  block_append s3335_706_706_860 s3335_706_1566_1075 rfl rfl rfl

private theorem s3335_706_2641_430 : blockEstimate 3335 706 2641 430 = 0x95be3b09d0 :=
  block_append p3335_706_2641 p3335_706_2856 rfl rfl rfl

private theorem s3335_706_3286_430 : blockEstimate 3335 706 3286 430 = 0x5edf261dda :=
  block_append p3335_706_3286 p3335_706_3501 rfl rfl rfl

private theorem s3335_706_3071_645 : blockEstimate 3335 706 3071 645 = 0x9f7c6f9536 :=
  block_append p3335_706_3071 s3335_706_3286_430 rfl rfl rfl

private theorem s3335_706_2641_1075 : blockEstimate 3335 706 2641 1075 = 0x1353aaa9f06 :=
  block_append s3335_706_2641_430 s3335_706_3071_645 rfl rfl rfl

private theorem s3335_706_3716_430 : blockEstimate 3335 706 3716 430 = 0x2f852e4c96 :=
  block_append p3335_706_3716 p3335_706_3931 rfl rfl rfl

private theorem s3335_706_4361_386 : blockEstimate 3335 706 4361 386 = 0x38fbdb004 :=
  block_append p3335_706_4361 p3335_706_4576 rfl rfl rfl

private theorem s3335_706_4146_601 : blockEstimate 3335 706 4146 601 = 0xcf5a5894c :=
  block_append p3335_706_4146 s3335_706_4361_386 rfl rfl rfl

private theorem s3335_706_3716_1031 : blockEstimate 3335 706 3716 1031 = 0x3c7ad3d5e2 :=
  block_append s3335_706_3716_430 s3335_706_4146_601 rfl rfl rfl

private theorem s3335_706_2641_2106 : blockEstimate 3335 706 2641 2106 = 0x171b57e74e8 :=
  block_append s3335_706_2641_1075 s3335_706_3716_1031 rfl rfl rfl

private theorem s3335_706_706_4041 : blockEstimate 3335 706 706 4041 = 0x309550b3c97 :=
  block_append s3335_706_706_1935 s3335_706_2641_2106 rfl rfl rfl

theorem moment3335_706 : momentEstimate 3335 706 = 0x309550b3c97 := s3335_706_706_4041

end HighCore82219BankProof
