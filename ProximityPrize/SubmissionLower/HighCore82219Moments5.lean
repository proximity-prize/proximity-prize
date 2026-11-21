import ProximityPrize.SubmissionLower.HighCore82219Moments4

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p2105_443_443 : blockEstimate 2105 443 443 215 = 0xc2aa570e := by decide +kernel
private theorem p2105_443_658 : blockEstimate 2105 443 658 215 = 0x4c7a48366 := by decide +kernel
private theorem p2105_443_873 : blockEstimate 2105 443 873 215 = 0xaf1d63b4b := by decide +kernel
private theorem p2105_443_1088 : blockEstimate 2105 443 1088 215 = 0xfe5c5811e := by decide +kernel
private theorem p2105_443_1303 : blockEstimate 2105 443 1303 215 = 0x12cbb70664 := by decide +kernel
private theorem p2105_443_1518 : blockEstimate 2105 443 1518 215 = 0x13a3a18162 := by decide +kernel
private theorem p2105_443_1733 : blockEstimate 2105 443 1733 215 = 0x126d84f218 := by decide +kernel
private theorem p2105_443_1948 : blockEstimate 2105 443 1948 215 = 0xf2aa7f3c1 := by decide +kernel
private theorem p2105_443_2163 : blockEstimate 2105 443 2163 215 = 0xa6fbceeb9 := by decide +kernel
private theorem p2105_443_2378 : blockEstimate 2105 443 2378 215 = 0x5c54d4350 := by decide +kernel
private theorem p2105_443_2593 : blockEstimate 2105 443 2593 215 = 0x220c4cd7e := by decide +kernel
private theorem p2105_443_2808 : blockEstimate 2105 443 2808 183 = 0x3f01f064 := by decide +kernel

private theorem s2105_443_658_430 : blockEstimate 2105 443 658 430 = 0xfb97abeb1 :=
  block_append p2105_443_658 p2105_443_873 rfl rfl rfl

private theorem s2105_443_443_645 : blockEstimate 2105 443 443 645 = 0x107c2515bf :=
  block_append p2105_443_443 s2105_443_658_430 rfl rfl rfl

private theorem s2105_443_1303_430 : blockEstimate 2105 443 1303 430 = 0x266f5887c6 :=
  block_append p2105_443_1303 p2105_443_1518 rfl rfl rfl

private theorem s2105_443_1088_645 : blockEstimate 2105 443 1088 645 = 0x36551e08e4 :=
  block_append p2105_443_1088 s2105_443_1303_430 rfl rfl rfl

private theorem s2105_443_443_1290 : blockEstimate 2105 443 443 1290 = 0x46d1431ea3 :=
  block_append s2105_443_443_645 s2105_443_1088_645 rfl rfl rfl

private theorem s2105_443_1948_430 : blockEstimate 2105 443 1948 430 = 0x199a64e27a :=
  block_append p2105_443_1948 p2105_443_2163 rfl rfl rfl

private theorem s2105_443_1733_645 : blockEstimate 2105 443 1733 645 = 0x2c07e9d492 :=
  block_append p2105_443_1733 s2105_443_1948_430 rfl rfl rfl

private theorem s2105_443_2593_398 : blockEstimate 2105 443 2593 398 = 0x25fc6bde2 :=
  block_append p2105_443_2593 p2105_443_2808 rfl rfl rfl

private theorem s2105_443_2378_613 : blockEstimate 2105 443 2378 613 = 0x825140132 :=
  block_append p2105_443_2378 s2105_443_2593_398 rfl rfl rfl

private theorem s2105_443_1733_1258 : blockEstimate 2105 443 1733 1258 = 0x342cfdd5c4 :=
  block_append s2105_443_1733_645 s2105_443_2378_613 rfl rfl rfl

private theorem s2105_443_443_2548 : blockEstimate 2105 443 443 2548 = 0x7afe40f467 :=
  block_append s2105_443_443_1290 s2105_443_1733_1258 rfl rfl rfl

theorem moment2105_443 : momentEstimate 2105 443 = 0x7afe40f467 := s2105_443_443_2548

private theorem p2518_553_553 : blockEstimate 2518 553 553 215 = 0xec02d9fa := by decide +kernel
private theorem p2518_553_768 : blockEstimate 2518 553 768 215 = 0x5e6c6c64a := by decide +kernel
private theorem p2518_553_983 : blockEstimate 2518 553 983 215 = 0xe687592d2 := by decide +kernel
private theorem p2518_553_1198 : blockEstimate 2518 553 1198 215 = 0x173ae1f31a := by decide +kernel
private theorem p2518_553_1413 : blockEstimate 2518 553 1413 215 = 0x1da2fe5573 := by decide +kernel
private theorem p2518_553_1628 : blockEstimate 2518 553 1628 215 = 0x217ac13680 := by decide +kernel
private theorem p2518_553_1843 : blockEstimate 2518 553 1843 215 = 0x22c22a9641 := by decide +kernel
private theorem p2518_553_2058 : blockEstimate 2518 553 2058 215 = 0x21793a74b6 := by decide +kernel
private theorem p2518_553_2273 : blockEstimate 2518 553 2273 215 = 0x1d9ff0d1df := by decide +kernel
private theorem p2518_553_2488 : blockEstimate 2518 553 2488 215 = 0x1769856506 := by decide +kernel
private theorem p2518_553_2703 : blockEstimate 2518 553 2703 215 = 0x105451ace8 := by decide +kernel
private theorem p2518_553_2918 : blockEstimate 2518 553 2918 215 = 0x9af3b894b := by decide +kernel
private theorem p2518_553_3133 : blockEstimate 2518 553 3133 215 = 0x4504d41cb := by decide +kernel
private theorem p2518_553_3348 : blockEstimate 2518 553 3348 215 = 0xfa94ae09 := by decide +kernel
private theorem p2518_553_3563 : blockEstimate 2518 553 3563 61 = 0x304acb8 := by decide +kernel

private theorem s2518_553_768_430 : blockEstimate 2518 553 768 430 = 0x144f3c591c :=
  block_append p2518_553_768 p2518_553_983 rfl rfl rfl

private theorem s2518_553_553_645 : blockEstimate 2518 553 553 645 = 0x153b3f3316 :=
  block_append p2518_553_553 s2518_553_768_430 rfl rfl rfl

private theorem s2518_553_1198_430 : blockEstimate 2518 553 1198 430 = 0x34dde0488d :=
  block_append p2518_553_1198 p2518_553_1413 rfl rfl rfl

private theorem s2518_553_1628_430 : blockEstimate 2518 553 1628 430 = 0x443cebccc1 :=
  block_append p2518_553_1628 p2518_553_1843 rfl rfl rfl

private theorem s2518_553_1198_860 : blockEstimate 2518 553 1198 860 = 0x791acc154e :=
  block_append s2518_553_1198_430 s2518_553_1628_430 rfl rfl rfl

private theorem s2518_553_553_1505 : blockEstimate 2518 553 553 1505 = 0x8e560b4864 :=
  block_append s2518_553_553_645 s2518_553_1198_860 rfl rfl rfl

private theorem s2518_553_2058_430 : blockEstimate 2518 553 2058 430 = 0x3f192b4695 :=
  block_append p2518_553_2058 p2518_553_2273 rfl rfl rfl

private theorem s2518_553_2488_430 : blockEstimate 2518 553 2488 430 = 0x27bdd711ee :=
  block_append p2518_553_2488 p2518_553_2703 rfl rfl rfl

private theorem s2518_553_2058_860 : blockEstimate 2518 553 2058 860 = 0x66d7025883 :=
  block_append s2518_553_2058_430 s2518_553_2488_430 rfl rfl rfl

private theorem s2518_553_2918_430 : blockEstimate 2518 553 2918 430 = 0xdff88cb16 :=
  block_append p2518_553_2918 p2518_553_3133 rfl rfl rfl

private theorem s2518_553_3348_276 : blockEstimate 2518 553 3348 276 = 0xfd995ac1 :=
  block_append p2518_553_3348 p2518_553_3563 rfl rfl rfl

private theorem s2518_553_2918_706 : blockEstimate 2518 553 2918 706 = 0xefd2225d7 :=
  block_append s2518_553_2918_430 s2518_553_3348_276 rfl rfl rfl

private theorem s2518_553_2058_1566 : blockEstimate 2518 553 2058 1566 = 0x75d4247e5a :=
  block_append s2518_553_2058_860 s2518_553_2918_706 rfl rfl rfl

private theorem s2518_553_553_3071 : blockEstimate 2518 553 553 3071 = 0x1042a2fc6be :=
  block_append s2518_553_553_1505 s2518_553_2058_1566 rfl rfl rfl

theorem moment2518_553 : momentEstimate 2518 553 = 0x1042a2fc6be := s2518_553_553_3071

end HighCore82219BankProof
