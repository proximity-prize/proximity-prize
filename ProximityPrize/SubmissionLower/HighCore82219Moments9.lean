import ProximityPrize.SubmissionLower.HighCore82219Moments8

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p3749_788_788 : blockEstimate 3749 788 788 215 = 0x1673f5bde := by decide +kernel
private theorem p3749_788_1003 : blockEstimate 3749 788 1003 215 = 0x93e9db556 := by decide +kernel
private theorem p3749_788_1218 : blockEstimate 3749 788 1218 215 = 0x1784c84bd2 := by decide +kernel
private theorem p3749_788_1433 : blockEstimate 3749 788 1433 215 = 0x2ab0e31eb9 := by decide +kernel
private theorem p3749_788_1648 : blockEstimate 3749 788 1648 215 = 0x3eeb09ef28 := by decide +kernel
private theorem p3749_788_1863 : blockEstimate 3749 788 1863 215 = 0x4fd790f7f5 := by decide +kernel
private theorem p3749_788_2078 : blockEstimate 3749 788 2078 215 = 0x5d1d54241c := by decide +kernel
private theorem p3749_788_2293 : blockEstimate 3749 788 2293 215 = 0x66bc53739d := by decide +kernel
private theorem p3749_788_2508 : blockEstimate 3749 788 2508 215 = 0x6cb48ee678 := by decide +kernel
private theorem p3749_788_2723 : blockEstimate 3749 788 2723 215 = 0x6f06067cad := by decide +kernel
private theorem p3749_788_2938 : blockEstimate 3749 788 2938 215 = 0x6db0ba363c := by decide +kernel
private theorem p3749_788_3153 : blockEstimate 3749 788 3153 215 = 0x68b4aa1325 := by decide +kernel
private theorem p3749_788_3368 : blockEstimate 3749 788 3368 215 = 0x6011d61368 := by decide +kernel
private theorem p3749_788_3583 : blockEstimate 3749 788 3583 215 = 0x53c9958879 := by decide +kernel
private theorem p3749_788_3798 : blockEstimate 3749 788 3798 215 = 0x44b8f4c78f := by decide +kernel
private theorem p3749_788_4013 : blockEstimate 3749 788 4013 215 = 0x351f6de478 := by decide +kernel
private theorem p3749_788_4228 : blockEstimate 3749 788 4228 215 = 0x2628344dc0 := by decide +kernel
private theorem p3749_788_4443 : blockEstimate 3749 788 4443 215 = 0x18b18aa05f := by decide +kernel
private theorem p3749_788_4658 : blockEstimate 3749 788 4658 215 = 0xd85386c9f := by decide +kernel
private theorem p3749_788_4873 : blockEstimate 3749 788 4873 215 = 0x571bfcbaa := by decide +kernel
private theorem p3749_788_5088 : blockEstimate 3749 788 5088 215 = 0xf4f0232d := by decide +kernel
private theorem p3749_788_5303 : blockEstimate 3749 788 5303 22 = 0x3d8219 := by decide +kernel

private theorem s3749_788_788_430 : blockEstimate 3749 788 788 430 = 0xaa5dd1134 :=
  block_append (B := 3749) (J := 788) (start := 788) (next := 1003)
    (a := 215) (b := 215) (n := 430) (x := 0x1673f5bde) (y := 0x93e9db556) (z := 0xaa5dd1134)
    p3749_788_788 p3749_788_1003 rfl rfl rfl

private theorem s3749_788_1433_430 : blockEstimate 3749 788 1433 430 = 0x699bed0de1 :=
  block_append (B := 3749) (J := 788) (start := 1433) (next := 1648)
    (a := 215) (b := 215) (n := 430) (x := 0x2ab0e31eb9) (y := 0x3eeb09ef28) (z := 0x699bed0de1)
    p3749_788_1433 p3749_788_1648 rfl rfl rfl

private theorem s3749_788_1218_645 : blockEstimate 3749 788 1218 645 = 0x8120b559b3 :=
  block_append (B := 3749) (J := 788) (start := 1218) (next := 1433)
    (a := 215) (b := 430) (n := 645) (x := 0x1784c84bd2) (y := 0x699bed0de1) (z := 0x8120b559b3)
    p3749_788_1218 s3749_788_1433_430 rfl rfl rfl

private theorem s3749_788_788_1075 : blockEstimate 3749 788 788 1075 = 0x8bc6926ae7 :=
  block_append (B := 3749) (J := 788) (start := 788) (next := 1218)
    (a := 430) (b := 645) (n := 1075) (x := 0xaa5dd1134) (y := 0x8120b559b3) (z := 0x8bc6926ae7)
    s3749_788_788_430 s3749_788_1218_645 rfl rfl rfl

private theorem s3749_788_2078_430 : blockEstimate 3749 788 2078 430 = 0xc3d9a797b9 :=
  block_append (B := 3749) (J := 788) (start := 2078) (next := 2293)
    (a := 215) (b := 215) (n := 430) (x := 0x5d1d54241c) (y := 0x66bc53739d) (z := 0xc3d9a797b9)
    p3749_788_2078 p3749_788_2293 rfl rfl rfl

private theorem s3749_788_1863_645 : blockEstimate 3749 788 1863 645 = 0x113b1388fae :=
  block_append (B := 3749) (J := 788) (start := 1863) (next := 2078)
    (a := 215) (b := 430) (n := 645) (x := 0x4fd790f7f5) (y := 0xc3d9a797b9) (z := 0x113b1388fae)
    p3749_788_1863 s3749_788_2078_430 rfl rfl rfl

private theorem s3749_788_2723_430 : blockEstimate 3749 788 2723 430 = 0xdcb6c0b2e9 :=
  block_append (B := 3749) (J := 788) (start := 2723) (next := 2938)
    (a := 215) (b := 215) (n := 430) (x := 0x6f06067cad) (y := 0x6db0ba363c) (z := 0xdcb6c0b2e9)
    p3749_788_2723 p3749_788_2938 rfl rfl rfl

private theorem s3749_788_2508_645 : blockEstimate 3749 788 2508 645 = 0x1496b4f9961 :=
  block_append (B := 3749) (J := 788) (start := 2508) (next := 2723)
    (a := 215) (b := 430) (n := 645) (x := 0x6cb48ee678) (y := 0xdcb6c0b2e9) (z := 0x1496b4f9961)
    p3749_788_2508 s3749_788_2723_430 rfl rfl rfl

private theorem s3749_788_1863_1290 : blockEstimate 3749 788 1863 1290 = 0x25d1c88290f :=
  block_append (B := 3749) (J := 788) (start := 1863) (next := 2508)
    (a := 645) (b := 645) (n := 1290) (x := 0x113b1388fae) (y := 0x1496b4f9961) (z := 0x25d1c88290f)
    s3749_788_1863_645 s3749_788_2508_645 rfl rfl rfl

private theorem s3749_788_788_2365 : blockEstimate 3749 788 788 2365 = 0x2e8e31a93f6 :=
  block_append (B := 3749) (J := 788) (start := 788) (next := 1863)
    (a := 1075) (b := 1290) (n := 2365) (x := 0x8bc6926ae7) (y := 0x25d1c88290f) (z := 0x2e8e31a93f6)
    s3749_788_788_1075 s3749_788_1863_1290 rfl rfl rfl

private theorem s3749_788_3153_430 : blockEstimate 3749 788 3153 430 = 0xc8c680268d :=
  block_append (B := 3749) (J := 788) (start := 3153) (next := 3368)
    (a := 215) (b := 215) (n := 430) (x := 0x68b4aa1325) (y := 0x6011d61368) (z := 0xc8c680268d)
    p3749_788_3153 p3749_788_3368 rfl rfl rfl

private theorem s3749_788_3798_430 : blockEstimate 3749 788 3798 430 = 0x79d862ac07 :=
  block_append (B := 3749) (J := 788) (start := 3798) (next := 4013)
    (a := 215) (b := 215) (n := 430) (x := 0x44b8f4c78f) (y := 0x351f6de478) (z := 0x79d862ac07)
    p3749_788_3798 p3749_788_4013 rfl rfl rfl

private theorem s3749_788_3583_645 : blockEstimate 3749 788 3583 645 = 0xcda1f83480 :=
  block_append (B := 3749) (J := 788) (start := 3583) (next := 3798)
    (a := 215) (b := 430) (n := 645) (x := 0x53c9958879) (y := 0x79d862ac07) (z := 0xcda1f83480)
    p3749_788_3583 s3749_788_3798_430 rfl rfl rfl

private theorem s3749_788_3153_1075 : blockEstimate 3749 788 3153 1075 = 0x19668785b0d :=
  block_append (B := 3749) (J := 788) (start := 3153) (next := 3583)
    (a := 430) (b := 645) (n := 1075) (x := 0xc8c680268d) (y := 0xcda1f83480) (z := 0x19668785b0d)
    s3749_788_3153_430 s3749_788_3583_645 rfl rfl rfl

private theorem s3749_788_4443_430 : blockEstimate 3749 788 4443 430 = 0x2636c30cfe :=
  block_append (B := 3749) (J := 788) (start := 4443) (next := 4658)
    (a := 215) (b := 215) (n := 430) (x := 0x18b18aa05f) (y := 0xd85386c9f) (z := 0x2636c30cfe)
    p3749_788_4443 p3749_788_4658 rfl rfl rfl

private theorem s3749_788_4228_645 : blockEstimate 3749 788 4228 645 = 0x4c5ef75abe :=
  block_append (B := 3749) (J := 788) (start := 4228) (next := 4443)
    (a := 215) (b := 430) (n := 645) (x := 0x2628344dc0) (y := 0x2636c30cfe) (z := 0x4c5ef75abe)
    p3749_788_4228 s3749_788_4443_430 rfl rfl rfl

private theorem s3749_788_5088_237 : blockEstimate 3749 788 5088 237 = 0xf52da546 :=
  block_append (B := 3749) (J := 788) (start := 5088) (next := 5303)
    (a := 215) (b := 22) (n := 237) (x := 0xf4f0232d) (y := 0x3d8219) (z := 0xf52da546)
    p3749_788_5088 p3749_788_5303 rfl rfl rfl

private theorem s3749_788_4873_452 : blockEstimate 3749 788 4873 452 = 0x666ed70f0 :=
  block_append (B := 3749) (J := 788) (start := 4873) (next := 5088)
    (a := 215) (b := 237) (n := 452) (x := 0x571bfcbaa) (y := 0xf52da546) (z := 0x666ed70f0)
    p3749_788_4873 s3749_788_5088_237 rfl rfl rfl

private theorem s3749_788_4228_1097 : blockEstimate 3749 788 4228 1097 = 0x52c5e4cbae :=
  block_append (B := 3749) (J := 788) (start := 4228) (next := 4873)
    (a := 645) (b := 452) (n := 1097) (x := 0x4c5ef75abe) (y := 0x666ed70f0) (z := 0x52c5e4cbae)
    s3749_788_4228_645 s3749_788_4873_452 rfl rfl rfl

private theorem s3749_788_3153_2172 : blockEstimate 3749 788 3153 2172 = 0x1e92e5d26bb :=
  block_append (B := 3749) (J := 788) (start := 3153) (next := 4228)
    (a := 1075) (b := 1097) (n := 2172) (x := 0x19668785b0d) (y := 0x52c5e4cbae) (z := 0x1e92e5d26bb)
    s3749_788_3153_1075 s3749_788_4228_1097 rfl rfl rfl

private theorem s3749_788_788_4537 : blockEstimate 3749 788 788 4537 = 0x4d21177bab1 :=
  block_append (B := 3749) (J := 788) (start := 788) (next := 3153)
    (a := 2365) (b := 2172) (n := 4537) (x := 0x2e8e31a93f6) (y := 0x1e92e5d26bb) (z := 0x4d21177bab1)
    s3749_788_788_2365 s3749_788_3153_2172 rfl rfl rfl

theorem moment3749_788 : momentEstimate 3749 788 = 0x4d21177bab1 := s3749_788_788_4537

end HighCore82219BankProof
