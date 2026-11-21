import ProximityPrize.SubmissionLower.HighCore82219Moments10

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p5969_1261_1261 : blockEstimate 5969 1261 1261 215 = 0x2457e4fae := by decide +kernel
private theorem p5969_1261_1476 : blockEstimate 5969 1261 1476 215 = 0xf460c1c46 := by decide +kernel
private theorem p5969_1261_1691 : blockEstimate 5969 1261 1691 215 = 0x27d877bf96 := by decide +kernel
private theorem p5969_1261_1906 : blockEstimate 5969 1261 1906 215 = 0x4a7eac8b3b := by decide +kernel
private theorem p5969_1261_2121 : blockEstimate 5969 1261 2121 215 = 0x75ba95d0d2 := by decide +kernel
private theorem p5969_1261_2336 : blockEstimate 5969 1261 2336 215 = 0xa80cfc890b := by decide +kernel
private theorem p5969_1261_2551 : blockEstimate 5969 1261 2551 215 = 0xdd6f444f4c := by decide +kernel
private theorem p5969_1261_2766 : blockEstimate 5969 1261 2766 215 = 0x10e304b52b9 := by decide +kernel
private theorem p5969_1261_2981 : blockEstimate 5969 1261 2981 215 = 0x1391a2be022 := by decide +kernel
private theorem p5969_1261_3196 : blockEstimate 5969 1261 3196 215 = 0x15e2ce5f787 := by decide +kernel
private theorem p5969_1261_3411 : blockEstimate 5969 1261 3411 215 = 0x17d687998e8 := by decide +kernel
private theorem p5969_1261_3626 : blockEstimate 5969 1261 3626 215 = 0x196cce6c445 := by decide +kernel
private theorem p5969_1261_3841 : blockEstimate 5969 1261 3841 215 = 0x1aa5a2d799e := by decide +kernel
private theorem p5969_1261_4056 : blockEstimate 5969 1261 4056 215 = 0x1b8104db8f3 := by decide +kernel
private theorem p5969_1261_4271 : blockEstimate 5969 1261 4271 215 = 0x1bfef478244 := by decide +kernel
private theorem p5969_1261_4486 : blockEstimate 5969 1261 4486 215 = 0x1c1f71ad591 := by decide +kernel
private theorem p5969_1261_4701 : blockEstimate 5969 1261 4701 215 = 0x1be27c7b2da := by decide +kernel
private theorem p5969_1261_4916 : blockEstimate 5969 1261 4916 215 = 0x1b4814e1a1f := by decide +kernel
private theorem p5969_1261_5131 : blockEstimate 5969 1261 5131 215 = 0x1a503ae0b60 := by decide +kernel
private theorem p5969_1261_5346 : blockEstimate 5969 1261 5346 215 = 0x18faee7869d := by decide +kernel
private theorem p5969_1261_5561 : blockEstimate 5969 1261 5561 215 = 0x17482fa8bd6 := by decide +kernel
private theorem p5969_1261_5776 : blockEstimate 5969 1261 5776 215 = 0x153801936ad := by decide +kernel
private theorem p5969_1261_5991 : blockEstimate 5969 1261 5991 215 = 0x12d9c5c8b1b := by decide +kernel
private theorem p5969_1261_6206 : blockEstimate 5969 1261 6206 215 = 0x106142f53d7 := by decide +kernel
private theorem p5969_1261_6421 : blockEstimate 5969 1261 6421 215 = 0xde66828428 := by decide +kernel
private theorem p5969_1261_6636 : blockEstimate 5969 1261 6636 215 = 0xb78fa5cde2 := by decide +kernel
private theorem p5969_1261_6851 : blockEstimate 5969 1261 6851 215 = 0x927ba2d03e := by decide +kernel
private theorem p5969_1261_7066 : blockEstimate 5969 1261 7066 215 = 0x70029b0631 := by decide +kernel
private theorem p5969_1261_7281 : blockEstimate 5969 1261 7281 215 = 0x50bad578be := by decide +kernel
private theorem p5969_1261_7496 : blockEstimate 5969 1261 7496 215 = 0x35c33205a5 := by decide +kernel
private theorem p5969_1261_7711 : blockEstimate 5969 1261 7711 215 = 0x1fc6322f5f := by decide +kernel
private theorem p5969_1261_7926 : blockEstimate 5969 1261 7926 215 = 0xf3b3c81a9 := by decide +kernel
private theorem p5969_1261_8141 : blockEstimate 5969 1261 8141 215 = 0x499b75db0 := by decide +kernel
private theorem p5969_1261_8356 : blockEstimate 5969 1261 8356 135 = 0x4a9b520c := by decide +kernel

private theorem s5969_1261_1261_430 : blockEstimate 5969 1261 1261 430 = 0x118b8a6bf4 :=
  block_append (B := 5969) (J := 1261) (start := 1261) (next := 1476)
    (a := 215) (b := 215) (n := 430) (x := 0x2457e4fae) (y := 0xf460c1c46) (z := 0x118b8a6bf4)
    p5969_1261_1261 p5969_1261_1476 rfl rfl rfl

private theorem s5969_1261_1691_430 : blockEstimate 5969 1261 1691 430 = 0x7257244ad1 :=
  block_append (B := 5969) (J := 1261) (start := 1691) (next := 1906)
    (a := 215) (b := 215) (n := 430) (x := 0x27d877bf96) (y := 0x4a7eac8b3b) (z := 0x7257244ad1)
    p5969_1261_1691 p5969_1261_1906 rfl rfl rfl

private theorem s5969_1261_1261_860 : blockEstimate 5969 1261 1261 860 = 0x83e2aeb6c5 :=
  block_append (B := 5969) (J := 1261) (start := 1261) (next := 1691)
    (a := 430) (b := 430) (n := 860) (x := 0x118b8a6bf4) (y := 0x7257244ad1) (z := 0x83e2aeb6c5)
    s5969_1261_1261_430 s5969_1261_1691_430 rfl rfl rfl

private theorem s5969_1261_2121_430 : blockEstimate 5969 1261 2121 430 = 0x11dc79259dd :=
  block_append (B := 5969) (J := 1261) (start := 2121) (next := 2336)
    (a := 215) (b := 215) (n := 430) (x := 0x75ba95d0d2) (y := 0xa80cfc890b) (z := 0x11dc79259dd)
    p5969_1261_2121 p5969_1261_2336 rfl rfl rfl

private theorem s5969_1261_2551_430 : blockEstimate 5969 1261 2551 430 = 0x1eb9f8fa205 :=
  block_append (B := 5969) (J := 1261) (start := 2551) (next := 2766)
    (a := 215) (b := 215) (n := 430) (x := 0xdd6f444f4c) (y := 0x10e304b52b9) (z := 0x1eb9f8fa205)
    p5969_1261_2551 p5969_1261_2766 rfl rfl rfl

private theorem s5969_1261_2121_860 : blockEstimate 5969 1261 2121 860 = 0x3096721fbe2 :=
  block_append (B := 5969) (J := 1261) (start := 2121) (next := 2551)
    (a := 430) (b := 430) (n := 860) (x := 0x11dc79259dd) (y := 0x1eb9f8fa205) (z := 0x3096721fbe2)
    s5969_1261_2121_430 s5969_1261_2551_430 rfl rfl rfl

private theorem s5969_1261_1261_1720 : blockEstimate 5969 1261 1261 1720 = 0x38d49d0b2a7 :=
  block_append (B := 5969) (J := 1261) (start := 1261) (next := 2121)
    (a := 860) (b := 860) (n := 1720) (x := 0x83e2aeb6c5) (y := 0x3096721fbe2) (z := 0x38d49d0b2a7)
    s5969_1261_1261_860 s5969_1261_2121_860 rfl rfl rfl

private theorem s5969_1261_2981_430 : blockEstimate 5969 1261 2981 430 = 0x2974711d7a9 :=
  block_append (B := 5969) (J := 1261) (start := 2981) (next := 3196)
    (a := 215) (b := 215) (n := 430) (x := 0x1391a2be022) (y := 0x15e2ce5f787) (z := 0x2974711d7a9)
    p5969_1261_2981 p5969_1261_3196 rfl rfl rfl

private theorem s5969_1261_3411_430 : blockEstimate 5969 1261 3411 430 = 0x31435605d2d :=
  block_append (B := 5969) (J := 1261) (start := 3411) (next := 3626)
    (a := 215) (b := 215) (n := 430) (x := 0x17d687998e8) (y := 0x196cce6c445) (z := 0x31435605d2d)
    p5969_1261_3411 p5969_1261_3626 rfl rfl rfl

private theorem s5969_1261_2981_860 : blockEstimate 5969 1261 2981 860 = 0x5ab7c7234d6 :=
  block_append (B := 5969) (J := 1261) (start := 2981) (next := 3411)
    (a := 430) (b := 430) (n := 860) (x := 0x2974711d7a9) (y := 0x31435605d2d) (z := 0x5ab7c7234d6)
    s5969_1261_2981_430 s5969_1261_3411_430 rfl rfl rfl

private theorem s5969_1261_3841_430 : blockEstimate 5969 1261 3841 430 = 0x3626a7b3291 :=
  block_append (B := 5969) (J := 1261) (start := 3841) (next := 4056)
    (a := 215) (b := 215) (n := 430) (x := 0x1aa5a2d799e) (y := 0x1b8104db8f3) (z := 0x3626a7b3291)
    p5969_1261_3841 p5969_1261_4056 rfl rfl rfl

private theorem s5969_1261_4486_430 : blockEstimate 5969 1261 4486 430 = 0x3801ee2886b :=
  block_append (B := 5969) (J := 1261) (start := 4486) (next := 4701)
    (a := 215) (b := 215) (n := 430) (x := 0x1c1f71ad591) (y := 0x1be27c7b2da) (z := 0x3801ee2886b)
    p5969_1261_4486 p5969_1261_4701 rfl rfl rfl

private theorem s5969_1261_4271_645 : blockEstimate 5969 1261 4271 645 = 0x5400e2a0aaf :=
  block_append (B := 5969) (J := 1261) (start := 4271) (next := 4486)
    (a := 215) (b := 430) (n := 645) (x := 0x1bfef478244) (y := 0x3801ee2886b) (z := 0x5400e2a0aaf)
    p5969_1261_4271 s5969_1261_4486_430 rfl rfl rfl

private theorem s5969_1261_3841_1075 : blockEstimate 5969 1261 3841 1075 = 0x8a278a53d40 :=
  block_append (B := 5969) (J := 1261) (start := 3841) (next := 4271)
    (a := 430) (b := 645) (n := 1075) (x := 0x3626a7b3291) (y := 0x5400e2a0aaf) (z := 0x8a278a53d40)
    s5969_1261_3841_430 s5969_1261_4271_645 rfl rfl rfl

private theorem s5969_1261_2981_1935 : blockEstimate 5969 1261 2981 1935 = 0xe4df5177216 :=
  block_append (B := 5969) (J := 1261) (start := 2981) (next := 3841)
    (a := 860) (b := 1075) (n := 1935) (x := 0x5ab7c7234d6) (y := 0x8a278a53d40) (z := 0xe4df5177216)
    s5969_1261_2981_860 s5969_1261_3841_1075 rfl rfl rfl

private theorem s5969_1261_1261_3655 : blockEstimate 5969 1261 1261 3655 = 0x11db3ee824bd :=
  block_append (B := 5969) (J := 1261) (start := 1261) (next := 2981)
    (a := 1720) (b := 1935) (n := 3655) (x := 0x38d49d0b2a7) (y := 0xe4df5177216) (z := 0x11db3ee824bd)
    s5969_1261_1261_1720 s5969_1261_2981_1935 rfl rfl rfl

private theorem s5969_1261_4916_430 : blockEstimate 5969 1261 4916 430 = 0x35984fc257f :=
  block_append (B := 5969) (J := 1261) (start := 4916) (next := 5131)
    (a := 215) (b := 215) (n := 430) (x := 0x1b4814e1a1f) (y := 0x1a503ae0b60) (z := 0x35984fc257f)
    p5969_1261_4916 p5969_1261_5131 rfl rfl rfl

private theorem s5969_1261_5346_430 : blockEstimate 5969 1261 5346 430 = 0x30431e21273 :=
  block_append (B := 5969) (J := 1261) (start := 5346) (next := 5561)
    (a := 215) (b := 215) (n := 430) (x := 0x18faee7869d) (y := 0x17482fa8bd6) (z := 0x30431e21273)
    p5969_1261_5346 p5969_1261_5561 rfl rfl rfl

private theorem s5969_1261_4916_860 : blockEstimate 5969 1261 4916 860 = 0x65db6de37f2 :=
  block_append (B := 5969) (J := 1261) (start := 4916) (next := 5346)
    (a := 430) (b := 430) (n := 860) (x := 0x35984fc257f) (y := 0x30431e21273) (z := 0x65db6de37f2)
    s5969_1261_4916_430 s5969_1261_5346_430 rfl rfl rfl

private theorem s5969_1261_5776_430 : blockEstimate 5969 1261 5776 430 = 0x2811c75c1c8 :=
  block_append (B := 5969) (J := 1261) (start := 5776) (next := 5991)
    (a := 215) (b := 215) (n := 430) (x := 0x153801936ad) (y := 0x12d9c5c8b1b) (z := 0x2811c75c1c8)
    p5969_1261_5776 p5969_1261_5991 rfl rfl rfl

private theorem s5969_1261_6206_430 : blockEstimate 5969 1261 6206 430 = 0x1e47ab1d7ff :=
  block_append (B := 5969) (J := 1261) (start := 6206) (next := 6421)
    (a := 215) (b := 215) (n := 430) (x := 0x106142f53d7) (y := 0xde66828428) (z := 0x1e47ab1d7ff)
    p5969_1261_6206 p5969_1261_6421 rfl rfl rfl

private theorem s5969_1261_5776_860 : blockEstimate 5969 1261 5776 860 = 0x465972799c7 :=
  block_append (B := 5969) (J := 1261) (start := 5776) (next := 6206)
    (a := 430) (b := 430) (n := 860) (x := 0x2811c75c1c8) (y := 0x1e47ab1d7ff) (z := 0x465972799c7)
    s5969_1261_5776_430 s5969_1261_6206_430 rfl rfl rfl

private theorem s5969_1261_4916_1720 : blockEstimate 5969 1261 4916 1720 = 0xac34e05d1b9 :=
  block_append (B := 5969) (J := 1261) (start := 4916) (next := 5776)
    (a := 860) (b := 860) (n := 1720) (x := 0x65db6de37f2) (y := 0x465972799c7) (z := 0xac34e05d1b9)
    s5969_1261_4916_860 s5969_1261_5776_860 rfl rfl rfl

private theorem s5969_1261_6636_430 : blockEstimate 5969 1261 6636 430 = 0x14a0b489e20 :=
  block_append (B := 5969) (J := 1261) (start := 6636) (next := 6851)
    (a := 215) (b := 215) (n := 430) (x := 0xb78fa5cde2) (y := 0x927ba2d03e) (z := 0x14a0b489e20)
    p5969_1261_6636 p5969_1261_6851 rfl rfl rfl

private theorem s5969_1261_7066_430 : blockEstimate 5969 1261 7066 430 = 0xc0bd707eef :=
  block_append (B := 5969) (J := 1261) (start := 7066) (next := 7281)
    (a := 215) (b := 215) (n := 430) (x := 0x70029b0631) (y := 0x50bad578be) (z := 0xc0bd707eef)
    p5969_1261_7066 p5969_1261_7281 rfl rfl rfl

private theorem s5969_1261_6636_860 : blockEstimate 5969 1261 6636 860 = 0x20ac8b91d0f :=
  block_append (B := 5969) (J := 1261) (start := 6636) (next := 7066)
    (a := 430) (b := 430) (n := 860) (x := 0x14a0b489e20) (y := 0xc0bd707eef) (z := 0x20ac8b91d0f)
    s5969_1261_6636_430 s5969_1261_7066_430 rfl rfl rfl

private theorem s5969_1261_7496_430 : blockEstimate 5969 1261 7496 430 = 0x5589643504 :=
  block_append (B := 5969) (J := 1261) (start := 7496) (next := 7711)
    (a := 215) (b := 215) (n := 430) (x := 0x35c33205a5) (y := 0x1fc6322f5f) (z := 0x5589643504)
    p5969_1261_7496 p5969_1261_7711 rfl rfl rfl

private theorem s5969_1261_8141_350 : blockEstimate 5969 1261 8141 350 = 0x4e452afbc :=
  block_append (B := 5969) (J := 1261) (start := 8141) (next := 8356)
    (a := 215) (b := 135) (n := 350) (x := 0x499b75db0) (y := 0x4a9b520c) (z := 0x4e452afbc)
    p5969_1261_8141 p5969_1261_8356 rfl rfl rfl

private theorem s5969_1261_7926_565 : blockEstimate 5969 1261 7926 565 = 0x141f8f3165 :=
  block_append (B := 5969) (J := 1261) (start := 7926) (next := 8141)
    (a := 215) (b := 350) (n := 565) (x := 0xf3b3c81a9) (y := 0x4e452afbc) (z := 0x141f8f3165)
    p5969_1261_7926 s5969_1261_8141_350 rfl rfl rfl

private theorem s5969_1261_7496_995 : blockEstimate 5969 1261 7496 995 = 0x69a8f36669 :=
  block_append (B := 5969) (J := 1261) (start := 7496) (next := 7926)
    (a := 430) (b := 565) (n := 995) (x := 0x5589643504) (y := 0x141f8f3165) (z := 0x69a8f36669)
    s5969_1261_7496_430 s5969_1261_7926_565 rfl rfl rfl

private theorem s5969_1261_6636_1855 : blockEstimate 5969 1261 6636 1855 = 0x27471ac8378 :=
  block_append (B := 5969) (J := 1261) (start := 6636) (next := 7496)
    (a := 860) (b := 995) (n := 1855) (x := 0x20ac8b91d0f) (y := 0x69a8f36669) (z := 0x27471ac8378)
    s5969_1261_6636_860 s5969_1261_7496_995 rfl rfl rfl

private theorem s5969_1261_4916_3575 : blockEstimate 5969 1261 4916 3575 = 0xd37bfb25531 :=
  block_append (B := 5969) (J := 1261) (start := 4916) (next := 6636)
    (a := 1720) (b := 1855) (n := 3575) (x := 0xac34e05d1b9) (y := 0x27471ac8378) (z := 0xd37bfb25531)
    s5969_1261_4916_1720 s5969_1261_6636_1855 rfl rfl rfl

private theorem s5969_1261_1261_7230 : blockEstimate 5969 1261 1261 7230 = 0x1f12fe9a79ee :=
  block_append (B := 5969) (J := 1261) (start := 1261) (next := 4916)
    (a := 3655) (b := 3575) (n := 7230) (x := 0x11db3ee824bd) (y := 0xd37bfb25531) (z := 0x1f12fe9a79ee)
    s5969_1261_1261_3655 s5969_1261_4916_3575 rfl rfl rfl

theorem moment5969_1261 : momentEstimate 5969 1261 = 0x1f12fe9a79ee := s5969_1261_1261_7230

end HighCore82219BankProof
