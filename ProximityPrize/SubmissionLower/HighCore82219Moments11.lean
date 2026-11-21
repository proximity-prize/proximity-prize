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
  block_append p5969_1261_1261 p5969_1261_1476 rfl rfl rfl

private theorem s5969_1261_1691_430 : blockEstimate 5969 1261 1691 430 = 0x7257244ad1 :=
  block_append p5969_1261_1691 p5969_1261_1906 rfl rfl rfl

private theorem s5969_1261_1261_860 : blockEstimate 5969 1261 1261 860 = 0x83e2aeb6c5 :=
  block_append s5969_1261_1261_430 s5969_1261_1691_430 rfl rfl rfl

private theorem s5969_1261_2121_430 : blockEstimate 5969 1261 2121 430 = 0x11dc79259dd :=
  block_append p5969_1261_2121 p5969_1261_2336 rfl rfl rfl

private theorem s5969_1261_2551_430 : blockEstimate 5969 1261 2551 430 = 0x1eb9f8fa205 :=
  block_append p5969_1261_2551 p5969_1261_2766 rfl rfl rfl

private theorem s5969_1261_2121_860 : blockEstimate 5969 1261 2121 860 = 0x3096721fbe2 :=
  block_append s5969_1261_2121_430 s5969_1261_2551_430 rfl rfl rfl

private theorem s5969_1261_1261_1720 : blockEstimate 5969 1261 1261 1720 = 0x38d49d0b2a7 :=
  block_append s5969_1261_1261_860 s5969_1261_2121_860 rfl rfl rfl

private theorem s5969_1261_2981_430 : blockEstimate 5969 1261 2981 430 = 0x2974711d7a9 :=
  block_append p5969_1261_2981 p5969_1261_3196 rfl rfl rfl

private theorem s5969_1261_3411_430 : blockEstimate 5969 1261 3411 430 = 0x31435605d2d :=
  block_append p5969_1261_3411 p5969_1261_3626 rfl rfl rfl

private theorem s5969_1261_2981_860 : blockEstimate 5969 1261 2981 860 = 0x5ab7c7234d6 :=
  block_append s5969_1261_2981_430 s5969_1261_3411_430 rfl rfl rfl

private theorem s5969_1261_3841_430 : blockEstimate 5969 1261 3841 430 = 0x3626a7b3291 :=
  block_append p5969_1261_3841 p5969_1261_4056 rfl rfl rfl

private theorem s5969_1261_4486_430 : blockEstimate 5969 1261 4486 430 = 0x3801ee2886b :=
  block_append p5969_1261_4486 p5969_1261_4701 rfl rfl rfl

private theorem s5969_1261_4271_645 : blockEstimate 5969 1261 4271 645 = 0x5400e2a0aaf :=
  block_append p5969_1261_4271 s5969_1261_4486_430 rfl rfl rfl

private theorem s5969_1261_3841_1075 : blockEstimate 5969 1261 3841 1075 = 0x8a278a53d40 :=
  block_append s5969_1261_3841_430 s5969_1261_4271_645 rfl rfl rfl

private theorem s5969_1261_2981_1935 : blockEstimate 5969 1261 2981 1935 = 0xe4df5177216 :=
  block_append s5969_1261_2981_860 s5969_1261_3841_1075 rfl rfl rfl

private theorem s5969_1261_1261_3655 : blockEstimate 5969 1261 1261 3655 = 0x11db3ee824bd :=
  block_append s5969_1261_1261_1720 s5969_1261_2981_1935 rfl rfl rfl

private theorem s5969_1261_4916_430 : blockEstimate 5969 1261 4916 430 = 0x35984fc257f :=
  block_append p5969_1261_4916 p5969_1261_5131 rfl rfl rfl

private theorem s5969_1261_5346_430 : blockEstimate 5969 1261 5346 430 = 0x30431e21273 :=
  block_append p5969_1261_5346 p5969_1261_5561 rfl rfl rfl

private theorem s5969_1261_4916_860 : blockEstimate 5969 1261 4916 860 = 0x65db6de37f2 :=
  block_append s5969_1261_4916_430 s5969_1261_5346_430 rfl rfl rfl

private theorem s5969_1261_5776_430 : blockEstimate 5969 1261 5776 430 = 0x2811c75c1c8 :=
  block_append p5969_1261_5776 p5969_1261_5991 rfl rfl rfl

private theorem s5969_1261_6206_430 : blockEstimate 5969 1261 6206 430 = 0x1e47ab1d7ff :=
  block_append p5969_1261_6206 p5969_1261_6421 rfl rfl rfl

private theorem s5969_1261_5776_860 : blockEstimate 5969 1261 5776 860 = 0x465972799c7 :=
  block_append s5969_1261_5776_430 s5969_1261_6206_430 rfl rfl rfl

private theorem s5969_1261_4916_1720 : blockEstimate 5969 1261 4916 1720 = 0xac34e05d1b9 :=
  block_append s5969_1261_4916_860 s5969_1261_5776_860 rfl rfl rfl

private theorem s5969_1261_6636_430 : blockEstimate 5969 1261 6636 430 = 0x14a0b489e20 :=
  block_append p5969_1261_6636 p5969_1261_6851 rfl rfl rfl

private theorem s5969_1261_7066_430 : blockEstimate 5969 1261 7066 430 = 0xc0bd707eef :=
  block_append p5969_1261_7066 p5969_1261_7281 rfl rfl rfl

private theorem s5969_1261_6636_860 : blockEstimate 5969 1261 6636 860 = 0x20ac8b91d0f :=
  block_append s5969_1261_6636_430 s5969_1261_7066_430 rfl rfl rfl

private theorem s5969_1261_7496_430 : blockEstimate 5969 1261 7496 430 = 0x5589643504 :=
  block_append p5969_1261_7496 p5969_1261_7711 rfl rfl rfl

private theorem s5969_1261_8141_350 : blockEstimate 5969 1261 8141 350 = 0x4e452afbc :=
  block_append p5969_1261_8141 p5969_1261_8356 rfl rfl rfl

private theorem s5969_1261_7926_565 : blockEstimate 5969 1261 7926 565 = 0x141f8f3165 :=
  block_append p5969_1261_7926 s5969_1261_8141_350 rfl rfl rfl

private theorem s5969_1261_7496_995 : blockEstimate 5969 1261 7496 995 = 0x69a8f36669 :=
  block_append s5969_1261_7496_430 s5969_1261_7926_565 rfl rfl rfl

private theorem s5969_1261_6636_1855 : blockEstimate 5969 1261 6636 1855 = 0x27471ac8378 :=
  block_append s5969_1261_6636_860 s5969_1261_7496_995 rfl rfl rfl

private theorem s5969_1261_4916_3575 : blockEstimate 5969 1261 4916 3575 = 0xd37bfb25531 :=
  block_append s5969_1261_4916_1720 s5969_1261_6636_1855 rfl rfl rfl

private theorem s5969_1261_1261_7230 : blockEstimate 5969 1261 1261 7230 = 0x1f12fe9a79ee :=
  block_append s5969_1261_1261_3655 s5969_1261_4916_3575 rfl rfl rfl

theorem moment5969_1261 : momentEstimate 5969 1261 = 0x1f12fe9a79ee := s5969_1261_1261_7230

end HighCore82219BankProof
