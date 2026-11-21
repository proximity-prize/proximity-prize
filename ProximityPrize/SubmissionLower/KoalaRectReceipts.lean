import ProximityPrize.SubmissionLower.KoalaRectArithmetic

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open HighCore82219 (terminal agreement)
open HighCore82219TerminalArithmetic (Parts)

private abbrev T := terminal .h2367
def rectWitness : ℕ → RectArgs
  | 1 => ⟨![264000, 36000], ![224, 225]⟩
  | 2 => ⟨![264000, 36000], ![222, 223]⟩
  | 3 => ⟨![264000, 36000], ![220, 220]⟩
  | 4 => ⟨![264000, 36000], ![217, 218]⟩
  | 5 => ⟨![264000, 36000], ![215, 216]⟩
  | 6 => ⟨![264000, 36000], ![212, 213]⟩
  | 7 => ⟨![264000, 36000], ![210, 211]⟩
  | 8 => ⟨![264000, 36000], ![207, 208]⟩
  | 9 => ⟨![264000, 36000], ![205, 205]⟩
  | 10 => ⟨![264000, 36000], ![202, 203]⟩
  | 11 => ⟨![264000, 36000], ![199, 200]⟩
  | 12 => ⟨![264000, 36000], ![196, 197]⟩
  | 13 => ⟨![255000, 45000], ![193, 193]⟩
  | 14 => ⟨![255000, 45000], ![188, 189]⟩
  | 15 => ⟨![255000, 45000], ![183, 184]⟩
  | 16 => ⟨![255000, 45000], ![178, 179]⟩
  | 17 => ⟨![246000, 54000], ![173, 173]⟩
  | 18 => ⟨![150000, 150000], ![146, 147]⟩
  | 19 => ⟨![150000, 150000], ![113, 114]⟩
  | 20 => ⟨![150000, 150000], ![78, 78]⟩
  | 21 => ⟨![150000, 150000], ![40, 40]⟩
  | 22 => ⟨![150000, 150000], ![0, 1]⟩
  | 23 => ⟨![150000, 150000], ![0, 1]⟩
  | 24 => ⟨![150000, 150000], ![0, 1]⟩
  | 25 => ⟨![150000, 150000], ![0, 1]⟩
  | 26 => ⟨![150000, 150000], ![0, 1]⟩
  | 27 => ⟨![150000, 150000], ![0, 1]⟩
  | 28 => ⟨![150000, 150000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 448
  | 2 => 444
  | 3 => 439
  | 4 => 434
  | 5 => 430
  | 6 => 424
  | 7 => 420
  | 8 => 414
  | 9 => 409
  | 10 => 404
  | 11 => 398
  | 12 => 392
  | 13 => 385
  | 14 => 376
  | 15 => 366
  | 16 => 356
  | 17 => 345
  | 18 => 292
  | 19 => 226
  | 20 => 155
  | 21 => 79
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 1 (rectWitness 1) :=
  block! 1436,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x644dee40564d9559b44cf9a0,0x645edf6a9bf2e34eb36f2d00,(last! 0x54388fc3c61869c69da8160,0x532be3fc03887a944c87aa0))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 2 (rectWitness 2) :=
  block! 1437,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x645e72647a91de931fc9d6a0,0x646f633c1fc8329dc73d0480,(last! 0x5330c8ce537146f6d3eb320,0x5224223d4422d86dd2181a0))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 3 (rectWitness 3) :=
  block! 1439,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x646a3242e87140dd3717cbc0,0x647b234c07df83a5223f5940,(last! 0x5273805b8a4ed656fd23fa0,0x5166d68e596a402eff64a60))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 4 (rectWitness 4) :=
  block! 1441,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x647b434fa4e561e834b64240,0x648c33fafa361efe55953680,(last! 0x51630573282f5b25e99bc00,0x50566192170066d3caba160))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 5 (rectWitness 5) :=
  block! 1442,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x648ce6c97b7e8872c74af2a0,0x649dd706e14aaaca3a8f0000,(last! 0x5049957ffeb1fadb28fcc20,0x4f3cf892bfb9258a3e642c0))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 6 (rectWitness 6) :=
  block! 1445,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x6499f0f6ef43d11f8ffad220,0x64aae14e224872872a42c200,(last! 0x4f77e2dde03d461b2169aa0,0x4e6b44358e29d41b3acfa20))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 7 (rectWitness 7) :=
  block! 1446,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64ac5c91546c69edb73b91a0,0x64bd4c656ddbbf62b6559240,(last! 0x4e522c27dc32f455457d4a0,0x4d4595cc5642e7e76c62c40))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 8 (rectWitness 8) :=
  block! 1449,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64ba7b1b649a8d97264f4340,0x64cb6af12881677b9439e380,(last! 0x4d6f751df2787c77bbdd300,0x4c62de908206310a78e11e0))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 9 (rectWitness 9) :=
  block! 1451,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64c97174ee7e151788f380a0,0x64da6137a9b7778267084680,(last! 0x4c7f7e05bff829d036d7860,0x4b72e898219273f4c4c6640))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 10 (rectWitness 10) :=
  block! 1453,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64dcdb3ffbdea6eb3d8221a0,0x64edca60848efe18c2666380,(last! 0x4b4a3754e21dac70d8acd20,0x4a3dac2e7d0527c217a42a0))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 11 (rectWitness 11) :=
  block! 1456,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64eca8b259d1a609002ae5e0,0x64fd97a8ab230d2f400f6fc0,(last! 0x4a4d09b67e70b53edcadfe0,0x494081291e3f8d994ba4de0))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 12 (rectWitness 12) :=
  block! 1458,7,0x6991691911209b66a3ffdf80,0x69916c521d901d046b3c4440,(more! 0x64fd0f66265e85544aaaaca0,0x650dfe211743a9699905d180,(last! 0x494676b6a6150cb857f70a0,0x4839f1d9d91b639eeb34140))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 13 (rectWitness 13) :=
  block! 1509,9,0x7f6fba142b6eadfa63ffdf80,0x7f6fbd4d37de2f982b3c4440,(more! 0x7946cc3625561a29c1c750e0,0x795b59b5cb06b1b32663e200,(last! 0x628eee57a34ccb87dd828e0,0x6148f1ca9b9276ed13c7e00))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 14 (rectWitness 14) :=
  block! 1514,10,0x7f6fba142b6eadfa63ffdf80,0x7f6fbd4d37de2f982b3c4440,(more! 0x7965e15cdbdfb0ed2346ef20,0x797a6e07fa9bea394b508b00,(last! 0x609e696e1630107f42eabc0,0x5f587a3cef96324e7c278c0))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 15 (rectWitness 15) :=
  block! 1520,10,0x7f6fba142b6eadfa63ffdf80,0x7f6fbd4d37de2f982b3c4440,(more! 0x7982799d745f5d6304c1dee0,0x799705d6f89b3341508b40c0,(last! 0x5ed414bc58c155c883e8de0,0x5d8e2c8ae881a42778fefa0))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 16 (rectWitness 16) :=
  block! 1527,10,0x7f6fba142b6eadfa63ffdf80,0x7f6fbd4d37de2f982b3c4440,(more! 0x79a0b73f4c397ff66af35440,0x79b542b37417e0de9c7f2800,(last! 0x5cf051cea004a26b887c260,0x5baa75f1c17c5df37ebde40))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 17 (rectWitness 17) :=
  block! 1588,12,0x9381e859519a47cba3ffdf80,0x9381eb925e09c9696b3c4440,(more! 0x8c8b48a9150a46f10a525100,0x8ca323bdc1ed062dad44bf00,(last! 0x6f6a06020f92d7d262d0f80,0x6def9b2191dd4faae661e80))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 18 (rectWitness 18) :=
  block! 1609,13,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xeca6571e8bd02523b0d4fae0,0xeccf0e1a79480ec17a69a320,(last! 0xd1c33a7f226bd74f6b43d40,0xcf3d3279192b81389adbf00))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 19 (rectWitness 19) :=
  block! 1592,12,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xece3c1cc12ab5c9484618b80,0xed0c756a51a022774a9716c0,(last! 0xcdec808ed67048cda9f9da0,0xcb66ae58b1171e9be3441c0))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 20 (rectWitness 20) :=
  block! 1576,12,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xed1ca53811764c8ebc6b52e0,0xed45559a2aacf80a16188cc0,(last! 0xca5e3b0fa02dd8d28e37b60,0xc7d89c921e2ce3c72f3e180))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 21 (rectWitness 21) :=
  block! 1562,11,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xed51581a4fe8a2dde9183720,0xed7a05691326cacaa3c3ff20,(last! 0xc712e573600f0aa9d2a4320,0xc48d781f5068099598036e0))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 22 (rectWitness 22) :=
  block! 1549,11,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xed8473b3e77f13bdcffb7c40,0xedad1da8eef7d4ad9d61efa0,(last! 0xc3e2b851412f84e04217b60,0xc15d80bd946f11d4d00bfa0))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 23 (rectWitness 23) :=
  block! 1537,10,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xee0bf21f3ec2381cba4b7dc0,0xee348786fb662027a3217680,(last! 0xbbb52ea8805168f36996d40,0xb93148048516c6fdbc97c80))

theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 24 (rectWitness 24) :=
  block! 1526,10,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xee87b1ce96c4396a02a7bbe0,0xeeb0347344905c275e5ce880,(last! 0xb43d6038224531e39c0b240,0xb1baad329b402bf26680f00))

theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 25 (rectWitness 25) :=
  block! 1516,10,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xeef9297d898bf1b33a9ac5c0,0xef219aef51a5003100ce9280,(last! 0xad649f343dd456997d29620,0xaae306329f9592cd45e7580))

theorem r26 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 26 (rectWitness 26) :=
  block! 1507,9,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xef6194223051ab6769c15ba0,0xef89f5c21f0d013ccc9d1800,(last! 0xa717dcf53639d6e7c9b23c0,0xa4974760149281913176ba0))

theorem r27 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 27 (rectWitness 27) :=
  block! 1498,9,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xefc1fc574014f9f7990be100,0xefea4f5dc88493a05b6c0200,(last! 0xa146f8bdafc62fc93ec8900,0x9ec75295fc7871c1e253b40))

theorem r28 : BlockChecks T.shape T.nodeRows T.poleMoment 2378 28 (rectWitness 28) :=
  block! 1490,9,0xf9c2828f9226e4cba3ffdf80,0xf9c285c89e9666696b3c4440,(more! 0xf01a94a80b6d3674ce5daf40,0xf042da4c5a5e0cc28ae88480,(last! 0x9beeaafcd1df4170140e2a0,0x996fe054785155c6a34c280))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2378 E (rectWitness E) := by
  interval_cases E
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20
  · exact r21
  · exact r22
  · exact r23
  · exact r24
  · exact r25
  · exact r26
  · exact r27
  · exact r28

theorem witness_guards {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    (rectWitness E).U 1 ≤ (rectWitness E).U 0 ∧
      (rectWitness E).U 0 + (rectWitness E).U 1 ≤ T.shape.U := by
  interval_cases E <;> decide

theorem paid_order {E : ℕ} (hl : 1 ≤ E) (hu : E < 28) :
    (rectWitness E).order 0 ≤ (rectWitness E).order 1 ∧
      (rectWitness E).order 1 ≤ (rectWitness E).order 0 + 1 ∧
      (rectWitness E).order 0 + (rectWitness E).order 1 = paidCap E + 1 := by
  interval_cases E <;> decide

theorem rect_bounds {h E : ℕ} (hl : 2378 ≤ h) (hu : h ≤ 2465)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
