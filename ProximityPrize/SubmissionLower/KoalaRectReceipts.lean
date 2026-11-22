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
  | 1 => ⟨![320625, 54375], ![512, 512]⟩
  | 2 => ⟨![335808, 39192], ![266, 267]⟩
  | 3 => ⟨![329995, 45005], ![343, 344]⟩
  | 4 => ⟨![333557, 41443], ![287, 288]⟩
  | 5 => ⟨![335807, 39193], ![252, 252]⟩
  | 6 => ⟨![337125, 37875], ![227, 228]⟩
  | 7 => ⟨![337120, 37880], ![223, 223]⟩
  | 8 => ⟨![336557, 38443], ![223, 223]⟩
  | 9 => ⟨![335995, 39005], ![223, 223]⟩
  | 10 => ⟨![335250, 39750], ![223, 223]⟩
  | 11 => ⟨![334500, 40500], ![223, 223]⟩
  | 12 => ⟨![333745, 41255], ![222, 222]⟩
  | 13 => ⟨![333745, 41255], ![212, 212]⟩
  | 14 => ⟨![333182, 41818], ![204, 204]⟩
  | 15 => ⟨![332250, 42750], ![196, 197]⟩
  | 16 => ⟨![330745, 44255], ![189, 190]⟩
  | 17 => ⟨![327933, 47067], ![183, 184]⟩
  | 18 => ⟨![187500, 187500], ![178, 178]⟩
  | 19 => ⟨![187500, 187500], ![173, 173]⟩
  | 20 => ⟨![188435, 186565], ![168, 169]⟩
  | 21 => ⟨![187500, 187500], ![164, 164]⟩
  | 22 => ⟨![187500, 187500], ![114, 114]⟩
  | 23 => ⟨![187500, 187500], ![111, 111]⟩
  | 24 => ⟨![187500, 187500], ![109, 109]⟩
  | 25 => ⟨![187687, 187313], ![106, 107]⟩
  | 26 => ⟨![187687, 187313], ![104, 105]⟩
  | 27 => ⟨![187687, 187313], ![102, 103]⟩
  | 28 => ⟨![187500, 187500], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 1023
  | 2 => 532
  | 3 => 686
  | 4 => 574
  | 5 => 503
  | 6 => 454
  | 7 => 445
  | 8 => 445
  | 9 => 445
  | 10 => 445
  | 11 => 445
  | 12 => 443
  | 13 => 423
  | 14 => 407
  | 15 => 392
  | 16 => 378
  | 17 => 366
  | 18 => 355
  | 19 => 345
  | 20 => 336
  | 21 => 327
  | 22 => 227
  | 23 => 221
  | 24 => 217
  | 25 => 212
  | 26 => 208
  | 27 => 204
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 1 (rectWitness 1) :=
  block! 1382,5,0xc195306a71c663ada2f9d840,0xc1953471c0f7a7d279ec5a00,(more! 0xbb3bd10727a912e1707fe400,0xbb3c17fd5cff912c0730ec00,(last! 0x679ca43d5f15dcc7bae1a00,0x679cbb0b8d90ae42ae4a000))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 2 (rectWitness 2) :=
  block! 1422,6,0x922c69252e32544c17f9d840,0x922c6d2c7d639870eeec5a00,(more! 0x8ba2224ff7dbfb2449818120,0x8ba2566d835cc709fdec93c0,(last! 0x68f8145440ead7b7c330780,0x68f82b8d329e9cb1faa1840))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 3 (rectWitness 3) :=
  block! 1406,6,0xa4edd5911b301d071af9d840,0xa4edd9986a61612bf1ec5a00,(more! 0x9e780cd08ea3506bc9b05440,0x9e784849df0bc5103352f980,(last! 0x68557a77bad347cf9a72e80,0x685592585e52023d9663f40))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 4 (rectWitness 4) :=
  block! 1419,6,0x99867768ace5ae1dcaf9d840,0x99867b6ffc16f242a1ec5a00,(more! 0x930dbbc33f71b01e4fb64b00,0x930df2a74b57041877d7e300,(last! 0x681963217fbbe172632cf80,0x68197b9e6d1726a3a1f1a00))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 5 (rectWitness 5) :=
  block! 1431,6,0x922d40d27fbd61ff12f9d840,0x922d44d9ceeea623e9ec5a00,(more! 0x8bafb779fffdf9b77cf2b000,0x8bafeb5b6cf19ce2e1190e00,(last! 0x681c83c7394e6caf8c13b00,0x681c9d12a4d523433803a00))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 6 (rectWitness 6) :=
  block! 1442,7,0x8dd1ec598b0935136af9d840,0x8dd1f060da3a793841ec5a00,(more! 0x8749157a838972c6e7332f00,0x8749477d046739c157f66a00,(last! 0x689e3944ffcc0a3dd59e200,0x689e539e1c7e09ed9c62d00))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 7 (rectWitness 7) :=
  block! 1445,7,0x8dd62c4bf05d53df17f9d840,0x8dd630533f8e9803eeec5a00,(more! 0x8754188bc01c3b70d08cc340,0x87544a78cd4691d24e61b2e0,(last! 0x682c5416ec1587893cc5a00,0x682c6f3fb5141cb693df8e0))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 8 (rectWitness 8) :=
  block! 1448,7,0x8fb3ca96cd4bea805af9d840,0x8fb3ce9e1c7d2ea531ec5a00,(more! 0x892febe3f621c61a4d2a5b60,0x89301e6da5b99fefafc24fa0,(last! 0x68501c21ba4e7b70902fbe0,0x685038447775b2c8808e620))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 9 (rectWitness 9) :=
  block! 1450,7,0x918ec3fa82fb8dff7af9d840,0x918ec801d22cd22451ec5a00,(more! 0x8b0b28337183aa192434e760,0x8b0b5b5993664ae121e67ca0,(last! 0x68536929448e315feb7cb80,0x685386455566255b1409100))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 10 (rectWitness 10) :=
  block! 1454,7,0x9401a2ee054ef6ef13f9d840,0x9401a6f554803b13eaec5a00,(more! 0x8d7439acaea87eb1692d9d20,0x8d746d9f44f3ad65beb21600,(last! 0x68f849360c0aed3713682c0,0x68f86788f1377bbdeff52a0))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 11 (rectWitness 11) :=
  block! 1457,7,0x967587a0fa73566327f9d840,0x96758ba849a49a87feec5a00,(more! 0x8fe0c0254ebc2b1357eb7e80,0x8fe0f4e5784c378717870560,(last! 0x6976b7b704d09fcffc3cd80,0x6976d74230a0f35d9b23ca0))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 12 (rectWitness 12) :=
  block! 1461,8,0x98ea61b720c6649722f9d840,0x98ea65be6ff7a8bbf9ec5a00,(more! 0x924b93b4e5d37e8749dd6b00,0x924bc93d6ee9fd96ada9c700,(last! 0x6a1db888e86b7eeeffa3e00,0x6a1dd96ec41aaac0dc6b700))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 13 (rectWitness 13) :=
  block! 1470,8,0x98ea61b720c6649722f9d840,0x98ea65be6ff7a8bbf9ec5a00,(more! 0x9244af94604aedd591d3c500,0x9244e4e710083bd631c55900,(last! 0x6a7b59ebd20eec8e1262400,0x6a7b7c6203d06fd1c8d6e00))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 14 (rectWitness 14) :=
  block! 1480,8,0x9abd34bd7cf0a19ff3f9d840,0x9abd38c4cc21e5c4caec5a00,(more! 0x93fd0e7927500c168d584720,0x93fd443269ee8cc8521abd20,(last! 0x6c17950c81327c0e018b100,0x6c17b9ad92aefd2ef5cce40))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 15 (rectWitness 15) :=
  block! 1493,9,0x9dbe099cefb45a61f3f9d840,0x9dbe0da43ee59e86caec5a00,(more! 0x96d8bf5c01b2e2175025c540,0x96d8f5deca5d0541ebc82960,(last! 0x6e61ead7f598c4daed88c80,0x6e62121d2e891bdac8c19a0))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 16 (rectWitness 16) :=
  block! 1508,9,0xa28d226f26189a8752f9d840,0xa28d26767549deac29ec5a00,(more! 0x9b6bf2416d9b7dcbd3736ac0,0x9b6c2a1bbbf0b35ed83bc880,(last! 0x72198c78e63634dab772280,0x7219b74fb9c501923654c00))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 17 (rectWitness 17) :=
  block! 1531,10,0xab66e228d30923ef3af9d840,0xab66e630223a681411ec5a00,(more! 0xa3d82d902e7dbf5019fdea80,0xa3d86807ed85c8be9e325700,(last! 0x78f03d2fa0f5537ac4ed400,0x78f06d6fcac95d5a2264500))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 18 (rectWitness 18) :=
  block! 1609,13,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x171e9fb980c2ca3adac99b700,0x171ea78b85128f2a90df77220,(last! 0x144f39b7a47053d1af866800,0x144f439dc2faba79d4fc3220))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 19 (rectWitness 19) :=
  block! 1592,12,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x172cb550688d3e8d79a2d8000,0x172cbd3288f9a27797b83ab40,(last! 0x13743dd724b133d754afa740,0x1374476bc08c7954979690a0))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 20 (rectWitness 20) :=
  block! 1576,12,0x18634058a4f518e40aaf9d840,0x1863409919e82d26581ec5a00,(more! 0x173992ab5ada0122d964ddc00,0x17399a9cc62ba6f5e47da4880,(last! 0x12a9f1daca176ed040707080,0x12a9fb20a5271e17e091ab80))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 21 (rectWitness 21) :=
  block! 1562,11,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x1745ad1584d8747693258faa0,0x1745b5155e3c75a221ef9f0c0,(last! 0x11f065bae853f41a825c5ea0,0x11f06eb656631fe30f23b480))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 22 (rectWitness 22) :=
  block! 1549,11,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x1749255a33ce25d60a1c8e9a0,0x17492d56c5920f7d2fee4ccc0,(last! 0x11b80923e8901177a222d180,0x11b8123bad961283c1e99f00))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 23 (rectWitness 23) :=
  block! 1537,10,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x175432a37f0113dfac412ef20,0x17543aae930facd33687afde0,(last! 0x110cca3f4d1f9d93fecd5f00,0x110cd309afa4c089da180560))

theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 24 (rectWitness 24) :=
  block! 1526,10,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x175e88f17e8e92eb1dfe485c0,0x175e910a6bf29e269bebbe580,(last! 0x106cb54944a0063789a74000,0x106cbdc94444446e35a253e0))

theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 25 (rectWitness 25) :=
  block! 1516,10,0x1863667c963c8190f22f9d840,0x186366bd0b2f95d33f9ec5a00,(more! 0x1768049f7bf4349f8a8fe46c0,0x17680cc52d88f4bd25b9d21c0,(last! 0xfd9c5319698522b38045140,0xfd9cd6cd5006eb0cd57fa40))

theorem r26 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 26 (rectWitness 26) :=
  block! 1507,9,0x1863667c963c8190f22f9d840,0x186366bd0b2f95d33f9ec5a00,(more! 0x1770e114c5d5bcbea0089e600,0x1770e9468c53bc7b76a2a5800,(last! 0xf509c0a0a7e35052b16c800,0xf50a403f12f502eb1aef800))

theorem r27 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 27 (rectWitness 27) :=
  block! 1498,9,0x1863667c963c8190f22f9d840,0x186366bd0b2f95d33f9ec5a00,(more! 0x17791d90ab52bf3a27e328b40,0x177925cdc2091e97fde45a180,(last! 0xed125c65b5ed037f59eb3c0,0xed12d82dff20af7a446f740))

theorem r28 : BlockChecks T.shape T.nodeRows T.poleMoment 2391 28 (rectWitness 28) :=
  block! 1490,9,0x186368136af4d098267f9d840,0x18636853dfe7e4da73eec5a00,(more! 0x17762bc79392adf7b2d8f8b60,0x177633f6c6481b0be0efd1520,(last! 0xefb7fd38641bee5e9ce0320,0xefb87e6cee5b2d713591080))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2391 E (rectWitness E) := by
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

theorem rect_bounds {h E : ℕ} (hl : 2391 ≤ h) (hu : h ≤ 2490)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)


end KoalaRectReceipts
