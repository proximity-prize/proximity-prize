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
  | 1 => ⟨![225000, 225000], ![479, 479]⟩
  | 2 => ⟨![396000, 54000], ![239, 240]⟩
  | 3 => ⟨![355500, 94500], ![309, 309]⟩
  | 4 => ⟨![382500, 67500], ![258, 259]⟩
  | 5 => ⟨![396000, 54000], ![227, 227]⟩
  | 6 => ⟨![409500, 40500], ![204, 205]⟩
  | 7 => ⟨![396000, 54000], ![223, 223]⟩
  | 8 => ⟨![382500, 67500], ![223, 223]⟩
  | 9 => ⟨![382500, 67500], ![223, 223]⟩
  | 10 => ⟨![382500, 67500], ![220, 221]⟩
  | 11 => ⟨![382500, 67500], ![209, 210]⟩
  | 12 => ⟨![396000, 54000], ![199, 200]⟩
  | 13 => ⟨![396000, 54000], ![191, 191]⟩
  | 14 => ⟨![396000, 54000], ![183, 184]⟩
  | 15 => ⟨![396000, 54000], ![176, 177]⟩
  | 16 => ⟨![396000, 54000], ![170, 171]⟩
  | 17 => ⟨![225000, 225000], ![165, 165]⟩
  | 18 => ⟨![225000, 225000], ![160, 160]⟩
  | 19 => ⟨![225000, 225000], ![155, 156]⟩
  | 20 => ⟨![225000, 225000], ![151, 152]⟩
  | 21 => ⟨![225000, 225000], ![147, 148]⟩
  | 22 => ⟨![225000, 225000], ![102, 103]⟩
  | 23 => ⟨![225000, 225000], ![100, 100]⟩
  | 24 => ⟨![225000, 225000], ![98, 98]⟩
  | 25 => ⟨![225000, 225000], ![96, 96]⟩
  | 26 => ⟨![225000, 225000], ![94, 94]⟩
  | 27 => ⟨![225000, 225000], ![92, 92]⟩
  | 28 => ⟨![225000, 225000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 957
  | 2 => 478
  | 3 => 617
  | 4 => 516
  | 5 => 453
  | 6 => 408
  | 7 => 445
  | 8 => 445
  | 9 => 445
  | 10 => 440
  | 11 => 418
  | 12 => 398
  | 13 => 381
  | 14 => 366
  | 15 => 352
  | 16 => 340
  | 17 => 329
  | 18 => 319
  | 19 => 310
  | 20 => 302
  | 21 => 294
  | 22 => 204
  | 23 => 199
  | 24 => 195
  | 25 => 191
  | 26 => 187
  | 27 => 183
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 1 (rectWitness 1) :=
  block! 1980,7,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x313ca1529273d6e3a95224ea0,0x31451c91e226bf9b43a39c4e0,(more! 0x8e5a3c58a4dcd115b1b14b20,0x8de290ab7a44fca984218400,(last! 0x34309a2dcc40b8a41b97020,0x334425a22547ef1245dd200)))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 2 (rectWitness 2) :=
  block! 1736,14,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x157dd8a1c6723959de274ef00,0x15815f0c094ffcb3eb65f59e0,(last! 0x32a0e8aaa544619b98373760,0x32690fc3b9ecc024185ccd00))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 3 (rectWitness 3) :=
  block! 1816,1,0x26b825545ec890d959277c280,0x26b825eca8ada142d273235c0,(more! 0x2139f863950ea6cfac99e1700,0x213f8f242eb2aaa2d2259dbe0,(more! 0x57ea0bf7d46c3a351ae58f20,0x57928bf9e61898f6649ed100,(last! 0x4b8b5cb7b0e3327bb7480,0x3a5c6b1e73ec370c3e580)))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 4 (rectWitness 4) :=
  block! 1771,15,0x1dc3216404e2970559277c280,0x1dc321fc4ec7a76ed273235c0,(more! 0x19d35ace33980f274ffeb39a0,0x19d7a047bb6ea5da64340d9a0,(last! 0x3f08ba94af2dcd5750a67000,0x3ec50c6723944fcf303d0da0))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 5 (rectWitness 5) :=
  block! 1748,14,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x158790ad3a69b0ff06b8501c0,0x158b177586b3b5c54285371e0,(last! 0x320374a1ddefa770ded894a0,0x31cb95a2db2770c6b64b4e40))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 6 (rectWitness 6) :=
  block! 1708,13,0x13202cb69a217e5999277c280,0x13202d4ee4068ec31273235c0,(more! 0x10deb0691319f63ab2a2841a0,0x10e168b1d017065fd1027f260,(last! 0x24180a89eae8b5d3596cca60,0x23ecf568b376df8971721a00))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 7 (rectWitness 7) :=
  block! 1753,14,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x159558c99294a0c0dec811a60,0x1598df275c1a040a3c70afe20,(last! 0x312830b71a6760520d986a20,0x30f058826e45b7aca9588960))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 8 (rectWitness 8) :=
  block! 1813,1,0x1dc3216404e2970559277c280,0x1dc321fc4ec7a76ed273235c0,(more! 0x19d5959b7088cb4a411aff660,0x19d9dde04e8a44f32ae474aa0,(more! 0x3ed824a881a3abaee87cab40,0x3e948ad0df1ff7562db971e0,(last! 0xbd199bbe29e26bc69d20,0x7ab69973807b9b73df40)))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 9 (rectWitness 9) :=
  block! 1813,1,0x1dc3216404e2970559277c280,0x1dc321fc4ec7a76ed273235c0,(more! 0x19e5a8752dfaca143e38066e0,0x19e9efdc21df16846988359a0,(more! 0x3dda24b3faa41b63021f5080,0x3d968d4367e0582a405934e0,(last! 0x9b407444725de706e360,0x64a9d20a90b43cb14740)))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 10 (rectWitness 10) :=
  block! 1816,1,0x1dc3216404e2970559277c280,0x1dc321fc4ec7a76ed273235c0,(more! 0x19f27a81beda40b7acd073c00,0x19f6c15d7279fdbe18e1d22e0,(more! 0x3d0e4312db7a3a2ed9b462a0,0x3ccac3298f1c42a756995cc0,(last! 0x11f90466baa8afe364d40,0xda57267076aa69316480)))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 11 (rectWitness 11) :=
  block! 1832,1,0x1dc3216404e2970559277c280,0x1dc321fc4ec7a76ed273235c0,(more! 0x19f40f1df66c6608fb1766200,0x19f856caf755229ab4da4c6e0,(more! 0x3ceb19ffa2421bfa5dd186e0,0x3ca7ecaec2bfbe546f1884c0,(last! 0x749dd745809c4b61b3f80,0x6a48dfaf1a61b87b5b580)))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 12 (rectWitness 12) :=
  block! 1781,15,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x15abdc7502bedb06488fe3520,0x15af63176182f9da4a54d8ae0,(last! 0x2fbdaf9ee26aad51332df360,0x2f85d2dee43feee8f976c120))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 13 (rectWitness 13) :=
  block! 1793,16,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x15ad336eac0633d708d2044a0,0x15b0ba91f372e0da510ea3aa0,(last! 0x2fa5e7456e84d91ddd4712a0,0x2f6e02345793867c6a25a0e0))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 14 (rectWitness 14) :=
  block! 1804,16,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x15b117ee6af692852ecf242e0,0x15b49f4a11c7b33bc7930ede0,(last! 0x2f665eae7e7f65bf4c3408c0,0x2f2e75f38547738269682fc0))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 15 (rectWitness 15) :=
  block! 1816,1,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x15b5b318d36512c283a94b880,0x15b93a9b16ed68cff859979e0,(more! 0x2f1b7d16530608d094bc45e0,0x2ee39c4c1dae3dd256e928c0,(last! 0x28073525a021f01a5680,0x1d8eea27978cb901a680)))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 16 (rectWitness 16) :=
  block! 1826,1,0x18a76524f19d6e8a71277c280,0x18a765bd3b827ef3ea73235c0,(more! 0x15bbbbc724d3c7acce91c8e80,0x15bf433d6cc1786b475d7a2e0,(more! 0x2eba6ca799b639795686ed80,0x2e828feebb719e74a5ce1de0,(last! 0x671d30b66c689fc95600,0x594a8f5ebf3a0e66ff00)))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 17 (rectWitness 17) :=
  block! 1929,5,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x32da7bcb77f25d2f4c04643c0,0x32e2f17fe471c5fa7a07e01e0,(more! 0x77b362dc52c3cc1d2f2eaa60,0x772df0fc485118efa21e4700,(last! 0x6e324e60c0a28e3a1c860,0x639ee738fd27d4f40d000)))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 18 (rectWitness 18) :=
  block! 1906,4,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x3303247e0c4cc7ed7ad752740,0x330b95b2c9d2d86b3fd350440,(more! 0x754041633806ccfa91703220,0x74ba8e4e3ea29b20f4f7e5c0,(last! 0x86dc51ebfb9c6273ec40,0x68b5e4c9b3288d1a4600)))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 19 (rectWitness 19) :=
  block! 1885,3,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x332881a53f86a522eca474260,0x3330eea9cd22d269390cc1580,(more! 0x72fb003ed4842eace2ebed80,0x727573ca1b88c0f9fae9f960,(last! 0x0,0x0)))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 20 (rectWitness 20) :=
  block! 1867,3,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x334aee517391ee87cccebd7c0,0x3353576f247d5b11ff63eb820,(more! 0x70e34b26a581bda4b3208d40,0x705dfec88adf7527cbeff980,(last! 0x0,0x0)))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 21 (rectWitness 21) :=
  block! 1850,2,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x336a7eaca8874a3faa774d0e0,0x3372e4307343a84e04b8c95c0,(more! 0x6ef84a51db78e7e9fd826aa0,0x6e73391cf2f8e92b5d307420,(last! 0x0,0x0)))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 22 (rectWitness 22) :=
  block! 1834,1,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x3375d8af2b0d16a9b1c627820,0x337e3db4b627e07b2a3c88600,(more! 0x6e42cc65e5070562426ca100,0x6dbdc316ea84b78bdf992cc0,(last! 0x0,0x0)))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 23 (rectWitness 23) :=
  block! 1820,1,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x3392bb19f48934a37fda45f60,0x339b1cb2dcc9dc0467f0b4a00,(more! 0x6c824a9ef01db4e8ea1a9320,0x6bfd799aa9e69221dae49840,(last! 0x0,0x0)))

private theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 24 (rectWitness 24) :=
  block! 1807,16,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x33ad86fc2ca1db0670d370460,0x33b5e5639ab450b6614bafa20,(last! 0x6ae259f4505d55e677e976c0,0x6a5dbd70660e604b6be5e4e0))

private theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 25 (rectWitness 25) :=
  block! 1795,16,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x33c647afc43ad0fb7cca167c0,0x33cea3225f6d4e86d031b3e00,(last! 0x6962366ab1f839a7d6f5b6c0,0x68ddca836570e99c85fcd340))

private theorem r26 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 26 (rectWitness 26) :=
  block! 1784,16,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x33dd369d7e82ce62a2ab4f960,0x33e58f519842e666a803feba0,(last! 0x67fe608b12aeccb26023bfc0,0x677a21c48c21de7b72ab4860))

private theorem r27 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 27 (rectWitness 27) :=
  block! 1774,15,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x33f2851c109db336aa8fc3840,0x33fadb42453713ba893a90d80,(last! 0x66b3d70a49044cdc94b50e80,0x662fc2462c6790d2d270dec0))

private theorem r28 : BlockChecks T.shape T.nodeRows T.poleMoment 2354 28 (rectWitness 28) :=
  block! 1765,15,0x3a56169f6e563caa51277c280,0x3a561737b83b4d13ca73235c0,(more! 0x33edc264a0b74515f45a8e360,0x33f61a24542d002656984b6a0,(last! 0x66f71dbbdeba3e4d5ae5cfc0,0x6672ee632abb0af4742ca180))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2354 E (rectWitness E) := by
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

theorem rect_bounds {h E : ℕ} (hl : 2354 ≤ h) (hu : h ≤ 2440)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
