import ProximityPrize.SubmissionLower.KoalaRectArithmetic

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open HighCore82229 (terminal agreement)
open HighCore82229TerminalArithmetic (Parts)

private abbrev T := terminal .h2367
def rectWitness : ℕ → RectArgs
  | 1 => ⟨![335505, 37495], ![217, 218]⟩
  | 2 => ⟨![335376, 37624], ![214, 215]⟩
  | 3 => ⟨![335087, 37913], ![212, 213]⟩
  | 4 => ⟨![334810, 38190], ![210, 211]⟩
  | 5 => ⟨![334729, 38271], ![208, 208]⟩
  | 6 => ⟨![334273, 38727], ![205, 206]⟩
  | 7 => ⟨![334025, 38975], ![202, 203]⟩
  | 8 => ⟨![333605, 39395], ![200, 201]⟩
  | 9 => ⟨![333203, 39797], ![197, 198]⟩
  | 10 => ⟨![332636, 40364], ![194, 195]⟩
  | 11 => ⟨![332105, 40895], ![191, 192]⟩
  | 12 => ⟨![331421, 41579], ![188, 189]⟩
  | 13 => ⟨![330636, 42364], ![184, 185]⟩
  | 14 => ⟨![329742, 43258], ![181, 181]⟩
  | 15 => ⟨![328220, 44780], ![176, 177]⟩
  | 16 => ⟨![325873, 47127], ![171, 172]⟩
  | 17 => ⟨![315731, 57269], ![165, 166]⟩
  | 18 => ⟨![186500, 186500], ![128, 128]⟩
  | 19 => ⟨![186500, 186500], ![87, 87]⟩
  | 20 => ⟨![186500, 186500], ![43, 43]⟩
  | 21 => ⟨![186697, 186303], ![0, 1]⟩
  | 22 => ⟨![186650, 186350], ![0, 1]⟩
  | 23 => ⟨![186620, 186380], ![0, 1]⟩
  | 24 => ⟨![186598, 186402], ![0, 1]⟩
  | 25 => ⟨![186582, 186418], ![0, 1]⟩
  | 26 => ⟨![186570, 186430], ![0, 1]⟩
  | 27 => ⟨![186561, 186439], ![0, 1]⟩
  | 28 => ⟨![186500, 186500], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 434
  | 2 => 428
  | 3 => 424
  | 4 => 420
  | 5 => 415
  | 6 => 410
  | 7 => 404
  | 8 => 400
  | 9 => 394
  | 10 => 388
  | 11 => 382
  | 12 => 376
  | 13 => 368
  | 14 => 361
  | 15 => 352
  | 16 => 342
  | 17 => 330
  | 18 => 255
  | 19 => 173
  | 20 => 85
  | 21 => 0
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

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 1 (rectWitness 1) :=
  block! 1536,8,0xab2dd5e7047cf2b24060a200,0xab2ddb2787499fd26260ac80,(more! 0x9fe162d4f81d518bac22c100,0x9ffb5e3ffea3f031c8c70f80,(last! 0xb4c9e43ce5dfd8c83b29940,0xb32e1177c2817f4748d74c0))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 2 (rectWitness 2) :=
  block! 1539,8,0xabb38b3e1ae1b9cc3ae0a200,0xabb3907e9dae66ec5ce0ac80,(more! 0xa0694eb426545503245598e0,0xa0835f9202f1b5242fe61140,(last! 0xb4a3d4e25475940a202b780,0xb306ad6cfbd6bf27e350200))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 3 (rectWitness 3) :=
  block! 1542,8,0xacdeabf8b16e615c5860a200,0xacdeb139343b0e7c7a60ac80,(more! 0xa18ed9b1fe5360594b3ddc00,0xa1a918f61e01b44912247000,(last! 0xb4fe0f964d8c29ecc5f6900,0xb35e080dce2c9a7d1d6a980))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 4 (rectWitness 4) :=
  block! 1545,8,0xadfcd5630cd19f1038e0a200,0xadfcdaa38f9e4c305ae0ac80,(more! 0xa2aaca7982d011bf01d3bc40,0xa2c536045b691cccfcb7dfc0,(last! 0xb522b755797d07cb570afe0,0xb37ff1741d33b8f90c69a20))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 5 (rectWitness 5) :=
  block! 1548,8,0xae5069665c8583f66860a200,0xae506ea6df5231168a60ac80,(more! 0xa30b815a0aa2412270a63000,0xa325fa3772997714ecfad000,(last! 0xb44e9e0b70dc26d3847bc00,0xb2ab04875bf8486b1e37400))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 6 (rectWitness 6) :=
  block! 1552,9,0xb02612e743981af81060a200,0xb0261827c664c8183260ac80,(more! 0xa4ce8d5c5427764d5d0f45c0,0xa4e94f1ece7016c6ae289080,(last! 0xb579fc4528de306e7ea7680,0xb3d1de5f8cc49d1a1e2e500))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 7 (rectWitness 7) :=
  block! 1556,9,0xb124e5886f1502552860a200,0xb124eac8f1e1af754a60ac80,(more! 0xa5cbcf281fa51b7e4d709800,0xa5e6b8ed959aeaec3e1fd000,(last! 0xb5918679ed436b6542f3080,0xb3e6ed865af811d23905a80))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 8 (rectWitness 8) :=
  block! 1560,9,0xb2d3799eb56f0bbe2460a200,0xb2d37edf383bb8de4660ac80,(more! 0xa7719e7ce0b0bce2d9fbb140,0xa78ccab8c2490f4a9f0d2e80,(last! 0xb62034c3b86fc4f19cc7480,0xb4717da07b877e766a37b80))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 9 (rectWitness 9) :=
  block! 1565,9,0xb46e734bd3c880d29460a200,0xb46e788c56952df2b660ac80,(more! 0xa9004abb5f4a44259cca4e00,0xa91bb72d23b0e2bef1432400,(last! 0xb6e449a5f92dfcc96bd9d80,0xb531979afc8ef36ef721580))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 10 (rectWitness 10) :=
  block! 1571,9,0xb6b032a374e59640c2e0a200,0xb6b037e3f7b24360e4e0ac80,(more! 0xab288cde5d6fb89e535d6400,0xab44537b8f4a97676366c740,(last! 0xb87bd1a9b110bbb721dd3a0,0xb6c388e3796734b4c4cc900))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 11 (rectWitness 11) :=
  block! 1577,9,0xb8cb3bf06ab97b04a860a200,0xb8cb4130ed862824ca60ac80,(more! 0xad320cfa364c7978cbadd000,0xad4e2779dee2acac1b780000,(last! 0xb994abd5bd48556edfef000,0xb7d7302523718f292968000))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 12 (rectWitness 12) :=
  block! 1584,10,0xbb7eb1bcbba2f1cbec60a200,0xbb7eb6fd3e6f9eec0e60ac80,(more! 0xafc9e3bc35260f43a5bf9240,0xafe669bae7e0fbf3c6502280,(last! 0xbb4f9ab6a2af55bde257f40,0xb98b759208f850336d17b80))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 13 (rectWitness 13) :=
  block! 1593,10,0xbe943e54f6d10d67c2e0a200,0xbe944395799dba87e4e0ac80,(more! 0xb2b8b175d2af46e88d44fda0,0xb2d5b3007f28a13aba5e5f40,(last! 0xbdb99688d6482b8d7743040,0xbbedc8d8be67852fd44c220))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 14 (rectWitness 14) :=
  block! 1603,10,0xc2123390780250a078e0a200,0xc21238d0facefdc09ae0ac80,(more! 0xb60db8e5edcfdbff95b4aa00,0xb62b45d9ea24d624cfcc1840,(last! 0xc047ce4ee175f552dfd9360,0xbe735c8db2a74bc51b09720))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 15 (rectWitness 15) :=
  block! 1617,11,0xc7f755bba83fe4eec2e0a200,0xc7f75afc2b0c920ee4e0ac80,(more! 0xbb9bf64307e4c73960cea2a0,0xbbba6e653e187e4a22db6740,(last! 0xc5b6aa343bc468620d6d140,0xc3d3a50056ce34023c9d7e0))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 16 (rectWitness 16) :=
  block! 1638,12,0xd0eee5cc204eefb4e060a200,0xd0eeeb0ca31b9cd50260ac80,(more! 0xc401ae01bee38620fac40180,0xc4218c4d74c2305169869700,(last! 0xced37fa3501222296126500,0xccda477ef266b37a8ea3600))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 17 (rectWitness 17) :=
  block! 1709,14,0xf5f5e39aebf16a9b5460a200,0xf5f5e8db6ebe17bb7660ac80,(more! 0xe64b63d47f84e6ead08cf080,0xe67108d5bbe0a9ccca059b00,(last! 0xfaa998991c21c10c8169d80,0xf854ba5fb18d6ba382c7000))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 18 (rectWitness 18) :=
  block! 1722,15,0x1d8f5099e769ea5e762e0a200,0x1d8f50edef96b530784e0ac80,(more! 0x1b7d687bfd995e21dddf77be0,0x1b81f958ef3b47adfa8b74c80,(last! 0x211e87399b71e0a8b317b660,0x20d61c0a23f7b1e5da31d440))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 19 (rectWitness 19) :=
  block! 1703,14,0x1d8f5099e769ea5e762e0a200,0x1d8f50edef96b530784e0ac80,(more! 0x1b84feb914bf79d6f410cd380,0x1b898f314f40d1a594057df40,(last! 0x20a528f21b2a2ece15b803c0,0x205cc40da1db853ce1b44320))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 20 (rectWitness 20) :=
  block! 1686,13,0x1d8f5099e769ea5e762e0a200,0x1d8f50edef96b530784e0ac80,(more! 0x1b8c02a10c2e46a3a231b5ca0,0x1b9092b8f0ea270cd08c0ace0,(last! 0x2034eee1977756dc933a8e00,0x1fec9001fb4d2d1e10a75020))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 21 (rectWitness 21) :=
  block! 1671,13,0x1d8f4e70c8fdcd1bca860a200,0x1d8f4ec4d12a97edcca60ac80,(more! 0x1b93aa4f4fedb2e3c94912b80,0x1b9839d48043df2e5c206ddc0,(last! 0x1fbb412a9c3f46d0c91ca7c0,0x1f72eb8fdfd00f1fc42983c0))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 22 (rectWitness 22) :=
  block! 1657,12,0x1d8f4f5939f806e82b8e0a200,0x1d8f4fad4224d1ba2dae0ac80,(more! 0x1ba59492c51ced3461a4d33a0,0x1baa2191e0a5c3f8a3f914560,(last! 0x1ea6384d4715a30d554a0540,0x1e5e0c20cc6a8b1abbc74b60))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 23 (rectWitness 23) :=
  block! 1644,12,0x1d8f4fccab9be8273c2e0a200,0x1d8f5020b3c8b2f93e4e0ac80,(more! 0x1bb5dedf1a24cb9861db7cc80,0x1bba6992eb6d3be06261969a0,(last! 0x1daa533b10998338758e4b40,0x1d624cb8ce698a3fd65e85a0))

private theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 24 (rectWitness 24) :=
  block! 1632,11,0x1d8f50110648699a328e0a200,0x1d8f50650e75346c34ae0ac80,(more! 0x1bc4bf7fcf1e0fcbe705e8d80,0x1bc9481b7627af1859bbe9260,(last! 0x1cc44c1d5425b031a862d600,0x1c7c67fec9fcc5b63010c800))

private theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 25 (rectWitness 25) :=
  block! 1622,11,0x1d8f503a123e6a0ba48e0a200,0x1d8f508e1a6b34dda6ae0ac80,(more! 0x1bd263966e982ec025b8b2460,0x1bd6ea46ad158d6d776a12940,(last! 0x1bf1685d67c4e11a39a68fe0,0x1ba9a3c470caecd276bc0680))

private theorem r26 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 26 (rectWitness 26) :=
  block! 1612,11,0x1d8f50541149260f398e0a200,0x1d8f50a81975f0e13bae0ac80,(more! 0x1bdef10d5008e4ded1b98be20,0x1be375f98bc7ba604ed581320,(last! 0x1b2f5cf384a39d35442f7a40,0x1ae7b559da0f4972ba2bdce0))

private theorem r27 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 27 (rectWitness 27) :=
  block! 1603,10,0x1d8f5064defb74a411060a200,0x1d8f50b8e7283f7613260ac80,(more! 0x1bea87f8505ec149b26cbaf40,0x1bef0b4353a8997e506d875c0,(last! 0x1a7c390fe90556e379c06300,0x1a34ac3abf812d52a2e647c0))

private theorem r28 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 28 (rectWitness 28) :=
  block! 1594,10,0x1d8f5099e769ea5e762e0a200,0x1d8f50edef96b530784e0ac80,(more! 0x1bf53176260c329b9ead13420,0x1bf9b34243dc2fb609c201400,(last! 0x19d76c6b9f08207dac906ea0,0x198ff8276ef5ac791c9d1a60))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2356 E (rectWitness E) := by
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

theorem rect_bounds {h E : ℕ} (hl : 2356 ≤ h) (hu : h ≤ 2439)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
