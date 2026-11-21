import ProximityPrize.SubmissionLower.KoalaRectArithmetic

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open HighCore82209 (terminal agreement)
open HighCore82209TerminalArithmetic (Parts)

private abbrev T := terminal .h2367
def rectWitness : ℕ → RectArgs
  | 1 => ⟨![186000, 54000], ![184, 185]⟩
  | 2 => ⟨![186000, 54000], ![182, 183]⟩
  | 3 => ⟨![186000, 54000], ![180, 181]⟩
  | 4 => ⟨![186000, 54000], ![178, 179]⟩
  | 5 => ⟨![184500, 55500], ![175, 176]⟩
  | 6 => ⟨![184500, 55500], ![173, 174]⟩
  | 7 => ⟨![183000, 57000], ![171, 172]⟩
  | 8 => ⟨![183000, 57000], ![168, 169]⟩
  | 9 => ⟨![183000, 57000], ![165, 166]⟩
  | 10 => ⟨![181500, 58500], ![162, 163]⟩
  | 11 => ⟨![180000, 60000], ![159, 160]⟩
  | 12 => ⟨![178500, 61500], ![156, 157]⟩
  | 13 => ⟨![177000, 63000], ![152, 153]⟩
  | 14 => ⟨![183000, 67000], ![147, 148]⟩
  | 15 => ⟨![125000, 125000], ![142, 142]⟩
  | 16 => ⟨![121500, 118500], ![132, 133]⟩
  | 17 => ⟨![120000, 120000], ![120, 120]⟩
  | 18 => ⟨![120000, 120000], ![107, 107]⟩
  | 19 => ⟨![120000, 120000], ![92, 92]⟩
  | 20 => ⟨![120000, 120000], ![76, 77]⟩
  | 21 => ⟨![120000, 120000], ![59, 60]⟩
  | 22 => ⟨![120000, 120000], ![41, 41]⟩
  | 23 => ⟨![120000, 120000], ![22, 22]⟩
  | 24 => ⟨![120000, 120000], ![1, 2]⟩
  | 25 => ⟨![120000, 120000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 368
  | 2 => 364
  | 3 => 360
  | 4 => 356
  | 5 => 350
  | 6 => 346
  | 7 => 342
  | 8 => 336
  | 9 => 330
  | 10 => 324
  | 11 => 318
  | 12 => 312
  | 13 => 304
  | 14 => 294
  | 15 => 283
  | 16 => 264
  | 17 => 239
  | 18 => 213
  | 19 => 183
  | 20 => 152
  | 21 => 118
  | 22 => 81
  | 23 => 43
  | 24 => 2
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
  block! 2305,3,0x1b72a982fd527cf4a7f800200,0x1b72aa8349c52060fc4a34480,(more! 0x17b4b2fe9b175ad732a97b0a0,0x17b7aa80ce1325355ab562fc0,(more! 0x3af3a2f0835e871a3ad643c0,0x3acc0104a9905f864932e0e0,(last! 0xec0ae5df51a96db8234be0,0xe4d356671470ad596c2bc0)))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 2 (rectWitness 2) :=
  block! 2309,3,0x1b72a982fd527cf4a7f800200,0x1b72aa8349c52060fc4a34480,(more! 0x17b9b36288000c082ec606720,0x17bcaada22fc46206217eaf80,(more! 0x3aa05908a6b21b0d3660fd80,0x3a788c4afccaeeeb41d0a8a0,(last! 0xef5bce41b7b85f782fe6a0,0xe84fbb56c24769811b4740)))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 3 (rectWitness 3) :=
  block! 2312,3,0x1b72a982fd527cf4a7f800200,0x1b72aa8349c52060fc4a34480,(more! 0x17bed6caf4567c0d588168da0,0x17c1ce3619b5d71e24d0656c0,(more! 0x3a4c2af1cba00e34ada57180,0x3a242ec829410936af26fee0,(last! 0xf16905bee6845c169d2360,0xea8d284c03fefa08e693c0)))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 4 (rectWitness 4) :=
  block! 2315,3,0x1b72a982fd527cf4a7f800200,0x1b72aa8349c52060fc4a34480,(more! 0x17c41d50249fb5c62304398e0,0x17c714acd4f88f7116cc10260,(more! 0x39f72ac1e620c5da9c41a080,0x39cefaec08c047b7884db940,(last! 0xf21f9749394ef660945580,0xeb78508210b2a080618300)))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 5 (rectWitness 5) :=
  block! 2329,4,0x1bfb6c75cb3636c928f800200,0x1bfb6d7617a8da357d4a34480,(more! 0x183689d2324e570af97c791a0,0x18399096a455bdd4785d24880,(more! 0x3b225cb8bd3732a669ea2000,0x3af9bb639c8075fad23279a0,(last! 0x12bd6d4e5c8a5104fb7d460,0x124ad4a4579a0f6dda917c0)))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 6 (rectWitness 6) :=
  block! 2332,4,0x1bfb6c75cb3636c928f800200,0x1bfb6d7617a8da357d4a34480,(more! 0x183ca32416674706c5b0607e0,0x183fa9d229c848231a682a7c0,(more! 0x3ac5f5b79370384566f4de00,0x3a9d0ce6b934a274a533a3e0,(last! 0x126ea3b688b193950a33a20,0x12009994e79c5d6fec9b400)))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 7 (rectWitness 7) :=
  block! 2345,4,0x1c810a8f277ea2c7dbf800200,0x1c810b8f73f14634304a34480,(more! 0x18afdd6c18c3f9efc6cd24420,0x18b2f2fdcae8f3f7fe6f61200,(more! 0x3bc4625434f829277f7da100,0x3b9ac8063b468559c5475ca0,(last! 0x14f0b85c1f6f9e56ef997e0,0x147f0e5ff2735951a525140)))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 8 (rectWitness 8) :=
  block! 2351,5,0x1c810a8f277ea2c7dbf800200,0x1c810b8f73f14634304a34480,(more! 0x18b4fde45666c9e114d8f9880,0x18b81378a200353911b757720,(more! 0x3b73de50e2c2b218cc352f80,0x3b4a03a4284cc2805f353740,(last! 0x14d3d6211d5a7775bb5eec0,0x14662eef86c9a7229580fa0)))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 9 (rectWitness 9) :=
  block! 2357,5,0x1c810a8f277ea2c7dbf800200,0x1c810b8f73f14634304a34480,(more! 0x18ba65fcda77e1e650d338260,0x18bd7b8fd4aa3fd4301d7c1c0,(more! 0x3b21d26afa4f5cd25481a940,0x3af7b27ee0ae8673a5fa9d20,(last! 0x1488e630063177867017080,0x141f93db901debbd2495100)))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 10 (rectWitness 10) :=
  block! 2372,5,0x1d0383cf122bc0f0c0f800200,0x1d0384cf5e9e645d154a34480,(more! 0x192bbb9e5e5b7b1147d25f920,0x192edfc993ffbe8dee00b4b80,(more! 0x3c13bf5ae9710e350c8fdb80,0x3be8d60b8ced859ccc09b7c0,(last! 0x168c4796e1d911c4008ff40,0x16211d6f6aec96b3245c740)))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 11 (rectWitness 11) :=
  block! 2389,6,0x1d82d8358b3d9143d7f800200,0x1d82d935d7b034b02c4a34480,(more! 0x199ba1e0af267ed24014cfe60,0x199ed441047251c79881e4580,(more! 0x3cf3b07ae531b8349b9df580,0x3cc7ecc31169eb16228da600,(last! 0x17fc0c1b9bb0031a5528ec0,0x17907cc4855da71b8676ec0)))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 12 (rectWitness 12) :=
  block! 2405,7,0x1dff07c292b413c120f800200,0x1dff08c2df26b72d754a34480,(more! 0x1a0a2a901835b0cd4eb100fa0,0x1a0d6abf5cc63adbeee9f45c0,(more! 0x3dc20bed80b1f27d4e4a4f40,0x3d955f033a317d1589e6ae80,(last! 0x18c0f7c0ec9f8cd20ebf780,0x18565558ed0a3a945cc4b00)))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 13 (rectWitness 13) :=
  block! 2425,7,0x1e781276288f48689bf800200,0x1e7813767501ebd4f04a34480,(more! 0x1a75e7515836badf7bb864a20,0x1a793509f199da112c04b42c0,(more! 0x3e8e75f69f0e764dc9b0a1c0,0x3e60e16ddc5fe6cb7c763000,(last! 0x1943e88748ce79c3a7d3cc0,0x18da5d7cab471ebd92f2fc0)))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 14 (rectWitness 14) :=
  block! 2466,9,0x217ff80bee8227cac461b1200,0x217ff916e8c912529577a2880,(more! 0x1d1290eab33c3232b11e9a960,0x1d16342ea60af00e78d168260,(more! 0x44f6ec07ac648f216b9511c0,0x44c4e0d9c3f45f0c5c81c100,(last! 0x1e00dc72daf9b747659cbc0,0x1d8a37dfdc4fd482f59b2c0)))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 15 (rectWitness 15) :=
  block! 2646,15,0x2aae3dade6af39053461b1200,0x2aae3eb8e0f6238d0577a2880,(more! 0x24d853f691cf4edaae6185d40,0x24dcfe0289d0631cb8bd6a700,(more! 0x5a07fe37c95ea82490678fa0,0x59c9dc5a82bf5c636bb2c880,(last! 0x356d4fe9f0b6502bf72f340,0x34b44885b007822dede52c0)))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 16 (rectWitness 16) :=
  block! 2607,14,0x27546d4bd7c3267cb0f800200,0x27546e4c2435c9e9054a34480,(more! 0x22088698c9d0a3fae2e881a80,0x220cd190e697e3dea1e33ec40,(more! 0x5230470a6524ba80cb4ca900,0x51f62289cad2dd58ed97f1c0,(last! 0x28e5e100baf115f24ee0fe0,0x284af6698b1179955a0b760)))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 17 (rectWitness 17) :=
  block! 2572,13,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x22145a9607ac07feef8351b40,0x2218a583486dce9328e1ad180,(more! 0x51e126153869119f5bd38440,0x51a673f3f1b6fbe62e23aaa0,(last! 0x2392e56c6748720a4c2d8e0,0x2300dfc14c3ea881eb6d1e0)))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 18 (rectWitness 18) :=
  block! 2541,12,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x221ed9b393ec2621a135e1480,0x22232452a11613bcade425aa0,(more! 0x518b3d9a5fd43c62694fbd20,0x514ff8f5011f62ec030e20c0,(last! 0x1e771ff76383453733f8000,0x1dee9130d34ceea3f71fa40)))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 19 (rectWitness 19) :=
  block! 2513,11,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x2227d4dbd7dc7dbe062084a60,0x222c1f452cc86188bda2bb520,(more! 0x514461df4969151fb646c0c0,0x51088f69774b2241cbce4700,(last! 0x19e5de285ddb874768bace0,0x1966619f8f1dd31a776bb60)))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 20 (rectWitness 20) :=
  block! 2488,10,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x2230cde0e8974766b5ddf9ac0,0x22351802e362121440a55ba40,(more! 0x50f976de37f40db8be559060,0x50bd0d9bae476a9fe7a9c240,(last! 0x159ed10c3d08d108a09b9a0,0x152908f237f955c1532ec00)))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 21 (rectWitness 21) :=
  block! 2465,9,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x2238e1adaf621cc9eae63c6a0,0x223d2b9315348f5dfd9792380,(more! 0x50b59cd67cb356e0acbdfd20,0x50789a6b417e9176248ee120,(last! 0x11c893c8955744902922440,0x115c9abb5e42d295fc93c00)))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 22 (rectWitness 22) :=
  block! 2445,8,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x224029772c26745694bd3af80,0x22447329c8b034132af796ce0,(more! 0x5077a3ce7377d0724810b700,0x503a0476ee210a8075e30ca0,(last! 0xe5d4ac18ce28fc56a03560,0xdfb52dc678dcddd5110f20)))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 23 (rectWitness 23) :=
  block! 2426,7,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x22476d744c81a49506c883780,0x224bb6e7cc767f5de3d44ba20,(more! 0x50349c14ef3e7e46b4db4ac0,0x4ff657179aeb916c4b5169c0,(last! 0xb4c32e1376b8fde5f07fe0,0xaf4d4ab8287519ff1ab7e0)))

private theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 24 (rectWitness 24) :=
  block! 2409,7,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x224df7f88abaf0a773f542ca0,0x2252413788d0e922e4275f420,(more! 0x4ff6494433462c40acea0360,0x4fb75b6ef26a1a313b3bde40,(last! 0x8a601bcd5c407f18056740,0x8596563287d5b1786f8f20)))

private theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2356 25 (rectWitness 25) :=
  block! 2393,6,0x2755ffb89090cd6797f800200,0x275600b8dd0370d3ec4a34480,(more! 0x22605359d3efe5c6c404f5ec0,0x22649aef1aaf994f25b797b80,(more! 0x4f05a7fab482d887195a6340,0x4ec5dad305d876f0a63530a0,(last! 0x5e5c2dd7d78c3cc55dacc0,0x5a8d551b934cec26e1c300)))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 25) :
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

theorem witness_guards {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 25) :
    (rectWitness E).U 1 ≤ (rectWitness E).U 0 ∧
      (rectWitness E).U 0 + (rectWitness E).U 1 ≤ T.shape.U := by
  interval_cases E <;> decide

theorem paid_order {E : ℕ} (hl : 1 ≤ E) (hu : E < 25) :
    (rectWitness E).order 0 ≤ (rectWitness E).order 1 ∧
      (rectWitness E).order 1 ≤ (rectWitness E).order 0 + 1 ∧
      (rectWitness E).order 0 + (rectWitness E).order 1 = paidCap E + 1 := by
  interval_cases E <;> decide

theorem rect_bounds {h E : ℕ} (hl : 2356 ≤ h) (hu : h ≤ 2394)
    (hel : 1 ≤ E) (heu : E ≤ 25) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
