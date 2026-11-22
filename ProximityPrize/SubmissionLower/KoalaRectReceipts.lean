import ProximityPrize.SubmissionLower.KoalaRectArithmetic

set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open HighCore82258 (terminal agreement)
open HighCore82258TerminalArithmetic (Parts)

private abbrev T := terminal .h2367
def rectWitness : ℕ → RectArgs
  | 1 => ⟨![276931, 38069], ![234, 235]⟩
  | 2 => ⟨![276556, 38444], ![232, 233]⟩
  | 3 => ⟨![276424, 38576], ![230, 231]⟩
  | 4 => ⟨![276241, 38759], ![227, 228]⟩
  | 5 => ⟨![275903, 39097], ![225, 226]⟩
  | 6 => ⟨![275753, 39247], ![222, 223]⟩
  | 7 => ⟨![275221, 39779], ![220, 221]⟩
  | 8 => ⟨![274889, 40111], ![217, 218]⟩
  | 9 => ⟨![274581, 40419], ![214, 215]⟩
  | 10 => ⟨![274085, 40915], ![211, 212]⟩
  | 11 => ⟨![273410, 41590], ![208, 209]⟩
  | 12 => ⟨![272771, 42229], ![205, 206]⟩
  | 13 => ⟨![272177, 42823], ![201, 202]⟩
  | 14 => ⟨![271243, 43757], ![197, 198]⟩
  | 15 => ⟨![269993, 45007], ![193, 194]⟩
  | 16 => ⟨![268071, 46929], ![189, 190]⟩
  | 17 => ⟨![264769, 50231], ![183, 184]⟩
  | 18 => ⟨![159653, 155347], ![166, 167]⟩
  | 19 => ⟨![158110, 156890], ![134, 135]⟩
  | 20 => ⟨![157500, 157500], ![100, 100]⟩
  | 21 => ⟨![157500, 157500], ![63, 63]⟩
  | 22 => ⟨![157500, 157500], ![24, 24]⟩
  | 23 => ⟨![157500, 157500], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 468
  | 2 => 464
  | 3 => 460
  | 4 => 454
  | 5 => 450
  | 6 => 444
  | 7 => 440
  | 8 => 434
  | 9 => 428
  | 10 => 422
  | 11 => 416
  | 12 => 410
  | 13 => 402
  | 14 => 394
  | 15 => 386
  | 16 => 378
  | 17 => 366
  | 18 => 332
  | 19 => 268
  | 20 => 199
  | 21 => 125
  | 22 => 47
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 1 (rectWitness 1) :=
  block! 1485,5,0x83d379a3a9c9f897d69db800,0x83d37d9a2e6fea174d41bc00,(more! 0x801e7667043602d82ae18b40,0x802e172a3a1e6883fe76ac40,(last! 0x3b5037367304d65ce1668c0,0x3a592d0f3adaebb552a9c80))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 2 (rectWitness 2) :=
  block! 1488,5,0x84f16e852c2f4dd7af9db800,0x84f1727bb0d53f572641bc00,(more! 0x81387b1c705df3c074e73360,0x81481e1107f77f12f046cf60,(last! 0x3b8fe5b9f4b6bb314ce4080,0x3a98be8c12dd92df737de80))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 3 (rectWitness 3) :=
  block! 1490,6,0x8555dfdb97dd5afd9f9db800,0x8555e3d21c834c7d1641bc00,(more! 0x81a7ad0124badf59e1111b20,0x81b734f7e2301c03b0035820,(last! 0x3ae4b17b1b1064aa0432ca0,0x39ef3c5b86392f26ecc8ec0))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 4 (rectWitness 4) :=
  block! 1493,6,0x85e0f0b5731d1b628e9db800,0x85e0f4abf7c30ce20541bc00,(more! 0x8235b5a1a07590c9c4c3a480,0x82452d03f06680da7f5a8a00,(last! 0x3ab3d25075a77e564c6d700,0x39bf693b05abe5a4a8d5a80))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 5 (rectWitness 5) :=
  block! 1496,6,0x86e13b24339b241a3e9db800,0x86e13f1ab8411599b541bc00,(more! 0x833804bb47ad49896f8f9780,0x83477763df63ea416c35b200,(last! 0x3a94b414579e04cc5e56b00,0x39a09c1840c7362a4199100))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 6 (rectWitness 6) :=
  block! 1499,6,0x8752bc4794859204de9db800,0x8752c03e192b83845541bc00,(more! 0x83b0bb56bd411c6ba5ff0d80,0x83c0185ce3a9deb7fa308680,(last! 0x3a204f301d1d0bc929edf00,0x392d939e40df5b5398c3000))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 7 (rectWitness 7) :=
  block! 1503,6,0x88e4234637ae07cf169db800,0x88e4273cbc53f94e8d41bc00,(more! 0x853d963bcaeb90914edde580,0x854d01d5c5470bb64beb5000,(last! 0x3a6aaefacf4420e8e4733c0,0x397712bfcb43b325c7ad200))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 8 (rectWitness 8) :=
  block! 1507,6,0x89ddb844e70d3b769e9db800,0x89ddbc3b6bb32cf61541bc00,(more! 0x8638b92609fa04e8d17ad080,0x864821079e0a9de2952c7080,(last! 0x3a51365c81559e0c7a1abc0,0x395ddad0fc10428c3847080))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 9 (rectWitness 9) :=
  block! 1511,6,0x8ac4a124229ed254169db800,0x8ac4a51aa744c3d38d41bc00,(more! 0x872425e537bae1f6acbeb080,0x873386728d996a91c5672900,(last! 0x3a08a2608b031bf1e80cc00,0x3915c0e4fb752b9acd2b900))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 10 (rectWitness 10) :=
  block! 1516,7,0x8c373578e7fd58c6f69db800,0x8c37396f6ca34a466d41bc00,(more! 0x8894dd36faec2c3eae3fd900,0x88a448dfc268883517f8c000,(last! 0x3a266e50c9ddef6488bf600,0x3932e2dfd5854e421c47a00))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 11 (rectWitness 11) :=
  block! 1522,7,0x8e2cff8f32327d91eb9db800,0x8e2d0385b6d86f116241bc00,(more! 0x8a83d154a00ac1f1e51da420,0x8a93589a40bfbd2c4f4f2820,(last! 0x3a942b0102785081fb42f20,0x399ef04e09922bb5e082900))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 12 (rectWitness 12) :=
  block! 1528,7,0x900557420f20e2b7569db800,0x90055b3893c6d436cd41bc00,(more! 0x8c5a16e9faa40a3701acaf80,0x8c69b3e4da1b2f7c31065480,(last! 0x3ab623c9595f215a3c50e80,0x39bf97bcd32733f620c3400))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 13 (rectWitness 13) :=
  block! 1535,7,0x91ba13fa9aaf10974e9db800,0x91ba17f11f550216c541bc00,(more! 0x8e0d10a6e20d5eef2e438c80,0x8e1cc14875a1f1d3eb5a6400,(last! 0x3ad112cf1364617ad395640,0x39d9555933e016e37eb8800))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 14 (rectWitness 14) :=
  block! 1544,8,0x94643c79cee7928b269db800,0x94644070538d840a9d41bc00,(more! 0x90acba743203dcb010ba9c00,0x90bc9d2157703a698eb8ed80,(last! 0x3b786b7a3db66df4f47de80,0x3a7d9b835d4dfd8b763a080))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 15 (rectWitness 15) :=
  block! 1555,8,0x97ec75b56ba930d5de9db800,0x97ec79abf04f22555541bc00,(more! 0x9424de114a4cfffd9f0bcc00,0x94350cc4094941e1d1105180,(last! 0x3c7a275701e2aad40f45b80,0x3b7aa9fece3930b8517f940))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 16 (rectWitness 16) :=
  block! 1570,9,0x9d474ce81fa050440e9db800,0x9d4750dea44641c38541bc00,(more! 0x9961248e5bee20385424a780,0x9971d728061d04780b50d380,(last! 0x3e6507f27caccec374adc00,0x3d5d69104a0946ace94d500))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 17 (rectWitness 17) :=
  block! 1596,10,0xa64340a53ca9b058ae9db800,0xa643449bc14fa1d82541bc00,(more! 0xa2199b0e6aa5f60b944da600,0xa22b49747ecbda2c3ea5a800,(last! 0x429b7731cf2bb4fe166cc00,0x41844b87bb239b859ff5e00))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 18 (rectWitness 18) :=
  block! 1671,12,0x135ec5c2c4abdffa4f69db800,0x135ec6022cf63f1246d41bc00,(more! 0x12c379453d40d0dc048dff900,0x12c5b0c592ff8564d5cfd7300,(last! 0x9b4cbf5d657570722532400,0x991bfb8bc5ff52c698b8c00))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 19 (rectWitness 19) :=
  block! 1653,12,0x135f9fde534aed1be8b9db800,0x135fa01dbb954c33e0241bc00,(more! 0x12c8efdc56d9b8c54a4c1a9e0,0x12cb2673366c3e39646aaf4a0,(last! 0x96b05963ad22dcc52867540,0x94807f49b675a53c4aa0740))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 20 (rectWitness 20) :=
  block! 1636,11,0x135fb2e7a1b794c20af9db800,0x135fb3270a01f3da02641bc00,(more! 0x12cd56ca6f9660051f0434960,0x12cf8cd3735783cc60b66bb60,(last! 0x925c79d07af3918290c5c00,0x902d2d90d9d7da4368971e0))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 21 (rectWitness 21) :=
  block! 1621,10,0x135fb2e7a1b794c20af9db800,0x135fb3270a01f3da02641bc00,(more! 0x12d1619cae077c72a7e0378c0,0x12d39787168b5fe211f285600,(last! 0x8e518180713031d33442100,0x8c2253d0014be3026d03300))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 22 (rectWitness 22) :=
  block! 1608,10,0x135fb2e7a1b794c20af9db800,0x135fb3270a01f3da02641bc00,(more! 0x12d53c9bdc8c7d46d78e78e80,0x12d772b6a45b2b23265555be0,(last! 0x8a7741892ca1ef670c2fb40,0x8847e38750e7ca7dbd7dae0))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2414 23 (rectWitness 23) :=
  block! 1596,10,0x135fb2e7a1b794c20af9db800,0x135fb3270a01f3da02641bc00,(more! 0x12db543fedd3864e23345f9a0,0x12dd86b02f00ce4b10e73f1c0,(last! 0x8485b375d9caf7fb1a8e400,0x825a040c8f44c06dfce18c0))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 23) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2414 E (rectWitness E) := by
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

theorem witness_guards {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 23) :
    (rectWitness E).U 1 ≤ (rectWitness E).U 0 ∧
      (rectWitness E).U 0 + (rectWitness E).U 1 ≤ T.shape.U := by
  interval_cases E <;> decide

theorem paid_order {E : ℕ} (hl : 1 ≤ E) (hu : E < 23) :
    (rectWitness E).order 0 ≤ (rectWitness E).order 1 ∧
      (rectWitness E).order 1 ≤ (rectWitness E).order 0 + 1 ∧
      (rectWitness E).order 0 + (rectWitness E).order 1 = paidCap E + 1 := by
  interval_cases E <;> decide

theorem rect_bounds {h E : ℕ} (hl : 2414 ≤ h) (hu : h ≤ 2535)
    (hel : 1 ≤ E) (heu : E ≤ 23) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
