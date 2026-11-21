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
  | 1 => ⟨![181500, 58500], ![222, 223]⟩
  | 2 => ⟨![180000, 60000], ![220, 221]⟩
  | 3 => ⟨![180000, 60000], ![217, 218]⟩
  | 4 => ⟨![180000, 60000], ![215, 216]⟩
  | 5 => ⟨![180000, 60000], ![213, 213]⟩
  | 6 => ⟨![178500, 61500], ![210, 211]⟩
  | 7 => ⟨![178500, 61500], ![207, 208]⟩
  | 8 => ⟨![177000, 63000], ![205, 205]⟩
  | 9 => ⟨![177000, 63000], ![202, 203]⟩
  | 10 => ⟨![175500, 64500], ![199, 200]⟩
  | 11 => ⟨![174000, 66000], ![196, 196]⟩
  | 12 => ⟨![174000, 66000], ![192, 193]⟩
  | 13 => ⟨![171000, 69000], ![189, 189]⟩
  | 14 => ⟨![169500, 70500], ![185, 186]⟩
  | 15 => ⟨![166500, 73500], ![180, 181]⟩
  | 16 => ⟨![159000, 81000], ![175, 176]⟩
  | 17 => ⟨![121500, 118500], ![166, 167]⟩
  | 18 => ⟨![120000, 120000], ![156, 156]⟩
  | 19 => ⟨![120000, 120000], ![144, 144]⟩
  | 20 => ⟨![120000, 120000], ![131, 132]⟩
  | 21 => ⟨![120000, 120000], ![117, 118]⟩
  | 22 => ⟨![120000, 120000], ![102, 103]⟩
  | 23 => ⟨![120000, 120000], ![86, 87]⟩
  | 24 => ⟨![120000, 120000], ![69, 70]⟩
  | 25 => ⟨![120000, 120000], ![51, 52]⟩
  | 26 => ⟨![120000, 120000], ![32, 33]⟩
  | 27 => ⟨![120000, 120000], ![12, 13]⟩
  | 28 => ⟨![120000, 120000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

def paidCap : ℕ → ℕ
  | 1 => 444
  | 2 => 440
  | 3 => 434
  | 4 => 430
  | 5 => 425
  | 6 => 420
  | 7 => 414
  | 8 => 409
  | 9 => 404
  | 10 => 398
  | 11 => 391
  | 12 => 384
  | 13 => 377
  | 14 => 370
  | 15 => 360
  | 16 => 350
  | 17 => 332
  | 18 => 311
  | 19 => 287
  | 20 => 262
  | 21 => 234
  | 22 => 204
  | 23 => 172
  | 24 => 138
  | 25 => 102
  | 26 => 64
  | 27 => 24
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

private theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 1 (rectWitness 1) :=
  block! 2276,3,0x1d0375cae3e6d104247925f00,0x1d0376cb3059747078cb5a180,(more! 0x18d4b5724bd1f00fe1b398720,0x18daf92ceb7684e71a43ab3c0,(more! 0x41d8a58c6e6d4a6020bc3d40,0x417d83c84f25882cb2b52e80,(last! 0x113adbfef8757eff0a5f740,0x10b3d2914f0bc2e63c16720)))

private theorem r2 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 2 (rectWitness 2) :=
  block! 2285,3,0x1d82ca315cf8a1573b7925f00,0x1d82cb31a96b44c38fcb5a180,(more! 0x193ebfbdbb5b5a06c75805520,0x19451fe4b211415ac66335fc0,(more! 0x42fa6efa2633a2d52736ba60,0x429e08976cc7ee5330d506c0,(last! 0x146a9e1c25ec655d62789e0,0x13db9c8da53909a599b6ae0)))

private theorem r3 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 3 (rectWitness 3) :=
  block! 2289,3,0x1d82ca315cf8a1573b7925f00,0x1d82cb31a96b44c38fcb5a180,(more! 0x1942074a0a2abd8f21bccbbe0,0x194867893ea53653cd9f33cc0,(more! 0x42bf09338b9e84ba3bc93500,0x42627a96b361f0eb189e4e80,(last! 0x14d39dc790fe5c2d1a3c340,0x144706f671a690beb928220)))

private theorem r4 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 4 (rectWitness 4) :=
  block! 2291,3,0x1d82ca315cf8a1573b7925f00,0x1d82cb31a96b44c38fcb5a180,(more! 0x19470b67972672368228a22e0,0x194d6b84fc07d95a970cd5ca0,(more! 0x4272df3c0d53fde0be6086e0,0x42160b82eee2bb77edcae300,(last! 0x14956d6cedfd6b3e43af300,0x140d4a8973451a39392a500)))

private theorem r5 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 5 (rectWitness 5) :=
  block! 2295,4,0x1d82ca315cf8a1573b7925f00,0x1d82cb31a96b44c38fcb5a180,(more! 0x194ad598ba74361d8877162c0,0x195135c0631001100cafc81e0,(more! 0x4232fae932e592d0a2c99c40,0x41d5f3cda690fdf19d3521c0,(last! 0x14c5bd865326ff3fecca800,0x1440c618812380245f9dfe0)))

private theorem r6 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 6 (rectWitness 6) :=
  block! 2305,4,0x1dfef9be646f23d4847925f00,0x1dfefabeb0e1c740d8cb5a180,(more! 0x19b41323337803873387419c0,0x19ba8ef3a135793cccff39f80,(more! 0x4339b1fc1c3261ee17d38160,0x42db366b6438a8f61e7f5ac0,(last! 0x1750228857d5da72eec6900,0x16c6f315b824cc885851b60)))

private theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 7 (rectWitness 7) :=
  block! 2309,4,0x1dfef9be646f23d4847925f00,0x1dfefabeb0e1c740d8cb5a180,(more! 0x19b85481d80a211c9bfe03220,0x19bed0579299d7310f07f5dc0,(more! 0x42f6f9de3d43c735420c8ec0,0x42983ddf2319876c588d8080,(last! 0x1736f7f311322a76f07b580,0x16b1c9b899bf2f45f2d38a0)))

private theorem r8 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 8 (rectWitness 8) :=
  block! 2321,5,0x1e780471fa4a587bff7925f00,0x1e78057246bcfbe853cb5a180,(more! 0x1a1f206f42fe9e5c043a1f700,0x1a25b7550306d69d64de8f540,(more! 0x43f30372d451e714329b73e0,0x4392cbd5416e17ad7c3b4d00,(last! 0x19b3fe75876ed83491a5fc0,0x192ba1f3644a478b441e7e0)))

private theorem r9 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 9 (rectWitness 9) :=
  block! 2324,5,0x1e780471fa4a587bff7925f00,0x1e78057246bcfbe853cb5a180,(more! 0x1a2555c4a2d52ab0d0b07e620,0x1a2bec6f689d318b2d2fc27c0,(more! 0x439fdf888e2b495714442b40,0x433f4aa2182d7ad0a663a280,(last! 0x18b7812b1af09a93da31980,0x183534e6676a9a808c34260)))

private theorem r10 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 10 (rectWitness 10) :=
  block! 2336,5,0x1eedea4c1e8a3f4dac7925f00,0x1eedeb4c6afce2ba00cb5a180,(more! 0x1a8ab096c516705f564de2b40,0x1a9161911a161583e86f76600,(more! 0x448b00768ec7d8e0702371e0,0x4428e0085b0f7ae574617e40,(last! 0x1a909463bfdde471f511800,0x1a0cd7f9c4720afcf70ad60)))

private theorem r11 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 11 (rectWitness 11) :=
  block! 2350,6,0x1f60ab4cd12ed8498b7925f00,0x1f60ac4d1da17bb5dfcb5a180,(more! 0x1aed2f4f28356c079f7d430c0,0x1af3fa0ac50e565c68657a000,(more! 0x45716176816413f7e4c97ca0,0x450dba62b8bfe30e1c9cff40,(last! 0x1c6643a42c3e21107ba9f20,0x1be155737fcdcc6a1ab64e0)))

private theorem r12 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 12 (rectWitness 12) :=
  block! 2355,6,0x1f60ab4cd12ed8498b7925f00,0x1f60ac4d1da17bb5dfcb5a180,(more! 0x1af35ad8a99b23b20a1c498e0,0x1afa25708a587accef2392d00,(more! 0x45231248a61f4f9255ad5ba0,0x44bf0b772b0d9535ef239f00,(last! 0x1b21ae8f714e48f0788f840,0x1aa2e027ac9c5d525743200)))

private theorem r13 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 13 (rectWitness 13) :=
  block! 2379,7,0x203cbec1e1a620bfdf7925f00,0x203cbfc22e18c42c33cb5a180,(more! 0x1bae45579b1f58810c460bd40,0x1bb5411dd0d2ce37b67763680,(more! 0x47089d5603601026b6249e40,0x46a1cbb3c2dc306891e1a880,(last! 0x1defc3a7c92992610d16500,0x1d6cbc5ea8f9bea607b3980)))

private theorem r14 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 14 (rectWitness 14) :=
  block! 2393,7,0x20a611363f78d03a547925f00,0x20a612368beb73a6a8cb5a180,(more! 0x1c0cd03770dc5918524c00cc0,0x1c13e33e5a88b598bc90b19c0,(more! 0x47bab748004a3be1e6d30360,0x4752476bd0b0f3fbb175c3c0,(last! 0x1d9d6877cdcfd89c5369c20,0x1d1d27b0198c042a616cc40)))

private theorem r15 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 15 (rectWitness 15) :=
  block! 2420,8,0x216f4792a64c45add47925f00,0x216f4892f2bee91a28cb5a180,(more! 0x1cb9e230fe2cd0886230bc8e0,0x1cc1223459db888dae3e7b180,(more! 0x49694d2b692d44559e0d7880,0x48fe2d62f1dc2d7a2aa66cc0,(last! 0x1ed296d75028488a8997520,0x1e509a208b2161b362b4ee0)))

private theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 16 (rectWitness 16) :=
  block! 2474,10,0x232f4a9c633f1930ff7925f00,0x232f4b9cafb1bc9d53cb5a180,(more! 0x1e36c299b4966ae4728664660,0x1e3e667dc0cf12af309bac400,(more! 0x4d6999c0e5c54d9b7c6123e0,0x4cf8d2b48bc010a2e49ded00,(last! 0x21f304c5e1b9ef3e808efc0,0x21682fb9c2af3419576e620)))

private theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 17 (rectWitness 17) :=
  block! 2572,14,0x27545f47a97e3690147925f00,0x27546047f5f0d9fc68cb5a180,(more! 0x21b58a88aca671e65cc64ebc0,0x21be1b1c114ed16db5b347120,(more! 0x5749c8f08419a03d2b578180,0x56cc14312aed3b551ed06180,(last! 0x2a38f3234d7388a1874c5e0,0x2991a7947db865cad07ade0)))

private theorem r18 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 18 (rectWitness 18) :=
  block! 2541,13,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21c007c3881a9057063d8e9c0,0x21c89848d4cd6a5da477b2740,(more! 0x5703814f69792cedcf191a20,0x56854aaa0a09f2c44e8afb80,(last! 0x25b46333b65058bc01e65e0,0x251544bc577c3f437c9ef80)))

private theorem r19 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 19 (rectWitness 19) :=
  block! 2513,12,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21c83ddc203e816115f1bbac0,0x21d0ce0f627d720490a55b2a0,(more! 0x56c2e289d6eebdf6e445d320,0x564434583b55684d44090540,(last! 0x2185f716849c8374d46fc00,0x20eea317b06e5c1c3cd38e0)))

private theorem r20 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 20 (rectWitness 20) :=
  block! 2488,11,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21d0660a773bdee8e6f0bc8e0,0x21d8f5cef7961841812733320,(more! 0x56810958b1f471c3ccdc37a0,0x5601e045efd92c99d07b6280,(last! 0x1d7e2a4bf0fdc076e1da0c0,0x1ceef35cdd98725bf685020)))

private theorem r21 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 21 (rectWitness 21) :=
  block! 2465,10,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21d7b1658dd7f7b7ff97dc480,0x21e040d2019cba2279a29ee20,(more! 0x564766b8872db6ea0ba21980,0x55c7c51294755e52317b95e0,(last! 0x19cbf447efbbf154f5b58c0,0x19449e699ddfdb66e19e000)))

private theorem r22 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 22 (rectWitness 22) :=
  block! 2445,9,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21de92930013df4885233b420,0x21e721a63e5e29b7e63a9fd20,(more! 0x561080b58f4f916606454880,0x5590641acbb85734bc8c9c00,(last! 0x16589e1af07adacf9f123e0,0x15d9509f6f75818113481a0)))

private theorem r23 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 23 (rectWitness 23) :=
  block! 2426,8,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21e50e9c9ed1e33d9f28a55e0,0x21ed9d56f50feebb02f3da7c0,(more! 0x55dbed5c4acc10529d931420,0x555b528b8726199ce79982a0,(last! 0x132592cd0ad6aaf04a3b380,0x12ae818446023395a820140)))

private theorem r24 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 24 (rectWitness 24) :=
  block! 2409,8,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21eb2aae3646b5cf446cfee00,0x21f3b91101bfc339ea7108ee0,(more! 0x55a9472596938dbe76b0ab00,0x55282a3a535652ef9926b940,(last! 0x1033d920a66ac61926e6100,0xfc540fb9509f2bc8f25820)))

private theorem r25 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 25 (rectWitness 25) :=
  block! 2393,7,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21f0ebf6367468025e3159940,0x21f97a03c48ecaeff481575e0,(more! 0x55782df32268f1daa1ec7420,0x54f68aa55c585a99e7fa9c20,(last! 0xd842401438ad51c7528460,0xd1e4734fd61f034d46e460)))

private theorem r26 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 26 (rectWitness 26) :=
  block! 2379,7,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21f6578d6b49f242236d23ec0,0x21fee548b35cbec9c2806c000,(more! 0x5548484e26e6af5590b6ca20,0x54c61a3d4bde894cb9c351a0,(last! 0xb16d6d323512a1adf7d5a0,0xab9f870ac905730795da00)))

private theorem r27 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 27 (rectWitness 27) :=
  block! 2365,6,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x21fb726588a20a4e415d93fa0,0x2203ffd1fc90856c60b0fa140,(more! 0x551944c3ca3db9bc2d495080,0x549687ca8616963ccf7e3980,(last! 0x8ec00c6eff4d9fff3adb60,0x8985fae9937cb7328bf0e0)))

private theorem r28 : BlockChecks T.shape T.nodeRows T.poleMoment 2342 28 (rectWitness 28) :=
  block! 2352,6,0x2755f1b4624bdd7afb7925f00,0x2755f2b4aebe80e74fcb5a180,(more! 0x220460897e373953fde1fbc20,0x220ceca63c6fca9ab301d16a0,(more! 0x54af3d8765c72c505bb96720,0x542bde7856076f699edf7400,(last! 0x6ce5738dce432cf968a3e0,0x6862c7bce11df83e99e1e0)))

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2342 E (rectWitness E) := by
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

theorem rect_bounds {h E : ℕ} (hl : 2342 ≤ h) (hu : h ≤ 2414)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
