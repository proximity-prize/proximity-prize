import ProximityPrize.SubmissionLower.HighCore82209TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209Terminal

open HighCore82209
open HighCore82209TerminalArithmetic
open K1_14 (Shape)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs =>
    BlockChecks ({t.shape with U := g.slots}) t.nodeRows t.poleMoment h e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

private theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc : GradeChecks t h e gs) (i : Fin gs.length) :
    BlockChecks {t.shape with U := (gs.get i).slots} t.nodeRows t.poleMoment h (i.val+e) ((gs.get i).seedCap+1) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · simpa [GradeChecks] using hc.1
    · have h' := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h'

set_option quotPrecheck false
local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 239942) N P 2395 23 0 :=
  block! 2675,1,0x6a216a3556d68161886ec2b00,0x6a216d343006e7547ca3d9c00,(more! 0x54322349b3c8f7535c1e22300,0x543d2ac96517a4d39104bb700,(more! 0x115ed5782dac385d3b60a9600,0x11676e3960a528ec9b9814400,(more! 0x4913f98c4d779349387bbf80,0x47dc4613e6416d0197050b80,(last! 0x0,0x0))))
private theorem r1 : BlockChecks (S 183418) N P 2395 1 358 :=
  block! 2731,4,0x3e097e56b21496ad203628f00,0x3e0980a0e54215a88e9806c00,(more! 0x3049a95c656e05466bae4e620,0x30501307067b5464526fbc700,(more! 0xa19a1a44b26e6d7f2b3b8e80,0xa1eabafcf08aba87356babc0,(more! 0x3a2c78b8754acfe1ed877b60,0x39789ea79dbdb3fb527030a0,(last! 0x36bca894a5cc9c12d3d0a0,0x34bdbe8d1456c9ac1259c0))))
private theorem r2 : BlockChecks (S 182486) N P 2395 2 353 :=
  block! 2735,4,0x3d689dc1a484c9fe8c30d7b00,0x3d68a008dd2a702d0fb33dc00,(more! 0x2fe1ae9f35108403d7e567540,0x2fe8074524949e99656141480,(more! 0x9feca684db0da29129fdfb80,0xa03c619a0c703f7a4e38d4e0,(more! 0x384a9b86adbd24ee0b961b20,0x3798a4a45d41128fc32a5680,(last! 0x37b01cf75ec08997135ba0,0x35c089c09de58fd9922980))))
private theorem r3 : BlockChecks (S 181095) N P 2395 3 348 :=
  block! 2739,4,0x3c7a082dba2f52cf91b75c800,0x3c7a0a7080c35b0d11df9a000,(more! 0x2f3efaa155bd4cdae19669340,0x2f453a145d6866216b3099600,(more! 0x9d70b2234e0fa049f9c90200,0x9dbf202a8e26bba930676640,(more! 0x360a9982792bbfd83c25e9c0,0x355b5c5a719c06482c92ef80,(last! 0x358d28389ae7f2a831f240,0x33bf08be710d122dbca580))))
private theorem r4 : BlockChecks (S 185101) N P 2395 4 342 :=
  block! 2760,5,0x3f2e1459d30b4af846856d600,0x3f2e16a96731f222b953d3800,(more! 0x31564096b2d9926bbeddae260,0x315cc8d7b2069b4c7c26e1520,(more! 0xa49e44d0df97c47269544460,0xa4f0402a01568d0483f627c0,(more! 0x388af59f9e92d29fe6dde9a0,0x37d43571948d0d68fffc9dc0,(last! 0x5401c436a03f2f2c81f5c0,0x51ab1edb0512512e1940a0))))
private theorem r5 : BlockChecks (S 187654) N P 2395 5 336 :=
  block! 2777,5,0x40ef02ea243c19842d350eb00,0x40ef0541e129d3a7ea42c9c00,(more! 0x32b9625346c168ff0347d2580,0x32c019c871406cfffa2a99300,(more! 0xa945aacb9f728def84943d00,0xa999edf56c72615f035a9000,(more! 0x39a8f33ec85d308219dcb300,0x38ed4e999a9b959b73a50f80,(last! 0x6b6b682081f53cc0d08f80,0x68c7a3e747070a890f7880))))
private theorem r6 : BlockChecks (S 187748) N P 2395 6 330 :=
  block! 2787,6,0x40ffa8793f5e2e5b6599fd100,0x40ffaad1493440d5b9cb71400,(more! 0x32d86c41968a99d83d0e429e0,0x32df255fd1eb259e50594ea40,(more! 0xa96f7a5288165b2e19e89c80,0xa9c3c432a31ff5a4dcb5a920,(more! 0x38953f44d865684449b65be0,0x37d969f8364dcef7a12fa3a0,(last! 0x6f09ec067dad764525f100,0x6c75e0b37035966526d960))))
private theorem r7 : BlockChecks (S 193653) N P 2395 7 323 :=
  block! 2818,7,0x45261725f54df5d088bb29e00,0x45261990de691d1d761aed800,(more! 0x360ed6922c02ffd1f4970c8c0,0x3615ff8740c0164968d15e520,(more! 0xb47631d7607d04ed8b09a8a0,0xb4cff3650f0641cc33bcbf40,(more! 0x3c5e6c80e7b238a72fd6a480,0x3b96cdd53052d6b6e4f98660,(last! 0x9f6ae65ccd0962867e84e0,0x9c418e19be3024ba7668a0))))
private theorem r8 : BlockChecks (S 195395) N P 2395 8 316 :=
  block! 2837,7,0x4665cad873a4827413a6e3400,0x4665cd48edfe65facbcdb1000,(more! 0x3716a7be52ce7126236dd6a40,0x371df247023b352a6b2c63e80,(more! 0xb7c563ea2dc676b0203bedc0,0xb820be4bb3c8e471328f04c0,(more! 0x3c8399d4da7f2353c7c77100,0x3bb84f095f5127bed22b8f80,(last! 0xa933e44d4110f7f35b5f80,0xa60b5b4833d5cde0f60ec0))))
private theorem r9 : BlockChecks (S 203011) N P 2395 9 308 :=
  block! 2878,9,0x4bfd1fa9585261222b414f400,0x4bfd223229d31eb3f4d721000,(more! 0x3b6d61a5d02f362dcb699aa40,0x3b7542f0c27cea25e9a91c2c0,(more! 0xc6a2372772d5f1a1d6f169c0,0xc704f0ce5ee149cbccaffc00,(more! 0x417ac4c8c6106eaf196c9d80,0x409f59c11029793619c324c0,(last! 0xdee44afa3478704b725f80,0xdb2ebb980efde4430601c0))))
private theorem r10 : BlockChecks (S 201548) N P 2395 10 300 :=
  block! 2890,9,0x4ae5ed734e01e643860be1900,0x4ae5eff7728896a76b93ab400,(more! 0x3ab25d95f488ca7688336b1c0,0x3aba214a044e766aff6287be0,(more! 0xc3b69cc911f5e2a4581a7da0,0xc417d006732420a5a59035c0,(more! 0x3ec5bafe91d6627f831d20a0,0x3ded26c2a9fcd1d6d56393c0,(last! 0xbca616025839a10100cf80,0xb973aef2e0d2fe363271e0))))
private theorem r11 : BlockChecks (S 210336) N P 2395 11 290 :=
  block! 2944,11,0x51915c06013c4697645371d00,0x51915ea63bcdc748ddd6a0400,(more! 0x3fe5a9331d0a4d984aa218820,0x3fee20c7fa1a57cd07daa4740,(more! 0xd5719635acbac891dd30cd40,0xd5db9301d289de3088bff240,(more! 0x446e0628bade021a515f81a0,0x4381eccc0205b7d93de66280,(last! 0xdb90d7c67d8c2226b2a400,0xd7ffdca63b8e2267dde1a0))))
private theorem r12 : BlockChecks (S 237758) N P 2395 12 277 :=
  block! 3077,16,0x6835519d4f4f2d792c845c300,0x683554952d9fba8ad613f7c00,(more! 0x515ccb3d28b06595f7de40040,0x5167a67663bcc64be39fecb40,(more! 0x111bc462361ac4fe73fb41060,0x1124441d19fb212c8d71c6500,(more! 0x5a7955997dfe560ba41541a0,0x594b42aecd31ec6f90a2f720,(last! 0x152ca46c2ce0e38bfd58620,0x14d7315485adae51da8a140))))
private theorem r13 : BlockChecks (S 238373) N P 2395 13 262 :=
  block! 3027,15,0x68bf6f56dd854ee3d06268e00,0x68bf7250b301e772ce9d19800,(more! 0x51f00336daf65b0f825a56060,0x51faeca01e3c7de121f28c080,(more! 0x1131e1ef288c963df8fc9f460,0x113a6b2e7aa08294d451c9f80,(more! 0x58e3889a8280a8131337ef20,0x57b317a4287fc81a6bcaf5a0,(last! 0xf51a80b9fd8002401c2f40,0xf0a8eda52e872aee8a4fc0))))
private theorem r14 : BlockChecks (S 237823) N P 2395 14 245 :=
  block! 2969,12,0x6843e64b98e447b064d1d0000,0x6843e943ac631cbc922040000,(more! 0x51b7b1084a86a1e7172706f80,0x51c28cee9b098a5ed6bbab2c0,(more! 0x111c4c7d3ec45e7c2fe1b1fe0,0x1124c99cfe8590681244750c0,(more! 0x565fb60a7e286b8b85504120,0x552fe09a1885460e11586bc0,(last! 0x9ed66ee512d6ea01fcb680,0x9b60e19831dfc7874d9f00))))
private theorem r15 : BlockChecks (S 239141) N P 2395 15 225 :=
  block! 2919,11,0x696c698fae5e98cc50e1d8e00,0x696c6c8bf835293a0145d9800,(more! 0x52c042939504cbf582e1011a0,0x52cb3d455c9c63c0864cf6960,(more! 0x114c96ae70f94c3386d1692a0,0x11552aa4542174d72b0ca9fa0,(more! 0x559a955c7502ff0efb8b0b60,0x54668d71123202f781035600,(last! 0x5e6f9fc958764ec145e000,0x5bd89dbd7abbb40e7f7d20))))
private theorem r16 : BlockChecks (S 239235) N P 2395 16 203 :=
  block! 2875,9,0x69819f4cb211583f7d66c7400,0x6981a24948d04103c4ee81000,(more! 0x52f2437913e552314435c8c60,0x52fd3fdd8906d32f41f53c500,(more! 0x114f002cc2ddfc81a708cb9c0,0x1157944ce865e25239014e6e0,(more! 0x53d80fd0d7c18cb07c1a9320,0x52a30456adb73766b377dce0,(last! 0x2daaa9f58c23e3d9cc5d00,0x2bf9d26327a940551c1300))))
private theorem r17 : BlockChecks (S 238897) N P 2395 17 179 :=
  block! 2837,7,0x6935654ccc9f8b0239e406a00,0x693568484ed430afd4583c800,(more! 0x52d65817cc3ecd3684dbf19c0,0x52e14be41b3d2ee14c60b1020,(more! 0x1141329bc9c2786cec930d4a0,0x1149bf024affda73d7edfca60,(more! 0x51cdcc7a0f85f44e0a792b40,0x5098f66d567ef73ab885a360,(last! 0xfdd227d7a71dfffc65540,0xefa5cbca551c0dbd71260))))
private theorem r18 : BlockChecks (S 239330) N P 2395 18 152 :=
  block! 2802,6,0x699710f7cf492aa1c84935700,0x699713f4b3c1df0f468560c00,(more! 0x533ed6f592d1cddd91ff2d780,0x5349d4818259d38ba36002080,(more! 0x115054266f632bd749ad29880,0x1158e766d688e20a37eb54480,(more! 0x507bb38e1c84eeeec179c680,0x4f453c267682c3e5e0edf100,(last! 0x2aa76375c2ecc216e2f80,0x26177bfdbd4c5223efe80))))
private theorem r19 : BlockChecks (S 239402) N P 2395 19 123 :=
  block! 2771,5,0x69a753028a63e31600d527f00,0x69a755ffa9c506c05fc532c00,(more! 0x5366374d34fadf5954d090760,0x537136032c00307c2950f8f20,(more! 0x1151f04f29a6f0b8a0e8196e0,0x115a83db2ffa82ea2eb5eba00,(more! 0x4ef2b4fcd171ff19571509e0,0x4dbbde873e9201eb898687e0,(last! 0x16f7406f29b1bc47900,0x769aa536616c16b240))))
private theorem r20 : BlockChecks (S 239942) N P 2395 20 91 :=
  block! 2744,4,0x6a216a3556d68161886ec2b00,0x6a216d343006e7547ca3d9c00,(more! 0x53de15a9f0e5efee48f640ca0,0x53e920b3e740a7fae99d66900,(more! 0x11652903d593852b567068320,0x116dc5caa1fd460e9b21511c0,(more! 0x4de2b8af8181cd2a7b20bb60,0x4caa8adcf02c30477f3e70c0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 239668) N P 2395 21 58 :=
  block! 2719,3,0x69e36e4b0a97c7f4d4ebf6100,0x69e37149039abf79003ba5400,(more! 0x53c50e02c8647fa17b8feff60,0x53d011fc9580e478c11605140,(more! 0x1159d38fb10e716d144aec660,0x11626a858fd29a9783b52aa40,(more! 0x4c48cbacdfd4a701c0c8d2c0,0x4b116a9ca5bfdcef6bdfb6e0,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 239868) N P 2395 22 22 :=
  block! 2696,2,0x6a10aaed46d544449137d0900,0x6a10adebe37a5455659797400,(more! 0x53fdfce31b1d0e032fd976e60,0x5409051d3fdd98dc624310ce0,(more! 0x116056cdc7f40a765107d1c60,0x1168f0fd895f3762dbd804020,(more! 0x4b2573cbd2bb16d788f40b00,0x49ed9c06392d7dfa60271dc0,(last! 0x0,0x0))))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 1077) N P 7773 7 0 :=
  block! 57,1,0x26e39bce3b995c780,0x26e39fd5c96033500,(last! 0x26f68c23119673cc0,0x26f6967cc757dd5a0)
private theorem r1 : BlockChecks (S 799) N P 7773 1 26 :=
  block! 63,1,0x15840efef0452a800,0x158411fc785b57000,(last! 0x1584110aa420f8240,0x1584172bbbcfab380)
private theorem r2 : BlockChecks (S 754) N P 7773 2 25 :=
  block! 63,1,0x132f02478312e01c0,0x132f0519fb8166e80,(last! 0x132f06c8ad8ee0680,0x132f0c66fe2a27dc0)
private theorem r3 : BlockChecks (S 910) N P 7773 3 22 :=
  block! 74,3,0x1bd72b3d3e18aecc0,0x1bd72ea4fddd74080,(last! 0x1bd72ce87a54c98c0,0x1bd73461fa36641e0)
private theorem r4 : BlockChecks (S 1044) N P 7773 4 18 :=
  block! 76,3,0x248f4fed7078bf840,0x248f53d56a3c1cd80,(last! 0x248f522d36fb25840,0x248f5b6f64caa9a80)
private theorem r5 : BlockChecks (S 1049) N P 7773 5 12 :=
  block! 67,2,0x24e87a03143ac7c80,0x24e87defd6d7e2300,(last! 0x24e8809e8f6651c80,0x24e889f3450c73560)
private theorem r6 : BlockChecks (S 1077) N P 7773 6 3 :=
  block! 61,1,0x26e39bce3b995c780,0x26e39fd5c96033500,(last! 0x26e3b6618b7442140,0x26e3c01c73d87e8a0)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,trivial⟩
end h7773

set_option maxHeartbeats 800000

private theorem checks (b : Band) (hb : b ≠ .h2367) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.none
    | h7773 => exact h7773.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.all
    | h7773 => exact h7773.all
  cases x with
  | none => exact hn
  | some i => exact grade_at _ _ _ _ hc i

theorem terminal_bounds (b : Band) (hb : b ≠ .h2367) {h : ℕ} (hl : start b ≤ h) (hu : h ≤ finish b) (x : Test b) :
    debit h (tested b x) <
      jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) := by
  let t := tested b x
  have hh0 : finish b < 131071 := by cases b <;> decide
  have hh : h < 131071 := hu.trans_lt hh0
  have hshape : t.shape.J = (terminal b).shape.J := by cases x <;> rfl
  have hJ : t.shape.J ≤ 131071 - (start b + 1) := by
    rw [hshape]
    cases b <;> decide
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  have hc := checks b hb x
  change BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) at hc
  unfold BlockChecks at hc
  rw [blockSurplus_eq t (start b) _ _ (by omega) (by omega) he,
    blockSurplus_eq t (start b+1) _ _ (by omega) hJ he] at hc
  change debit h t < jointGain h t.shape (threshold b x) (seedThreshold b x)
  exact strict_of_first_difference (b := t) hl hh (by omega) (by omega)

#print axioms terminal_bounds
end HighCore82209Terminal
