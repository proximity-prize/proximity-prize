import ProximityPrize.SubmissionLower.HighCore82258TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Terminal

open HighCore82258
open HighCore82258TerminalArithmetic
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
private theorem r0 : BlockChecks (S 180000) N P 2536 27 0 :=
  block! 2608,12,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32aa532a25b41e6fd81f3dae0,0x32b052fea7d109e80717fc900,(more! 0x860bf7ce67370c53504dc5a0,0x85d697777d266dac22e40fc0,(last! 0xb5b0c05effeda7f253290c0,0xb31c31071b0f2e9946f8e40)))
private theorem r1 : BlockChecks (S 172349) N P 2536 1 339 :=
  block! 2727,1,0x36c8e62f2113c445e214b5000,0x36c8e855f3f9e7c3fbffd0200,(more! 0x2d3d4346c8cda08a5eb03cc20,0x2d42c56164964bc01333f0760,(more! 0x7de571ec27b1e6635b8ac1a0,0x7dc205d888f6b8a770fb3560,(more! 0x1ad4b539d8cf3c8b04204d40,0x1aa13bb300d07937f6b5a4a0,(last! 0x75fc8c8fca550176340,0x49a5106669ec5a6c500))))
private theorem r2 : BlockChecks (S 173304) N P 2536 2 334 :=
  block! 2737,1,0x3764a2c9e149d49830b5e9800,0x3764a4f3c1892d4f8b810e700,(more! 0x2dc6bc78609897232cde1da00,0x2dcc4e7abaab8fdaf472622a0,(more! 0x7f286d5ac159c540f434d480,0x7f03e53cc3e97c6df3727560,(more! 0x1ab593c576a7bc8eac0a2780,0x1a8248a691eb5b49e7638fe0,(last! 0x63fbd0ffa1d82efb6ac0,0x53a6087148188bc8f500))))
private theorem r3 : BlockChecks (S 179574) N P 2536 3 328 :=
  block! 2766,2,0x3b78790cf33d2be596ee7e800,0x3b787b4add63063d0c3eea900,(more! 0x311253b5b651c5cd511d65800,0x311850c7152d740a6e1c0f080,(more! 0x88b5261c0c29b5a315a88d00,0x888de3bfd77bfb252b22c780,(more! 0x1da72b88f463f991fea3ad80,0x1d7052c494f643d6f10a4880,(last! 0x603cf5ccfe3cfc8b83680,0x5a06ff47f4328dc60cd00))))
private theorem r4 : BlockChecks (S 177387) N P 2536 4 323 :=
  block! 2768,2,0x3a082b3dd649e3390e55d2000,0x3a082d74c31b8ab75a4e99400,(more! 0x2ffe0ae7d226b1390bec45a00,0x3003e212b0099eb56868ce2a0,(more! 0x85105d1a989629e4eee61480,0x84e8e2413d48a5b03ed56f00,(more! 0x1b8c1c3a2be2b0048cd1be40,0x1b57c8193a39cc50dd8eb940,(last! 0x58c12eb72defd49ab0c20,0x53331329c32b0655677c0))))
private theorem r5 : BlockChecks (S 175478) N P 2536 5 318 :=
  block! 2770,2,0x38ca5e388fbb01cbe5967e800,0x38ca606962abb22a4f5fea900,(more! 0x2f10819d6e9b860b69a4eb480,0x2f163813f4cd65415b825d700,(more! 0x81e77af28432e29e6f395ac0,0x81bfbe9907d7d7b85c93eda0,(more! 0x19b0ffa70e3f1c5514dbf940,0x197ee9f2e69e3891232b3900,(last! 0x54f22959740e37c5e33c0,0x4fde4fbfa3aaa52b58b40))))
private theorem r6 : BlockChecks (S 176977) N P 2536 6 312 :=
  block! 2786,3,0x39c39fd94e6e80bfbaf563000,0x39c3a20eebcd75ea7926c6e00,(more! 0x2fe7ec148d7532f9cc6202b40,0x2fedbc05d0f440705df2f3de0,(more! 0x840603a519b2f67193f89e40,0x83dceee6f1fe060ffce1abc0,(more! 0x19abdd8f42ca39c06fa2bf40,0x1979ac7b50c8e9a22aa2aaa0,(last! 0x95b27ebcaa2e24c9fb8c0,0x8eb43b17e39e12c0fd620))))
private theorem r7 : BlockChecks (S 177384) N P 2536 7 306 :=
  block! 2798,4,0x3a07aab2d9f19395ee5c91800,0x3a07ace9c44ee11c5ba32f700,(more! 0x302f0fb7e300271b9a737ddc0,0x3034e68a1f9f5dfc8964799a0,(more! 0x8474fc4999624509681ac9c0,0x844aea6df194acbf2725a620,(more! 0x19088be514ee06512ccee0a0,0x18d6f872b431bb64eae0d120,(last! 0xc2784dca6c56ef53ae8e0,0xbaa7b1c0ea81d0fbef200))))
private theorem r8 : BlockChecks (S 176903) N P 2536 8 300 :=
  block! 2808,4,0x39b74514b7870839b6612c000,0x39b7474a185aa78254bd3f800,(more! 0x2fff1aae1ffb57e23d0e8d340,0x3004e92540101c85987a07ec0,(more! 0x838444e962a51dcc4237b080,0x83598971eb4839175e3f8940,(more! 0x17f14d83ab6fac80c7a9bac0,0x17c0e53c3571489bb1fe46c0,(last! 0xd13ff0ed55c3bd7f57440,0xc9964d8c09eee6788ffc0))))
private theorem r9 : BlockChecks (S 178309) N P 2536 9 293 :=
  block! 2827,5,0x3aa2e3b09ac5b8a55e2141000,0x3aa2e5ea79f0b7b659524ba00,(more! 0x30ce35c5132a7adc405338f00,0x30d41c49dbb2b80d357d4bac0,(more! 0x85809f057829ad6a2777b100,0x85548c2fd9bc36fef2e30d60,(more! 0x17b9a094ea188258210c9b80,0x17891fea16abe2f879479660,(last! 0x109f1f9ab14be9e81e2880,0x1018626f376a3f55730980))))
private theorem r10 : BlockChecks (S 178543) N P 2536 10 286 :=
  block! 2843,5,0x3aca48ce2325d0c4d862e8000,0x3aca4b08c1c4395baddc89000,(more! 0x30ff8fe0930cfbe330e38f000,0x31057a4f7c1d04d2cac568000,(more! 0x85ac72404b8828da250bb540,0x857f783c0df68eb6bc643060,(more! 0x16ee3aabf366b63a359e3200,0x16be5bc6819b1bf94fbc6100,(last! 0x10e1f16409e58fd13f5140,0x1062ce61d837d4241a4ea0))))
private theorem r11 : BlockChecks (S 179864) N P 2536 11 278 :=
  block! 2865,6,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x31c6a42ac974c9435a25cfbc0,0x31cca55ec696bc049a2a1ea20,(more! 0x878af186f3ebb222c42dc680,0x875ca581abb1c589f01eeee0,(more! 0x16940902cde1efc42d111a60,0x16640e96e30609e7557bd460,(last! 0x11261affcf05b424a225c0,0x10ace102e711d3b3630300))))
private theorem r12 : BlockChecks (S 179838) N P 2536 12 270 :=
  block! 2885,7,0x3ba53cb17fb1429ca0dcaa800,0x3ba53ef041d60a28a36b4a100,(more! 0x31d529a42fc8cc35ac1b6f540,0x31db2a3d3b352eda027bd7260,(more! 0x87507539f5c485a062be5cc0,0x872164200520d1846e3ee420,(more! 0x15a33fd2c81518b4d82056e0,0x1573fcf334469dde1f5a57a0,(last! 0xd7bdfb510b49272bb50c0,0xd19c342183215e475d1c0))))
private theorem r13 : BlockChecks (S 178760) N P 2536 13 262 :=
  block! 2901,8,0x3aeedd0d67cc19a33bf021800,0x3aeedf48b7f54343531619700,(more! 0x315218500ab4979b201e73340,0x3158060c6d5613e2e9d4852a0,(more! 0x8574b7dca63b43ebabe69880,0x85455a1e526271bf22971940,(more! 0x144f7c38e909f18e21f97520,0x1421911d41a5442d2e2a7fa0,(last! 0x817d4dac31b4c11812bc0,0x7d489b0bdb87492deb640))))
private theorem r14 : BlockChecks (S 179370) N P 2536 14 252 :=
  block! 2930,9,0x3b55ed64e68ef3619bd95c800,0x3b55efa229cce7e1e9d6cf500,(more! 0x31b7ac81cf277587be9428c40,0x31bda49e59129a9d19779fcc0,(more! 0x863a80bdd05c00b845291600,0x860a2e2255276940ef194280,(more! 0x13a5930ada9dd3455be01bc0,0x1377e0276aef0e4c65a32800,(last! 0x3fa8f4b04c5472cea9500,0x3d00f9389119d757a46c0))))
private theorem r15 : BlockChecks (S 179648) N P 2536 15 241 :=
  block! 2919,8,0x3b850386bea4500106e2b5800,0x3b8505c4e555803a9c0871f00,(more! 0x31ef050350d4130606e0562e0,0x31f501bb31ff98fe51f5a3a40,(more! 0x867ea9617502ee22ad2b6880,0x864d91614b40251ca56dc200,(more! 0x12e032b5559cbc151233f940,0x12b2e40da91164c866c12280,(last! 0x10c44c6c01091221c3080,0xfa337981f0aba4923960))))
private theorem r16 : BlockChecks (S 179554) N P 2536 16 229 :=
  block! 2875,7,0x3b751594d19c683d3b50d0800,0x3b7517d2ab6540203952d3d00,(more! 0x31f1cdf27076794b016c49500,0x31f7c8cb8bff9414e16095ea0,(more! 0x8631d43c208f94b3fc4398c0,0x86002dfe2e18dea951f7c560,(more! 0x12029cfda3266852143f4660,0x11d5e9fbc9224cec163d9fc0,(last! 0x90c6d728b261b6efc00,0x726cf10147678557840))))
private theorem r17 : BlockChecks (S 179916) N P 2536 17 215 :=
  block! 2837,5,0x3bb279b75f5a0fe4113d37800,0x3bb27bf6614ffa9cb1e409300,(more! 0x32334c9c0b40215ea2b66a320,0x32394d7d8f663ebbdea849360,(more! 0x869dcb14119e96e3b24d6f80,0x866b731461ec1ecefaf18380,(more! 0x115506d0eade86c78cfaf6e0,0x1128a46cef9fffb3cf498420,(last! 0x0,0x0))))
private theorem r18 : BlockChecks (S 179883) N P 2536 18 200 :=
  block! 2802,4,0x3bacdfb83d10572fc26772000,0x3bace1f724066441d1667d400,(more! 0x323cb89f980e6c0f0aa52dd00,0x3242b8abc6ba44f23de953e40,(more! 0x86702ff047949c297df5fc40,0x863d603a83f56ed2e4a9ee00,(more! 0x109241d6910c80e9d2ee9cc0,0x1066645d736b4ec75dcc15c0,(last! 0x0,0x0))))
private theorem r19 : BlockChecks (S 179596) N P 2536 19 184 :=
  block! 2771,3,0x3b7c3360d78e143f576257800,0x3b7c359ed3b3d7b083229d300,(more! 0x32219e84ab31f5d4945facc80,0x322799532b9cd5752b551dae0,(more! 0x85e13d4bcafd50c12ce60f40,0x85ae1fa2865bba6e216bd1a0,(more! 0xfc81093626a5800ee8d11e0,0xf9cd3e0318a48a4c463d940,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 179633) N P 2536 20 166 :=
  block! 2744,1,0x3b8278a5bdbf006f65f473000,0x3b827ae3d82a6ed1a19f60e00,(more! 0x323308a57e80b161051be1ba0,0x323903d5c7f62999d7ac9c640,(more! 0x85d6a402df42b7ec617cc6a0,0x85a320d48264e56cbf9837a0,(more! 0xf205c4e17fe6a95e04fee00,0xef57f234a81fb725faebba0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 179890) N P 2536 21 146 :=
  block! 2719,16,0x3bae0fe0fa30ef5b3add08800,0x3bae121fe6e123afa6d11ed00,(more! 0x326299ce2235d3591eae2be00,0x32689931c9eb77d44c926bc60,(more! 0x8627000a775589b133d0bd60,0x85f30a57cf893699d2e77760,(last! 0xe90613e5bad6aef7a09a940,0xe65b44b10597f2a54dbaa80)))
private theorem r22 : BlockChecks (S 179925) N P 2536 22 125 :=
  block! 2696,16,0x3bb400da166403740418f9000,0x3bb403191fb6fc1440d646a00,(more! 0x32724bdb85e541c160a3aef40,0x32784b9a121af1c089da3c680,(more! 0x8622651ebc0c4e95cce098e0,0x85ee1fb1980830e4a7fb7b40,(last! 0xdf8eb0c1413338d43daca40,0xdce88436986bb3a546480c0)))
private theorem r23 : BlockChecks (S 179808) N P 2536 23 103 :=
  block! 2675,15,0x3ba0259d2fdefd13cbd025800,0x3ba027dbd97840f11b6927f00,(more! 0x326be9425d2e130dea29db9a0,0x3271e6ba7fa5289c6e58fece0,(more! 0x85e46b96b24e463e79f6e800,0x85aff02de78a0051cb47bca0,(last! 0xd5f5a3de293cd4241bbd020,0xd35516affcd27b76ba85b40)))
private theorem r24 : BlockChecks (S 179897) N P 2536 24 79 :=
  block! 2656,14,0x3baf400cbe6c340265629f000,0x3baf424bb0d68f992e4bc0600,(more! 0x3281f1f74938d959f99a7f6c0,0x3287f0bd3a45df93a2d779920,(more! 0x85fb748f8fa8222eccf75fa0,0x85c6b470481f22148cd19b60,(last! 0xcd96d154625cc8854dffa20,0xcaf946c07517b52a91ee380)))
private theorem r25 : BlockChecks (S 179864) N P 2536 25 54 :=
  block! 2639,13,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x328637752ae2b0a45fc6b75a0,0x328c356d41e64fe5231ffb6c0,(more! 0x85e4b42b0ca4291a83e2baa0,0x85afc375c3d5037a6d23dfa0,(last! 0xc52383eb03909f4c808ebe0,0xc289ce9b12266d50ce52aa0)))
private theorem r26 : BlockChecks (S 180000) N P 2536 26 27 :=
  block! 2623,13,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32a1db7a4843f931689bacaa0,0x32a7db946a242ca9c12cd66e0,(more! 0x86140b405ae227fc14091040,0x85dedd78c2b3610c41b5a7e0,(last! 0xbda0ec69bd9321766644e40,0xbb08ede85a2e27e939813e0)))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7773 8 0 :=
  block! 54,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b44034829a1c5c40,0x1b440b0132a3efce0)
private theorem r1 : BlockChecks (S 821) N P 7773 1 27 :=
  block! 63,1,0x16b4691bfccae8780,0x16b46c2e9238bb500,(last! 0x16b469e60cf39a680,0x16b47065d051b2120)
private theorem r2 : BlockChecks (S 771) N P 7773 2 26 :=
  block! 62,1,0x140c8975326695d00,0x140c8c57ef5305e00,(last! 0x140c907ab565f9380,0x140c96636d8c3b740)
private theorem r3 : BlockChecks (S 796) N P 7773 3 24 :=
  block! 66,2,0x155b30a8b220bf240,0x155b33a35b4de0980,(last! 0x155b34cc89b45ea60,0x155b3afff981a4da0)
private theorem r4 : BlockChecks (S 855) N P 7773 4 21 :=
  block! 73,3,0x189ade77390253e00,0x189ae1aa576bf9400,(last! 0x189ae1c092142b7e0,0x189ae8aae50a3f6c0)
private theorem r5 : BlockChecks (S 879) N P 7773 5 17 :=
  block! 67,2,0x19fe04ee09e5aec00,0x19fe08381f97ac800,(last! 0x19fe0de212de406c0,0x19fe1519ad30c4f80)
private theorem r6 : BlockChecks (S 900) N P 7773 6 11 :=
  block! 61,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b3cccb63cd44c040,0x1b3cd43274f8314e0)
private theorem r7 : BlockChecks (S 899) N P 7773 7 4 :=
  block! 57,1,0x1b2d6acfe1cdcfd00,0x1b2d6e2d1ae6c1e00,(last! 0x1b2d770f87d996c00,0x1b2d7e8890a242a40)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,trivial⟩
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
end HighCore82258Terminal
