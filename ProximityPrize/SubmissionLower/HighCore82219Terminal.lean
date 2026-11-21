import ProximityPrize.SubmissionLower.HighCore82219TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219Terminal

open HighCore82219
open HighCore82219TerminalArithmetic
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
private theorem r0 : BlockChecks (S 229924) N P 2441 24 0 :=
  block! 2656,16,0x6175af926294d83b1c7d91b00,0x6175b271376256e5d36119e00,(more! 0x4edb1d75566c2de733d9cb920,0x4ee5251096b42d0570f32c880,(more! 0xf70b60b553e146baa75fa900,0xf760d0b4f8ead10b0b896c60,(last! 0x32a98256d6b63e5c7319d5c0,0x31b5bbc1c57bbb707ae3cf00)))
private theorem r1 : BlockChecks (S 179010) N P 2441 1 366 :=
  block! 2708,2,0x3b183b23670b1218167537d00,0x3b183d5f83beda6800ef4d200,(more! 0x2ef8d9a37dc1cb2ff30c298e0,0x2efee6aee9071dac1c4017000,(more! 0x9534f19ab9bf8281bf4f00e0,0x956f0b410d244a3304033320,(more! 0x2cbafd7211a20741db9f7de0,0x2c21e6efc77a266e954e22e0,(last! 0x6f3377b67d259e464ca60,0x672859fca895d68ceed40))))
private theorem r2 : BlockChecks (S 185266) N P 2441 2 360 :=
  block! 2733,3,0x3f4b52e0f9107fc6d6bb70d00,0x3f4b553114367b3221d0b7200,(more! 0x3239f9f744e9dd3bbbfb30dc0,0x32407736de31d4692613eeb40,(more! 0xa007920582fe7113499ae140,0xa045cab8fee8c6dc568d9f00,(more! 0x30f52448ae5b82be6b983c00,0x3051aa7c0df797db28d4ec40,(last! 0x19b0c99dce135b0ac84240,0x1887e29f0aab0a22d6dcc0))))
private theorem r3 : BlockChecks (S 183202) N P 2441 3 355 :=
  block! 2735,3,0x3de48bf5447eaccfff31b1d00,0x3de48e3ec6f2de14cb77f1200,(more! 0x3138592af653de31489a4ad60,0x313eb0dd4ba3ab8c5ca147fe0,(more! 0x9c61782e0b6452e991cd1220,0x9c9d46f3c635e3a7d97daa20,(more! 0x2e4b2b20d6483a07460fa8a0,0x2dac4d6ddecd20d6aceb9440,(last! 0x175d0b36c16006e404ffc0,0x16532f8f2aa827f55c61c0))))
private theorem r4 : BlockChecks (S 186942) N P 2441 4 349 :=
  block! 2754,4,0x40719c7c7fcba2528e34b8100,0x40719ed1f6309eaa80c17ba00,(more! 0x333c03fe9d43e5ec27be29800,0x33429fd1dbd83c55de6a19340,(more! 0xa2f12a208ddb285a91575560,0xa32f14c9a37c1765eba03320,(more! 0x303f4eb107315d2532214420,0x2f9a8ed3340c9716a1267620,(last! 0x29eb53c176b9cf972c5760,0x2873892662282f89e14220))))
private theorem r5 : BlockChecks (S 189067) N P 2441 5 343 :=
  block! 2770,4,0x41ea8bcf7e398138d9fb87400,0x41ea8e2bbf38c26750d344800,(more! 0x346e7b925c2db4e4809e9ce80,0x34753eaf05710e68bea66ed40,(more! 0xa6b74293301038f0a6d23d60,0xa6f6045e5ace50345a2cf440,(more! 0x30d20d1ba1e80ebfb5bf17e0,0x302a47da21b033d909619f40,(last! 0x389558505aa88b652490e0,0x36df33e65141afed430b60))))
private theorem r6 : BlockChecks (S 188960) N P 2441 6 337 :=
  block! 2779,5,0x41d776ed955ca516cf6d01f00,0x41d779497ed0b2bc94c7a8600,(more! 0x347216d8c85afdfc6f5dc9c40,0x3478d7de4b848ffcf84c344e0,(more! 0xa67e19bbe45fd897b0d5d900,0xa6bbf5f47e5cb8f9fa2e2900,(more! 0x2f9cd11e32a35d565f5bb5e0,0x2ef60d7bbc40a92e31282220,(last! 0x3bf750ec94da01ff420280,0x3a4629b8088f5752217340))))
private theorem r7 : BlockChecks (S 194045) N P 2441 7 330 :=
  block! 2807,6,0x456e37e5f553b7e3729b58200,0x456e3a521f2775b4b59587400,(more! 0x374903b5e8b625f8263c4e580,0x3750249e6fe03a82cf24c13e0,(more! 0xafbb10f2b5854e8b9b7c1540,0xaffc09ceeba742f5b77e20e0,(more! 0x323eb0cde44b1d372dc5d500,0x318f5629981ad21dddca9b60,(last! 0x5a6e2de58d10067f7127e0,0x584ca526770b183b6f9320))))
private theorem r8 : BlockChecks (S 195714) N P 2441 8 323 :=
  block! 2824,6,0x46a116093a0f6360cfbe23d00,0x46a1187ab967fadc5d3ac5200,(more! 0x384aecf423e7b4975b3a80880,0x38522dcf87a9cff55150f1fc0,(more! 0xb2cb028fac726febc0b96b80,0xb30c709a28a72b909ac66060,(more! 0x3234bb18bb954bbaa299ef60,0x3182fcd981d82e7ce0f423e0,(last! 0x63c48f72d56407caf56820,0x6198c0f41d70e946697b80))))
private theorem r9 : BlockChecks (S 201989) N P 2441 9 315 :=
  block! 2860,8,0x4b3a53e9b200a20db52a87a00,0x4b3a566f3f56fbc67b000a400,(more! 0x3bf0f2748aa95dec9c011ff40,0x3bf8ae3a93c46fcf31bdf03e0,(more! 0xbea2fe820d96bfab90959480,0xbee87c89e932426cd88f9700,(more! 0x356f1b61f88a87307ba9e340,0x34b216fc16a5e0d2dfe08fa0,(last! 0x84fdb82f1bac7d203ab900,0x82724425599572b6030e00))))
private theorem r10 : BlockChecks (S 201870) N P 2441 10 307 :=
  block! 2876,8,0x4b23a834af5dac70e76c53100,0x4b23aab9db576ac180fc19a00,(more! 0x3bf7d09cffb8c6c13a7818080,0x3bff89dcb9eceb9faede722c0,(more! 0xbe5e4e56a25d43fc5bb38500,0xbea2d7604807022359334ac0,(more! 0x33e822d629eb19eb4d4ed820,0x332bf75ee7f7776e11126b60,(last! 0x78082e407fe5b51cac4ec0,0x75c0b1c38055874f5755a0))))
private theorem r11 : BlockChecks (S 210653) N P 2441 11 297 :=
  block! 2928,10,0x51d0c874b96094a80766ca200,0x51d0cb15f74de2a9171e5b400,(more! 0x41445d030b73b11d21167b1a0,0x414cc8c9dc41b22a4a20c46a0,(more! 0xcf9306d501d113a5353a8cc0,0xcfddadd23517bf4fb1aeac00,(more! 0x38a30de6f178259433509ac0,0x37d611a4a231f2dc88c3a420,(last! 0x91b87fb28c32ec299b7480,0x8f1f6dc13958079819a280))))
private theorem r12 : BlockChecks (S 223669) N P 2441 12 285 :=
  block! 3003,13,0x5c3b63ab182de42fbe85fca00,0x5c3b6675ef5aa311b45f0c400,(more! 0x4983e4772a24dcac4f28d9f80,0x498d6701471718bd4a9130260,(more! 0xea728d6565a36ad6d2724940,0xeac7178df2c0c971cd222d60,(more! 0x405f2abdbe9bb56608357cc0,0x3f777ed5dd1194303eadda20,(last! 0xa773d81d6660a0aa102e80,0xa47318c1110b4340783200))))
private theorem r13 : BlockChecks (S 229924) N P 2441 13 271 :=
  block! 3027,14,0x6175af926294d83b1c7d91b00,0x6175b271376256e5d36119e00,(more! 0x4dbd47ea3b231f6628faac780,0x4dc756335b4ec84914331fa80,(more! 0xf7e5e375b139dc1e3796c540,0xf83ee957cfa5a206af5763e0,(more! 0x431aab01031e6754f3f442c0,0x4225a0a9668d9fff48750a20,(last! 0x8735e4472b1b9cc2530b40,0x8477f8ea05930062e227c0))))
private theorem r14 : BlockChecks (S 228680) N P 2441 14 256 :=
  block! 2969,12,0x606895e322d2af79b3b8ef700,0x606898bdfdd3c8a5075c37600,(more! 0x4d0c9280f8813161128ee3980,0x4d168437da3f848059edce060,(more! 0xf51ba6935abde7f214a4bb20,0xf572c958e22948705a653c00,(more! 0x40550d5411e6676894cbfe00,0x3f62ed12689a294675970c00,(last! 0x50c828e0ce6111fb6cdae0,0x4ec6bc94a93d838d088280))))
private theorem r15 : BlockChecks (S 228103) N P 2441 15 239 :=
  block! 2919,10,0x5fec43d7573ab917a2496f800,0x5fec46b05a26e50950bd03000,(more! 0x4cca7e7ef8601f9b865329d40,0x4cd462c3173da530adf7404e0,(more! 0xf3c7c38d2d8fe6d401f6ece0,0xf41db54f24e2fd130e3d9220,(more! 0x3e2c6e987c5e9775944db500,0x3d3baa56da92e688c6e65ba0,(last! 0x296769aac45d750415b900,0x280f8b581127d8d400da60))))
private theorem r16 : BlockChecks (S 229092) N P 2441 16 219 :=
  block! 2875,8,0x60c18c12af12aafe56e8c5b00,0x60c18eeedb295d227774e1e00,(more! 0x4d8fd64daacb20f74dab6fda0,0x4d99d068111c7c1e332090ac0,(more! 0xf5dc1accc779111ccb19e6c0,0xf63251f2f88cf3936c93bb60,(more! 0x3d2ffabb7eb9d704194ddbe0,0x3c3d06b7d76c0906c1979040,(last! 0x108d4286592dbc101cb4c0,0xfc6d0cd6e7fb619687040))))
private theorem r17 : BlockChecks (S 229493) N P 2441 17 197 :=
  block! 2837,7,0x6118498e15c335dc919790a00,0x61184c6b89ef8c6ca3d494400,(more! 0x4defc766b5c8c5679b700e920,0x4df9ca163e7657e6a0dc549a0,(more! 0xf6aa086cd4b26fe4c5b1e100,0xf70021c1362a65102eff0300,(more! 0x3bdbc3630569a7764c4bfe80,0x3ae7eb855d3c563f10594660,(last! 0x39e0c535ef7999ebab320,0x351c0aca83a44521a8de0))))
private theorem r18 : BlockChecks (S 229615) N P 2441 18 173 :=
  block! 2802,6,0x6132b509bc0309c99501b1000,0x6132b7e7940055b9b2369a000,(more! 0x4e1e44993f2d570a96a6305c0,0x4e28498dd5254a4c9dea070a0,(more! 0xf6dd067be05049e96ad66580,0xf732e218f6a728858cd596e0,(more! 0x3a6b33220b4ffed6b7cf5fc0,0x39772ef4158c362ff09e8060,(last! 0x14db786931a02fb19540,0xecfb9074db699329880))))
private theorem r19 : BlockChecks (S 229607) N P 2441 19 147 :=
  block! 2771,4,0x6130f96bbea65b192b4c91800,0x6130fc4990180c744bfbb7000,(more! 0x4e34b37825a6dc906172603e0,0x4e3eb7c137a01558bf89765e0,(more! 0xf6c8601dd32214395a9d32a0,0xf71dfe24fd80cbc95212b800,(more! 0x38fd46116379758687678480,0x3809841859257c1a44ccb5a0,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 229548) N P 2441 20 119 :=
  block! 2744,3,0x61243238b346eb46d2bcc9300,0x61243516547308972d116ce00,(more! 0x4e40b6162b0f954223fc239a0,0x4e4ab88e474920e3dc499b240,(more! 0xf698591a642e1f81b36b4c40,0xf6edca2a7cd5a97e7b5db400,(more! 0x37a0afe2062b84508871f4a0,0x36ad37a72121c110729166a0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 229477) N P 2441 21 89 :=
  block! 2719,2,0x6114d2cead0a23385c2d51a00,0x6114d5ac141f449e755ece400,(more! 0x4e491f74f3bb276dc8f496b40,0x4e531fd9bdeb08121375e95c0,(more! 0xf662d126830474ef70a940e0,0xf6b82da65ee1315082b29220,(more! 0x3659aab40e65c5b81b2c51e0,0x356667e8a5a4ba485bd46cc0,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 229895) N P 2441 22 56 :=
  block! 2696,2,0x616f655ec7b4c2a460c4ff800,0x616f683d84c830f30443a3000,(more! 0x4ea45c6183438fba2ee5b0100,0x4eae65c5984d3b2e49900ea00,(more! 0xf73f952eb0683bdd2eb2c400,0xf79566c0337cff6fef2b7280,(more! 0x357242359a96a277e9139f80,0x347dfc46e22ad5a7028a5580,(last! 0x0,0x0))))
private theorem r23 : BlockChecks (S 229805) N P 2441 23 22 :=
  block! 2675,1,0x615be17c4675d367412f5d200,0x615be45ab9e6b6a9cbcd29400,(more! 0x4ea6e6d0e7ca387f53d01d020,0x4eb0edb966232c9f0119056c0,(more! 0xf701b7b5aee28628671d7820,0xf757a4b124f4de3ab60da1e0,(more! 0x344f39fba631588755835660,0x335afff0e1b6a314ca123600,(last! 0x0,0x0))))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 949) N P 7827 7 0 :=
  block! 57,1,0x1e423ff8d2c008080,0x1e424385e45a5ce00,(last! 0x1e433f97c52250800,0x1e4347a1d99f268e0)
private theorem r1 : BlockChecks (S 729) N P 7827 1 27 :=
  block! 60,1,0x11f2af3f2763bab80,0x11f2b1f9b39190200,(last! 0x11f2b703741263fc0,0x11f2bc5ffd4cacca0)
private theorem r2 : BlockChecks (S 773) N P 7827 2 25 :=
  block! 63,1,0x142787d4fba963c80,0x14278ab9a28685e00,(last! 0x14278dd998bd13300,0x142793b3c92805fe0)
private theorem r3 : BlockChecks (S 800) N P 7827 3 23 :=
  block! 67,2,0x159258c789ec22cc0,0x15925bc606faa8500,(last! 0x15925fe8f538619e0,0x15926612bdaedd680)
private theorem r4 : BlockChecks (S 949) N P 7827 4 19 :=
  block! 76,3,0x1e423ff8d2c008080,0x1e424385e45a5ce00,(last! 0x1e4242335b5ef8860,0x1e424a34eb9f57020)
private theorem r5 : BlockChecks (S 916) N P 7827 5 15 :=
  block! 67,2,0x1c355896c6e3c93c0,0x1c355c04447aa4900,(last! 0x1c35647adddcbeb00,0x1c356c0f917163ea0)
private theorem r6 : BlockChecks (S 943) N P 7827 6 8 :=
  block! 61,1,0x1de1717bddd688400,0x1de17503319ec7000,(last! 0x1de18165573a2c200,0x1de189537bdddf900)
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
end HighCore82219Terminal
