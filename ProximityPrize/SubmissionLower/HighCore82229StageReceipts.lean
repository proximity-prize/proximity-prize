import ProximityPrize.SubmissionLower.HighCore82229Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82229Stages

open HighCore82229
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine cons (bank! 106,158465,0x17b4649ae0,0x87bdb3c0a0) (bank! 607,364135,0x76e47c3ef53c,0x4ab0fe00b314f8) ?_
    refine cons (bank! 116,126008,0x980b05930,0xcf462c3450) (bank! 605,436938,0x5db1edf58de8,0x673ade97134d78) ?_
    refine cons (bank! 128,195951,0x437fddf3e0,0x12bf1f76158) (bank! 705,514606,0x71605a337cf0,0xaa054c3528c04c) ?_
    refine cons (bank! 138,163494,0x394b79b4b0,0x1ab2d136ee0) (bank! 683,205554,0x12d56ba4395a8,0xe14674752dd5c0) ?_
    refine cons (bank! 149,182237,0x3a42c04880,0x24f87c7da00) (bank! 729,345862,0x16b1be7f57d68,0x13e9a5c1238f070) ?_
    refine cons (bank! 162,123465,0xde66130278,0x327972865b0) (bank! 891,668090,0x49f7483e79b8,0x1fe2961f42d4490) ?_
    refine cons (bank! 176,111181,0x7c9ad8a030,0x5bd6264feb0) (bank! 950,672111,0xd04a254e0ec0,0x358f43fe7536938) ?_
    refine cons (bank! 198,143955,0x91fc1ee1c8,0xd23d71cbfa0) (bank! 1200,863925,0x5683bca312e00,0x83fcb47b062f740) ?_
    refine cons (bank! 238,184618,0x3b17e473a00,0x4a7ad99ca498) (bank! 1406,612838,0xa2fa5696238c8,0x19c5286ffa829690) ?_
    refine cons (bank! 248,185145,0x312c0c6cfc0,0xc80383ebbc8) (bank! 1099,730345,0x2ddc3431b0838,0x73e3f5c149edc80) ?_
    refine cons (bank! 348,220405,0x90da450e3e0,0x4df438c751f0) (bank! 1806,537365,0x3424536bd51cc0,0x3d5b72253abfcc6c) ?_
    refine cons (bank! 363,212201,0x12b5aa5ab04c,0x32391d60cf110) (bank! 2023,410176,0x3444e053531f80,0x10e5dedc5abc9fd6c) ?_
    refine cons (bank! 479,398833,0x40e70efba078,0x15b5ba9e9225c) (bank! 2224,759563,0x94b9155ea9640,0xf387af53273b9f28) ?_
    refine cons (bank! 523,251482,0x232836285c18,0x575d335a0a170) (bank! 3124,718637,0x1ac95b3757302f0,0x4151675c41c1a9b10) ?_
    refine cons (bank! 832,462944,0x24efc8a7016b0,0x28871f167b8ad8) (bank! 4833,898669,0x6cc7855e729b208,0x22f0e70f7c3be00528) ?_
    refine cons (bank! 693,168778,0x55d4f2fdca80,0x11b9968fb1c8b08) (bank! 3826,654538,0x24893e2510b0808,0x2a706ad197f4c64014) ?_
    refine cons (bank! 1127,132809,0x788ea3571cc48,0xbb135c7b030e9c) (bank! 6618,285969,0x734c9a7d82eb6c8,0xa512ece93244711b08) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,142064,0x22ac228d00,0x54d1e57320) (bank! 489,429521,0x12a10fa7d94c,0x12e78075200dc4) ?_
    refine cons (bank! 109,136342,0x272cab7ea0,0x8701e46008) (bank! 479,322915,0x1d8af5aa6b88,0x1aa29380f63fc8) ?_
    refine cons (bank! 120,155841,0x36b22423c0,0xc5870344f8) (bank! 535,439930,0x656cab07c27c,0x29576631e8e168) ?_
    refine cons (bank! 131,175340,0x11fabe78f8,0x11af4c0d370) (bank! 571,353493,0x1de63cda8dc0,0x3c95a473edd900) ?_
    refine cons (bank! 142,194839,0x424c19c880,0x18a9a2be580) (bank! 608,446971,0xdb6817410,0x56b6e33d739928) ?_
    refine cons (bank! 151,111770,0x9e0fee240,0x223078a2140) (bank! 725,505124,0x17fa4a9446128,0x878c0e5c468a50) ?_
    refine cons (bank! 150,235521,0x7e868a958,0x340517e17f0) (bank! 791,646518,0x85cc1918e0b0,0xc187ed0a71f2e4) ?_
    refine cons (bank! 198,158823,0xc789a1e770,0x84290475e40) (bank! 966,657232,0x278c20b858dbc,0x22eedb1fcdecbf4) ?_
    refine cons (bank! 227,177459,0xc809550510,0x28598aef1c60) (bank! 1181,859112,0x28dc365b6f108,0x76179e0548068f0) ?_
    refine cons (bank! 307,312289,0xb388f519b40,0x2774c51eb894) (bank! 1321,883796,0xb42a98c55ef94,0xb20bceb8b21f5bc) ?_
    refine cons (bank! 295,207346,0x805091702d0,0x935b254c7728) (bank! 1547,1110055,0x8ef92881ecad0,0x1c07651dd20d7868) ?_
    refine cons (bank! 363,237233,0x1a16cc166de8,0x197cd084b1900) (bank! 2029,1424031,0x2f42a1fcb397bc,0x5627390c2a71074c) ?_
    refine cons (bank! 342,220239,0x5771ffedd00,0x7778b48e2e8000) (bank! 1692,1162444,0x274df0aea7eb70,0x9c39120c026ad8c0) ?_
    refine cons (bank! 387,339759,0x1a951686f278,0xb65211d17e6d58) (bank! 1720,1001165,0x13692d6aa9ca5c,0x3217d921f9a6ec8ec) ?_
    refine cons (bank! 741,624150,0x1b339035c1c00,0x8e6313cd85a58) (bank! 3123,2161399,0x10f837a44232f10,0x2c71aee24b5555cf8) ?_
    refine cons (bank! 884,629402,0xc5a844632f60,0x2e14d223975940) (bank! 4818,3341700,0xa9e12932ee1efc0,0x12ea3662c729c7b2e0) ?_
    refine cons (bank! 1073,873778,0x6cdd0e668e580,0x7481d03c254c40) (bank! 5783,3955012,0x100877fcfb891830,0x2feaef2fe065fca970) ?_
    refine cons (bank! 1444,1198097,0x45e8c7e178c1c,0x1c1611b1809acf8) (bank! 7609,5080275,0x6ccef3043d2dae8,0xbd821471e1efec6bdc) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129595,0x48886b0,0x27db390) (bank! 29,145956,0x6d4420e8,0x1fe17568) ?_
    refine cons (bank! 30,171481,0x7808a7c8,0xe01dea8) (bank! 54,270884,0x8eb7cc3ec,0x137c8d868) ?_
    refine cons (bank! 48,244374,0x3d1db2c68,0x6148fe48) (bank! 90,463308,0x5f4df9080,0xabbbf8660) ?_
    refine cons (bank! 76,312600,0xce448bf40,0x31f54a0d0) (bank! 142,630937,0x7747ec8670,0x657f3be74c) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end HighCore82229Stages
