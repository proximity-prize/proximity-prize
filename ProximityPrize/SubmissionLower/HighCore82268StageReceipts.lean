import ProximityPrize.SubmissionLower.HighCore82268Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82268Stages

open HighCore82268
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

set_option maxHeartbeats 4000000 in
private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2527 =>
    rw [stages]
    refine cons (bank! 98,122552,0x3b92d957d0,0x4b53886360) (bank! 472,356528,0x6a6c935adbc8,0x11ccf4ce2c7c88) ?_
    refine cons (bank! 102,142950,0x36743f00dc,0x809e923840) (bank! 497,375642,0x7982601b7b4c,0x1b373a54eb1d88) ?_
    refine cons (bank! 116,137040,0x78839fda44,0xb4fa7cd660) (bank! 601,364168,0xdcb8ee2b7ca0,0x316999adfc7890) ?_
    refine cons (bank! 127,157010,0x8f7ba8dd50,0x10bfa8d99e0) (bank! 604,333234,0x17d6a87594128,0x4126f9962c3540) ?_
    refine cons (bank! 148,145618,0x15e2369d580,0x1fe02b5de60) (bank! 753,288258,0x27f8198071ed8,0x98a17e2fb99b08) ?_
    refine cons (bank! 167,211438,0x1a86ec2d000,0x3951f940f80) (bank! 832,504650,0x4af82143babb0,0x10c9a1d17f95250) ?_
    refine cons (bank! 198,168684,0x3790b764388,0x7c92a6dd6f0) (bank! 1016,760900,0x7bfcbd1909908,0x286d54d1c8f5310) ?_
    refine cons (bank! 236,110340,0x705a837f284,0x240c31926bdc) (bank! 1279,842856,0x1a2e0f1ddff660,0x8ddeccff46e1380) ?_
    refine cons (bank! 287,225170,0xfc28b6ad1d8,0x12539a9a038c) (bank! 1292,0x122e26,0x2046846f3fda28,0x665c160a1e4cb38) ?_
    refine cons (bank! 288,225962,0xbef90d60c70,0x759f3391df10) (bank! 1635,0x12a7d6,0x3582307cc30e30,0x1d9ed551328bb9d8) ?_
    refine cons (bank! 363,252980,0x25daa8579558,0x1939a19c66258) (bank! 2080,0x1c224c,0x760d363651ce38,0x62876a138eecc950) ?_
    refine cons (bank! 360,263698,0x236bc6425180,0x4de7d9519dd40) (bank! 1760,0x106f3a,0x65a50e64a38424,0x87dabd6725f838b8) ?_
    refine cons (bank! 386,303820,0x278a91600c38,0x379632766ecc498) (bank! 1810,0x148e18,0x7951bc855b9c64,0x2170675a2581c1e18) ?_
    refine cons (bank! 612,537286,0x11a72fd869c60,0x594ed2c621430) (bank! 2802,0x18f732,0x26eb6e884e3e43c,0x1f7fb693298c57304) ?_
    refine cons (bank! 832,541556,0x45b73a9dd12d8,0x23ebe996095260) (bank! 4455,0x345128,0xc0024b08db602c0,0xefc294f02ec4fff80) ?_
    refine cons (bank! 1221,0x105748,0x12dba65e1a0200,0xd6a500893bba10) (bank! 6694,0x4411cc,0x4ac69902f41700ec,0x6623b05483c987f360) ?_
    refine cons (bank! 1610,0x127760,0x3949d5334e4b68,0x3dec005d6873978) (bank! 8986,0x40def8,0xb64936ada649a040,0x1ca1c2e509e67f07230) ?_
    exact nil
  | h2528 =>
    rw [stages]
    refine cons (bank! 102,148105,0x4aebb94444,0x4937a38628) (bank! 485,433369,0x5a59a18eec20,0x12628a9dcb5a10) ?_
    refine cons (bank! 112,116751,0x69589e6120,0x73a4fa8e40) (bank! 497,376138,0x966e0f6f2824,0x1ae45d955e72a0) ?_
    refine cons (bank! 124,188063,0x6d34960868,0xac8bde77f8) (bank! 564,392749,0xbc086cd88588,0x2bc5039c76ee58) ?_
    refine cons (bank! 135,208042,0xc49282d910,0xfd9bea0fa8) (bank! 590,463219,0x138f64db39308,0x3f04f6abc08ab0) ?_
    refine cons (bank! 148,150811,0x16c4eb6fff0,0x167f131a970) (bank! 640,635092,0x1864cf53389b8,0x5bf863168f4770) ?_
    refine cons (bank! 160,222123,0x14cd2d4ac58,0x1f1b5bbc740) (bank! 715,574072,0x2a2d0dcd7acec,0x88398b11db2b04) ?_
    refine cons (bank! 161,88524,0x1389f8f1348,0x2d085c7c8f8) (bank! 804,512210,0x38c887953000c,0xcea2a2b4ef1130) ?_
    refine cons (bank! 198,168861,0x41011abd778,0x7c0d43d2ea0) (bank! 942,740652,0x63369cc234690,0x235b1c440efc0a0) ?_
    refine cons (bank! 236,110543,0x53923d152e0,0x23d15308afcc) (bank! 1232,0x11a191,0x1878be02f85680,0x84cf10f8a248f00) ?_
    refine cons (bank! 297,373952,0xfc4e95079d8,0x15fd5ce44d28) (bank! 1123,709482,0xfbf08194358ec,0x5738a37960a18d0) ?_
    refine cons (bank! 300,297515,0xdeb37db7710,0x81a1acd3ddb4) (bank! 1644,0x161fd2,0x414bb346af090c,0x209cd90df64ab9e8) ?_
    refine cons (bank! 363,253278,0x254ce34c7150,0x18ae2a3aa9f40) (bank! 2012,0x1916e7,0x6b42c53c44b460,0x5c47eb027ebe6f04) ?_
    refine cons (bank! 360,263987,0x2780cbcc88d0,0x48a4fbc4b63e0) (bank! 1767,0x146073,0x624de243cc7968,0x82b3bd2c00c080e0) ?_
    refine cons (bank! 386,304121,0x2caac9458d44,0x12a95596b04ba1c) (bank! 1797,758286,0x65a151bc5f373c,0x214bfd7899fad01a4) ?_
    refine cons (bank! 594,682949,0x1381303e46380,0x6a9262351bf80) (bank! 2809,0x1ebb04,0x179e004dacd94c0,0x23a08968065022ae8) ?_
    refine cons (bank! 847,772602,0x4bd9da08f16c0,0x236302e957fcc0) (bank! 4151,0x2d9a66,0xb87d6c63b49fbb8,0xd17f1650da760c270) ?_
    refine cons (bank! 1077,750740,0xda2db64f12da8,0x8bf20b0186deb8) (bank! 5723,0x41fe60,0x18e71060bb2a3310,0x378bd41eee00b134a8) ?_
    refine cons (bank! 1610,0x158a11,0x39a134ea49ada8,0x3563859e9bc6470) (bank! 8392,0x5ee429,0x84b51656144e14a0,0x16c93cc1c926f27d160) ?_
    exact nil
  | h2536 =>
    rw [stages, start]
    refine cons (bank! 102,148913,0x4b8dc88d70,0x46653d1220) (bank! 489,462737,0x7a7a47d356f0,0x1139a66b62c698) ?_
    refine cons (bank! 109,143476,0x668a357c18,0x6ff86d3d98) (bank! 479,355348,0x85ae2bdd88a0,0x17aacbf4f0f200) ?_
    refine cons (bank! 120,163527,0x648e64ed60,0xa733065830) (bank! 535,475891,0x97ab8e1a2030,0x255f27ee6975c8) ?_
    refine cons (bank! 131,183578,0xccafbe95e0,0xf4660b0960) (bank! 571,391800,0x12ddb8f29b380,0x3721ff3954a160) ?_
    refine cons (bank! 142,203629,0x109a5c80780,0x1597ee8bd80) (bank! 608,487585,0x163c880aa3f68,0x4f7559373e95f4) ?_
    refine cons (bank! 151,120998,0x139035672c0,0x1e1436aef28) (bank! 725,553502,0x2aedf44eb28a4,0x805519c7671014) ?_
    refine cons (bank! 150,244461,0x18d7687b80c,0x2c859f51f48) (bank! 791,699168,0x35a3bb40dff00,0xb8f49074803708) ?_
    refine cons (bank! 198,170277,0x2a40b4909b0,0x7794dde38c0) (bank! 966,721096,0x5fa5006d81c78,0x21c8cd310327d1c) ?_
    refine cons (bank! 227,189726,0x700c857a0b0,0x236b4f0349a8) (bank! 1181,936419,0x13d4db685668d8,0x7339a7fa5867ce4) ?_
    refine cons (bank! 307,329590,0x1b3298ec0420,0x25b25c226640) (bank! 1321,970316,0x19a7d740fdfe90,0xaf19ffd2ed805c0) ?_
    refine cons (bank! 295,222694,0x107c012f6340,0x859afd688068) (bank! 1547,0x12798a,0x2f7c40a752ef00,0x1bdad22b7ce31800) ?_
    refine cons (bank! 363,255662,0x1c5b4fdb7b00,0x179aca1378250) (bank! 2030,0x17be7e,0x6833f549fc7480,0x565b4d1ff4f37ee0) ?_
    refine cons (bank! 342,236469,0x28123f330c68,0x3d29197c54e2c0) (bank! 1692,0x1363f0,0x3f483e6553e8d4,0x9a52515fcd50f50c) ?_
    refine cons (bank! 387,357870,0x3acef1844460,0x6b38b5aaf8c828) (bank! 1720,0x10f145,0x36ca8580660434,0x2f97d15f134f72b28) ?_
    refine cons (bank! 741,663996,0x25f7cc99db4c0,0x8ced36d681288) (bank! 3124,0x241183,0x2f99db4ff8b7184,0x2d018700fc7d4d124) ?_
    refine cons (bank! 884,673775,0x459cb68a9c85c,0x2dab98f8cc25e8) (bank! 4819,0x37c2c6,0xdfb6aa158794894,0x133e73e77ef4beabe4) ?_
    refine cons (bank! 1073,927304,0xaba0e9fe18580,0x740e773358f5c0) (bank! 5784,0x42113e,0x2f704561dfd95d84,0x30d9f9c715329a3568) ?_
    refine cons (bank! 1444,0x136133,0x301974011d699c,0x1c208380562cf88) (bank! 7610,0x5508ea,0x5dc009e14a0b5ab0,0xc1885965b1de8e57f8) ?_
    exact nil
  | h2540 =>
    rw [stages, start]
    refine cons (bank! 102,149317,0x2cc35021bc,0x44e618cb78) (bank! 489,464693,0x7e0a2d0047f0,0x108e5028ad7958) ?_
    refine cons (bank! 109,143900,0x4eda28dd58,0x6d9bb51ad8) (bank! 479,357260,0x7f35490c233c,0x168d4e1d5e74c0) ?_
    refine cons (bank! 120,163987,0x58ddddd840,0xa3f0822e60) (bank! 535,478015,0x83260c2e2098,0x23aee932881ac0) ?_
    refine cons (bank! 131,184074,0xcae99038a0,0xefea607ea0) (bank! 571,394064,0xf023be20df00,0x349605869525a0) ?_
    refine cons (bank! 142,204161,0x139f976d480,0x15395cc9880) (bank! 608,489989,0x14d0134fd0d38,0x4bb64077d866f4) ?_
    refine cons (bank! 151,121558,0x14347bb7480,0x1d8bf638fa0) (bank! 725,556366,0x1ac1ace65df24,0x7b56f9edcd8bec) ?_
    refine cons (bank! 150,245009,0x14589a45800,0x2b89c3592e0) (bank! 791,702288,0x3d81edb6f92f4,0xb20779769c8c90) ?_
    refine cons (bank! 198,170985,0x37424a09d20,0x758bb619680) (bank! 966,724888,0x78877a01b8800,0x207c39876630930) ?_
    refine cons (bank! 227,190502,0x4b58a0322c0,0x227f94ef07d8) (bank! 1181,941023,0xfda1b3dd383c0,0x6e511ef2ac8ce90) ?_
    refine cons (bank! 307,330670,0x174700b3eb98,0x2531de4c3738) (bank! 1321,975468,0x13f9723f4a69c0,0xa826a732ffeaeb8) ?_
    refine cons (bank! 295,223678,0x163314bc09a0,0x8245ca3fb578) (bank! 1547,0x129102,0x2b9c6df1b02da0,0x1aadd6e5685059f0) ?_
    refine cons (bank! 363,256854,0x1c905eadadc0,0x1705880899200) (bank! 2030,0x17dd46,0x78a7c3fb625d60,0x5315cab9b97dce40) ?_
    refine cons (bank! 342,237545,0x17ddb96d3860,0x3375d2372289b0) (bank! 1692,0x137d50,0x519c24d286a180,0x8e922f11b1811280) ?_
    refine cons (bank! 387,359078,0x259a2af03100,0x5ac3927b6c7be8) (bank! 1720,0x110ae9,0x4c30aa9af74990,0x2860d611c27d9b6b0) ?_
    refine cons (bank! 741,666524,0x21ede84a6d5c0,0x8b64a0d1bba20) (bank! 3124,0x2440bf,0x234399a49a1b078,0x2b55a7e75180654b4) ?_
    refine cons (bank! 884,676659,0x6dacac3fdc95c,0x2cfe75a4d40028) (bank! 4819,0x380bb6,0xe47a2aac2be1dd0,0x129ba37cb5dbadbdc8) ?_
    refine cons (bank! 1073,930792,0xb46fee6869840,0x725a28c9b5a540) (bank! 5784,0x4268b6,0x3166fbab5b0225d4,0x2f3981e9f7b26bac78) ?_
    refine cons (bank! 1444,0x137387,0x201c4015ccd10c,0x1bbcd9ea96f17e8) (bank! 7611,0x557bea,0x8c9fb7d84abc9e70,0xbb144d2d960eff0110) ?_
    exact nil
  | h2570 =>
    rw [stages, start]
    refine cons (bank! 102,152347,0x6af837a763c,0x43353a9b18) (bank! 489,479363,0x676c6cb75a20,0xc99ffa2592f80) ?_
    refine cons (bank! 109,147080,0x948e88b26c8,0x693f21d8f0) (bank! 479,371600,0x51b7bad0ac88,0x104351879e8510) ?_
    refine cons (bank! 120,167437,0xb1b092e8b80,0x9abebd0d9c) (bank! 535,493945,0x8ad4525f28f0,0x1a0e2695b798e0) ?_
    refine cons (bank! 131,187794,0xcb3b18d8cb0,0xdeeecc33b0) (bank! 571,411044,0xc6baed398ce8,0x2629017ce672e8) ?_
    refine cons (bank! 142,208151,0xd804c4c7f00,0x1377ee8b520) (bank! 608,508019,0x102ea473cdae0,0x36965ce44e1ed0) ?_
    refine cons (bank! 151,125758,0xf5d50475ba0,0x1ae669f13d0) (bank! 725,577846,0x2674a617c7b98,0x5dea925f1d0210) ?_
    refine cons (bank! 150,249119,0x1475dc7f2c24,0x26c875336f8) (bank! 791,725688,0x3a1d56179b090,0x88c1d59093bb30) ?_
    refine cons (bank! 198,176295,0x4b52209ef70,0x679f4636b50) (bank! 966,753328,0x7fa83a1274b60,0x18c9a0e716964f0) ?_
    refine cons (bank! 227,196322,0x6aec571eb10,0x1cbbe0c914d8) (bank! 1181,975553,0x11afd8232d52f0,0x51f04045ded5d70) ?_
    refine cons (bank! 307,338770,0x12939ebde770,0x21d14c24b6d0) (bank! 1321,0xf795c,0x215e012e2a5898,0x7f4f5351c8fc828) ?_
    refine cons (bank! 295,231058,0x155313879810,0x6cbc43336a68) (bank! 1547,0x134106,0x3a30613fe1ed58,0x13dd3f22e3bec410) ?_
    refine cons (bank! 363,265794,0x2f9a175ed9e0,0x134a7076cc0d0) (bank! 2030,0x18c422,0xa5651ed0e5179c,0x3fa64ed1f18b84b8) ?_
    refine cons (bank! 342,245615,0x244cfcd88858,0x13b3efdbb3e0c0) (bank! 1693,0x143ba0,0x3fed0e728a26b0,0x55c3a1250b507720) ?_
    refine cons (bank! 387,368138,0x39233d70e2d0,0x23a86dbabf2a88) (bank! 1720,0x11cb37,0x63078296497ec0,0x1003729d135cea820) ?_
    refine cons (bank! 741,685484,0x2c99ae997eb80,0x80cf921068ef0) (bank! 3124,0x25a301,0x3f4a5261685e680,0x215df67f2d7d88d40) ?_
    refine cons (bank! 884,698289,0x5ea14014ec31c,0x28553c41396698) (bank! 4819,0x3a2ebe,0x15d0160019b07cf0,0xeb97f688ab58adfd8) ?_
    refine cons (bank! 1073,956952,0xb8e7003ae83c0,0x66be2051c16740) (bank! 5785,0x44f8ba,0x3234ab9e4256dbec,0x254e031040e0610f54) ?_
    refine cons (bank! 1444,0x13fcfd,0x29bfbd507223a0,0x19193ae1b7216c0) (bank! 7612,0x58da6a,0x7d07c046cfcf24e0,0x93bb7cbb0d32693660) ?_
    exact nil
  | h8100 =>
    rw [stages, start]
    refine cons (bank! 16,134071,0x21173b188,0x2541db0) (bank! 29,154332,0x14fbfdd6c0,0x1d4ed9a8) ?_
    refine cons (bank! 30,178837,0x95bb2a390,0xd5e5da0) (bank! 54,285425,0x72f7893630,0x11f852ac0) ?_
    refine cons (bank! 48,255147,0x2924f3ee00,0x5c1ee518) (bank! 90,486645,0x1e10e29d9c0,0x9f40923c0) ?_
    refine cons (bank! 76,328479,0x74e5b17a10,0x2eeb83a88) (bank! 142,666565,0x1baf93845cc,0x5d909c030c) ?_
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
end HighCore82268Stages
