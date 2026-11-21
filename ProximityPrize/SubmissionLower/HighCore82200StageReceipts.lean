import ProximityPrize.SubmissionLower.HighCore82200Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82200Stages

open HighCore82200
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
    refine cons (bank! 102,136808,0x2cc6f38f44,0x64d6350bd8) (bank! 485,379016,0x91be68ada578,0x149278379f54a0) ?_
    refine cons (bank! 112,104642,0x4efad2c800,0x9b25a5de00) (bank! 497,320626,0x8e673e896588,0x1e90d7eedc51c8) ?_
    refine cons (bank! 124,174956,0x9e9e2ae318,0xdda07990e0) (bank! 564,330036,0xbd43f32ac740,0x2f9d4c0ebf9d00) ?_
    refine cons (bank! 135,194030,0x8e90f3e000,0x13caa0a8000) (bank! 590,397934,0xf19f9326045c,0x44004e06e61bec) ?_
    refine cons (bank! 148,135640,0x120bc0d6780,0x1b4ce633420) (bank! 640,564688,0x112598173a190,0x61a908bcb86770) ?_
    refine cons (bank! 160,205954,0x16257b96808,0x24e9dd9b540) (bank! 715,495426,0x1f4cf21504250,0x8e4f4fe466bac0) ?_
    refine cons (bank! 161,72516,0x11463ed3018,0x37795c29c60) (bank! 804,423748,0x3f3f8134fd9b8,0xd2a528426d7408) ?_
    refine cons (bank! 198,150020,0x40330800840,0x912ceeb4050) (bank! 942,638060,0x7abc24e4a367c,0x235713f1cb0db24) ?_
    refine cons (bank! 236,89352,0x5423056a94c,0x2ae8d315b044) (bank! 1232,0xf9a20,0xf31ed1f59e600,0x80c210b7ced07c0) ?_
    refine cons (bank! 297,345356,0x11a06de79dd0,0x1746ca233f6c) (bank! 1122,587716,0xc16090a5f90f8,0x55f00f885fd739c) ?_
    refine cons (bank! 300,271792,0xde8e2e306b8,0x92c3241ca7e8) (bank! 1644,0x136d98,0x4d5b390bb731c0,0x1f06a409bbf7c658) ?_
    refine cons (bank! 363,223048,0x236e80fa3488,0x1b3cfde5d13f8) (bank! 2011,0x15cd10,0x6cd4114c073cc0,0x568ea6a8ddcc7a40) ?_
    refine cons (bank! 360,235070,0x1e9cdedb2e44,0x5670bb006c8c0) (bank! 1767,0x118516,0x51e1b737a80908,0x7755f71c57aff798) ?_
    refine cons (bank! 386,274564,0x358d8f0acee0,0x469a1f5193cd170) (bank! 1797,569172,0x6c269c0bb662a0,0x1c01065f3ff3c1a60) ?_
    refine cons (bank! 594,633070,0x155a14bad6600,0x6c5643d1e43a0) (bank! 2808,0x1a2a0e,0x203ba15b2115710,0x20d74c5faac942a50) ?_
    refine cons (bank! 847,702416,0x4ca0ed8a272f8,0x23301a3325d8e8) (bank! 4150,0x26db80,0x8092fffb9892308,0xbe84f602601ea9764) ?_
    refine cons (bank! 1077,663438,0xb55472b3e4c78,0x89a471f38c1b7c) (bank! 5721,0x38b07e,0x24c4af640e7c0018,0x3281ca417468a1ac00) ?_
    refine cons (bank! 1610,0x138c84,0x3f808ad4317dbc,0x33da54baad53198) (bank! 8390,0x51422c,0x92a3a383d02010b0,0x14a1936f6901ff7b958) ?_
    exact nil
  | h2368 =>
    rw [stages]
    refine cons (bank! 106,161929,0x4ffba1e380,0x6129ee3080) (bank! 499,377099,0x7ca198d59100,0x152fe4e994a4e0) ?_
    refine cons (bank! 112,104751,0x7302652fe0,0x9a6df57d00) (bank! 494,347343,0x8a4747d4cea0,0x1de362e423d8d0) ?_
    refine cons (bank! 126,97613,0xb7c5160978,0xdde3432ab8) (bank! 543,462903,0xacd6c34e8a1c,0x2da29041714f70) ?_
    refine cons (bank! 138,167937,0xe8c5f32c7c,0x1359c810588) (bank! 596,474780,0x128a9c984a0e0,0x438516e4f45a08) ?_
    refine cons (bank! 148,135779,0xb7d9a87cd0,0x1b2279a1c50) (bank! 670,534295,0x1be9c60cb9680,0x6527ce9766b578) ?_
    refine cons (bank! 160,206103,0x1c06982ae10,0x24c5021cd00) (bank! 723,546172,0x1a7598ef6e5b0,0x8e5233aa8cadac) ?_
    refine cons (bank! 159,150126,0x18a78b0c948,0x3596f761f68) (bank! 812,603285,0x47caea2a0ee74,0xd3b577ea92a140) ?_
    refine cons (bank! 198,150197,0x41813f6fc40,0x906d1695590) (bank! 924,616366,0x732e81e560870,0x2234291091039f0) ?_
    refine cons (bank! 271,263494,0xd9ed2805c68,0x1caa5d57a278) (bank! 1206,822336,0xffa858ecaa5b0,0x7bac0b6d19589d8) ?_
    refine cons (bank! 328,295655,0x17578d04c9fc,0x2bfac62acd30) (bank! 1426,980597,0x1bc1c893ea8e38,0xcdf8da0525b1df0) ?_
    refine cons (bank! 325,293460,0x1243f0497000,0x6d326417e268) (bank! 1757,0x12c259,0x40e59ecedc3f14,0x2289fbde25b8fec0) ?_
    refine cons (bank! 363,223346,0x23a5c0e863c0,0x1b0a9db6b94c8) (bank! 2033,0x149806,0xb6e04e6bca5030,0x56d2e0306f4a9f0c) ?_
    refine cons (bank! 348,155563,0x209a6e0374b0,0x451f725563cf40) (bank! 1685,0x1082f1,0x32a4a6a9c1a100,0xa299bc8e8758e000) ?_
    refine cons (bank! 616,487047,0xee920d90cc2c,0x88d9e96e4d520) (bank! 3042,0x1e79ba,0x216258d78bfd158,0x2a79237f0a6803da0) ?_
    refine cons (bank! 943,740078,0x8cf77279a9724,0x2d3e64c446a21c) (bank! 4694,0x3082c9,0x11fad667ed0f74e0,0x11b0418ed0703b2830) ?_
    refine cons (bank! 1384,948503,0x298a28cbd02a78,0x1d09d2d2e1d420c) (bank! 7323,0x4c8a3d,0x6f5cd944c5848ed0,0xac4b6cafe2f0e9c640) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,139636,0x12af7f11e270,0x6ed6aa9430) (bank! 489,417724,0xf63fa738e1f800,0x11be3a24160220) ?_
    refine cons (bank! 109,133834,0x1c5d72551d38,0xaf6e1067e8) (bank! 479,311410,0x160775d9eee1d88,0x18d181020c76d0) ?_
    refine cons (bank! 120,153160,0x2567bfa59df4,0xf5fd0dc284) (bank! 535,427200,0x1f0bdbd90f038a8,0x25c9f684c993f8) ?_
    refine cons (bank! 131,172486,0x31478abc09a0,0x15561c22410) (bank! 571,339942,0x2a33860907599b8,0x366bb635012b64) ?_
    refine cons (bank! 142,191812,0x3f36a5548220,0x1cf1c68ce60) (bank! 608,432628,0x37aacedeb25d138,0x4c78ebefdf36b8) ?_
    refine cons (bank! 151,108602,0x548553b21e38,0x27c7afeb768) (bank! 725,488042,0x49c14db3100c938,0x76c9648fd9b668) ?_
    refine cons (bank! 150,232488,0x82e0c36fc8dc,0x3e80456c2d8) (bank! 791,627948,0x6004b3bba900640,0xa83a6d5c11bd00) ?_
    refine cons (bank! 198,154976,0xfa5f79d0b8c0,0x909d00c6b00) (bank! 966,634756,0xe492c72218ae224,0x1d91d7d547eb514) ?_
    refine cons (bank! 227,173456,0x453c8aa8cfa80,0x2c8654eb6340) (bank! 1181,831996,0x27222a91d3bed808,0x6029c0572e90bd0) ?_
    refine cons (bank! 307,306548,0x308cacddf3a60,0x27ecfb7d1020) (bank! 1321,853444,0x355f31cac6cb24f4,0x9181b3f9d30e774) ?_
    refine cons (bank! 295,202424,0xbef023c706b00,0x9870f2f51640) (bank! 1547,0x106670,0x68e7035bf7c4e518,0x1631cb17324a8c78) ?_
    refine cons (bank! 363,231392,0x1add0f97667030,0x195ff33763350) (bank! 2029,0x150610,0x108fa4820650ed7c0,0x44eceb8359a65780) ?_
    refine cons (bank! 342,215268,0x88ad2d2f798d1e0,0x7c3a801381be30) (bank! 1692,0x112988,0x1ea8cfe12fc119938,0x67507b099b73b700) ?_
    refine cons (bank! 387,334260,0x96f2e8b95480998,0x9ac9711d3576b8) (bank! 1720,963280,0x7bd333cf156f6e3a8,0x171bbd3252ac6dbd8) ?_
    refine cons (bank! 741,611196,0x46d477b6ccef60,0x8831011597fe0) (bank! 3123,0x1fe6b0,0x5df82ccde9bbeba20,0x231ecd3253a461bcc) ?_
    refine cons (bank! 884,615430,0x122b45d6c610fc0,0x2ae9a33c929580) (bank! 4818,0x315282,0x1cabaab359ba8e95ec,0xf2c1cb61014e52388) ?_
    refine cons (bank! 1073,856984,0x23aa30ec2f949c0,0x6ba170e70e8480) (bank! 5783,0x3a59a0,0x3ef1559d0996d98880,0x2641392c62bf3a9820) ?_
    refine cons (bank! 1444,0x11efea,0x60eb1ba10da7330,0x19da8c343b0bfe0) (bank! 7609,0x4ae4a6,0xd77b1eab0b373b1418,0x96d4167f09594f8150) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129914,0x10487f58,0x2541db0) (bank! 29,146536,0x8df4cf68,0x1d4ed9a8) ?_
    refine cons (bank! 30,172090,0x10cd9b470,0xd5e5da0) (bank! 54,271986,0xfeb68b70,0x11f852ac0) ?_
    refine cons (bank! 48,245360,0x558f588d8,0x5c1ee518) (bank! 90,465164,0x5b5f76f80,0x9f40923c0) ?_
    refine cons (bank! 76,314166,0xc00d7db58,0x2eeb83a88) (bank! 142,633866,0xc117ea7098,0x5d909c030c) ?_
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
end HighCore82200Stages
