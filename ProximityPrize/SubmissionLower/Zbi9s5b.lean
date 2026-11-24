import ProximityPrize.SubmissionLower.Z9vlvqb
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace qcZ3orc
open P6_6 P6_6_8 q2w4Sxc
local notation "r!" l "," u "," kv "," f "," w "," h =>
  C8 (lo:=l) (hi:=u) (k :=kv) (bw:=f)
    (Or.inl (order (r :=l) (k :=kv) (ws :=w) h rfl (by decide)))
    (by decide) (by decide) (by decide) rfl (by decide)
local notation "p!" l "," w "," h =>
  Certificate.prune (order (r :=l) (k :=43) (ws :=w) h rfl (by decide))
private theorem r1 :C ⟨8,17,1⟩ ⟨133,38,1⟩ :=
  r! ⟨8,17,1⟩,⟨133,38,1⟩,25,0x161f8447c41965d,[([30,8],0xee03b80163e),([8,9],0x3ba191389f5),([11,13],0x271f87bb0f8),([17,28],0xda7c01aecb)],⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r2 :C ⟨5,17,2⟩ ⟨34,22,7⟩ :=
  r! ⟨5,17,2⟩,⟨34,22,7⟩,10,0x14b739ca87cf2d4,[([31,29],0x123e38092572),([49],0x264aed85ef5)],⟨(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r3:C ⟨35,17,2⟩ ⟨133,22,7⟩ :=
  r! ⟨35,17,2⟩,⟨133,22,7⟩,27,0x1c74371dad3d553,[([33,10],0x107133b01673),([11,14],0x3b48e7c7ada),([20,38],0x161cf8c1248)],⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r4 :C ⟨6,23,2⟩ ⟨48,38,12⟩ :=
  r! ⟨6,23,2⟩,⟨48,38,12⟩,33,0x1d65310b05166b2,[([36,6],0x10b167e85aea),([6,7],0x2e8435022ab),([8,10],0x1dc4cea774c),([12,21],0xa0ecf2ceda)],⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r5:C ⟨49,23,2⟩ ⟨133,29,9⟩ :=
  r! ⟨49,23,2⟩,⟨133,29,9⟩,36,0x26f400254c9c0bb,[([39,6],0x11c894ff9fd3),([7,8],0x2adacf8f32b),([10,13],0x135ba86be36),([26],0x2e0efcf27a)],⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r6:C ⟨49,30,2⟩ ⟨91,38,12⟩ :=
  r! ⟨49,30,2⟩,⟨91,38,12⟩,37,0x2f2bfa1ee601954,[([43,10],0x13ec80a51b5d),([14,26],0x2159aad748a)],⟨(by decide +kernel),(by decide +kernel),trivial⟩
private theorem r7:C ⟨92,30,2⟩ ⟨133,38,12⟩ :=
  p! ⟨92,30,2⟩,[([44,4],0x133cd95ec0ac),([4,5],0x1b76a15d73e),([6,8],0xecdf397d86),([14],0x2b9c300cc8)],⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
theorem B:C ⟨1,17,1⟩ ⟨133,38,12⟩ :=
  Certificate.trim (.splitT 1
    (Certificate.trim (r1))
    (.rK 22
      (Certificate.trim (.splitB 34
        (r2)
        (r3)))
      (Certificate.trim (.splitB 48
        (r4)
        (.rK 29
          (Certificate.trim (r5))
          (.splitB 91
            (r6)
            (r7)))))))
end qcZ3orc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qJrCx9a
open P6_6 P6_6_8 q2w4Sxc
set_option quotPrecheck false in
local notation "r!" nn "," mm "," cs =>
  receipt nn mm cs rfl rfl rfl (by decide)
    (by repeat' first | exact rfl | exact True.intro | apply And.intro)
local notation "o!" hc "," ff "," aa "," hh =>
  C8 hh (by decide) (by decide) (by decide) (by decide) hc
    (f :=ff) (a :=aa) rfl rfl (by decide)
private theorem a3:CompanionTest ⟨3,7,1⟩ ⟨1,3,1⟩ 27 :=
  r! 178,0x160733fd718d,[([8,9,10,9,8,8,9,10],0x12b36a0a4dbb),
  ([9,9,10,12,11,14,16,26],0x353c9f323d2)]
private theorem p3:CompanionTest ⟨3,7,1⟩ ⟨1,12,1⟩ 77 :=
  r! 138,0x1617d7b1820a,[([3,4,3,4,3,4,3,4],0x9cfa9c6d3e8),
  ([3,4,4,4,4,4,4,4],0x7439dca1216),
  ([5,3,3,3,4,4,3,4],0x3ff3a1b5e8b),
  ([3,4,3,4,4,5,5,5],0xfa3a932ff4),
  ([17],0xb1b720d8d)]
private theorem h3:CompanionTest ⟨3,7,1⟩ ⟨2,6,2⟩ 46 :=
  r! 152,0x160c7eb9efa4,[([7,8,8,9,10,10,8,9],0x12ed15400aa0),
  ([14,17,19,33],0x31f6979e504)]
private theorem q31 :Lw ⟨3,7,1⟩=⟨0x10b9467b345ce,0x7510a80729654,0xa58c42783cb⟩:= by decide +kernel
theorem s31 :Certificate ⟨3,7,1⟩ ⟨1,3,1⟩ (cap ⟨3,7,1⟩) :=
  assemble (b:=130) (m:=11) (t:=15) (u:=3) rfl rfl
    (o! q31,0x167a5350afd389,0x17090cad328c95,a3)
    (o! q31,0x2d45ba726f2f31,0x2e12195a65192a,h3)
    p3
private theorem q32 :Lw ⟨3,7,2⟩=⟨0x10b11d181ed04,0x743c798a469da,0x27bbf733a7c9⟩:= by decide +kernel
theorem s32 :Certificate ⟨3,7,2⟩ ⟨1,3,1⟩ (cap ⟨3,7,2⟩) :=
  assemble (b:=130) (m:=11) (t:=14) (u:=3) rfl rfl
    (o! q32,0x167a5350afd389,0x16fe2492a2d25b,(top_mono a3))
    (o! q32,0x2d45ba726f2f31,0x2dfc492545a4b6,(top_mono h3))
    (top_mono p3)
private theorem a4 :CompanionTest ⟨4,7,1⟩ ⟨1,3,1⟩ 28 :=
  r! 179,0x1602d655d160,[([8,9,11,8,8,8,9,10],0x129d0bb7c856),
  ([9,9,10,12,11,14,43],0x365ca9e090a)]
private theorem p4 :CompanionTest ⟨4,7,1⟩ ⟨1,12,1⟩ 80 :=
  r! 139,0x161356cd3c3b,[([3,4,3,4,3,4,3,4],0x9c611a2b728),
  ([3,4,4,4,4,4,4,4],0x72bee2590ec),
  ([5,3,3,6,4,2,3,4],0x4176ec3446c),
  ([3,4,3,4,4,5,5,5],0x1033e050329),
  ([6,11],0x6aa3cac92)]
private theorem h4 :CompanionTest ⟨4,7,1⟩ ⟨2,6,2⟩ 48 :=
  r! 153,0x16086f96e929,[([7,8,8,9,10,11,8,9],0x13003522bdd1),
  ([14,17,19,33],0x3083a742b58)]
private theorem q41 :Lw ⟨4,7,1⟩=⟨0xfcfe657bff2c,0x6db6938123192,0x9b8a48d8ad4⟩:= by decide +kernel
theorem s41 :Certificate ⟨4,7,1⟩ ⟨1,3,1⟩ (cap ⟨4,7,1⟩) :=
  assemble (b:=129) (m:=11) (t:=15) (u:=3) rfl rfl
    (o! q41,0x156c3a8483fcfe,0x1598f2b2401eb6,a4)
    (o! q41,0x2aa9ca7a92e948,0x2b31e564803d6c,h4)
    p4
private theorem q42 :Lw ⟨4,7,2⟩=⟨0xfc7e2280f012,0x6ced608977a92,0x2552c55d88ba⟩:= by decide +kernel
theorem s42 :Certificate ⟨4,7,2⟩ ⟨1,3,1⟩ (cap ⟨4,7,2⟩) :=
  assemble (b:=129) (m:=11) (t:=14) (u:=3) rfl rfl
    (o! q42,0x156c3a8483fcfe,0x158e5301a4e882,(top_mono a4))
    (o! q42,0x2aa9ca7a92e948,0x2b1ca60349d104,(top_mono h4))
    (top_mono p4)
private theorem a5:CompanionTest ⟨5,7,1⟩ ⟨1,3,1⟩ 25 :=
  r! 178,0x160d6b383746,[([8,9,10,8,8,8,9,9],0x120a9dacac17),
  ([18,22,25,44],0x402cd8b8b2f)]
private theorem p5:CompanionTest ⟨5,7,1⟩ ⟨1,11,1⟩ 84 :=
  r! 145,0x161667417bac,[([3,2,2,3,2,2,3,2],0x6f371e92e0c),
  ([2,3,2,2,3,4,4,4],0x68e11ac9164),
  ([4,4,4,2,3,3,3,3],0x4d7e5d86b84),
  ([3,3,3,5,2,3,2,2],0x2acce2d6bd8),
  ([4,4,4,4,4,5,5,5],0x1099a2f866c),
  ([7,11],0x695765e74)]
private theorem h5:CompanionTest ⟨5,7,1⟩ ⟨2,6,2⟩ 42 :=
  r! 150,0x160cfc3eb22d,[([15,16,18,8,9,14,17,20],0x15da34c3d2ee),
  ([33],0x32c77adf3f)]
private theorem q51 :Lw ⟨5,7,1⟩=⟨0xeb292e0afc71,0x653930c34b7b5,0x8cf74f18b21⟩:= by decide +kernel
theorem s51 :Certificate ⟨5,7,1⟩ ⟨1,3,1⟩ (cap ⟨5,7,1⟩) :=
  assemble (b:=128) (m:=10) (t:=15) (u:=3) rfl rfl
    (o! q51,0x136b6406e7fd4f,0x13eeb1c79aaeb1,a5)
    (o! q51,0x27823274b6b294,0x27dd638f355d62,h5)
    p5
private theorem q52 :Lw ⟨5,7,2⟩=⟨0xeaae2e72fcc3,0x647e2d36e2320,0x222f54014504⟩:= by decide +kernel
theorem s52 :Certificate ⟨5,7,2⟩ ⟨1,3,1⟩ (cap ⟨5,7,2⟩) :=
  assemble (b:=128) (m:=10) (t:=14) (u:=3) rfl rfl
    (o! q52,0x136b6406e7fd4f,0x13e485fcbeab27,(top_mono a5))
    (o! q52,0x27823274b6b294,0x27c90bf97d564e,(top_mono h5))
    (top_mono p5)
private theorem a6:CompanionTest ⟨6,7,1⟩ ⟨1,3,1⟩ 27 :=
  r! 178,0x15fda50107d5,[([8,9,10,8,8,8,9,9],0x1202c45431f0),
  ([18,22,25,44],0x3fae0acd5e5)]
private theorem p6:CompanionTest ⟨6,7,1⟩ ⟨1,11,1⟩ 88 :=
  r! 148,0x1617540b4ed7,[([3,2,2,3,2,2,3,2],0x6ee8c08e1fe),
  ([2,3,2,2,2,2,4,4],0x5ca4dca9f98),
  ([4,4,4,4,2,3,4,5],0x59dee3cdb9b),
  ([5,5,4,4,2,2,2,3],0x2e98815504a),
  ([2,3,4,4,4,5,5,6],0xd161d4c556),
  ([7,11],0x5a210dc06)]
private theorem h6:CompanionTest ⟨6,7,1⟩ ⟨2,6,2⟩ 45 :=
  r! 151,0x15dc3c78828a,[([15,16,10,10,8,8,14,17],0x1529acae925a),
  ([20,33],0xb28fc9f030)]
private theorem q61 :Lw ⟨6,7,1⟩=⟨0xdaedeb5c7d80,0x5d6a0e2efb2c4,0x88703e747ce⟩:= by decide +kernel
theorem s61 :Certificate ⟨6,7,1⟩ ⟨1,3,1⟩ (cap ⟨6,7,1⟩) :=
  assemble (b:=127) (m:=10) (t:=15) (u:=3) rfl rfl
    (o! q61,0x11bdad404bf944,0x1267579812dd9a,a6)
    (o! q61,0x241e464f569dc3,0x24ceaf3025bb34,h6)
    p6
private theorem q62 :Lw ⟨6,7,2⟩=⟨0xda74f57b1d02,0x5cb90fbef6d69,0x205f152292dd⟩:= by decide +kernel
theorem s62 :Certificate ⟨6,7,2⟩ ⟨1,3,1⟩ (cap ⟨6,7,2⟩) :=
  assemble (b:=127) (m:=10) (t:=14) (u:=3) rfl rfl
    (o! q62,0x11bdad404bf944,0x125d86fe6bf81a,(top_mono a6))
    (o! q62,0x241e464f569dc3,0x24bb0dfcd7f034,(top_mono h6))
    (top_mono p6)
end qJrCx9a
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qJrCx9a
open P6_6 P6_6_8 q2w4Sxc
set_option quotPrecheck false in
local notation "r!" nn "," mm "," cs =>
  receipt nn mm cs rfl rfl rfl (by decide)
    (by repeat' first | exact rfl | exact True.intro | apply And.intro)
local notation "o!" hc "," ff "," aa "," hh =>
  C8 hh (by decide) (by decide) (by decide) (by decide) hc
    (f :=ff) (a :=aa) rfl rfl (by decide)
private theorem a7:CompanionTest ⟨7,7,1⟩ ⟨1,3,1⟩ 28 :=
  r! 179,0x15d61ec6d4b4,[([8,9,10,8,8,8,9,9],0x11ecd519471a),
  ([18,22,26,44],0x3e949ad8d9a)]
private theorem p7:CompanionTest ⟨7,7,1⟩ ⟨1,11,1⟩ 92 :=
  r! 150,0x16166fd93019,[([3,2,2,3,2,2,3,2],0x6e9a62895f0),
  ([2,3,4,4,4,4,4,4],0x78690f36436),
  ([4,4,2,3,5,5,5,5],0x52e01694709),
  ([3,4,4,3,2,3,2,3],0x1f1cb9fe251),
  ([4,4,4,5,5,5,7,11],0x866bb40c99)]
private theorem h7:CompanionTest ⟨7,7,1⟩ ⟨2,6,2⟩ 48 :=
  r! 153,0x15f2d1e869a3,[([15,16,10,11,8,8,14,17],0x1540e3237783),
  ([20,34],0xb1eec4f220)]
private theorem q71 :Lw ⟨7,7,1⟩=⟨0xcc19a377d072,0x5638aed0c708a,0x7b58dc26b18⟩:= by decide +kernel
theorem s71 :Certificate ⟨7,7,1⟩ ⟨1,3,1⟩ (cap ⟨7,7,1⟩) :=
  assemble (b:=126) (m:=10) (t:=15) (u:=3) rfl rfl
    (o! q71,0x10e86ccf889214,0x10fe6ff85f8d28,a7)
    (o! q71,0x21269c1557597c,0x21fcdff0bf1a50,h7)
    p7
private theorem q72 :Lw ⟨7,7,2⟩=⟨0xcba4a11bea94,0x55941c4850b8c,0x1d91b07ceb94⟩:= by decide +kernel
theorem s72 :Certificate ⟨7,7,2⟩ ⟨1,3,1⟩ (cap ⟨7,7,2⟩) :=
  assemble (b:=126) (m:=10) (t:=14) (u:=3) rfl rfl
    (o! q72,0x10e86ccf889214,0x10f4fb9f27f8cc,(top_mono a7))
    (o! q72,0x21269c1557597c,0x21e9f73e4ff198,(top_mono h7))
    (top_mono p7)
private theorem a8:CompanionTest ⟨8,7,1⟩ ⟨1,3,1⟩ 25 :=
  r! 178,0x15ebf5de40f0,[([8,8,10,8,16,18,18,22],0x15124feea4c8),
  ([26,44],0xd9a5ef9c28)]
private theorem p8:CompanionTest ⟨8,7,1⟩ ⟨1,10,1⟩ 98 :=
  r! 157,0x161728d6f922,[([3,2,2,3,2,2,3,2],0x6e4c04849e2),
  ([2,2,2,2,2,2,2,4],0x4f73c1faef2),
  ([4,4,4,2,3,4,2,3],0x517a3471b34),
  ([2,3,5,5,3,3,3,4],0x36140083e1b),
  ([4,4,2,3,2,3,4,4],0x17ac5387b1a),
  ([5,5,5,6,7,12],0x4783e72be5)]
private theorem h8:CompanionTest ⟨8,7,1⟩ ⟨2,6,2⟩ 42 :=
  r! 150,0x15c587bea6b9,[([14,16,19,16,14,17,20,34],0x15c587bea6b9)]
private theorem q81 :Lw ⟨8,7,1⟩=⟨0xb81aaa931e34,0x4d34339d38095,0x6f0aa21c309⟩:= by decide +kernel
theorem s81 :Certificate ⟨8,7,1⟩ ⟨1,3,1⟩ (cap ⟨8,7,1⟩) :=
  assemble (b:=125) (m:=9) (t:=15) (u:=3) rfl rfl
    (o! q81,0xeec39fa23d476,0xf38d5022f62fc,a8)
    (o! q81,0x1dd3fa5eb45c61,0x1e71aa045ec5f8,h8)
    p8
private theorem q82 :Lw ⟨8,7,2⟩=⟨0xb7aa20ef2516,0x4c9d80c5ec70c,0x1a9ae3bb0b3f⟩:= by decide +kernel
theorem s82 :Certificate ⟨8,7,2⟩ ⟨1,3,1⟩ (cap ⟨8,7,2⟩) :=
  assemble (b:=125) (m:=9) (t:=14) (u:=3) rfl rfl
    (o! q82,0xeec39fa23d476,0xf2fcd29c68579,(top_mono a8))
    (o! q82,0x1dd3fa5eb45c61,0x1e5f9a538d0af2,(top_mono h8))
    (top_mono p8)
private theorem a9:CompanionTest ⟨9,7,1⟩ ⟨1,3,1⟩ 29 :=
  r! 179,0x160320c1fd44,[([8,9,9,9,16,18,18,22],0x15314c410578),
  ([25,45],0xd1d480f7cc)]
private theorem p9:CompanionTest ⟨9,7,1⟩ ⟨1,10,1⟩ 107 :=
  r! 162,0x16166663df5f,[([3,2,2,3,2,2,3,2],0x6dfda67fdd4),
  ([2,2,2,2,2,2,2,2],0x46d7b8a2796),
  ([2,4,2,3,4,2,3,4],0x4da88de628b),
  ([2,3,2,3,3,3,3,3],0x2ecdc0e91c1),
  ([3,3,3,3,3,4,4,4],0x23226fd2b70),
  ([3,3,4,4,5,5,5,6],0xc9d13a389e),
  ([7,12],0x5b34d619b)]
private theorem h9:CompanionTest ⟨9,7,1⟩ ⟨2,6,2⟩ 47 :=
  r! 152,0x15b9557dd3f2,[([15,16,10,10,16,14,17,20],0x1587a6c3b9b8),
  ([34],0x31aeba1a3a)]
private theorem q91 :Lw ⟨9,7,1⟩=⟨0x9e485f84dd3c,0x422a601fcf144,0x603f80b1576⟩:= by decide +kernel
theorem s91 :Certificate ⟨9,7,1⟩ ⟨1,3,1⟩ (cap ⟨9,7,1⟩) :=
  assemble (b:=124) (m:=9) (t:=15) (u:=3) rfl rfl
    (o! q91,0xc9e219cfd02f6,0xd0c3e5d86c67e,a9)
    (o! q91,0x19e32769214442,0x1a187cbb0d8cfc,h9)
    p9
private theorem q92 :Lw ⟨9,7,2⟩=⟨0x9ddf571270f2,0x41a4edef5110d,0x170b022cf722⟩:= by decide +kernel
theorem s92 :Certificate ⟨9,7,2⟩ ⟨1,3,1⟩ (cap ⟨9,7,2⟩) :=
  assemble (b:=124) (m:=9) (t:=14) (u:=3) rfl rfl
    (o! q92,0xc9e219cfd02f6,0xd03d6f61e9b3b,(top_mono a9))
    (o! q92,0x19e32769214442,0x1a07adec3d3676,(top_mono h9))
    (top_mono p9)
private theorem Ki:CompanionTest ⟨10,7,1⟩ ⟨1,3,1⟩ 28 :=
  r! 179,0x160cbfc05f4c,[([16,9,9,16,18,18,22,26],0x15d047c99e8b),
  ([45],0x3c77f6c0c1)]
private theorem p10 :CompanionTest ⟨10,7,1⟩ ⟨1,9,1⟩ 122 :=
  r! 174,0x1617bbd8a991,[([1,2,2,2,1,2,2,2],0x536315e42aa),
  ([2,2,2,2,2,2,2,2],0x4c01ddd4c44),
  ([2,2,2,2,2,2,2,1],0x3769c35a6aa),
  ([2,2,1,2,2,3,2,3],0x2fbddeb4d85),
  ([2,3,2,3,2,3,2,3],0x27cc796ad8d),
  ([2,3,2,3,3,3,3,3],0x1c4bb15bb44),
  ([3,3,3,4,2,3,3,3],0x118ae0841e7),
  ([3,3,3,3,3,4,4,8],0x519b4641b0),
  ([15],0x326813a0c)]
private theorem Kr :CompanionTest ⟨10,7,1⟩ ⟨2,6,2⟩ 45 :=
  r! 151,0x15ae41dbd66f,[([14,16,20,16,14,17,20,34],0x15ae41dbd66f)]
private theorem q101 :Lw ⟨10,7,1⟩=⟨0x7ba4910083d0,0x3410b8e179fbc,0x4db31b56528⟩:= by decide +kernel
theorem s101 :Certificate ⟨10,7,1⟩ ⟨1,3,1⟩ (cap ⟨10,7,1⟩) :=
  assemble (b:=123) (m:=8) (t:=15) (u:=2) rfl rfl
    (o! q101,0x9e6bcbb218863,0xa43a26cfcc82c,Ki)
    (o! q101,0x142a9a005ba0db,0x148744d9f99058,Kr)
    p10
private theorem q102 :Lw ⟨10,7,2⟩=⟨0x7b474d7040c7,0x33a165ff56e84,0x1293fad5a624⟩:= by decide +kernel
theorem s102 :Certificate ⟨10,7,2⟩ ⟨1,3,1⟩ (cap ⟨10,7,2⟩) :=
  assemble (b:=123) (m:=8) (t:=14) (u:=2) rfl rfl
    (o! q102,0x9e6bcbb218863,0xa3c1e68263277,(top_mono Ki))
    (o! q102,0x142a9a005ba0db,0x14783cd04c64ee,(top_mono Kr))
    (top_mono p10)
end qJrCx9a
end
