import ProximityPrize.SubmissionLower.GoldBranch7N1
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_3
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l1v0 : List Lane := [⟨21,20,1,1,1⟩,⟨22,18,2,31,0x3f7ffffb7efffff8⟩,⟨23,16,3,7,912676⟩,⟨24,14,4,31,0xfdfffeb9fbfff9b3f7fff5efeffffad⟩,⟨25,12,5,11,0x14a8714415007e⟩,⟨26,10,6,31,0x3f7fff19fefff89ffdffe863fbffdb47f7ffe47feffff83⟩,⟨27,8,7,13,0x7391b91b893029585e8054⟩,⟨28,6,8,31,0xfdfffd6ffbffe27ff7ff724feffe909fdffdd8ffbffe27ff7fff2efeffffdd⟩,⟨29,4,9,13,0xa521c2f424c113a4ec0d20120009⟩,⟨30,2,10,31,0x3f7fffe57efffe6cfdfff5e3fbffdb47f7ffad5fefff89ffdfff973fbfffca7f7ffff37f000000⟩,⟨31,1,10,10,0x2c5a512a0dcaf46909006c02⟩,⟨32,0,10,31,0x3f8000007efffff8fdffffbbfbfffeb7f7fffc1feffff83fdffff5bfbffff77f7ffffc7f000000⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 94
  free := [(20,0)]
  vectors := [l1v0].map (vectorData false 41 11)
private def b1 := bands [(0,22,20),(1,23,18),(2,24,16),(3,25,14),(4,26,12),(5,27,10),(6,28,8),(7,29,6),(8,30,4),(9,31,2)]
private theorem k1v0 : good false 41 l1v0 b1 := rfl
private theorem v1j0 : CJ6.VectorDots 41 11 z1 0 := v! false, 41, b1, l1v0, k1v0
theorem r1 : (CJ0.blockMatrix CJ6.source 41 ((11 : ℤ)-20)).rank ≤ 94 :=
  (CJ6.block_rank_le 41 11).trans (CJ6.rank_of_dots (z := z1) (by decide) (CJ6.belowSucc CJ6.belowZero v1j0))
private def l2v0 : List Lane := [⟨21,0,0,0,0⟩,⟨22,0,0,0,0⟩,⟨23,0,0,0,0⟩,⟨24,14,3,31,0x7f7fffff80000001⟩,⟨25,12,4,31,0xfdffffee0000003000000027efffffb⟩,⟨26,10,5,31,0x2dfdffffdffbffff3000000060000000f⟩,⟨27,8,6,31,0x3f7fffc4feffffd10000014000000103f7fffe7feffffed⟩,⟨28,6,7,31,0x348000007e7effff4bfdfffdd20000000000000230000000f⟩,⟨29,4,8,31,0xfdfffe0bfbfff827f7fffe4800001a4000001a5fbffff27f7fffe8fefffffb⟩,⟨30,2,9,31,0xd2000004980000065bf7fff90fefffea3fdffff76000000ac000000800000001⟩,⟨31,1,9,31,0x7effff89fdfffca3fbfff807f7fffc8800000d20000011800000023f7ffffafeffffff⟩,⟨32,0,9,31,0x2d0000018c00000514000006c00000000fdffff77fbffff98000000000000001⟩,⟨33,0,8,31,0xfdffffeffbffff37f7fffcafeffff93fdffff9e00000000000000400000002⟩,⟨34,0,7,5,0x4cfa3cc1⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l2v1 : List Lane := [⟨21,0,0,0,0⟩,⟨22,0,0,0,0⟩,⟨23,16,2,31,0xff000000⟩,⟨24,14,2,31,0x3f7ffff780000011⟩,⟨25,12,4,31,0xfdffff940000024c0000002feffffb0⟩,⟨26,10,5,31,0x14afdfffd4bfbfff82c0000074000000b9⟩,⟨27,8,6,31,0x3f7ffe11feffffef00000e08000006f3f7ffeaf7effff16⟩,⟨28,6,7,31,0x1ce000003727efff637fdffea22000004ec00001ab000000ab⟩,⟨29,4,8,31,0xfdffedf7fbffbdbc00001030000125200000f0bfbfff373f7ffeea7effffbe⟩,⟨30,2,9,31,0x7bc000029a000003023f7ffa18fefff1a6fdfffba200000840000005a0000000b⟩,⟨31,1,9,31,0x7efffb7efdffe029fbffb857f7ffef68000096f00000b360000009bf7fffbbfeffffeb⟩,⟨32,0,9,31,0x1b800000efc0000304400003c87effff52fdfff9fffbfffbb000000020000000b⟩,⟨33,0,8,31,0xfdffff3dfbfff803f7ffdef7efffbd8fdfffc6000000054000002b80000015⟩,⟨34,0,7,8,0xa3c96c8963c0a⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l2v2 : List Lane := [⟨21,0,0,0,0⟩,⟨22,0,0,0,0⟩,⟨23,16,3,31,0x400000007f000000⟩,⟨24,14,4,31,0xfdffffee00000003f7ffffc80000010⟩,⟨25,12,5,31,0x2dfdfffff00000018ff7ffff37effffb6⟩,⟨26,10,6,31,0x3f7fffc480000051fdfffd6ffbfffb30000008a000000aa⟩,⟨27,8,7,31,0x34bf7fff5e8000016e00000b40000001cbf7ffea57effff2a⟩,⟨28,6,8,31,0xfdfffe0a00000bd000000fc7efff629fdffef9a0000098400001a40000009c⟩,⟨29,4,9,31,0xd2fdfff727fbffdd3c00003090000106800000a1ffbfff143f7ffef47effffc4⟩,⟨30,2,10,31,0x3f7fffc48000046e00001a880000145bf7ff970fefff390fdfffdee000008c400000560000000a⟩,⟨31,1,10,31,0x16fefffd0dfdffe929fbffcfa400000930000096f000009affbffff8ff7fffba7effffec⟩,⟨32,0,10,31,0x3f7ffffb8000014400000bc00000258000002a67efffe80fdfffa1bfbfffc2c00000050000000b⟩,⟨33,0,9,31,0x1fdffff61fbfff943f7ffe417efffc8cfdfffd34000000c4000002b80000014⟩,⟨34,0,7,8,0x93687b4873609⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l2v3 : List Lane := [⟨21,0,0,0,0⟩,⟨22,18,1,1,1⟩,⟨23,16,1,31,0x7effffef⟩,⟨24,14,2,31,0x3f7ffff780000099⟩,⟨25,12,4,31,0xfdfffe4a00000a0bf7fff4ffefffdad⟩,⟨26,10,5,31,0x5cdfdfff067fbffe318000043e000004dd⟩,⟨27,8,6,31,0x3f7ff6b8800003cc000047d000000603f7ff664fefffa1f⟩,⟨28,6,7,31,0x90600000e467effc5c3fdff9702000041a00000b1300000427⟩,⟨29,4,8,31,0xfdffa333fbfec1140000bfa000065b8000041a1fbffa0dff7ff91ffefffe69⟩,⟨30,2,9,31,0x289b0000d3c80000d00bf7fdaecfeffb213fdfff13e000036e4000022800000042⟩,⟨31,1,9,31,0x7effe7f1fdff58cffbfe97a7f7ffeb0800037c800003cb5fbfffe97f7ffe50feffff7d⟩,⟨32,0,9,31,0x9480000504c0000fe9400012f07efff971fdffdce7fbffe828000001800000042⟩,⟨33,0,8,31,0xfdfffbcbfbffd46ff7ff4cffeffe9bdfdffed420000034800000ff00000078⟩,⟨34,0,7,11,0xdca5339898ce4a5037⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l2v4 : List Lane := [⟨21,0,0,0,0⟩,⟨22,19,1,1,1⟩,⟨23,16,1,31,0x7effffee⟩,⟨24,14,4,31,0xfdffff9400000003f7fffea800000e8⟩,⟨25,12,5,31,0x14afdffff3c00001077f7ffec47efffc20⟩,⟨26,10,6,31,0x3f7ffe118000037bfdffe107fbffd56800007d100000866⟩,⟨27,8,7,31,0x1ce3f7ff90a800014fa00007bc1fbfff377f7fee3a7efff5ac⟩,⟨28,6,8,31,0xfdffedf6000081f000005e87eff8a89fdff57060000954c00014820000075c⟩,⟨29,4,9,31,0x7bcfdff9e8ffbfeae0c0002a930000ba3600005dcbfbff3ccbf7ff33f7efffd2a⟩,⟨30,2,10,31,0x3f7ffdbf000030ba000113b80000964bf7fb059feff760efdfff41600006d2c000040280000076⟩,⟨31,1,10,31,0xdc7effdf85fdff0bf5fbfe15e40000ca200006e5500006a7bfbfff4dff7ffcaffeffff0a⟩,⟨32,0,10,31,0x3f7fffcf00000dec00007f5800018f600001a977effeb4efdffbbc3fbffd55c000004880000081⟩,⟨33,0,9,31,0xafdfff90dfbffb60bf7fecfe7effdaccfdffe2e800000a9c00001f6800000e3⟩,⟨34,0,7,11,0x18d295cdf7973529063⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l2v5 : List Lane := [⟨21,20,1,1,1⟩,⟨22,0,0,0,0⟩,⟨23,16,1,31,0x7effff43⟩,⟨24,14,4,31,0xfdfffe4a00000000000008c00000730⟩,⟨25,12,5,31,0x5cdfdfffb5e00004babf7ff2adfeffe3f9⟩,⟨26,10,6,31,0x3f7ff6b8800014e2fdff509bfbff7e5c0003d80000039d4⟩,⟨27,8,7,31,0x9063f7fd63c8000866400029d01fbfe97d7f7f8139feffbae7⟩,⟨28,6,8,31,0xfdffa33200030ba000013b07efd3f31fdfcaae20004d5080008b7400003048⟩,⟨29,4,9,31,0x289bfdfdb74bfbf8c4140011b020004464c00018c7dfbfa86eff7fabaffeffeda0⟩,⟨30,2,10,31,0x3f7ff3f88001245c00062fd000025fb3f7e0c44fefcdc5f00000ff80002e3080001a00000002f4⟩,⟨31,1,10,31,0x4a47eff3d19fdfa69b7fbf5404400066360002aafe00026e75fbff9197f7fea4cfefff9d7⟩,⟨32,0,10,31,0x3f7ffef2800053880002f2d000091d4000093907eff70fffdfe5963fbff0194000022a00000336⟩,⟨33,0,9,31,0x37fdffd63ffbfe464ff7f8f09feff24ddfdff5a2600004a980000c3f00000575⟩,⟨34,0,7,14,0x25237b22ceb9a22ce37b0252⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def z2 : CJ1.Block where
  bank := .rightHigh
  cap := 94
  free := [(16,1),(17,1),(18,0),(18,1),(19,0),(20,0)]
  vectors := [l2v0,l2v1,l2v2,l2v3,l2v4,l2v5].map (vectorData false 41 12)
private def b2 := bands [(0,23,19),(1,24,17),(2,25,15),(3,26,13),(4,27,11),(5,28,9),(6,29,7),(7,30,5),(8,31,3),(9,32,1)]
private theorem k2v0 : good false 41 l2v0 b2 := rfl
private theorem v2j0 : CJ6.VectorDots 41 12 z2 0 := v! false, 41, b2, l2v0, k2v0
private theorem k2v1 : good false 41 l2v1 b2 := rfl
private theorem v2j1 : CJ6.VectorDots 41 12 z2 1 := v! false, 41, b2, l2v1, k2v1
private theorem k2v2 : good false 41 l2v2 b2 := rfl
private theorem v2j2 : CJ6.VectorDots 41 12 z2 2 := v! false, 41, b2, l2v2, k2v2
private theorem k2v3 : good false 41 l2v3 b2 := rfl
private theorem v2j3 : CJ6.VectorDots 41 12 z2 3 := v! false, 41, b2, l2v3, k2v3
private theorem k2v4 : good false 41 l2v4 b2 := rfl
private theorem v2j4 : CJ6.VectorDots 41 12 z2 4 := v! false, 41, b2, l2v4, k2v4
private theorem k2v5 : good false 41 l2v5 b2 := rfl
private theorem v2j5 : CJ6.VectorDots 41 12 z2 5 := v! false, 41, b2, l2v5, k2v5
theorem r2 : (CJ0.blockMatrix CJ6.source 41 ((12 : ℤ)-20)).rank ≤ 94 :=
  (CJ6.block_rank_le 41 12).trans (CJ6.rank_of_dots (z := z2) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v2j0) v2j1) v2j2) v2j3) v2j4) v2j5))
private def l3v0 : List Lane := [⟨8,8,2,30,0x8c234f740000001⟩,⟨7,7,4,30,0x8c234f76308d3de0000003c000008c⟩,⟨6,6,6,31,0x118469eec611a7bb4611a7da0000026c000021e800016e3⟩,⟨5,5,8,31,0x4611a7bba469ee6348d3dd42308d488000009b000006c800003d080001c560⟩,⟨4,4,10,31,0x118469ee8d234f74a669ee7e348d40bd1846cb000001ff800012a600008fdc0003a71600144aec⟩,⟨3,3,12,31,0x4611a7bac0b08d4702c2359e058476e6058531e8c23e5600005a940002d4a000131b38006e64600227f5e009688e0⟩,⟨2,2,14,31,0x118469eed334f72e2308d40706c238808c2387e533522e746135d00000e2720006311e002526b400c12fa8036e1e700db879c0308cc28⟩,⟨1,1,16,31,0x4611a7bbd8f72c2f25cb098d334f823a669fe3992e64f8fb1f68b3a30d3848001fd80800c623c0042df44013c1f7005252da812ff6d803e6bd580b71a2e0⟩,⟨0,0,18,31,0x118469ee9a469ee7b7ee5876e3b9654d3b4fb9f38ee92feb7f0ca92693026b918e9226004174f4016e8ef0070777e01e75b2207527234191aac204cfc7640d3b645320b0d9be⟩]
private def z3 : CJ1.Block where
  bank := .leftHigh
  cap := 89
  free := [(8,1)]
  vectors := [l3v0].map (vectorData true 41 13)
private def b3 := bands [(37,40,2),(36,38,4),(35,36,6),(34,34,8),(33,33,9),(32,32,10),(31,31,10),(30,30,10),(29,29,9),(28,28,8),(27,27,7),(26,26,6),(25,25,5),(24,24,4),(23,23,3),(22,22,2),(21,21,1)]
private theorem k3v0 : good true 41 l3v0 b3 := rfl
private theorem v3j0 : CJ6.VectorDots 41 13 z3 0 := v! true, 41, b3, l3v0, k3v0
theorem r3 : (CJ0.blockMatrix CJ6.source 41 ((13 : ℤ)-20)).rank ≤ 89 :=
  (CJ6.block_rank_le 41 13).trans (CJ6.rank_of_dots (z := z3) (by decide) (CJ6.belowSucc CJ6.belowZero v3j0))
end CJ6_3
end
section
namespace CJ6_3
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l4v0 : List Lane := [⟨22,0,0,0,0⟩,⟨23,0,0,0,0⟩,⟨24,16,2,31,0xff000000⟩,⟨25,14,3,31,0x1fbffffdc000000100000007⟩,⟨26,12,4,31,0x5a0000006ff7fffef7effffec⟩,⟨27,10,5,31,0x7effff89fdfffeb200000070000003800000023⟩,⟨28,8,6,31,0x69000001ce00000189fbfffcf7f7fffa97effffde⟩,⟨29,6,7,31,0x1fbfffc17f7ffe86fefffd5300000000000004ec000004d00000015⟩,⟨30,4,8,31,0x1a400000c78000021b000001eafdfffea5fbfffc33f7fffda7efffffa⟩,⟨31,2,9,31,0x7effff89fdfffbb3fbfff0b7f7ffe78feffff520000011800000188000000a00000001⟩,⟨32,1,9,31,0x2d000001e60000085000001260000013b00000047fbffff5ff7ffff7feffffff⟩,⟨33,0,9,31,0x7efffff7fdffff87fbfffd83f7fff90feffff52fdffff77fbffffe8000000200000001⟩,⟨34,0,8,6,0x475638d51c1⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l4v1 : List Lane := [⟨22,0,0,0,0⟩,⟨23,18,1,1,1⟩,⟨24,16,1,31,0x7effffef⟩,⟨25,14,3,31,0x1fbffff28000002e00000062⟩,⟨26,12,4,31,0x295fbffffbff7ffee1fefffef7⟩,⟨27,10,5,31,0x7efffc23fdfff822000010a000002f4000001a4⟩,⟨28,8,6,31,0x39c00000e1c00000311fbffcf07f7ffbc3fefffe6b⟩,⟨29,6,7,31,0x1fbffdbeff7ff334feffecdd00000f50000041a0000038e000000ee⟩,⟨30,4,8,31,0xf780000723000011fe00000b7cfdffe767fbffd0fff7ffe47feffffb3⟩,⟨31,2,9,31,0x7efffb7efdffd723fbff7327f7ff2fcfefffd4500000f50000011f000000700000000b⟩,⟨32,1,9,31,0x1b80000126c00004fa00000ab800000aaa0000008dfbfff7b7f7fff9afeffffeb⟩,⟨33,0,9,31,0x7effff9efdfffb3bfbffe74ff7ffbbcfefff971fdfffafbfbffff5c00000180000000b⟩,⟨34,0,8,9,0x5119a55eaf3488c0a⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l4v2 : List Lane := [⟨22,0,0,0,0⟩,⟨23,19,1,1,1⟩,⟨24,16,3,31,0x1fbffffdc00000007efffff8⟩,⟨25,14,4,31,0x5bfbffffe0000001b0000003f⟩,⟨26,12,5,31,0x7effff89000000a3fbffff53f7fff397effff44⟩,⟨27,10,6,31,0x697efffebdfdfffc1200000d2000002370000013b⟩,⟨28,8,7,31,0x1fbfffc14000017a0000085e00000001fbffd8a7f7ffcae7efffec6⟩,⟨29,6,8,31,0x1a5fbffee4ff7ff7a2fefff35f00000ec40000362400002df000000bd⟩,⟨30,4,9,31,0x7effff89000008dc000050b80000d3500000762fdffe9ddfbffd853f7ffe947effffc2⟩,⟨31,2,10,31,0x16fefffd0dfdffe113fbff91c7f7ff5e9fefffec600000dc800000f78000005e80000009⟩,⟨32,1,10,31,0x3f7ffffb8000014400000ed6000041a000008dc0000089dfdffffd9fbfff86ff7fffa6feffffee⟩,⟨33,0,10,31,0xfeffffb0fdfffbeffbffeab3f7ffc4ffefffa58fdfffbbffbffff9800000168000000a⟩,⟨34,0,8,9,0x48fd7b3b9daf47e09⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def l4v3 : List Lane := [⟨22,20,1,1,1⟩,⟨23,0,0,0,0⟩,⟨24,16,3,31,0x1fbffff2800000007effff7a⟩,⟨25,14,4,31,0x295fbfffe7800001cb0000035d⟩,⟨26,12,5,31,0x7efffc23000006f7fbffe40bf7ff4ce7efff668⟩,⟨27,10,6,31,0x39c7efff215fdffec520000d9e00001d8800000f81⟩,⟨28,8,7,31,0x1fbffdbec000103e00004a52fdffb683fbfdd2dff7fd58d7efff0d4⟩,⟨29,6,8,31,0xf79fbff3d1ff7facd2feffa2fb000109c80002c9ac00023af000008f7⟩,⟨30,4,9,31,0x7efffb7e00006174000348a80007ee700001d88fdfebda1fbfe09abf7feea77efffd0d⟩,⟨31,2,10,31,0xdc7effdf85fdfeb5d3fbfb8cc7f7fa08480000fff0000b8680000be68000046e0000006b⟩,⟨32,1,10,31,0x3f7fffcf00000dec0000a0aa0002bce00005c49000052effdffedcdfbff9efff7ffbc47effff20⟩,⟨33,0,10,31,0x57efffc86fdffd36ffbff180bf7fd822feffc3b6fdffd45ffbfffec0000011700000076⟩,⟨34,0,8,12,0x632b581fd89d8981f2b5063⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩]
private def z4 : CJ1.Block where
  bank := .rightHigh
  cap := 91
  free := [(17,1),(18,1),(19,0),(20,0)]
  vectors := [l4v0,l4v1,l4v2,l4v3].map (vectorData false 42 11)
private def b4 := bands [(0,24,19),(1,25,17),(2,26,15),(3,27,13),(4,28,11),(5,29,9),(6,30,7),(7,31,5),(8,32,3),(9,33,1)]
private theorem k4v0 : good false 42 l4v0 b4 := rfl
private theorem v4j0 : CJ6.VectorDots 42 11 z4 0 := v! false, 42, b4, l4v0, k4v0
private theorem k4v1 : good false 42 l4v1 b4 := rfl
private theorem v4j1 : CJ6.VectorDots 42 11 z4 1 := v! false, 42, b4, l4v1, k4v1
private theorem k4v2 : good false 42 l4v2 b4 := rfl
private theorem v4j2 : CJ6.VectorDots 42 11 z4 2 := v! false, 42, b4, l4v2, k4v2
private theorem k4v3 : good false 42 l4v3 b4 := rfl
private theorem v4j3 : CJ6.VectorDots 42 11 z4 3 := v! false, 42, b4, l4v3, k4v3
theorem r4 : (CJ0.blockMatrix CJ6.source 42 ((11 : ℤ)-20)).rank ≤ 91 :=
  (CJ6.block_rank_le 42 11).trans (CJ6.rank_of_dots (z := z4) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v4j0) v4j1) v4j2) v4j3))
private def l5v0 : List Lane := [⟨8,9,1,1,1⟩,⟨7,7,4,30,0xfdffffebf7fff28fdffc63ff7f5ae5⟩,⟨6,6,6,31,0x3f7ffff9fefffe417effc7f1fbfb5609fbb632ffec693f3⟩,⟨5,5,8,31,0x7effffd6fdfff52bf7fea4cfefe35c9fde4041bfaa7a1d7ea7c144f7e7ac59⟩,⟨4,4,10,31,0x3f7ffff27efffc457eff86b5fbf5e447f760d28fe84ded1f9236ccbd2d7f746cf18cc68b8266a1⟩,⟨3,3,12,31,0x7effffb8fdffecc1fbfd8133f7c9c92fdc9c91bf9573fb7dcbea76f05ece8d92c859f7509f62b1322422300d2169b⟩,⟨2,2,14,31,0x3f7fffeafefffa0d7eff35cdfbee75a1fae19397e1adc71f4a776bbaa3bf62595295be871973c27f9be07098c5424af668928c398d56c⟩,⟨1,1,16,31,0x7effff9afdffe36bf7fc1c27efa788e7ea3a3baf947a0bbc5a6b24e2e12979275d661668b8f5479eb32aeaa7b89c11bede9a229b1cf17eb7e2129afa1760⟩,⟨0,0,18,31,0x3f7fffe37efff7997efed3d1fbe4ab8ff62c657fd78955b6e4fac7d636abb474846b8f03c7187438c6844442f4e5dc273acbc0762868eb390f6df3177e9211f1c32cdf6bc553⟩]
private def l5v1 : List Lane := [⟨8,8,1,1,1⟩,⟨7,7,4,31,0xbe8000037d000024fe000459fc00617⟩,⟨6,6,6,31,0x1fc00000800000103f800200fe002a66fa029b400020439⟩,⟨5,5,8,31,0x3f8000037d00006400000c200000ffc0000f974000bf6380077d66003eb794⟩,⟨4,4,10,31,0x80000021be8004320000596000057ea00043ef0002ada9c016a25600a2f73803f432b4⟩,⟨3,3,12,31,0xbe8000057d0000aefa0015f5f401dc50001dc4400175a2800ef2ed0080429203aadd0e1735014c802e0c7a6e6cf23⟩,⟨2,2,14,31,0x1fc00001000000343f8006e8fe00996afa09c988007d4680051bb8c02cab7d014d79e2086ac4c82f8e716aecbfc4281c7b34302568026⟩,⟨1,1,16,31,0x3f8000057d0000fdfc0021ebf8030323f8325597d292a7c01b71a600f532a4074ed3d6304c4495177251f592ec0ea965d0bcc6f96bb3b4a8d987bc0a0233⟩,⟨0,0,18,31,0x100000049be800a320000ed9dfc0fe32000d4d72bf11381e052fb7e028805d611219bdc6596017a1843bc4dc0206280a832b2b7d9236b1e54e4864ae97590076f8555⟩]
private def z5 : CJ1.Block where
  bank := .leftHigh
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [l5v0,l5v1].map (vectorData true 42 12)
private def b5 := bands [(38,42,1),(37,40,3),(36,38,5),(35,36,7),(34,34,9),(33,33,10),(32,32,10),(31,31,10),(30,30,9),(29,29,8),(28,28,7),(27,27,6),(26,26,5),(25,25,4),(24,24,3),(23,23,2),(22,22,1)]
private theorem k5v0 : good true 42 l5v0 b5 := rfl
private theorem v5j0 : CJ6.VectorDots 42 12 z5 0 := v! true, 42, b5, l5v0, k5v0
private theorem k5v1 : good true 42 l5v1 b5 := rfl
private theorem v5j1 : CJ6.VectorDots 42 12 z5 1 := v! true, 42, b5, l5v1, k5v1
theorem r5 : (CJ0.blockMatrix CJ6.source 42 ((12 : ℤ)-20)).rank ≤ 88 :=
  (CJ6.block_rank_le 42 12).trans (CJ6.rank_of_dots (z := z5) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v5j0) v5j1))
end CJ6_3
end
section
namespace CJ6_3
theorem proof : CJ6.c3 := ⟨r1, r2, r3, r4, r5, trivial⟩
end CJ6_3
end
