import ProximityPrize.SubmissionLower.SixRows3
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_5
open CJ6.Fast
open CJ6 (belowZero belowSucc)
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (rfl : good side q l b)
local notation "r!" q "," u "," pkt "," h =>
  Nat.le_trans (CJ6.block_rank_le q u) (CJ6.rank_of_dots (z := pkt) (by decide) h)
local notation "L[" a "," p "," n "," w "," x "]" => (⟨a,p,n,w,x⟩ : Lane)
local notation "L0[" a "]" => (⟨a,0,0,0,0⟩ : Lane)
private def l1v0 : List Lane := [L0[25],L0[26],L[27,16,1,1,1],L[28,14,2,31,0x3f7ffffc7efffffa],L[29,12,3,6,151061],L[30,10,4,31,0xfdffff5bfbfffcf7f7fffb77effffde],L[31,8,5,9,0x7ec46e5a423],L[32,6,6,31,0x3f7fffc1fefffe17fdfffa45fbfff7d3f7fffa97effffec],L[33,4,7,10,0x54622dfaf15e15007],L[34,2,8,31,0xfdffffbbfbfffcf7f7fff247efffdf4fdfffd47fbfffe0ff7ffff67f000000],L[35,1,8,8,0x93893d2af541502],L[36,0,8,31,0xfe000001fbffffebf7ffff67effffdefdffffbdfbffffb3f7ffffd7f000000],L0[37],L0[38],L0[39]]
private def l1v1 : List Lane := [L0[25],L[26,18,1,1,1],L[27,17,1,31,0x7efffff8],L[28,14,3,31,0x93f7ffffcfeffffe5],L[29,12,4,31,0xfdffff5a00000100000007e00000070],L[30,10,5,31,0x7efdfffe43fbfff0b7f7ffe5cfeffff2f],L[31,8,6,31,0x3f7fffc1800001c0000010d800002a000000299000000e0],L[32,6,7,31,0x153f7ffee8fefff485fdffdad3fbffc957f7ffdb4feffff75],L[33,4,8,31,0xfdffffba0000070000004fa000013b00000264800002680000012600000030],L[34,2,9,31,0x9fdfffe43fbffea97f7ff9c4fefff0f7fdffebe3fbfff197f7fffb4fefffffa],L[35,1,9,31,0x7f000000000000800000069000002300000064a00000a8000000a1000000500000000f],L[36,0,8,31,0xfdfffff3fbffff27f7fffacfefffee9fdfffdd3fbfffd67f7fffe4fefffff9],L0[37],L0[38],L0[39]]
private def l1v2 : List Lane := [L[25,20,1,1,1],L[26,19,1,31,0x7efffff8],L[27,17,2,31,0x127efffff8],L[28,14,4,31,0xfdffff5a0000012000000007effffad],L[29,12,5,31,0x7efdfffe0a00000090000017a0000017a],L[30,10,6,31,0x3f7fffc1800001f8fdfffe0bfbffd0c7f7ffa57fefffd0d],L[31,8,7,31,0x153f7ffec5800002f400003678000095a0000099900000348],L[32,6,8,31,0xfdffffba000007e3f7ffd8afeffd8a1fdff7633fbff2f57f7ff724fefffde5],L[33,4,9,31,0x9fdfffe0a000013b0000123600004c4a00009798000099900000492000000bd],L[34,2,10,31,0x3f80000000000048fdfffa1bfbffac07f7fe6a7feffc1fdfdffacabfbffc467f7ffeca7effffe5],L[35,1,9,31,0x7efffff8000001f800001b90000095a00001b1200002d4800002b5000001560000003f],L[36,0,8,31,0xfdffffbbfbfffc17f7ffe86fefffb15fdfff62bfbfff437f7fff82feffffdd],L0[37],L0[38],L0[39]]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 81
  free := [(16,2),(18,1),(20,0)]
  vectors := [l1v0,l1v1,l1v2].map (vectorData false 45 9)
private def b1 := bands [(0,28,18),(1,29,16),(2,30,14),(3,31,12),(4,32,10),(5,33,8),(6,34,6),(7,35,4),(8,36,2)]
private theorem v1j0 : CJ6.VectorDots 45 9 z1 0 := v! false, 45, b1, l1v0
private theorem v1j1 : CJ6.VectorDots 45 9 z1 1 := v! false, 45, b1, l1v1
private theorem v1j2 : CJ6.VectorDots 45 9 z1 2 := v! false, 45, b1, l1v2
theorem r1 : (CJ0.blockMatrix CJ6.source 45 ((9 : ℤ)-20)).rank ≤ 81 :=
  r! 45, 9, z1, (belowSucc (belowSucc (belowSucc belowZero v1j0) v1j1) v1j2)
private def l2v0 : List Lane := [L0[8],L[7,7,3,31,0x1c0311dca8e329ad00000001],L[6,6,5,31,0x61188ee3c0b711de7e42fa154aca6bd29594e14],L[5,5,7,31,0x148935952884a6b36b3fa0c239394da211b892df760c1ce5a14f9e0],L[4,4,9,31,0x43311dc5479f417edcc5f42a3711dd9a578ef841d8900752d42441800071392ad6c770],L[3,3,11,31,0xd0f594dabd7417dd48b29b26e047780bf3d0d4e9a035d17623fcb3a567aa5e14bfff8babb96bc106f941c],L[2,2,13,31,0x2549aca7db4be8325dc5f431f02fa2f62341a33cb0d85ea19d93eab6a48f85b99e8cc8c6110ab6801cbcc29b8d116137fa7fe],L[1,1,15,31,0x5957d0632dafa0cd1094d6de24fa16f3854e27534a46238a860df5a685466ab44ec2cf36190ed85917a28a9119b638da508e0da36ed95905c701],L[0,0,17,31,0x7623b897fbd05f755ddc49d569acdc09c892ac00bd3c20b1f512ced6a7080e5058d49c63dce4edfc9c565e5604e6167a044b738011614fa4360c7b15ecbb5b69ce1]]
private def l2v1 : List Lane := [L[8,8,1,1,1],L[7,8,2,29,0x29594d662f417d5],L[6,6,5,31,0x29594d65646b298785dc41945e826360bcfac94],L[5,5,7,31,0xf817d05c5e82f8a0ec473f10bd015f127544cae1f2c212bdd567ef],L[4,4,9,31,0x52b29ac91d88ed930fb87af13327ded9a92e675997a927dbfca75abed62a80f3d26627],L[3,3,11,31,0x19d7d05edd88edf140fa04da4cc9c67e76189e5381454fa69ea49ec2b6ad230e5356a2ac4e3d06e9a19f1d],L[2,2,13,31,0x7c0be82d23711cbd0fb869848dc100b5b8b18c0e62b221a44974592978467bbbe7d9b45848a4482170170692d62259a164f3c],L[1,1,15,31,0x46e23b788dc471f0bd053668dc35834bcf1fb02653bb9f1fb4ff7bd8f42ba93c395ac3715dfbc12d8c20b557cb4771005da619fc90d97b30d4a8],L[0,0,17,31,0x266535907623b705569a9003c8b8de5a952e26775c812b4137384d580634e905221401091f339995f1fd2757b8b4e1657c4138c54fd961247234b9fb836f17a366c4]]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 79
  free := [(7,2),(8,0)]
  vectors := [l2v0,l2v1].map (vectorData true 45 10)
private def b2 := bands [(40,45,1),(39,43,3),(38,41,5),(37,39,7),(36,37,9),(35,35,10),(34,34,10),(33,33,9),(32,32,8),(31,31,7),(30,30,6),(29,29,5),(28,28,4),(27,27,3),(26,26,2),(25,25,1)]
private theorem v2j0 : CJ6.VectorDots 45 10 z2 0 := v! true, 45, b2, l2v0
private theorem v2j1 : CJ6.VectorDots 45 10 z2 1 := v! true, 45, b2, l2v1
theorem r2 : (CJ0.blockMatrix CJ6.source 45 ((10 : ℤ)-20)).rank ≤ 79 :=
  r! 45, 10, z2, (belowSucc (belowSucc belowZero v2j0) v2j1)
private def l3v0 : List Lane := [L0[8],L[7,9,1,1,1],L[6,6,5,31,0x4c33335932ccd73f9667e911968cda5002f0830],L[5,5,7,31,0x19666681f2ccd45d4c34432a32e679db32a0ddbe7c4f01be070b17f],L[4,4,9,31,0x4c33340b9866a2a7966ed48000c931200e0aa303f4b8a7af8d832b4314cc829e98e82a],L[3,3,11,31,0x5959667fb732d05e98cb889c5005f32074543fd20242a239333197fa3b43ed0851d2d325700d894b],L[2,2,13,31,0x21600009a1c00160830cd47ddce7efa072213c108d85a72b433270e56d6781042783f9b85bcc586210609341e4937f70],L[1,1,15,31,0x130ccd878cb36a1be5a195fd665d8d0c0dec6304c832dcd47d559c86d14d783d6d87d1ea31955518bb2c7630cb93f03a58fa7636bd91a854c0392],L[0,0,17,31,0x65999d7ccb345dd930f913bccf84c42d1301dcfae5a54243b3d96438800126a503bc6497adc55b2168d75271e7464508e1236b092d42922552a24a450c468cc7071a]]
private def l3v1 : List Lane := [L0[8],L[7,8,1,1,1],L[6,6,5,31,0x32cccccbcb333294659981fa6197383fefd1039],L[5,5,7,31,0x65999980cb332bd32ccbc16cb319d0acb16254994bc8013189442a],L[4,4,9,31,0x32ccccc0659995e665991487f7f38e9fef21142ca6c5b798d3aa3113a99e7d4d826281],L[3,3,11,31,0x1fbffffae619980a4c32fab932c78307fba187e7f2c412d1591cced0cce143b8236a04e6cc192391bc6f60],L[2,2,13,31,0x7effffe0fdfff67bfbfea2db2cabc9919414af8fbef74bfe3c4302b0749a80ca5bca34996bae3cece3c044dc3b146c46bb9ad],L[1,1,15,31,0xcb33327f2ccc9669965e7af985a3ed5fb22b99beb8fa5a42fe8ffb097243c742928d8c658312513dafcdf95c964b586543d70ba7d4998b11b1d9],L[0,0,17,31,0x1966662932ccba48cb3073fb2c882ca327d7dfb93e0e89cfa9198d50762c971e8c3ea2cc068a7294d7b2169a62cb9612241a310324e002dafd851b97eefbdf0e22a2]]
private def l3v2 : List Lane := [L0[8],L[7,7,1,1,1],L[6,6,5,31,0x6e11111210eeeef48777783487778a7aa556cd3],L[5,5,7,31,0x130ccccd2619999dc3bbbc3f10eefb62659a7e1b7095a21c3c5b000],L[4,4,9,31,0x1966666732cccceb30ccd0dc000061254ab1799659fae16cb7b0aaa20ad3540183c9a0],L[3,3,11,31,0x152aaaab1da2222ebb4445fc98668f960002e0880028d924c511de0998f4c8e6f85c016ef71ad373244c22],L[2,2,13,31,0x10000004aa9555ff043bcbc84c345410001015b200bcec3407558e4e986eec85031b822c21ed6d1cdf9aff4d11dd37],L[1,1,15,31,0x659999a196666814c33370ccb3391ad52b163900060ccc65e1478d359ab4c74900bbf0b68a4707ec7f4fe2bf07c409a386d6ab9675cf122f0d0c],L[0,0,17,31,0x21dddde043bbbc4db844599c43bdd0dee13797a76abb181980c51f9a71ab866eb6cb8356757780c5961ca0ee5b9e327b78be71b635c92c14f91cc2cdc8d80459b1cd]]
private def l3v3 : List Lane := [L[8,8,1,1,1],L0[7],L[6,6,5,31,0x4c33333532cccd2f966675d196680cd00022340],L[5,5,7,31,0x19666667f2cccd224c333f8b32ce015b30e3767e62edda3cd3b4ab7],L[4,4,9,31,0x4c33333e9866694d9666cfa80009fb7000b5858337120ca6d49b3b6af998c3aa9647c4],L[3,3,11,31,0x4996667af32ccfb74cb3799c8004f4b20046f26068e04e54ec0233e8500ed0f866bbcb77b8e2fb2],L[2,2,13,31,0x1c0000081800012938cb4f683e5b9763201c87584150ff480d29f8d025509999f5c1e28862f90874492840ba4121bf1],L[1,1,15,31,0x130cccd70cb33628e59a07de65a431bc00c162940ae8c703ae84e66e9f0f80e616ac71916db6d5ec85a574ca0b599224d1986f0aff515477c6c49],L[0,0,17,31,0x659999d1cb33439b30cf3b1ccb6ff46cc79800c699dae86fb7ef482b60b8a9c179ed4c4bcc9cd39347453fc8c090c4f778a7ce87b02e6dad9d894405eee7cdaec154]]
private def z3 : CJ1.Block where
  bank := .leftHigh
  cap := 77
  free := [(7,0),(7,1),(7,2),(8,0)]
  vectors := [l3v0,l3v1,l3v2,l3v3].map (vectorData true 46 9)
private def b3 := bands [(40,45,2),(39,43,4),(38,41,6),(37,39,8),(36,37,9),(35,35,10),(34,34,9),(33,33,8),(32,32,7),(31,31,6),(30,30,5),(29,29,4),(28,28,3),(27,27,2),(26,26,1)]
private theorem v3j0 : CJ6.VectorDots 46 9 z3 0 := v! true, 46, b3, l3v0
private theorem v3j1 : CJ6.VectorDots 46 9 z3 1 := v! true, 46, b3, l3v1
private theorem v3j2 : CJ6.VectorDots 46 9 z3 2 := v! true, 46, b3, l3v2
private theorem v3j3 : CJ6.VectorDots 46 9 z3 3 := v! true, 46, b3, l3v3
theorem r3 : (CJ0.blockMatrix CJ6.source 46 ((9 : ℤ)-20)).rank ≤ 77 :=
  r! 46, 9, z3, (belowSucc (belowSucc (belowSucc (belowSucc belowZero v3j0) v3j1) v3j2) v3j3)
end CJ6_5
end
section
namespace CJ6_5
open CJ6.Fast
open CJ6 (belowZero belowSucc)
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (rfl : good side q l b)
local notation "r!" q "," u "," pkt "," h =>
  Nat.le_trans (CJ6.block_rank_le q u) (CJ6.rank_of_dots (z := pkt) (by decide) h)
local notation "L[" a "," p "," n "," w "," x "]" => (⟨a,p,n,w,x⟩ : Lane)
local notation "L0[" a "]" => (⟨a,0,0,0,0⟩ : Lane)
private def l4v0 : List Lane := [L0[27],L0[28],L0[29],L[30,14,1,1,1],L[31,12,2,31,0x3f7ffffcfefffffb],L[32,10,3,6,117391],L[33,8,4,31,0xfdffff93fbfffe0ff7fffd3feffffed],L[34,6,5,8,0x46d2e1640f],L[35,4,6,31,0x3f7fffe4feffff2ffdfffdabfbfffce7f7fffe2fefffffb],L[36,2,7,8,0x1c7ee1c85a1201],L[37,1,7,31,0x1fbffffe7f7fffebfeffffa7fdffff3bfbffff17f7ffff7feffffff],L[38,0,7,5,0x4cfa3cc1],L0[39],L0[40],L0[41]]
private def l4v1 : List Lane := [L0[27],L0[28],L[29,16,1,1,1],L[30,15,1,31,0x7efffff9],L[31,12,3,31,0x73f7ffffd7effffec],L[32,10,4,31,0xfdffff92000000c4000005400000046],L[33,8,5,31,0x46fdfffeddfbfff72bf7fff1d7effff98],L[34,6,6,31,0x3f7fffe4800000f50000083400001324000011800000054],L[35,4,7,31,0x73f7fff867efffb7efdfff257fbffed6ff7fff4e7effffde],L[36,2,8,31,0xfdfffff20000024c000017a00000578000009d8000008dc000003800000006],L[37,1,8,31,0x3fbffff43f7fff787efffdaefdfffad1fbfff9cbf7fffc57efffff4],L[38,0,7,8,0x72a698c692a07],L0[39],L0[40],L0[41]]
private def l4v2 : List Lane := [L0[27],L[28,18,1,1,1],L[29,17,1,31,0x7efffff9],L[30,15,2,31,0xe7efffff9],L[31,12,4,31,0xfdffff92000000e000000007effffc9],L[32,10,5,31,0x46fdfffeb20000007000000e0000000d2],L[33,8,6,31,0x3f7fffe480000118fdfffeb3fbffe787f7ffd44fefffeb1],L[34,6,7,31,0x73f7fff74800001a40000181000003d40000039c00000118],L[35,4,8,31,0xfdfffff2000002a3f7ffee8fefff1c9fdffd213fbffc027f7ffd98feffff89],L[36,2,9,31,0x1fdffff920000069000005080000136a0000237000001ff000000c800000015],L[37,1,8,31,0x11fbfffd67f7ffe08fefff741fdffec53fbffe867f7fff20feffffd1],L[38,0,7,10,0x1c2a1a48c1a42a01c],L0[39],L0[40],L0[41]]
private def z4 : CJ1.Block where
  bank := .rightHigh
  cap := 75
  free := [(14,3),(16,2),(18,1)]
  vectors := [l4v0,l4v1,l4v2].map (vectorData false 47 8)
private def b4 := bands [(0,31,17),(1,32,15),(2,33,13),(3,34,11),(4,35,9),(5,36,7),(6,37,5),(7,38,3),(8,39,1)]
private theorem v4j0 : CJ6.VectorDots 47 8 z4 0 := v! false, 47, b4, l4v0
private theorem v4j1 : CJ6.VectorDots 47 8 z4 1 := v! false, 47, b4, l4v1
private theorem v4j2 : CJ6.VectorDots 47 8 z4 2 := v! false, 47, b4, l4v2
theorem r4 : (CJ0.blockMatrix CJ6.source 47 ((8 : ℤ)-20)).rank ≤ 75 :=
  r! 47, 8, z4, (belowSucc (belowSucc (belowSucc belowZero v4j0) v4j1) v4j2)
private def l5v0 : List Lane := [L[7,7,2,30,0xe01e1e200000001],L[6,6,4,30,0xe01e1e238078789fe00004bf8000c1],L[5,5,6,31,0x1c03c3c4700f0f11ef0f0f3600000349fc0036280002b50],L[4,4,8,31,0x700f0f10a45a5a6344b4b55f787886d7f000f2efe00c854000858c00049ed8],L[3,3,10,31,0x1c03c3c4611e1e20255a5a8584787c5dc03c801800039ab7f027a5a0016a7c000af9410049285c],L[2,2,12,31,0x700f0f106896969f9e5a5b173cb4c59344b5e32e01f26b9fc0bb6c3f86e71d003738e4017c6b7808ea84d02f03196],L[1,1,14,31,0x1c03c3c4522d2d2f1de1e211a25a5ee87787db8d22d78c7ef12810c002177d1fd141c7807ab75002f8d6f0103608c04e5a7fa15185d70],L[0,0,16,31,0x700f0f102cd2d2db08f0f1bf78788c2ef0f26578479d0e255b5ca677919e7a7f55c3070074eb7c0fb91640589eda81bb1a4487b8eb591ee3ad646f33a368]]
private def z5 : CJ1.Block where
  bank := .leftHigh
  cap := 71
  free := [(7,1)]
  vectors := [l5v0].map (vectorData true 47 9)
private def b5 := bands [(41,46,2),(40,44,4),(39,42,6),(38,40,8),(37,38,9),(36,36,10),(35,35,9),(34,34,8),(33,33,7),(32,32,6),(31,31,5),(30,30,4),(29,29,3),(28,28,2),(27,27,1)]
private theorem v5j0 : CJ6.VectorDots 47 9 z5 0 := v! true, 47, b5, l5v0
theorem r5 : (CJ0.blockMatrix CJ6.source 47 ((9 : ℤ)-20)).rank ≤ 71 :=
  r! 47, 9, z5, (belowSucc belowZero v5j0)
private def l6v0 : List Lane := [L[7,8,1,1,1],L[6,6,4,31,0x2a55554d52aaa798a954d64feff27da],L[5,5,6,31,0x152aaaa5d4aaa915fdffc397fbfa0b57f790953fe999836],L[4,4,8,31,0x7effffe1fbfff63aa553e427efdc1ed7ed6ae7df9a87233dc3795f6dbd0781],L[3,3,10,31,0x2a55554ad4aaa750a954d5c9529e358ff719c1e7e2ea73df44443639abe5398b94ab96d18d0691],L[2,2,12,31,0xd3aaaa7552aa9971fbfd66caa51380c2a086745f794c7f5c6d87645d6e63a6d9b0156216cdb9de39372c37e87fabe],L[1,1,14,31,0x3f7fffeffefffab2a95484a5fbeafd47f670cbcd3362628ec3bb24b45c19565af11d027d87a880db9dc40bebb72c493f6390f07cf61ad],L[0,0,16,31,0x2a55550752aa9146a55159eaa4ecb2ba8d6c1ff4b26b7d247f2c1b4212c9c95a2abbeca8077624ca3a3f1bff025eca60297c032186b4501ce5298fcd4d2d]]
private def l6v1 : List Lane := [L[7,7,1,1,1],L[6,6,4,31,0x2a55555752aaaac8a955598800006f9],L[5,5,6,31,0x152aaaab54aaaab8000001e000002f08000369e80031dac],L[4,4,8,31,0x7f0000020000004ea555608800011587f013eb20012016400d4d720083c220],L[3,3,10,31,0x2a55555654aaaac5a955592752ab09e00006dd800063b7b004a098a02e22f3018929d460009642],L[2,2,12,31,0xd3aaaaaf52aaab31fc0013baa5574882a579c6c002177d1fd922c900fda8e1088e7b54e9708fcc525ef1799b8c7c3],L[1,1,14,31,0x80000028a9555b7c00009e70000bc2554b5a3020085df40055c30502f0ae889668f9dc95f195c0d2ac51126cffe0a713da5a6],L[0,0,16,31,0x2a55555952aaab6ea5557342a558673a9590c2352e31ec2a812aca01c965708ef7fa9bceb196cdfbc12dc979b163320ebaad038497775fd98fb51db3710f]]
private def z6 : CJ1.Block where
  bank := .leftHigh
  cap := 70
  free := [(7,0),(7,1)]
  vectors := [l6v0,l6v1].map (vectorData true 48 8)
private def b6 := bands [(42,48,1),(41,46,3),(40,44,5),(39,42,7),(38,40,8),(37,38,9),(36,36,9),(35,35,8),(34,34,7),(33,33,6),(32,32,5),(31,31,4),(30,30,3),(29,29,2),(28,28,1)]
private theorem v6j0 : CJ6.VectorDots 48 8 z6 0 := v! true, 48, b6, l6v0
private theorem v6j1 : CJ6.VectorDots 48 8 z6 1 := v! true, 48, b6, l6v1
theorem r6 : (CJ0.blockMatrix CJ6.source 48 ((8 : ℤ)-20)).rank ≤ 70 :=
  r! 48, 8, z6, (belowSucc (belowSucc belowZero v6j0) v6j1)
end CJ6_5
end
section
namespace CJ6_5
theorem proof : CJ6.c5 := ⟨r1, r2, r3, r4, r5, r6, trivial⟩
end CJ6_5
end
