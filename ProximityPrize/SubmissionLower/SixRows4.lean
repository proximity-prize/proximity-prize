import ProximityPrize.SubmissionLower.SixRows5
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_4
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l1v0 : List Lane := [⟨23,0,0,0,0⟩,⟨24,18,1,1,1⟩,⟨25,16,2,31,0x3f7ffffbfefffff9⟩,⟨26,14,3,7,746524⟩,⟨27,12,4,31,0xfdffff13fbfffb87f7fff90feffffc9⟩,⟨28,10,5,10,0xd2a831062046⟩,⟨29,8,6,31,0x3f7fff82fefffc11fdfff3c3fbffeda7f7fff2efeffffc9⟩,⟨30,6,7,11,0x349f87a8f510688c01c⟩,⟨31,4,8,31,0xfdffff13fbfff587f7ffcf0fefff859fdfff513fbfff747f7fffc8fefffff9⟩,⟨32,2,9,11,0x2d240c424c41a4602a00c001⟩,⟨33,1,9,31,0x7efffff7fdffff73fbfffc87f7fff3cfefffe5dfdfffdd3fbfffe47f7ffff4feffffff⟩,⟨34,0,9,7,0x11071c467070401⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩]
private def l1v1 : List Lane := [⟨23,20,1,1,1⟩,⟨24,19,1,31,0x7efffff7⟩,⟨25,16,3,31,0xb7f7ffffc7effffdd⟩,⟨26,14,4,31,0xfdffff120000014400000b4000000a8⟩,⟨27,12,5,31,0xd2fdfffd7bfbffe747f7ffd36fefffe87⟩,⟨28,10,6,31,0x3f7fff82800002f400001f80000052b0000056a000001f8⟩,⟨29,8,7,31,0x34bf7ffdc9feffe669fdffa8bbfbff782ff7ff9d9fefffe5d⟩,⟨30,6,8,31,0xfdffff12000011b80000dc80000396c0000762000007ff80000444000000d8⟩,⟨31,4,9,31,0x2dfdfffa1bfbffb147f7fe7e2feffc27bfdffa76bfbffb927f7ffe3efeffffc2⟩,⟨32,2,10,31,0x3f7ffffb800001440000120000006510000133200002274000024c0000015f0000006300000008⟩,⟨33,1,10,31,0xfeffffb0fdfffb3bfbffe1d7f7ff95bfefff1bbfdffecfbfbfff0d7f7fff997efffff0⟩,⟨34,0,9,10,0x9120fc7e2767e0fc12009⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 88
  free := [(18,1),(20,0)]
  vectors := [l1v0,l1v1].map (vectorData false 43 10)
private def b1 := bands [(0,25,19),(1,26,17),(2,27,15),(3,28,13),(4,29,11),(5,30,9),(6,31,7),(7,32,5),(8,33,3),(9,34,1)]
private theorem k1v0 : good false 43 l1v0 b1 := rfl
private theorem v1j0 : CJ6.VectorDots 43 10 z1 0 := v! false, 43, b1, l1v0, k1v0
private theorem k1v1 : good false 43 l1v1 b1 := rfl
private theorem v1j1 : CJ6.VectorDots 43 10 z1 1 := v! false, 43, b1, l1v1, k1v1
theorem r1 : (CJ0.blockMatrix CJ6.source 43 ((10 : ℤ)-20)).rank ≤ 88 :=
  (CJ6.block_rank_le 43 10).trans (CJ6.rank_of_dots (z := z1) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v1j0) v1j1))
private def l2v0 : List Lane := [⟨8,0,0,0,0⟩,⟨7,8,3,31,0xfdd49a3e2d6327600000001⟩,⟨6,6,6,31,0x3873629671dcb08ea59f68b7fbffff1ff7ffecae5998608⟩,⟨5,5,8,31,0x2aa9b7ad6a192c41fc56cb1dff3031cfdfff333fbff4904cb2ad4e996142ed⟩,⟨4,4,10,31,0x155fb547d49e9c9dc690ffcc9dfe7edb68b231db2cc73fafdfc19c2657496359538c6d65143114⟩,⟨3,3,12,31,0x644ce2acd86c357c4854481b3974faa5375e17fe8e41dabf7e527cfef04b81cab4a6a12d5433ff175f8bc77afb471⟩,⟨2,2,14,31,0x15c4f815d3f10581477b4c62bd4c87df8ee455d2cd5a9c9dbe22a79fb99eac7f4ca390fd971a51c278a1d96671bfb30d084a0be97d8d1⟩,⟨1,1,16,31,0x2dd3ce1c1457b4b2a1cac9c83d06b15f77ff8f2b86a6613e7e9551faf1c78bfcbb776bf3088086f4d6f4e6b98a6916af84a904fa080c53b417a178158324⟩,⟨0,0,18,31,0x39a32b001d7f2c8ccc7fe8732835d60db55b022d8247004e8989df5a0f8ac684216054fb80b821e7ebe823e58c39ba531deff341b77a5294f5dc781e05058ea13444d78fcd2e⟩]
private def l2v1 : List Lane := [⟨8,0,0,0,0⟩,⟨7,7,4,31,0x3dbdc01b287e51e8000000000000001⟩,⟨6,6,6,31,0x335f0a6c820682a6c9588a111dc000217d00025626ccf03⟩,⟨5,5,8,31,0xb13b3cc686d7230a8ebc32e6f58f5a97f000166cb3346bdfc00e0ccc33bb3d⟩,⟨4,4,10,31,0x39bebe56262e65094e7a5ad02187ad4711ad3bfcc333c681966cce6986a2afc65b80fd2626f9d4⟩,⟨3,3,12,31,0x70bb5f662dc556dde4d50084fea54b0474b66df544999ec0002b76800194ae4c3fdeed312551b72eec95780b8c4e8⟩,⟨2,2,14,31,0x131f1bbccc7f9909c55e815f54357891a69a9a1315624b7dc1259b6fe0a2fcafa51b735f63c20ed8c3031c1e1e34f11509fc1a60b8569⟩,⟨1,1,16,31,0x7a3e27fd9968b4eb11e370c0fa53c326748e892836c9040c06b61b21694a28bea0167efee264de99e7949ce1a8404951d8cbf27cdcbd9a51c063a5ab26a2⟩,⟨0,0,18,31,0x3e8022a155021086f60b072ff539ebe6b55841799bd6bd6a4649b1d8e0a115ca2d53060057f1c7a743c16f892359169e8981af6cc0240069318db814ff42162d24f7e3e23262⟩]
private def l2v2 : List Lane := [⟨8,9,1,1,1⟩,⟨7,9,2,31,0x27b00000bf800006⟩,⟨6,6,6,31,0x1bc80003575000b32fa016fade420a627b24024cf80a2d2⟩,⟨5,5,8,31,0x6f2000223f800862ba8111a000178527f187c6c0148668e0a5c2a808910a7a⟩,⟨4,4,10,31,0x27b000112fa00448ce608c7f5d4c035c00c534280a19b8f85deabe93d97f8b400e49701fdb3d46⟩,⟨3,3,12,31,0x7000001d4c0003cedbf853ff7aef65c48046948282fb25b19b5aff8a59dea41be7c4d0b035eda4e47f19624⟩,⟨2,2,14,31,0x23b8002ac7700b4cce617ed69ee177aabcac76e199a23a79270855fb0dcd59e926136d0d634042a33bfa3ebb6a82eef215d2985e45e2b⟩,⟨1,1,16,31,0x4f6000ef3d80410fb888cb85f4c8787cf339d31c788924537afb9bc65a286a76ead408877fd11b150833615b188296484f9ec13b34f177e8d00a3b1ee038⟩,⟨0,0,18,31,0xfe0004fdf40164a2fa315202007b9f200d237c841711d33d7c296010cb265db49df94142e451dd45692dd09def25b1f58352bf151afea7507e05ab04ee4ef0d4c6b97c76ebb⟩]
private def l2v3 : List Lane := [⟨8,8,1,1,1⟩,⟨7,9,2,31,0x1e7daec9cbc316f4⟩,⟨6,6,6,31,0x1065218be4734f6d2ddf8e30de3fedd27afec5ce8c54e8f⟩,⟨5,5,8,31,0x54d9611af22d05074da50a270fc6b637eff2f5dfbf52fd13054ecde552b30e⟩,⟨4,4,10,31,0x2cf152fac58584461832141152bcf4bf1ec2d07cc2df21e7ec73238965bd460555be6dd1d74fd1⟩,⟨3,3,12,31,0x6058469dc772c1478ee564be6098a3f4ac40cbd5ab30a77f678aca7e208febaae9208e9ba0d463a15db459d0cb00d⟩,⟨2,2,14,31,0x1624944cb50b5d36f168c792129b9db32388aad34a8a71b46536c7ef852ae5cd11066b8c4e12b37a64caa757f5f82a9b58a3a814a8196⟩,⟨1,1,16,31,0x9c736bac02308b2f0251d11e3a0b478b412a7ece2efa9d5afe77aed39c9d4c2dbde3a481f3b2d8c7a5782f61d22fe5b2e9fde7c6bc00945e271c5086b2d7⟩,⟨0,0,18,31,0xb7ee58245d998e69a7ad3a83f45add94cace429e86b099a6d675986a421d09d81d0f54e95beee8dcb462373859c6e0d656774a7d395075b6ac5a95029bdae0f1306ac53b903⟩]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 86
  free := [(7,2),(7,3),(8,0),(8,1)]
  vectors := [l2v0,l2v1,l2v2,l2v3].map (vectorData true 43 11)
private def b2 := bands [(38,42,2),(37,40,4),(36,38,6),(35,36,8),(34,34,10),(33,33,10),(32,32,10),(31,31,9),(30,30,8),(29,29,7),(28,28,6),(27,27,5),(26,26,4),(25,25,3),(24,24,2),(23,23,1)]
private theorem k2v0 : good true 43 l2v0 b2 := rfl
private theorem v2j0 : CJ6.VectorDots 43 11 z2 0 := v! true, 43, b2, l2v0, k2v0
private theorem k2v1 : good true 43 l2v1 b2 := rfl
private theorem v2j1 : CJ6.VectorDots 43 11 z2 1 := v! true, 43, b2, l2v1, k2v1
private theorem k2v2 : good true 43 l2v2 b2 := rfl
private theorem v2j2 : CJ6.VectorDots 43 11 z2 2 := v! true, 43, b2, l2v2, k2v2
private theorem k2v3 : good true 43 l2v3 b2 := rfl
private theorem v2j3 : CJ6.VectorDots 43 11 z2 3 := v! true, 43, b2, l2v3, k2v3
theorem r2 : (CJ0.blockMatrix CJ6.source 43 ((11 : ℤ)-20)).rank ≤ 86 :=
  (CJ6.block_rank_le 43 11).trans (CJ6.rank_of_dots (z := z2) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v2j0) v2j1) v2j2) v2j3))
end CJ6_4
end
section
namespace CJ6_4
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l3v0 : List Lane := [⟨24,0,0,0,0⟩,⟨25,0,0,0,0⟩,⟨26,0,0,0,0⟩,⟨27,14,2,31,0xff000000⟩,⟨28,12,3,31,0x1fbffffe0000000100000006⟩,⟨29,10,4,31,0x4800000053f7ffff37efffff2⟩,⟨30,8,5,31,0x7effffadfdffff2200000054000002300000014⟩,⟨31,6,6,31,0x3f0000010a000000d3fbfffe63f7fffd67efffff2⟩,⟨32,4,7,31,0x1fbfffe0ff7fff4afefffec600000000000001f4000001b00000006⟩,⟨33,2,8,31,0xa8000004d000000c7800000affdffff9ffbfffefff7ffff87f000000⟩,⟨34,1,8,31,0xfdffffbbfbfffd87f7fff787effff2ffdffff9e00000060000000780000002⟩,⟨35,0,8,31,0x12000000bc0000031800000690000006e00000027f7fffff7f000000⟩,⟨36,0,7,31,0x1fc000003f7ffffdfefffff2fdffffdbfbffffcbf7ffffdff000000⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def l3v1 : List Lane := [⟨24,0,0,0,0⟩,⟨25,0,0,0,0⟩,⟨26,16,1,1,1⟩,⟨27,14,1,31,0x7efffff1⟩,⟨28,12,3,31,0x1fbffff5000000250000004b⟩,⟨29,10,4,31,0x1e1fbffffc7f7fff3dfeffff57⟩,⟨30,8,5,31,0x7efffd8bfdfffb32000009d800001a4000000d7⟩,⟨31,6,6,31,0x1f800000770000001a5fbffe90ff7ffe2afeffff65⟩,⟨32,4,7,31,0x1fbffef9ff7ffa5efefff7cd000005780000170c000011d0000003d⟩,⟨33,2,8,31,0x5a00000284000006270000041afdfff9c3fbfff4c7f7fffa9fefffff7⟩,⟨34,1,8,31,0xfdfffd8dfbffea67f7ffb7dfefff971fdfffddc000004b0000004e00000014⟩,⟨35,0,8,31,0xa00000068000001b30000038e00000398000000f3f7fffeffefffff7⟩,⟨36,0,7,31,0x1fbffffe3f7fffe5feffff7afdfffe9bfbfffdebf7fffe5fefffff8⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def l3v2 : List Lane := [⟨24,0,0,0,0⟩,⟨25,0,0,0,0⟩,⟨26,17,1,1,1⟩,⟨27,14,3,31,0x1fbffffe000000007efffff9⟩,⟨28,12,4,31,0x49fbffffe4000001600000030⟩,⟨29,10,5,31,0x7effffad00000081fbffff77f7fff78feffff89⟩,⟨30,8,6,31,0x3f7effff21fdfffd9a000007e0000013b000000a0⟩,⟨31,6,7,31,0x1fbfffe0c00000e00000047c00000001fbffed6ff7ffe90feffff89⟩,⟨32,4,8,31,0xa9fbfff747f7ffc3afefffa89000005780000132000000e600000030⟩,⟨33,2,9,31,0x7effffdd0000038000001d500000498000002bcfdfffa43fbfff677f7fffb8fefffff9⟩,⟨34,1,9,31,0x9fdfffe43fbffef17f7ffc64fefffacffdfffea200000450000004400000011⟩,⟨35,0,9,31,0x7f000000000000800000057000001700000030200000300000000b3f7ffff0fefffff8⟩,⟨36,0,7,31,0x1fbffffe7f7fffe8feffff89fdfffec3fbfffe27f7fffe8fefffff9⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def l3v3 : List Lane := [⟨24,0,0,0,0⟩,⟨25,18,1,1,1⟩,⟨26,0,0,0,0⟩,⟨27,14,3,31,0x1fbffff5000000007effff95⟩,⟨28,12,4,31,0x1e1fbfffec4000014c00000250⟩,⟨29,10,5,31,0x7efffd8b00000501fbffee27f7ff928fefffa7f⟩,⟨30,8,6,31,0x1f87efff741fdfff432000073800000ec400000720⟩,⟨31,6,7,31,0x1fbffef9c00008c000002530fdffe163fbff14dff7fef70fefffac5⟩,⟨32,4,8,31,0x5a1fbffa887f7fdd54feffd8a1000057800000e2400000a1400000210⟩,⟨33,2,9,31,0x7efffec600002300000118e0000295800000f0afdffb503fbff9347f7ffce8feffffaa⟩,⟨34,1,9,31,0x50fdffee83fbff5a27f7fdd70feffd0f9fdfffb02000033e000002f0000000b8⟩,⟨35,0,9,31,0x7efffff800000500000035f00000e2800001d4200001c40000004b3f7fff48feffffa0⟩,⟨36,0,7,31,0x1fbfffec7f7fff10fefffb51fdfff383fbffed47f7fff10feffffb1⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def l3v4 : List Lane := [⟨24,0,0,0,0⟩,⟨25,19,1,1,1⟩,⟨26,18,1,31,0x7efffff8⟩,⟨27,14,4,31,0x49fbffffe000000007effffdd⟩,⟨28,12,5,31,0x7effffad00000090000000000000078000000d8⟩,⟨29,10,6,31,0x3f7effff0500000049fbfff797f7ffd5dfefffde5⟩,⟨30,8,7,31,0x1fbfffe0c00000fc7effff05000000000000313800005e8000002d0⟩,⟨31,6,8,31,0xa9fbfff62c000017a00000984fdffec53fbff9b9ff7ff934fefffde5⟩,⟨32,4,9,31,0x7effffdd000003f1fbffec57f7ff52cfefff62900002b50000061e00000438000000d8⟩,⟨33,2,10,31,0x4feffff05000009d8000062700000e85000001f8fdffdc4bfbffd037f7ffeaf7effffdd⟩,⟨34,1,10,31,0x3f80000000000048fdfffa1bfbffc047f7ff277feffee4900000108000018c0000015180000050⟩,⟨35,0,9,31,0x7efffff8000001f80000168000005fa00000c4e00000b8800000123f7fffa6feffffd4⟩,⟨36,0,7,31,0x1fbffff77f7fff94fefffde5fdfffa63fbfff797f7fff94feffffdd⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def l3v5 : List Lane := [⟨24,20,1,1,1⟩,⟨25,0,0,0,0⟩,⟨26,18,1,31,0x7effffd4⟩,⟨27,14,4,31,0x1e1fbfffe9c00000007efffe21⟩,⟨28,12,5,31,0x7efffd8b000005a1fbffff74000067800000ac2⟩,⟨29,10,6,31,0x1f87efff62900000511fbff7fc7f7fddd4feffe5d9⟩,⟨30,8,7,31,0x1fbffef9c00009d87efff239000020d00002977800049d400002238⟩,⟨31,6,8,31,0x5a1fbff9d9400012b4000056a0fdfec503fbfb0057f7fad08feffe6b1⟩,⟨32,4,9,31,0x7efffec600002761fbff13c7f7f8eccfeffc27b00024ea00004b69000032a000000a05⟩,⟨33,2,10,31,0x287efff62900007230000429c000092ac7effec51fdfe3773fbfdc007f7ff064fefffe59⟩,⟨34,1,10,31,0x3f7ffffc000002d0fdffbd13fbfd4567f7f6f0dfeff4cd900002a30000130e00000f97800003a8⟩,⟨35,0,9,31,0x7effffa7000015f00000f7800004140000084e4000078f000000483f7ffbc8fefffdf7⟩,⟨36,0,7,31,0x1fbfff9d7f7ffb5cfeffe8cdfdffc223fbffa337f7ffb5cfefffe75⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩]
private def z3 : CJ1.Block where
  bank := .rightHigh
  cap := 84
  free := [(15,2),(16,2),(17,1),(18,1),(19,0),(20,0)]
  vectors := [l3v0,l3v1,l3v2,l3v3,l3v4,l3v5].map (vectorData false 44 10)
private def b3 := bands [(0,27,18),(1,28,16),(2,29,14),(3,30,12),(4,31,10),(5,32,8),(6,33,6),(7,34,4),(8,35,2)]
private theorem k3v0 : good false 44 l3v0 b3 := rfl
private theorem v3j0 : CJ6.VectorDots 44 10 z3 0 := v! false, 44, b3, l3v0, k3v0
private theorem k3v1 : good false 44 l3v1 b3 := rfl
private theorem v3j1 : CJ6.VectorDots 44 10 z3 1 := v! false, 44, b3, l3v1, k3v1
private theorem k3v2 : good false 44 l3v2 b3 := rfl
private theorem v3j2 : CJ6.VectorDots 44 10 z3 2 := v! false, 44, b3, l3v2, k3v2
private theorem k3v3 : good false 44 l3v3 b3 := rfl
private theorem v3j3 : CJ6.VectorDots 44 10 z3 3 := v! false, 44, b3, l3v3, k3v3
private theorem k3v4 : good false 44 l3v4 b3 := rfl
private theorem v3j4 : CJ6.VectorDots 44 10 z3 4 := v! false, 44, b3, l3v4, k3v4
private theorem k3v5 : good false 44 l3v5 b3 := rfl
private theorem v3j5 : CJ6.VectorDots 44 10 z3 5 := v! false, 44, b3, l3v5, k3v5
theorem r3 : (CJ0.blockMatrix CJ6.source 44 ((10 : ℤ)-20)).rank ≤ 84 :=
  (CJ6.block_rank_le 44 10).trans (CJ6.rank_of_dots (z := z3) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v3j0) v3j1) v3j2) v3j3) v3j4) v3j5))
private def l4v0 : List Lane := [⟨8,8,1,1,1⟩,⟨7,7,3,9,279024⟩,⟨6,6,5,16,0x10021021015509fd8⟩,⟨5,5,7,21,0x4000440023100bb002d4a087de148588⟩,⟨4,4,9,25,0x1000011800094c00332200cc88027a0c06311e0cd37516720cc⟩,⟨3,3,11,28,0x1000002400002760001be4000e619005c0a001db89007f60201cdbc7459c8330f269568⟩,⟨2,2,13,31,0x10000004a00000a680000f2d000101fd000d4d72008de4c004e8c58024d1c940ed47f48530c626197b128c6e6aa5b4⟩,⟨1,1,15,31,0x40000013000002bf000041e80004815c003d45b002a1fe9018123c00ba8d5104dbae1c1c2d583c8f727b6089832b2e260cacb4459afb0⟩,⟨0,0,17,31,0x10000004e00000b9400011d98001414b0011921a00c7227c07558e483aac724194322f89792d1d31f34af66a1a087bce44c0c2286d15172c16464d8c42d2d⟩]
private def z4 : CJ1.Block where
  bank := .leftHigh
  cap := 80
  free := [(8,0)]
  vectors := [l4v0].map (vectorData true 44 11)
private def b4 := bands [(39,43,2),(38,41,4),(37,39,6),(36,37,8),(35,35,10),(34,34,10),(33,33,10),(32,32,9),(31,31,8),(30,30,7),(29,29,6),(28,28,5),(27,27,4),(26,26,3),(25,25,2),(24,24,1)]
private theorem k4v0 : good true 44 l4v0 b4 := rfl
private theorem v4j0 : CJ6.VectorDots 44 11 z4 0 := v! true, 44, b4, l4v0, k4v0
theorem r4 : (CJ0.blockMatrix CJ6.source 44 ((11 : ℤ)-20)).rank ≤ 80 :=
  (CJ6.block_rank_le 44 11).trans (CJ6.rank_of_dots (z := z4) (by decide) (CJ6.belowSucc CJ6.belowZero v4j0))
end CJ6_4
end
section
namespace CJ6_4
theorem proof : CJ6.c4 := ⟨r1, r2, r3, r4, trivial⟩
end CJ6_4
end
