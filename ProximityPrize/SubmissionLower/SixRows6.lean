import ProximityPrize.SubmissionLower.GoldBranch7N2
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_6
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l1v0 : List Lane := [⟨29,0,0,0,0⟩,⟨30,0,0,0,0⟩,⟨31,0,0,0,0⟩,⟨32,0,0,0,0⟩,⟨33,12,1,1,1⟩,⟨34,10,2,31,0x3f7ffffd7efffffc⟩,⟨35,8,3,5,22474⟩,⟨36,6,4,31,0xfdffffbdfbfffedbf7fffe7fefffff7⟩,⟨37,4,5,7,0x23c991405⟩,⟨38,2,6,31,0x3f7ffff67effffb6fdffff3bfbffff17f7ffff97f000000⟩,⟨39,1,6,6,0x1deca83c2⟩,⟨40,0,6,31,0x3f8000007efffffcfdffffeffbffffdff7ffffe7f000000⟩,⟨41,0,0,0,0⟩,⟨42,0,0,0,0⟩]
private def l1v1 : List Lane := [⟨29,0,0,0,0⟩,⟨30,0,0,0,0⟩,⟨31,0,0,0,0⟩,⟨32,14,1,1,1⟩,⟨33,13,1,31,0x7efffffa⟩,⟨34,10,3,31,0x57f7ffffdfefffff2⟩,⟨35,8,4,31,0xfdffffbc00000090000003480000028⟩,⟨36,6,5,31,0x23fdffff4ffbfffb57f7fff92feffffd4⟩,⟨37,4,6,31,0x3f7ffff6000000780000038400000780000006180000018⟩,⟨38,2,7,31,0x1ff7fffd3fefffe8afdfffbf3fbfffb1bf7fffd9fefffffc⟩,⟨39,1,7,31,0x1fc0000000000012000000a50000023000000384000002a0000000b⟩,⟨40,0,6,31,0x3f7ffffdfeffffe3fdffff8bfbffff17f7ffff1fefffffb⟩,⟨41,0,0,0,0⟩,⟨42,0,0,0,0⟩]
private def l1v2 : List Lane := [⟨29,0,0,0,0⟩,⟨30,0,0,0,0⟩,⟨31,16,1,1,1⟩,⟨32,15,1,31,0x7efffffa⟩,⟨33,13,2,31,0xafefffffa⟩,⟨34,10,4,31,0xfdffffbc000000a800000007effffde⟩,⟨35,8,5,31,0x23fdffff3000000054000007a80000069⟩,⟨36,6,6,31,0x3f7ffff60000008cfdffff31fbfff48bf7ffed77effff83⟩,⟨37,4,7,31,0x1ff7fffcc000000d20000094c00001554000011b80000046⟩,⟨38,2,8,31,0xfe000000000000abf7fff97fefffbc4fdfff3b5fbfff0eff7fff89fefffff2⟩,⟨39,1,7,31,0x1fbffffe800000348000020d0000071c00000b7c000008880000023⟩,⟨40,0,6,31,0x3f7ffff67effff98fdfffe5ffbfffcbff7fffcc7effffec⟩,⟨41,0,0,0,0⟩,⟨42,0,0,0,0⟩]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 68
  free := [(12,3),(14,3),(16,2)]
  vectors := [l1v0,l1v1,l1v2].map (vectorData false 49 7)
private def b1 := bands [(0,34,16),(1,35,14),(2,36,12),(3,37,10),(4,38,8),(5,39,6),(6,40,4),(7,41,2)]
private theorem k1v0 : good false 49 l1v0 b1 := rfl
private theorem v1j0 : CJ6.VectorDots 49 7 z1 0 := v! false, 49, b1, l1v0, k1v0
private theorem k1v1 : good false 49 l1v1 b1 := rfl
private theorem v1j1 : CJ6.VectorDots 49 7 z1 1 := v! false, 49, b1, l1v1, k1v1
private theorem k1v2 : good false 49 l1v2 b1 := rfl
private theorem v1j2 : CJ6.VectorDots 49 7 z1 2 := v! false, 49, b1, l1v2, k1v2
theorem r1 : (CJ0.blockMatrix CJ6.source 49 ((7 : ℤ)-20)).rank ≤ 68 :=
  (CJ6.block_rank_le 49 7).trans (CJ6.rank_of_dots (z := z1) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v1j0) v1j1) v1j2))
private def l2v0 : List Lane := [⟨7,7,1,1,1⟩,⟨6,6,3,10,1087130⟩,⟨5,5,5,17,0x1001300afc41e92057⟩,⟨4,4,7,22,0x100009c002e5008ecc1414b2324371c89f⟩,⟨3,3,9,27,0x100000500000c3000134c00164fe01414b00ea46b08e3d3449578ed⟩,⟨2,2,11,31,0x40000014800003340000534800062e58005b7ab00449c0402ae182816c7cd54a70e8c6c2d29e90⟩,⟨1,1,13,31,0x10000005400000d74000166c0001b53a0019f5d801402d680cdd40c0708ff69352789c55ed1c074092176f181d7913⟩,⟨0,0,15,31,0x40000015800003870000606a000788480075813005d064603d766e422929e050ce6225f24834ffb1b13df665069fc4a93348be3c005c4⟩]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 63
  free := [(7,0)]
  vectors := [l2v0].map (vectorData true 50 7)
private def b2 := bands [(43,49,2),(42,47,4),(41,45,6),(40,43,7),(39,41,8),(38,39,8),(37,37,8),(36,36,7),(35,35,6),(34,34,5),(33,33,4),(32,32,3),(31,31,2),(30,30,1)]
private theorem k2v0 : good true 50 l2v0 b2 := rfl
private theorem v2j0 : CJ6.VectorDots 50 7 z2 0 := v! true, 50, b2, l2v0, k2v0
theorem r2 : (CJ0.blockMatrix CJ6.source 50 ((7 : ℤ)-20)).rank ≤ 63 :=
  (CJ6.block_rank_le 50 7).trans (CJ6.rank_of_dots (z := z2) (by decide) (CJ6.belowSucc CJ6.belowZero v2j0))
private def l3v0 : List Lane := [⟨31,0,0,0,0⟩,⟨32,0,0,0,0⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,10,1,1,1⟩,⟨37,8,2,31,0x3f7ffffdfefffffd⟩,⟨38,6,3,5,16006⟩,⟨39,4,4,31,0xfdffffdbfbffff67f7ffff4fefffffd⟩,⟨40,2,5,6,0xfa24301⟩,⟨41,1,5,31,0x7efffffbfdffffdbfbffffa7f7ffffafeffffff⟩,⟨42,0,5,3,6561⟩,⟨43,0,0,0,0⟩,⟨44,0,0,0,0⟩]
private def l3v1 : List Lane := [⟨31,0,0,0,0⟩,⟨32,0,0,0,0⟩,⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,12,1,1,1⟩,⟨36,11,1,31,0x7efffffb⟩,⟨37,8,3,31,0x3ff7ffffe7efffff7⟩,⟨38,6,4,31,0xfdffffda00000064000001e00000014⟩,⟨39,4,5,31,0xffdffff9ffbfffdd7f7fffd3fefffff2⟩,⟨40,2,6,31,0x3f7ffffd800000320000014000000258000001900000004⟩,⟨41,1,6,31,0xfeffffe8fdffff4ffbfffe4ff7fffe57efffff8⟩,⟨42,0,5,5,5929605⟩,⟨43,0,0,0,0⟩,⟨44,0,0,0,0⟩]
private def l3v2 : List Lane := [⟨31,0,0,0,0⟩,⟨32,0,0,0,0⟩,⟨33,0,0,0,0⟩,⟨34,14,1,1,1⟩,⟨35,13,1,31,0x7efffffb⟩,⟨36,11,2,31,0x7fefffffb⟩,⟨37,8,4,31,0xfdffffda0000007800000007effffed⟩,⟨38,6,5,31,0xffdffff8a0000003c000003c0000002d⟩,⟨39,4,6,31,0x3f7ffffd8000003cfdffff8bfbfffb57f7fff97feffffdd⟩,⟨40,2,7,31,0x7f7ffff18000005a000002f8000005dc000003f0000000a⟩,⟨41,1,6,31,0x37effffc5fdfffe23fbfffb57f7fffb5feffffe9⟩,⟨42,0,5,7,0xf7969e0f⟩,⟨43,0,0,0,0⟩,⟨44,0,0,0,0⟩]
private def z3 : CJ1.Block where
  bank := .rightHigh
  cap := 61
  free := [(10,3),(12,3),(14,3)]
  vectors := [l3v0,l3v1,l3v2].map (vectorData false 51 6)
private def b3 := bands [(0,37,15),(1,38,13),(2,39,11),(3,40,9),(4,41,7),(5,42,5),(6,43,3),(7,44,1)]
private theorem k3v0 : good false 51 l3v0 b3 := rfl
private theorem v3j0 : CJ6.VectorDots 51 6 z3 0 := v! false, 51, b3, l3v0, k3v0
private theorem k3v1 : good false 51 l3v1 b3 := rfl
private theorem v3j1 : CJ6.VectorDots 51 6 z3 1 := v! false, 51, b3, l3v1, k3v1
private theorem k3v2 : good false 51 l3v2 b3 := rfl
private theorem v3j2 : CJ6.VectorDots 51 6 z3 2 := v! false, 51, b3, l3v2, k3v2
theorem r3 : (CJ0.blockMatrix CJ6.source 51 ((6 : ℤ)-20)).rank ≤ 61 :=
  (CJ6.block_rank_le 51 6).trans (CJ6.rank_of_dots (z := z3) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v3j0) v3j1) v3j2))
private def l4v0 : List Lane := [⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,8,1,1,1⟩,⟨40,6,2,31,0x3f7ffffe7efffffe⟩,⟨41,4,3,4,2755⟩,⟨42,2,4,31,0xfdffffeffbffffbff7ffffc7f000000⟩,⟨43,1,4,4,23698⟩,⟨44,0,4,31,0xfe000001fbfffffbf7fffff7f000000⟩,⟨45,0,0,0,0⟩]
private def l4v1 : List Lane := [⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,10,1,1,1⟩,⟨39,9,1,31,0x7efffffc⟩,⟨40,6,3,31,0x2bf7ffffefefffffb⟩,⟨41,4,4,31,0xfdffffee00000040000000f00000008⟩,⟨42,2,5,31,0x5fdffffd3fbffff2ff7ffff2fefffffe⟩,⟨43,1,5,31,0x7f00000000000020000000a8000001000000007⟩,⟨44,0,4,31,0xfdfffffbfbffffd7f7ffffafefffffd⟩,⟨45,0,0,0,0⟩]
private def l4v2 : List Lane := [⟨33,0,0,0,0⟩,⟨34,0,0,0,0⟩,⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,12,1,1,1⟩,⟨38,11,1,31,0x7efffffc⟩,⟨39,9,2,31,0x57efffffc⟩,⟨40,6,4,31,0xfdffffee0000005000000007efffff7⟩,⟨41,4,5,31,0x5fdffffc60000002800000190000000f⟩,⟨42,2,6,31,0x3f80000000000014fdffffc7fbfffe77f7fffe57efffffb⟩,⟨43,1,5,31,0x7efffffc0000003c0000016800000230000000f⟩,⟨44,0,4,31,0xfdffffeffbffff8ff7ffff1fefffff7⟩,⟨45,0,0,0,0⟩]
private def z4 : CJ1.Block where
  bank := .rightHigh
  cap := 53
  free := [(8,2),(10,2),(12,2)]
  vectors := [l4v0,l4v1,l4v2].map (vectorData false 53 5)
private def b4 := bands [(0,40,14),(1,41,12),(2,42,10),(3,43,8),(4,44,6),(5,45,4),(6,46,2)]
private theorem k4v0 : good false 53 l4v0 b4 := rfl
private theorem v4j0 : CJ6.VectorDots 53 5 z4 0 := v! false, 53, b4, l4v0, k4v0
private theorem k4v1 : good false 53 l4v1 b4 := rfl
private theorem v4j1 : CJ6.VectorDots 53 5 z4 1 := v! false, 53, b4, l4v1, k4v1
private theorem k4v2 : good false 53 l4v2 b4 := rfl
private theorem v4j2 : CJ6.VectorDots 53 5 z4 2 := v! false, 53, b4, l4v2, k4v2
theorem r4 : (CJ0.blockMatrix CJ6.source 53 ((5 : ℤ)-20)).rank ≤ 53 :=
  (CJ6.block_rank_le 53 5).trans (CJ6.rank_of_dots (z := z4) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v4j0) v4j1) v4j2))
private def l5v0 : List Lane := [⟨6,6,1,1,1⟩,⟨5,5,1,31,0x7effffdf⟩,⟨4,4,1,10,595⟩,⟨3,3,1,31,0x7effe41d⟩,⟨2,2,1,17,66045⟩,⟨1,1,1,31,0x7ef8574b⟩,⟨0,0,1,22,3262623⟩]
private def z5 : CJ1.Block where
  bank := .leftHigh
  cap := 48
  free := [(6,0)]
  vectors := [l5v0].map (vectorData true 54 5)
private def b5 := bands [(46,53,2),(45,51,4),(44,49,5),(43,47,6),(42,45,6),(41,43,6),(40,41,6),(39,39,6),(38,38,5),(37,37,4),(36,36,3),(35,35,2),(34,34,1)]
private theorem k5v0 : good true 54 l5v0 b5 := rfl
private theorem v5j0 : CJ6.VectorDots 54 5 z5 0 := v! true, 54, b5, l5v0, k5v0
theorem r5 : (CJ0.blockMatrix CJ6.source 54 ((5 : ℤ)-20)).rank ≤ 48 :=
  (CJ6.block_rank_le 54 5).trans (CJ6.rank_of_dots (z := z5) (by decide) (CJ6.belowSucc CJ6.belowZero v5j0))
private def l6v0 : List Lane := [⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩,⟨40,0,0,0,0⟩,⟨41,0,0,0,0⟩,⟨42,6,1,1,1⟩,⟨43,4,2,31,0x3f7ffffefeffffff⟩,⟨44,2,3,3,433⟩,⟨45,1,3,31,0x1fbfffff7f7ffffdfeffffff⟩,⟨46,0,3,2,25⟩,⟨47,0,0,0,0⟩]
private def l6v1 : List Lane := [⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩,⟨40,0,0,0,0⟩,⟨41,8,1,1,1⟩,⟨42,7,1,31,0x7efffffd⟩,⟨43,4,3,31,0x1bf7fffff7efffffe⟩,⟨44,2,4,31,0xfdfffffa00000024000000600000002⟩,⟨45,1,4,31,0x3fbffffe3f7ffff97efffffc⟩,⟨46,0,3,3,243⟩,⟨47,0,0,0,0⟩]
private def l6v2 : List Lane := [⟨35,0,0,0,0⟩,⟨36,0,0,0,0⟩,⟨37,0,0,0,0⟩,⟨38,0,0,0,0⟩,⟨39,0,0,0,0⟩,⟨40,10,1,1,1⟩,⟨41,9,1,31,0x7efffffd⟩,⟨42,7,2,31,0x37efffffd⟩,⟨43,4,4,31,0xfdfffffa0000003000000007efffffd⟩,⟨44,2,5,31,0x1fdffffea00000018000000800000003⟩,⟨45,1,4,31,0x9fbffffd7f7ffff4fefffff9⟩,⟨46,0,3,4,1734⟩,⟨47,0,0,0,0⟩]
private def z6 : CJ1.Block where
  bank := .rightHigh
  cap := 45
  free := [(6,2),(8,2),(10,2)]
  vectors := [l6v0,l6v1,l6v2].map (vectorData false 55 4)
private def b6 := bands [(0,43,13),(1,44,11),(2,45,9),(3,46,7),(4,47,5),(5,48,3),(6,49,1)]
private theorem k6v0 : good false 55 l6v0 b6 := rfl
private theorem v6j0 : CJ6.VectorDots 55 4 z6 0 := v! false, 55, b6, l6v0, k6v0
private theorem k6v1 : good false 55 l6v1 b6 := rfl
private theorem v6j1 : CJ6.VectorDots 55 4 z6 1 := v! false, 55, b6, l6v1, k6v1
private theorem k6v2 : good false 55 l6v2 b6 := rfl
private theorem v6j2 : CJ6.VectorDots 55 4 z6 2 := v! false, 55, b6, l6v2, k6v2
theorem r6 : (CJ0.blockMatrix CJ6.source 55 ((4 : ℤ)-20)).rank ≤ 45 :=
  (CJ6.block_rank_le 55 4).trans (CJ6.rank_of_dots (z := z6) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v6j0) v6j1) v6j2))
end CJ6_6
end
section
namespace CJ6_6
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l7v0 : List Lane := [⟨5,6,1,1,1⟩,⟨4,4,2,31,0x3f7fffee7effffbd⟩,⟨3,3,2,12,2882041⟩,⟨2,2,2,31,0x3f7fee277eff3fc7⟩,⟨1,1,2,20,0x164fe9e6a5⟩,⟨0,0,2,31,0x3f7a4855fe9b9891⟩]
private def l7v1 : List Lane := [⟨5,5,1,1,1⟩,⟨4,4,1,31,0x7effffdd⟩,⟨3,3,1,10,666⟩,⟨2,2,1,31,0x7effdf0d⟩,⟨1,1,1,17,82251⟩,⟨0,0,1,31,0x7ef5f5a9⟩]
private def z7 : CJ1.Block where
  bank := .leftHigh
  cap := 40
  free := [(5,0),(5,1)]
  vectors := [l7v0,l7v1].map (vectorData true 56 4)
private def b7 := bands [(48,56,1),(47,54,3),(46,52,4),(45,50,5),(44,48,5),(43,46,5),(42,44,5),(41,42,5),(40,40,5),(39,39,4),(38,38,3),(37,37,2),(36,36,1)]
private theorem k7v0 : good true 56 l7v0 b7 := rfl
private theorem v7j0 : CJ6.VectorDots 56 4 z7 0 := v! true, 56, b7, l7v0, k7v0
private theorem k7v1 : good true 56 l7v1 b7 := rfl
private theorem v7j1 : CJ6.VectorDots 56 4 z7 1 := v! true, 56, b7, l7v1, k7v1
theorem r7 : (CJ0.blockMatrix CJ6.source 56 ((4 : ℤ)-20)).rank ≤ 40 :=
  (CJ6.block_rank_le 56 4).trans (CJ6.rank_of_dots (z := z7) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v7j0) v7j1))
end CJ6_6
end
section
namespace CJ6_6
theorem proof : CJ6.c6 := ⟨r1, r2, r3, r4, r5, r6, r7, trivial⟩
end CJ6_6
end
