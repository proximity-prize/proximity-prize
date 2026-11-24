import ProximityPrize.SubmissionLower.Z8Nymda
set_option Elab.async false
set_option autoImplicit true
namespace q33KzTa
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option quotPrecheck false in
local notation "r!" a "," b "," c =>
  row (l:=a) (q:=b) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) c (by decide +kernel) (by decide +kernel)
set_option quotPrecheck false in
local notation "p!" a =>
  prefix_at (k :=0) (m:=0) a (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option quotPrecheck false in
local notation "g!" a "," b "," c "," d =>
  base_next (k :=b) (x :=c) (y :=d) a (by decide +kernel) (by decide +kernel)
private theorem g1 :tu 4 16 0x62f5b0ec45e 0x418103d02 :=g! (base_zero 4),16,0x62f5b0ec45e,0x418103d02
private theorem g2 :tu 4 32 0xbc08a1584f0 0xeb7edd23d:=g! g1,16,0x5912f06c092,0xa9fdd953b
private theorem g3:tu 4 48 0x10bcb1f26ec3 0x1e5040dc28:=g! g2,16,0x4fc27dce9d3,0xf985309eb
private theorem g4 :tu 4 64 0x152d0f23bb68 0x3181d2cc7a :=g! g3,16,0x4705d314ca5,0x133191f052
private theorem g5:tu 4 69 0x1674f864f19d 0x380cb8909f :=g! g4,5,0x147e9413635,0x68ae5c425
private theorem g6:tu 4 70 0x16b50c43899d 0x39621fdb05:=g! g5,1,0x4013de9800,0x155674a66
private theorem g7:tu 4 71 0x16f4a1175f47 0x3ab983b194 :=g! g6,1,0x3f94d3d5aa,0x15763d68f
private theorem g8:tu 4 72 0x1733b774afa7 0x3c12d36bfc:=g! g7,1,0x3f165d5060,0x1594fba68
private theorem g9:tu 4 73 0x17724fefa9e4 0x3d6dfe8b76:=g! g8,1,0x3e987afa3d,0x15b2b1f7a
private theorem g10 :tu 4 74 0x17b06b1c7cd3 0x3ecaf4bae2 :=g! g9,1,0x3e1b2cd2ef,0x15cf62f6c
private theorem g11 :tu 4 75 0x17ee098f48c8 0x4029a5ce54 :=g! g10,1,0x3d9e72cbf5,0x15eb11372
private theorem g12 :tu 4 77 0x1867d2971096 0x42ebf8bee3:=g! g11,2,0x79c907c7ce,0x2c252f08f
private theorem g13:tu 4 78 0x18a3fe541d94 0x444f7b113d:=g! g12,1,0x3c2bbd0cfe,0x16382525a
private theorem g14 :tu 4 80 0x191ae7244244 0x471ae3bfb5:=g! g13,2,0x76e8d024b0,0x2cb68ae78
private theorem g15:tu 4 81 0x1955a55f1417 0x4882ab8459:=g! g14,1,0x3abe3ad1d3,0x167c7c4a4
private theorem g16:tu 4 83 0x19c9b85cec79 0x4b56169a82 :=g! g15,2,0x7412fdd862,0x2d36b1629
private theorem g17:tu 4 85 0x1a3bed3de51e 0x4e2e43d684 :=g! g16,2,0x7234e0f8a5,0x2d82d3c02
private theorem g18:tu 4 88 0x1ae3c62e0084 0x527a7655f6:=g! g17,3,0xa7d8f01b66,0x44c327f72
private theorem g19:tu 4 90 0x1b5163ee5cea 0x555c923367:=g! g18,2,0x6d9dc05c66,0x2e21bdd71
private theorem g20:tu 4 93 0x1bf26fbd4407 0x59b5a03313:=g! g19,3,0xa10bcee71d,0x4590dffac
private theorem g21 :tu 4 97 0x1cc2f3e7c224 0x5f8a835992 :=g! g20,4,0xd0842a7e1d,0x5d4e3267f
private theorem g22 :tu 4 101 0x1d8c8034609c 0x656688efff :=g! g21,4,0xc98c4c9e78,0x5dc05966d
private theorem g23:tu 4 107 0x1eae11b4346e 0x6e3744d55e :=g! g22,6,0x121917fd3d2,0x8d0bbe55f
private theorem g24 :tu 4 115 0x20191900bf52 0x79f5c26c3f :=g! g23,8,0x16b074c8ae4,0xbbe7d96e1
private theorem g25:tu 4 117 0x206fda9f31c8 0x7ce2b3b987:=g! g24,2,0x56c19e7276,0x2ecf14d48
theorem lane4_1 (b:ℕ) (h0:2≤b) (h1 :b≤22) :Test ⟨b,4,1⟩:= by
  interval_cases b
  · exact r! 70,0x6e57bee4c6e8673e,(p! g5)
  · exact r! 71,0x6c8a58d3f98fdbf2,(p! g6)
  · exact r! 72,0x68820f6a87d5c3d0,(p! g7)
  · exact r! 73,0x649a51bf9efde052,(p! g8)
  · exact r! 74,0x60d1616b6d3378d8,(p! g9)
  · exact r! 75,0x5d25b61448219e14,(p! g10)
  · exact r! 76,0x5b65f71260dda05d,(p! g11)
  · exact r! 78,0x55e205794fefd9de,(p! g12)
  · exact r! 79,0x5285792b484370a6,(p! g13)
  · exact r! 81,0x4f026e4d4a7b3985,(p! g14)
  · exact r! 82,0x4bd489b7dade3e91,(p! g15)
  · exact r! 84,0x4721ddca20c8626c,(p! g16)
  · exact r! 86,0x43f1aa3f4f1546de,(p! g17)
  · exact r! 89,0x3e4249585e4672b9,(p! g18)
  · exact r! 91,0x3b55c474b08c547d,(p! g19)
  · exact r! 94,0x364503a599202dc0,(p! g20)
  · exact r! 98,0x315e2045534aa99a,(p! g21)
  · exact r! 102,0x2cd101f208417763,(p! g22)
  · exact r! 108,0x26db4cf127b73a59,(p! g23)
  · exact r! 116,0x20a916aa33254e5e,(p! g24)
  · exact r! 129,0x186a1785d4a7a7a3,(prefix_at (k :=11) (m:=0x62f433d4ad) g25 rfl (by decide) (by decide) rfl (by decide))
end q33KzTa
