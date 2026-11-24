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
private theorem g1 :tu 7 16 0x5f005c25d80 0x3dbb1b30e :=g! (base_zero 7),16,0x5f005c25d80,0x3dbb1b30e
private theorem g2 :tu 7 32 0xad7a269ae11 0xd0e5ee415:=g! g1,16,0x4e79ca75091,0x932ad3107
private theorem g3:tu 7 48 0xed31aabd07a 0x193c4f558c:=g! g2,16,0x3fb78422269,0xc2df07177
private theorem g4 :tu 7 64 0x11fec0711996 0x2690bfdf2a :=g! g3,16,0x32ba5c5491c,0xd5470899e
private theorem g5:tu 7 80 0x147679fe27db 0x33af97c371 :=g! g4,16,0x277b98d0e45,0xd1ed7e447
private theorem g6:tu 7 96 0x165549703fef 0x3fa71e04d8:=g! g5,16,0x1decf721814,0xbf7864167
private theorem g7:tu 7 101 0x16cfa7f15531 0x430e015965:=g! g6,5,0x7a5e811542,0x366e3548d
private theorem g8:tu 7 105 0x17291e061f20 0x45a509e215:=g! g7,4,0x597614c9ef,0x2970888b0
private theorem g9:tu 7 109 0x177b7d2a29f6 0x481cdabd1a :=g! g8,4,0x525f240ad6,0x277d0db05
private theorem g10 :tu 7 114 0x17d90b2183ef 0x4b05636c2b:=g! g9,5,0x5d8df759f9,0x2e888af11
private theorem g11 :tu 7 119 0x182ccbd67ba2 0x4dba964abe :=g! g10,5,0x53c0b4f7b3,0x2b532de93
private theorem g12 :tu 7 127 0x18a01b785f54 0x51a3a7b68d:=g! g11,8,0x734fa1e3b2,0x3e9116bcf
private theorem g13:tu 7 138 0x191d6fa3d1fd 0x562cabc91f :=g! g12,11,0x7d542b72a9,0x489041292
private theorem g14 :tu 7 154 0x199b49d8deee 0x5b1f4360a7:=g! g13,16,0x7dda350cf1,0x4f2979788
private theorem g15:tu 7 157 0x19acb9958c85 0x5bd94bd6aa :=g! g14,3,0x116fbcad97,0xba087603
theorem lane7_1 (b:ℕ) (h0:3≤b) (h1 :b≤10) :Test ⟨b,7,1⟩:= by
  interval_cases b
  · exact r! 102,0x2bb97010d368e18e,(p! g7)
  · exact r! 106,0x27e5faf7ca876a3c,(p! g8)
  · exact r! 110,0x23c2d4b2f2b93dcb,(p! g9)
  · exact r! 115,0x1fd6f82f53568486,(p! g10)
  · exact r! 120,0x1c49223f8daf0f7e,(p! g11)
  · exact r! 128,0x17d1ebe1336aa6e4,(p! g12)
  · exact r! 139,0x12a504d55d90fe96,(p! g13)
  · exact r! 158,0xc522ac421969580,(p! g15)
set_option quotPrecheck false in
local notation "p2!" a =>
  prefix_from (lane7_1 a (by decide) (by decide)) (by decide +kernel) (by decide +kernel)
theorem lane7_2 (b:ℕ) (h0:3≤b) (h1 :b≤10) :Test ⟨b,7,2⟩:= by
  interval_cases b
  · exact r! 102,0x2ba45323e1ffeaa2,(p2! 3)
  · exact r! 106,0x27d1f553d545995e,(p2! 4)
  · exact r! 110,0x23b04bf5b5025ff1,(p2! 5)
  · exact r! 115,0x1fc58b7caa2bbac3,(p2! 6)
  · exact r! 120,0x1c390e87c97e65e4,(p2! 7)
  · exact r! 128,0x17c3784ebc327254,(p2! 8)
  · exact r! 139,0x1298b7b7dca3d781,(p2! 9)
  · exact r! 158,0xc48e39be02643c3,(p2! 10)
end q33KzTa
