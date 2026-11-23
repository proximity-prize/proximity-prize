import ProximityPrize.SubmissionLower.Z8Nymda
set_option Elab.async false
set_option autoImplicit true
namespace q33KzTa
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
local notation "r!" a "," b "," c =>
  row (l:=a) (q:=b) rfl (by decide) (by decide) (by decide) c rfl (by decide)
local notation "p!" a =>
  prefix_at (k :=0) (m:=0) a rfl (by decide) (by decide) rfl (by decide)
local notation "g!" a "," b "," c "," d =>
  base_next (k :=b) (x :=c) (y :=d) a rfl rfl
private theorem g1 :tu 5 16 0x61a098fe822 0x403a36ef9:=g! (base_zero 5),16,0x61a098fe822,0x403a36ef9
private theorem g2 :tu 5 32 0xb714c9fe0e9 0xe25b6f292 :=g! g1,16,0x557430ff8c7,0xa22138399
private theorem g3:tu 5 48 0x1014221039a6 0x1c8a3d8464 :=g! g2,16,0x4a2d57058bd,0xe648691d2
private theorem g4 :tu 5 64 0x141102498fba 0x2d9e50889d:=g! g3,16,0x3fce0395614,0x1114130439
private theorem g5:tu 5 75 0x16761cdb2fbf 0x3a3a40af84 :=g! g4,11,0x2651a91a005,0xc9bf026e7
private theorem g6:tu 5 76 0x16aa75edc8c6 0x3b64a1e690:=g! g5,1,0x3459129907,0x12a61370c
private theorem g7:tu 5 77 0x16de424c3e8f 0x3c8f8ce932 :=g! g6,1,0x33cc5e75c9,0x12aeb02a2
private theorem g8:tu 5 79 0x1744387f6740 0x3ee6c0cb16:=g! g7,2,0x65f63328b1,0x25733e1e4
private theorem g9:tu 5 80 0x1776641ccdf4 0x4012ea78c6:=g! g8,1,0x322b9d66b4,0x12c29adb0
private theorem g10 :tu 5 82 0x17d920d35302 0x426c1103fd:=g! g9,2,0x62bcb6850e,0x259268b37
private theorem g11 :tu 5 84 0x1839c01c0853 0x44c5ee0961 :=g! g10,2,0x609f48b551,0x259dd0564
private theorem g12 :tu 5 86 0x1898490fd197 0x47200db668:=g! g11,2,0x5e88f3c944,0x25a1fad07
private theorem g13:tu 5 88 0x18f4c2c2e604 0x4979ffbb37:=g! g12,2,0x5c79b3146d,0x259f204cf
private theorem g14 :tu 5 90 0x194f3444a645 0x4bd3573fe0:=g! g13,2,0x5a7181c041,0x2595784a9
private theorem g15:tu 5 92 0x19a7a49f92aa 0x4e2baada4d:=g! g14,2,0x58705aec65,0x258539a6d
private theorem g16:tu 5 95 0x1a289a59a7d7 0x51ad62a6a8:=g! g15,3,0x80f5ba152d,0x381b7cc5b
private theorem g17:tu 5 99 0x1acdc9f87037 0x56532db8fe :=g! g16,4,0xa52f9ec860,0x4a5cb1256
private theorem g18:tu 5 103 0x1b6b72a2ead0 0x5aee283c20:=g! g17,4,0x9da8aa7a99,0x49afa8322
private theorem g19:tu 5 107 0x1c01cb9557ad 0x5f7ba47d63:=g! g18,4,0x9658f26cdd,0x48d7c4143
private theorem g20:tu 5 113 0x1cd6134c4e53 0x663130d7b0:=g! g19,6,0xd447b6f6a6,0x6b58c5a4d
private theorem g21 :tu 5 121 0x1dd9823698a2 0x6ede6e8b68:=g! g20,8,0x1036eea4a4f,0x8ad3db3b8
private theorem g22 :tu 5 134 0x1f49870d81a7 0x7c2c9c4a68:=g! g21,13,0x17004d6e905,0xd4e2dbf00
theorem lane5_1 (b:ℕ) (h0:2≤b) (h1 :b≤19) :Test ⟨b,5,1⟩:= by
  interval_cases b
  · exact r! 76,0x5b686652a1344ef3,(p! g5)
  · exact r! 77,0x57fd180481242d0c,(p! g6)
  · exact r! 78,0x54ac40b164d67a24,(p! g7)
  · exact r! 80,0x4fa386a6bf3a21dd,(p! g8)
  · exact r! 81,0x4e14cd95277a41fa,(p! g9)
  · exact r! 83,0x4961938ae4ea3916,(p! g10)
  · exact r! 85,0x44f3975ca57e0ccb,(p! g11)
  · exact r! 87,0x41f8da46742b11c5,(p! g12)
  · exact r! 89,0x3dec58063a04b176,(p! g13)
  · exact r! 91,0x3b2531303b5f3b96,(p! g14)
  · exact r! 93,0x376e52028ab287f3,(p! g15)
  · exact r! 96,0x33afd11d220e81aa,(p! g16)
  · exact r! 100,0x2e4ae9302baf08ee,(p! g17)
  · exact r! 104,0x2a1f142f7cd7fd28,(p! g18)
  · exact r! 108,0x263e70b41e5896c3,(p! g19)
  · exact r! 114,0x212ac14d5abc0fba,(p! g20)
  · exact r! 122,0x1bdf335f5d50568b,(p! g21)
  · exact r! 135,0x14d3fb67cb84e911,(p! g22)
end q33KzTa
