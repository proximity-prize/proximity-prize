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
private theorem g1 :tu 6 16 0x604ed135c5b 0x3ef8420ac:=g! (base_zero 6),16,0x604ed135c5b,0x3ef8420ac
private theorem g2 :tu 6 32 0xb23a99d657a 0xd97e2c818:=g! g1,16,0x51ebc8a091f,0x9a85ea76c
private theorem g3:tu 6 48 0xf70ef12cc75 0x1ad91a7e44 :=g! g2,16,0x44d457566fb,0xd4137b62c
private theorem g4 :tu 6 64 0x130195c314fd 0x29f95ccb30:=g! g3,16,0x390a6b04888,0xf20424cec
private theorem g5:tu 6 80 0x15ea52f704c5 0x399c0e36dc:=g! g4,16,0x2e8bd33efc8,0xfa2b16bac
private theorem g6:tu 6 84 0x168caa6ed08a 0x3d7866f9a5:=g! g5,4,0xa25777cbc5,0x3dc58c2c9
private theorem g7:tu 6 85 0x16b3d8d0ec71 0x3e6db90056:=g! g6,1,0x272e621be7,0xf55206b1
private theorem g8:tu 6 87 0x17008ee76312 0x4055e44de2 :=g! g7,2,0x4cb61676a1,0x1e82b4d8c
private theorem g9:tu 6 89 0x174b19aa28fe 0x423a7252c1 :=g! g8,2,0x4a8ac2c5ec,0x1e48e04df
private theorem g10 :tu 6 91 0x179382f33409 0x441b0501f7:=g! g9,2,0x4869490b0b,0x1e092af36
private theorem g11 :tu 6 94 0x17fc378a686e 0x46e3a6d0f8:=g! g10,3,0x68b4973465,0x2c8a1cf01
private theorem g12 :tu 6 97 0x186057b98f22 0x49a16de09b:=g! g11,3,0x64202f26b4,0x2bdc70fa3
private theorem g13:tu 6 100 0x18c00418cb4b 0x4c5352fd01 :=g! g12,3,0x5fac5f3c29,0x2b1e51c66
private theorem g14 :tu 6 103 0x191b5cf65b6f 0x4ef863b6de :=g! g13,3,0x5b58dd9024,0x2a510b9dd
private theorem g15:tu 6 108 0x19aa5565ab31 0x5341ffb777:=g! g14,5,0x8ef86f4fc2,0x4499c0099
private theorem g16:tu 6 113 0x1a2e345f2554 0x57620b1bdf :=g! g15,5,0x83def97a23,0x4200b6468
private theorem g17:tu 6 119 0x1abe9652b577 0x5c1a45cb9a :=g! g16,6,0x9061f39023,0x4b83aafbb
private theorem g18:tu 6 128 0x1b7cc5c44239 0x62ada78260:=g! g17,9,0xbe2f718cc2,0x69361b6c6
private theorem g19:tu 6 141 0x1c5d351f1b8c 0x6b0c44c874 :=g! g18,13,0xe06f5ad953,0x85e9d4614
private theorem g20:tu 6 157 0x1d2b9fdd3437 0x7378b66088:=g! g19,16,0xce6abe18ab,0x86c719814
private theorem g21 :tu 6 170 0x1da47b332bb2 0x78d4165019:=g! g20,13,0x78db55f77b,0x55b5fef91
theorem lane6_1 (b:ℕ) (h0:2≤b) (h1 :b≤16) :Test ⟨b,6,1⟩:= by
  interval_cases b
  · exact r! 85,0x448c5ad1bcc0ddac,(p! g6)
  · exact r! 86,0x432c7209b6f59f0b,(p! g7)
  · exact r! 88,0x3f238beb5aec87a6,(p! g8)
  · exact r! 90,0x3b5467b5169c8c5f,(p! g9)
  · exact r! 92,0x38bcdaa66970917b,(p! g10)
  · exact r! 95,0x341873acdc0cb4d2,(p! g11)
  · exact r! 98,0x30a6aa977c374cb9,(p! g12)
  · exact r! 101,0x2d618d51a5cc6cf3,(p! g13)
  · exact r! 104,0x2990a29de53c415a,(p! g14)
  · exact r! 109,0x250662d3fa7c9014,(p! g15)
  · exact r! 114,0x20ea0c1f20253053,(p! g16)
  · exact r! 120,0x1c8e69c99dbc56b2,(p! g17)
  · exact r! 129,0x177aa18203aad4d9,(p! g18)
  · exact r! 142,0x11ca41601fb64dde,(p! g19)
  · exact r! 171,0x9742062570cfdbc,(p! g21)
local notation "p2!" a =>
  prefix_from (lane6_1 a (by decide) (by decide)) rfl (by decide)
theorem lane6_2 (b:ℕ) (h0:2≤b) (h1 :b≤16) :Test ⟨b,6,2⟩:= by
  interval_cases b
  · exact r! 85,0x4469f244fdbf3d98,(p2! 2)
  · exact r! 86,0x430a5222da30aac8,(p2! 3)
  · exact r! 88,0x3f02a906f2f37ad4,(p2! 4)
  · exact r! 90,0x3b34bd66a711fc57,(p2! 5)
  · exact r! 92,0x389dda98fcc9f484,(p2! 6)
  · exact r! 95,0x33faf8667bb646b8,(p2! 7)
  · exact r! 98,0x308a306bb692f0ed,(p2! 8)
  · exact r! 101,0x2d461a8688596f24,(p2! 9)
  · exact r! 104,0x2976ad12f2c79641,(p2! 10)
  · exact r! 109,0x24ee06d4f27a669e,(p2! 11)
  · exact r! 114,0x20d3489af7ffb774,(p2! 12)
  · exact r! 120,0x1c797d6d78f3cabb,(p2! 13)
  · exact r! 129,0x1767ef663a5fa48e,(p2! 14)
  · exact r! 142,0x11ba6055e96c0718,(p2! 15)
  · exact r! 171,0x969618fdda3e23b,(p2! 16)
end q33KzTa
