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
private theorem g1 :tu 3 16 0x644e161dd39 0x42ccb296c:=g! (base_zero 3),16,0x644e161dd39,0x42ccb296c
private theorem g2 :tu 3 32 0xc1160371cd9 0xf4e99d418:=g! g1,16,0x5cc7ed53fa0,0xb21ceaaac
private theorem g3:tu 3 48 0x116a9a57e679 0x202bacf604 :=g! g2,16,0x5593a20c9a0,0x10dd1321ec
private theorem g4 :tu 3 63 0x160a2967842f 0x3430e139f0:=g! g3,15,0x49f8f0f9db6,0x14053443ec
private theorem g5:tu 3 64 0x1655bad9cdee 0x35a61b4530:=g! g4,1,0x4b917249bf,0x1753a0b40
private theorem g6:tu 3 65 0x16a0e365a291 0x371eed585d:=g! g5,1,0x4b288bd4a3,0x178d2132d
private theorem g7:tu 3 66 0x16eba35e6d1d 0x389b481e43:=g! g6,1,0x4abff8ca8c,0x17c5ac5e6
private theorem g8:tu 3 67 0x1735fb179521 0x3a1b1c5b11 :=g! g7,1,0x4a57b92804,0x17fd43cce
private theorem g9:tu 3 68 0x177feae48d4c 0x3b9e5aec89:=g! g8,1,0x49efccf82b,0x1833e9178
private theorem g10 :tu 3 69 0x17c97318c4a4 0x3d24f4c9ab:=g! g9,1,0x4988343758,0x18699dd22
private theorem g11 :tu 3 70 0x18129407b51f 0x3eaedb02e7:=g! g10,1,0x4920eef07b,0x189e6393c
private theorem g12 :tu 3 72 0x18a3a163a356 0x41cc51491e :=g! g11,2,0x910d5bee37,0x31d764637
private theorem g13:tu 3 73 0x18eb8e7799a7 0x435fc3f4b9:=g! g12,1,0x47ed13f651,0x19372ab9b
private theorem g14 :tu 3 74 0x1933159438c5 0x44f648398b:=g! g13,1,0x47871c9f1e,0x1968444d2
private theorem g15:tu 3 76 0x19c0f335624c 0x482c4bdee7:=g! g14,2,0x8ddda12987,0x33603a55c
private theorem g16:tu 3 77 0x1a074a60e9e2 0x49cbaea5af :=g! g15,1,0x46572b8796,0x19f62c6c8
private theorem g17:tu 3 79 0x1a92cb0f5d8f 0x4d12ef54cc:=g! g16,2,0x8b80ae73ad,0x34740af1d
private theorem g18:tu 3 81 0x1b1cbbb4502d 0x5065219c75:=g! g17,2,0x89f0a4f29e,0x3523247a9
private theorem g19:tu 3 83 0x1ba51eebbbd1 0x53c1d6eeed:=g! g18,2,0x8863376ba4,0x35cb55278
private theorem g20:tu 3 85 0x1c2bf7519760 0x5728a244b3:=g! g19,2,0x86d865db8f,0x366cb55c6
private theorem g21 :tu 3 87 0x1cb14781d377 0x5a99181a42 :=g! g20,2,0x8550303c17,0x37075d58f
private theorem g22 :tu 3 91 0x1db759b0dc80 0x61955cbd13:=g! g21,4,0x106122f0909,0x6fc44a2d1
private theorem g23:tu 3 94 0x1e77f52da73f 0x66e8e63887:=g! g22,3,0xc09b7ccabf,0x553897b74
private theorem g24 :tu 3 96 0x1ef680b345f1 0x6a7fd10348:=g! g23,2,0x7e8b859eb2,0x396eacac1
private theorem g25:tu 3 99 0x1fb18e4ac402 0x6ff00f9109:=g! g24,3,0xbb0d977e11,0x5703e8dc1
theorem r0_0_0:Test ⟨0,0,0⟩:=r! 55,0xbd8a5d191d76e950,empty_prefix
private theorem zLx1 :Test ⟨1,3,1⟩:=r! 64,0x88cf620583d772a9,(p! g4)
private theorem zLx2 :Test ⟨2,3,1⟩:=r! 65,0x83d4a01f053a5a6c,(p! g5)
private theorem zLx3 :Test ⟨3,3,1⟩:=r! 66,0x81d76c52078a7f8d,(p! g6)
private theorem zLx4 :Test ⟨4,3,1⟩:=r! 67,0x7d0d038766aa5792,(p! g7)
private theorem zLx5 :Test ⟨5,3,1⟩:=r! 68,0x786bd6a25a20703f,(p! g8)
private theorem zLx6 :Test ⟨6,3,1⟩:=r! 68,0x76ad592206b9ed63,(p! g8)
private theorem zLx7 :Test ⟨7,3,1⟩:=r! 69,0x7237ecb01931bca3,(p! g9)
private theorem zLx8 :Test ⟨8,3,1⟩:=r! 70,0x6de6fd1c15985b10,(p! g10)
private theorem zLx9 :Test ⟨9,3,1⟩:=r! 71,0x6bf4de47ad78f676,(p! g11)
private theorem zLx10 :Test ⟨10,3,1⟩:=r! 73,0x656e1a7105027db1,(p! g12)
private theorem zLx11 :Test ⟨11,3,1⟩:=r! 74,0x617e9126add3cf08,(p! g13)
private theorem zLx12 :Test ⟨12,3,1⟩:=r! 75,0x5dac522fb557a9bd,(p! g14)
private theorem zLx13 :Test ⟨13,3,1⟩:=r! 77,0x59b7d3acdf3e869f,(p! g15)
private theorem zLx14 :Test ⟨14,3,1⟩:=r! 78,0x561b565f21bfdb78,(p! g16)
private theorem zLx15 :Test ⟨15,3,1⟩:=r! 80,0x50c3ee160b03e1a6,(p! g17)
private theorem zLx16 :Test ⟨16,3,1⟩:=r! 82,0x4d2d98c357f68d7e,(p! g18)
private theorem zLx17 :Test ⟨17,3,1⟩:=r! 84,0x484b344d2179905c,(p! g19)
private theorem zLx18 :Test ⟨18,3,1⟩:=r! 86,0x44f035f31523cca6,(p! g20)
private theorem zLx19 :Test ⟨19,3,1⟩:=r! 88,0x40735f0663ea5802,(p! g21)
private theorem zLx20 :Test ⟨20,3,1⟩:=r! 92,0x3aa6985d5a61a94c,(p! g22)
private theorem zLx21 :Test ⟨21,3,1⟩:=r! 95,0x3580abe37089ce9c,(p! g23)
private theorem zLx22 :Test ⟨22,3,1⟩:=r! 100,0x2f758153bb8e73b9,(p! g25)
private theorem zLx23 :Test ⟨23,3,1⟩:=r! 106,0x29c261235fb565f0,(prefix_at (k :=9) (m:=0xac03f1ca0c) g24 rfl (by decide) (by decide) rfl (by decide))
private theorem zLx24 :Test ⟨24,3,1⟩:=r! 116,0x217a3d0f0536563f,(prefix_at (k :=24) (m:=0x182ebfe3ce8) g22 rfl (by decide) (by decide) (join_tail (k :=12) (m:=12) (x :=0xe5bbcca7cb) (y :=0x9d3031951d) rfl rfl) (by decide))
theorem lane3_1 (b:ℕ) (h0:1≤b) (h1 :b≤24) :Test ⟨b,3,1⟩:= by
  interval_cases b
  exacts [zLx1,zLx2,zLx3,zLx4,zLx5,zLx6,zLx7,zLx8,zLx9,zLx10,zLx11,zLx12,zLx13,zLx14,zLx15,zLx16,zLx17,zLx18,zLx19,zLx20,zLx21,zLx22,zLx23,zLx24]
end q33KzTa
