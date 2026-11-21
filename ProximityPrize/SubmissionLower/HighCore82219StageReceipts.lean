import ProximityPrize.SubmissionLower.HighCore82219Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219Stages

open HighCore82219
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine cons (bank! 106,157755,0x2e439e020,0x86cb0c46e8) (bank! 558,241610,0x88c6a5615290,0x3b5ae0412de4c0) ?_
    refine cons (bank! 116,125256,0x1c92b2b840,0xcd85ea6d60) (bank! 555,391992,0x21015e59548,0x5768faf6ffbbe0) ?_
    refine cons (bank! 128,195149,0x40ab9fb000,0x12850392960) (bank! 638,369572,0x815afd625a78,0x866430bf783acc) ?_
    refine cons (bank! 138,162650,0x3d5921318,0x1a4d0027bc0) (bank! 694,481793,0x78b239338ba0,0xc5e268b471b630) ?_
    refine cons (bank! 148,130151,0xa69da26718,0x24fe318e9c8) (bank! 799,248677,0x1982b35ca470,0x13595e9b98ac480) ?_
    refine cons (bank! 162,122511,0x18b15b5198,0x318a4f397f0) (bank! 791,580462,0x927f14803908,0x1855b1ed7d37fc8) ?_
    refine cons (bank! 159,144164,0x7c4028d08,0x4d303179368) (bank! 900,243476,0x4c57410a3134,0x240e00ae6b4532c) ?_
    refine cons (bank! 198,142897,0xe6f9892678,0xcca3c1290b0) (bank! 1068,755380,0x527aa2546fae0,0x62d21cf4a8bb988) ?_
    refine cons (bank! 238,183458,0x23db2586778,0x47187d072968) (bank! 1355,254154,0x719a6ea2553e4,0x160b15b65c18f6d4) ?_
    refine cons (bank! 276,159099,0x58e3068e38c,0x1a7b76efc460) (bank! 1355,134793,0x82c25ecf55cc4,0x10738f1e6a4f6fb4) ?_
    refine cons (bank! 390,191003,0x17feeaa0be18,0x8890043acab0) (bank! 1976,238728,0xec6af0cfdb00c,0x5f74cf6f2445f254) ?_
    refine cons (bank! 363,210639,0x1540bc7ca214,0x2ef53cbd93b88) (bank! 2108,1460464,0x6dae7bc829e20,0xe06c6ab9733f0954) ?_
    refine cons (bank! 360,222924,0x101302c55010,0x107cc3fd49f680) (bank! 1807,249013,0x1393915cd3c520,0x263e53c745f32060c) ?_
    refine cons (bank! 511,183957,0x16c745a74298,0x44273968caf10) (bank! 2651,242171,0x8b2e4ef54f33e8,0x2928a9c5f895c9488) ?_
    refine cons (bank! 617,170827,0x4f79d905b8,0x8ce1f1d702f50) (bank! 3403,142783,0xe22544f12c2a80,0x64ca42a6ce41e0630) ?_
    refine cons (bank! 847,133682,0x1a773752d4f28,0x3051a7ad0360b0) (bank! 5099,127293,0x3747ba154515480,0x2697710b87d5f99290) ?_
    refine cons (bank! 1127,128019,0x79479f0e1b880,0xb3522639ff8140) (bank! 6618,243255,0x127be137b6c27e28,0x92413fa2da18be2108) ?_
    refine cons (bank! 1673,133701,0x1a59f8c85edd70,0x4476f529cca9d48) (bank! 9249,241442,0x401832cbdb21ad74,0x3673da8ba6f5a9357c4) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,140269,0x12fd2b08e0,0x5999f7d6b0) (bank! 489,420816,0xa689d56a3c8,0x137b34d018f498) ?_
    refine cons (bank! 109,134472,0x4aa54bb50,0x8e9a96ee30) (bank! 479,314415,0x441ac0542918,0x1bad61356eac28) ?_
    refine cons (bank! 120,153826,0x212962d0ac,0xcf6f37d484) (bank! 535,430505,0x43ae7886c0f0,0x2abaa1801c8a7c) ?_
    refine cons (bank! 131,173180,0x236ac96b10,0x127cffca880) (bank! 571,343453,0x8f0a7eb4cde0,0x3e843eff1b1a78) ?_
    refine cons (bank! 142,192534,0x4093a2d400,0x19a9cb9f200) (bank! 608,436326,0x31b8b725bb2c,0x594e85178c1424) ?_
    refine cons (bank! 151,109350,0xce97a9488,0x23880d56168) (bank! 725,492444,0x149399b00b6f0,0x8a2a952714e810) ?_
    refine cons (bank! 150,233176,0x727a206b78,0x3691e9ca5f0) (bank! 791,632718,0x202378980045c,0xc4c01dce5ec810) ?_
    refine cons (bank! 198,155818,0x4a2ebc3658,0x8820d397760) (bank! 966,640492,0xf05c2165b4a4,0x23652c85bdca484) ?_
    refine cons (bank! 227,174239,0x2d13464c0f0,0x29fec3c97b20) (bank! 1181,838847,0xa82ad4afbecf8,0x776d41481dde7b8) ?_
    refine cons (bank! 307,307749,0xb852d9adacc,0x28051be8e84c) (bank! 1321,861116,0xce3d2ea5a5c08,0xb399895b1eba130) ?_
    refine cons (bank! 295,203316,0xd71be26ab0,0x97ca6bb4f6e0) (bank! 1547,1083655,0x1bb6a8720ab160,0x1c33941dea57f9f8) ?_
    refine cons (bank! 363,232393,0x18f0ec0b8240,0x1a19c8c7c6d50) (bank! 2029,1389411,0x3f483eb3773960,0x5670223b47f160cc) ?_
    refine cons (bank! 342,215974,0x79126432920,0x9a16da5d0c8f30) (bank! 1692,1134044,0xa88c05d605bc0,0x9e07e0c0f2fdf040) ?_
    refine cons (bank! 387,334999,0x13fa11fced50,0xdda953150a8e98) (bank! 1720,972540,0x16c1ce8362fb68,0x33b719874f8ce588c) ?_
    refine cons (bank! 741,613690,0x156524b4ce38,0x8ee01e25ec948) (bank! 3123,2108344,0x7cbb5202d286ec,0x2c76b21fb0ad547f8) ?_
    refine cons (bank! 884,617747,0x5321a337e300,0x2e44242c81f940) (bank! 4818,3259740,0x4b2689be99d0ba0,0x12e422c8298a015340) ?_
    refine cons (bank! 1073,859718,0x6a35495a8ca80,0x74ced5af83e780) (bank! 5783,3856762,0x5b390d17056c6f0,0x2fd53456cffd5e91d0) ?_
    refine cons (bank! 1444,1179192,0x16282d17620408,0x1c1f056956403b0) (bank! 7609,4951145,0x1d85721a42ba38c8,0xbd168a368a8de7089c) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129705,0x12b44650,0x2732ca0) (bank! 29,146156,0x211771c8,0x1ed6b828) ?_
    refine cons (bank! 30,171691,0xb9d27db0,0xdcaf4a8) (bank! 54,271264,0x23a30a500,0x12e56bc00) ?_
    refine cons (bank! 48,244714,0x2a53e1904,0x5f3406e4) (bank! 90,463948,0x1c46193900,0xa785fbb80) ?_
    refine cons (bank! 76,313140,0x12dc10edb8,0x30ef7df80) (bank! 142,631947,0x1006fac8fb0,0x62bc51df10) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end HighCore82219Stages
