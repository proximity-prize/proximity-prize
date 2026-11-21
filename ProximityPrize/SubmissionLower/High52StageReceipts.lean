import ProximityPrize.SubmissionLower.High52Stages
import ProximityPrize.SubmissionLower.High52Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High52Stages

open High52
open High52Stages (BankCertificate checked of_certificate)
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
  | h2452 =>
    rw [stages]
    refine cons (bank! 102,142546,0x3dc23f5880,0x567a8601b0) (bank! 490,354536,0x80accd1e2f00,0x15457cb993f294) ?_
    refine cons (bank! 84,114019,0x196a0a7f20,0xa139e7fc34c) (bank! 562,444124,0x10cbdf23875a0,0x247ea4f80b9fd8) ?_
    refine cons (bank! 152,178368,0x1498354a400,0xecba16c000) (bank! 618,432756,0x18c463b6b5f50,0x38c08db361bfc8) ?_
    refine cons (bank! 170,197087,0x26463849c60,0x17121f8a5a0) (bank! 657,320432,0x145c0f491ee38,0x51b518dd15dc98) ?_
    refine cons (bank! 182,262996,0x2c3bd75ba64,0x26df6296b5c) (bank! 775,682745,0x3c447f56b2af8,0xab7808efef63f0) ?_
    refine cons (bank! 195,195382,0x27ee36e0600,0x52126f05cf0) (bank! 906,652681,0x3fa3761276d80,0x1921b77d95e7d60) ?_
    refine cons (bank! 249,241731,0x8177d8188e0,0xfe5e3a573e0) (bank! 1192,774938,0xc8bd923b726c0,0x59832e088fb4678) ?_
    refine cons (bank! 268,292120,0x8818cd517fc,0x2cdd22c3f0dc) (bank! 1447,926474,0x2cdbaff7156698,0xeb7dbed62942188) ?_
    refine cons (bank! 503,436272,0x80e117b5ad38,0xca90bddc3a00) (bank! 1699,0x12a8d4,0x582e583f10c188,0x2829aeb24c365ff8) ?_
    refine cons (bank! 292,209705,0xe77639532d0,0x2e5a97ad95f5d0) (bank! 1828,442233,0x536dcde3616fe0,0x426f9ed566abc700) ?_
    refine cons (bank! 410,314780,0x3de65a3bf640,0xfdc1c07e7270) (bank! 2103,0x1c1741,0xd04a9e8a6648ac,0x60a3604bc36632f0) ?_
    refine cons (bank! 560,193301,0x969f55d36c40,0x5124ddafa6878) (bank! 2944,0x22d131,0x20d0c2601604680,0x1fa539d15403d2a20) ?_
    refine cons (bank! 524,262208,0x8db47c10a810,0x38df18f1861d490) (bank! 2988,0x2355e5,0x1da196450be4ae0,0x4875d1bcee19e02c8) ?_
    refine cons (bank! 693,639200,0x2786aa50c0a50,0x110817a17340b0) (bank! 3739,0x267cb9,0x50f4a01999c90f4,0x6a3cab116d5190404) ?_
    refine cons (bank! 732,177989,0x325200f2ee120,0x29b9c6ad196f3b30) (bank! 3898,0x14a1e1,0x892701325be607c,0x1a76abbdbe93ac4660) ?_
    refine cons (bank! 591,231135,0x10d0c2f859fa0,0x25905325c3473b40) (bank! 2817,0x18af67,0x19717cafac6eb08,0x11918e5b435059ca40) ?_
    refine cons (bank! 1117,949706,0xcb59835334480,0x9830442f3b72b8) (bank! 5950,0x38ecc0,0x1d37f4c3caa8b980,0x4138056a0af941fb30) ?_
    refine cons (bank! 112,110787,0x479ab8aa60,0x8702b26180) (bank! 528,190926,0xcdb2d12ba510,0xa0c7cb5dde5ab0) ?_
    refine cons (bank! 120,156361,0x7327369f80,0xca73665fec) (bank! 760,133311,0x201cb7703e69c,0x1efcb76170a19f8) ?_
    refine cons (bank! 127,150649,0xbb6045d880,0x138149647f8) (bank! 1502,633760,0x1de6bfb7978d98,0x62361b316e287560) ?_
    refine cons (bank! 135,196223,0x85ff035f48,0x1bc3c488af0) (bank! 921,464729,0x59f0a84dbf018,0xf976d6bc66824c) ?_
    refine cons (bank! 154,261324,0x129f5a4b3c0,0x33051e9f790) (bank! 686,353774,0x1f73b17a92564,0xe12b84e1e53e38) ?_
    refine cons (bank! 180,140808,0x324b4cdde80,0x74ec1061660) (bank! 973,537125,0x613dcacd67460,0x374ba975253a278) ?_
    refine cons (bank! 224,218916,0x4d623605120,0x10b0770393a0) (bank! 1383,598456,0x19fac3ffb20a20,0x5c35672fbcfda310) ?_
    refine cons (bank! 234,177349,0x5ad6f02a5a8,0x28017ec3f370) (bank! 1556,357592,0x418e7f1330b59c,0x1183c4ff1a0a8ce0) ?_
    refine cons (bank! 264,291401,0x7a0f70f3918,0x10be4649d8c8) (bank! 2512,0x1cb5d9,0x16e101d756834d8,0x4f0bb63442a242c0) ?_
    refine cons (bank! 347,156859,0x176495928174,0xd0fcc240b348) (bank! 3321,0x18948d,0x2c9448ab6544218,0x162b2ab3b1fdcb998) ?_
    refine cons (bank! 352,218672,0x24aad7dc3100,0x19ca24733a6f8) (bank! 1563,231938,0x3fc123763d7450,0x1cb7d6bba16f464c8) ?_
    refine cons (bank! 370,296239,0x3307b8a9f144,0x426e936d7ed8) (bank! 1417,96898,0x2fccb81471b0c0,0x160a2c8a4f6e9a40) ?_
    refine cons (bank! 440,175367,0x4c4de8cbc960,0x733fa67edec10) (bank! 3479,361178,0x394a7e32bce682c,0x2ef761b7738a376b8) ?_
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
end High52Stages
