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
    refine cons (bank! 106,158255,0x256fa49ff0,0x89a58cff50) (bank! 561,346706,0xf1f0ba9f974,0x44b35a545d1b2c) ?_
    refine cons (bank! 113,152103,0x128ff4b4c,0xe3578b0d20) (bank! 594,412297,0x5a3342771d38,0x69235a825fcac0) ?_
    refine cons (bank! 109,127226,0xaf9cf1370,0xfffa95ee38) (bank! 541,268811,0x5919b98db2f0,0x6b0c5f90f85448) ?_
    refine cons (bank! 126,93309,0x296e33c1b8,0x13ad68cc478) (bank! 614,352059,0x2dcbf660e4b8,0x9de48bba2aa2f4) ?_
    refine cons (bank! 137,112034,0x5c654646e4,0x1b50ba34324) (bank! 681,410430,0x127c0c76b31f4,0xe85066cd3a81b8) ?_
    refine cons (bank! 152,155636,0xb048016ae0,0x24f35d4f5f0) (bank! 737,522887,0xacc631efbe70,0x14b1b90b4791678) ?_
    refine cons (bank! 162,123163,0x86f4f1bd50,0x32fcd259ce0) (bank! 880,514176,0xd908cc9466b0,0x200b5ef9c25bb08) ?_
    refine cons (bank! 174,188378,0xbdecfe4880,0x5e18a94f360) (bank! 973,588384,0x4d8a9ac0a8090,0x38d0da7b5cc4748) ?_
    refine cons (bank! 189,231980,0xeddbc350a0,0x775fb7d19f0) (bank! 1151,752368,0x1af2f81e8e2cc,0x5c3855260d9e884) ?_
    refine cons (bank! 214,238401,0x234a850a900,0xf66c9a30e00) (bank! 1232,747237,0x4ea88dac7dd2c,0xa5209ade6ab6e7c) ?_
    refine cons (bank! 234,168747,0x3d99ce517f8,0x1fb4af464bf0) (bank! 1717,1146901,0x2c830f80e4f3d8,0x1fb1a7538e3ef184) ?_
    refine cons (bank! 245,206304,0x10f5aa2ff68,0xebdea59a070) (bank! 1304,835193,0x5d2ea82457e0,0xb7c6779c89d7a98) ?_
    refine cons (bank! 269,137987,0x2cd4a148768,0x607ec2fc37c0) (bank! 1682,1001864,0x1ae5623de9b9bc,0x317ffdea95e910a0) ?_
    refine cons (bank! 301,355835,0xae04bcc5a18,0x2275d2023540) (bank! 1294,715409,0x27d58fbb4bab0,0x1562222435ed6e20) ?_
    refine cons (bank! 393,364721,0x330f565feb4,0x5d82de78fe00) (bank! 1831,1197945,0xb7d7a24941328,0x3ff8f154c78afe60) ?_
    refine cons (bank! 308,136812,0xcd52f5aaa80,0xa4cc163a86f0) (bank! 2091,1412704,0x62a90007cb04f8,0x70864c327dbc14e4) ?_
    refine cons (bank! 381,252426,0x1a74ad6df818,0xf82a64e272e0) (bank! 2173,1320638,0x5daad43b3869dc,0xb6e54543ceb86458) ?_
    refine cons (bank! 416,216958,0x15e2b48d7ac0,0x24db6f48d8300) (bank! 2472,1538930,0x40071b7713eef0,0x17064cc42ce12d024) ?_
    refine cons (bank! 372,307849,0x16f56f1397d0,0x3873a74985320) (bank! 1970,1030342,0x16c69e4e99f984,0x156767bc26a80af38) ?_
    refine cons (bank! 415,128096,0x15d9eae456f0,0x10029aafd868db8) (bank! 2385,978849,0x5d858dba03acf4,0x37e4a9cf278dd86c4) ?_
    refine cons (bank! 553,333110,0x2334bcae80c8,0x74a3f5fdabde0) (bank! 3233,1782556,0x1e717a941d4bfe0,0x5431d3e8e7c72f600) ?_
    refine cons (bank! 408,124832,0x9bd2860b1e0,0x100f5cd974dca4f0) (bank! 2088,958714,0x1275ba9bb4dc0c,0xbce04840a862432a4) ?_
    refine cons (bank! 693,446481,0x795f338443b0,0xbf3737f25bda0) (bank! 3774,2018411,0x2b9bd0e272abebc,0xa747f41c2dab644c4) ?_
    refine cons (bank! 845,577987,0x33a8ed6ba3d8,0x2ec55c30e38438) (bank! 5020,2900303,0xc557403893cdc0,0x28e4cd3ff666e93800) ?_
    refine cons (bank! 912,429796,0x3e8a69aa16a30,0x5d8cd972b32e0a38) (bank! 4900,267958,0xabdeb898cbd7f98,0x1ae147a2f519618b9fc) ?_
    refine cons (bank! 1107,730952,0x36767ee3da4a8,0xb7038b76dde930) (bank! 6456,3040345,0x2435dd746a636d28,0x9a860d4302d1399474) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,142165,0x3e283719a30,0x5999f7d6b0) (bank! 489,430010,0x48e6ce55b9e528,0x137b6c3f207f50) ?_
    refine cons (bank! 109,136448,0x5de81280d80,0x8e9a96ee30) (bank! 479,323393,0x6a0b5a5ba0d768,0x1bae0b12e63dc4) ?_
    refine cons (bank! 120,155956,0x822d4702664,0xcf6f37d484) (bank! 535,440461,0x988cdfb891fd04,0x2abb0b26091ba0) ?_
    refine cons (bank! 131,175464,0xaf56443af30,0x127cffca880) (bank! 571,354059,0xd455c34cfc2b70,0x3e855e95b63340) ?_
    refine cons (bank! 142,194972,0xe77e2a18000,0x19a9cb9f200) (bank! 608,447572,0x11e50bf9329b1ec,0x59507662186980) ?_
    refine cons (bank! 151,111910,0x132419edc3b8,0x23880d56168) (bank! 725,505840,0x182add152b31a10,0x8a2ce80e5bae60) ?_
    refine cons (bank! 150,235658,0x1d88e0415618,0x3691e9ca5f0) (bank! 791,647298,0x200dd0a12de49fc,0xc4c1d0d016964c) ?_
    refine cons (bank! 198,159000,0x3cba387fa6f8,0x8820d397760) (bank! 966,658180,0x50040b8f2157bd8,0x2365d40b6fb8d44) ?_
    refine cons (bank! 227,177653,0x10fe6ca6469d0,0x29fec3c97b20) (bank! 1181,860263,0xebb614ad16887c8,0x776efa8a72ccbb0) ?_
    refine cons (bank! 307,312559,0xd548353dc90c,0x28051be8e84c) (bank! 1321,885084,0x1468e937c881a620,0xb39cd8e604cb644) ?_
    refine cons (bank! 295,207592,0x31b9d6018cdd0,0x97ca6bb4f6e0) (bank! 1547,1111557,0x2b8d2af665ca4b20,0x1c33f35097fac490) ?_
    refine cons (bank! 363,237531,0x765e377697dc0,0x1a19c8c7c6d50) (bank! 2029,1426001,0x73389fe7643b879c,0x567176a39ba59b20) ?_
    refine cons (bank! 342,220508,0x2cb73fdfdd91240,0x9a16da5d0c8f30) (bank! 1692,1164068,0xf459230dba92bec0,0x9e0a3eb8491ddec0) ?_
    refine cons (bank! 387,340061,0x399ac4c3dd53930,0xdda953150a8e98) (bank! 1720,1002806,0x57925e7017a4839e0,0x33b8220d953a756a8) ?_
    refine cons (bank! 741,624782,0x155bcdf1cb3f88,0x8ee01e25ec948) (bank! 3123,2164422,0x2ec4a87ada09fbfa0,0x2c775efc98ca2faac) ?_
    refine cons (bank! 884,630123,0x5daa5e2f6091c0,0x2e44242c81f940) (bank! 4818,3346368,0x10553bfb2e491bdc18,0x12e4691aefe48bf028) ?_
    refine cons (bank! 1073,874650,0xc9523a629d3880,0x74ced5af83e780) (bank! 5783,3960610,0x268cee171771ccde40,0x2fd5eabf77c0407820) ?_
    refine cons (bank! 1444,1199270,0x261a3228f49a1c8,0x1c1f056956403b0) (bank! 7609,5087635,0x8ead34dee91ebc4510,0xbd1985ee14ee72ee98) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,130405,0x70bc3900,0x2732ca0) (bank! 29,147468,0x403f3acb8,0x1ed6b828) ?_
    refine cons (bank! 30,172831,0x24fd10298,0xdcaf4a8) (bank! 54,273530,0x1b27516900,0x12e56bc00) ?_
    refine cons (bank! 48,246372,0xa5f89b20c,0x5f3406e4) (bank! 90,467574,0xa8185e8600,0xa785fbb80) ?_
    refine cons (bank! 76,315570,0x366bd1f578,0x30ef7df80) (bank! 142,637471,0x3a585060b90,0x62bc51df10) ?_
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
