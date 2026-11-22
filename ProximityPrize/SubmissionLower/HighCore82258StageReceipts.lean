import ProximityPrize.SubmissionLower.HighCore82258Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Stages

open HighCore82258
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
    refine cons (bank! 106,162351,0x20ef589c40,0x7bad3e36c8) (bank! 607,386726,0x490e5bb019bc,0x50a5eaa0057db0) ?_
    refine cons (bank! 116,130155,0x16e4293354,0xbef02c57d8) (bank! 605,459326,0x7d6894a3f60c,0x7137d8c720c5a0) ?_
    refine cons (bank! 128,200417,0x5c3a768750,0x118d47335d8) (bank! 705,540590,0x304602695a60,0xbaa66a480e9db8) ?_
    refine cons (bank! 138,168221,0x29eba4fe14,0x192c82feb88) (bank! 683,230726,0x59a49a00f040,0xfb304ba224cee0) ?_
    refine cons (bank! 149,187254,0xa834a92ae8,0x23377db1a00) (bank! 729,372571,0xf92356de5480,0x166b8886a72b900) ?_
    refine cons (bank! 162,128859,0xf4a24e2498,0x30728dabb70) (bank! 891,700628,0x1bed12c4e5730,0x236fd5a55b08e68) ?_
    refine cons (bank! 176,116865,0x1125c6979e0,0x58814b322a0) (bank! 950,706650,0x3ebea8323310c,0x3c74ab52126b820) ?_
    refine cons (bank! 198,150103,0xdc56dcdf88,0xcbf901a5660) (bank! 1200,907396,0xacbc9bfc8ce90,0x948bf249e7d3de0) ?_
    refine cons (bank! 238,191549,0x214d03d17c4,0x489ceb48fb90) (bank! 1406,663472,0x320fe88476d10,0x1dd373b1fc7b0080) ?_
    refine cons (bank! 248,193149,0x476e17c1170,0xc6bcf0e8228) (bank! 1099,770075,0x61cadc94218d8,0x846f7bfd0475a6c) ?_
    refine cons (bank! 348,230961,0xc2b969342f8,0x4e83dfd741d4) (bank! 1806,602557,0x2393c2a89116c,0x45c5c2272d839e88) ?_
    refine cons (bank! 363,221916,0x13c8544943e8,0x33712240cdb08) (bank! 2023,482183,0x3fdcca9c6216d0,0x14d0b866bf57842a0) ?_
    refine cons (bank! 479,412956,0x2bfba7d88f08,0x1614c95048b38) (bank! 2224,839081,0x616619301dcda0,0x11d9f687047038f20) ?_
    refine cons (bank! 523,265750,0x6ad4770e8de0,0x59f9a402df920) (bank! 3124,830432,0xd198c6d2a9ea34,0x4bc4ebbc97b77fd14) ?_
    refine cons (bank! 832,485303,0x28d5d4e161530,0x2a2045a47994d8) (bank! 4833,1071161,0x6390c24daae7030,0x28ace08958f6057038) ?_
    refine cons (bank! 693,185656,0x7a422d080410,0x14481628d952a08) (bank! 3826,788982,0x297036ab61bfc6c,0x393aed856f240ffbec) ?_
    refine cons (bank! 1127,162708,0x257f9bf6d7690,0xc374d592dade00) (bank! 6619,522261,0x202ac1755461d688,0xc04d8b35a55552dc70) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,149643,0x120ae359a0,0x411fa80f30) (bank! 489,466257,0xfd57570fb90,0xde9ee59c70758) ?_
    refine cons (bank! 109,144256,0x374eeb2bf0,0x673dc63448) (bank! 479,358798,0x4829c474f280,0x125049ac08c840) ?_
    refine cons (bank! 120,164387,0x31ad37dca0,0x9a59ee56f0) (bank! 535,479741,0x6dd66152350,0x1d22a475fe9f80) ?_
    refine cons (bank! 131,184518,0x45a7355a20,0xe1a14eba10) (bank! 571,395910,0x807fc0b8740,0x2aaf7b23ace09c) ?_
    refine cons (bank! 142,204649,0x7c184b9b00,0x13f4bef8700) (bank! 608,491965,0x475b049a9aa8,0x3d13efa2a2ba68) ?_
    refine cons (bank! 151,122078,0x51526ed020,0x1bbfe38b568) (bank! 725,558722,0xd29d79c7f6c,0x66d65f48a54788) ?_
    refine cons (bank! 150,245541,0x5f43c99aa4,0x2861ef827d8) (bank! 791,704868,0x6977eed2ed90,0x951555e4b9eefc) ?_
    refine cons (bank! 198,171697,0xf306f350e8,0x6de71223ae0) (bank! 966,728056,0x26562d995e1b4,0x1b00b0b4dad5bc0) ?_
    refine cons (bank! 227,191356,0x383e7e43700,0x1f3787a02a30) (bank! 1181,944929,0x41645551ed248,0x59bf0f55e1df1c8) ?_
    refine cons (bank! 307,331800,0x36df16d19d4,0x2321bc5321fc) (bank! 1321,979836,0x8f201c51e1100,0x8a798e73aa9e470) ?_
    refine cons (bank! 295,224814,0x28b5c7576c0,0x75257e460388) (bank! 1547,1221912,0x16e51ce694312c,0x15a7fd0622eb61fc) ?_
    refine cons (bank! 363,258272,0xf196889bc20,0x14aba25bd4a60) (bank! 2030,1570724,0x26d000ce3eb90c,0x44b866bce5ab7188) ?_
    refine cons (bank! 342,238929,0x5a7f94d0ab0,0x1ba86f5afd0b00) (bank! 1692,1282968,0x2d4ec0dee9a000,0x6300a6f3c8b53800) ?_
    refine cons (bank! 387,360660,0x9b8733e9578,0x30fb975b86cc30) (bank! 1720,1122741,0x1ba8f9524af258,0x147e9eeb3dd45cb90) ?_
    refine cons (bank! 741,669336,0x10b27cd68a920,0x84297fd979658) (bank! 3124,2386299,0xb683806d5d938,0x23e48582a4a1d5b98) ?_
    refine cons (bank! 884,680145,0xf0aed3d7465c,0x29bdc7b8f52178) (bank! 4819,3689082,0x8e76f03e82f1720,0xfb3d41bbfa2b552d0) ?_
    refine cons (bank! 1073,935044,0x7bd50719eddc0,0x6a293c91fdd840) (bank! 5784,4371490,0x4e20b0b3a6c41c0,0x27c859ce5723e66800) ?_
    refine cons (bank! 1444,1280487,0x15a10b287d3164,0x19d91dac5545d98) (bank! 7611,5627712,0x125d41128f26c300,0x9d8015d61153361108) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129276,0x91b38d0,0x2b3a4f0) (bank! 29,145376,0x6b5df5e0,0x22d5a6a0) ?_
    refine cons (bank! 30,170872,0xc84f4e18,0xee1a738) (bank! 54,269782,0x33b81f4c,0x14f083b48) ?_
    refine cons (bank! 48,243388,0xa6f64cdc,0x66957bc4) (bank! 90,461452,0x4108a6fa00,0xba22184a0) ?_
    refine cons (bank! 76,311034,0x254912c820,0x3570486a8) (bank! 142,628008,0x1864c9d3718,0x6e86722fcc) ?_
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
end HighCore82258Stages
