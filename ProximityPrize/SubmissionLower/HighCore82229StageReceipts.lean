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
    refine cons (bank! 106,160620,0x26752d7e40,0x83588f68b0) (bank! 607,376675,0x91bc5455adc0,0x54382b96de50b8) ?_
    refine cons (bank! 116,128303,0x28eeb0c020,0xca0b14eb00) (bank! 605,449358,0x8a6bac6ae678,0x77241fc4fc6338) ?_
    refine cons (bank! 128,198416,0x133fd2c878,0x1268176fe48) (bank! 705,529016,0x424c37b44d20,0xc2617d83f9a208) ?_
    refine cons (bank! 138,166099,0x2b1c2c6f8,0x1a59afa57a8) (bank! 684,399409,0x586610a67f08,0x1072af31c41acd8) ?_
    refine cons (bank! 149,184997,0x44ddf17288,0x24b548b38a0) (bank! 730,540562,0x1480fac98f1e8,0x179bce7a3eaa840) ?_
    refine cons (bank! 162,126430,0x6ade86ab90,0x324dcd7b520) (bank! 889,506225,0x1f0ceacce4074,0x248f4adbba97508) ?_
    refine cons (bank! 176,114296,0x1cb93af9c8,0x5bf743c3f78) (bank! 950,691241,0x2f08514bdc760,0x3eadc453f64da98) ?_
    refine cons (bank! 198,147310,0x3e2f81d10,0xd4464a0ff10) (bank! 1199,708100,0x3bc2f95d7c268,0x98632f99ec86568) ?_
    refine cons (bank! 238,188373,0x183f5887ed8,0x4c94fbe9e148) (bank! 1408,820753,0xd8b4f2b130e08,0x1eb758b09c66c8a0) ?_
    refine cons (bank! 248,189530,0x1fbddf8b798,0xca93c13b908) (bank! 1099,752340,0x52d5850ec185c,0x88fc0a6215f8e88) ?_
    refine cons (bank! 348,406045,0x12ae3aaa4bf0,0x4fb969e6eb3c) (bank! 1810,1113135,0xb7b130d70ff58,0x470f023575c8eba8) ?_
    refine cons (bank! 363,217411,0x3496d733cd8,0x35a9ae06ad1f0) (bank! 2029,1169561,0x218d06ebc77810,0x155826ee265f02410) ?_
    refine cons (bank! 479,406493,0x41ebc9d7a798,0x165a6af7d0818) (bank! 2228,1343223,0x3356b26c977dc0,0x123c5880d3182dc50) ?_
    refine cons (bank! 523,439047,0x5d60c7c3dc28,0x5ae755ce81cf0) (bank! 3132,1859837,0x182bea2d25145c,0x4cb0818a123cc1050) ?_
    refine cons (bank! 832,654834,0x90a3a0d4fb30,0x2a7456d51b1670) (bank! 4847,2792994,0x14751b8e3195e28,0x290a957b3b8c9c85e0) ?_
    refine cons (bank! 693,357613,0xadd487a770b0,0x14ab4c5dc5cca00) (bank! 3836,1988033,0x23f39305fb095a0,0x3a915990a71cb35460) ?_
    refine cons (bank! 1127,688514,0x669acc80f2d78,0xc16583495d4f2c) (bank! 6635,2575364,0xfe2925f89cf1940,0xc141b52d77a8346470) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,145755,0xae9c80778,0x4bdefd90f8) (bank! 489,447420,0x22db701eabf4,0x11ab5336d31f90) ?_
    refine cons (bank! 109,140188,0x1244a9e7c0,0x78be41c8d0) (bank! 479,340393,0x2b90970c8500,0x1876584523b480) ?_
    refine cons (bank! 120,159986,0x16ae1ad338,0xb2dc1b4468) (bank! 535,459311,0x600e0a516228,0x265c58172f3528) ?_
    refine cons (bank! 131,179784,0x38cba2a5c8,0x10340cdcab0) (bank! 571,374139,0x8d97050e880,0x3863037e365a40) ?_
    refine cons (bank! 142,199582,0x4eeb898ca0,0x16c4ae09220) (bank! 608,468862,0xa6d3acf262e0,0x50fa1f15f4d360) ?_
    refine cons (bank! 151,116750,0x261fce9bc8,0x1fa49c29058) (bank! 725,531200,0x3b79fc2a4c50,0x8150e08308b5c0) ?_
    refine cons (bank! 150,240348,0xb4b05315a4,0x2f64a541868) (bank! 791,674898,0x19a668af4d92c,0xb9b38392e40088) ?_
    refine cons (bank! 198,165010,0x1f43d6f4b0,0x7c39b247890) (bank! 966,691660,0x85f9e1e0b148,0x21b6bf0760d5b20) ?_
    refine cons (bank! 227,184093,0x11d333091e0,0x252f6bd213a8) (bank! 1181,900793,0x7fd44c195b480,0x724a04f24719400) ?_
    refine cons (bank! 307,321639,0x5e76071ff68,0x263f801de598) (bank! 1321,930444,0xca7af743d66c0,0xad4672f5703e220) ?_
    refine cons (bank! 295,215652,0x2553b3c15b8,0x8a37bed5f118) (bank! 1547,1164357,0xef13de8239554,0x1b654f894fa110d8) ?_
    refine cons (bank! 363,247211,0x14da754cb158,0x1831e80be43e0) (bank! 2029,1495241,0x36fa12eca1c670,0x54c3a8ca839cfd20) ?_
    refine cons (bank! 342,229038,0xbfbf3737498,0x4abcbd7bbb46c0) (bank! 1692,1220868,0x114a1665c9a3a0,0x95b52f998d0ad620) ?_
    refine cons (bank! 387,349581,0xea1b220ca58,0x7c93a7451bde90) (bank! 1720,1060056,0x3550f18ff1a18,0x2d2a7a01742aa90a8) ?_
    refine cons (bank! 741,645702,0x3799187b5a50,0x8cd87fd69e4b0) (bank! 3124,2270532,0x21f9c8d897198a8,0x2bfa995289cefc644) ?_
    refine cons (bank! 884,653433,0x17d591384cd8,0x2d8b096f6aba28) (bank! 4818,3510288,0xb35c8704de2f80c,0x12cc81fe89c8b00874) ?_
    refine cons (bank! 1073,902770,0x6a1e74d838100,0x737cacf762bd00) (bank! 5783,4157110,0x571a5dc69a2dad4,0x2fab2900b659d81a44) ?_
    refine cons (bank! 1444,1237080,0xa590d7709af98,0x1bedda60b820850) (bank! 7610,5345895,0x2ab84b361dfcf300,0xbcb0ee7783efcb9c80) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,130980,0xa9f3680,0x235d790) (bank! 29,148552,0x8cb33710,0x1d4ed9a8) ?_
    refine cons (bank! 30,173736,0x51cb8a40,0xd5e5da0) (bank! 54,275367,0x2b497f0c0,0x12c777678) ?_
    refine cons (bank! 48,247653,0x55ff36920,0x5f3406e4) (bank! 90,470481,0x91182b760,0xa8ebe2520) ?_
    refine cons (bank! 76,317405,0x29637fc210,0x319dbdce8) (bank! 142,641864,0xc6f57eb9b0,0x64bd8411c0) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

end HighCore82219Stages
