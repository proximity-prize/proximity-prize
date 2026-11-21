import ProximityPrize.SubmissionLower.HighCore82229Moments5

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82229BankProof

open P3_7_1 (BankOK checked)
open HighCore82229

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2367 => exact (pass! 4625,6431,1364,0xa60d3e1440000,0x29ff0aaee26a; moment6431_1364)
  | h2395 => exact (pass! 7550,10506,2218,0x2cfea55aa80000,0x129e297a45c0c; moment10506_2218)
  | h7773 => exact (pass! 124,173,32,0xc4fd80000,0x15c66e5; moment173_32)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine stages_cons (pass! 76,105,23,0x345100000,0x3777f9; moment105_23) (pass! 437,608,128,0x2407b5c0000,0xdd657d32; moment608_128) ?_
    refine stages_cons (pass! 83,115,25,0x439080000,0x4ed4ac; moment115_25) (pass! 436,606,128,0x23d8b880000,0xdb115372; moment606_128) ?_
    refine stages_cons (pass! 92,127,28,0x5c3600000,0x75b415; moment127_28) (pass! 508,706,149,0x389233c0000,0x19280bd7d; moment706_149) ?_
    refine stages_cons (pass! 99,137,30,0x722180000,0x9dd5af; moment137_30) (pass! 492,686,144,0x33533580000,0x1656b0db4; moment686_144) ?_
    refine stages_cons (pass! 107,148,33,0x917680000,0xd8f2fa; moment148_33) (pass! 525,731,154,0x3e6d7fc0000,0x1cdc7da38; moment731_154) ?_
    refine stages_cons (pass! 116,161,35,0xb5c380000,0x128bb48; moment161_35) (pass! 642,892,188,0x71d1af40000,0x3fe068fa5; moment892_188) ?_
    refine stages_cons (pass! 126,175,39,0xec9f00000,0x1a458a5; moment175_39) (pass! 685,952,201,0x8a677880000,0x52f0bdb9b; moment952_201) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 865,1202,254,0x1166fe340000,0xd28832ce8; moment1202_254) ?_
    refine stages_cons (pass! 171,237,50,0x2316e80000,0x53b7f45; moment237_50) (pass! 1014,1412,298,0x1c0729180000,0x1901657cf3; moment1412_298) ?_
    refine stages_cons (pass! 178,247,55,0x2932d00000,0x66c8fdf; moment247_55) (pass! 792,1101,233,0xd623cb40000,0x947787094; moment1101_233) ?_
    refine stages_cons (pass! 250,347,78,0x721cb80000,0x18f6d6a4; moment347_78) (pass! 1302,1815,383,0x3b50b1000000,0x442ac5ba92; moment1815_383) ?_
    refine stages_cons (pass! 261,362,81,0x813b280000,0x1d6fb003; moment362_81) (pass! 1459,2035,429,0x536744d80000,0x6b96ecc888; moment2035_429) ?_
    refine stages_cons (pass! 345,478,108,0x12b1e340000,0x59a98629; moment478_108) (pass! 1604,2235,472,0x6edb04b80000,0x9cb2a062f8; moment2235_472) ?_
    refine stages_cons (pass! 376,522,118,0x183833c0000,0x7f6275d9; moment522_118) (pass! 2253,3142,664,0x1334cd7ac0000,0x263b0eab16b; moment3142_664) ?_
    refine stages_cons (pass! 599,831,188,0x617b2300000,0x32de21d13; moment831_188) (pass! 3486,4863,1027,0x4711f2a780000,0xdb0e8041cee; moment4863_1027) ?_
    refine stages_cons (pass! 498,692,155,0x37c11c80000,0x185234383; moment692_155) (pass! 2760,3850,812,0x233f7cff80000,0x5601e71ab3f; moment3850_812) ?_
    refine stages_cons (pass! 809,1126,252,0xee4ed940000,0xa99a27482; moment1126_252) (pass! 4774,6667,1405,0xb6532fbfc0000,0x304357eb723c; moment6667_1405) ?_
    exact stages_nil
  | h2395 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 352,489,103,0x12dda700000,0x5cfd94a5; moment489_103) ?_
    refine stages_cons (pass! 78,108,24,0x392740000,0x3e9e8f; moment108_24) (pass! 345,480,101,0x11c61f80000,0x564a51c0; moment480_101) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 385,535,112,0x188bf840000,0x84679137; moment535_112) ?_
    refine stages_cons (pass! 94,130,29,0x633bc0000,0x822d2c; moment130_29) (pass! 411,572,120,0x1dec1a80000,0xad1e0c80; moment572_120) ?_
    refine stages_cons (pass! 102,141,31,0x7cec00000,0xb15384; moment141_31) (pass! 438,609,128,0x2436d340000,0xde912dc3; moment609_128) ?_
    refine stages_cons (pass! 108,150,33,0x948040000,0xe271e9; moment150_33) (pass! 522,726,153,0x3d548e40000,0x1c16ef1c7; moment726_153) ?_
    refine stages_cons (pass! 108,149,33,0x948040000,0xdda994; moment149_33) (pass! 570,792,167,0x4fc3e700000,0x27c2e15db; moment792_167) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 696,968,204,0x910a3980000,0x5884788a7; moment968_204) ?_
    refine stages_cons (pass! 163,226,50,0x1f8a780000,0x47e88b5; moment226_50) (pass! 851,1183,249,0x108708880000,0xc4f2a7606; moment1183_249) ?_
    refine stages_cons (pass! 221,306,68,0x4e346c0000,0xf032b8c; moment306_68) (pass! 952,1324,279,0x17270e900000,0x1350bb1fb5; moment1324_279) ?_
    refine stages_cons (pass! 212,294,65,0x44e9c40000,0xcc1a54f; moment294_65) (pass! 1115,1550,329,0x255cff880000,0x2473d5ffe4; moment1550_329) ?_
    refine stages_cons (pass! 261,362,82,0x826c0c0000,0x1db6eefa; moment362_82) (pass! 1463,2034,430,0x54106e900000,0x6b9d823520; moment2034_430) ?_
    refine stages_cons (pass! 246,341,75,0x6ae4280000,0x16e7d3b2; moment341_75) (pass! 1220,1696,357,0x309db61c0000,0x33e3754396; moment1696_357) ?_
    refine stages_cons (pass! 279,386,85,0x9b80980000,0x25892b87; moment386_85) (pass! 1240,1725,359,0x32a0cb700000,0x370899d961; moment1725_359) ?_
    refine stages_cons (pass! 534,740,167,0x44f1df00000,0x1ff6e1863; moment740_167) (pass! 2252,3131,661,0x131ef423c0000,0x25ab1ba8825; moment3131_661) ?_
    refine stages_cons (pass! 637,883,197,0x73e2ad80000,0x401d0f0c6; moment883_197) (pass! 3474,4830,1019,0x461aa92080000,0xd5013df2ef9; moment4830_1019) ?_
    refine stages_cons (pass! 774,1072,239,0xcf60ca00000,0x8af950b98; moment1072_239) (pass! 4170,5798,1223,0x7934721300000,0x1ba1a89b2ba1; moment5798_1223) ?_
    refine stages_cons (pass! 1042,1443,329,0x201c60040000,0x1cf53a5560; moment1443_329) (pass! 5487,7630,1607,0x113c22e7a00000,0x52bdbe618ec3; moment7630_1607) ?_
    exact stages_nil
  | h7773 =>
    rw [stages]
    refine stages_cons (pass! 11,15,3,0x3500000,0x892; moment15_3) (pass! 20,28,4,0xdc00000,0x4287; moment28_4) ?_
    refine stages_cons (pass! 21,29,6,0x13cc0000,0x609d; moment29_6) (pass! 38,53,9,0x5d840000,0x33bc5; moment53_9) ?_
    refine stages_cons (pass! 34,47,10,0x4f100000,0x26533; moment47_10) (pass! 64,89,15,0x1a3600000,0x17e10a; moment89_15) ?_
    refine stages_cons (pass! 54,75,16,0x12f140000,0xe9a95; moment75_16) (pass! 101,141,24,0x64f3c0000,0x91e8ba; moment141_24) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s, hs, rfl | rfl⟩ | ⟨i, rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes, (terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

theorem interpolation_sources_for_crt : CRTSourceExists :=
  source_for_crt (fun b t ht => (listed_ok b t ht).nodes)
    (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources_for_crt
#print axioms interpolation_sources
end HighCore82229BankProof
