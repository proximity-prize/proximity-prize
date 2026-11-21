import ProximityPrize.SubmissionLower.HighCore82229NewMoments

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P3_7_1 (BankOK checked)
open HighCore82219

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2367 => exact (pass! 5119,7120,1510,0xe128896c00000,0x3f15ec384879; nextMoment7120_1510)
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
    refine stages_cons (pass! 76,105,23,0x345100000,0x3777f9; moment105_23) (pass! 404,562,118,0x1c6edf40000,0xa178c6a5; nextMoment562_118) ?_
    refine stages_cons (pass! 81,112,24,0x3e2240000,0x464bcb; nextMoment112_24) (pass! 428,595,125,0x21c85ec0000,0xcaca5052; nextMoment595_125) ?_
    refine stages_cons (pass! 78,108,23,0x376900000,0x3ca9b9; nextMoment108_23) (pass! 390,543,114,0x199ac680000,0x8cc85625; moment543_114) ?_
    refine stages_cons (pass! 90,125,27,0x558480000,0x6ce383; moment125_27) (pass! 442,615,129,0x252cb940000,0xe712e33d; nextMoment615_129) ?_
    refine stages_cons (pass! 98,136,30,0x6f9680000,0x9a30e6; nextMoment136_30) (pass! 491,683,143,0x32d29400000,0x15e85234c; nextMoment683_143) ?_
    refine stages_cons (pass! 109,151,33,0x979280000,0xe74c1b; nextMoment151_33) (pass! 531,738,155,0x40589300000,0x1de880865; nextMoment738_155) ?_
    refine stages_cons (pass! 116,161,35,0xb5c380000,0x128bb48; moment161_35) (pass! 634,882,186,0x6dc80e00000,0x3d18186c7; nextMoment882_186) ?_
    refine stages_cons (pass! 125,173,38,0xe40bc0000,0x18d4b08; nextMoment173_38) (pass! 701,975,205,0x93eccb80000,0x5aef90203; nextMoment975_205) ?_
    refine stages_cons (pass! 136,188,41,0x1230340000,0x224f886; nextMoment188_41) (pass! 830,1154,244,0xf64247c0000,0xb2ffabfb1; nextMoment1154_244) ?_
    refine stages_cons (pass! 154,213,47,0x1a8b200000,0x38bfb68; nextMoment213_47) (pass! 888,1235,261,0x12d6ab5c0000,0xea98932cb; nextMoment1235_261) ?_
    refine stages_cons (pass! 168,233,51,0x223cd80000,0x507dc25; nextMoment233_51) (pass! 1238,1721,365,0x3316da1c0000,0x37562c3cfd; nextMoment1721_365) ?_
    refine stages_cons (pass! 176,244,54,0x27a0ec0000,0x6176fe9; nextMoment244_54) (pass! 940,1307,276,0x165246500000,0x125fc26c02; nextMoment1307_276) ?_
    refine stages_cons (pass! 193,268,58,0x3355540000,0x8b05777; nextMoment268_58) (pass! 1213,1687,355,0x2fca43300000,0x32c91050b2; nextMoment1687_355) ?_
    refine stages_cons (pass! 217,300,67,0x4a41300000,0xdedff80; nextMoment300_67) (pass! 933,1298,273,0x15c511280000,0x11d168cd1f; nextMoment1298_273) ?_
    refine stages_cons (pass! 283,392,88,0xa4c1a80000,0x2881bf10; nextMoment392_88) (pass! 1320,1835,388,0x3dc53d480000,0x47547d44aa; nextMoment1835_388) ?_
    refine stages_cons (pass! 221,307,67,0x4d57b00000,0xeffb6fa; nextMoment307_67) (pass! 1508,2096,448,0x5ccf20680000,0x7a60dae739; nextMoment2096_448) ?_
    refine stages_cons (pass! 274,380,84,0x9407640000,0x235f32c1; nextMoment380_84) (pass! 1567,2179,461,0x67590c380000,0x8dc92dfed1; nextMoment2179_461) ?_
    refine stages_cons (pass! 299,415,91,0xbf09300000,0x31e9f423; nextMoment415_91) (pass! 1783,2479,526,0x988329100000,0xedf44d5ab0; nextMoment2479_526) ?_
    refine stages_cons (pass! 268,371,84,0x8ce2900000,0x20c08c09; nextMoment371_84) (pass! 1421,1977,416,0x4ccddb6c0000,0x5fb60cd0a4; nextMoment1977_416) ?_
    refine stages_cons (pass! 298,414,87,0xb74a900000,0x2fd6e865; nextMoment414_87) (pass! 1720,2395,500,0x876425080000,0xccb7865054; nextMoment2395_500) ?_
    refine stages_cons (pass! 398,552,121,0x1c06f240000,0x9b6be4a3; nextMoment552_121) (pass! 2332,3244,683,0x1531f7ce80000,0x2b4fcb8af08; nextMoment3244_683) ?_
    refine stages_cons (pass! 293,407,89,0xb38f080000,0x2e1859e9; nextMoment407_89) (pass! 1506,2096,439,0x5b1c71d00000,0x787427c579; nextMoment2096_439) ?_
    refine stages_cons (pass! 499,692,155,0x38015300000,0x185234383; nextMoment692_155) (pass! 2722,3787,799,0x21c10b6c00000,0x508a478f764; nextMoment3787_799) ?_
    refine stages_cons (pass! 609,844,187,0x64c14500000,0x3540983af; nextMoment844_187) (pass! 3621,5036,1070,0x4fd4b92ec0000,0xfd1cefeba54; nextMoment5036_1070) ?_
    refine stages_cons (pass! 657,911,204,0x7f80d840000,0x48d3f0165; nextMoment911_204) (pass! 3535,4935,1017,0x48c5840680000,0xe3e67c2d9d6; nextMoment4935_1017) ?_
    refine stages_cons (pass! 798,1106,244,0xe18c53c0000,0x9c255acf1; nextMoment1106_244) (pass! 4657,6482,1369,0xa91a172280000,0x2b334b40c95c; nextMoment6482_1369) ?_
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
end HighCore82219BankProof
