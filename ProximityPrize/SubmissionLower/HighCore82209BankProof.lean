import ProximityPrize.SubmissionLower.HighCore82209Moments5

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209BankProof

open P3_7_1 (BankOK checked)
open HighCore82209

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2367 => exact (pass! 6825,9490,2013,0x21575027980000,0xc712452a9ff2; moment9490_2013)
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
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 349,485,102,0x125f7fc0000,0x59e3ed8b; moment485_102) ?_
    refine stages_cons (pass! 80,111,24,0x3c7300000,0x4451ef; moment111_24) (pass! 358,498,104,0x13bbdc40000,0x6355595b; moment498_104) ?_
    refine stages_cons (pass! 89,123,27,0x536d00000,0x67700d; moment123_27) (pass! 406,565,119,0x1ceebd00000,0xa5555e6d; moment565_119) ?_
    refine stages_cons (pass! 97,134,30,0x6d1340000,0x931387; moment134_30) (pass! 425,591,125,0x2141d180000,0xc672a1cc; moment591_125) ?_
    refine stages_cons (pass! 106,147,32,0x8b45c0000,0xcf7010; moment147_32) (pass! 461,640,135,0x2a445e00000,0x1100a07c3; moment640_135) ?_
    refine stages_cons (pass! 115,159,35,0xb24d00000,0x11d1f9e; moment159_35) (pass! 515,716,150,0x3a9f1980000,0x1a74a03e8; moment716_150) ?_
    refine stages_cons (pass! 115,160,34,0xae8580000,0x11c9279; moment160_34) (pass! 579,806,170,0x53ba8f80000,0x2aa645c9f; moment806_170) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 679,944,199,0x86af1a00000,0x5018948c9; moment944_199) ?_
    refine stages_cons (pass! 169,235,50,0x222f040000,0x517adc3; moment235_50) (pass! 888,1233,260,0x12c890e80000,0xe8ae039a1; moment1233_260) ?_
    refine stages_cons (pass! 214,296,66,0x472de80000,0xd30a80f; moment296_66) (pass! 809,1126,236,0xe2bba140000,0xa12bddaf7; moment1126_236) ?_
    refine stages_cons (pass! 216,299,66,0x48ac040000,0xd9f9f46; moment299_66) (pass! 1185,1646,346,0x2c7b45940000,0x2dfe19c180; moment1646_346) ?_
    refine stages_cons (pass! 261,362,81,0x813b280000,0x1d6fb003; moment362_81) (pass! 1450,2015,424,0x5186864c0000,0x6746edbc88; moment2015_424) ?_
    refine stages_cons (pass! 259,359,81,0x7f07680000,0x1ca909eb; moment359_81) (pass! 1274,1771,373,0x375ff1cc0000,0x3db5501b19; moment1771_373) ?_
    refine stages_cons (pass! 429,593,135,0x23fdde00000,0xd4e9369b; moment593_135) (pass! 2025,2816,590,0xdd3ba2e40000,0x1882537ea3b; moment2816_590) ?_
    refine stages_cons (pass! 611,846,188,0x65e80780000,0x35e195e5b; moment846_188) (pass! 2993,4162,879,0x2ce2150400000,0x75919b3c614; moment4162_879) ?_
    refine stages_cons (pass! 776,1076,242,0xd28dc840000,0x8e03abac2; moment1076_242) (pass! 4126,5736,1211,0x757a25a480000,0x1a7cbea93549; moment5736_1211) ?_
    refine stages_cons (pass! 1162,1609,361,0x2bf86f440000,0x2c2f29a34d; moment1609_361) (pass! 6051,8413,1776,0x172699d8580000,0x7a821d9dae58; moment8413_1776) ?_
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
end HighCore82209BankProof
