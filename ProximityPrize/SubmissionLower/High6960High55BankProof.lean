import ProximityPrize.SubmissionLower.High6960High55Source
import ProximityPrize.SubmissionLower.High6960High55SmallMoments

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High6960High55BankProof

open P3_7_1 (BankOK checked)
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open High6960High55

set_option maxHeartbeats 4000000
open private r1A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r2A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r3A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r4A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r5A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r6A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r7A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r8A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r10A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r12A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r14A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r16A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r17A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r19A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r20A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r23A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r24A from ProximityPrize.SubmissionLower.High6960High55SmallMoments
open private r25A from ProximityPrize.SubmissionLower.High6960High55SmallMoments

private theorem moment15_3:momentEstimate 15 3=2194:=r1A

private theorem moment28_4:momentEstimate 28 4=17031:=r2A

private theorem moment29_6:momentEstimate 29 6=24733:=r3A

private theorem moment47_10:momentEstimate 47 10=156979:=r4A

private theorem moment53_9:momentEstimate 53 9=211909:=r5A

private theorem moment75_16:momentEstimate 75 16=957077:=r6A

private theorem moment89_15:momentEstimate 89 15=0x17e10a:=r7A

private theorem moment101_22:momentEstimate 101 22=0x2f6f2a:=r8A

private theorem moment108_24:momentEstimate 108 24=0x3e9e8f:=r10A

private theorem moment119_26:momentEstimate 119 26=0x5a8245:=r12A

private theorem moment130_29:momentEstimate 130 29=0x822d2c:=r14A

private theorem moment141_24:momentEstimate 141 24=0x91e8ba:=r16A

private theorem moment141_31:momentEstimate 141 31=0xb15384:=r17A

private theorem moment149_33:momentEstimate 149 33=0xdda994:=r19A

private theorem moment150_33:momentEstimate 150 33=0xe271e9:=r20A

private theorem moment173_32:momentEstimate 173 32=0x15c66e5:=r23A

private theorem moment197_43:momentEstimate 197 43=0x294fec6:=r24A

private theorem moment226_50:momentEstimate 226 50=0x47e88b5:=r25A

private theorem moment294_65 : momentEstimate 294 65 = 0xcc1a54f := by
  exact moment_from_blocks [⟨220,0x9b91fd2⟩, ⟨139,0x308857d⟩]
    ⟨(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment306_68 : momentEstimate 306 68 = 0xf032b8c := by
  exact moment_from_blocks [⟨220,0xadb2093⟩, ⟨154,0x4280af9⟩]
    ⟨(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment341_75 : momentEstimate 341 75 = 0x16e7d3b2 := by
  exact moment_from_blocks [⟨220,0xe2cbd21⟩, ⟨196,0x8bb1691⟩]
    ⟨(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment362_82 : momentEstimate 362 82 = 0x1db6eefa := by
  exact moment_from_blocks [⟨220,0x10953e8c⟩, ⟨220,0xd219e1d⟩, ⟨4,4689⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment386_85 : momentEstimate 386 85 = 0x25892b87 := by
  exact moment_from_blocks [⟨220,0x12e20d53⟩, ⟨220,0x1296e6bc⟩, ⟨31,0x103778⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment480_101 : momentEstimate 480 101 = 0x564a51c0 := by
  exact moment_from_blocks [⟨220,0x1cff6c77⟩, ⟨220,0x335db15d⟩, ⟨141,0x5ed33ec⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment489_103 : momentEstimate 489 103 = 0x5cfd94a5 := by
  exact moment_from_blocks [⟨220,0x1e1184e2⟩, ⟨220,0x377640d9⟩, ⟨152,0x775ceea⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment535_112 : momentEstimate 535 112 = 0x84679137 := by
  exact moment_from_blocks [⟨220,0x2377d012⟩, ⟨220,0x4d9e6502⟩, ⟨207,0x13515c23⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment572_120 : momentEstimate 572 120 = 0xad1e0c80 := by
  exact moment_from_blocks [⟨220,0x27f8a832⟩, ⟨220,0x61ae3614⟩, ⟨220,0x235c906a⟩, ⟨32,0x1a9dd0⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment609_128 : momentEstimate 609 128 = 0xde912dc3 := by
  exact moment_from_blocks [⟨220,0x2c7f734a⟩, ⟨220,0x772d7efa⟩, ⟨220,0x3983871d⟩, ⟨77,0x160b462⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment726_153 : momentEstimate 726 153 = 0x1c16ef1c7 := by
  exact moment_from_blocks [⟨220,0x3aabb454⟩, ⟨220,0xc33b47fa⟩, ⟨220,0xa282e542⟩, ⟨219,0x21051037⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment740_167 : momentEstimate 740 167 = 0x1ff6e1863 := by
  exact moment_from_blocks [⟨220,0x3cf21eda⟩, ⟨220,0xd67bc218⟩, ⟨220,0xbcc3ee24⟩, ⟨220,0x2f26e723⟩, ⟨27,0x15622a⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment792_167 : momentEstimate 792 167 = 0x27c2e15db := by
  exact moment_from_blocks [⟨220,0x4271d23a⟩, ⟨220,0xf2c75298⟩, ⟨220,0xf0b537ce⟩, ⟨220,0x544aa0d7⟩, ⟨79,0x1f51864⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment883_197 : momentEstimate 883 197 = 0x401d0f0c6 := by
  exact moment_from_blocks [⟨220,0x4cfcc39b⟩, ⟨220,0x142ef2dae⟩, ⟨220,0x17ce952be⟩, ⟨220,0xd4e276cc⟩, ⟨200,0x201935f3⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment968_204 : momentEstimate 968 204 = 0x5884788a7 := by
  exact moment_from_blocks [⟨220,0x5626d855⟩, ⟨220,0x17d5abee0⟩, ⟨220,0x1edb84f40⟩, ⟨220,0x15f411d92⟩, ⟨220,0x65f4a3ac⟩, ⟨72,0x1d7e0f4⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment1072_239:momentEstimate 1072 239=0x8af950b98:=P1_7_1_3_3.moment1072_239

private theorem moment1183_249:momentEstimate 1183 249=0xc4f2a7606:=P1_7_1_3_3.moment1183_249

private theorem moment1324_279:momentEstimate 1324 279=0x1350bb1fb5:=P1_7_1_3_3.moment1324_279

private theorem moment1443_329:momentEstimate 1443 329=0x1cf53a5560:=P1_7_1_3_3.moment1443_329

private theorem moment1550_329:momentEstimate 1550 329=0x2473d5ffe4:=P1_7_1_3_3.moment1550_329

private theorem moment1696_357:momentEstimate 1696 357=0x33e3754396:=P1_7_1_3_3.moment1696_357

private theorem moment1725_359:momentEstimate 1725 359=0x370899d961:=P1_7_1_3_3.moment1725_359

private theorem moment2034_430 : momentEstimate 2034 430 = 0x6b9d823520 := by
  exact moment_from_blocks [⟨220,0xc87bf9c1⟩, ⟨220,0x4e3f4d3f4⟩, ⟨220,0xae80a0832⟩, ⟨220,0xf6b22dc22⟩, ⟨220,0x11cb25bb92⟩, ⟨220,0x120812a682⟩, ⟨220,0x1021e99cf2⟩, ⟨220,0xc32470568⟩, ⟨220,0x7738b7944⟩, ⟨220,0x3514df015⟩, ⟨220,0xb0b10df9⟩, ⟨44,0xf10757⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment3131_661 : momentEstimate 3131 661 = 0x25ab1ba8825 := by
  exact moment_from_blocks [⟨220,0x13e1c3cbd⟩, ⟨220,0x814fefd91⟩, ⟨220,0x1439c24285⟩, ⟨220,0x2318e1a2fe⟩, ⟨220,0x2fca5f778e⟩, ⟨220,0x39338f9f1e⟩, ⟨220,0x3f547219ae⟩, ⟨220,0x422d06e73e⟩, ⟨220,0x41bd4e07ce⟩, ⟨220,0x3e05477b5e⟩, ⟨220,0x3704f341ee⟩, ⟨220,0x2ced7aaa31⟩, ⟨220,0x218df32002⟩, ⟨220,0x1692e1b9a9⟩, ⟨220,0xcf2dfed74⟩, ⟨220,0x59295cf26⟩, ⟨220,0x12ee8a16e⟩, ⟨52,0x25ca9be⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

private theorem moment4830_1019:momentEstimate 4830 1019=0xd5013df2ef9:=P1_7_1_3_5.moment4830

private theorem moment5798_1223:momentEstimate 5798 1223=0x1ba1a89b2ba1:=P1_7_1_3_5.moment5798

private theorem moment7630_1607:momentEstimate 7630 1607=0x52bdbe618ec3:=P1_7_1_3_5.moment7630

private theorem moment10506_2218:momentEstimate 10506 2218=0x129e297a45c0c:=P1_7_1_3_6.moment10506

private theorem moment115_25:momentEstimate 115 25=0x4ed4ac:=rfl

private theorem moment362_81 : momentEstimate 362 81 = 0x1d6fb003 := by
  exact moment_from_blocks [⟨220,0x1079a22e⟩, ⟨220,0xcf603f5⟩, ⟨3,2528⟩]
    ⟨(by decide +kernel),(by decide +kernel),(by decide +kernel),trivial⟩
    rfl rfl

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2570 => exact (pass! 7550,10506,2218,0x2cfea55aa80000,0x129e297a45c0c; moment10506_2218)
  | h8100 => exact (pass! 124,173,32,0xc4fd80000,0x15c66e5; moment173_32)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss,BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf:BankOK s.free) (hm:BankOK s.moving) (ht:StageOK ss):StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2570 =>
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
  | h8100 =>
    rw [stages]
    refine stages_cons (pass! 11,15,3,0x3500000,2194; moment15_3) (pass! 20,28,4,0xdc00000,17031; moment28_4) ?_
    refine stages_cons (pass! 21,29,6,0x13cc0000,24733; moment29_6) (pass! 38,53,9,0x5d840000,211909; moment53_9) ?_
    refine stages_cons (pass! 34,47,10,0x4f100000,156979; moment47_10) (pass! 64,89,15,0x1a3600000,0x17e10a; moment89_15) ?_
    refine stages_cons (pass! 54,75,16,0x12f140000,957077; moment75_16) (pass! 101,141,24,0x64f3c0000,0x91e8ba; moment141_24) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s,hs,rfl | rfl⟩ | ⟨i,rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes,(terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources
end High6960High55BankProof
