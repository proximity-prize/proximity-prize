import ProximityPrize.SubmissionLower.KoalaH2429BankResize
import ProximityPrize.SubmissionLower.KoalaH2430Moment333_74
import ProximityPrize.SubmissionLower.KoalaH2430Moment1704_359
import ProximityPrize.SubmissionLower.KoalaH2430Moment337_74
import ProximityPrize.SubmissionLower.KoalaH2430Moment2139_449
import ProximityPrize.SubmissionLower.KoalaH2430Moment452_102
import ProximityPrize.SubmissionLower.KoalaH2430Moment2240_473
import ProximityPrize.SubmissionLower.KoalaH2430Moment715_159
import ProximityPrize.SubmissionLower.KoalaH2430Moment4658_982
import ProximityPrize.SubmissionLower.KoalaH2430Moment1031_223
import ProximityPrize.SubmissionLower.KoalaH2430Moment6675_1411
-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, HighCore82258BankProof.lean.
import ProximityPrize.SubmissionLower.HighCore82258Moments5

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258BankProof

open P3_7_1 (BankOK checked)
open HighCore82258

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem terminal2430_ok : BankOK KoalaH2430Banks.terminal :=
  (pass! 4800,6675,1411,0xb9273b5380000,0x309c85fb6d6a; KoalaH2430Banks.moment6675_1411)

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2367 => exact (pass! 4600,6398,1353,0xa30a49bf40000,0x290bd5ec7938; moment6398_1353)

  | h2430 => exact terminal2430_ok
  | h2429 => exact KoalaH2429Banks.resize_ok terminal2430_ok _
  | h2429B => exact KoalaH2429TerminalB.terminal_ok

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss,BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf:BankOK s.free) (hm:BankOK s.moving) (ht:StageOK ss):StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩

private theorem stages2430_ok : StageOK KoalaH2430Banks.stages := by
  rw [KoalaH2430Banks.stages]
  refine stages_cons (pass! 70,97,21,0x28d4c0000,0x284e2c; moment97_21) (pass! 417,580,122,0x1f4b8940000,0xb758706b; moment580_122) ?_
  refine stages_cons (pass! 77,107,23,0x35da00000,0x3ae575; moment107_23) (pass! 436,606,128,0x23d8b880000,0xdb115372; moment606_128) ?_
  refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 523,727,154,0x3de60680000,0x1c5b77ce0; moment727_154) ?_
  refine stages_cons (pass! 93,129,28,0x5e72c0000,0x7bb5e0; moment129_28) (pass! 497,691,144,0x347eb240000,0x16dd8a416; moment691_144) ?_
  refine stages_cons (pass! 103,143,31,0x7fa800000,0xb978d4; moment143_31) (pass! 525,731,154,0x3e6d7fc0000,0x1cdc7da38; moment731_154) ?_
  refine stages_cons (pass! 111,154,33,0x9dd080000,0xf64733; moment154_33) (pass! 652,906,191,0x773dc800000,0x43fc612ca; moment906_191) ?_
  refine stages_cons (pass! 126,175,39,0xec9f00000,0x1a458a5; moment175_39) (pass! 695,966,204,0x90934f00000,0x57ee6dc45; moment966_204) ?_
  refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 865,1202,254,0x1166fe340000,0xd28832ce8; moment1202_254) ?_
  refine stages_cons (pass! 171,237,50,0x2316e80000,0x53b7f45; moment237_50) (pass! 1059,1473,310,0x1fd33c580000,0x1d8ad324e3; moment1473_310) ?_
  refine stages_cons (pass! 178,247,55,0x2932d00000,0x66c8fdf; moment247_55) (pass! 827,1150,242,0xf2bf9c80000,0xafe167953; moment1150_242) ?_
  refine stages_cons (pass! 240,333,74,0x6425e40000,0x1502259a; KoalaH2430Banks.moment333_74) (pass! 1224,1704,359,0x312e99700000,0x34e8dd2611; KoalaH2430Banks.moment1704_359) ?_
  refine stages_cons (pass! 215,299,66,0x47ec700000,0xd9f9f46; moment299_66) (pass! 1350,1878,396,0x41f8149c0000,0x4e1409a395; moment1878_396) ?_
  refine stages_cons (pass! 244,337,74,0x67e92c0000,0x15d422a2; KoalaH2430Banks.moment337_74) (pass! 1537,2139,449,0x6101d1080000,0x82dccd701e; KoalaH2430Banks.moment2139_449) ?_
  refine stages_cons (pass! 256,355,79,0x7978e00000,0x1b1f653e; moment355_79) (pass! 1467,2041,430,0x549403e80000,0x6ccf71d82e; moment2041_430) ?_
  refine stages_cons (pass! 326,452,102,0xfc78800000,0x47b11e70; KoalaH2430Banks.moment452_102) (pass! 1611,2240,473,0x701eae480000,0x9e16b78820; KoalaH2430Banks.moment2240_473) ?_
  refine stages_cons (pass! 340,471,104,0x1196c380000,0x53100efb; moment471_104) (pass! 2059,2864,605,0xea109ad80000,0x1a640ee22cd; moment2864_605) ?_
  refine stages_cons (pass! 420,584,129,0x212bb440000,0xc3b69b6e; moment584_129) (pass! 2720,3784,799,0x21b2df4c00000,0x5055cdfca34; moment3784_799) ?_
  refine stages_cons (pass! 517,715,159,0x3dcd1800000,0x1b8dfc3d0; KoalaH2430Banks.moment715_159) (pass! 3348,4658,982,0x3ec0352340000,0xb8275fdfb7e; KoalaH2430Banks.moment4658_982) ?_
  refine stages_cons (pass! 450,626,134,0x27d33980000,0xfbef358d; moment626_134) (pass! 2820,3926,832,0x25ad525a80000,0x5d58d7fc090; moment3926_832) ?_
  refine stages_cons (pass! 650,904,200,0x7aa2ccc0000,0x45f662bb3; moment904_200) (pass! 4200,5843,1234,0x7c020ca840000,0x1c86bbc42d5b; moment5843_1234) ?_
  refine stages_cons (pass! 743,1031,223,0xb3959800000,0x742d14dfc; KoalaH2430Banks.moment1031_223) (pass! 4765,6631,1396,0xb4aacea6c0000,0x2f3124f90909; moment6631_1396) ?_
  refine stages_cons (pass! 398,554,118,0x1b800f00000,0x9a361749; moment554_118) (pass! 2164,3012,632,0x10e708bd80000,0x201c0863f68; moment3012_632) ?_
  exact stages_nil

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine stages_cons (pass! 70,97,21,0x28d4c0000,0x284e2c; moment97_21) (pass! 417,580,122,0x1f4b8940000,0xb758706b; moment580_122) ?_
    refine stages_cons (pass! 77,107,23,0x35da00000,0x3ae575; moment107_23) (pass! 436,606,128,0x23d8b880000,0xdb115372; moment606_128) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 523,727,154,0x3de60680000,0x1c5b77ce0; moment727_154) ?_
    refine stages_cons (pass! 93,129,28,0x5e72c0000,0x7bb5e0; moment129_28) (pass! 497,691,144,0x347eb240000,0x16dd8a416; moment691_144) ?_
    refine stages_cons (pass! 103,143,31,0x7fa800000,0xb978d4; moment143_31) (pass! 525,731,154,0x3e6d7fc0000,0x1cdc7da38; moment731_154) ?_
    refine stages_cons (pass! 111,154,33,0x9dd080000,0xf64733; moment154_33) (pass! 652,906,191,0x773dc800000,0x43fc612ca; moment906_191) ?_
    refine stages_cons (pass! 126,175,39,0xec9f00000,0x1a458a5; moment175_39) (pass! 695,966,204,0x90934f00000,0x57ee6dc45; moment966_204) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 865,1202,254,0x1166fe340000,0xd28832ce8; moment1202_254) ?_
    refine stages_cons (pass! 171,237,50,0x2316e80000,0x53b7f45; moment237_50) (pass! 1059,1473,310,0x1fd33c580000,0x1d8ad324e3; moment1473_310) ?_
    refine stages_cons (pass! 178,247,55,0x2932d00000,0x66c8fdf; moment247_55) (pass! 827,1150,242,0xf2bf9c80000,0xafe167953; moment1150_242) ?_
    refine stages_cons (pass! 215,299,66,0x47ec700000,0xd9f9f46; moment299_66) (pass! 1350,1878,396,0x41f8149c0000,0x4e1409a395; moment1878_396) ?_
    refine stages_cons (pass! 250,347,77,0x71041c0000,0x18b7e486; moment347_77) (pass! 1360,1893,399,0x4373e8600000,0x509300a57a; moment1893_399) ?_
    refine stages_cons (pass! 230,318,70,0x575d000000,0x115d6f33; moment318_70) (pass! 1450,2018,424,0x5186864c0000,0x67c5a7c1f4; moment2018_424) ?_
    refine stages_cons (pass! 256,355,79,0x7978e00000,0x1b1f653e; moment355_79) (pass! 1467,2041,430,0x549403e80000,0x6ccf71d82e; moment2041_430) ?_
    refine stages_cons (pass! 340,471,106,0x11d7aac0000,0x544a4209; moment471_106) (pass! 1790,2489,526,0x99da4d600000,0xf10deb594c; moment2489_526) ?_
    refine stages_cons (pass! 340,471,104,0x1196c380000,0x53100efb; moment471_104) (pass! 2059,2864,605,0xea109ad80000,0x1a640ee22cd; moment2864_605) ?_
    refine stages_cons (pass! 420,584,129,0x212bb440000,0xc3b69b6e; moment584_129) (pass! 2720,3784,799,0x21b2df4c00000,0x5055cdfca34; moment3784_799) ?_
    refine stages_cons (pass! 574,794,177,0x54ac1b40000,0x29ef4219f; moment794_177) (pass! 3487,4851,1023,0x46e7550000000,0xd8a91833248; moment4851_1023) ?_
    refine stages_cons (pass! 450,626,134,0x27d33980000,0xfbef358d; moment626_134) (pass! 2820,3926,832,0x25ad525a80000,0x5d58d7fc090; moment3926_832) ?_
    refine stages_cons (pass! 650,904,200,0x7aa2ccc0000,0x45f662bb3; moment904_200) (pass! 4200,5843,1234,0x7c020ca840000,0x1c86bbc42d5b; moment5843_1234) ?_
    refine stages_cons (pass! 790,1096,237,0xd7b5b1c0000,0x9443175ae; moment1096_237) (pass! 4765,6631,1396,0xb4aacea6c0000,0x2f3124f90909; moment6631_1396) ?_
    refine stages_cons (pass! 398,554,118,0x1b800f00000,0x9a361749; moment554_118) (pass! 2164,3012,632,0x10e708bd80000,0x201c0863f68; moment3012_632) ?_
    exact stages_nil

  | h2430 => exact stages2430_ok
  | h2429 | h2429B =>
    exact KoalaH2429Banks.resize_stages_ok _ _ stages2430_ok

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s,hs,rfl | rfl⟩ | ⟨i,rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes,(terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

theorem interpolation_sources_for_crt : CRTSourceExists :=
  source_for_crt (fun b t ht => (listed_ok b t ht).nodes)
    (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources_for_crt
#print axioms interpolation_sources
end HighCore82258BankProof
