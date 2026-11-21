import ProximityPrize.SubmissionLower.HighCore82219Source
import ProximityPrize.SubmissionLower.HighCore82219Moments12

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
  | h2405 => exact (pass! 7052,9807,2078,0x24c0a185540000,0xe2d5b7791e37; moment9807_2078)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2405 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 353,491,103,0x12fc4600000,0x5e3742a9; moment491_103) ?_
    refine stages_cons (pass! 60,83,18,0x19fec0000,0x15f0f2; moment83_18) (pass! 405,563,118,0x1c9714c0000,0xa26535f3; moment563_118) ?_
    refine stages_cons (pass! 109,151,33,0x979280000,0xe74c1b; moment151_33) (pass! 445,619,130,0x25f62dc0000,0xed5a05de; moment619_130) ?_
    refine stages_cons (pass! 122,169,38,0xd80c80000,0x170ad54; moment169_38) (pass! 473,659,138,0x2d836e40000,0x12ff82db2; moment659_138) ?_
    refine stages_cons (pass! 131,181,40,0x106e580000,0x1dd3cf8; moment181_40) (pass! 558,775,163,0x4aad7380000,0x246465872; moment775_163) ?_
    refine stages_cons (pass! 140,194,42,0x13bfdc0000,0x26a2eee; moment194_42) (pass! 653,908,191,0x77a65000000,0x447811faa; moment908_191) ?_
    refine stages_cons (pass! 179,248,55,0x29b7600000,0x681fcb3; moment248_55) (pass! 859,1195,253,0x111524d80000,0xcdfbb5b3b; moment1195_253) ?_
    refine stages_cons (pass! 193,267,58,0x3355540000,0x895de88; moment267_58) (pass! 1043,1451,305,0x1e61e4680000,0x1bcaea101e; moment1451_305) ?_
    refine stages_cons (pass! 362,502,114,0x15ae1900000,0x6d68a9c9; moment502_114) (pass! 1225,1703,357,0x310fd3780000,0x349473cb5b; moment1703_357) ?_
    refine stages_cons (pass! 210,291,64,0x42b1ac0000,0xc32b568; moment291_64) (pass! 1318,1839,385,0x3d329b940000,0x4765896c69; moment1839_385) ?_
    refine stages_cons (pass! 295,409,90,0xb7d8100000,0x2f3b1229; moment409_90) (pass! 1516,2105,443,0x5d1c55480000,0x7afe40f467; moment2105_443) ?_
    refine stages_cons (pass! 402,559,122,0x1cd6b900000,0xa2dfd458; moment559_122) (pass! 2123,2950,628,0x101e034e80000,0x1de23726e9e; moment2950_628) ?_
    refine stages_cons (pass! 377,523,114,0x17bd5e40000,0x7cce7b05; moment523_114) (pass! 2155,2994,634,0x10c9546a80000,0x1f9316168cb; moment2994_634) ?_
    refine stages_cons (pass! 500,692,155,0x3841b080000,0x185234383; moment692_155) (pass! 2696,3749,788,0x20b0925680000,0x4d21177bab1; moment3749_788) ?_
    refine stages_cons (pass! 526,731,158,0x3fecfe00000,0x1d7121286; moment731_158) (pass! 2811,3918,819,0x24f5ff3100000,0x5b99db6de2b; moment3918_819) ?_
    refine stages_cons (pass! 425,590,130,0x22423840000,0xcb755a0e; moment590_130) (pass! 2032,2827,594,0xe01986d40000,0x18f3217cfe1; moment2827_594) ?_
    refine stages_cons (pass! 806,1116,251,0xeba01480000,0xa44b9ecd3; moment1116_251) (pass! 4291,5969,1261,0x844328b580000,0x1f12fe9a79ee; moment5969_1261) ?_
    refine stages_cons (pass! 80,111,24,0x3c7300000,0x4451ef; moment111_24) (pass! 380,530,100,0x15dc6d00000,0x7597b06c; moment530_100) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 547,764,141,0x3fe66d80000,0x1f060dc24; moment764_141) ?_
    refine stages_cons (pass! 91,126,27,0x57a300000,0x6fafa5; moment126_27) (pass! 1081,1507,264,0x1d679b940000,0x1bfe368baa; moment1507_264) ?_
    refine stages_cons (pass! 97,134,29,0x6a6580000,0x8f605a; moment134_29) (pass! 664,925,200,0x809ed600000,0x4b52e2da2; moment925_200) ?_
    refine stages_cons (pass! 111,153,34,0xa15400000,0xf6b69e; moment153_34) (pass! 494,688,140,0x32b0a2c0000,0x160efc81a; moment688_140) ?_
    refine stages_cons (pass! 129,179,39,0xf95600000,0x1c3d3dd; moment179_39) (pass! 701,976,192,0x8cad28c0000,0x56ac98d52; moment976_192) ?_
    refine stages_cons (pass! 161,223,49,0x1e3a480000,0x43d826b; moment223_49) (pass! 996,1388,254,0x17ce40840000,0x14de8d1a33; moment1388_254) ?_
    refine stages_cons (pass! 168,233,50,0x21bc440000,0x4f48465; moment233_50) (pass! 1122,1566,343,0x271c0f900000,0x26eb47ca19; moment1566_343) ?_
    refine stages_cons (pass! 190,263,59,0x3235480000,0x849a735; moment263_59) (pass! 1811,2518,553,0xa40e21480000,0x1042a2fc6be; moment2518_553) ?_
    refine stages_cons (pass! 249,346,77,0x7002580000,0x187d9080; moment346_77) (pass! 2394,3335,706,0x170d016500000,0x309550b3c97; moment3335_706) ?_
    refine stages_cons (pass! 253,351,80,0x776e8c0000,0x1a683d4b; moment351_80) (pass! 1126,1572,307,0x243638180000,0x241fd7a6b1; moment1572_307) ?_
    refine stages_cons (pass! 266,369,82,0x8812100000,0x1f9950b6; moment369_82) (pass! 1022,1428,311,0x1d7761500000,0x1ace076bd3; moment1428_311) ?_
    refine stages_cons (pass! 316,439,98,0xe4864c0000,0x3f4c6dc0; moment439_98) (pass! 2509,3505,762,0x1b224cb7c0000,0x3c82694be91; moment3505_762) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s, hs, rfl | rfl⟩ | ⟨i, rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes, (terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources
end HighCore82219BankProof
