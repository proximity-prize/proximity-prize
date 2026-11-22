-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229BankProof.lean.
import ProximityPrize.SubmissionLower.Peer653High53FirstBandMoments

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653High53BankProof

open P3_7_1 (BankOK checked)
open Peer653High53

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2367 => exact (pass! 4625,6431,1364,0xa60d3e1440000,0x29ff0aaee26a; moment6431_1364)

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
end Peer653High53BankProof
