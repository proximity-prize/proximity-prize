/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The middle band uses the public Koala peer geometry from Proximity Prize
submission 653, source commit d3db79e374b16bebd9780b96f1c1fe0c156679bc,
and the native joint prefix ledger.
-/
import ProximityPrize.SubmissionLower.FrontIntermediateProtocol
import ProximityPrize.SubmissionLower.Low53At2389GeoCount
import ProximityPrize.SubmissionLower.HighCore82268Finish
import ProximityPrize.SubmissionLower.OrdinaryTransfer

set_option Elab.async false
set_option autoImplicit false

namespace Front53Direct

open Finset ProximityPrize.Benchmark
open P1 (I K Words)

def PeerBandCount : Prop :=
  ∀ {u : Words} {deleted : Finset I} (M : P1.ModelAt 33463 u deleted)
    {Γ : Finset K} (F : P1.FamilyAt 179896 M Γ),
    (2390 : ℤ) ≤ M.overhead → M.overhead ≤ 2526 →
    Γ.card ≤ FrontIntermediate.coreBudget

theorem core_count (rank : Low53At2389Primary.LocalRankBound) (middle : PeerBandCount) :
    FrontIntermediate.CoreCount (Cell82Intermediate.agreement .s53)
      FrontIntermediate.coreBudget := by
  intro u deleted M Γ F hlo hhi
  by_cases hl : M.overhead ≤ 2389
  · exact Low53At2389Geo.ordinary_count rank M F hlo hl
  by_cases hm : M.overhead ≤ 2526
  · exact middle M F (by omega) hm
  let hc : 33463 ≤ HighCore82268.heightCap := by decide
  let M' := OrdinaryTransfer.enlarge M hc
  have F' : P1.FamilyAt HighCore82268.agreement M' Γ :=
    OrdinaryTransfer.family M F hc (by decide)
  have hhlo : (2527 : ℤ) ≤ M'.overhead := by
    change (2527 : ℤ) ≤ M.overhead
    omega
  have hhhi : M'.overhead ≤ (HighCore82268.heightCap : ℤ) := by
    exact hhi
  exact (HighCore82268.ordinary_high_from2527 M' F' hhlo hhhi).trans (by decide)

theorem protocol (rank : Low53At2389Primary.LocalRankBound) (middle : PeerBandCount) :
    ProtocolClaim 6953 2893879419934332965 9223372036854743289 :=
  FrontIntermediate.of_core_count .s53 (core_count rank middle)

#print axioms protocol

end Front53Direct
