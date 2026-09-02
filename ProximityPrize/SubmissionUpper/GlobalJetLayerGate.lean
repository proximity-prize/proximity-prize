/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Global derivative-layer gates for an upper attack

The lower score-68 rectangular work applies the entire `R`-derivative ladder
to one fixed global owner.  For `R` degree at most 27, every selected seed is
either terminal (the terminal derivative is `R`-free) or belongs to one of 27
first-surviving regular layers.

This upper-only module combines that abstract cover with the complete
conditional terminal `R`-free caps at the first improving and square-jet
endpoints.  It proves the exact minimum size forced in one regular layer by a
winning challenge image.  It does not construct a global owner or prove the
terminal/regular classification for an arbitrary upper family.
-/

namespace ProximityPrize.SubmissionUpper.GlobalJetLayerGate

open scoped BigOperators

def challengeThreshold : ℕ := 274980728111395088
def regularLayerCount : ℕ := 27

/-- Complete conditional terminal `R`-free cap at agreement 139776. -/
def strictTerminalCap : ℕ := 4466279432592298

/-- Minimum size forced in one of 27 regular layers if the terminal branch is
bounded by `strictTerminalCap`. -/
def strictRegularLayerGate : ℕ := 10019053654770474

/-- Complete conditional terminal `R`-free cap at agreement 140287. -/
def squareJetTerminalCap : ℕ := 4219607880466124

/-- Corresponding minimum regular-layer size at the square-jet endpoint. -/
def squareJetRegularLayerGate : ℕ := 10028189638182555

theorem endpoint_arithmetic_receipt :
    strictTerminalCap + regularLayerCount * (strictRegularLayerGate - 1) <
        challengeThreshold ∧
      challengeThreshold ≤
        strictTerminalCap + regularLayerCount * strictRegularLayerGate ∧
      squareJetTerminalCap +
          regularLayerCount * (squareJetRegularLayerGate - 1) <
        challengeThreshold ∧
      challengeThreshold ≤
        squareJetTerminalCap +
          regularLayerCount * squareJetRegularLayerGate := by
  norm_num [strictTerminalCap, regularLayerCount, strictRegularLayerGate,
    challengeThreshold, squareJetTerminalCap, squareJetRegularLayerGate]

/-- A threshold-sized family covered by the terminal branch and 27 regular
layers forces one regular layer to contain at least
`10,019,053,654,770,474` challenges. -/
theorem exists_large_strict_regular_layer
    (card terminal : ℕ) (regular : Fin 27 → ℕ)
    (hwinning : challengeThreshold ≤ card)
    (hterminal : terminal ≤ strictTerminalCap)
    (hcover : card ≤ terminal + ∑ i, regular i) :
    ∃ i, strictRegularLayerGate ≤ regular i := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : ∑ i, regular i ≤ 27 * (strictRegularLayerGate - 1) := by
    calc
      ∑ i, regular i ≤ ∑ _i : Fin 27, (strictRegularLayerGate - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hsmall := hnone i
        omega
      _ = 27 * (strictRegularLayerGate - 1) := by simp
  norm_num [challengeThreshold, strictTerminalCap,
    strictRegularLayerGate] at hwinning hterminal hcover hsum ⊢
  omega

/-- Sharper layer gate under the square-jet terminal cap. -/
theorem exists_large_square_jet_regular_layer
    (card terminal : ℕ) (regular : Fin 27 → ℕ)
    (hwinning : challengeThreshold ≤ card)
    (hterminal : terminal ≤ squareJetTerminalCap)
    (hcover : card ≤ terminal + ∑ i, regular i) :
    ∃ i, squareJetRegularLayerGate ≤ regular i := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : ∑ i, regular i ≤ 27 * (squareJetRegularLayerGate - 1) := by
    calc
      ∑ i, regular i ≤ ∑ _i : Fin 27, (squareJetRegularLayerGate - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hsmall := hnone i
        omega
      _ = 27 * (squareJetRegularLayerGate - 1) := by simp
  norm_num [challengeThreshold, squareJetTerminalCap,
    squareJetRegularLayerGate] at hwinning hterminal hcover hsum ⊢
  omega

end ProximityPrize.SubmissionUpper.GlobalJetLayerGate

#print axioms ProximityPrize.SubmissionUpper.GlobalJetLayerGate.exists_large_strict_regular_layer
#print axioms ProximityPrize.SubmissionUpper.GlobalJetLayerGate.exists_large_square_jet_regular_layer
