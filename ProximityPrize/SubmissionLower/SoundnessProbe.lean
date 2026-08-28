/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LineDecoding
import ProximityPrize.SubmissionLower.JohnsonFamily

/-!
# Conditional soundness probe just beyond unique decoding

This file does not change the benchmark candidate.  It isolates the two code-theoretic
obligations needed to use line decoding at a larger radius: a concrete line-decodability
statement for the IRS code and a list-size bound for its two-row interleaving.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem CodingTheory
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

noncomputable abbrev ProbeSquaredCode : Set (IRSProfile.Index →
    Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem probeSquaredCode_minDistance :
    Code.minDist ProbeSquaredCode = 131073 := by
  calc
    Code.minDist ProbeSquaredCode =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

/-- The exact bridge from the new line-decoding theorem and a list-size estimate to the
protected extractor-error expression. -/
theorem certifiedGammaError_le_of_line_and_list
    (δ : ℝ≥0) (a listBudget : Nat)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hline : IsLineDecodable (F := IRSProfile.Field)
      (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field))
      δ a (Fintype.card IRSProfile.Index + 1))
    (hlist : (Code.Lambda ProbeSquaredCode (δ : ℝ)).toNat ≤ listBudget)
    (hbudget : ((a + listBudget : Nat) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) ≤
      (reductionTarget : ENNReal)) :
    certifiedGammaError IRSProfile.code δ ≤ reductionTarget := by
  have hmca := IsLineDecodable.mcaError_le IRSProfile.code δ a hδpos hδlt hline
  have hlist' :
      ((Code.Lambda ProbeSquaredCode (δ : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (listBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hlist) _
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (δ : ℝ) +
          ((Code.Lambda ProbeSquaredCode (δ : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
        (a : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
          (listBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add hmca hlist'
    _ = ((a + listBudget : Nat) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (reductionTarget : ENNReal) := hbudget

/-- A convenient, deliberately loose split of the available field-size budget. -/
theorem two_pow_56_each_clears_reduction_budget :
    (((2 ^ 56 + 2 ^ 56 : Nat) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal)) ≤
      (reductionTarget : ENNReal) := by
  have hne :
      (((2 ^ 56 + 2 ^ 56 : Nat) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal)) ≠ ⊤ := by
    apply ENNReal.div_ne_top <;> simp
  apply (ENNReal.toReal_le_toReal hne (by simp)).mp
  rw [ENNReal.toReal_div]
  norm_num [reductionTarget, ProximityGap.prizeThreshold,
    IRSProfile.Field, KoalaBear.Ext6, div_le_iff₀]

/-- A rational radius which is just large enough for a `53.13`-bit score and remains in
the disagreement-count cell with floor value `65541`. -/
noncomputable def nextRadius : ℝ≥0 :=
  claimedRadius 3277077 13107200

theorem nextRadius_admissible :
    nextRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [nextRadius, claimedRadius, IRSProfile.minRelativeDistance]

theorem nextRadius_floor_eq :
    Nat.floor (nextRadius * Fintype.card IRSProfile.Index) = 65541 := by
  norm_num [nextRadius, claimedRadius, IRSProfile.Index]

/-- The generic Johnson bound easily clears the list-side budget at the probe radius. -/
theorem nextRadius_listBudget :
    (Code.Lambda ProbeSquaredCode (nextRadius : ℝ)).toNat ≤ 2 ^ 56 := by
  let η : ℝ := 1 - Real.sqrt (1 / 2 : ℝ) - nextRadius
  have hsqrt : Real.sqrt (1 / 2 : ℝ) < 71 / 100 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hs0 := Real.sqrt_nonneg (1 / 2 : ℝ)
    nlinarith
  have hη : 1 / 100 < η := by
    dsimp only [η]
    rw [show (nextRadius : ℝ) = (3277077 : ℝ) / 13107200 by
      norm_num [nextRadius, claimedRadius]]
    norm_num at ⊢ hsqrt
    linarith
  have hηpos : 0 < η := (by norm_num : (0 : ℝ) < 1 / 100).trans hη
  have hJohnson := mds_johnson_lambda_le_of_rate_distance
    ProbeSquaredCode (1 / 2 : ℝ) η (by norm_num) (by norm_num) hηpos
    (by
      rw [probeSquaredCode_minDistance]
      norm_num [IRSProfile.Index])
  have hradius : 1 - Real.sqrt (1 / 2 : ℝ) - η = (nextRadius : ℝ) := by
    dsimp only [η]
    ring
  rw [hradius] at hJohnson
  have hreal : 1 / (2 * η * (1 / 2 : ℝ)) ≤ 100 := by
    rw [show 2 * η * (1 / 2 : ℝ) = η by ring]
    exact (div_le_iff₀ hηpos).2 (by nlinarith)
  have hLambdaENN :
      (Code.Lambda ProbeSquaredCode (nextRadius : ℝ) : ENNReal) ≤
        (2 ^ 56 : Nat) := by
    refine hJohnson.trans ((ENNReal.ofReal_le_ofReal hreal).trans ?_)
    norm_num
  have hLambdaENat :
      Code.Lambda ProbeSquaredCode (nextRadius : ℝ) ≤
        ((2 ^ 56 : Nat) : ℕ∞) := by
    exact_mod_cast hLambdaENN
  exact ENat.toNat_le_of_le_coe hLambdaENat

/-- At the probe radius, these are the two remaining code-theoretic obligations. -/
theorem nextRadius_reduction_of_obligations
    (hline : IsLineDecodable (F := IRSProfile.Field)
      (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field))
      nextRadius (2 ^ 56) (Fintype.card IRSProfile.Index + 1))
    :
    certifiedGammaError IRSProfile.code nextRadius ≤ reductionTarget := by
  apply certifiedGammaError_le_of_line_and_list nextRadius (2 ^ 56) (2 ^ 56)
  · exact nextRadius_admissible.1
  · exact nextRadius_admissible.2.trans (by
      norm_num [IRSProfile.minRelativeDistance])
  · exact hline
  · exact nextRadius_listBudget
  · exact two_pow_56_each_clears_reduction_budget

end ProximityPrize.SubmissionLower
