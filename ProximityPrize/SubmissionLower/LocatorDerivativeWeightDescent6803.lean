import ProximityPrize.SubmissionLower.LocatorDerivativeChain

/-!
# Exact cumulative-weight descent along the locator derivative chain

The promoted locator certificate only tightens the explicit `R`-degree of
`dR j F`.  The three cumulative flags used by the factor-sensitive ledger all
give weight one to `R`, so the same derivative step also lowers the middle and
total weights.  This file records that loss without any geometric or
counting hypothesis.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeWeightDescent6803

open RCN095 RCN130 RCN156 RCN234 RCN313 LocatorDerivativeChain
  LocatorFactorAggregate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K : Type} [Field K]

/-- Iterating `pderiv R` spends exactly one unit from any weight budget which
assigns unit weight to `R`.  The statement is phrased with an arbitrary
ambient bound so it can be used both for a single factor and for an aggregate
factor product. -/
theorem dR_wt_le_sub (weights : Fin 4 → ℕ)
    (hweight : weights (2 : Fin 4) = 1)
    (F : MvPolynomial (Fin 4) K) (j A : ℕ)
    (hF : wt weights F ≤ A) :
    wt weights (dR j F) ≤ A - j := by
  induction j with
  | zero => simpa using hF
  | succ j ih =>
      rw [dR_succ]
      have hstep := wt_pderiv_le weights (dR j F) (2 : Fin 4)
        (A - j) ih
      rw [hweight] at hstep
      simpa [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hstep

/-- The scaled form: one `R` derivative spends the actual `R` weight. -/
theorem dR_wt_le_sub_mul (weights : Fin 4 → ℕ) (r : ℕ)
    (hweight : weights (2 : Fin 4) = r)
    (F : MvPolynomial (Fin 4) K) (j A : ℕ)
    (hF : wt weights F ≤ A) :
    wt weights (dR j F) ≤ A - j * r := by
  induction j with
  | zero => simpa using hF
  | succ j ih =>
      rw [dR_succ]
      have hstep := wt_pderiv_le weights (dR j F) (2 : Fin 4)
        (A - j * r) ih
      rw [hweight] at hstep
      simpa [Nat.sub_sub, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hstep

/-- The slope component of the cumulative locator flag drops by the full
derivative order. -/
theorem dR_slopeWeight_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    wt residualSWeights (dR j F) ≤
      wt residualSWeights F - j := by
  exact dR_wt_le_sub residualSWeights rfl F j
    (wt residualSWeights F) le_rfl

/-- The middle (`Y+R`) locator weight drops by the full derivative order. -/
theorem dR_middleWeight_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    wt residualYSWeights (dR j F) ≤
      wt residualYSWeights F - j := by
  exact dR_wt_le_sub residualYSWeights rfl F j
    (wt residualYSWeights F) le_rfl

/-- The total (`Y+R+Z`) locator weight drops by the full derivative order. -/
theorem dR_totalWeight_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    wt residualTotalWeights (dR j F) ≤
      wt residualTotalWeights F - j := by
  exact dR_wt_le_sub residualTotalWeights rfl F j
    (wt residualTotalWeights F) le_rfl

/-- Cumulative form consumed by the factor-sensitive chain ledger. -/
theorem dR_cumulative_weights_le_sub
    (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    (originalCumulativeFlag (dR j F)).all ≤
        (originalCumulativeFlag F).all - j ∧
      middle (originalCumulativeFlag (dR j F)) ≤
        middle (originalCumulativeFlag F) - j ∧
      total (originalCumulativeFlag (dR j F)) ≤
        total (originalCumulativeFlag F) - j := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(originalCumulativeFlag_cumulative (dR j F)).1,
      (originalCumulativeFlag_cumulative F).1]
    exact dR_slopeWeight_le_sub F j
  · change
      (originalCumulativeFlag (dR j F)).yz +
          (originalCumulativeFlag (dR j F)).all ≤
        (originalCumulativeFlag F).yz + (originalCumulativeFlag F).all - j
    rw [(originalCumulativeFlag_cumulative (dR j F)).2.1,
      (originalCumulativeFlag_cumulative F).2.1]
    exact dR_middleWeight_le_sub F j
  · change
      (originalCumulativeFlag (dR j F)).zOnly +
            (originalCumulativeFlag (dR j F)).yz +
          (originalCumulativeFlag (dR j F)).all ≤
        (originalCumulativeFlag F).zOnly + (originalCumulativeFlag F).yz +
          (originalCumulativeFlag F).all - j
    rw [(originalCumulativeFlag_cumulative (dR j F)).2.2,
      (originalCumulativeFlag_cumulative F).2.2]
    exact dR_totalWeight_le_sub F j

end

end ProximityPrize.SubmissionLower.LocatorDerivativeWeightDescent6803
