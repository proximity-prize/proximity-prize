import ProximityPrize.SubmissionLower.LocatorGroupedNonRegularAssembly6803
import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeArithmetic6803
import ProximityPrize.SubmissionLower.LocatorFourPhaseCoarseGroupedLedger6803
import ProximityPrize.SubmissionLower.LocatorRetainedQuotient6803

/-!
# Unscaled cardinality adapters for grouped derivative chains

The grouped numerator is an ordinary adjacent-pair numerator followed by one
proper-escape dot product already multiplied by the agreement gap.  Thus the
escape dot is added only after division; it is not a separate seed set.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedNonRegularCardinality6803

open scoped Classical BigOperators
open RCN095 RCN223 RCN260 RCN294 RCN318
open LocatorAggregateTerminalProduct6803
  LocatorPositiveFactorGroupedAggregate6803
  LocatorGroupedDerivativeUniformCaps6803
  LocatorGroupedNonRegularAssembly6803
  LocatorGroupedDerivativeArithmetic6803
  LocatorFourPhaseCoarseGroupedLedger6803
  LocatorRetainedQuotient6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- The unequal-parameter stage comparing a first derivative in the reduced
box to its original polynomial in the cumulative box. -/
def adjacentGroupedStage (n w a yCap sCap lCap : ℕ) : UnequalParameters :=
  ⟨n, w, a, yCap - 1, sCap - 1, lCap - 1, yCap, sCap, lCap⟩

/-- The one extra proper-escape charge already present in the grouped
incidence numerator. -/
def groupedEscapeDot (yCap sCap lCap : ℕ) : ℕ :=
  ∑ j, activeEscapeSurfaceCap yCap sCap lCap j *
    positiveDerivativeMixedBudget yCap sCap lCap j

theorem groupedDerivativeNumerator_le_adjacent
    (n w a yCap sCap lCap : ℕ) :
    groupedDerivativeNumerator n w a (n - a) yCap sCap lCap ≤
      (adjacentGroupedStage n w a yCap sCap lCap).regularNumerator +
        (adjacentGroupedStage n w a yCap sCap lCap).gap *
          groupedEscapeDot yCap sCap lCap := by
  let P := adjacentGroupedStage n w a yCap sCap lCap
  have hdot :
      (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
        positiveDerivativeMixedBudget yCap sCap lCap j) ≤
      dot P.agreement P.mixedCost := by
    calc
      (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
          positiveDerivativeMixedBudget yCap sCap lCap j) =
          dot P.leftAgreement P.mixedCost := by
            simp [P, adjacentGroupedStage, activeCarrierAgreementCap,
              positiveDerivativeMixedBudget, UnequalParameters.leftAgreement,
              UnequalParameters.mixedCost, dot, Fin.sum_univ_succ]
            ring
      _ ≤ dot P.agreement P.mixedCost := by
        apply dot_mono_left
        exact ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _⟩
  have hmixedZ :
      positiveDerivativeMixedBudget yCap sCap lCap 2 = P.mixedCost.z := by
    simp [P, adjacentGroupedStage, positiveDerivativeMixedBudget,
      UnequalParameters.mixedCost]
    ring
  have hcore :
      (n - w) *
          (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
            positiveDerivativeMixedBudget yCap sCap lCap j) +
        (n - a + 1) * (a - w) *
          positiveDerivativeMixedBudget yCap sCap lCap 2 ≤
      P.regularNumerator := by
    rw [UnequalParameters.regularNumerator]
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left (n - w) hdot
    · rw [hmixedZ]
      rfl
  change
    (n - w) *
          (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
            positiveDerivativeMixedBudget yCap sCap lCap j) +
        (n - a + 1) * (a - w) *
            positiveDerivativeMixedBudget yCap sCap lCap 2 +
          (a - w) * groupedEscapeDot yCap sCap lCap ≤
      P.regularNumerator + P.gap * groupedEscapeDot yCap sCap lCap
  exact Nat.add_le_add hcore le_rfl

/-- Divide the grouped estimate by its gap.  The only post-division surcharge
is the proper-escape dot product. -/
theorem grouped_count_le_adjacent_regularCountCap_add_escape
    (count n w a yCap sCap lCap : ℕ) (hwa : w < a)
    (hscaled : count * (a - w) ≤
      groupedDerivativeNumerator n w a (n - a) yCap sCap lCap) :
    count ≤ (adjacentGroupedStage n w a yCap sCap lCap).regularCountCap +
      groupedEscapeDot yCap sCap lCap := by
  let P := adjacentGroupedStage n w a yCap sCap lCap
  apply count_le_regularCountCap_add P count
    (groupedEscapeDot yCap sCap lCap)
  · change 0 < a - w
    omega
  · change count * (a - w) ≤
      P.regularNumerator + (a - w) * groupedEscapeDot yCap sCap lCap
    exact hscaled.trans
      (groupedDerivativeNumerator_le_adjacent n w a yCap sCap lCap)

/-- A direct consumer for the scaled conclusion of
`allGroupedNonRegularSeeds_of_cumulativeCaps` (with no outer exceptional
set).  The tail cap is added after division by the common gap. -/
theorem allGroupedNonRegularSeeds_card_le_adjacent_of_scaled
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (n w a yCap sCap lCap tailCap : ℕ) (hwa : w < a)
    (hscaled :
      (allGroupedNonRegularSeeds Q selected Gamma).card * (a - w) ≤
        groupedDerivativeNumerator n w a (n - a) yCap sCap lCap +
          tailCap * (a - w)) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (adjacentGroupedStage n w a yCap sCap lCap).regularCountCap +
        groupedEscapeDot yCap sCap lCap + tailCap := by
  let P := adjacentGroupedStage n w a yCap sCap lCap
  have hgap : 0 < P.gap := by
    change 0 < a - w
    omega
  have hscaled' :
      (allGroupedNonRegularSeeds Q selected Gamma).card * P.gap ≤
        P.regularNumerator +
          P.gap * (groupedEscapeDot yCap sCap lCap + tailCap) := by
    change
      (allGroupedNonRegularSeeds Q selected Gamma).card * (a - w) ≤
        P.regularNumerator +
          (a - w) * (groupedEscapeDot yCap sCap lCap + tailCap)
    calc
      (allGroupedNonRegularSeeds Q selected Gamma).card * (a - w) ≤
          groupedDerivativeNumerator n w a (n - a) yCap sCap lCap +
            tailCap * (a - w) := hscaled
      _ ≤ (P.regularNumerator +
            (a - w) * groupedEscapeDot yCap sCap lCap) +
          tailCap * (a - w) :=
        Nat.add_le_add_right
          (groupedDerivativeNumerator_le_adjacent n w a yCap sCap lCap) _
      _ = P.regularNumerator +
          (a - w) * (groupedEscapeDot yCap sCap lCap + tailCap) := by
        ring
  have hcount := count_le_regularCountCap_add P
    (allGroupedNonRegularSeeds Q selected Gamma).card
    (groupedEscapeDot yCap sCap lCap + tailCap) hgap hscaled'
  simpa only [P, Nat.add_assoc] using hcount

/-- Add the one aggregate terminal population after unscaling the grouped
exact-chain count. -/
theorem allGroupedNonRegularSeeds_card_le_adjacent_add_tail
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (n w a yCap sCap lCap tailCap : ℕ) (hwa : w < a)
    (hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card * (a - w) ≤
        groupedDerivativeNumerator n w a (n - a) yCap sCap lCap)
    (htail : (aggregateTerminalSeeds Q selected Gamma).card ≤ tailCap) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (adjacentGroupedStage n w a yCap sCap lCap).regularCountCap +
        groupedEscapeDot yCap sCap lCap + tailCap := by
  have hgrouped := grouped_count_le_adjacent_regularCountCap_add_escape
    (allPositiveExactChainSeeds Q selected Gamma).card
    n w a yCap sCap lCap hwa hscaled
  calc
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
        (allPositiveExactChainSeeds Q selected Gamma).card +
          (aggregateTerminalSeeds Q selected Gamma).card := by
      exact Finset.card_union_le _ _
    _ ≤ (adjacentGroupedStage n w a yCap sCap lCap).regularCountCap +
          groupedEscapeDot yCap sCap lCap + tailCap :=
      Nat.add_le_add hgrouped htail

def fixedHGroupedStage : UnequalParameters :=
  adjacentGroupedStage 262144 131071 181363 153 34 6676

def fixedHEscapeDot : ℕ := groupedEscapeDot 153 34 6676

theorem fixedHGroupedStage_exact :
    fixedHGroupedStage.regularCountCap = 139952655613867 := by
  native_decide

theorem fixedHEscapeDot_exact : fixedHEscapeDot = 200877080 := by
  native_decide

/-- Exact fixed-H ledger shape: one all-factor grouped charge, its escape dot,
and one aggregate tail. -/
theorem fixedH_allGroupedNonRegularSeeds_card_le
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) 153 34 6676)
    (htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      tailUniformStage.countCap) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      fixedHGroupedStage.regularCountCap + fixedHEscapeDot +
        tailUniformStage.countCap := by
  exact allGroupedNonRegularSeeds_card_le_adjacent_add_tail
    Q selected Gamma 262144 131071 181363 153 34 6676
      tailUniformStage.countCap (by omega) hscaled htail

def residualBGroupedStage (p : FlagDegree) : UnequalParameters :=
  adjacentGroupedStage 262144 131071 181363
    (153 - middle p) (34 - p.all) (14261 - total p)

def residualBEscapeDot (p : FlagDegree) : ℕ :=
  groupedEscapeDot (153 - middle p) (34 - p.all) (14261 - total p)

def residualBTailStage (p : FlagDegree) : TightParameters :=
  ⟨262144, 131071, 181363,
    131071 * (153 - middle p), 14261 - total p, 1⟩

/-- Residual-B ledger shape after subtracting the retained flag from every
cumulative cap. -/
theorem residualB_allGroupedNonRegularSeeds_card_le
    (p : FlagDegree)
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) (153 - middle p) (34 - p.all)
          (14261 - total p))
    (htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      (residualBTailStage p).countCap) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (residualBGroupedStage p).regularCountCap + residualBEscapeDot p +
        (residualBTailStage p).countCap := by
  exact allGroupedNonRegularSeeds_card_le_adjacent_add_tail
    Q selected Gamma 262144 131071 181363
      (153 - middle p) (34 - p.all) (14261 - total p)
      (residualBTailStage p).countCap (by omega) hscaled htail

def residualBMaxEscapeDot : ℕ := groupedEscapeDot 153 34 14261

theorem residualBMaxEscapeDot_exact : residualBMaxEscapeDot = 429140070 := by
  native_decide

theorem groupedEscapeDot_mono
    {yCap sCap lCap yCap' sCap' lCap' : ℕ}
    (hy : yCap ≤ yCap') (hs : sCap ≤ sCap') (hl : lCap ≤ lCap') :
    groupedEscapeDot yCap sCap lCap ≤
      groupedEscapeDot yCap' sCap' lCap' := by
  unfold groupedEscapeDot
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul
  · fin_cases j <;> simp [activeEscapeSurfaceCap] <;> omega
  · fin_cases j <;> simp [positiveDerivativeMixedBudget] <;> gcongr

theorem residualBEscapeDot_le_max (p : FlagDegree) :
    residualBEscapeDot p ≤ residualBMaxEscapeDot := by
  apply groupedEscapeDot_mono
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _

/-- Uniform residual-B version used when the exceptional allowance reserves
the full-box escape dot. -/
theorem residualB_allGroupedNonRegularSeeds_card_le_maxEscape
    (p : FlagDegree)
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hscaled :
      (allPositiveExactChainSeeds Q selected Gamma).card *
          (181363 - 131071) ≤
        groupedDerivativeNumerator 262144 131071 181363
          (262144 - 181363) (153 - middle p) (34 - p.all)
          (14261 - total p))
    (htail : (aggregateTerminalSeeds Q selected Gamma).card ≤
      (residualBTailStage p).countCap) :
    (allGroupedNonRegularSeeds Q selected Gamma).card ≤
      (residualBGroupedStage p).regularCountCap + residualBMaxEscapeDot +
        (residualBTailStage p).countCap := by
  exact (residualB_allGroupedNonRegularSeeds_card_le
    p Q selected Gamma hscaled htail).trans
      (Nat.add_le_add_right
        (Nat.add_le_add_left (residualBEscapeDot_le_max p) _) _)

end

end ProximityPrize.SubmissionLower.LocatorGroupedNonRegularCardinality6803
