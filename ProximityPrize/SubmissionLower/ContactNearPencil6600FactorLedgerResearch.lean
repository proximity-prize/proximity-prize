import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6600FlagResearch

/-!
# Factorwise linear aggregation of the 66.00 regular ledger

The nested residual-incidence cost is linear in the flag of the original
surface factor.  Consequently distinct irreducible factors must be charged
their own flags and then summed; charging the full surface flag to every
factor would be an invalid overcount.  This module proves the exact finite
aggregation against the one global `surfaceFlag6600` ledger.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch

open scoped BigOperators
open ContactFlagBezout6543Research
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch

set_option maxHeartbeats 1000000

/-- Primary two-layer residual cost assigned to one surface-factor flag. -/
def factorPrimary (p : FlagDegree) : ℕ :=
  flagMixed p agreementDirection6600 agreementDirection6600 * degreeIncidence ^ 2 +
    2 * flagMixed p agreementDirection6600 unitYZFlag *
      degreeIncidence * unitIncidence +
    flagMixed p unitYZFlag unitYZFlag * unitIncidence ^ 2

/-- Branch-local large-pencil `Z` charge assigned to one surface-factor
flag. -/
def factorZTail (p : FlagDegree) : ℕ :=
  (errors + 1) * gap *
    (flagMixed p agreementDirection6600 unitZFlag * degreeIncidence +
      flagMixed p unitYZFlag unitZFlag * unitIncidence)

/-- Degree-zero-safe all-coordinate fallback for the large-pencil branch. -/
def factorAllTail (p : FlagDegree) : ℕ :=
  (errors + 1) * gap *
    (flagMixed p agreementDirection6600 unitAllFlag * degreeIncidence +
      flagMixed p unitYZFlag unitAllFlag * unitIncidence)

def factorRegularLedger (p : FlagDegree) : ℕ :=
  factorPrimary p + factorZTail p + factorAllTail p

/-- The final factor ledger is literally linear in the three nested flag
coordinates. -/
theorem factorRegularLedger_projection_decomposition (p : FlagDegree) :
    factorRegularLedger p =
      p.zOnly * factorRegularLedger unitZFlag +
      p.yz * factorRegularLedger unitYZFlag +
      p.all * factorRegularLedger unitAllFlag := by
  cases p
  simp [factorRegularLedger, factorPrimary, factorZTail, factorAllTail, flagMixed,
    unitZFlag, unitYZFlag, unitAllFlag]
  ring

/-- The one global surface flag evaluates to the independently checked
primary and `Z`-tail numerators. -/
theorem factorRegularLedger_surface_exact :
    factorRegularLedger surfaceFlag6600 =
      stratifiedPrimary + stratifiedZTail + factorAllTail surfaceFlag6600 := by
  simp only [factorRegularLedger, factorPrimary, factorZTail]
  rw [flagMixed_direction_values.1,
    flagMixed_direction_values.2.1,
    flagMixed_direction_values.2.2.1,
    flagMixed_direction_values.2.2.2.1,
    flagMixed_direction_values.2.2.2.2]
  rfl

/-- Finite surface factors aggregate against any coordinatewise flag cap. -/
theorem sum_factorRegularLedger_le_flag
    {I : Type} [Fintype I] (p : I → FlagDegree) (cap : FlagDegree)
    (hz : (∑ i, (p i).zOnly) ≤ cap.zOnly)
    (hyz : (∑ i, (p i).yz) ≤ cap.yz)
    (hall : (∑ i, (p i).all) ≤ cap.all) :
    (∑ i, factorRegularLedger (p i)) ≤ factorRegularLedger cap := by
  classical
  calc
    (∑ i, factorRegularLedger (p i)) =
        ∑ i, ((p i).zOnly * factorRegularLedger unitZFlag +
          (p i).yz * factorRegularLedger unitYZFlag +
          (p i).all * factorRegularLedger unitAllFlag) := by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedger_projection_decomposition (p i)
    _ =
        (∑ i, (p i).zOnly) * factorRegularLedger unitZFlag +
        (∑ i, (p i).yz) * factorRegularLedger unitYZFlag +
        (∑ i, (p i).all) * factorRegularLedger unitAllFlag := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ cap.zOnly * factorRegularLedger unitZFlag +
        cap.yz * factorRegularLedger unitYZFlag +
        cap.all * factorRegularLedger unitAllFlag :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_right _ hz)
          (Nat.mul_le_mul_right _ hyz))
        (Nat.mul_le_mul_right _ hall)
    _ = factorRegularLedger cap :=
      (factorRegularLedger_projection_decomposition cap).symm

/-- Finite surface factors whose coordinatewise flag sum fits in the sharp
global surface flag consume at most the sharp global regular ledger. -/
theorem sum_factorRegularLedger_le
    {I : Type} [Fintype I] (p : I → FlagDegree)
    (hz : (∑ i, (p i).zOnly) ≤ surfaceFlag6600.zOnly)
    (hyz : (∑ i, (p i).yz) ≤ surfaceFlag6600.yz)
    (hall : (∑ i, (p i).all) ≤ surfaceFlag6600.all) :
    (∑ i, factorRegularLedger (p i)) ≤
      stratifiedPrimary + stratifiedZTail + factorAllTail surfaceFlag6600 := by
  calc
    _ ≤ factorRegularLedger surfaceFlag6600 :=
      sum_factorRegularLedger_le_flag p surfaceFlag6600 hz hyz hall
    _ = stratifiedPrimary + stratifiedZTail + factorAllTail surfaceFlag6600 :=
      factorRegularLedger_surface_exact

/-- Robust rectangular factor cap obtained directly from the three existing
separated degree budgets.  It is slightly larger than `surfaceFlag6600` but
still leaves substantial score-66 ledger slack. -/
def rectangularSurfaceFlag6600 : FlagDegree := ⟨495, 43, 8⟩

def rectangularRegularNumerator : ℕ :=
  factorRegularLedger rectangularSurfaceFlag6600

def rectangularTotalNumerator : ℕ :=
  rectangularRegularNumerator + retainedSingularContribution

def rectangularLedgerCeiling : ℕ :=
  (rectangularTotalNumerator + gap ^ 2 - 1) / gap ^ 2

theorem rectangular_regular_exact :
    rectangularRegularNumerator = 361802540717144456802514527 := by
  norm_num [rectangularRegularNumerator, factorRegularLedger,
    factorPrimary, factorZTail, factorAllTail, rectangularSurfaceFlag6600,
    flagMixed, agreementDirection6600, unitYZFlag, unitZFlag, unitAllFlag,
    degreeIncidence, unitIncidence, errors, gap, agreements, n, w]

theorem rectangular_total_exact :
    rectangularTotalNumerator = 368517457418416467513333482 := by
  rw [show rectangularTotalNumerator =
      rectangularRegularNumerator + retainedSingularContribution by rfl,
    rectangular_regular_exact]
  norm_num [retainedSingularContribution]

theorem rectangular_ledger_ceiling_exact :
    rectangularLedgerCeiling = 135685232102542715 := by
  norm_num [rectangularLedgerCeiling, rectangular_total_exact,
    gap, agreements, n, errors, w]

theorem rectangular_strict_budget :
    rectangularTotalNumerator < alignmentBudget * gap ^ 2 := by
  rw [rectangular_total_exact]
  norm_num [alignmentBudget, gap, agreements, n, errors, w]

theorem rectangular_budget_slack :
    alignmentBudget - rectangularLedgerCeiling = 1805131953154828 := by
  rw [rectangular_ledger_ceiling_exact]
  norm_num [alignmentBudget]

theorem sum_factorRegularLedger_rectangular_le
    {I : Type} [Fintype I] (p : I → FlagDegree)
    (hz : (∑ i, (p i).zOnly) ≤ 495)
    (hyz : (∑ i, (p i).yz) ≤ 43)
    (hall : (∑ i, (p i).all) ≤ 8) :
    (∑ i, factorRegularLedger (p i)) ≤ rectangularRegularNumerator := by
  exact sum_factorRegularLedger_le_flag p rectangularSurfaceFlag6600 hz hyz hall

/-- Component-count inequalities aggregate before applying the flag budget. -/
theorem sum_factor_counts_le
    {I : Type} [Fintype I] (count : I → ℕ) (p : I → FlagDegree)
    (hcount : ∀ i, count i * gap ^ 2 ≤ factorRegularLedger (p i))
    (hz : (∑ i, (p i).zOnly) ≤ surfaceFlag6600.zOnly)
    (hyz : (∑ i, (p i).yz) ≤ surfaceFlag6600.yz)
    (hall : (∑ i, (p i).all) ≤ surfaceFlag6600.all) :
    (∑ i, count i) * gap ^ 2 ≤
      stratifiedPrimary + stratifiedZTail + factorAllTail surfaceFlag6600 := by
  calc
    (∑ i, count i) * gap ^ 2 = ∑ i, count i * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i, factorRegularLedger (p i) :=
      Finset.sum_le_sum (fun i _ ↦ hcount i)
    _ ≤ stratifiedPrimary + stratifiedZTail + factorAllTail surfaceFlag6600 :=
      sum_factorRegularLedger_le p hz hyz hall

theorem sum_factor_counts_rectangular_le
    {I : Type} [Fintype I] (count : I → ℕ) (p : I → FlagDegree)
    (hcount : ∀ i, count i * gap ^ 2 ≤ factorRegularLedger (p i))
    (hz : (∑ i, (p i).zOnly) ≤ 495)
    (hyz : (∑ i, (p i).yz) ≤ 43)
    (hall : (∑ i, (p i).all) ≤ 8) :
    (∑ i, count i) * gap ^ 2 ≤ rectangularRegularNumerator := by
  calc
    (∑ i, count i) * gap ^ 2 = ∑ i, count i * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i, factorRegularLedger (p i) :=
      Finset.sum_le_sum (fun i _ ↦ hcount i)
    _ ≤ rectangularRegularNumerator :=
      sum_factorRegularLedger_rectangular_le p hz hyz hall

theorem combined_rectangular_scaled_bound
    (regularCount singularCount : ℕ)
    (hregular : regularCount * gap ^ 2 ≤ rectangularRegularNumerator)
    (hsingular : singularCount * gap ^ 2 ≤ retainedSingularContribution) :
    (regularCount + singularCount) * gap ^ 2 ≤ rectangularTotalNumerator := by
  calc
    (regularCount + singularCount) * gap ^ 2 =
        regularCount * gap ^ 2 + singularCount * gap ^ 2 := by ring
    _ ≤ rectangularRegularNumerator + retainedSingularContribution :=
      Nat.add_le_add hregular hsingular
    _ = rectangularTotalNumerator := rfl

end ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch

#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.factorRegularLedger_projection_decomposition
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factorRegularLedger_le_flag
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factorRegularLedger_le
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factor_counts_le
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.rectangular_strict_budget
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factor_counts_rectangular_le
