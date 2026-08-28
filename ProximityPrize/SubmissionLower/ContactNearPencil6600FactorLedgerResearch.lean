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


end ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch

#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.factorRegularLedger_projection_decomposition
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factorRegularLedger_le_flag
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch.sum_factorRegularLedger_le
