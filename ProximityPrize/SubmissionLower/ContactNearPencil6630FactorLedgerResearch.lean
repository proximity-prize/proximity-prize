import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
import ProximityPrize.SubmissionLower.ContactCumulativeWeightedDegreeResearch
import ProximityPrize.SubmissionLower.ContactSingularLedger6630Research

/-!
# Sharp cumulative factor ledger for score 66.30

The factorwise regular cost is linear in the three flag increments.  Its
unit coefficients are monotone from Z to YZ to All, so the actual cumulative
factor caps `(total, YS, S) <= (609,40,8)` recover the sharp global flag
`(569,32,8)` without a rectangular overcount.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch

set_option autoImplicit false

open scoped BigOperators
open ContactFlagBezout6543Research
open ContactNearPencil6630ArithmeticResearch
open ContactNearPencil6630FlagResearch
open ContactCumulativeWeightedDegreeResearch

set_option maxHeartbeats 2000000

def factorPrimary6630 (p : FlagDegree) : ℕ :=
  flagMixed p agreementDirection6630 agreementDirection6630 *
      degreeIncidence ^ 2 +
    2 * flagMixed p agreementDirection6630 unitYZFlag *
      degreeIncidence * unitIncidence +
    flagMixed p unitYZFlag unitYZFlag * unitIncidence ^ 2

def factorZTail6630 (p : FlagDegree) : ℕ :=
  (errors + 1) * gap *
    (flagMixed p agreementDirection6630 unitZFlag * degreeIncidence +
      flagMixed p unitYZFlag unitZFlag * unitIncidence)

def factorYZTail6630 (p : FlagDegree) : ℕ :=
  (errors + 1) * gap *
    (flagMixed p agreementDirection6630 unitYZFlag * degreeIncidence +
      flagMixed p unitYZFlag unitYZFlag * unitIncidence)

def factorRegularLedgerYZ (p : FlagDegree) : ℕ :=
  factorPrimary6630 p + factorZTail6630 p + factorYZTail6630 p

theorem factorRegularLedgerYZ_projection_decomposition (p : FlagDegree) :
    factorRegularLedgerYZ p =
      p.zOnly * factorRegularLedgerYZ unitZFlag +
      p.yz * factorRegularLedgerYZ unitYZFlag +
      p.all * factorRegularLedgerYZ unitAllFlag := by
  cases p
  simp [factorRegularLedgerYZ, factorPrimary6630, factorZTail6630,
    factorYZTail6630, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

theorem unit_ledger_values :
    factorRegularLedgerYZ unitZFlag = 204268535546862145962855 ∧
      factorRegularLedgerYZ unitYZFlag = 3446465238109331870665515 ∧
      factorRegularLedgerYZ unitAllFlag = 17716880486755708388420112 := by
  norm_num [factorRegularLedgerYZ, factorPrimary6630, factorZTail6630,
    factorYZTail6630, flagMixed, agreementDirection6630, unitZFlag,
    unitYZFlag, unitAllFlag, degreeIncidence, unitIncidence, errors, gap,
    agreements, n, w]

theorem unit_ledger_monotone :
    factorRegularLedgerYZ unitZFlag ≤ factorRegularLedgerYZ unitYZFlag ∧
      factorRegularLedgerYZ unitYZFlag ≤ factorRegularLedgerYZ unitAllFlag := by
  rw [unit_ledger_values.1, unit_ledger_values.2.1,
    unit_ledger_values.2.2]
  norm_num

theorem factorRegularLedgerYZ_eq_nestedCost (p : FlagDegree) :
    factorRegularLedgerYZ p =
      nestedIncrementCost
        (factorRegularLedgerYZ unitZFlag)
        (factorRegularLedgerYZ unitYZFlag)
        (factorRegularLedgerYZ unitAllFlag)
        (p.zOnly + p.yz + p.all) (p.yz + p.all) p.all := by
  rw [factorRegularLedgerYZ_projection_decomposition]
  simp only [nestedIncrementCost]
  have htotal : p.zOnly + p.yz + p.all - (p.yz + p.all) = p.zOnly := by
    omega
  have hmiddle : p.yz + p.all - p.all = p.yz := by omega
  rw [htotal, hmiddle]
  ring

theorem factorRegularLedgerYZ_surface_exact :
    factorRegularLedgerYZ surfaceFlag6630 = regularNumerator := by
  simp only [factorRegularLedgerYZ, factorPrimary6630, factorZTail6630,
    factorYZTail6630]
  rw [flagMixed_direction_values6630.1,
    flagMixed_direction_values6630.2.1,
    flagMixed_direction_values6630.2.2.1,
    flagMixed_direction_values6630.2.2.2.1,
    flagMixed_direction_values6630.2.2.2.2]
  rfl

/-- Generic cumulative aggregation into an arbitrary enclosing nested flag.
This is the factor-to-geometric-factor seam; the fixed `(609,40,8)` theorem
below is its global specialization. -/
theorem sum_factorRegularLedgerYZ_le_flag
    {I : Type*} [Fintype I] (p : I → FlagDegree) (q : FlagDegree)
    (hall : (∑ i, (p i).all) ≤ q.all)
    (hyzAll : (∑ i, ((p i).yz + (p i).all)) ≤ q.yz + q.all)
    (htotal : (∑ i, ((p i).zOnly + (p i).yz + (p i).all)) ≤
      q.zOnly + q.yz + q.all) :
    (∑ i, factorRegularLedgerYZ (p i)) ≤ factorRegularLedgerYZ q := by
  let cZ := factorRegularLedgerYZ unitZFlag
  let cYZ := factorRegularLedgerYZ unitYZFlag
  let cAll := factorRegularLedgerYZ unitAllFlag
  have hmono : cZ ≤ cYZ ∧ cYZ ≤ cAll := unit_ledger_monotone
  have hbound := sum_nestedIncrementCost_le_of_cumulative_caps
    cZ cYZ cAll
    (fun i ↦ (p i).zOnly + (p i).yz + (p i).all)
    (fun i ↦ (p i).yz + (p i).all) (fun i ↦ (p i).all)
    (q.zOnly + q.yz + q.all) (q.yz + q.all) q.all
    (fun i ↦ ⟨by omega, by omega⟩) hmono.1 hmono.2
    htotal hyzAll hall
  calc
    (∑ i, factorRegularLedgerYZ (p i)) =
        ∑ i, nestedIncrementCost cZ cYZ cAll
          ((p i).zOnly + (p i).yz + (p i).all)
          ((p i).yz + (p i).all) (p i).all := by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedgerYZ_eq_nestedCost (p i)
    _ ≤ cZ * (q.zOnly + q.yz + q.all) +
          (cYZ - cZ) * (q.yz + q.all) +
          (cAll - cYZ) * q.all := hbound
    _ = factorRegularLedgerYZ q := by
      rw [factorRegularLedgerYZ_eq_nestedCost]
      rw [nestedIncrementCost_eq_cumulative _ _ _ _ _ _
        (by omega) (by omega) hmono.1 hmono.2]

/-- Cumulative factor caps recover the sharp flag, using monotonicity of the
three unit-ledger coefficients. -/
theorem sum_factorRegularLedgerYZ_cumulative_le
    {I : Type*} [Fintype I] (p : I → FlagDegree)
    (hall : (∑ i, (p i).all) ≤ 8)
    (hyzAll : (∑ i, ((p i).yz + (p i).all)) ≤ 40)
    (htotal : (∑ i, ((p i).zOnly + (p i).yz + (p i).all)) ≤ 609) :
    (∑ i, factorRegularLedgerYZ (p i)) ≤
      factorRegularLedgerYZ surfaceFlag6630 := by
  exact sum_factorRegularLedgerYZ_le_flag p surfaceFlag6630
    (by simpa only [surfaceFlag6630] using hall)
    (by simpa only [surfaceFlag6630] using hyzAll)
    (by simpa only [surfaceFlag6630] using htotal)

theorem sum_factor_counts6630_le
    {I : Type*} [Fintype I] (count : I → ℕ) (p : I → FlagDegree)
    (hcount : ∀ i, count i * gap ^ 2 ≤ factorRegularLedgerYZ (p i))
    (hall : (∑ i, (p i).all) ≤ 8)
    (hyzAll : (∑ i, ((p i).yz + (p i).all)) ≤ 40)
    (htotal : (∑ i, ((p i).zOnly + (p i).yz + (p i).all)) ≤ 609) :
    (∑ i, count i) * gap ^ 2 ≤ regularNumerator := by
  calc
    (∑ i, count i) * gap ^ 2 = ∑ i, count i * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i, factorRegularLedgerYZ (p i) :=
      Finset.sum_le_sum (fun i _ ↦ hcount i)
    _ ≤ factorRegularLedgerYZ surfaceFlag6630 :=
      sum_factorRegularLedgerYZ_cumulative_le p hall hyzAll htotal
    _ = regularNumerator := factorRegularLedgerYZ_surface_exact

def tightSingularContribution6630 : ℕ :=
  ContactSingularLedger6630Research.tightSingularContribution

def totalNumerator6630 : ℕ :=
  regularNumerator + tightSingularContribution6630

def fieldBudget6630 : ℕ := 137490364055697543

def ledgerCeiling6630 : ℕ :=
  (totalNumerator6630 + gap ^ 2 - 1) / gap ^ 2

theorem tight_singular_contribution6630_exact :
    tightSingularContribution6630 = 29656986038790928183272 := by
  exact ContactSingularLedger6630Research.exact_values.2.2

theorem total_numerator6630_exact :
    totalNumerator6630 = 368280385225747638949705143 := by
  rw [show totalNumerator6630 =
      regularNumerator + tightSingularContribution6630 by rfl,
    regular_numerator_exact, tight_singular_contribution6630_exact]

theorem ledger_ceiling6630_exact :
    ledgerCeiling6630 = 136797514325107227 := by
  norm_num [ledgerCeiling6630, total_numerator6630_exact, gap,
    agreements, n, errors, w]

theorem field_slack6630_exact :
    fieldBudget6630 - ledgerCeiling6630 = 692849730590316 := by
  rw [ledger_ceiling6630_exact]
  norm_num [fieldBudget6630]

theorem strict_field_budget6630 :
    totalNumerator6630 < fieldBudget6630 * gap ^ 2 := by
  rw [total_numerator6630_exact]
  norm_num [fieldBudget6630, gap, agreements, n, errors, w]

theorem combined_scaled_bound6630
    (regularCount singularCount : ℕ)
    (hregular : regularCount * gap ^ 2 ≤ regularNumerator)
    (hsingular : singularCount * gap ^ 2 ≤ tightSingularContribution6630) :
    (regularCount + singularCount) * gap ^ 2 ≤ totalNumerator6630 := by
  calc
    (regularCount + singularCount) * gap ^ 2 =
        regularCount * gap ^ 2 + singularCount * gap ^ 2 := by ring
    _ ≤ regularNumerator + tightSingularContribution6630 :=
      Nat.add_le_add hregular hsingular
    _ = totalNumerator6630 := rfl

end ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch

#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch.factorRegularLedgerYZ_projection_decomposition
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch.sum_factorRegularLedgerYZ_cumulative_le
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch.ledger_ceiling6630_exact
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch.strict_field_budget6630
