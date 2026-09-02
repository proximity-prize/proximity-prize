/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Common-shear aggregate gate

The canceled, unaccepted lower PR #452 contains a useful new mechanism: one
nonzero shear `R + a Z` is selected for an entire finite component family.
Its geometric theorem controls the sum of the sheared coordinate degrees by
the old `R` and `Z` mixed-degree budgets together.

This upper-only file isolates the exact arithmetic handoff.  If an upper
argument supplies a common shear with

`sum dS <= mixedR + mixedZ`,

then the transformed fiber costs replace the `Z` cap by `capZ + 2 * capR`.
The theorem below proves that aggregation rule without importing or asserting
the lower geometric result.  The final receipt checks that even this full
penalty leaves the accepted carrier-oriented worst profile well below the
regular-layer gate.
-/

namespace ProximityPrize.SubmissionUpper.CommonShearSumGate

open scoped BigOperators

/-- Exact aggregate cost conversion for a single shear shared across a finite
component family.  The three hypotheses are the semantic interface that an
upper component theorem must supply. -/
theorem common_shear_aggregate
    {I : Type} [Fintype I]
    (dY dS dZ : I → ℕ)
    (capY capR capZ mixedY mixedR mixedZ : ℕ)
    (hY : ∑ i : I, dY i ≤ mixedY)
    (hS : ∑ i : I, dS i ≤ mixedR + mixedZ)
    (hZ : ∑ i : I, dZ i ≤ mixedZ) :
    Finset.univ.sum
        (fun i : I => capY * dY i + capR * dS i + (capZ + capR) * dZ i) ≤
      capY * mixedY + capR * mixedR + (capZ + 2 * capR) * mixedZ := by
  calc
    Finset.univ.sum
        (fun i : I => capY * dY i + capR * dS i + (capZ + capR) * dZ i) =
        capY * (∑ i : I, dY i) + capR * (∑ i : I, dS i) +
          (capZ + capR) * (∑ i : I, dZ i) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ capY * mixedY + capR * (mixedR + mixedZ) +
        (capZ + capR) * mixedZ :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left capY hY)
          (Nat.mul_le_mul_left capR hS))
        (Nat.mul_le_mul_left (capZ + capR) hZ)
    _ = capY * mixedY + capR * mixedR +
        (capZ + 2 * capR) * mixedZ := by ring

def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def targetAgreement : ℕ := 139782
def errors : ℕ := domainSize - targetAgreement
def gap : ℕ := targetAgreement - rowDegree
def movingNodes : ℕ := domainSize - rowDegree

/-- Carrier-oriented agreement caps and mixed degrees at the accepted audit's
worst Source-C profile. -/
def capY : ℕ := 22282071
def capR : ℕ := 4849627
def capZ : ℕ := 764406073
def mixedY : ℕ := 3294084
def mixedR : ℕ := 14780892
def mixedZ : ℕ := 7768

def commonShearDot : ℕ :=
  capY * mixedY + capR * mixedR + (capZ + 2 * capR) * mixedZ

def pencilTerm : ℕ := (errors + 1) * gap * mixedZ
def commonShearNumerator : ℕ := movingNodes * commonShearDot + pencilTerm
def commonShearCap : ℕ := commonShearNumerator / gap
def strictRegularLayerGate : ℕ := 10019053654770474

/-- The exact common-shear penalty is only `1,133,685,978,900` over the
left-oriented cap, and the resulting cap remains far below the layer gate. -/
theorem common_shear_oriented_receipt :
    commonShearNumerator = 19804362192015601456 ∧
      commonShearCap = 2273488944095465 ∧
      commonShearCap < strictRegularLayerGate := by
  norm_num [commonShearNumerator, commonShearCap, commonShearDot, pencilTerm,
    movingNodes, errors, gap, domainSize, targetAgreement, rowDegree, capY,
    capR, capZ, mixedY, mixedR, mixedZ, strictRegularLayerGate]

/-- The mixed-`R` characteristic gate excluded by the provisional residual
profile really does fail, while the common-shear interface does not require
it.  This is a feasibility receipt only, not evidence that PR #452 passed. -/
def fieldCharacteristic : ℕ := 2130706433
def provisionalImplicitYCap : ℕ := 4528
def provisionalAlgebraicCap : ℕ := 255893

theorem provisional_old_mixedR_gate_fails :
    fieldCharacteristic ≤
      2 * provisionalImplicitYCap * provisionalAlgebraicCap ∧
    2 * provisionalImplicitYCap * provisionalAlgebraicCap -
      fieldCharacteristic = 186660575 := by
  norm_num [fieldCharacteristic, provisionalImplicitYCap,
    provisionalAlgebraicCap]

#print axioms common_shear_aggregate
#print axioms common_shear_oriented_receipt
#print axioms provisional_old_mixedR_gate_fails

end ProximityPrize.SubmissionUpper.CommonShearSumGate
