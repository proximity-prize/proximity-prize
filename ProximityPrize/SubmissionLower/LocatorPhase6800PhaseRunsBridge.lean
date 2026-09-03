import ProximityPrize.SubmissionLower.LocatorPhase6800Concrete
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRuns

/-! Definitional bridge from the sparse affine-run checker to the public
`PhaseStateRCheck`.  It contains no generated data and no computation. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge

open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorPhase6800Audit
open LocatorPhase6800Concrete LocatorPhase6800BaseDirectData
open LocatorPhase6800PhaseRuns

set_option autoImplicit false
set_option maxRecDepth 100000

theorem baseAt_rowContext_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    baseAt (rowContext R V) z = checkedBaseCap (rawFlag R V z) := by
  have hnarrow : NarrowState (rawFlag R V z) := by
    simp only [NarrowState, rawFlag_all, rawFlag_middle, rawFlag_total]
    omega
  rw [checkedBaseCap_of_narrow hnarrow]
  rfl

theorem parentCharge0_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 0 z =
      r1200Potential.eval (rawFlag R V z) +
        parentDefect rPrefix (rawFlag R V z) := by
  rfl

theorem parentCharge1_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 1 z =
      sourceCPotential.eval (rawFlag R V z) +
        parentDefect cPrefix (rawFlag R V z) := by
  rfl

theorem parentCharge2_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 2 z =
      split500Potential.eval (rawFlag R V z) +
        parentDefect f500Prefix (rawFlag R V z) := by
  rfl

theorem parentCharge3_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 3 z =
      split390Potential.eval (rawFlag R V z) +
        parentDefect s390Prefix (rawFlag R V z) := by
  rfl

theorem hereCharge0_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 0 z =
      r1200Potential.eval (rawFlag R V z) + rPrefix (rawFlag R V z) := by
  rfl

theorem hereCharge1_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 1 z =
      sourceCPotential.eval (rawFlag R V z) + cPrefix (rawFlag R V z) := by
  rfl

theorem hereCharge2_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 2 z =
      split500Potential.eval (rawFlag R V z) + f500Prefix (rawFlag R V z) := by
  rfl

theorem hereCharge3_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 3 z =
      split390Potential.eval (rawFlag R V z) + s390Prefix (rawFlag R V z) := by
  rfl

theorem capBefore0_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 0 z = checkedBaseCap (rawFlag R V z) :=
  baseAt_rowContext_eq R V z hR hR28 hV hz

theorem capBefore1_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 1 z = fastAfterR (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 0 ≤ z then
    min (baseAt (rowContext R V) z) (parentCharge (rowContext R V) 0 z)
    else baseAt (rowContext R V) z) = fastAfterR (rawFlag R V z)
  rw [baseAt_rowContext_eq R V z hR hR28 hV hz, parentCharge0_eq]
  rfl

theorem capBefore2_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 2 z = fastAfterC (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 1 ≤ z then
    min (capBefore (rowContext R V) 1 z) (parentCharge (rowContext R V) 1 z)
    else capBefore (rowContext R V) 1 z) = fastAfterC (rawFlag R V z)
  rw [capBefore1_eq R V z hR hR28 hV hz, parentCharge1_eq]
  rfl

theorem capBefore3_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 3 z = fastAfterF500 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 2 ≤ z then
    min (capBefore (rowContext R V) 2 z) (parentCharge (rowContext R V) 2 z)
    else capBefore (rowContext R V) 2 z) = fastAfterF500 (rawFlag R V z)
  rw [capBefore2_eq R V z hR hR28 hV hz, parentCharge2_eq]
  rfl

theorem capBefore4_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 4 z = fastAfterS390 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 3 ≤ z then
    min (capBefore (rowContext R V) 3 z) (parentCharge (rowContext R V) 3 z)
    else capBefore (rowContext R V) 3 z) = fastAfterS390 (rawFlag R V z)
  rw [capBefore3_eq R V z hR hR28 hV hz, parentCharge3_eq]
  rfl

theorem sparseRV_to_public (R V : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28) (hV : V < 128 - R)
    (h : SparsePhaseStateRVCheck (rowContext R V))
    (z : ℕ) (hz : z < 5965 - (R + V)) :
    let p := rawFlag R V z
    (rThreshold R V ≤ z ∨
      checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
    (cThreshold R V ≤ z ∨
      fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
    (f500Threshold R V ≤ z ∨
      fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
    (s390Threshold R V ≤ z ∨
      fastAfterF500 p ≤ split390Potential.eval p + s390Prefix p) ∧
    fastAfterS390 p ≤ certifiedNarrowMaximum ∧
    fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  have hs := h z hz
  dsimp only
  rw [← capBefore0_eq R V z hR hR28 hV hz,
    ← capBefore1_eq R V z hR hR28 hV hz,
    ← capBefore2_eq R V z hR hR28 hV hz,
    ← capBefore3_eq R V z hR hR28 hV hz,
    ← capBefore4_eq R V z hR hR28 hV hz,
    ← hereCharge0_eq R V z, ← hereCharge1_eq R V z,
    ← hereCharge2_eq R V z, ← hereCharge3_eq R V z]
  exact hs

theorem sparseLayer_to_public (R : ℕ) (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (h : ∀ V ∈ List.range (128 - R),
      SparsePhaseStateRVCheck (rowContext R V)) : PhaseStateRCheck R := by
  intro V hV z hz
  exact sparseRV_to_public R V hR hR28 (List.mem_range.mp hV)
    (h V hV) z (List.mem_range.mp hz)

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge
