import ProximityPrize.SubmissionLower.LocatorHybridCells

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCellsC1. -/
section PackedLocator_LocatorHybridCellsC1
/-
LOCATOR HYBRID CELLS — C1 VARIANT.

C1 drops the half-tail offset from the hybrid coordinate:

  cellHybridCoordinateC1 t y r = cellRational t y r      (was  cellRational + ⟨0, (w+1)/2, 3·((w+1)/2)⟩)

which is affordable once the *flag* route is restricted to components of local
multiplicity at least 6.  Components of multiplicity 1..5 are charged instead
through the moving engine at cut level `w + mult`, so the moving term's outer
factor grows from `w + 1` to `w + 5`.  The branch condition gains `3 ≤ r`
(equivalently `1 ≤ cellS r`); at `r = 2` the padded two-tail cost is already
cheaper than the current hybrid cost, so nothing is lost there.

This file only ADDS the C1 pieces on top of `LocatorHybridCells`; every flag and
lemma that is unchanged (cellA/cellB/cellS, cellSupport, cellSharpTail,
cellRational, cellMovingFiber, cellMovingCut, cellMovingCut_eq_center_add,
weightedCost_mono, the closed forms) is reused verbatim.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridCellsC1
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### The C1 hybrid coordinate -/

/-- C1: the hybrid coordinate is the bare rational coordinate. -/
def cellHybridCoordinateC1 (t y r : Nat) : FlagDegree := cellRational t y r

/-- The rational coordinate at an arbitrary cut level `k`; `k = w + 1` is
`cellRational`.  This is the flag part produced by the moving engine when the
proper cut sits at `globalTailCut (w + 1 + delay)` with `k = w + delay`. -/
def cellRationalAt (t y r k : Nat) : FlagDegree :=
  center (cellA t y) (cellB y r) (cellS r) +
    k • (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree)

theorem cellRationalAt_succ_w (t y r : Nat) :
    cellRationalAt t y r (w + 1) = cellRational t y r :=
  center_add_smul_eq_cellRational t y r

theorem cellRationalAt_eq (t y r k : Nat) :
    cellRationalAt t y r k =
      ⟨2 * cellA t y + k * cellA t y,
        2 * cellB y r + 2 + k * cellB y r,
        2 * cellS r + 3 + k * cellS r⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellRationalAt, center, direction, unitYZFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

/-! ### Absorption at the bare rational coordinate, threshold `6 ≤ mult`

The three lemmas below replace `LocatorHybridCells.sharp_absorbs_all` /
`sharp_absorbs_ysall` / `sharp_absorbs_total`.  The offsets `196608` and
`262144` are gone; in exchange `2 ≤ mult` becomes `6 ≤ mult` and the branch
positivity hypotheses `1 ≤ s`, `1 ≤ b + s`, `1 ≤ a + b + s` are required.  All
three follow from `r + 2 ≤ y` and `3 ≤ r`. -/

/-- z-cumulative absorption.
    sharp.all = (2s+3)·(131072+delay);  rational.all = 131072·s + (2s+3). -/
theorem sharp_absorbs_all_C1 (s delay mult : ℕ) (hs : 1 ≤ s)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    (2 * s + 3) * (131072 + delay) ≤ mult * (131072 * s + (2 * s + 3)) := by
  have key : 131072 * (2 * s + 3) ≤ mult * (131072 * s) := by
    calc 131072 * (2 * s + 3) ≤ 131072 * (6 * s) := by omega
      _ = 6 * (131072 * s) := by ring
      _ ≤ mult * (131072 * s) := Nat.mul_le_mul_right _ hm6
  calc
    (2 * s + 3) * (131072 + delay) ≤ (2 * s + 3) * (131072 + mult) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 131072 * (2 * s + 3) + mult * (2 * s + 3) := by ring
    _ ≤ mult * (131072 * s) + mult * (2 * s + 3) := Nat.add_le_add_right key _
    _ = mult * (131072 * s + (2 * s + 3)) := by ring

/-- yz-cumulative absorption, with `B = b + s`.
    sharp.(yz+all) = 1 + (2B+4)·(131072+delay);  rational.(yz+all) = 131072·B + 2B + 5. -/
theorem sharp_absorbs_ysall_C1 (B delay mult : ℕ) (hB : 1 ≤ B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * B + 4) * (131072 + delay) ≤ mult * (131072 * B + 2 * B + 5) := by
  have key : 1 + 131072 * (2 * B + 4) ≤ mult * (131072 * B) + mult := by
    have h6 : 6 * (131072 * B) + 6 ≤ mult * (131072 * B) + mult := by
      have := Nat.mul_le_mul_right (131072 * B) hm6
      omega
    have hB' : 262144 * B + 524289 ≤ 786432 * B + 6 := by
      have : (524288 : ℕ) ≤ 524288 * B := by
        calc (524288 : ℕ) = 524288 * 1 := by ring
          _ ≤ 524288 * B := Nat.mul_le_mul_left _ hB
      omega
    calc 1 + 131072 * (2 * B + 4) = 262144 * B + 524289 := by ring
      _ ≤ 786432 * B + 6 := hB'
      _ = 6 * (131072 * B) + 6 := by ring
      _ ≤ mult * (131072 * B) + mult := h6
  calc
    1 + (2 * B + 4) * (131072 + delay) ≤ 1 + (2 * B + 4) * (131072 + mult) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    _ = (1 + 131072 * (2 * B + 4)) + mult * (2 * B + 4) := by ring
    _ ≤ (mult * (131072 * B) + mult) + mult * (2 * B + 4) :=
      Nat.add_le_add_right key _
    _ = mult * (131072 * B + 2 * B + 5) := by ring

/-- total-cumulative absorption; the `yz` shape with `A = a + b + s`. -/
theorem sharp_absorbs_total_C1 (A delay mult : ℕ) (hA : 1 ≤ A)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * A + 4) * (131072 + delay) ≤ mult * (131072 * A + 2 * A + 5) :=
  sharp_absorbs_ysall_C1 A delay mult hA hdm hm6

/-! ### The multiplicity 1..5 route fits inside `mult` copies of the coordinate

`weightedCost` is linear in the *raw* flag components, so the moving route's flag
part must be dominated componentwise (not just cumulatively). -/

theorem affine_le_smul (u v mult : ℕ) (hm : 1 ≤ mult) :
    (131073 + mult) * u + v ≤ mult * (131074 * u + v) := by
  have h1 : 131073 + mult ≤ 131074 * mult := by
    have : 131073 * 1 ≤ 131073 * mult := Nat.mul_le_mul_left _ hm
    omega
  calc (131073 + mult) * u + v ≤ (131074 * mult) * u + mult * v :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.le_mul_of_pos_left _ hm)
    _ = mult * (131074 * u + v) := by ring

/-- The flag charged to a multiplicity-`mult` component on the moving route
(`k = w + mult`) is dominated componentwise by `mult` copies of the C1 hybrid
coordinate.  This is what makes the low-multiplicity branch affordable. -/
theorem cellRationalAt_le_smul (t y r mult : Nat) (hm : 1 ≤ mult) :
    (cellRationalAt t y r (w + mult)).zOnly ≤
        (mult • cellHybridCoordinateC1 t y r).zOnly ∧
      (cellRationalAt t y r (w + mult)).yz ≤
        (mult • cellHybridCoordinateC1 t y r).yz ∧
      (cellRationalAt t y r (w + mult)).all ≤
        (mult • cellHybridCoordinateC1 t y r).all := by
  have hz := affine_le_smul (cellA t y) 0 mult hm
  have hy := affine_le_smul (cellB y r) 2 mult hm
  have ha := affine_le_smul (cellS r) 3 mult hm
  simp only [cellRationalAt_eq, cellHybridCoordinateC1, cellRational_eq,
    nsmul_zOnly, nsmul_yz, nsmul_all, w] at *
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hz, hy, ha]

/-- Trivially, the rational coordinate is the C1 hybrid coordinate. -/
theorem cellRational_le_hybridC1 (t y r : Nat) :
    (cellRational t y r).zOnly ≤ (cellHybridCoordinateC1 t y r).zOnly ∧
      (cellRational t y r).yz ≤ (cellHybridCoordinateC1 t y r).yz ∧
      (cellRational t y r).all ≤ (cellHybridCoordinateC1 t y r).all :=
  ⟨le_rfl, le_rfl, le_rfl⟩

theorem cellHybridCoordinateC1_yz (t y r : Nat) :
    (cellHybridCoordinateC1 t y r).yz = 131074 * cellB y r + 2 :=
  cellRational_yz t y r

/-- The single numeric gate: in the hybrid branch `r + 2 ≤ y` we have `b ≥ 1`, so
any error cap below `131076` passes. -/
theorem hybridC1Gate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  rationalGate_of_le t y r errorCap hb hcap

/-! ### The C1 cell cost -/

def cellHybridCostC1 (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellSharpTail t y r)
      (cellHybridCoordinateC1 t y r) +
    (w + 5) * flagMixed (cellFixedFlag t y r) (cellMovingFiber t y r)
      (cellMovingCut t y r)

def cellRegularCostC1 (t y r : Nat) : Nat :=
  if 3 ≤ r ∧ r + 2 ≤ y then cellHybridCostC1 t y r else cellDelayedCost t y r

def cellCostOfC1 (f : FlagDegree) (t y r : Nat) : Nat :=
  if 3 ≤ r ∧ r + 2 ≤ y then
    flagMixed f (cellSharpTail t y r) (cellHybridCoordinateC1 t y r) +
      (w + 5) * flagMixed f (cellMovingFiber t y r) (cellMovingCut t y r)
  else flagMixed f (cellFirstTail t y r) (cellSecondTail t y r)

theorem cellRegularCostC1_eq_cellCostOfC1 (t y r : Nat) :
    cellRegularCostC1 t y r = cellCostOfC1 (cellFixedFlag t y r) t y r := by
  unfold cellRegularCostC1 cellCostOfC1 cellHybridCostC1 cellDelayedCost
  split_ifs <;> rfl

theorem sum_cellCostOfC1_le_of_cumulative {J : Type*} [Fintype J]
    (f : J → FlagDegree) (p : FlagDegree) (t y r : Nat)
    (hs : (∑ i, (f i).all) ≤ p.all)
    (hm : (∑ i, ((f i).yz + (f i).all)) ≤ p.yz + p.all)
    (ht : (∑ i, ((f i).zOnly + (f i).yz + (f i).all)) ≤
      p.zOnly + p.yz + p.all) :
    (∑ i, cellCostOfC1 (f i) t y r) ≤ cellCostOfC1 p t y r := by
  unfold cellCostOfC1
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht)
      (Nat.mul_le_mul_left _
        (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht))
  · exact sum_flagMixed_le_of_cumulative f p _ _ hs hm ht

/-- The C1 bound in closed (a, b, s)-form, matching `hybridBound_eq`. -/
theorem hybridBoundC1_eq (flag : FlagDegree) (t y r : Nat) :
    flagMixed flag (cellSharpTail t y r) (cellHybridCoordinateC1 t y r) +
        (w + 5) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) =
      flagMixed flag
          ⟨2 * cellA t y * 131072, 1 + (2 * cellB y r + 1) * 131072,
            (2 * cellS r + 3) * 131072⟩
          ⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ +
        131076 * flagMixed flag ⟨cellA t y, cellB y r + 1, cellS r + 3⟩
          (⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 131072, 262144⟩) := by
  simp only [cellSharpTail_eq, cellHybridCoordinateC1, cellRational_eq,
    cellMovingFiber_eq, cellMovingCut_eq, w]

end
end ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier49 : True := by trivial
end ProximityPrize.SubmissionLower

