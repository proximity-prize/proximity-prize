/-
LOCATOR HYBRID CELLS (port of ContactRouterCellCosts6750Research + the pure
flag arithmetic of ContactHybridTailProvider6751Research §1 from pr359).

Cells are parameterised by (t y r) with the atoms
  a = cellA t y = t - y,  b = cellB y r = y - r - 1,  s = cellS r = r - 2,
so that (for 2 ≤ r < y ≤ t) t = a+b+s+3, y = b+s+3, r = s+2 and the stage
support is `support a b s`.  `w` is the Locator's `RCN327.w = 131071`.
-/
import ProximityPrize.SubmissionLower.AL
import ProximityPrize.SubmissionLower.I
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Cell atoms and flags -/

def cellA (t y : Nat) : Nat := t - y
def cellB (y r : Nat) : Nat := y - r - 1
def cellS (r : Nat) : Nat := r - 2

def cellSupport (t y r : Nat) : ResidualSupportParameters :=
  support (cellA t y) (cellB y r) (cellS r)

def cellFixedFlag (t y r : Nat) : FlagDegree :=
  surfaceFlag (cellA t y) (cellB y r) (cellS r)

def cellFirstTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellSharpTail (t y r : Nat) : FlagDegree :=
  sharpResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellSecondTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 2)

def cellDirection (t y r : Nat) : FlagDegree :=
  RCN206.directionFlag (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r : Nat) : FlagDegree :=
  ⟨(w + 1) * cellA t y + (cellDirection t y r).zOnly,
    (w + 1) * cellB y r + (cellDirection t y r).yz + 1,
    (w + 1) * cellS r + (cellDirection t y r).all⟩

def cellHybridCoordinate (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, (w + 1) / 2, 3 * ((w + 1) / 2)⟩

def cellMovingFiber (t y r : Nat) : FlagDegree :=
  RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r)

def cellMovingCut (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, w + 1, 2 * (w + 1)⟩

def cellHybridCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellSharpTail t y r)
      (cellHybridCoordinate t y r) +
    (w + 1) * flagMixed (cellFixedFlag t y r) (cellMovingFiber t y r)
      (cellMovingCut t y r)

def cellDelayedCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellFirstTail t y r)
    (cellSecondTail t y r)

def cellRegularCost (t y r : Nat) : Nat :=
  if r + 2 ≤ y then cellHybridCost t y r else cellDelayedCost t y r

def cellTail1 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellSharpTail t y r else cellFirstTail t y r

def cellTail2 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellHybridCoordinate t y r else cellSecondTail t y r

def cellCostOf (f : FlagDegree) (t y r : Nat) : Nat :=
  if r + 2 ≤ y then
    flagMixed f (cellSharpTail t y r) (cellHybridCoordinate t y r) +
      (w + 1) * flagMixed f (cellMovingFiber t y r) (cellMovingCut t y r)
  else flagMixed f (cellFirstTail t y r) (cellSecondTail t y r)

theorem cellRegularCost_eq_cellCostOf (t y r : Nat) :
    cellRegularCost t y r = cellCostOf (cellFixedFlag t y r) t y r := by
  unfold cellRegularCost cellCostOf cellHybridCost cellDelayedCost
  split_ifs <;> rfl

theorem sum_cellCostOf_le_of_cumulative {J : Type*} [Fintype J]
    (f : J → FlagDegree) (p : FlagDegree) (t y r : Nat)
    (hs : (∑ i, (f i).all) ≤ p.all)
    (hm : (∑ i, ((f i).yz + (f i).all)) ≤ p.yz + p.all)
    (ht : (∑ i, ((f i).zOnly + (f i).yz + (f i).all)) ≤
      p.zOnly + p.yz + p.all) :
    (∑ i, cellCostOf (f i) t y r) ≤ cellCostOf p t y r := by
  unfold cellCostOf
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht)
      (Nat.mul_le_mul_left _
        (sum_flagMixed_le_of_cumulative f p _ _ hs hm ht))
  · exact sum_flagMixed_le_of_cumulative f p _ _ hs hm ht

/-! ### Pure flag arithmetic (pr359 §1)

All lemmas are subtraction-free: they are stated over the cell atoms
a = cellA t y, b = cellB y r, s = cellS r. -/

/-- z-cumulative absorption: sharp.all ≤ (mult • hybrid).all.
    sharp.all = (2s+3)·d with d = (w+1)+delay; hybrid.all = (w+1)s+(2s+3)+3((w+1)/2). -/
theorem sharp_absorbs_all (_a _b s delay mult : ℕ)
    (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    (2 * s + 3) * (131072 + delay) ≤
      mult * (131072 * s + (2 * s + 3) + 196608) := by
  calc
    (2 * s + 3) * (131072 + delay) ≤ (2 * s + 3) * (131072 + mult) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (65536 * (2 * s + 3)) + mult * (2 * s + 3) := by ring
    _ ≤ mult * (65536 * (2 * s + 3)) + mult * (2 * s + 3) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hm2) _
    _ = mult * (131072 * s + (2 * s + 3) + 196608) := by ring

/-- yz-cumulative absorption:
    sharp.(yz+all) = 1+(2(b+s)+4)·d; hybrid.(yz+all) = 131072(b+s)+2(b+s)+5+262144. -/
theorem sharp_absorbs_ysall (_a b s delay mult : ℕ)
    (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    1 + (2 * (b + s) + 4) * (131072 + delay) ≤
      mult * (131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
  have h1 : 1 + (2 * (b + s) + 4) * (131072 + delay) ≤
      1 + (2 * (b + s) + 4) * (131072 + mult) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have h2 : 2 * (65536 * (2 * (b + s) + 4)) ≤
      mult * (65536 * (2 * (b + s) + 4)) :=
    Nat.mul_le_mul_right _ hm2
  have hm1 : 1 ≤ mult := by omega
  calc
    1 + (2 * (b + s) + 4) * (131072 + delay) ≤
        1 + (2 * (b + s) + 4) * (131072 + mult) := h1
    _ = 1 + 2 * (65536 * (2 * (b + s) + 4)) + mult * (2 * (b + s) + 4) := by
      ring
    _ ≤ 1 + mult * (65536 * (2 * (b + s) + 4)) + mult * (2 * (b + s) + 4) :=
      Nat.add_le_add_right (Nat.add_le_add_left h2 _) _
    _ = mult * (131072 * (b + s) + 2 * (b + s) + 4 + 262144) + 1 := by ring
    _ ≤ mult * (131072 * (b + s) + 2 * (b + s) + 4 + 262144) + mult :=
      Nat.add_le_add_left (by omega : (1:ℕ) ≤ mult) _
    _ = mult * (131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by ring

/-- total-cumulative absorption: adds the z-column 131074·a on the hybrid side
    against 2a·d on the sharp side. -/
theorem sharp_absorbs_total (a b s delay mult : ℕ)
    (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
  have h1 : 1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
      1 + (2 * a + 2 * (b + s) + 4) * (131072 + mult) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have h2 : 2 * (65536 * (2 * a + 2 * (b + s) + 4)) ≤
      mult * (65536 * (2 * a + 2 * (b + s) + 4)) :=
    Nat.mul_le_mul_right _ hm2
  calc
    1 + (2 * a + 2 * (b + s) + 4) * (131072 + delay) ≤
        1 + (2 * a + 2 * (b + s) + 4) * (131072 + mult) := h1
    _ = 1 + 2 * (65536 * (2 * a + 2 * (b + s) + 4)) +
        mult * (2 * a + 2 * (b + s) + 4) := by ring
    _ ≤ 1 + mult * (65536 * (2 * a + 2 * (b + s) + 4)) +
        mult * (2 * a + 2 * (b + s) + 4) :=
      Nat.add_le_add_right (Nat.add_le_add_left h2 _) _
    _ = mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 4 + 262144) +
        1 := by ring
    _ ≤ mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 4 + 262144) +
        mult := Nat.add_le_add_left (by omega : (1:ℕ) ≤ mult) _
    _ = mult * (131074 * a + 131072 * (b + s) + 2 * (b + s) + 5 + 262144) := by
      ring

/-- center + (w+1) • ⟨a,b,s⟩ = cellRational (as flags), the identity that folds the
    moving engine's k·wc(⟨a,b,s⟩) term into the rational weightedCost. -/
theorem center_add_smul_eq_cellRational (t y r : Nat) :
    center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) =
      cellRational t y r := by
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  simp only [center, direction, unitYZFlag, cellDirection,
    RCN206.directionFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  congr 1 <;> ring

theorem flag_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g; simp_all

/-- cellMovingCut = center + (w+1) • surfaceFlag — the flag under which
    exists_firstTail_cut_budgets bounds the movingCost sum. -/
theorem cellMovingCut_eq_center_add (t y r : Nat) :
    cellMovingCut t y r =
      center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • RCN206.surfaceFlag (cellA t y) (cellB y r) (cellS r) := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
      cellDirection, RCN206.directionFlag, RCN206.surfaceFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

/-- rational ≤ hybrid coordinate-wise (hybrid = rational + ⟨0,(w+1)/2,3((w+1)/2)⟩). -/
theorem cellRational_le_hybrid (t y r : Nat) :
    (cellRational t y r).zOnly ≤ (cellHybridCoordinate t y r).zOnly ∧
    (cellRational t y r).yz ≤ (cellHybridCoordinate t y r).yz ∧
    (cellRational t y r).all ≤ (cellHybridCoordinate t y r).all := by
  simp only [cellHybridCoordinate, add_zOnly, add_yz, add_all]
  omega

/-- weightedCost is monotone under coordinate-wise flag dominance. -/
theorem weightedCost_mono
    {Omega : Type} [Field Omega]
    {G T H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
      surfaceFlag firstTailFlag)
    (C : RegularComponent Omega G T H)
    {f g : FlagDegree}
    (hz : f.zOnly ≤ g.zOnly) (hy : f.yz ≤ g.yz) (ha : f.all ≤ g.all) :
    B.weightedCost f C ≤ B.weightedCost g C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  gcongr

/-! ### Numeric gates for the cell coordinates -/

/-- The rational coordinate's yz-column in closed form. -/
theorem cellRational_yz (t y r : Nat) :
    (cellRational t y r).yz = 131074 * cellB y r + 2 := by
  simp only [cellRational, cellDirection, RCN206.directionFlag, w]
  omega

/-- The hybrid coordinate's yz-column in closed form. -/
theorem cellHybridCoordinate_yz (t y r : Nat) :
    (cellHybridCoordinate t y r).yz = 131074 * cellB y r + 65538 := by
  simp only [cellHybridCoordinate, add_yz, cellRational_yz, w]

/-- In the hybrid branch `r + 2 ≤ y` the atom `b = cellB y r` is positive, so any
    error cap below 131075 passes the rational gate. -/
theorem rationalGate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellRational t y r).yz := by
  rw [cellRational_yz]
  have hB : 1 ≤ cellB y r := by
    simp only [cellB]
    omega
  have := Nat.mul_le_mul_left 131074 hB
  omega

theorem tangentGate_of_rationalGate (t y r errorCap : Nat)
    (h : errorCap + 1 ≤ (cellRational t y r).yz) :
    errorCap + 1 ≤ (cellHybridCoordinate t y r).yz :=
  h.trans (cellRational_le_hybrid t y r).2.1

/-! ### Closed forms in the atoms (a, b, s) = (cellA t y, cellB y r, cellS r)

These match the subtraction-free shapes `sharpABS / rationalABS / hybABS /
mfibABS / mcutABS` used elsewhere in the Locator, so the hybrid bound can be
rewritten into that form by `hybridBound_eq`. -/

theorem cellSharpTail_eq (t y r : Nat) :
    cellSharpTail t y r =
      ⟨2 * cellA t y * 131072, 1 + (2 * cellB y r + 1) * 131072,
        (2 * cellS r + 3) * 131072⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellSharpTail, sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w] <;> omega

theorem cellRational_eq (t y r : Nat) :
    cellRational t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellRational, cellDirection, RCN206.directionFlag, w] <;> omega

theorem cellHybridCoordinate_eq (t y r : Nat) :
    cellHybridCoordinate t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 65536, 196608⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, w] <;> omega

theorem cellMovingFiber_eq (t y r : Nat) :
    cellMovingFiber t y r = ⟨cellA t y, cellB y r + 1, cellS r + 3⟩ := rfl

theorem cellMovingCut_eq (t y r : Nat) :
    cellMovingCut t y r =
      ⟨131072 * cellA t y + 2 * cellA t y,
        131072 * cellB y r + 2 * cellB y r + 2,
        131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 131072, 262144⟩ := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [cellMovingCut, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, w] <;> omega

/-- The hybrid bound in closed (a, b, s)-form. -/
theorem hybridBound_eq (flag : FlagDegree) (t y r : Nat) :
    flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) =
      flagMixed flag
          ⟨2 * cellA t y * 131072, 1 + (2 * cellB y r + 1) * 131072,
            (2 * cellS r + 3) * 131072⟩
          (⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 65536, 196608⟩) +
        131072 * flagMixed flag ⟨cellA t y, cellB y r + 1, cellS r + 3⟩
          (⟨131072 * cellA t y + 2 * cellA t y,
            131072 * cellB y r + 2 * cellB y r + 2,
            131072 * cellS r + 2 * cellS r + 3⟩ + ⟨0, 131072, 262144⟩) := by
  simp only [cellSharpTail_eq, cellHybridCoordinate_eq, cellMovingFiber_eq,
    cellMovingCut_eq, w]

end
end ProximityPrize.SubmissionLower.LocatorHybridCells
