import ProximityPrize.SubmissionLower.Part.G001_06
section Compact_PackedLocatorTail
section PackedLocator_LocatorHybridCells
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000



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
end PackedLocator_LocatorHybridCells

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




end
end ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProvider. -/
section PackedLocator_LocatorHybridTailProvider
/-
LOCATOR HYBRID TAIL PROVIDER (port of ContactHybridTailProvider6751Research, pr359).

Covers the `r + 2 ≤ y` ("hybrid second-surface") branch of `cellRegularCost`.
The delayed branch keeps the Locator's reduced-tail discharge (Q2.lean) verbatim.

§0 defines the *bounded* provider `HybridTailMultiplicityProvider`: it is
pr359's refactored `DelayedTailMultiplicityProvider` (an extra
`divisorBound` optParam and a single field `cost_sum_le : ∑ cost ≤ divisorBound`
in place of `cost_le`/`divisor_le`), kept as a NEW structure so that the
existing B3.lean structure and its constructors (Q2.lean, GZ.lean) stay
untouched.  `stage_card_le_divisorBound` is the generalized
`stage_card_le_flagMixed`.

Conclusion shape of §3:

  Nonempty (HybridTailMultiplicityProvider
    (tailFlag1 := cellSharpTail t y r) (tailFlag2 := cellHybridCoordinate t y r) S
    (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r)
      + (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)))

Caller-side obligations (discharged in LocatorHybridTailRealization.lean):
  B            : sharp unit family (activeNestedUnitFamily on T1 in the sharp
                 flag DIRECTLY — no congruent-cut transport)
  budget/hcost/hmovingSum : outputs of exists_firstTail_cut_budgets
  hresultants  : sharp-family certificate (activeNestedWeightedCertificate on T1)
  htangent     : the tangent count vs B.yzCost
  htangentGate / hrationalGate : numeric gates errors+1 ≤ hybrid.yz / rational.yz
                 (rational.yz = 131074·b + 2 ≥ 131076 whenever b ≥ 1, i.e. r+2 ≤ y).
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ### 0. The bounded provider (pr359's refactored DelayedTailMultiplicityProvider) -/

section BoundedProvider
variable {K0 Omega Iota : Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi : Polynomial K0 →+* Omega} {Gamma0 : Finset K0} {x0 : Iota → K0}
  {pchar errorCap d : ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2 : FlagDegree}
  {support0 : RCN275.ResidualSupportParameters}

structure HybridTailMultiplicityProvider
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound : optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily : PrimeFlagBudgetFamily
    (G := S.G) (T := globalTailCut phi S.F (d + 1))
    (H := regularitySurface phi S.F) flag0 tailFlag1
  multiplicity : FirstTailComponent S → ℕ
  cost : FirstTailComponent S → ℕ
  one_le_multiplicity : ∀ C, 1 ≤ multiplicity C
  tangentYZGate : errorCap + 1 ≤ tailFlag2.yz
  cost_sum_le : (∑ C, cost C) ≤ divisorBound
  componentBound : ∀ C,
    (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
      (regularitySurface phi S.F) Gamma0
      (selectedPoint phi S.selected) C).card ≤ cost C
  dichotomy : ∀ C,
    (∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
      globalTailCut phi S.F (d + 1 + delay) ∉ C.1) ∨
    ((∀ delay, globalTailCut phi S.F (d + 1 + delay) ∈ C.1) ∧
      (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
        (regularitySurface phi S.F) Gamma0
        (selectedPoint phi S.selected) C).card ≤
          (errorCap + 1) * budgetFamily.yzCost C)

/-- The generalized `stage_card_le_flagMixed`: any bounded provider bounds the
seed count by its `divisorBound`. -/
theorem stage_card_le_divisorBound
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound : ℕ}
    (P : HybridTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S divisorBound) :
    Gamma0.card ≤ divisorBound := by
  classical
  let T1 := globalTailCut phi S.F (d + 1)
  let H := regularitySurface phi S.F
  let point := selectedPoint phi S.selected
  have hG : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G = 0 := S.on_component
  have hT1 : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    exact selectedPoint_evaluation phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover : Gamma0.card ≤
      ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card :=
    card_le_sum_componentSeeds Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card ≤ ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card := hcover
    _ ≤ ∑ C : RegularComponent Omega S.G T1 H, P.cost C :=
      Finset.sum_le_sum (fun C _ ↦ P.componentBound C)
    _ ≤ divisorBound := P.cost_sum_le

end BoundedProvider

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 1. L1 — the delayed cut lands in mult • hybrid (mult ≥ 2)

Direct containment (no mod-G reduction): the (w+1+delay)-th tail cut lies in the
sharp flag at degree w+1+delay, and the three cumulative absorptions of
LocatorHybridCells push that into `mult • cellHybridCoordinate` whenever
1 ≤ delay ≤ mult and 2 ≤ mult. -/

theorem laterTail_in_hybridFlag
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinate t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  -- globalTailCut is definitionally surfaceMap of the agreement numerator with
  -- the tail selector, so the sharp containment applies directly.
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  -- rewrite the sharp cumulative sums into the subtraction-free atom form
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  -- hybrid cumulative sums in atom form
  have hhallV : (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3) + 196608) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_all, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_yz, add_all, nsmul_yz, nsmul_all, w]
    norm_num
    ring
  have hhtotV : (mult • cellHybridCoordinate t y r).zOnly +
      (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, w]
    norm_num
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all (cellA t y) (cellB y r) (cellS r) delay mult hdm hm2)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)

/-! ### 2. L2 — the multiplicity-1 moving count

For a component whose (w+2)-cut is proper, the seeds are bounded by
wc(rational) + (w+1)·movingCost, via the filteredCut decomposition of the (w+2)
cut and the MovingPoleBudget zero bound at C := center, k := w+1. -/

set_option maxHeartbeats 20000000 in
theorem component_hybrid_moving_card_le
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y) (_hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + 1) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hR : S.F.degreeOf 2 ≤ cellS r + 2 := by
    have h := Hsupport.coordinate_bounds.2.1
    simpa only [cellSupport, cellS, RCN198.support] using h
  have hYR : wt ![0, 1, 1, 0] S.F ≤ cellB y r + cellS r + 3 := by
    have h := Hsupport.ys_weight
    simpa only [residualYSWeights, cellSupport, cellB, cellS, RCN198.support] using h
  have hAll : wt ![0, 1, 1, 1] S.F ≤ cellA t y + cellB y r + cellS r + 3 := by
    have h := Hsupport.total_weight
    simpa only [residualTotalWeights, cellSupport, cellA, cellB, cellS,
      RCN198.support] using h
  obtain ⟨Bc, cf, heq, hcoeff, hclass⟩ :=
    globalTailCut_certificate (polynomialEmbedding K)
      (cellA t y) (cellB y r) (cellS r) S.F hR hYR hAll
      (w + 1) (Nat.le_add_left 1 w)
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (w + 1) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (w + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (w + 1)
      (center (cellA t y) (cellB y r) (cellS r)) Bc cf hHnot hA hcoeff hclass
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (filteredCut (w + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F))) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + 1)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + 1)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

/-! ### 3. The hybrid provider from a local DVR family -/


end
end ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorReplacement. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorDerivativeChain. -/
section PackedLocator_LocatorDerivativeChain

/-!
# Derivative chain for singular seeds

For an irreducible factor `F` with positive `R`-degree, a seed at which both `F`
and `∂_R F` specialise to zero is either a regular seed of some iterated
`R`-derivative `∂_R^j F` (`1 ≤ j`), or a zero of the `R`-free polynomial
`∂_R^m F` obtained when the `R`-degree is exhausted.  Regular seeds of a
derivative are counted by the coprime pair `(∂_R^j F, F)`; the `R`-free tail is
counted by the singular-seed bound at slope cap `1`, whose characteristic gate is
`2 * ((D - 1) / w) * L < p`.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Iterated `R`-derivative. -/
def dR (j : ℕ) (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (MvPolynomial.pderiv (2 : Fin 4))^[j] F

@[simp] theorem dR_zero (F : MvPolynomial (Fin 4) K) : dR 0 F = F := rfl

theorem dR_succ (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    dR (j + 1) F = MvPolynomial.pderiv (2 : Fin 4) (dR j F) := by
  unfold dR
  exact Function.iterate_succ_apply' _ _ _

/-- The `R`-derivative stays inside every coefficient box. -/
theorem pderiv_R_mem_box (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    MvPolynomial.pderiv (2 : Fin 4) Q ∈ globalCoefficientBox K D w L s := by
  intro d hd
  have hmem := support_before_pderiv (2 : Fin 4) Q d hd
  obtain ⟨ht, hs, hc⟩ := hbox hmem
  have h0 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 0 = d 0 := by
    simp [Finsupp.single_apply]
  have h1 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 1 = d 1 := by
    simp [Finsupp.single_apply]
  have h2 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 2 = d 2 + 1 := by
    simp [Finsupp.single_apply]
  have h3 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 3 = d 3 := by
    simp [Finsupp.single_apply]
  simp only [h0, h1, h2, h3] at ht hs hc
  have hw1 : (w - 1) * d 2 ≤ (w - 1) * (d 2 + 1) := Nat.mul_le_mul_left _ (by omega)
  exact ⟨by omega, by omega, by omega⟩

theorem dR_mem_box (j : ℕ) (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    dR j Q ∈ globalCoefficientBox K D w L s := by
  induction j with
  | zero => simpa using hbox
  | succ k ih =>
      rw [dR_succ]
      exact pderiv_R_mem_box _ D w L s ih

/-- Tighten only the `R`-slope coordinate of a coefficient box from an
independent bound on the polynomial's actual `R`-degree. -/
theorem mem_box_of_R_degree_le (Q : MvPolynomial (Fin 4) K) (D w L s s' : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hR : Q.degreeOf 2 ≤ s') :
    Q ∈ globalCoefficientBox K D w L s' := by
  intro d hd
  obtain ⟨ht, _, hz⟩ := hbox hd
  have hdR : d 2 ≤ Q.degreeOf 2 :=
    MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
  exact ⟨ht, hdR.trans hR, hz⟩

theorem dR_R_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [dR_succ]
      have h := pderiv_same_degree_bound (2 : Fin 4) (dR k F) (F.degreeOf 2 - k) ih
      omega

/-- A box with slope cap `s` and no `R`-dependence lies in the slope-`1` box. -/
theorem mem_box_slope_one (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hR : Q.degreeOf 2 = 0) :
    Q ∈ globalCoefficientBox K D w L 1 := by
  intro d hd
  obtain ⟨ht, _, hc⟩ := hbox hd
  have hd2 : d 2 ≤ Q.degreeOf 2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
  exact ⟨ht, by omega, hc⟩

/-- Exhaustion index of the `R`-degree along the derivative chain. -/
theorem exists_dR_R_degree_zero (F : MvPolynomial (Fin 4) K) :
    ∃ j, (dR j F).degreeOf 2 = 0 :=
  ⟨F.degreeOf 2, Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F)⟩

def chainLength (F : MvPolynomial (Fin 4) K) : ℕ :=
  Nat.find (exists_dR_R_degree_zero F)

theorem chainLength_spec (F : MvPolynomial (Fin 4) K) :
    (dR (chainLength F) F).degreeOf 2 = 0 :=
  Nat.find_spec (exists_dR_R_degree_zero F)

theorem chainLength_le (F : MvPolynomial (Fin 4) K) : chainLength F ≤ F.degreeOf 2 :=
  Nat.find_min' (exists_dR_R_degree_zero F)
    (Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F))

theorem dR_R_degree_pos_of_lt_chainLength (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hj : j < chainLength F) : 0 < (dR j F).degreeOf 2 :=
  Nat.pos_of_ne_zero (Nat.find_min (exists_dR_R_degree_zero F) hj)

theorem chainLength_pos (F : MvPolynomial (Fin 4) K) (hpos : 0 < F.degreeOf 2) :
    1 ≤ chainLength F := by
  by_contra h
  have h0 : chainLength F = 0 := by omega
  have := chainLength_spec F
  rw [h0] at this
  simp at this
  omega

theorem dR_ne_zero (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : F.degreeOf 2 < p) (j : ℕ) (hj : j ≤ chainLength F) : dR j F ≠ 0 := by
  induction j with
  | zero => simpa using hF
  | succ k ih =>
      rw [dR_succ]
      have hk : k < chainLength F := by omega
      have hpos := dR_R_degree_pos_of_lt_chainLength F k hk
      have hle : (dR k F).degreeOf 2 < p := by
        have := dR_R_degree_le k F
        omega
      exact R_derivative_nonzero (dR k F) p hpos hle

/-- Seeds along the chain: either some derivative is regular, or every
derivative up to the exhaustion index vanishes. -/
theorem chain_split (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (h0 : specialization K P γ F = 0)
    (h1 : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    (∃ j, 1 ≤ j ∧ j < m ∧ RegularSolution (dR j F) P γ) ∨
      (∀ i ≤ m, specialization K P γ (dR i F) = 0) := by
  induction m with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        right
        intro i hi
        interval_cases i
        · simpa using h0
        · rw [dR_succ]; simpa using h1
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
        rcases ih hk1 with ⟨j, hj1, hjk, hreg⟩ | hall
        · exact Or.inl ⟨j, hj1, by omega, hreg⟩
        · by_cases hnext : specialization K P γ (dR (k + 1) F) = 0
          · right
            intro i hi
            rcases Nat.lt_or_ge i (k + 1) with hlt | hge
            · exact hall i (by omega)
            · have : i = k + 1 := by omega
              subst this
              exact hnext
          · left
            refine ⟨k, hk1, by omega, hall k le_rfl, ?_⟩
            rw [← dR_succ]
            exact hnext

/-- A regular seed of `G` is a regular seed of one of its irreducible factors
of positive `R`-degree. -/
theorem exists_regular_positive_factor (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (P : Polynomial K) (γ : K) (hreg : RegularSolution G P γ) :
    ∃ F' ∈ positiveRFactors G, RegularSolution F' P γ := by
  classical
  let ψ : MvPolynomial (Fin 4) K →+* Polynomial K := (specialization K P γ).toRingHom
  obtain ⟨F', hmem, hzero⟩ := exists_normalized_factor_of_map_zero ψ G hG hreg.1
  have hdiv : F' ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
  have hregF' : ψ (MvPolynomial.pderiv (2 : Fin 4) F') ≠ 0 :=
    factor_derivative_regular_at_zero ψ G F' hdiv hzero hreg.2
  have hpos : 0 < F'.degreeOf 2 := by
    apply Nat.pos_of_ne_zero
    intro hzeroDeg
    apply hregF'
    rw [pderiv_zero_of_degree_zero (2 : Fin 4) F' hzeroDeg, map_zero]
  have hactive : F' ∈ activeFactors G := by
    unfold activeFactors
    exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem, by omega⟩
  refine ⟨F', ?_, hzero, hregF'⟩
  unfold positiveRFactors
  exact Finset.mem_filter.mpr ⟨hactive, hpos⟩

/-- Every seed of `Q` is a seed of an active irreducible factor of `Q`. -/
theorem exists_active_factor_of_solution (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (γ : K) (hsol : specialization K P γ Q = 0) :
    ∃ F ∈ activeFactors Q, specialization K P γ F = 0 := by
  classical
  let φ := polynomialEmbedding K
  let v : Fin 3 → GenericField K := fun i => initialPoint K P γ i.succ
  have heval (F : MvPolynomial (Fin 4) K) :
      MvPolynomial.eval v (surfaceMap φ F) = 0 ↔ specialization K P γ F = 0 := by
    simpa only [canonical_geometricSurfaceMap] using
      (actual_generic_initial_zero_iff K P γ F)
  obtain ⟨F, hF, hz⟩ := exists_active_factor_of_surface_zero φ
    (polynomialEmbedding_injective K) Q hQ v ((heval Q).mpr hsol)
  exact ⟨F, hF, (heval F).mp hz⟩

theorem irreducible_not_dvd_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : ¬ F ∣ dR j F := by
  intro hdiv
  have hne : dR j F ≠ 0 := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hle := degreeOf_le_of_dvd (2 : Fin 4) F (dR j F) hdiv hne
  have hdeg := dR_R_degree_le j F
  omega

theorem isRelPrime_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : IsRelPrime (dR j F) F :=
  (hF.isRelPrime_iff_not_dvd.mpr (irreducible_not_dvd_dR F hF p hpos hsmall j hj1 hj)).symm

section Counting

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Seeds that are regular for `dR j F` and at which `F` vanishes. -/
def chainSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => RegularSolution (dR j F) (selected γ) γ ∧
    specialization K (selected γ) γ F = 0

/-- Seeds of the `R`-free tail of the chain of `F`. -/
def tailSeeds (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (dR (chainLength F) F) = 0

/-- Product of the `R`-free active factors of `Q`. -/
def rfreeProduct (Q : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∏ F ∈ (activeFactors Q).filter (fun F => F.degreeOf 2 = 0), F

def rfreeSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (rfreeProduct Q) = 0


theorem tailSeeds_subset (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    tailSeeds F selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    rfreeSeeds Q selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeProduct_dvd (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ∣ Q := by
  classical
  unfold rfreeProduct
  exact (Finset.prod_dvd_prod_of_subset _ (activeFactors Q) id
    (Finset.filter_subset _ _)).trans (activeFactors_product_dvd Q hQ)

theorem rfreeProduct_ne_zero (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ≠ 0 :=
  ne_zero_of_dvd_ne_zero hQ (rfreeProduct_dvd Q hQ)

theorem rfreeProduct_R_degree (Q : MvPolynomial (Fin 4) K) :
    (rfreeProduct Q).degreeOf 2 = 0 := by
  classical
  unfold rfreeProduct
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  apply Nat.le_of_eq
  apply Finset.sum_eq_zero
  intro F hF
  exact (Finset.mem_filter.mp hF).2

/-- Every seed of `Q` lies in the regular pair seeds, the chain seeds, the tail
seeds or the `R`-free seeds. -/
theorem cover (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q =>
          regularPairSeeds Q T selected Gamma F) ∪
        ((positiveRFactors Q).biUnion fun F =>
          (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
        ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma := by
  classical
  intro γ hγ
  obtain ⟨F, hFactive, hFzero⟩ :=
    exists_active_factor_of_solution Q hQ (selected γ) γ (hQsolution γ hγ)
  by_cases hRfree : F.degreeOf 2 = 0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr ⟨hγ, ?_⟩
    have hdiv : F ∣ rfreeProduct Q := by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hFactive, hRfree⟩)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, map_mul, hFzero, zero_mul]
  · have hpos : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero hRfree
    have hFpos : F ∈ positiveRFactors Q := by
      unfold positiveRFactors
      exact Finset.mem_filter.mpr ⟨hFactive, hpos⟩
    by_cases hreg : specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    · have hm := chainLength_pos F hpos
      rcases chain_split F (selected γ) γ hFzero hreg (chainLength F) hm with
        ⟨j, hj1, hjm, hjreg⟩ | hall
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr ⟨F, hFpos, ?_⟩
        apply Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjm⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hγ, hjreg, hFzero⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr ⟨F, hFpos, ?_⟩
        exact Finset.mem_filter.mpr ⟨hγ, hall (chainLength F) le_rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr ⟨⟨F, hFpos⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hγ, ⟨hFzero, hreg⟩, hTsolution γ hγ⟩

/-- The chain seeds at stage `j` are covered by the regular pair seeds of
`(dR j F, F)`. -/
theorem chainSeeds_subset_regularPairSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hne : dR j F ≠ 0) (selected : K → Polynomial K) (Gamma : Finset K) :
    chainSeeds F j selected Gamma ⊆
      Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
        regularPairSeeds (dR j F) F selected Gamma F' := by
  classical
  intro γ hγ
  obtain ⟨hγΓ, hreg, hFzero⟩ := Finset.mem_filter.mp hγ
  obtain ⟨F', hF'mem, hF'reg⟩ :=
    exists_regular_positive_factor (dR j F) hne (selected γ) γ hreg
  apply Finset.mem_biUnion.mpr ⟨⟨F', hF'mem⟩, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨hγΓ, hF'reg, hFzero⟩

theorem chainSeeds_card_le
    (Pc : UnequalParameters) (Q F : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hF : F ∈ positiveRFactors Q) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (D w L s p : ℕ) [CharP K p] (hsmall : s < p) (hw : 1 ≤ w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcgap : 0 < Pc.gap)
    (hcY : (D - 1) / w ≤ Pc.leftY) (hcR : F.degreeOf 2 - j ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR) (hcZ' : L ≤ Pc.rightZ)
    (hleftR : 1 ≤ Pc.leftR)
    (hleftYSmall : Pc.leftY < p) (hleftRSmall : Pc.leftR < p) (hleftZSmall : Pc.leftZ < p)
    (hmixedYSmall : Pc.mixedCost.y < p) (hmixedRSmall : Pc.mixedCost.r < p)
    (hmixedZSmall : Pc.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = Pc.n)
    (hPw : 1 ≤ Pc.w) (hchar : Pc.w < p) (hwa : Pc.w < Pc.a) (han : Pc.a ≤ Pc.n)
    (hdegree : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hagreement : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors) :
    (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
  classical
  obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
  have hFsmall : F.degreeOf 2 < p := by
    have := degreeOf_R_le_of_mem_box F D w L s hFbox
    omega
  have hne : dR j F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall j hj
  have hrel : IsRelPrime (dR j F) F := isRelPrime_dR F hFirr p hFpos hFsmall j hj1 hj
  have hdR : (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := dR_R_degree_le j F
  have hbox' : dR j F ∈ globalCoefficientBox K D w L (F.degreeOf 2 - j) :=
    mem_box_of_R_degree_le (dR j F) D w L s (F.degreeOf 2 - j)
      (dR_mem_box j F D w L s hFbox) hdR
  have hFcaps := degree_bounds_of_mem_box F D w L s (by omega) hFbox
  have hsub := chainSeeds_subset_regularPairSeeds F j hne selected Gamma
  have hcount := all_regularPairSeeds_bound Pc (dR j F) F hne hrel D w L
      (F.degreeOf 2 - j) p hbox' hw
    hcY hcR hcZ (hFcaps.1.trans hcY') (hFcaps.2.1.trans hcR') (hFcaps.2.2.trans hcZ')
    hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hPw hchar hwa han hdegree hagreement hnoPencil
  have hsum := sum_regular_counts_bound Pc (dR j F) F selected Gamma
    (regularVector_budgets Pc (dR j F) hne D w L (F.degreeOf 2 - j) (by omega)
      hbox' hcY hcR hcZ) hcount
  have hcap : (∑ F' : RegularIndex (dR j F),
      (regularPairSeeds (dR j F) F selected Gamma F').card) ≤ Pc.regularCountCap :=
    Pc.regular_count_le _ hcgap hsum
  calc (chainSeeds F j selected Gamma).card
      ≤ (Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
          regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_le_card hsub
    _ ≤ ∑ F' : RegularIndex (dR j F),
          (regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_biUnion_le
    _ ≤ Pc.regularCountCap := hcap

/-- `regularVector_budgets` with the LEFT Y-budget taken from the actual Y-degree of `Q`
rather than from the kernel box. -/
theorem regularVector_budgets'
    (P : UnequalParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hY : Q.degreeOf 1 ≤ P.leftY)
    (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ) :
    (∑ F : RegularIndex Q, (regularVector P F.1).y) ≤ P.mixedCost.y ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).r) ≤ P.mixedCost.r ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).z) ≤ P.mixedCost.z := by
  classical
  have hb := directFactor_input_budgets Q hQ D w L s hw hbox
  have hbY0 := (separated_degree_budgets_of_prod_dvd (positiveRFactors Q) id Q hQ
    (positiveRFactors_product_dvd Q hQ)).1
  have hbY : (∑ F : RegularIndex Q, F.1.degreeOf (1 : Fin 4)) ≤ Q.degreeOf 1 := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    simpa using hbY0
  have hbR : (∑ F : RegularIndex Q, F.1.degreeOf (2 : Fin 4)) ≤ s := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    exact hb.2.1
  have hbZ : (∑ F : RegularIndex Q, F.1.degreeOf (3 : Fin 4)) ≤ L := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    exact hb.2.2
  simp only [regularVector, Finset.sum_add_distrib]
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightZ (hbR.trans hR))
      (Nat.mul_le_mul_right P.rightR (hbZ.trans hZ))
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightZ (hbY.trans hY))
      (Nat.mul_le_mul_right P.rightY (hbZ.trans hZ))
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightR (hbY.trans hY))
      (Nat.mul_le_mul_right P.rightY (hbR.trans hR))

/-- `all_regularPairSeeds_bound` with the LEFT Y-budget taken from `Q.degreeOf 1`. -/
theorem all_regularPairSeeds_bound'
    (P : UnequalParameters) (Q T : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (D w L s p : ℕ) [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hwBox : 1 ≤ w)
    (hY : Q.degreeOf 1 ≤ P.leftY)
    (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY)
    (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p)
    (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u₀ u₁ : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n)
    (hw : 1 ≤ P.w) (hchar : P.w < p) (hwa : P.w < P.a)
    (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u₀ i + gamma * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    ∀ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * RCN294.dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z := by
  intro F
  have hFbox := (directFactor_data Q F.1 hQ D w L s hbox F.2).2.2
  have hFcaps := degree_bounds_of_mem_box F.1 D w L s hwBox hFbox
  have hFY : F.1.degreeOf 1 ≤ Q.degreeOf 1 :=
    degreeOf_le_of_dvd 1 F.1 Q (positiveRFactors_spec Q F.1 F.2).2.1 hQ
  exact regularPairSeeds_bound P Q T hrel F p
    (hFY.trans hY)
    (hFcaps.2.1.trans hR) (hFcaps.2.2.trans hZ)
    hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u₀ u₁
    hinj hnodes hw hchar hwa han hdegree hagreement hnoPencil

theorem pderiv_other_degree_le (i j : Fin 4) (hij : j ≠ i) (P : MvPolynomial (Fin 4) K) :
    (MvPolynomial.pderiv i P).degreeOf j ≤ P.degreeOf j := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hh := (MvPolynomial.degreeOf_le_iff (n := j) (f := P) (d := P.degreeOf j)).mp le_rfl
    (d + Finsupp.single i 1) (support_before_pderiv i P d hd)
  simpa [Finsupp.add_apply, Finsupp.single_apply, hij.symm] using hh

theorem dR_Y_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    (dR j F).degreeOf 1 ≤ F.degreeOf 1 := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [dR_succ]
      exact (pderiv_other_degree_le 2 1 (by decide) _).trans ih

/-- `chainSeeds_card_le` with the Y-budgets and the RIGHT slope taken from the factor `F`
itself instead of the kernel box of `Q`. -/
theorem chainSeeds_card_le'
    (Pc : UnequalParameters) (Q F : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hF : F ∈ positiveRFactors Q) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (D w L s p : ℕ) [CharP K p] (hsmall : s < p) (hw : 1 ≤ w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcgap : 0 < Pc.gap)
    (hcY : F.degreeOf 1 ≤ Pc.leftY) (hcR : F.degreeOf 2 - j ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : F.degreeOf 1 ≤ Pc.rightY) (hcR' : F.degreeOf 2 ≤ Pc.rightR) (hcZ' : L ≤ Pc.rightZ)
    (hleftR : 1 ≤ Pc.leftR)
    (hleftYSmall : Pc.leftY < p) (hleftRSmall : Pc.leftR < p) (hleftZSmall : Pc.leftZ < p)
    (hmixedYSmall : Pc.mixedCost.y < p) (hmixedRSmall : Pc.mixedCost.r < p)
    (hmixedZSmall : Pc.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = Pc.n)
    (hPw : 1 ≤ Pc.w) (hchar : Pc.w < p) (hwa : Pc.w < Pc.a) (han : Pc.a ≤ Pc.n)
    (hdegree : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hagreement : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors) :
    (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
  classical
  obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
  have hFsmall : F.degreeOf 2 < p := by
    have := degreeOf_R_le_of_mem_box F D w L s hFbox
    omega
  have hne : dR j F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall j hj
  have hrel : IsRelPrime (dR j F) F := isRelPrime_dR F hFirr p hFpos hFsmall j hj1 hj
  have hdR : (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := dR_R_degree_le j F
  have hbox' : dR j F ∈ globalCoefficientBox K D w L (F.degreeOf 2 - j) :=
    mem_box_of_R_degree_le (dR j F) D w L s (F.degreeOf 2 - j)
      (dR_mem_box j F D w L s hFbox) hdR
  have hFcaps := degree_bounds_of_mem_box F D w L s (by omega) hFbox
  have hYleft : (dR j F).degreeOf 1 ≤ Pc.leftY := (dR_Y_degree_le j F).trans hcY
  have hsub := chainSeeds_subset_regularPairSeeds F j hne selected Gamma
  have hcount := all_regularPairSeeds_bound' Pc (dR j F) F hne hrel D w L
      (F.degreeOf 2 - j) p hbox' hw
    hYleft hcR hcZ hcY' hcR' (hFcaps.2.2.trans hcZ')
    hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hPw hchar hwa han hdegree hagreement hnoPencil
  have hsum := sum_regular_counts_bound Pc (dR j F) F selected Gamma
    (regularVector_budgets' Pc (dR j F) hne D w L (F.degreeOf 2 - j) (by omega)
      hbox' hYleft hcR hcZ) hcount
  have hcap : (∑ F' : RegularIndex (dR j F),
      (regularPairSeeds (dR j F) F selected Gamma F').card) ≤ Pc.regularCountCap :=
    Pc.regular_count_le _ hcgap hsum
  calc (chainSeeds F j selected Gamma).card
      ≤ (Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
          regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_le_card hsub
    _ ≤ ∑ F' : RegularIndex (dR j F),
          (regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_biUnion_le
    _ ≤ Pc.regularCountCap := hcap


/-- Seeds of a nonzero `R`-free polynomial in the slope-`1` box are bounded by
the singular-seed count of the slope-`1` Tight parameters. -/
theorem rfree_seed_count_le
    (S : TightParameters) (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0)
    (p : ℕ) [CharP K p]
    (hbox : J ∈ globalCoefficientBox K S.D S.w S.L S.s) (hJR : J.degreeOf 2 = 0) (hSs : S.s = 1)
    (hp : 1 < p) (hw : 1 ≤ S.w) (hchar : S.w < p) (hDw : S.w < S.kappa * S.D)
    (hj : 1 ≤ S.algebraicCap) (hjYSmall : S.implicitYCap < p) (hjZSmall : S.algebraicCap < p)
    (hmixedSmall : 2 * S.implicitYCap * S.algebraicCap < p)
    (hwa : S.w < S.a) (han : S.a ≤ S.n)
    (selected : K → Polynomial K) (Delta : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = S.n)
    (hdegree : ∀ γ ∈ Delta, (selected γ).natDegree ≤ S.w)
    (hsol : ∀ γ ∈ Delta, specialization K (selected γ) γ J = 0)
    (hagreement : ∀ γ ∈ Delta, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta S.w S.errors) :
    Delta.card ≤ S.countCap := by
  classical
  have hs1 : 1 ≤ S.s := by omega
  have hsp : S.s < p := by omega
  have hcover := card_le_regular_sum_add_singular J J hJ S.D S.w S.L S.s p
    hs1 hsp hw (by simpa [TightParameters.kappa] using hDw)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hj)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hjZSmall)
    hbox selected Delta hsol hsol
  have hregZero : (∑ F' : RegularIndex J, (regularPairSeeds J J selected Delta F').card) = 0 := by
    apply Finset.sum_eq_zero
    intro F' _
    exfalso
    obtain ⟨_, hdvd, hpos⟩ := positiveRFactors_spec J F'.1 F'.2
    have := degreeOf_le_of_dvd (2 : Fin 4) F'.1 J hdvd hJ
    omega
  have hsingularOld := RCN292.TightParameters.singularSeeds_count_le_countCap
    S J hJ hbox hs1 hsp hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
    hwa han selected Delta nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  have hsingular : (RCN052.singularSeeds J selected Delta).card ≤ S.countCap := by
    change (RCN291.singularSeeds J selected Delta).card ≤ S.countCap
    exact hsingularOld
  omega

end Counting

section Assembly

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

theorem sum_chainLength_sub_one_le (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s : ℕ) (hw : 0 < w) (hs : 1 ≤ s)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) ≤ s - 1 ∧
      (positiveRFactors Q).card ≤ s := by
  classical
  have hbudget := (directFactor_input_budgets Q hQ D w L s hw hbox).2.1
  have hpos : ∀ F ∈ positiveRFactors Q, 1 ≤ F.degreeOf 2 :=
    fun F hF => (positiveRFactors_spec Q F hF).2.2
  have hcard : (positiveRFactors Q).card ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
    calc (positiveRFactors Q).card = ∑ _F ∈ positiveRFactors Q, (1 : ℕ) := by simp
      _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := Finset.sum_le_sum hpos
  have hsub : (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) + (positiveRFactors Q).card ≤
      ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
    calc (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) + (positiveRFactors Q).card
        = ∑ F ∈ positiveRFactors Q, ((chainLength F - 1) + 1) := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
          apply Finset.sum_le_sum
          intro F hF
          have h1 := hpos F hF
          have h2 := chainLength_le F
          omega
  refine ⟨?_, hcard.trans hbudget⟩
  by_cases hempty : (positiveRFactors Q).card = 0
  · rw [Finset.card_eq_zero] at hempty
    simp [hempty]
  · omega

theorem residual_chain_count_le
    (P : UnequalParameters) (Pc : ℕ → UnequalParameters) (S : TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hgap : 0 < P.gap) (hY : (D - 1) / w ≤ P.leftY) (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY) (hTR : T.degreeOf 2 ≤ P.rightR) (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR) (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p) (hmixedYSmall : P.mixedCost.y < p)
    (hmixedRSmall : P.mixedCost.r < p) (hmixedZSmall : P.mixedCost.z < p)
    (hcmono : Monotone (fun t => (Pc t).regularCountCap))
    (hcgap : ∀ t, 0 < (Pc t).gap) (hcY : ∀ t, (D - 1) / w ≤ (Pc t).leftY)
    (hcR : ∀ t, t ≤ s → t ≤ (Pc t).leftR) (hcZ : ∀ t, L ≤ (Pc t).leftZ)
    (hcY' : ∀ t, (D - 1) / w ≤ (Pc t).rightY) (hcR' : ∀ t, s ≤ (Pc t).rightR)
    (hcZ' : ∀ t, L ≤ (Pc t).rightZ)
    (hcleftR : ∀ t, 1 ≤ (Pc t).leftR) (hcleftYSmall : ∀ t, (Pc t).leftY < p)
    (hcleftRSmall : ∀ t, (Pc t).leftR < p)
    (hcleftZSmall : ∀ t, (Pc t).leftZ < p) (hcmixedYSmall : ∀ t, (Pc t).mixedCost.y < p)
    (hcmixedRSmall : ∀ t, (Pc t).mixedCost.r < p) (hcmixedZSmall : ∀ t, (Pc t).mixedCost.z < p)
    (htailLe : S.countCap ≤ (Pc 1).regularCountCap)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p) (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesP : nodes.card = P.n) (hnodesC : ∀ t, nodes.card = (Pc t).n)
    (hnodesS : nodes.card = S.n)
    (hPw : 1 ≤ P.w) (hPchar : P.w < p) (hPwa : P.w < P.a) (hPan : P.a ≤ P.n)
    (hCw : ∀ t, 1 ≤ (Pc t).w) (hCchar : ∀ t, (Pc t).w < p) (hCwa : ∀ t, (Pc t).w < (Pc t).a)
    (hCan : ∀ t, (Pc t).a ≤ (Pc t).n)
    (hdegreeP : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ P.w)
    (hdegreeC : ∀ t, ∀ γ ∈ Gamma, (selected γ).natDegree ≤ (Pc t).w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementP : ∀ γ ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementC : ∀ t, ∀ γ ∈ Gamma, (Pc t).a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilP : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hnoPencilC : ∀ t, NoLargeSelectedPencil selected Gamma (Pc t).w (Pc t).errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma.card ≤ P.regularCountCap
      + ChainAmort.capSum (fun t => (Pc t).regularCountCap) s + 2 * S.countCap := by
  classical
  -- regular pairs
  have hregular := all_regularPairSeeds_bound P Q T hQ hrel D w L s p hbox hw hY hR hZ
    hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall
    hmixedZSmall selected Gamma nodes x u0 u1 hinj hnodesP hPw hPchar hPwa hPan
    hdegreeP hagreementP hnoPencilP
  have hregSum := sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ D w L s (by omega) hbox hY hR hZ) hregular
  have hregCap : (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) ≤
      P.regularCountCap := P.regular_count_le _ hgap hregSum
  -- cover
  have hRcap : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q T hQ p s hsmall hRcap selected Gamma hQsolution hTsolution
  -- chain seeds
  have hchain : ∀ F ∈ positiveRFactors Q, ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ (Pc (F.degreeOf 2 - j)).regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    have hFd : F.degreeOf 2 ≤ s :=
      degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
    exact chainSeeds_card_le (Pc (F.degreeOf 2 - j)) Q F hQ hF j hj1 hjm.le D w L s p hsmall hw
      hbox (hcgap _) (hcY _) (hcR _ (by omega)) (hcZ _) (hcY' _) (hcR' _) (hcZ' _) (hcleftR _)
      (hcleftYSmall _) (hcleftRSmall _) (hcleftZSmall _)
      (hcmixedYSmall _) (hcmixedRSmall _) (hcmixedZSmall _)
      selected Gamma nodes x u0 u1 hinj (hnodesC _)
      (hCw _) (hCchar _) (hCwa _) (hCan _) (hdegreeC _) (hagreementC _) (hnoPencilC _)
  -- tail seeds
  have htail : ∀ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card ≤ S.countCap := by
    intro F hF
    obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
    have hFsmall : F.degreeOf 2 < p := by
      have := degreeOf_R_le_of_mem_box F D w L s hFbox
      omega
    have hJ : dR (chainLength F) F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall _ le_rfl
    have hJbox : dR (chainLength F) F ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s (dR_mem_box _ F D w L s hFbox) (chainLength_spec F)
    refine rfree_seed_count_le S _ hJ p hJbox (chainLength_spec F) hSs hp (by omega) hSchar
      hSDw hSj hSY hSZ hSmixed hSwa hSan selected (tailSeeds F selected Gamma) nodes x u0 u1
      hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (tailSeeds_subset F selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (tailSeeds_subset F selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (tailSeeds_subset F selected Gamma) hnoPencilS
  -- R-free seeds
  have hrfree : (rfreeSeeds Q selected Gamma).card ≤ S.countCap := by
    have hJ := rfreeProduct_ne_zero Q hQ
    have hJbox : rfreeProduct Q ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s
        (mem_globalCoefficientBox_of_dvd _ Q D w L s hQ (rfreeProduct_dvd Q hQ) hbox)
        (rfreeProduct_R_degree Q)
    refine rfree_seed_count_le S _ hJ p hJbox (rfreeProduct_R_degree Q) hSs hp (by omega)
      hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected (rfreeSeeds Q selected Gamma) nodes
      x u0 u1 hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (rfreeSeeds_subset Q selected Gamma) hnoPencilS
  -- budgets
  obtain ⟨hsumChain, hcardPos⟩ := sum_chainLength_sub_one_le Q hQ D w L s (by omega) hs hbox
  -- cardinalities of the four parts
  have hA : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ P.regularCountCap :=
    Finset.card_biUnion_le.trans hregCap
  have hdeg : (∑ F ∈ positiveRFactors Q, F.degreeOf 2) ≤ s :=
    (directFactor_input_budgets Q hQ D w L s (by omega) hbox).2.1
  have hpos1 : ∀ F ∈ positiveRFactors Q, 1 ≤ F.degreeOf 2 :=
    fun F hF => (positiveRFactors_spec Q F hF).2.2
  have hrow : ∀ F ∈ positiveRFactors Q,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        + (tailSeeds F selected Gamma).card ≤
      ChainAmort.capSumT (fun t => (Pc t).regularCountCap) S.countCap (F.degreeOf 2) := by
    intro F hF
    have h1 : ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
        chainSeeds F j selected Gamma).card ≤
        ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card :=
      Finset.card_biUnion_le
    have h2 : ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card ≤
        ChainAmort.capSum (fun t => (Pc t).regularCountCap) (F.degreeOf 2) :=
      le_trans (Finset.sum_le_sum fun j hj => hchain F hF j hj)
        (ChainAmort.chain_row_le (fun t => (Pc t).regularCountCap)
          (F.degreeOf 2) (chainLength F) (chainLength_le F))
    have h4 := htail F hF
    unfold ChainAmort.capSumT
    omega
  have hsumrow : ∑ F ∈ positiveRFactors Q,
      (((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        + (tailSeeds F selected Gamma).card) ≤
      ChainAmort.capSumT (fun t => (Pc t).regularCountCap) S.countCap s :=
    le_trans (Finset.sum_le_sum hrow)
      (ChainAmort.sum_capSumT_le (fun t => (Pc t).regularCountCap) hcmono S.countCap htailLe
        (positiveRFactors Q) (fun F => F.degreeOf 2) s hpos1 hdeg)
  rw [Finset.sum_add_distrib] at hsumrow
  unfold ChainAmort.capSumT at hsumrow
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q,
        ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
          chainSeeds F j selected Gamma).card := Finset.card_biUnion_le
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
  have hunion := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F)
    ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma)
  omega

end Assembly

end

end ProximityPrize.SubmissionLower.LocatorDerivativeChain
end PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedChain. -/
section PackedLocator_LocatorFixedChain
/-!
# Derivative chain on the fixed stage

`LocatorDerivativeChain.residual_chain_count_le` counts the seeds of a
polynomial `Q` by its regular seeds (through a coprime partner `T`), the
derivative-chain pairs `(∂_R^j F, F)` of its positive-slope factors, and the
R-free tails.  On the fixed stage the regular seeds of the common divisor `H`
are already charged by the phase certificate through
`LocatorFixedConsumer.initial_A_regularSeeds_sum_le`, so this file restates that
lemma with `T := Q` and the regular block replaced by a hypothesis: no second
polynomial of the selected pair is needed.  The chain pairs are coprime by the
R-degree drop (`isRelPrime_dR`) and, as in `chainSeeds_card_le`, the
differentiated left factor only needs slope `s - 1`; the tails use
`card_le_regular_sum_add_singular J J`.  The only new mathematics is the
inclusion `regularPairSeeds Q Q ⊆ regularSeeds Q`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135
  RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 RCN140 LocatorDerivativeChain

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- With `T := Q`, the regular pair seeds of `(Q, Q)` are the regular seeds of the
factors of `Q` (RCN140.regularSeeds, the set the grid bounds by `bound`). -/
theorem regularPairSeeds_self_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (F : RegularIndex Q) :
    regularPairSeeds Q Q selected Gamma F ⊆ regularSeeds Q selected Gamma F := by
  intro γ hγ
  simp only [regularPairSeeds, regularSeeds, Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, hγ.2.1⟩
end
end ProximityPrize.SubmissionLower.LocatorFixedChain
end PackedLocator_LocatorFixedChain
end Compact_PackedLocatorTail
