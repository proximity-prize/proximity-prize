/-
HYBRID-BRANCH PROVIDER (Path B) — draft for integration.

Covers ONLY the `r + 2 ≤ y` branch of `cellRegularCost`. The delayed branch keeps
its existing reduced-tail1 discharge verbatim (Path B ruling).

Conclusion shape (against the refactored DelayedTailMultiplicityProvider with
`divisorBound` optParam and `cost_sum_le`):

  Nonempty (DelayedTailMultiplicityProvider
    (tailFlag1 := cellSharpTail t y r) (tailFlag2 := cellHybridCoordinate t y r) S
    (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r)
      + (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)))

Caller-side obligations (mirroring the reduced path's realization):
  B            : sharp unit family (exists_adaptiveUnitProjectionFamily_of_nested /
                 exists_firstTail_cut_budgets `unit`, T1 in sharp DIRECTLY —
                 no congruent-cut transport)
  budget/hcost/hmovingSum : outputs of exists_firstTail_cut_budgets
  hresultants  : sharp-family certificate (activeNestedWeightedCertificate on T1
                 directly, or transport — caller's choice)
  htangent     : the tangent count vs B.yzCost (CellTangentProviderD6750-style)

Numeric gates (pre-verified in the model, all cells with r+2 <= y):
  htangentGate : errors+1 <= hybrid.yz   (>= 197000 when b >= 1)
  hrationalGate: errors+1 <= rational.yz (>= 131076 when b >= 1)

NOTE on names: `cellSharpTail` is the sharp (w+1) flag
  sharpResidualAgreementFlag (cellSupport t y r) (w+1);
if your def is named differently, sed accordingly.
-/
import ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research
import ProximityPrize.SubmissionLower.ContactFirstTailBudget6731Research
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

namespace ProximityPrize.SubmissionLower
namespace ContactHybridTailProvider6751Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research ContactTwoTailRecurrence6731Research
open ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research
open ContactMovingCurveBudget6719Research
open ContactRegularZeroBudget6676Research
open ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research
open ContactTaylorNumerators
open ContactWeakSeparableSeparatorResearch
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactTwoTailResultantProvider6732Research
open ContactRouterCellCosts6750Research
open ContactTwoTailParameters6750Research
open ContactTranslation ContactInterpolation
open ContactTwoTailTangentCost6732Research
open ContactMovingProjection6676Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]

/-! ### 1. Pure flag arithmetic

All four lemmas are subtraction-free: they are stated over the cell atoms
a = cellA t y, b = cellB y r, s = cellS r (so t = a+b+s+3, y = b+s+3, r = s+2),
where the branch hypothesis r+2 <= y gives b >= 1 — not needed for the
absorption calcs, only for the gates. -/

/-- z-cumulative absorption: sharp.all ≤ (mult • hybrid).all.
    sharp.all = (2s+3)·d with d = (w+1)+delay; hybrid.all = (w+1)s+(2s+3)+3((w+1)/2). -/
private theorem sharp_absorbs_all (a b s delay mult : ℕ)
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
private theorem sharp_absorbs_ysall (a b s delay mult : ℕ)
    (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
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
private theorem sharp_absorbs_total (a b s delay mult : ℕ)
    (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
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
  simp only [center, direction, unitYZFlag, cellRational, cellDirection,
    ContactMovingPositiveLedger6719Research.directionFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  congr 1 <;> ring

private theorem flag_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g; simp_all

/-- cellMovingCut = center + (w+1) • surfaceFlag — the flag under which
    exists_firstTail_cut_budgets bounds the movingCost sum. -/
theorem cellMovingCut_eq_center_add (t y r : Nat) :
    cellMovingCut t y r =
      center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) •
          ContactMovingPositiveLedger6719Research.surfaceFlag
            (cellA t y) (cellB y r) (cellS r) := by
  simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
    cellDirection, ContactMovingPositiveLedger6719Research.directionFlag,
    ContactMovingPositiveLedger6719Research.surfaceFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
      cellDirection, ContactMovingPositiveLedger6719Research.directionFlag,
      ContactMovingPositiveLedger6719Research.surfaceFlag,
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

/-! ### 2. L1 — the delayed cut lands in mult • hybrid (mult ≥ 2)

Direct containment (no mod-G reduction): the (w+1+delay)-th tail cut lies in the
sharp flag at degree w+1+delay, and the three cumulative absorptions above push
that into `mult • cellHybridCoordinate` whenever 1 ≤ delay ≤ mult and 2 ≤ mult. -/

theorem laterTail_in_hybridFlag6750
    (t y r : Nat) (hr2 : 2 ≤ r) (hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r))
    (delay mult : ℕ) (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinate t y r)
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1 + delay)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  -- globalTailCut is definitionally surfaceMap of the agreement numerator with
  -- the tail selector, so the sharp containment applies directly.
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (anchoredW + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (anchoredW + 1 + delay)
      (ContactFirstTailCertificate6731Research.tailSelector
        (anchoredW + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  -- rewrite the sharp cumulative sums into the subtraction-free atom form
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (anchoredW + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, ContactMovingAgreementCertificate6719Research.support,
      anchoredW, e3, e2, e1]
    all_goals ring
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (anchoredW + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (anchoredW + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, ContactMovingAgreementCertificate6719Research.support,
      anchoredW, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (anchoredW + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (anchoredW + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (anchoredW + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, ContactMovingAgreementCertificate6719Research.support,
      anchoredW, e3, e2, e1]
    all_goals ring
  -- hybrid cumulative sums in atom form
  have hhallV : (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3) + 196608) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      ContactMovingPositiveLedger6719Research.directionFlag,
      add_all, nsmul_all, w]
    all_goals norm_num
  have hhysV : (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      ContactMovingPositiveLedger6719Research.directionFlag,
      add_yz, add_all, nsmul_yz, nsmul_all, w]
    norm_num
    ring
  have hhtotV : (mult • cellHybridCoordinate t y r).zOnly +
      (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      ContactMovingPositiveLedger6719Research.directionFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all, w]
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

/-! ### 3. L2 — the multiplicity-1 moving count

For a component whose (w+2)-cut is proper, the seeds are bounded by
wc(rational) + (w+1)·movingCost, via the filteredCut decomposition of the (w+2)
cut and the MovingPoleBudget zero bound at C := center, k := w+1. -/

set_option maxHeartbeats 20000000 in
theorem component_hybrid_moving_card_le
    (t y r : Nat) (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1 + 1) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (anchoredW + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hR : S.F.degreeOf 2 ≤ cellS r + 2 := by
    have h := Hsupport.coordinate_bounds.2.1
    simpa only [cellSupport, cellS,
      ContactMovingAgreementCertificate6719Research.support] using h
  have hYR : wt ![0, 1, 1, 0] S.F ≤ cellB y r + cellS r + 3 := by
    have h := Hsupport.ys_weight
    simpa only [ContactIdentityResidualGlobalFlagResearch.residualYSWeights,
      cellSupport, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support] using h
  have hAll : wt ![0, 1, 1, 1] S.F ≤ cellA t y + cellB y r + cellS r + 3 := by
    have h := Hsupport.total_weight
    simpa only [ContactIdentityResidualGlobalFlagResearch.residualTotalWeights,
      cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support] using h
  obtain ⟨Bc, cf, heq, hcoeff, hclass⟩ :=
    globalTailCut_certificate (polynomialEmbedding K)
      (cellA t y) (cellB y r) (cellS r) S.F hR hYR hAll
      (anchoredW + 1) (Nat.le_add_left 1 anchoredW)
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (anchoredW + 1) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (anchoredW + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (anchoredW + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (anchoredW + 1)
      (center (cellA t y) (cellB y r) (cellS r)) Bc cf hHnot hA hcoeff hclass
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (filteredCut (anchoredW + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F))) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (anchoredW + 1 + 1)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma anchoredW (anchoredW + 1 + 1)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (anchoredW + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

theorem exists_hybridTailMultiplicityProvider_of_anchoredDVR
    (t y r : Nat) (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r))
    (hs : (cellSupport t y r).s ≤ anchoredFixedSupport.s)
    (hys : (cellSupport t y r).ys ≤ anchoredFixedSupport.ys)
    (htotal : (cellSupport t y r).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag
      (cellSharpTail t y r))
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))
    (htangentGate : anchoredErrors + 1 ≤ (cellHybridCoordinate t y r).yz)
    (hrationalGate : anchoredErrors + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStage S hs hys htotal)
        (canonicalLocalDVRFamily (loosenStage S hs hys htotal)
          hfirstProper) C)) :
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  have hry : r < y := by omega
  let S0 := loosenStage S hs hys htotal
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStage_one_le_localMultiplicity S hs hys htotal hfirstProper
  -- weightedCost over budget = weightedCost over B (cost equalities)
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  -- the piecewise cost
  let cost : FirstTailComponent S → ℕ := fun C =>
    if 2 ≤ multiplicity C then
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C
    else
      B.weightedCost (cellRational t y r) C +
        (w + 1) * (budget C).movingCost
  -- pointwise: cost C ≤ mult C * wc(hybrid) + (w+1) * movingCost C
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C +
        (w + 1) * (budget C).movingCost := by
    intro C
    by_cases hm : 2 ≤ multiplicity C
    · simp only [cost, if_pos hm]
      exact Nat.le_add_right _ _
    · simp only [cost, if_neg hm]
      have hmono := weightedCost_mono B C
        (cellRational_le_hybrid t y r).1
        (cellRational_le_hybrid t y r).2.1
        (cellRational_le_hybrid t y r).2.2
      have h1 : B.weightedCost (cellRational t y r) C ≤
          multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C := by
        calc B.weightedCost (cellRational t y r) C ≤
            B.weightedCost (cellHybridCoordinate t y r) C := hmono
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      omega
  -- the component bound
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 2 ≤ multiplicity C
      · -- mult ≥ 2: cut with the delayed cut inside mult • hybrid
        have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F
                (anchoredW + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma anchoredW (anchoredW + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod6750 C.1
            (multiplicity C • cellHybridCoordinate t y r)
            (globalTailCut (polynomialEmbedding K) S.F
              (anchoredW + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F
            (anchoredW + 1 + delay),
            laterTail_in_hybridFlag6750 t y r hr2 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simpa using C.1.zero_mem
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        have hscale : B.weightedCost
            (multiplicity C • cellHybridCoordinate t y r) C =
            multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C := by
          simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly,
            nsmul_yz, nsmul_all]
          ring
        simp only [cost, if_pos hm]
        rw [hscale] at hcount
        exact hcount
      · -- mult = 1: delay must be 1; use the moving engine
        have hm1 : multiplicity C = 1 := by
          have := hone C
          omega
        have hdelay1 : delay = 1 := by
          have h2 : delay ≤ 1 := by rw [← hm1]; exact hdelayMu
          omega
        subst hdelay1
        have hcount := component_hybrid_moving_card_le t y r hr2 hry hyt
          S C (budget C) (base C) htail
        simp only [cost, if_neg hm]
        simp only [hwcEq] at hcount
        -- fold wc(center) + (w+1)·wc(⟨a,b,s⟩) into wc(rational)
        have hfold : B.weightedCost
              (center (cellA t y) (cellB y r) (cellS r)) C +
            (anchoredW + 1) *
              (B.weightedCost
                (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) C +
                (budget C).movingCost) =
            B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := by
          have hid := center_add_smul_eq_cellRational t y r
          simp only [← hid, PrimeFlagBudgetFamily.weightedCost, add_zOnly,
            add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
            show anchoredW = w from rfl]
          ring
        omega
    · -- tangent branch
      have hcount := htangent C htangentBranch
      by_cases hm : 2 ≤ multiplicity C
      · simp only [cost, if_pos hm]
        calc _ ≤ (anchoredErrors + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinate t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinate t y r) C
              (anchoredErrors + 1) htangentGate
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      · simp only [cost, if_neg hm]
        calc _ ≤ (anchoredErrors + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellRational t y r) C :=
            yzCost_mul_le_weightedCost B (cellRational t y r) C
              (anchoredErrors + 1) hrationalGate
          _ ≤ B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := Nat.le_add_right _ _
  -- the sum bound: certificate + moving sum
  have hsum : (∑ C, cost C) ≤
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    calc (∑ C, cost C) ≤
        ∑ C, (multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C +
          (w + 1) * (budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C, multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C) +
          (w + 1) * (∑ C, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ flagMixed flag (cellSharpTail t y r)
            (cellHybridCoordinate t y r) +
          (w + 1) *
            flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
        Nat.add_le_add
          (hresultants.divisor_le B multiplicity)
          (Nat.mul_le_mul_left _ hmovingSum)
  have providerDichotomy := loosenStage_dichotomy_with_tangent S hs hys htotal
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := cost
    one_le_multiplicity := hone
    tangentYZGate := htangentGate
    cost_sum_le := hsum
    componentBound := hbound
    dichotomy := providerDichotomy }⟩

end
end ContactHybridTailProvider6751Research
end ProximityPrize.SubmissionLower
