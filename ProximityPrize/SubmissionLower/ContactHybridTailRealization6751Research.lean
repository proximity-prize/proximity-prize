/-
HYBRID REALIZATION (Path B) — the sharp analogue of
exists_delayedTailMultiplicityProvider_of_reducedWeightedResultants,
callable from ContactAnchoredOrdinaryProperProvider:89.

DESIGN (all signatures verified against the tree):
  * The reduced geometry (reducedActiveGeometry) is TRANSPORTED to the
    T1-components along regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S).
    Every field depends only on C.1 and the equiv preserves .1 by rfl, so the
    transport is pointwise composition.
  * The fixed powers come from reducedStage_activeFixedPowers applied AT THE
    TRIVIAL CONGRUENCE Tred := T1 (S.G ∣ T1 - T1 by simp): the congruence
    machinery collapses, and transportedMultiplicity at the self-congruence is
    the identity (funext + Subtype.ext rfl).
  * The certificate is activeNestedWeightedCertificate on T1 directly —
    NO ofCongruentCut, NO transport.
  * budget/hcost/hmovingSum come from exists_firstTail_cut_budgets with
    E := AlgebraicClosure (RatFunc (GenericField K)).
  * htangentGate/hrationalGate are discharged from r + 2 ≤ y by omega.
  * hmix stays a hypothesis (numeric, discharged at line 89 where prime is
    concrete; you priced it at 152x room).

KNOWN RISK SITES (marked in-line):
  (R1) the AdaptiveNestedProjectionDataActive constructor: I list the 16 fields
       visible in the structure; if the anonymous constructor reports missing
       fields, fill each with the same `fun C => A.data.<field> (e C)` pattern.
  (R2) the E-instances: if typeclass search misses
       Algebra (GenericField K) (AlgebraicClosure (RatFunc (GenericField K))),
       use the letI block in the comment at that site.
  (R3) defeq frictions cellSupport ↔ support / cellSharpTail ↔
       sharpResidualAgreementFlag: both are definitional; if an `exact` balks,
       insert `show` with the unfolded form.
-/
import ProximityPrize.SubmissionLower.ContactHybridTailProvider6751Research
import ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Research
import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionCoordinateResearch
import ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research

namespace ProximityPrize.SubmissionLower
namespace ContactHybridTailRealization6751Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch
open ContactRegularComponentCover ContactFlagBezout6543Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research
open ActualCurveCoordinateField
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open CoordinateBoxZeroCount
open ContactAdaptiveProjectionCoordinateResearch
open ContactFlagAffineFamilyDegree6543Research
open Polynomial KaehlerDifferential
open ActualCurveRationalProjection ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactPolynomialSolutions
open ContactScalarCoordinateSeparator6630Research
open ContactTerminalAdaptiveProjection6600Research
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactDelayedTailMultiplicityProvider6732Research
open ContactPrimeSeedIncidence
open ContactPrimeFlagBudgetFamilyResearch
open ContactResidualSupportParametersResearch
open ContactSharpTaylorFixedMeet6656Research
open ContactMovingCurveBudget6719Research
open ContactFirstTailBudget6731Research
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactAnchoredReducedWeightedResultants6750Research
open ContactAnchoredReducedActiveGeometry6750Research
open ContactAnchoredCongruentCuts6750Research
open ContactActiveNestedFlagCosts6733Research
open ContactActiveNestedCertificate6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactAnchoredReducedActivePowers6750Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactWeakSeparableSeparatorResearch
open ContactTwoTailResultantProvider6732Research
open ContactRouterCellCosts6750Research
open ContactTwoTailParameters6750Research
open ContactHybridTailProvider6751Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {t y r : Nat}

/-! ### 1. Trivial congruence and transport-collapse -/

theorem firstCut_sub_self_dvd
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r)) :
    S.G ∣ globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1) -
      globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1) := by
  simp

theorem transportedMultiplicity_self
    {G T H : MvPolynomial (Fin 3) (GenericField K)}
    (h : G ∣ T - T)
    (mult : RegularComponent (GenericField K) G T H → ℕ) :
    transportedMultiplicity h mult = mult := by
  funext C
  exact congrArg mult (Subtype.ext rfl)

/-! ### 2. Native sharp geometry over the T1-components -/

section Geometry

variable (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors
    flag anchoredW (cellSupport t y r))

theorem firstCut_in_sharp :
    PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
    (anchoredW + 1)
    (ContactFirstTailCertificate6731Research.tailSelector (anchoredW + 1))
    0 0 0

structure SharpActiveGeometry where
  base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1
  hactive : ∀ C : FirstTailComponent S,
    KaehlerDifferential.D (GenericField K)
        (CoordinateField (GenericField K) C.1)
        (coordinate (GenericField K) C.1 0) ≠ 0 ∨
      KaehlerDifferential.D (GenericField K)
        (CoordinateField (GenericField K) C.1)
        (coordinate (GenericField K) C.1 2) ≠ 0
  hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2
  data : AdaptiveNestedProjectionDataActive base hactive
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)

theorem exists_sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y) :
    Nonempty (SharpActiveGeometry S) := by
  classical
  have hGflag : PolynomialInFlag flag S.G := S.flag_support
  have hTflag : PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1)) :=
    firstCut_in_sharp S
  obtain ⟨hGY, hGS, hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hTflag
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have hTY' : (globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1)).degreeOf 0 ≤
      1 + (anchoredW + 1) * (2 * (cellB y r + cellS r + 3) - 2) := by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys (cellSupport t y r) hsy
      (anchoredW + 1)
  have hTS' : (globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1)).degreeOf 1 ≤
      (2 * (cellS r + 2) - 1) * (anchoredW + 1) := by
    apply hTS.trans_eq
    rfl
  have hGdegree : ∀ j : Fin 3, S.G.degreeOf j < p := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ : coordinateMixedDegree (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1)) 2 < p := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixedSharp
  let choiceData : ∀ C : FirstTailComponent S,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1)) p
      S.G_dvd_surface S.irreducible_G hfirstProper S.y_dependent
      hGdegree hmixedZ C
  let base : ∀ C : FirstTailComponent S,
      SeparableLiteralCoordinate C.1 := fun C ↦ (choiceData C).choose
  have hbaseIndex : ∀ C : FirstTailComponent S,
      (base C).index = 0 ∨ (base C).index = 2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : FirstTailComponent S,
      KaehlerDifferential.D (GenericField K)
          (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 0) ≠ 0 ∨
        KaehlerDifferential.D (GenericField K)
          (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 2) ≠ 0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  have hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate (GenericField K)
      C.1 2 htr p S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      S.irreducible_G
      (regularComponent_G_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      (regularComponent_T_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      hfirstProper hGdegree hmixedZ
  exact ⟨⟨base, hactive, hZ,
    Classical.choice (exists_adaptiveNestedProjectionDataActive base hactive
      (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S))⟩⟩

noncomputable def sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y) : SharpActiveGeometry S :=
  Classical.choice
    (exists_sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry)

/-! ### 3. The sharp unit family and budget family -/

noncomputable def sharpUnitFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y) :
    AdaptiveUnitProjectionFamily
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
      flag (cellSharpTail t y r) :=
  activeNestedUnitFamily
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))).2
      (firstCut_in_sharp S))

noncomputable def sharpBudgetFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y) :
    PrimeFlagBudgetFamily
      (G := S.G)
      (T := globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F)
      flag (cellSharpTail t y r) :=
  (sharpUnitFamily S hfirstProper hflagChar hmixedSharp hry).toPrimeFlagBudgetFamily

/-! ### 4. The certificate on T1 directly -/

theorem sharpWeightedResultants
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y)
    (hs : (cellSupport t y r).s ≤ anchoredFixedSupport.s)
    (hys : (cellSupport t y r).ys ≤ anchoredFixedSupport.ys)
    (htotal : (cellSupport t y r).total ≤ anchoredFixedSupport.total) :
    RegularComponentWeightedInertiaResultantCertificate
      (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp hry)
      (fun C => localMultiplicity (loosenStage S hs hys htotal)
        (canonicalLocalDVRFamily (loosenStage S hs hys htotal)
          hfirstProper) C) := by
  have h0 := firstCut_sub_self_dvd S
  have powers := reducedStage_activeFixedPowers
    (loosenStage S hs hys htotal) hfirstProper
    (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1)) h0
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).data
  exact activeNestedWeightedCertificate
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))).2
      (firstCut_in_sharp S))
    _ powers

end Geometry

/-! ### 5. The realization (statement changes: hmixed -> hmixedSharp, plus hry
    threading; body otherwise as before with the geometry projections) -/

theorem exists_hybridTailMultiplicityProvider_realized
    (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r))
    (hs : (cellSupport t y r).s ≤ anchoredFixedSupport.s)
    (hys : (cellSupport t y r).ys ≤ anchoredFixedSupport.ys)
    (htotal : (cellSupport t y r).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) *
            (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp
              (by omega)).yzCost C) :
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  have hry : r < y := by omega
  haveI : CharP (AlgebraicClosure (RatFunc (GenericField K))) p :=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget, hcost, hz, hyz, hall, hmov⟩ :=
    exists_firstTail_cut_budgets
      (E := AlgebraicClosure (RatFunc (GenericField K)))
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (cellA t y) (cellB y r) (cellS r) anchoredW (by norm_num [anchoredW])
      rfl
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
      (sharpUnitFamily S hfirstProper hflagChar hmixedSharp hry)
      p hmix
  have hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    have hcut := cellMovingCut_eq_center_add t y r
    have hfib : cellMovingFiber t y r =
        ContactMovingPositiveLedger6719Research.fiberFlag
          (cellA t y) (cellB y r) (cellS r) := rfl
    rw [hfib, hcut]
    exact hmov
  have htangentGate : anchoredErrors + 1 ≤
      (cellHybridCoordinate t y r).yz := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      ContactMovingPositiveLedger6719Research.directionFlag,
      add_yz, cellB, cellS, anchoredErrors, w]
    omega
  have hrationalGate : anchoredErrors + 1 ≤ (cellRational t y r).yz := by
    simp only [cellRational, cellDirection,
      ContactMovingPositiveLedger6719Research.directionFlag,
      cellB, cellS, anchoredErrors, w]
    omega
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp hry).zCost
          C ∧
      (budget C).yzCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp hry).yzCost
          C ∧
      (budget C).allCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp hry).allCost
          C :=
    hcost
  exact exists_hybridTailMultiplicityProvider_of_anchoredDVR
    t y r hr2 hb hyt S hs hys htotal hfirstProper
    (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp hry)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry).base
    budget hcost' hmovingSum htangentGate hrationalGate htangent
    (sharpWeightedResultants S hfirstProper hflagChar hmixedSharp hry
      hs hys htotal)

 
theorem sharpUnitFamily_one_le_yzCost
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (anchoredW + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (anchoredW + 1)) < p)
    (hry : r < y)
    (C : FirstTailComponent S) :
    1 ≤ (sharpUnitFamily S hfirstProper hflagChar hmixedSharp hry
      ).toPrimeFlagBudgetFamily.yzCost C := by
  let A := sharpActiveGeometry S hfirstProper hflagChar hmixedSharp hry
  let U := sharpUnitFamily S hfirstProper hflagChar hmixedSharp hry
  change 1 ≤ coordinateDegree (GenericField K)
    (CoordinateField (GenericField K) C.1) (U.yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  have hproj : U.yzProjection C = coordinateOfGate
      (affineU (GenericField K) C.1 A.data.lam) (A.data.uGate C) := rfl
  rw [hproj, coordinateOfGate_value]
  exact A.data.uTranscendental C
