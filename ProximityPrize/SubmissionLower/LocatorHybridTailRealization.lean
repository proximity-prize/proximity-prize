/-
LOCATOR HYBRID TAIL REALIZATION (port of ContactHybridTailRealization6751Research,
pr359) — the sharp analogue of Q2.lean's
`exists_delayedTailMultiplicityProvider_of_reducedGeneral`.

DESIGN (all signatures checked against this tree):
  * The sharp geometry is built NATIVELY over the T1-components (T1 = the
    (w+1)-th global tail cut) from the sharp-flag containment `firstCut_in_sharp`;
    no transport of the reduced geometry along regularComponentEquiv is needed.
  * The fixed powers come from reducedStage_activeFixedPowers applied AT THE
    TRIVIAL CONGRUENCE Tred := T1 (S.G ∣ T1 - T1 by simp): the congruence
    machinery collapses, and transportedMultiplicity at the self-congruence is
    the identity (funext + Subtype.ext rfl, `transportedMultiplicity_self`), so
    the certificate is stated for the local multiplicities directly.
  * The certificate is activeNestedWeightedCertificate on T1 directly —
    NO ofCongruentCut, NO transport.
  * budget/hcost/hmovingSum come from exists_firstTail_cut_budgets with
    E := AlgebraicClosure (RatFunc (GenericField K)).
  * The stage is loosened with loosenStageGeneral (no support-cap hypotheses,
    as in Q2.lean).
  * htangentGate is derived from hrationalGate (rational ≤ hybrid coordinate-
    wise); hrationalGate itself follows from `rationalGate_of_le` for any error
    cap with errorCap + 1 ≤ 131076, since b ≥ 1 in the hybrid branch r + 2 ≤ y.
  * hmix / hmixedSharp / hflagChar stay hypotheses (numeric, discharged where
    the prime is concrete).

KNOWN RISK SITES of the pr359 draft, and how they resolve here:
  (R1) the AdaptiveNestedProjectionDataActive constructor: obtained through
       exists_adaptiveNestedProjectionDataActive, no manual field list.
  (R2) the E-instances: Algebra (GenericField K) (AlgebraicClosure (RatFunc _))
       is found by typeclass search; CharP E p is supplied by
       charP_of_injective_algebraMap.
  (R3) defeq frictions cellSupport ↔ support / cellSharpTail ↔
       sharpResidualAgreementFlag: both are definitional (delta), `exact` works.
-/
import ProximityPrize.SubmissionLower.LocatorHybridTailProvider
namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealization
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

/-! ### 1. Trivial congruence and transport-collapse -/

theorem firstCut_sub_self_dvd
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r)) :
    S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
      globalTailCut (polynomialEmbedding K) S.F (w + 1) := by
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

variable (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap
    flag w (cellSupport t y r))

theorem firstCut_in_sharp :
    PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
    (w + 1) (tailSelector (w + 1)) 0 0 0

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
    (residualStage_pderiv_one_ne_zero_of_support S)

theorem exists_sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    Nonempty (SharpActiveGeometry S) := by
  classical
  have hGflag : PolynomialInFlag flag S.G := S.flag_support
  have hTflag : PolynomialInFlag (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) :=
    firstCut_in_sharp S
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hTY' : (globalTailCut (polynomialEmbedding K) S.F
      (w + 1)).degreeOf 0 ≤
      1 + (w + 1) * (2 * (cellB y r + cellS r + 3) - 2) := by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys (cellSupport t y r) hsy (w + 1)
  have hTS' : (globalTailCut (polynomialEmbedding K) S.F
      (w + 1)).degreeOf 1 ≤
      (2 * (cellS r + 2) - 1) * (w + 1) := by
    apply hTS.trans_eq
    rfl
  have hGdegree : ∀ j : Fin 3, S.G.degreeOf j < p := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ : coordinateMixedDegree (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) 2 < p := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixedSharp
  let choiceData : ∀ C : FirstTailComponent S,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) p
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
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      S.irreducible_G
      (regularComponent_G_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      (regularComponent_T_mem (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) C)
      hfirstProper hGdegree hmixedZ
  exact ⟨⟨base, hactive, hZ,
    Classical.choice (exists_adaptiveNestedProjectionDataActive base hactive
      (residualStage_pderiv_one_ne_zero_of_support S))⟩⟩

noncomputable def sharpActiveGeometry
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) : SharpActiveGeometry S :=
  Classical.choice
    (exists_sharpActiveGeometry S hfirstProper hflagChar hmixedSharp)

/-! ### 3. The sharp unit family and budget family -/

noncomputable def sharpUnitFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    AdaptiveUnitProjectionFamily
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
      flag (cellSharpTail t y r) :=
  activeNestedUnitFamily
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))).2
      (firstCut_in_sharp S))

noncomputable def sharpBudgetFamily
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    PrimeFlagBudgetFamily
      (G := S.G)
      (T := globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F)
      flag (cellSharpTail t y r) :=
  (sharpUnitFamily S hfirstProper hflagChar hmixedSharp).toPrimeFlagBudgetFamily

/-! ### 4. The certificate on T1 directly -/

theorem sharpWeightedResultants
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p) :
    RegularComponentWeightedInertiaResultantCertificate
      (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp)
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C) := by
  have h0 := firstCut_sub_self_dvd S
  have powers := reducedStage_activeFixedPowers
    (loosenStageGeneral S) hfirstProper
    (globalTailCut (polynomialEmbedding K) S.F (w + 1)) h0
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
  exact activeNestedWeightedCertificate
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hactive
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).hZ
    (residualStage_pderiv_one_ne_zero_of_support S)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).data
    S.irreducible_G hfirstProper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff (cellSharpTail t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))).2
      (firstCut_in_sharp S))
    _ powers

end Geometry

/-! ### 5. The realization -/

theorem exists_hybridTailMultiplicityProvider_realized
    (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  haveI : CharP (AlgebraicClosure (RatFunc (GenericField K))) p :=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget, hcost, hz, hyz, hall, hmov⟩ :=
    exists_firstTail_cut_budgets
      (E := AlgebraicClosure (RatFunc (GenericField K)))
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (cellA t y) (cellB y r) (cellS r) w (by norm_num [RCN327.w])
      rfl
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
      (sharpUnitFamily S hfirstProper hflagChar hmixedSharp)
      p hmix
  have hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    have hcut := cellMovingCut_eq_center_add t y r
    have hfib : cellMovingFiber t y r =
        RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r) := rfl
    rw [hfib, hcut]
    exact hmov
  have htangentGate : stageErrorCap + 1 ≤
      (cellHybridCoordinate t y r).yz :=
    tangentGate_of_rationalGate t y r stageErrorCap hrationalGate
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).zCost C ∧
      (budget C).yzCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C ∧
      (budget C).allCost =
        (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).allCost C :=
    hcost
  exact exists_hybridTailMultiplicityProvider_of_localDVR
    t y r hr2 hb hyt S hfirstProper
    (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp)
    (sharpActiveGeometry S hfirstProper hflagChar hmixedSharp).base
    budget hcost' hmovingSum htangentGate hrationalGate htangent
    (sharpWeightedResultants S hfirstProper hflagChar hmixedSharp)

/-- The hybrid fixed-stage seed bound: `Gamma.card ≤ cellHybridCost`-shaped
bound with the stage's own `flag`. -/
theorem hybrid_stage_card_le
    (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (sharpBudgetFamily S hfirstProper hflagChar hmixedSharp).yzCost C) :
    Gamma.card ≤
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
  stage_card_le_divisorBound S
    (exists_hybridTailMultiplicityProvider_realized hr2 hb hyt S hfirstProper
      hflagChar hmixedSharp hmix hrationalGate htangent).some

/-! ### 6. Positivity of the sharp yz-cost (for tangent-count consumers) -/

theorem sharpUnitFamily_one_le_yzCost
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedSharp : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 1) * (w + 1)) < p)
    (C : FirstTailComponent S) :
    1 ≤ (sharpUnitFamily S hfirstProper hflagChar hmixedSharp
      ).toPrimeFlagBudgetFamily.yzCost C := by
  let A := sharpActiveGeometry S hfirstProper hflagChar hmixedSharp
  let U := sharpUnitFamily S hfirstProper hflagChar hmixedSharp
  change 1 ≤ coordinateDegree (GenericField K)
    (CoordinateField (GenericField K) C.1) (U.yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  have hproj : U.yzProjection C = coordinateOfGate
      (affineU (GenericField K) C.1 A.data.lam) (A.data.uGate C) := rfl
  rw [hproj, coordinateOfGate_value]
  exact A.data.uTranscendental C

end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealization
