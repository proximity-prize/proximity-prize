import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedYZFamily6630Research
import ProximityPrize.SubmissionLower.ContactScalarCoordinateSeparator6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch
import ProximityPrize.SubmissionLower.ContactParameters6630Research
import ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research

/-!
# Terminal adaptive projection families at score 66.30

The literal-Y gate against the full agreement cut is intentionally absent.
When `Z` is algebraic, the scalar relation `Z-c` supplies the cheap Y gate;
when `Z` is transcendental, the ordinary (green) Z gate is used.  The chosen
separator is always Y or Z, so its separability proves the active-differential
hypothesis needed by the repaired common nested projection constructor.
-/

namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6630Research

open scoped Classical
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualCoordinateDegreeSum
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactGenericSurface ContactProperCutSeedCount ContactPrimeSeedIncidence
open ContactFlagBezout6543Research
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveNestedYZFamily6630Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactScalarCoordinateSeparator6630Research
open ContactIdentityResidualIteration6630Research
open ContactIdentityResidualCurveTerminalIncidence6630Research
open ContactIdentityResidualGlobalFlag6630Research
open ContactNearPencil6630ArithmeticResearch
open ContactNearPencil6630FlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactRegularFactorGate
open ContactReducedAgreement6643Research
open ContactCongruentCuts6643Research ContactPrimeFlagBudgetFamilyResearch

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Coordinatewise rectangular consequences of nested flag support. -/
theorem degree_bounds_of_polynomialInFlag6630
    {p : FlagDegree} {F : MvPolynomial (Fin 3) Omega}
    (hF : PolynomialInFlag p F) :
    F.degreeOf 0 ≤ p.yz + p.all ∧
      F.degreeOf 1 ≤ p.all ∧
      F.degreeOf 2 ≤ p.zOnly + p.yz + p.all := by
  refine ⟨?_, ?_, ?_⟩
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (hF e he).1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_left (e 2) (e 0 + e 1)).trans (by
      simpa only [Nat.add_assoc] using (hF e he).2.2)

/-- The derivative gate intrinsic to a score-66.30 residual stage. -/
theorem residualStage6630_pderiv_one_ne_zero
    {pchar e d : ℕ} [CharP Omega pchar] {flag : FlagDegree}
    (S : ResidualStage6630 phi Gamma x pchar e flag d) :
    MvPolynomial.pderiv (1 : Fin 3) S.G ≠ 0 := by
  intro hzero
  apply S.regular_proper
  rw [← surfaceMap_pderiv_R]
  obtain ⟨Q, hQ⟩ := S.G_dvd_surface
  refine ⟨MvPolynomial.pderiv (1 : Fin 3) Q, ?_⟩
  rw [hQ, MvPolynomial.pderiv_mul, hzero, zero_mul, zero_add]

/-- Consumer-facing terminal-family hypothesis, retaining the nested YZ
value required by regularity positivity. -/
def TerminalAdaptiveProjectionFamiliesYZ6630
    {pchar : ℕ} [CharP Omega pchar] {flag : FlagDegree}
    (S : ResidualStage6630 phi Gamma x pchar errors flag w) : Prop :=
  ∀ (D : S.TerminalDescendant) (i : Iota),
    i ∈ D.stage.nodes →
    ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i) →
    ∃ B : PrimeFlagBudgetFamily
        (G := D.stage.G)
        (T := agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (H := regularitySurface phi D.stage.F)
        flag (residualAgreementFlag6630 D.degree),
      (∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        Transcendental Omega (coordinate Omega C.1 2) → 1 ≤ B.zCost C) ∧
      (∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        ¬ Transcendental Omega (coordinate Omega C.1 2) → 1 ≤ B.yzCost C)

/-- Exact score-66.30 terminal construction.  Only the Z/agreement
characteristic gate is used; the failed Y/agreement gate has been replaced
by the scalar-coordinate theorem. -/
theorem terminalAdaptiveProjectionFamiliesYZ6630_of_cumulative_caps
    [CharP Omega ContactParameters6630Research.prime]
    {flag : FlagDegree}
    (S : ResidualStage6630 phi Gamma x ContactParameters6630Research.prime
      errors flag w)
    (hflagS : flag.all ≤ 10)
    (hflagYS : flag.yz + flag.all ≤ 48)
    (hflagTotal : flag.zOnly + flag.yz + flag.all ≤ 825) :
    TerminalAdaptiveProjectionFamiliesYZ6630 S := by
  classical
  intro D i hi hproper
  let T0 := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let T := reducedAgreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hcongr : D.stage.G ∣ T0 - T :=
    D.stage.G_dvd_surface.trans
      (agreementPolynomial_sub_reduced_dvd phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
  have hproperT : ¬ D.stage.G ∣ T := by
    intro hT
    apply hproper
    have hsum := dvd_add hcongr hT
    simpa only [sub_add_cancel, T0] using hsum
  let H := regularitySurface phi D.stage.F
  have hGflag : PolynomialInFlag flag D.stage.G := D.stage.flag_support
  have hTflag : PolynomialInFlag (residualAgreementFlag6630 D.degree) T := by
    exact surfaceMap_reducedAgreement_in_flag
      phi D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag6630 hGflag
  obtain ⟨hTY, hTS, hTZ⟩ := degree_bounds_of_polynomialInFlag6630 hTflag
  have hD : D.degree ≤ w := D.degree_le.trans (Nat.le_refl w)
  have hGY' : D.stage.G.degreeOf 0 ≤ 48 := hGY.trans hflagYS
  have hGS' : D.stage.G.degreeOf 1 ≤ 10 := hGS.trans hflagS
  have hGZ' : D.stage.G.degreeOf 2 ≤ 825 := hGZ.trans hflagTotal
  have hTY' : T.degreeOf 0 ≤ 1 + 94 * w := by
    simp only [residualAgreementFlag6630, unitYZFlag,
      agreementDirection6630, add_yz, add_all, nsmul_yz, nsmul_all] at hTY
    omega
  have hTS' : T.degreeOf 1 ≤ 18 * w := by
    simp only [residualAgreementFlag6630, unitYZFlag,
      agreementDirection6630, add_all, nsmul_all] at hTS
    omega
  have hTZ' : T.degreeOf 2 ≤ 1 + 1648 * w := by
    simp only [residualAgreementFlag6630, unitYZFlag,
      agreementDirection6630, add_zOnly, add_yz, add_all,
      nsmul_zOnly, nsmul_yz, nsmul_all] at hTZ
    omega
  have hGdegree : ∀ j : Fin 3,
      D.stage.G.degreeOf j < ContactParameters6630Research.prime := by
    intro j
    fin_cases j
    · exact hGY'.trans_lt (by norm_num [ContactParameters6630Research.prime])
    · exact hGS'.trans_lt (by norm_num [ContactParameters6630Research.prime])
    · exact hGZ'.trans_lt (by norm_num [ContactParameters6630Research.prime])
  have hmixedZ :
      coordinateMixedDegree Omega D.stage.G T 2 <
        ContactParameters6630Research.prime := by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w, ContactParameters6630Research.prime]
  have hSderiv : MvPolynomial.pderiv (1 : Fin 3) D.stage.G ≠ 0 :=
    residualStage6630_pderiv_one_ne_zero D.stage
  have hGdep : 0 < D.stage.G.degreeOf (1 : Fin 3) := by
    have hiff := pderiv_zero_iff_degree_zero_below_char
      (1 : Fin 3) D.stage.G ContactParameters6630Research.prime (hGdegree 1)
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hSderiv (hiff.mpr hzero)
  let choiceData : ∀ C : RegularComponent Omega D.stage.G T H,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C => regularComponent_exists_separableLiteralCoordinate6630
      phi D.stage.F D.stage.G T ContactParameters6630Research.prime
      D.stage.G_dvd_surface
      D.stage.irreducible_G hproperT hGdep hGdegree hmixedZ C
  let base : ∀ C : RegularComponent Omega D.stage.G T H,
      SeparableLiteralCoordinate C.1 := fun C => (choiceData C).choose
  have hbaseIndex : ∀ C : RegularComponent Omega D.stage.G T H,
      (base C).index = 0 ∨ (base C).index = 2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : RegularComponent Omega D.stage.G T H,
      KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 0) ≠ 0 ∨
        KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) ≠ 0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  let hZ : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      ContactParameters6630Research.prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproperT hGdegree hmixedZ
  obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested flag
    (residualAgreementFlag6630 D.degree) base hactive hZ hSderiv
    D.stage.irreducible_G hproperT
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff (residualAgreementFlag6630 D.degree) T).2 hTflag)
  let B := P.family.toPrimeFlagBudgetFamily
  refine ⟨ContactCongruentCuts6643Research.PrimeFlagBudgetFamily.ofCongruentCut
    hcongr B, ?_, ?_⟩
  · apply ContactCongruentCuts6643Research.PrimeFlagBudgetFamily.ofCongruentCut_z_positive
      hcongr B 2
    intro C htr
    exact P.family.one_le_toPrimeFlagBudgetFamily_zCost C htr
  · apply ContactCongruentCuts6643Research.PrimeFlagBudgetFamily.ofCongruentCut_yz_positive
      hcongr B 2
    intro C htr
    exact P.one_le_yzCost_of_not_z_transcendental phi D.stage.F rfl
      D.stage.G_dvd_surface C htr

/-- Convenient increment-cap wrapper for the full score-66.74 surface flag.
The cumulative theorem above is the one used for individual factors. -/
theorem terminalAdaptiveProjectionFamiliesYZ6630_of_rectangular_caps
    [CharP Omega ContactParameters6630Research.prime]
    {flag : FlagDegree}
    (S : ResidualStage6630 phi Gamma x ContactParameters6630Research.prime
      errors flag w)
    (hflagZ : flag.zOnly ≤ 777)
    (hflagY : flag.yz ≤ 38)
    (hflagS : flag.all ≤ 10) :
    TerminalAdaptiveProjectionFamiliesYZ6630 S := by
  apply terminalAdaptiveProjectionFamiliesYZ6630_of_cumulative_caps S hflagS
  · omega
  · omega

end


end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6630Research
