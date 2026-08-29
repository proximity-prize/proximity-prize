import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorProviderResearch

/-!
# Sharp equal-weight Taylor flags with the active Z/YZ factor provider

This module supplies the missing direction seam between the equal-weight
Taylor support theorem and the profile-generic active-YZ component provider.
It keeps the stored residual support used by the recursive coordinate changes,
but indexes every agreement cut by the smaller sharp flag.
-/

namespace ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch

open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualCoordinateDegreeSum
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactIncidence
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactIdentityResidualCurveTerminalIncidenceResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactIdentityResidualComponentFamilyYZSupportResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactIdentityResidualFactorProvider6600Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorFixedMeet6656Research
open ContactProfileYZFactorLedgerResearch
open ContactTerminalAdaptiveProjectionFixedMeetActive6656Research
open ContactNearPencilStratifiedIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactResidualSparseComponentAdapterResearch
open ContactStratifiedResidualComponentAdapter6600Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveNestedYZFamily6630Research
open ContactWeakSeparableSeparatorResearch
open ContactScalarCoordinateSeparator6630Research
open ContactResidualStageDerivative6600Research
open ContactTerminalAdaptiveProjection6656Research

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Prime-budget recursive incidence with a caller-supplied flag for every
terminal agreement degree.  This is the narrow parameterization of the
accepted recursive theorem needed by equal-weight Taylor cuts. -/
theorem recursive_curve_stratified_incidence_of_prime_flag_budget_for_cuts
    {e d a : ℕ} {surfaceFlag cutFlag : FlagDegree}
    {support : ResidualSupportParameters}
    (hphi : Function.Injective phi)
    (S : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag d support)
    (cutAt : ℕ → FlagDegree) (cost : FlagDegree → ℕ)
    (B : PrimeFlagZeroBudget S.primeIdeal cost)
    (degreeCost unitCost U V zCharge : ℕ)
    (hcost : ∀ t : ℕ, cost (cutAt t) = t * degreeCost + unitCost)
    (hcut : ∀ D : S.TerminalDescendant, D.stage.identities = ∅ →
      ∀ i ∈ D.stage.nodes,
        PolynomialInFlag (cutAt D.degree)
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i)))
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma, a ≤ (S.agreementFiber gamma).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  classical
  let Inv : ∀ n, CurveResidualStage phi Gamma x pchar e
      surfaceFlag cutFlag n support → Prop :=
    fun _ A ↦ PrimeFlagZeroBudget A.primeIdeal cost
  have htransport : ∀ {n m}
      {A : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag n support}
      {Anext : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag m support},
      A.ResidualTransition Anext → Inv n A → Inv m Anext := by
    intro n m A Anext htransition hbudget
    obtain ⟨aY, v, bY, aS, bS, cS, hv, _, _, hprime⟩ := htransition
    dsimp only [Inv] at hbudget ⊢
    rw [hprime]
    exact hbudget.mapResidual aY v bY aS bS cS hv
  obtain ⟨D, hDBudget⟩ := S.exists_terminal_descendant_with_invariant
    hphi Inv htransport B
  rcases D.terminal with hproper | hpencil
  · let k := d - D.degree
    have hk : k ≤ d := Nat.sub_le d D.degree
    have hDle : D.degree ≤ d := D.degree_le
    have hdegreeEq : D.degree = d - k := by
      dsimp only [k]
      omega
    have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
      simpa only [k] using D.nodes_card
    have hterminalAgreement : ∀ gamma ∈ Gamma,
        a - k ≤ (D.stage.agreementFiber gamma).card := by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber : ∀ i ∈ D.stage.nodes,
        (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost := by
      intro i hi
      have hflag := hcut D hproper i hi
      have hzero := hDBudget.zero_le (cutAt D.degree)
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        hflag (D.stage.proper_agreement_of_terminal hproper hi)
      rw [hcost D.degree] at hzero
      exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
        D.stage.F D.stage.selected Gamma pchar D.degree
        D.stage.characteristic_bound D.stage.degree_le D.stage.solution
        D.stage.regular D.stage.on_prime
        (x i) (D.stage.u0 i) (D.stage.u1 i)
        (D.degree * degreeCost + unitCost) hzero
    have hrawTerminal := incidence_after_exempt_nodes
      (fun gamma i ↦ D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a - k)
        (D.degree * degreeCost + unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw : Gamma.card * (a - k) ≤
        (S.nodes.card - k) * ((d - k) * degreeCost + unitCost) := by
      simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
        hrawTerminal
    have hmain : Gamma.card * (a - d) ≤ U * degreeCost + V * unitCost :=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail := hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)

/-- The recursive prime-budget theorem specialized to the equal-weight sharp
agreement flags.  Every terminal cut is certified directly from the residual
stage's preserved support weights. -/
theorem recursive_curve_stratified_incidence_of_sharp_prime_flag_budget
    {e d a : ℕ} {surfaceFlag cutFlag : FlagDegree}
    {support : ResidualSupportParameters}
    (hsy : support.s < support.ys)
    (hphi : Function.Injective phi)
    (S : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag d support)
    (cost : FlagDegree → ℕ)
    (B : PrimeFlagZeroBudget S.primeIdeal cost)
    (degreeCost unitCost U V zCharge : ℕ)
    (hcost : ∀ t : ℕ,
      cost (sharpResidualAgreementFlag support t) =
        t * degreeCost + unitCost)
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma, a ≤ (S.agreementFiber gamma).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  apply recursive_curve_stratified_incidence_of_prime_flag_budget_for_cuts
    hphi S (sharpResidualAgreementFlag support) cost B
    degreeCost unitCost U V zCharge hcost
  · intro D _hterminal i _hi
    exact surfaceMap_agreement_in_sharp_flag hsy (phi := phi)
      ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight,
        D.stage.surface_total_weight⟩
      D.degree (fun j : ℕ ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  · exact hda
  · exact hagreement
  · exact hlarge
  · exact hdegree
  · exact hunit

theorem weightedCost_sharpResidualAgreementFlag
    {G T H : MvPolynomial (Fin 3) Omega} {p q : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q)
    (support : ResidualSupportParameters)
    (C : RegularComponent Omega G T H) (d : ℕ) :
    B.weightedCost (sharpResidualAgreementFlag support d) C =
      d * B.weightedCost (sharpAgreementDirection support) C +
        B.weightedCost unitYZFlag C := by
  simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
    PrimeFlagBudgetFamily.weightedCost, unitYZFlag]
  ring

theorem flagMixed_sharpResidualAgreement_direction
    (p : FlagDegree) (support : ResidualSupportParameters) (d : ℕ) :
    flagMixed p (sharpResidualAgreementFlag support d)
        (sharpAgreementDirection support) =
      d * flagMixed p (sharpAgreementDirection support)
          (sharpAgreementDirection support) +
        flagMixed p (sharpAgreementDirection support) unitYZFlag := by
  simp [flagMixed, sharpResidualAgreementFlag, sharpAgreementDirection,
    unitYZFlag]
  ring

theorem flagMixed_sharpResidualAgreement_unit
    (p : FlagDegree) (support : ResidualSupportParameters) (d : ℕ) :
    flagMixed p (sharpResidualAgreementFlag support d) unitYZFlag =
      d * flagMixed p (sharpAgreementDirection support) unitYZFlag +
        flagMixed p unitYZFlag unitYZFlag := by
  simp [flagMixed, sharpResidualAgreementFlag, sharpAgreementDirection,
    unitYZFlag]
  ring

theorem flagMixed_sharpResidualAgreement_z
    (p : FlagDegree) (support : ResidualSupportParameters) (d : ℕ) :
    flagMixed p (sharpResidualAgreementFlag support d) unitZFlag =
      d * flagMixed p (sharpAgreementDirection support) unitZFlag +
        flagMixed p unitYZFlag unitZFlag := by
  simp [flagMixed, sharpResidualAgreementFlag, sharpAgreementDirection,
    unitYZFlag, unitZFlag]
  ring

/-- Component-family aggregation with sharp cuts and the joint Z/YZ tail. -/
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_sharp_z_yz
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag : FlagDegree)
    (support : ResidualSupportParameters)
    (hsy : support.s < support.ys)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag (sharpResidualAgreementFlag support d) T)
    (hFs : wt residualSWeights F ≤ support.s)
    (hFys : wt residualYSWeights F ≤ support.ys)
    (hFtotal : wt residualTotalWeights F ≤ support.total)
    (hinj : Set.InjOn x nodes)
    (hdegreeSelected : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ d)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hTpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma d e)
    (hchar : d < p) (hda : d < a)
    (B : PrimeFlagBudgetFamily (G := G) (T := T)
      (H := regularitySurface phi F) surfaceFlag
      (sharpResidualAgreementFlag support d))
    (hzyzPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F), 1 ≤ B.zCost C + B.yzCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
          (sharpAgreementDirection support) +
        V * flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
          unitYZFlag +
        (e + 1) * (a - d) *
          (flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
              unitZFlag +
            flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
              unitYZFlag) := by
  classical
  let H := regularitySurface phi F
  have hHp : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) H ≠ 0 := by
    intro gamma hgamma
    change MvPolynomial.eval (selectedPoint phi selected gamma)
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular gamma hgamma
  let degreeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost (sharpAgreementDirection support) C
  let unitCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost unitYZFlag C
  let largeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.zCost C + B.yzCost C
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (e + 1) * (a - d) * largeCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStageOfSupport support F G T selected Gamma
      nodes x u0 u1 p e d surfaceFlag
      (sharpResidualAgreementFlag support d) hdiv hGflag hTflag
      hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    apply recursive_curve_stratified_incidence_of_sharp_prime_flag_budget
      hsy hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
      (degreeCost C) (unitCost C) U V (largeCost C)
    · intro t
      simpa only [degreeCost, unitCost] using
        weightedCost_sharpResidualAgreementFlag B support C t
    · exact hda
    · intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    · intro D hmany
      have hcard : GammaC.card ≤ e + 1 :=
        D.stage.card_le_pencil_of_many_identities hmany
      have hscaled : GammaC.card * (a - d) ≤ (e + 1) * (a - d) :=
        Nat.mul_le_mul_right (a - d) hcard
      have hcharged : (e + 1) * (a - d) ≤
          (e + 1) * (a - d) * largeCost C := by
        have hmul := Nat.mul_le_mul_left ((e + 1) * (a - d))
          (hzyzPositive C)
        simpa only [largeCost, Nat.mul_one] using hmul
      exact hscaled.trans hcharged
    · simpa only [S, regularComponentCurveStageOfSupport] using hdegree
    · simpa only [S, regularComponentCurveStageOfSupport] using hunit
  have hlargeSum : (∑ C : RegularComponent Omega G T H, largeCost C) ≤
      flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitZFlag +
        flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
          unitYZFlag := by
    calc
      (∑ C : RegularComponent Omega G T H, largeCost C) =
          (∑ C : RegularComponent Omega G T H, B.zCost C) +
            ∑ C : RegularComponent Omega G T H, B.yzCost C := by
        simp only [largeCost, Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add B.sum_zCost_le B.sum_yzCost_le
  exact aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a - d) U V (e + 1)
    (flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
      (sharpAgreementDirection support))
    (flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitYZFlag)
    (flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitZFlag +
      flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitYZFlag)
    degreeCost unitCost largeCost hcomponent
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le (sharpAgreementDirection support))
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    hlargeSum

/-- Active-YZ terminal families whose second-cut box is the sharp Taylor flag. -/
def TerminalAdaptiveProjectionFamiliesSharpYZ
    {e w : ℕ} {flag : FlagDegree}
    (support : ResidualSupportParameters)
    (S : ResidualStage phi Gamma x pchar e flag w support) : Prop :=
  ∀ (D : S.TerminalDescendant) (i : Iota),
    i ∈ D.stage.nodes →
    ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i) →
    ∃ base : ∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
        (sharpResidualAgreementFlag support D.degree))

/-- Geometry-only active-YZ constructor for an arbitrary supplied sharp cut
flag.  This is the accepted constructor with only its second box exposed. -/
theorem terminalAdaptiveProjectionAtSharpCutYZ_of_active_yz_gates
    {e w : ℕ} {support : ResidualSupportParameters} {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar e flag w support)
    (D : S.TerminalDescendant) (i : Iota)
    (hproper : ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
      (x i) (D.stage.u0 i) (D.stage.u1 i))
    (hGdegree : ∀ j : Fin 3, D.stage.G.degreeOf j < pchar)
    (hmixedZ : coordinateMixedDegree Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
    (hGflag : PolynomialInFlag flag D.stage.G)
    (hTflag : PolynomialInFlag (sharpResidualAgreementFlag support D.degree)
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))) :
    ∃ base : ∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
        (sharpResidualAgreementFlag support D.degree)) := by
  classical
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let H := regularitySurface phi D.stage.F
  let choiceData : ∀ C : RegularComponent Omega D.stage.G T H,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      phi D.stage.F D.stage.G T pchar D.stage.G_dvd_surface
      D.stage.irreducible_G hproper D.stage.y_dependent hGdegree hmixedZ C
  let base : ∀ C : RegularComponent Omega D.stage.G T H,
      SeparableLiteralCoordinate C.1 := fun C ↦ (choiceData C).choose
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
      pchar D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hGdegree hmixedZ
  obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
    flag (sharpResidualAgreementFlag support D.degree)
    base hactive hZ (residualStage_pderiv_one_ne_zero_of_support D.stage)
    D.stage.irreducible_G hproper
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff
      (sharpResidualAgreementFlag support D.degree) T).2 hTflag)
  exact ⟨base, ⟨P⟩⟩

/-- Rectangular-cap constructor for sharp active-YZ terminal families. -/
theorem terminalAdaptiveProjectionFamiliesSharpYZ_of_active_yz_caps
    {e w : ℕ} {flag : FlagDegree}
    (support : ResidualSupportParameters) (hsy : support.s < support.ys)
    (S : ResidualStage phi Gamma x pchar e flag w support)
    (surfaceY surfaceS surfaceZ cutY cutS : ℕ)
    (hflagY : flag.yz + flag.all ≤ surfaceY)
    (hflagS : flag.all ≤ surfaceS)
    (hflagZ : flag.zOnly + flag.yz + flag.all ≤ surfaceZ)
    (hcutY : 1 + w * (2 * support.ys - 2) ≤ cutY)
    (hcutS : (2 * support.s - 1) * w ≤ cutS)
    (hsurfaceChar : surfaceY < pchar ∧ surfaceS < pchar ∧
      surfaceZ < pchar)
    (hmixedZ : cutY * surfaceS + surfaceY * cutS < pchar) :
    TerminalAdaptiveProjectionFamiliesSharpYZ support S := by
  intro D i _hi hproper
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hGflag : PolynomialInFlag flag D.stage.G := D.stage.flag_support
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag support D.degree) T :=
    surfaceMap_agreement_in_sharp_flag hsy (phi := phi)
      ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight,
        D.stage.surface_total_weight⟩
      D.degree (fun j : ℕ ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  obtain ⟨hGY, hGS, hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hTflag
  have hD : D.degree ≤ w := D.degree_le
  have hGY' : D.stage.G.degreeOf 0 ≤ surfaceY := hGY.trans hflagY
  have hGS' : D.stage.G.degreeOf 1 ≤ surfaceS := hGS.trans hflagS
  have hGZ' : D.stage.G.degreeOf 2 ≤ surfaceZ := hGZ.trans hflagZ
  have hTY' : T.degreeOf 0 ≤ cutY := by
    calc
      T.degreeOf 0 ≤
          (sharpResidualAgreementFlag support D.degree).yz +
            (sharpResidualAgreementFlag support D.degree).all := hTY
      _ = 1 + D.degree * (2 * support.ys - 2) :=
        sharpResidualAgreementFlag_ys support hsy D.degree
      _ ≤ 1 + w * (2 * support.ys - 2) :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right (2 * support.ys - 2) hD) 1
      _ ≤ cutY := hcutY
  have hTS' : T.degreeOf 1 ≤ cutS := by
    calc
      T.degreeOf 1 ≤ (sharpResidualAgreementFlag support D.degree).all := hTS
      _ = (2 * support.s - 1) * D.degree := by
        simp only [sharpResidualAgreementFlag, sharpAgreementDirection]
      _ ≤ (2 * support.s - 1) * w :=
        Nat.mul_le_mul_left (2 * support.s - 1) hD
      _ ≤ cutS := hcutS
  have hGdegree : ∀ j : Fin 3, D.stage.G.degreeOf j < pchar := by
    intro j
    fin_cases j
    · exact hGY'.trans_lt hsurfaceChar.1
    · exact hGS'.trans_lt hsurfaceChar.2.1
    · exact hGZ'.trans_lt hsurfaceChar.2.2
  have hmixedZ' : coordinateMixedDegree Omega D.stage.G T 2 < pchar := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt hmixedZ
  exact terminalAdaptiveProjectionAtSharpCutYZ_of_active_yz_gates
    S D i hproper hGdegree hmixedZ' hGflag hTflag

/-- One terminal outer fiber, using sharp Taylor flags throughout the inner
curve recursion and the joint Z/YZ large-pencil charge. -/
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile_sharp_z_yz
    (hphi : Function.Injective phi)
    (p : Profile) (support : ResidualSupportParameters)
    (hsy : support.s < support.ys)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w support)
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (_han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (D : S.TerminalDescendant) (i : Iota) (_hi : i ∈ D.stage.nodes)
    (B : PrimeFlagBudgetFamily
      (G := D.stage.G)
      (T := agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H := regularitySurface phi D.stage.F)
      flag (sharpResidualAgreementFlag support D.degree))
    (hzyzPositive : ∀ C : RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F), 1 ≤ B.zCost C + B.yzCost C) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * p.gap ≤
      D.degree * factorDegreeCostYZ p (sharpAgreementDirection support) flag +
        factorUnitCostYZ p (sharpAgreementDirection support) flag := by
  classical
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := p.agreements - (p.w - D.degree)
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag support D.degree) T := by
    exact surfaceMap_agreement_in_sharp_flag hsy (phi := phi)
      ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight,
        D.stage.surface_total_weight⟩
      D.degree (fun j : ℕ ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hsub : GammaI ⊆ Gamma := Finset.filter_subset _ _
  have hTpoint : ∀ gamma ∈ GammaI,
      MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T = 0 := by
    intro gamma hgamma
    obtain ⟨hGamma, hagree⟩ := Finset.mem_filter.mp hgamma
    exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
      pchar D.degree D.stage.characteristic_bound gamma
      (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
      (D.stage.regular gamma hGamma)
      (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
  have hinnerAgreement : ∀ gamma ∈ GammaI,
      aD ≤ (D.stage.nodes.filter (fun j ↦
        (D.stage.selected gamma).eval (x j) =
          D.stage.u0 j + gamma * D.stage.u1 j)).card := by
    intro gamma hgamma
    have hGamma := hsub hgamma
    have h0 := Nat.sub_le_sub_right (hagreement gamma hGamma)
      (p.w - D.degree)
    exact h0.trans (by
      simpa only [aD, ResidualStage.agreementFiber,
        ResidualStage.Agrees] using D.agreement_card gamma hGamma)
  have hda : D.degree < aD := by
    have hD := D.degree_le
    dsimp only [aD]
    omega
  have hdegree : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) * (D.degree - k) ≤
        p.degreeIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ p.w := D.degree_le
    let total := (p.w - D.degree) + k
    have htotal : total ≤ p.w := by
      dsimp only [total]
      omega
    have h := hdegreeGlobal total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap : aD - D.degree = p.gap := by
      dsimp only [aD, Profile.gap]
      omega
    have hn : p.n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have hw : p.w - total = D.degree - k := by
      dsimp only [total]
      omega
    have ha : p.agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, hw, ha] at h
    exact h
  have hunit : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) ≤
        p.unitIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ p.w := D.degree_le
    let total := (p.w - D.degree) + k
    have htotal : total ≤ p.w := by
      dsimp only [total]
      omega
    have h := hunitGlobal total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap : aD - D.degree = p.gap := by
      dsimp only [aD, Profile.gap]
      omega
    have hn : p.n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have ha : p.agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, ha] at h
    exact h
  have hbound :=
    proper_cut_seed_bound_of_recursive_prime_flag_budget_sharp_z_yz
      hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
      x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
      p.degreeIncidence p.unitIncidence flag support hsy
      D.stage.G_dvd_surface D.stage.flag_support hTflag
      D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.stage.x_injective
      (fun gamma hgamma ↦ D.stage.degree_le gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.solution gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.regular gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.on_component gamma (hsub hgamma))
      hTpoint hinnerAgreement
      (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree p.errors hsub D.stage.no_large_pencil)
      D.stage.characteristic_bound hda B (by simpa only [T] using hzyzPositive)
      hdegree hunit
  have hgapEq : aD - D.degree = p.gap := by
    have := D.degree_le
    dsimp only [aD, Profile.gap]
    omega
  rw [hgapEq] at hbound
  rw [flagMixed_sharpResidualAgreement_direction,
    flagMixed_sharpResidualAgreement_unit,
    flagMixed_sharpResidualAgreement_z] at hbound
  simp only [factorDegreeCostYZ, factorUnitCostYZ]
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

/-- Profile-generic sharp Taylor plus active-YZ fixed-factor provider. -/
theorem recursive_scaled_factorSharpYZ_of_adaptive_projection_families
    (hphi : Function.Injective phi)
    (p : Profile) (support : ResidualSupportParameters)
    (hsy : support.s < support.ys)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w support)
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ support S) :
    Gamma.card * p.gap ^ 2 ≤
      factorRegularLedgerYZForDirection p
        (sharpAgreementDirection support) flag := by
  apply recursive_scaled_factorYZ hphi p support
    (sharpAgreementDirection support) S hwa hagreement
  · intro D i hi hproper
    obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
    exact terminal_outer_fiber_bound_of_prime_flag_budget_profile_sharp_z_yz
      hphi p support hsy S hnodes hagreement hwa han
      hdegreeGlobal hunitGlobal D i hi P.family.toPrimeFlagBudgetFamily
      (fun C ↦ P.one_le_zCost_add_yzCost phi D.stage.F rfl
        D.stage.G_dvd_surface C)
  · intro k hk
    simpa only [hnodes] using hdegreeGlobal k hk
  · intro k hk
    simpa only [hnodes] using hunitGlobal k hk

end

end ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
