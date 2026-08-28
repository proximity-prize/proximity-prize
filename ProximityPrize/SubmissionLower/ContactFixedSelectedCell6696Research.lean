import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFixedMeetProfile6696Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

/-!
# Unconditional fixed selected cell at agreement 182414

This module instantiates the generic sharp-Taylor active-YZ factor provider
and the profile-generic tight selected-family combiner at the fixed meet used
by the score-66.96 arithmetic.
-/

namespace ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research

open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint
open ContactFactorCaps ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactTaylorNumerators
open ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research
open ContactRegularFactorFlag6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactResidualSupportParametersResearch.ResidualSupportParameters
open ContactFlagBezout6543Research
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorFixedMeet6656Research
open ContactSharpTaylorYZFactorProviderResearch
open ContactProfileYZFactorLedgerResearch
open ContactProfileFixedSelectedCombinerResearch
open ContactFixedMeetProfile6696Research

noncomputable section

set_option maxHeartbeats 7000000
set_option maxRecDepth 100000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The target interpolation box supplies the preserved `(8,43,933)` support
needed by the residual recursion. -/
theorem fixedSupport_of_mem_box
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap) :
    ResidualSupportData fixedSupport F := by
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights F 8).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 925 ∧ d 2 ≤ 8 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5654834 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 8
    norm_num
    exact hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights F 43).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 925 ∧ d 2 ≤ 8 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5654834 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 43
    norm_num
    norm_num at hb
    omega
  · apply (weightedTotalDegree_le_iff residualTotalWeights F 933).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 925 ∧ d 2 ≤ 8 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5654834 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 933
    norm_num
    norm_num at hb
    omega

/-- Canonical fixed-profile residual stage for one geometric factor of one
actual positive-`R` factor. -/
def fixedRegularGeometricResidualStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x prime fixedProfile.errors (geometricFlag K g) fixedProfile.w
      fixedSupport := by
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt
        (by norm_num [fixedProfile, prime])
  have hsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_mem_box R.1 hRdata.2.2
  exact regularGeometricResidualStageOfSupport fixedSupport Q selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
    hsupport (by norm_num [fixedProfile, prime]) g

/-- Geometric sharp-YZ bounds aggregate to the same direction-generic ledger
on one actual positive-`R` factor. -/
theorem regular_factor_seed_bound_of_geometric_sharp_yz_counts
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : RegularIndex Q)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected
          (regularSeeds Q selected Gamma R) g).card * fixedProfile.gap ^ 2 ≤
        factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
          (geometricFlag K g)) :
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularFlag Q R) := by
  obtain ⟨hRirred, _, _⟩ := directFactor_data Q R.1 hQ
    fixedProfile.weightedCap fixedProfile.w fixedProfile.seedTotalCap
      fixedProfile.slopeCap hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRirred.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hcaps := geometricFlag_budgets K R.1 hRirred.ne_zero
  calc
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
        (∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card) *
          fixedProfile.gap ^ 2 := Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected
          (regularSeeds Q selected Gamma R) g).card * fixedProfile.gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K R.1,
        factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
          (geometricFlag K g) := Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        ⟨R.1.degreeOf (3 : Fin 4), R.1.degreeOf (1 : Fin 4),
          R.1.degreeOf (2 : Fin 4)⟩ :=
      sum_factorRegularLedgerYZForDirection_le_flag fixedProfile
        fixedSharpDirection (geometricFlag K)
        ⟨R.1.degreeOf (3 : Fin 4), R.1.degreeOf (1 : Fin 4),
          R.1.degreeOf (2 : Fin 4)⟩ hcaps.1 hcaps.2.1 hcaps.2.2
    _ = factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularFlag Q R) := by rfl

/-- Every actual positive-`R` factor receives its sharp-YZ ledger from the
canonical active-YZ terminal families. -/
theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularFlag Q R) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  apply regular_factor_seed_bound_of_geometric_sharp_yz_counts Q hQ hbox
    selected Gamma R
  intro g
  let S := fixedRegularGeometricResidualStage Q hQ hbox selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds Q selected Gamma R) g).trans
      (regularSeeds_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = fixedProfile.n := by
    simpa [S, fixedRegularGeometricResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g,
      fixedProfile.agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
      fixedRegularGeometricResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using
        hagreement gamma (hgeomSub hgamma)
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hglobal := regularFlag_budgets fixedProfile Q hQ
    (by norm_num [fixedProfile]) hbox
  have hRZ : (regularFlag Q R).zOnly ≤ fixedProfile.seedTotalCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.1
  have hRY : (regularFlag Q R).yz ≤ fixedProfile.yCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.1
  have hRS : (regularFlag Q R).all ≤ fixedProfile.slopeCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.2
  have hgZ : (geometricFlag K g).zOnly ≤ (regularFlag Q R).zOnly := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide] using
      geometricFactor_degree_le K R.1 hRne g (2 : Fin 3)
  have hgY : (geometricFlag K g).yz ≤ (regularFlag Q R).yz := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (0 : Fin 3) = (1 : Fin 4) by decide] using
      geometricFactor_degree_le K R.1 hRne g (0 : Fin 3)
  have hgS : (geometricFlag K g).all ≤ (regularFlag Q R).all := by
    simpa only [geometricFlag, regularFlag,
      show Fin.succ (1 : Fin 3) = (2 : Fin 4) by decide] using
      geometricFactor_degree_le K R.1 hRne g (1 : Fin 3)
  have hflagY : (geometricFlag K g).yz + (geometricFlag K g).all ≤ 51 := by
    calc
      _ ≤ fixedProfile.yCap + fixedProfile.slopeCap :=
        Nat.add_le_add (hgY.trans hRY) (hgS.trans hRS)
      _ = 51 := by norm_num [fixedProfile, Profile.yCap]
  have hflagS : (geometricFlag K g).all ≤ 8 := by
    exact (hgS.trans hRS).trans_eq (by norm_num [fixedProfile])
  have hflagZ : (geometricFlag K g).zOnly + (geometricFlag K g).yz +
      (geometricFlag K g).all ≤ 976 := by
    calc
      _ ≤ fixedProfile.seedTotalCap + fixedProfile.yCap +
          fixedProfile.slopeCap :=
        Nat.add_le_add
          (Nat.add_le_add (hgZ.trans hRZ) (hgY.trans hRY))
          (hgS.trans hRS)
      _ = 976 := by norm_num [fixedProfile, Profile.yCap]
  have hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ fixedSupport S :=
    terminalAdaptiveProjectionFamiliesSharpYZ_of_active_yz_caps
      fixedSupport (by norm_num [fixedSupport]) S
      51 8 976 11009965 1966065
      hflagY hflagS hflagZ
      (by norm_num [fixedProfile, fixedSupport])
      (by norm_num [fixedProfile, fixedSupport])
      ⟨by norm_num [prime], by norm_num [prime], by norm_num [prime]⟩
      (by norm_num [prime])
  exact recursive_scaled_factorSharpYZ_of_adaptive_projection_families
    (polynomialEmbedding_injective K) fixedProfile fixedSupport
    (by norm_num [fixedSupport]) S hnodesS hagreementS
    fixed_characteristic_gates.2.2.2.2.1
    fixed_characteristic_gates.2.2.2.2.2.1
    fixed_degree_part_bound fixed_unit_part_bound hprojection

/-- Direction-generic rectangular aggregation for the target sharp-YZ
regular ledger. -/
theorem sum_regular_factor_counts_le_numerator
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ F, count F * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularFlag Q F)) :
    (∑ F, count F) * fixedProfile.gap ^ 2 ≤
      fixedSharpYZRegularNumerator := by
  have hcaps := regularFlag_budgets fixedProfile Q hQ
    (by norm_num [fixedProfile]) hbox
  calc
    (∑ F, count F) * fixedProfile.gap ^ 2 =
        ∑ F, count F * fixedProfile.gap ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ F, factorRegularLedgerYZForDirection fixedProfile
        fixedSharpDirection (regularFlag Q F) :=
      Finset.sum_le_sum (fun F _ ↦ hcount F)
    _ ≤ factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        fixedProfile.rectangularSurfaceFlag :=
      sum_factorRegularLedgerYZForDirection_le_flag fixedProfile
        fixedSharpDirection (regularFlag Q) fixedProfile.rectangularSurfaceFlag
        hcaps.1 hcaps.2.1 hcaps.2.2
    _ = fixedSharpYZRegularNumerator := rfl

/-- Strong inclusive fixed-cell cap.  This is two below the sum of the two
strict per-branch ceilings recorded in the arithmetic module. -/
theorem fixed_selected_count_le_exact_cap
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors) :
    Gamma.card ≤ 247648344661646309 := by
  have hA : FixedParameterAlignment fixedProfile fixedTightProfile :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h := global_count_le_regular_div_add_tight_countCap
    fixedProfile fixedTightProfile hA Q hQ hbox
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime, Profile.algebraicCap])
    (by norm_num [fixedTightProfile, prime,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa])
    (by norm_num [fixedTightProfile, prime,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile])
    selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement
    hnoPencil
    (factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection)
    (fun count _hcount ↦
      sum_regular_factor_counts_le_numerator Q hQ hbox count _hcount)
    (regular_factor_seed_bound Q hQ hbox selected Gamma nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)
  rw [fixed_sharp_yz_regular_numerator_exact,
    fixed_tight_singular_count_cap_exact] at h
  norm_num [fixedProfile, Profile.gap] at h ⊢
  exact h

/-- Safe fixed cost used by the six-ledger arithmetic: the sum of the two
strict branch ceilings. -/
theorem fixed_selected_count_le_fixedCountCeiling
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors) :
    Gamma.card ≤ fixedCountCeiling := by
  have h := fixed_selected_count_le_exact_cap Q hQ hbox selected Gamma
    nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  rw [fixed_count_ceiling_exact]
  exact h.trans (by norm_num)

end

end ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research

#print axioms ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research.fixedRegularGeometricResidualStage
#print axioms ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research.regular_factor_seed_bound
#print axioms ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research.fixed_selected_count_le_exact_cap
#print axioms ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research.fixed_selected_count_le_fixedCountCeiling
