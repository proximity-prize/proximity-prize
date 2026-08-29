import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research
import ProximityPrize.SubmissionLower.ContactGCDCumulativeLedgerResearch

/-!
# Cumulative-flag fixed selected cell

This module instantiates the generic sharp-Taylor active-YZ factor provider
and the profile-generic tight selected-family combiner at the fixed GCD meet.
The actual GCD supplies its sharper cumulative support as an explicit premise.
-/

namespace ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research

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
open ContactFixedMeetProfile6670Research
open ContactGCDCumulativeFlagsResearch ContactGCDCumulativeLedgerResearch

noncomputable section

set_option maxHeartbeats 7000000
set_option maxRecDepth 100000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The sharper support supplied for the actual GCD passes to every divisor. -/
theorem fixedSupport_of_dvd
    (F Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (Hsupport : ResidualSupportData fixedSupport Q) :
    ResidualSupportData fixedSupport F := by
  exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans
      Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans
      Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans
      Hsupport.total_weight⟩

/-- Canonical fixed-profile residual stage for one geometric factor of one
actual positive-`R` factor. -/
def fixedRegularGeometricResidualStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
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
      x prime fixedProfile.errors (geometricCumulativeFlag K g) fixedProfile.w
      fixedSupport := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt
        (by norm_num [fixedProfile, prime])
  have hsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
  let S := regularGeometricResidualStageOfSupport fixedSupport Q selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
    hsupport (by norm_num [fixedProfile, prime]) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)

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
          (geometricCumulativeFlag K g)) :
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularCumulativeFlag Q R) := by
  obtain ⟨hRirred, _, _⟩ := directFactor_data Q R.1 hQ
    fixedProfile.weightedCap fixedProfile.w fixedProfile.seedTotalCap
      fixedProfile.slopeCap hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  exact geometric_seed_counts_cumulative_le fixedProfile fixedSharpDirection
    R.1 hRirred.ne_zero selected (regularSeeds Q selected Gamma R)
    hsolutions hcount

/-- Every actual positive-`R` factor receives its sharp-YZ ledger from the
canonical active-YZ terminal families. -/
theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
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
        (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  apply regular_factor_seed_bound_of_geometric_sharp_yz_counts Q hQ hbox
    selected Gamma R
  intro g
  let S := fixedRegularGeometricResidualStage Q hQ hbox Hsupport selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds Q selected Gamma R) g).trans
      (regularSeeds_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = fixedProfile.n := by
    simpa [S, fixedRegularGeometricResidualStage, reflagResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g,
      fixedProfile.agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
      fixedRegularGeometricResidualStage, reflagResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using
        hagreement gamma (hgeomSub hgamma)
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hRsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
  have hflags := geometricCumulativeFlag_le_support R.1 hRne hRsupport g
  have hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ fixedSupport S :=
    terminalAdaptiveProjectionFamiliesSharpYZ_of_active_yz_caps
      fixedSupport (by norm_num [fixedSupport]) S
      fixedSupport.ys fixedSupport.s fixedSupport.total
      (1 + fixedProfile.w * (2 * fixedSupport.ys - 2))
      ((2 * fixedSupport.s - 1) * fixedProfile.w)
      hflags.2.1 hflags.1 hflags.2.2 le_rfl le_rfl
      ⟨by norm_num [fixedSupport, prime],
        by norm_num [fixedSupport, prime],
        by norm_num [fixedSupport, prime]⟩
      (by norm_num [fixedProfile, fixedSupport, prime])
  exact recursive_scaled_factorSharpYZ_of_adaptive_projection_families
    (polynomialEmbedding_injective K) fixedProfile fixedSupport
    (by norm_num [fixedSupport]) S hnodesS hagreementS
    fixed_characteristic_gates.2.2.2.2.1
    fixed_characteristic_gates.2.2.2.2.2.1
    fixed_degree_part_bound fixed_unit_part_bound hprojection

/-- Direction-generic cumulative aggregation for the target sharp-YZ
regular ledger. -/
theorem sum_regular_factor_counts_le_numerator
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ F, count F * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (regularCumulativeFlag Q F)) :
    (∑ F, count F) * fixedProfile.gap ^ 2 ≤
      fixedSharpYZRegularNumerator := by
  exact sum_regular_counts_cumulative_le fixedProfile fixedSharpDirection
    Q hQ Hsupport count hcount

/-- Strong inclusive fixed-cell cap.  This is two below the sum of the two
strict per-branch ceilings recorded in the arithmetic module. -/
theorem fixed_selected_count_le_exact_cap
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
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
    Gamma.card ≤ fixedSharpYZRegularNumerator / fixedProfile.gap ^ 2 +
      fixedTightProfile.countCap := by
  have hA : FixedParameterAlignment fixedProfile fixedTightProfile :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact global_count_le_regular_div_add_tight_countCap
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
    (regularCumulativeFlag Q)
    (factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection)
    (fun count _hcount ↦
      sum_regular_factor_counts_le_numerator Q hQ Hsupport count _hcount)
    (regular_factor_seed_bound Q hQ hbox Hsupport selected Gamma nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)

/-- Safe fixed cost used by the six-ledger arithmetic: the sum of the two
strict branch ceilings. -/
theorem fixed_selected_count_le_fixedCountCeiling
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
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
  have h := fixed_selected_count_le_exact_cap Q hQ hbox Hsupport selected Gamma
    nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  exact h.trans (by
    dsimp [fixedCountCeiling, fixedSharpYZRegularCeiling, fixedTightSingularCeiling]
    omega)

end

end ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research
