import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingFixedStage6719Research
import ProximityPrize.SubmissionLower.ContactMovingOuterFiber6719Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch

namespace ProximityPrize.SubmissionLower.ContactMovingFixedSelected6719Research

open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactOriginalRegularResidualStage6600Research ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch ContactResidualSupportParametersResearch
open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
open ContactGCDCumulativeFlagsResearch ContactSharpTaylorYZFactorProviderResearch
open ContactProfileFixedSelectedCombinerResearch
open ContactMovingFixedProfile6719Research ContactMovingFixedStage6719Research
open ContactMovingFactorLedger6719Research ContactMovingOuterFiber6719Research

noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _

/-- .
 -/
theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hagreement : ∀ γ ∈ Γ, fixedProfile.agreements ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i) = u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Γ R).card*fixedProfile.gap^2 ≤
      regularLedger fixedProfile 955 40 8 (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  let E := AlgebraicClosure (RatFunc (GenericField K))
  letI : IsScalarTower (GenericField K) (RatFunc (GenericField K)) E :=
    by infer_instance
  letI : CharP E prime := by infer_instance
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hsolutions : ∀ γ ∈ regularSeeds Q selected Γ R,
      specialization K (selected γ) γ R.1 = 0 := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2.1
  apply geometric_seed_counts_le fixedProfile 955 40 8 R.1 hRdata.1.ne_zero
    selected (regularSeeds Q selected Γ R) hsolutions
  intro g
  let S := fixedGeometricStage Q hQ hbox Hsupport selected Γ nodes x u0 u1
    hinj hdegree hnoPencil R g
  have hsub : geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g ⊆ Γ :=
    (geometricSeeds_subset K R.1 selected (regularSeeds Q selected Γ R) g).trans
      (regularSeeds_subset Q selected Γ R)
  have hnodesS : S.nodes.card = fixedProfile.n := by
    simpa [S, fixedGeometricStage, reflagResidualStage,
      regularGeometricResidualStageOfSupport, geometricResidualStageOfSupport] using hnodes
  have hagreementS : ∀ γ ∈ geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g,
      fixedProfile.agreements ≤ (S.agreementFiber γ).card := by
    intro γ hγ
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees, fixedGeometricStage,
      reflagResidualStage, regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using hagreement γ (hsub hγ)
  have hflags := geometric_flag_caps Q hQ hbox Hsupport R g
  have hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ fixedSupport S :=
    terminalAdaptiveProjectionFamiliesSharpYZ_of_active_yz_caps fixedSupport
      (by decide) S fixedSupport.ys fixedSupport.s fixedSupport.total
      (1+fixedProfile.w*(2*fixedSupport.ys-2))
      ((2*fixedSupport.s-1)*fixedProfile.w)
      hflags.2.1 hflags.1 hflags.2.2 le_rfl le_rfl
      ⟨by decide, by decide, by decide⟩ (by decide)
  have hsmall : 2*((geometricCumulativeFlag K g).zOnly+
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all)*
        (955+40+8+4) < prime :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hflags.2.2)).trans_lt
      fixed_small_moving_gate
  exact recursive_scaled_moving_factor (E := E) (polynomialEmbedding_injective K)
    fixedProfile 955 40 8 S hnodesS hagreementS (by decide) (by decide)
    fixed_degree_part_bound fixed_unit_part_bound hprojection hsmall

/-- .
 -/
theorem fixed_selected_count_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0)
    (hagreement : ∀ γ ∈ Γ, fixedProfile.agreements ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i) = u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors) :
    Γ.card ≤ ContactMovingParameters6719Research.fixedCost := by
  have h := global_count_le_regular_div_add_tight_countCap
    fixedProfile fixedTightProfile fixed_alignment Q hQ hbox
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    selected Γ nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
    (regularCumulativeFlag Q) (regularLedger fixedProfile 955 40 8)
    (fun count hcount ↦ sum_regular_counts_le fixedProfile 955 40 8
      Q hQ Hsupport count hcount)
    (regular_factor_seed_bound Q hQ hbox Hsupport selected Γ nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)
  exact h.trans fixed_inclusive_cost_le

end

end ProximityPrize.SubmissionLower.ContactMovingFixedSelected6719Research
