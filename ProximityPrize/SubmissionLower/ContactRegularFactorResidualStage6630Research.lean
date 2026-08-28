import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularSeeds6630Research
import ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6630Research
import ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6641Research

/-!
# Actual regular-factor residual stages at score 66.30

This adapter specializes the nested-Newton geometric residual stage to one
positive-`R` factor in the global selected-family decomposition.  Its second
theorem aggregates the geometric-factor estimates through cumulative support
functionals, rather than charging a separate rectangular box to every factor.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6630Research

set_option autoImplicit false

open scoped Classical
open ContactParameters6630Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation
open ContactGenericInitialPoint ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6630Research
open ContactRegularFactorFlag6630Research ContactRegularSeeds6630Research
open ContactIdentityResidualIteration6630Research ContactFlagBezout6543Research
open ContactNearPencil6630FactorLedgerResearch
open ContactFlagRegularFactorCaps6641Research
open ContactCumulativeWeightedDegreeResearch
open ContactIdentityResidualGlobalFlagResearch ContactFactorCaps

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The exact initial stage for one geometric factor of one actual score-66.30
regular factor. -/
def regularGeometricResidualStage6630
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage6630 (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds6630 Q selected Gamma R) g)
      x prime errors (geometricFlag6630 K g) w := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata :=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hRirred := hRdata.1
  have hRpos := hRdata.2.1
  have hRbox := hRdata.2.2
  have hRdiv := (positiveRFactors_spec Q R.1 R.2).2.1
  have hQweights := residual_surface_weights_of_flagBox6641 Q hsharp
  have hRweights :
      MvPolynomial.weightedTotalDegree residualSWeights R.1 ≤ 10 ∧
      MvPolynomial.weightedTotalDegree residualYSWeights R.1 ≤ 48 ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights R.1 ≤ 814 :=
    ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hRdiv hQ).trans
        hQweights.1,
      (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hRdiv hQ).trans
        hQweights.2.1,
      (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hRdiv hQ).trans
        hQweights.2.2⟩
  have hsub := regularSeeds6630_subset Q selected Gamma R
  exact geometricResidualStage6630 K R.1 hRirred hRpos hRbox hRweights selected
    (regularSeeds6630 Q selected Gamma R) nodes x u0 u1 hinj
    (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.1)
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil) g

/-- Geometric recursive bounds aggregate to the exact nested Newton ledger of
the original regular factor. -/
theorem regular_factor_seed_bound_of_geometric_counts6630
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : RegularIndex Q)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected
          (regularSeeds6630 Q selected Gamma R) g).card * gap ^ 2 ≤
        factorRegularLedgerYZ (geometricFlag6630 K g)) :
    (regularSeeds6630 Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedgerYZ (regularFlag6630 Q R) := by
  obtain ⟨hRirred, _, _⟩ :=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds6630 Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  simpa only [originalFlag6630_eq_regularFlag] using
    original_regular_seed_bound_of_geometric_counts6630 K R.1 hRirred
      selected (regularSeeds6630 Q selected Gamma R) hsolutions hcount

end

end ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6630Research
