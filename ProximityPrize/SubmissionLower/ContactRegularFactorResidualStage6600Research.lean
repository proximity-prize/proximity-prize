import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research
import ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research

/-!
# Actual regular-factor residual stages at score 66

This adapter specializes the canonical geometric residual stage to one of
the real positive-`R` factors in the global selected-family decomposition.
All solution, regularity, degree, agreement, and no-pencil fields are
inherited from the filtered original family.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

open scoped Classical
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactInterpolation ContactTranslation
open ContactGenericInitialPoint ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch ContactFlagBezout6543Research
open ContactNearPencil6600FactorLedgerResearch

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The exact initial stage for one geometric factor of one actual global
regular factor. -/
def regularGeometricResidualStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x prime errors (geometricFlag K g) w := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata :=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hRirred := hRdata.1
  have hRpos := hRdata.2.1
  have hRbox := hRdata.2.2
  have hsub := regularSeeds_subset Q selected Gamma R
  exact geometricResidualStage K R.1 hRirred hRpos hRbox selected
    (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
    (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.1)
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil) g

/-- Geometric recursive bounds aggregate to the exact original rectangular
factor ledger expected by the global selected-family join. -/
theorem regular_factor_seed_bound_of_geometric_counts
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card *
          gap ^ 2 ≤ factorRegularLedger (geometricFlag K g)) :
    (regularSeeds Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedger (regularFlag Q R) := by
  obtain ⟨hRirred, _, _⟩ :=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  simpa only [geometricFlag, regularFlag] using
    original_regular_seed_bound_of_geometric_factor_counts K R.1 hRirred
      selected (regularSeeds Q selected Gamma R) hsolutions hcount

end

end ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

#print axioms ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research.regularGeometricResidualStage
#print axioms ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research.regular_factor_seed_bound_of_geometric_counts
