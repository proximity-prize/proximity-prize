import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research
import ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research
namespace ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research
open scoped Classical
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactInterpolation ContactTranslation
open ContactGenericInitialPoint ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFactorCaps
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactNearPencil6600FactorLedgerResearch
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def regularGeometricResidualStageOfSupport
    (support:ResidualSupportParameters)
    {pchar errorCap degree:ℕ} [CharP K pchar]
    (Q:MvPolynomial (Fin 4) K)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota → K)
    (hinj:Set.InjOn x nodes)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
    (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
    (R:ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hRirred:Irreducible R.1)
    (hRpos:0 < R.1.degreeOf (2:Fin 4))
    (hRsmall:R.1.degreeOf (2:Fin 4) < pchar)
    (hRsupport:ResidualSupportData support R.1)
    (hdegreeChar:degree < pchar)
    (g:GeometricFactor K R.1):
    letI:CharP (GenericField K) pchar:=genericField_charP K pchar
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x pchar errorCap (geometricFlag K g) degree support:=by
  have hsub:=regularSeeds_subset Q selected Gamma R
  exact geometricResidualStageOfSupport K support R.1 hRirred hRpos
    hRsmall hRsupport selected
    (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
    (fun gamma hgamma↦hdegree gamma (hsub hgamma))
    (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.1)
    (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ degree errorCap hsub hnoPencil)
    hdegreeChar g
def regularGeometricResidualStage
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota → K)
    (hinj:Set.InjOn x nodes)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
    (R:ContactRegularFactorFlag6600Research.RegularIndex Q)
    (g:GeometricFactor K R.1):
    letI:CharP (GenericField K) prime:=genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x prime errors (geometricFlag K g) w:=by
  have hRdata:=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) < prime:=
    (degreeOf_R_le_of_mem_box R.1 weightedCap w seedTotalCap slopeCap
      hRdata.2.2).trans_lt (by norm_num [slopeCap,prime])
  have hsupport:=residual_surface_weights_of_box K R.1 hRdata.2.2
  exact regularGeometricResidualStageOfSupport
    ResidualSupportParameters.acceptedSupport Q selected Gamma nodes x u0 u1
    hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
    ⟨hsupport.1,hsupport.2.1,hsupport.2.2⟩
    (by norm_num [w,prime]) g
theorem regular_factor_seed_bound_of_geometric_counts
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (R:ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hcount:∀ g:GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card*
          gap^2 ≤ factorRegularLedger (geometricFlag K g)):
    (regularSeeds Q selected Gamma R).card*gap^2 ≤
      factorRegularLedger (regularFlag Q R):=by
  obtain ⟨hRirred,_,_⟩:=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hsolutions:∀ gamma∈regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  simpa only [geometricFlag,regularFlag] using
    original_regular_seed_bound_of_geometric_factor_counts K R.1 hRirred
      selected (regularSeeds Q selected Gamma R) hsolutions hcount
end
end ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research
