import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingReducedOuterFiberAssembled6720Research

namespace ProximityPrize.SubmissionLower.ContactMovingReducedOuterFiber6720Research

open scoped Classical BigOperators
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorYZFactorProviderResearch
open ContactReducedTaylorYZFactorProviderResearch
open ContactMovingComponentIncidence6719Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingReducedFactorLedger6720Research

noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

theorem recursive_scaled_moving_factor_reduced
    {E : Type} [Field E] [IsAlgClosed E] [Algebra Omega E]
    [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E]
    [CharP E pchar]
    (hphi : Function.Injective phi)
    (p : Profile) (a b s : ℕ) {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w (support a b s))
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n-k)*p.gap*(p.w-k) ≤ p.degreeIncidence*(p.agreements-k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
    (hprojectionSharp : TerminalAdaptiveProjectionFamiliesSharpYZ (support a b s) S)
    (hprojection : TerminalAdaptiveProjectionFamiliesReducedYZ (support a b s) S)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    Gamma.card*p.gap^2 ≤
      regularLedger p (support a b s) a b s flag := by
  have h := recursive_scaled_stratified_incidence_bound hphi S
    (factorDegreeCost p (support a b s) a b s flag)
    (factorUnitCost p (support a b s) a b s flag)
    p.degreeIncidence p.unitIncidence hwa hagreement
    (by
      intro D i hi hproper
      exact terminal_outer_fiber_bound_reduced (E := E) hphi p a b s S hnodes
        hagreement hwa han hdegreeGlobal hunitGlobal D i hi hproper
        hprojectionSharp hprojection hmix)
    (by intro k hk; simpa only [hnodes, Profile.gap] using hdegreeGlobal k hk)
    (by intro k hk; simpa only [hnodes, Profile.gap] using hunitGlobal k hk)
  simpa only [Profile.gap, regularLedger] using h

end
end ProximityPrize.SubmissionLower.ContactMovingReducedOuterFiber6720Research
