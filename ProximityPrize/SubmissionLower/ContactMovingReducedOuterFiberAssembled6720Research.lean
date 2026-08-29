import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingReducedBudget6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedTerminalNormalize6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedTerminalArithmetic6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedProperCut6720Research
import ProximityPrize.SubmissionLower.ContactMovingReducedTerminalAssembly6720Research
import ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research
import ProximityPrize.SubmissionLower.ContactReducedTaylorYZProjection6720Research

namespace ProximityPrize.SubmissionLower.ContactMovingReducedOuterFiber6720Research

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactFlagBezout6543Research
open ContactWeakSeparableSeparatorResearch
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch ContactPost6464MinkowskiRecurrenceResearch
open ContactRobustFixedMeet6656Research ContactSharpTaylorFixedMeet6656Research
open ContactReducedTaylorProfileResearch ContactReducedTaylorYZFactorProviderResearch
open ContactSharpTaylorYZFactorProviderResearch
open ContactMovingOuterBudget6719Research ContactMovingComponentIncidence6719Research
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research ContactCongruentCuts6643Research
open ContactMovingReducedBudget6720Research
open ContactMovingReducedPositiveLedger6720Research
open ContactMovingReducedFactorLedger6720Research
open ContactMovingReducedTerminalNormalize6720Research
open ContactMovingReducedTerminalArithmetic6720Research
open ContactMovingReducedProperCut6720Research
open ContactMovingReducedTerminalAssembly6720Research

noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

theorem terminal_outer_fiber_bound_reduced
    {E : Type} [Field E] [IsAlgClosed E] [Algebra Omega E]
    [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E]
    [CharP E pchar]
    (hphi : Function.Injective phi)
    (p : Profile) (a b s : ℕ) {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w (support a b s))
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (_han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n-k)*p.gap*(p.w-k) ≤ p.degreeIncidence*(p.agreements-k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
    (D : S.TerminalDescendant) (i : Iota) (hi : i ∈ D.stage.nodes)
    (hproper : ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
      (x i) (D.stage.u0 i) (D.stage.u1 i))
    (hprojectionSharp : TerminalAdaptiveProjectionFamiliesSharpYZ (support a b s) S)
    (hprojection : TerminalAdaptiveProjectionFamiliesReducedYZ (support a b s) S)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * p.gap ≤
      D.degree * factorDegreeCost p (support a b s) a b s flag +
        factorUnitCost p (support a b s) a b s flag := by
  classical
  have hsy : s+2 < b+s+3 := by omega
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := p.agreements - (p.w-D.degree)
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag (support a b s) D.degree) T :=
    surfaceMap_agreement_in_sharp_flag hsy (phi := phi)
      ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight,
        D.stage.surface_total_weight⟩ D.degree
      (fun j : ℕ ↦ (j.factorial : K)⁻¹)
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
          D.stage.u0 j + gamma*D.stage.u1 j)).card := by
    intro gamma hgamma
    have hGamma := hsub hgamma
    have h0 := Nat.sub_le_sub_right (hagreement gamma hGamma) (p.w-D.degree)
    exact h0.trans (by
      simpa only [aD, ResidualStage.agreementFiber, ResidualStage.Agrees]
        using D.agreement_card gamma hGamma)
  have hnodesD := D.nodes_card
  rw [hnodes] at hnodesD
  have hreindex := terminal_reindexed_bounds p D.degree D.stage.nodes.card
    D.degree_le hnodesD hwa hdegreeGlobal hunitGlobal
  have hda : D.degree < aD := by
    simpa only [aD, terminalAgreements] using hreindex.degree_lt_agreements
  have hdegree : ∀ k ≤ D.degree,
      (D.stage.nodes.card-k)*(aD-D.degree)*(D.degree-k) ≤
        p.degreeIncidence*(aD-k) := by
    simpa only [aD, terminalAgreements] using hreindex.degree
  have hunit : ∀ k ≤ D.degree,
      (D.stage.nodes.card-k)*(aD-D.degree) ≤ p.unitIncidence*(aD-k) := by
    simpa only [aD, terminalAgreements] using hreindex.unit
  obtain ⟨baseSharp, ⟨PSharp⟩⟩ := hprojectionSharp D i hi hproper
  obtain ⟨baseRed, ⟨PRed⟩⟩ := hprojection D i hi hproper
  let H : ProperCutStageData (phi := phi)
      D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
      x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
      p.degreeIncidence p.unitIncidence flag
      (sharpResidualAgreementFlag (support a b s) D.degree) a b s :=
    { hphi := hphi
      hdiv := D.stage.G_dvd_surface
      hGflag := D.stage.flag_support
      hTflag := hTflag
      hFs := D.stage.surface_s_weight
      hFys := D.stage.surface_ys_weight
      hFtotal := D.stage.surface_total_weight
      hinj := D.stage.x_injective
      hdegreeSelected := fun gamma hgamma ↦ D.stage.degree_le gamma (hsub hgamma)
      hsolution := fun gamma hgamma ↦ D.stage.solution gamma (hsub hgamma)
      hregular := fun gamma hgamma ↦ D.stage.regular gamma (hsub hgamma)
      hGpoint := fun gamma hgamma ↦ D.stage.on_component gamma (hsub hgamma)
      hTpoint := hTpoint
      hagreement := hinnerAgreement
      hnoPencil := noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree p.errors hsub D.stage.no_large_pencil
      hchar := D.stage.characteristic_bound
      hda := hda }
  have hgapEq : aD-D.degree = p.gap := by
    simpa only [aD, terminalAgreements] using hreindex.gap_eq
  exact terminal_bound_from_reduced_budgets (E := E)
    p a b s D.degree aD D.stage.F D.stage.G T D.stage.selected GammaI
    D.stage.nodes x D.stage.u0 D.stage.u1
    (x i) (D.stage.u0 i) (D.stage.u1 i) pchar flag H rfl
    D.stage.irreducible_G.ne_zero baseSharp PSharp.family baseRed PRed
    hmix hdegree hunit hgapEq

/-
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
-/

end
end ProximityPrize.SubmissionLower.ContactMovingReducedOuterFiber6720Research
