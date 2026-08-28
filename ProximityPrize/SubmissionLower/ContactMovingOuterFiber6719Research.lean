import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research
import ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactMovingFactorLedger6719Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch

namespace ProximityPrize.SubmissionLower.ContactMovingOuterFiber6719Research
open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch ContactPost6464MinkowskiRecurrenceResearch
open ContactRobustFixedMeet6656Research ContactSharpTaylorFixedMeet6656Research
open ContactSharpTaylorYZFactorProviderResearch ContactMovingOuterBudget6719Research
open ContactMovingComponentIncidence6719Research ContactMovingAgreementCertificate6719Research
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
open ContactMovingPositiveLedger6719Research ContactRegularComponentYZPositivity6630Research

abbrev factorDegreeCost := ContactMovingFactorLedger6719Research.factorDegreeCost
abbrev factorUnitCost := ContactMovingFactorLedger6719Research.factorUnitCost
abbrev factorLedger := ContactMovingFactorLedger6719Research.regularLedger

theorem terminal_outer_fiber_bound
    {E : Type} [Field E] [IsAlgClosed E] [Algebra Omega E]
    [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E] [CharP E pchar]
    (hphi : Function.Injective phi)
    (p : Profile) (a b s : ℕ)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w (ContactMovingAgreementCertificate6719Research.support a b s))
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (_han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (D : S.TerminalDescendant) (i : Iota) (hi : i ∈ D.stage.nodes)
    (hproper : ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
      (x i) (D.stage.u0 i) (D.stage.u1 i))
    (hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ (ContactMovingAgreementCertificate6719Research.support a b s) S)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * p.gap ≤
      D.degree * factorDegreeCost p a b s flag + factorUnitCost p a b s flag := by
  classical
  have hsy : s+2 < b+s+3 := by omega
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := p.agreements - (p.w - D.degree)
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag (ContactMovingAgreementCertificate6719Research.support a b s) D.degree) T := by
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
  obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
  obtain ⟨B, hcost, hz, hyz, hall, hmove⟩ := exists_actual_cut_budgets (E := E)
    phi D.stage.F D.stage.G T a b s D.degree (x i) (D.stage.u0 i) (D.stage.u1 i) rfl
    ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight, D.stage.surface_total_weight⟩
    flag D.stage.irreducible_G.ne_zero D.stage.G_dvd_surface D.stage.flag_support
    base P.family pchar hmix
  have hpositive : ∀ C : RegularComponent Omega D.stage.G T (regularitySurface phi D.stage.F),
      1 ≤ (B C).zCost + (B C).yzCost := by
    intro C
    rw [(hcost C).1, (hcost C).2.1]
    exact P.one_le_zCost_add_yzCost phi D.stage.F rfl D.stage.G_dvd_surface C
  have hbound :=
    proper_cut_seed_bound_of_moving_budgets
      hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
      x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
      p.degreeIncidence p.unitIncidence flag (sharpResidualAgreementFlag (ContactMovingAgreementCertificate6719Research.support a b s) D.degree) a b s
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
      D.stage.characteristic_bound hda base B hpositive
      (flagMixed flag (paddedCut a b s D.degree) unitZFlag)
      (flagMixed flag (paddedCut a b s D.degree) unitYZFlag)
      (flagMixed flag (paddedCut a b s D.degree) unitAllFlag)
      (flagMixed flag (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
        (center a b s + D.degree • ContactMovingPositiveLedger6719Research.surfaceFlag a b s))
      hz hyz hall hmove hdegree hunit
  have hgapEq : aD - D.degree = p.gap := by
    have := D.degree_le
    dsimp only [aD, Profile.gap]
    omega
  rw [hgapEq] at hbound
  change GammaI.card * p.gap ≤
    p.degreeIncidence * (weightedMixed flag (paddedCut a b s D.degree) (normalFlag a b s) +
      flagMixed flag (fiberFlag a b s) (centreFlag a b s + D.degree • surfaceFlag a b s)) +
    p.unitIncidence * weightedMixed flag (paddedCut a b s D.degree) (centreFlag a b s) +
    (p.errors+1)*p.gap*(flagMixed flag (paddedCut a b s D.degree) unitZFlag +
      flagMixed flag (paddedCut a b s D.degree) unitYZFlag) at hbound
  dsimp only [paddedCut] at hbound
  rw [envelope_identity, centre_identity, z_affine, yz_affine] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by
      unfold factorDegreeCost factorUnitCost
        ContactMovingFactorLedger6719Research.factorDegreeCost
        ContactMovingFactorLedger6719Research.factorUnitCost
      ring

theorem recursive_scaled_moving_factor
    {E : Type} [Field E] [IsAlgClosed E] [Algebra Omega E]
    [Algebra (RatFunc Omega) E] [IsScalarTower Omega (RatFunc Omega) E] [CharP E pchar]
    (hphi : Function.Injective phi)
    (p : Profile) (a b s : ℕ)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w (ContactMovingAgreementCertificate6719Research.support a b s))
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hwa : p.w < p.agreements) (han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (hprojection : TerminalAdaptiveProjectionFamiliesSharpYZ
      (ContactMovingAgreementCertificate6719Research.support a b s) S)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar) :
    Gamma.card * p.gap^2 ≤ factorLedger p a b s flag := by
  have h := recursive_scaled_stratified_incidence_bound hphi S
    (factorDegreeCost p a b s flag) (factorUnitCost p a b s flag)
    p.degreeIncidence p.unitIncidence hwa hagreement
    (by
      intro D i hi hproper
      exact terminal_outer_fiber_bound (E := E) hphi p a b s S hnodes
        hagreement hwa han hdegreeGlobal hunitGlobal D i hi hproper hprojection hmix)
    (by intro k hk; simpa only [hnodes, Profile.gap] using hdegreeGlobal k hk)
    (by intro k hk; simpa only [hnodes, Profile.gap] using hunitGlobal k hk)
  simpa only [Profile.gap, factorLedger, ContactMovingFactorLedger6719Research.regularLedger] using h

end
end ProximityPrize.SubmissionLower.ContactMovingOuterFiber6719Research
