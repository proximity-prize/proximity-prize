import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZSupportResearch
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjectionFixedMeetActive6656Research

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactProfileYZFactorProviderResearch

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactIdentityResidualComponentFamilyYZSupportResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualFactorProvider6600Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactProfileYZFactorLedgerResearch
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactTerminalAdaptiveProjectionFixedMeetActive6656Research

noncomputable section

set_option maxHeartbeats 3500000
set_option maxRecDepth 40000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- .


 -/
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile_z_yz
    (hphi : Function.Injective phi)
    (p : Profile) (support : ResidualSupportParameters)
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
      flag (support.residualAgreementFlag D.degree))
    (hzyzPositive : ∀ C : RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F), 1 ≤ B.zCost C + B.yzCost C) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * p.gap ≤
      D.degree * factorDegreeCostYZ p support.agreementDirection flag +
        factorUnitCostYZ p support.agreementDirection flag := by
  classical
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := p.agreements - (p.w - D.degree)
  have hTflag : PolynomialInFlag
      (support.residualAgreementFlag D.degree) T := by
    exact surfaceMap_agreement_in_flag_of_support support
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j ↦ (j.factorial : K)⁻¹)
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
    proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz_of_direction
      hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
      x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
      p.degreeIncidence p.unitIncidence flag
      (support.residualAgreementFlag D.degree) support
      support.agreementDirection D.stage.G_dvd_surface D.stage.flag_support
      hTflag D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.stage.x_injective
      (fun gamma hgamma ↦ D.stage.degree_le gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.solution gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.regular gamma (hsub hgamma))
      (fun gamma hgamma ↦ D.stage.on_component gamma (hsub hgamma))
      hTpoint hinnerAgreement
      (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree p.errors hsub D.stage.no_large_pencil)
      D.stage.characteristic_bound hda B
      (fun C t ↦ B.weightedCost_supportResidualAgreementFlag support C t)
      (by simpa only [T] using hzyzPositive) hdegree hunit
  have hgapEq : aD - D.degree = p.gap := by
    have := D.degree_le
    dsimp only [aD, Profile.gap]
    omega
  rw [hgapEq] at hbound
  rw [flagMixed_supportResidualAgreement_direction,
    flagMixed_supportResidualAgreement_unit,
    flagMixed_supportResidualAgreement_z] at hbound
  have hyz := flagMixed_supportResidualAgreement_unit flag support D.degree
  dsimp only [GammaI] at hbound
  simp only [factorDegreeCostYZ, factorUnitCostYZ]
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

/-- .
 -/
theorem recursive_scaled_factorYZ_of_adaptive_projection_families
    (hphi : Function.Injective phi)
    (p : Profile) (support : ResidualSupportParameters)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w support)
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (halign : support.agreementDirection = p.agreementDirection)
    (hwa : p.w < p.agreements) (han : p.agreements ≤ p.n)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (hprojection : TerminalAdaptiveProjectionFamiliesYZOfSupport support S) :
    Gamma.card * p.gap ^ 2 ≤ factorRegularLedgerYZ p flag := by
  change Gamma.card * p.gap ^ 2 ≤
    factorRegularLedgerYZForDirection p p.agreementDirection flag
  rw [← halign]
  apply recursive_scaled_factorYZ hphi p support support.agreementDirection S
    hwa hagreement
  · intro D i hi hproper
    obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
    exact terminal_outer_fiber_bound_of_prime_flag_budget_profile_z_yz
      hphi p support S hnodes hagreement hwa han hdegreeGlobal hunitGlobal
      D i hi P.family.toPrimeFlagBudgetFamily
      (fun C ↦ P.one_le_zCost_add_yzCost phi D.stage.F rfl
        D.stage.G_dvd_surface C)
  · intro k hk
    simpa only [hnodes] using hdegreeGlobal k hk
  · intro k hk
    simpa only [hnodes] using hunitGlobal k hk

end

end ProximityPrize.SubmissionLower.ContactProfileYZFactorProviderResearch
