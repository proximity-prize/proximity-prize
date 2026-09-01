import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research
import ProximityPrize.SubmissionLower.ContactFixedMeetFactorIncidence6656Research
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research
open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualIterationResearch.ResidualStage
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactIdentityResidualComponentFamilyAll6600Research
open ContactIdentityResidualFactorIncidence6600Research
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactResidualSupportParametersResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactRobustFixedMeet6656Research
open ContactFixedMeetFactorIncidence6656Research
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 40000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalLargeZChargeOfSupport
    {support:ResidualSupportParameters} {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w support)
    (D:S.TerminalDescendant) (i:Iota)
    (B:PrimeFlagBudgetFamily
      (G:=D.stage.G)
      (T:=agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H:=regularitySurface phi D.stage.F)
      flag (support.residualAgreementFlag D.degree)):Prop:=
  let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
  let T:=agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD:=agreements-(w-D.degree)
  ∀ C:RegularComponent Omega D.stage.G T
      (regularitySurface phi D.stage.F),
    let GammaC:=componentSeeds Omega D.stage.G T
      (regularitySurface phi D.stage.F) GammaI
      (selectedPoint phi D.stage.selected) C
    let SC:=regularComponentCurveStageOfSupport support D.stage.F D.stage.G T
      D.stage.selected GammaI D.stage.nodes x D.stage.u0 D.stage.u1
      pchar errors D.degree flag (support.residualAgreementFlag D.degree)
      D.stage.G_dvd_surface D.stage.flag_support
      (surfaceMap_agreement_in_flag_of_support support
        D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
        D.stage.surface_total_weight D.degree
        (fun j↦(j.factorial:K)⁻¹)
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.stage.x_injective
      (fun gamma hgamma↦D.stage.degree_le gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma↦D.stage.solution gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma↦D.stage.regular gamma
        (Finset.mem_filter.mp hgamma).1)
      (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree errors (Finset.filter_subset _ _) D.stage.no_large_pencil)
      D.stage.characteristic_bound C
    ∀ E:SC.TerminalDescendant,
      E.degree < E.stage.identities.card →
        GammaC.card*(aD-D.degree) ≤
          (errors+1)*(aD-D.degree)*B.zCost C
abbrev TerminalLargeZCharge
    {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w)
    (D:S.TerminalDescendant) (i:Iota)
    (B:PrimeFlagBudgetFamily
      (G:=D.stage.G)
      (T:=agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H:=regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree)):Prop:=
  TerminalLargeZChargeOfSupport S D i B
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile
    (hphi:Function.Injective phi)
    (n a w e U V:ℕ)
    {support:ResidualSupportParameters} {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar e flag w support)
    (hnodes:S.nodes.card=n)
    (hagreement:∀ gamma∈Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hwa:w < a) (_han:a ≤ n)
    (hdegreeGlobal:∀ k ≤ w,
      (n-k)*(a-w)*(w-k) ≤ U*(a-k))
    (hunitGlobal:∀ k ≤ w,
      (n-k)*(a-w) ≤ V*(a-k))
    (D:S.TerminalDescendant) (i:Iota) (_hi:i∈D.stage.nodes)
    (B:PrimeFlagBudgetFamily
      (G:=D.stage.G)
      (T:=agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H:=regularitySurface phi D.stage.F)
      flag (support.residualAgreementFlag D.degree))
    (hallPositive:∀ C:RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*(a-w) ≤
      D.degree*
          ((flagMixed flag support.agreementDirection support.agreementDirection*
              U+
            flagMixed flag support.agreementDirection unitYZFlag*
              V)+
            (e+1)*(a-w)*
              (flagMixed flag support.agreementDirection unitZFlag+
                flagMixed flag support.agreementDirection unitAllFlag))+
        ((flagMixed flag support.agreementDirection unitYZFlag*
              U+
            flagMixed flag unitYZFlag unitYZFlag*V)+
          (e+1)*(a-w)*
            (flagMixed flag unitYZFlag unitZFlag+
              flagMixed flag unitYZFlag unitAllFlag)):=by
  classical
  let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
  let T:=agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD:=a-(w-D.degree)
  have hTflag:PolynomialInFlag
      (support.residualAgreementFlag D.degree) T:=by
    exact surfaceMap_agreement_in_flag_of_support support
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j↦(j.factorial:K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hsub:GammaI ⊆ Gamma:=Finset.filter_subset _ _
  have hTpoint:∀ gamma∈GammaI,
      MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T=0:=by
    intro gamma hgamma
    obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hgamma
    exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
      pchar D.degree D.stage.characteristic_bound gamma
      (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
      (D.stage.regular gamma hGamma)
      (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
  have hinnerAgreement:∀ gamma∈GammaI,
      aD ≤ (D.stage.nodes.filter (fun j↦
        (D.stage.selected gamma).eval (x j)=
          D.stage.u0 j+gamma*D.stage.u1 j)).card:=by
    intro gamma hgamma
    have hGamma:=hsub hgamma
    have h0:=Nat.sub_le_sub_right (hagreement gamma hGamma)
      (w-D.degree)
    exact h0.trans (by
      simpa only [aD,ResidualStage.agreementFiber,
        ResidualStage.Agrees] using D.agreement_card gamma hGamma)
  have hda:D.degree < aD:=by
    have hD:=D.degree_le
    dsimp only [aD]
    omega
  have hdegree:∀ k ≤ D.degree,
      (D.stage.nodes.card-k)*(aD-D.degree)*(D.degree-k) ≤
        U*(aD-k):=by
    intro k hk
    have hDle:D.degree ≤ w:=D.degree_le
    let total:=(w-D.degree)+k
    have htotal:total ≤ w:=by
      dsimp only [total]
      omega
    have h:=hdegreeGlobal total htotal
    have hnodesD:=D.nodes_card
    rw [hnodes] at hnodesD
    have hgap:
        aD-D.degree=a-w:=by
      dsimp only [aD]
      omega
    have hn:n-total=D.stage.nodes.card-k:=by
      rw [hnodesD]
      dsimp only [total]
      omega
    have hw:w-total=D.degree-k:=by
      dsimp only [total]
      omega
    have ha:a-total=aD-k:=by
      dsimp only [total,aD]
      omega
    rw [hgap]
    rw [hn,hw,ha] at h
    exact h
  have hunit:∀ k ≤ D.degree,
      (D.stage.nodes.card-k)*(aD-D.degree) ≤
        V*(aD-k):=by
    intro k hk
    have hDle:D.degree ≤ w:=D.degree_le
    let total:=(w-D.degree)+k
    have htotal:total ≤ w:=by
      dsimp only [total]
      omega
    have h:=hunitGlobal total htotal
    have hnodesD:=D.nodes_card
    rw [hnodes] at hnodesD
    have hgap:
        aD-D.degree=a-w:=by
      dsimp only [aD]
      omega
    have hn:n-total=D.stage.nodes.card-k:=by
      rw [hnodesD]
      dsimp only [total]
      omega
    have ha:a-total=aD-k:=by
      dsimp only [total,aD]
      omega
    rw [hgap]
    rw [hn,ha] at h
    exact h
  have hbound:=
    proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
    hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
    x D.stage.u0 D.stage.u1 pchar e D.degree aD
    U V flag
    (support.residualAgreementFlag D.degree) support
    D.stage.G_dvd_surface D.stage.flag_support hTflag
    D.stage.surface_s_weight D.stage.surface_ys_weight
    D.stage.surface_total_weight D.stage.x_injective
    (fun gamma hgamma↦D.stage.degree_le gamma (hsub hgamma))
    (fun gamma hgamma↦D.stage.solution gamma (hsub hgamma))
    (fun gamma hgamma↦D.stage.regular gamma (hsub hgamma))
    (fun gamma hgamma↦D.stage.on_component gamma (hsub hgamma))
    hTpoint hinnerAgreement
    (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
      D.degree e hsub D.stage.no_large_pencil)
    D.stage.characteristic_bound hda B (by
      simpa only [T] using hallPositive)
    hdegree hunit
  have hgapEq:aD-D.degree=a-w:=by
    have:=D.degree_le
    dsimp only [aD]
    omega
  rw [hgapEq] at hbound
  rw [flagMixed_supportResidualAgreement_direction,
    flagMixed_supportResidualAgreement_unit,
    flagMixed_supportResidualAgreement_z,
    flagMixed_supportResidualAgreement_all] at hbound
  dsimp only [GammaI] at hbound
  calc
    _ ≤ _:=hbound
    _=_:=by ring
theorem terminal_outer_fiber_bound_of_prime_flag_budget_of_support
    (hphi:Function.Injective phi)
    {support:ResidualSupportParameters} {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w support)
    (hnodes:S.nodes.card=n)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (D:S.TerminalDescendant) (i:Iota) (hi:i∈D.stage.nodes)
    (B:PrimeFlagBudgetFamily
      (G:=D.stage.G)
      (T:=agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H:=regularitySurface phi D.stage.F)
      flag (support.residualAgreementFlag D.degree))
    (hallPositive:∀ C:RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
      D.degree*
          ((flagMixed flag support.agreementDirection support.agreementDirection*
              degreeIncidence+
            flagMixed flag support.agreementDirection unitYZFlag*
              unitIncidence)+
            (errors+1)*gap*
              (flagMixed flag support.agreementDirection unitZFlag+
                flagMixed flag support.agreementDirection unitAllFlag))+
        ((flagMixed flag support.agreementDirection unitYZFlag*
              degreeIncidence+
            flagMixed flag unitYZFlag unitYZFlag*unitIncidence)+
          (errors+1)*gap*
            (flagMixed flag unitYZFlag unitZFlag+
              flagMixed flag unitYZFlag unitAllFlag)):=by
  apply terminal_outer_fiber_bound_of_prime_flag_budget_profile hphi
    n agreements w errors degreeIncidence unitIncidence S hnodes hagreement
    (by norm_num [agreements,n,errors,w])
    (by norm_num [agreements,n,errors])
    (fun k hk => by simpa only [gap] using degree_part_bound k hk)
    (fun k hk => by simpa only [gap] using unit_part_bound k hk)
    D i hi B hallPositive
theorem terminal_outer_fiber_bound_of_prime_flag_budget
    (hphi:Function.Injective phi)
    {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w)
    (hnodes:S.nodes.card=n)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (D:S.TerminalDescendant) (i:Iota) (hi:i∈D.stage.nodes)
    (B:PrimeFlagBudgetFamily
      (G:=D.stage.G)
      (T:=agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H:=regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree))
    (hallPositive:∀ C:RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
      D.degree*
          ((flagMixed flag agreementDirection6600 agreementDirection6600*
              degreeIncidence+
            flagMixed flag agreementDirection6600 unitYZFlag*
              unitIncidence)+
            (errors+1)*gap*
              (flagMixed flag agreementDirection6600 unitZFlag+
                flagMixed flag agreementDirection6600 unitAllFlag))+
        ((flagMixed flag agreementDirection6600 unitYZFlag*
              degreeIncidence+
            flagMixed flag unitYZFlag unitYZFlag*unitIncidence)+
          (errors+1)*gap*
            (flagMixed flag unitYZFlag unitZFlag+
              flagMixed flag unitYZFlag unitAllFlag)):=by
  simpa [ResidualSupportParameters.acceptedSupport,
    ResidualSupportParameters.agreementDirection,agreementDirection6600] using
    terminal_outer_fiber_bound_of_prime_flag_budget_of_support
      hphi S hnodes hagreement D i hi B hallPositive
theorem recursive_scaled_factor_6600_of_prime_flag_budgets_of_support
    (hphi:Function.Injective phi)
    {support:ResidualSupportParameters} {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w support)
    (hnodes:S.nodes.card=n)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
      i∈D.stage.nodes →
      ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      ∃ B:PrimeFlagBudgetFamily
        (G:=D.stage.G)
          (T:=agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (H:=regularitySurface phi D.stage.F)
        flag (support.residualAgreementFlag D.degree),
        ∀ C:RegularComponent Omega D.stage.G
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    Gamma.card*gap^2 ≤
      factorRegularLedgerFor flag support.agreementDirection:=by
  apply recursive_scaled_factor_with_support_6600 hphi support S flag
    hnodes hagreement
  intro D i hi hproper
  obtain ⟨B,hallPositive⟩:=hbudget D i hi hproper
  exact terminal_outer_fiber_bound_of_prime_flag_budget_of_support
    hphi S hnodes hagreement D i hi B hallPositive
theorem recursive_scaled_factor_6656_of_prime_flag_budgets
    (hphi:Function.Injective phi)
    {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
      ResidualSupportParameters.fixedMeetSupport)
    (hnodes:S.nodes.card=meetProfile.n)
    (hagreement:∀ gamma∈Gamma,
      meetProfile.agreements ≤ (S.agreementFiber gamma).card)
    (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
      i∈D.stage.nodes →
      ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      ∃ B:PrimeFlagBudgetFamily
        (G:=D.stage.G)
        (T:=agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (H:=regularitySurface phi D.stage.F)
        flag (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
          D.degree),
        ∀ C:RegularComponent Omega D.stage.G
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    Gamma.card*meetProfile.gap^2 ≤
      meetProfile.factorRegularLedger flag:=by
  apply recursive_scaled_factor_6656 hphi S flag hnodes hagreement
  intro D i hi hproper
  obtain ⟨B,hallPositive⟩:=hbudget D i hi hproper
  have h:=terminal_outer_fiber_bound_of_prime_flag_budget_profile hphi
    meetProfile.n meetProfile.agreements meetProfile.w meetProfile.errors
    meetProfile.degreeIncidence meetProfile.unitIncidence S hnodes hagreement
    (by norm_num [meetProfile]) (by norm_num [meetProfile])
    meet_degree_part_bound meet_unit_part_bound D i hi B hallPositive
  simpa only [Profile.gap,meetFactorDegreeCost,meetFactorUnitCost] using h
theorem recursive_scaled_factor_6600_of_prime_flag_budgets
    (hphi:Function.Injective phi)
    {flag:FlagDegree}
    (S:ResidualStage phi Gamma x pchar errors flag w)
    (hnodes:S.nodes.card=n)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
      i∈D.stage.nodes →
      ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      ∃ B:PrimeFlagBudgetFamily
        (G:=D.stage.G)
        (T:=agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (H:=regularitySurface phi D.stage.F)
        flag (residualAgreementFlag D.degree),
        ∀ C:RegularComponent Omega D.stage.G
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
    Gamma.card*gap^2 ≤ factorRegularLedger flag:=by
  have h:=recursive_scaled_factor_6600_of_prime_flag_budgets_of_support
    hphi S hnodes hagreement hbudget
  calc
    Gamma.card*gap^2 ≤
        factorRegularLedgerFor flag
          ResidualSupportParameters.acceptedSupport.agreementDirection:=h
    _=factorRegularLedger flag:=by
      simp [factorRegularLedgerFor,factorRegularLedger,factorPrimary,
        factorZTail,factorAllTail,
        ResidualSupportParameters.acceptedSupport,
        ResidualSupportParameters.agreementDirection,
        agreementDirection6600]
      ring
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research
