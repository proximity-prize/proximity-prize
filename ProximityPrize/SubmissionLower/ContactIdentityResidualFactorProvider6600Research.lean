import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research

/-!
# Factorwise score-66 provider from shared adaptive prime budgets

At a terminal node of the outer factor recursion, the proper agreement cut
is decomposed into its regular curve components.  The inner recursion and
shared prime budget then give exactly the affine fiber bound consumed by
`recursive_scaled_factor_6600`.
-/

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
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 40000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The exact unresolved large-pencil leaf for one outer terminal cut.
Keeping it as a named proposition makes the final factor theorem readable:
all recursive and component bookkeeping has already been discharged.
-/
def TerminalLargeZCharge
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (D : S.TerminalDescendant) (i : Iota)
    (B : PrimeFlagBudgetFamily
      (G := D.stage.G)
      (T := agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H := regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree)) : Prop :=
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := agreements - (w - D.degree)
  ∀ C : RegularComponent Omega D.stage.G T
      (regularitySurface phi D.stage.F),
    let GammaC := componentSeeds Omega D.stage.G T
      (regularitySurface phi D.stage.F) GammaI
      (selectedPoint phi D.stage.selected) C
    let SC := regularComponentCurveStage D.stage.F D.stage.G T
      D.stage.selected GammaI D.stage.nodes x D.stage.u0 D.stage.u1
      pchar errors D.degree flag (residualAgreementFlag D.degree)
      D.stage.G_dvd_surface D.stage.flag_support
      (surfaceMap_agreement_in_flag_of_surface_weights
        D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
        D.stage.surface_total_weight D.degree
        (fun j ↦ (j.factorial : K)⁻¹)
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.stage.x_injective
      (fun gamma hgamma ↦ D.stage.degree_le gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma ↦ D.stage.solution gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma ↦ D.stage.regular gamma
        (Finset.mem_filter.mp hgamma).1)
      (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree errors (Finset.filter_subset _ _) D.stage.no_large_pencil)
      D.stage.characteristic_bound C
    ∀ E : SC.TerminalDescendant,
      E.degree < E.stage.identities.card →
        GammaC.card * (aD - D.degree) ≤
          (errors + 1) * (aD - D.degree) * B.zCost C

/-- One terminal outer proper cut receives the exact factor-affine bound.
The shared component budget and all two-level actual-identity arithmetic are
fully internal; `TerminalLargeZCharge` is the only remaining leaf.
-/
theorem terminal_outer_fiber_bound_of_prime_flag_budget
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (D : S.TerminalDescendant) (i : Iota) (hi : i ∈ D.stage.nodes)
    (B : PrimeFlagBudgetFamily
      (G := D.stage.G)
      (T := agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H := regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree))
    (hallPositive : ∀ C : RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F), 1 ≤ B.allCost C) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
      D.degree *
          ((flagMixed flag agreementDirection6600 agreementDirection6600 *
              degreeIncidence +
            flagMixed flag agreementDirection6600 unitYZFlag *
              unitIncidence) +
            (errors + 1) * gap *
              (flagMixed flag agreementDirection6600 unitZFlag +
                flagMixed flag agreementDirection6600 unitAllFlag)) +
        ((flagMixed flag agreementDirection6600 unitYZFlag *
              degreeIncidence +
            flagMixed flag unitYZFlag unitYZFlag * unitIncidence) +
          (errors + 1) * gap *
            (flagMixed flag unitYZFlag unitZFlag +
              flagMixed flag unitYZFlag unitAllFlag)) := by
  classical
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := agreements - (w - D.degree)
  have hTflag : PolynomialInFlag (residualAgreementFlag D.degree) T := by
    exact surfaceMap_agreement_in_flag_of_surface_weights
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
      (w - D.degree)
    exact h0.trans (by
      simpa only [aD, ResidualStage.agreementFiber,
        ResidualStage.Agrees] using D.agreement_card gamma hGamma)
  have hda : D.degree < aD := by
    have hD := D.degree_le
    norm_num [aD, agreements, n, errors, w] at *
    omega
  have hdegree : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) * (D.degree - k) ≤
        degreeIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ w := D.degree_le
    let total := (w - D.degree) + k
    have htotal : total ≤ w := by
      dsimp only [total]
      omega
    have h := degree_part_bound total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap :
        aD - D.degree = gap := by
      have hres := residual_gap_eq agreements w (w - D.degree)
        (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
      have hback : w - (w - D.degree) = D.degree := by omega
      simpa only [aD, hback, gap] using hres
    have hn : n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have hw : w - total = D.degree - k := by
      dsimp only [total]
      omega
    have ha : agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, hw, ha] at h
    exact h
  have hunit : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) ≤
        unitIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ w := D.degree_le
    let total := (w - D.degree) + k
    have htotal : total ≤ w := by
      dsimp only [total]
      omega
    have h := unit_part_bound total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap :
        aD - D.degree = gap := by
      have hres := residual_gap_eq agreements w (w - D.degree)
        (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
      have hback : w - (w - D.degree) = D.degree := by omega
      simpa only [aD, hback, gap] using hres
    have hn : n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have ha : agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, ha] at h
    exact h
  have hbound := proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all
    hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
    x D.stage.u0 D.stage.u1 pchar errors D.degree aD
    degreeIncidence unitIncidence flag (residualAgreementFlag D.degree)
    D.stage.G_dvd_surface D.stage.flag_support hTflag
    D.stage.surface_s_weight D.stage.surface_ys_weight
    D.stage.surface_total_weight D.stage.x_injective
    (fun gamma hgamma ↦ D.stage.degree_le gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.solution gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.regular gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.on_component gamma (hsub hgamma))
    hTpoint hinnerAgreement
    (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
      D.degree errors hsub D.stage.no_large_pencil)
    D.stage.characteristic_bound hda B (by
      simpa only [T] using hallPositive)
    hdegree hunit
  have hgapEq : aD - D.degree = gap := by
    have hres := residual_gap_eq agreements w (w - D.degree)
      (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
    have hback : w - (w - D.degree) = D.degree := by
      have := D.degree_le
      omega
    simpa only [aD, hback, gap] using hres
  rw [hgapEq] at hbound
  rw [flagMixed_residualAgreement_direction,
    flagMixed_residualAgreement_unit,
    flagMixed_residualAgreement_z,
    flagMixed_residualAgreement_all] at hbound
  dsimp only [GammaI] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

/-- Complete factorwise regular count, conditional only on producing one
shared adaptive budget whose all-coordinate cost is positive at every
terminal outer cut.
-/
theorem recursive_scaled_factor_6600_of_prime_flag_budgets
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbudget : ∀ (D : S.TerminalDescendant) (i : Iota),
      i ∈ D.stage.nodes →
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      ∃ B : PrimeFlagBudgetFamily
        (G := D.stage.G)
        (T := agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (H := regularitySurface phi D.stage.F)
        flag (residualAgreementFlag D.degree),
        ∀ C : RegularComponent Omega D.stage.G
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (regularitySurface phi D.stage.F), 1 ≤ B.allCost C) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger flag := by
  apply recursive_scaled_factor_6600 hphi S flag hnodes hagreement
  intro D i hi hproper
  obtain ⟨B, hallPositive⟩ := hbudget D i hi hproper
  exact terminal_outer_fiber_bound_of_prime_flag_budget
    hphi S hnodes hagreement D i hi B hallPositive

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research.terminal_outer_fiber_bound_of_prime_flag_budget
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research.recursive_scaled_factor_6600_of_prime_flag_budgets
