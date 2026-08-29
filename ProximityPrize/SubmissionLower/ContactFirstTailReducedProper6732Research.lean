import ProximityPrize.SubmissionLower.ContactFirstTailReducedProjection6732Research
import ProximityPrize.SubmissionLower.ContactFirstTailReducedBudget6732Research
import ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research
import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research

/-! The proper first-tail bound with reduced static pole costs. -/

namespace ProximityPrize.SubmissionLower.ContactFirstTailReducedProper6732Research

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch ContactPost6464MinkowskiRecurrenceResearch
open ContactRobustFixedMeet6656Research ContactSharpTaylorFixedMeet6656Research
open ContactMovingAgreementCertificate6719Research ContactMovingPositiveLedger6719Research
open ContactMovingComponentIncidence6719Research ContactFirstTailCertificate6731Research
open ContactFirstTailProjection6731Research ContactReducedTaylorProfileResearch
open ContactMovingReducedPositiveLedger6720Research
open ContactMovingReducedFactorLedger6720Research
open ContactFirstTailReducedCertificate6732Research
open ContactFirstTailReducedProjection6732Research
open ContactFirstTailReducedBudget6732Research

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

theorem proper_firstTail_reduced_seed_bound
    (hphi : Function.Injective phi) (p : Profile) (a b s : ℕ) {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar p.errors flag p.w (support a b s))
    (hnodes : S.nodes.card = p.n)
    (hagreement : ∀ gamma ∈ Gamma, p.agreements ≤ (S.agreementFiber gamma).card)
    (hw : 1 ≤ p.w) (hwa : p.w < p.agreements)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k))
    (hproper : ¬ S.G ∣ surfaceMap phi (numerator K S.F (p.w + 1)))
    (hflagChar : flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
      flag.zOnly + flag.yz + flag.all < pchar)
    (hmixedSharp : (1 + (p.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (p.w + 1)) < pchar)
    (hmixedReduced : (1 + (p.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (p.w + 1)) < pchar)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    Gamma.card * p.gap ≤
      (p.w + 1) * factorDegreeCost p (support a b s) a b s flag +
        factorUnitCost p (support a b s) a b s flag := by
  classical
  let E := AlgebraicClosure (RatFunc Omega)
  letI : IsScalarTower Omega (RatFunc Omega) E := by infer_instance
  letI : CharP E pchar := by infer_instance
  let supp := support a b s
  let T := globalTailCut phi S.F (p.w + 1)
  have hproperT : ¬ S.G ∣ T := by
    intro h
    apply hproper
    exact (globalTailCut_dvd_iff phi hphi S.F (p.w + 1) S.G).mp h
  let Hsupport : ResidualSupportData supp S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag supp (p.w + 1)) T :=
    ContactFirstTailProjection6731Research.firstTail_in_sharp_flag S
  obtain ⟨baseSharp, ⟨PSharp⟩⟩ :=
    exists_firstTail_projection_of_caps S hproperT hflagChar hmixedSharp
  obtain ⟨baseRed, ⟨PRed⟩⟩ :=
    exists_reduced_firstTail_projection_of_caps S hproperT hflagChar hmixedReduced
  obtain ⟨B, hpositive, hz, hyz, hall, hmove⟩ :=
    exists_firstTail_cut_budgets_reduced (E := E) phi S.F S.G T a b s p.w hw
      rfl Hsupport flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      baseSharp PSharp.family baseRed PRed pchar hmix
  have hTpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi S.selected gamma) T = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma p.w
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hbound := proper_cut_seed_bound_of_moving_budgets
    hphi S.F S.G T S.selected Gamma S.nodes x S.u0 S.u1
    pchar p.errors p.w p.agreements p.degreeIncidence p.unitIncidence
    flag (sharpResidualAgreementFlag supp (p.w + 1)) a b s
    S.G_dvd_surface S.flag_support hTflag
    S.surface_s_weight S.surface_ys_weight S.surface_total_weight S.x_injective
    S.degree_le S.solution S.regular S.on_component hTpoint
    (fun gamma hgamma ↦ by
      simpa only [ResidualStage.agreementFiber, ResidualStage.Agrees] using
        hagreement gamma hgamma)
    S.no_large_pencil S.characteristic_bound hwa baseSharp B hpositive
    (flagMixed flag (reducedResidualAgreementFlag supp (p.w + 1)) unitZFlag)
    (flagMixed flag (reducedResidualAgreementFlag supp (p.w + 1)) unitYZFlag)
    (flagMixed flag (reducedResidualAgreementFlag supp (p.w + 1)) unitAllFlag)
    (flagMixed flag (fiberFlag a b s)
      (center a b s + (p.w + 1) • surfaceFlag a b s))
    hz hyz hall hmove
    (by intro k hk; simpa only [hnodes, Profile.gap] using hdegreeGlobal k hk)
    (by intro k hk; simpa only [hnodes, Profile.gap] using hunitGlobal k hk)
  change Gamma.card * p.gap ≤
    p.degreeIncidence *
      (weightedMixed flag (reducedResidualAgreementFlag supp (p.w + 1))
          (normalFlag a b s) +
        flagMixed flag (fiberFlag a b s)
          (centreFlag a b s + (p.w + 1) • surfaceFlag a b s)) +
    p.unitIncidence * weightedMixed flag
      (reducedResidualAgreementFlag supp (p.w + 1)) (centreFlag a b s) +
    (p.errors + 1) * p.gap *
      (flagMixed flag (reducedResidualAgreementFlag supp (p.w + 1)) unitZFlag +
        flagMixed flag (reducedResidualAgreementFlag supp (p.w + 1)) unitYZFlag) at hbound
  rw [← reducedCut_eq_residualFlag] at hbound
  rw [terminal_affine] at hbound
  exact hbound

end

end ProximityPrize.SubmissionLower.ContactFirstTailReducedProper6732Research
