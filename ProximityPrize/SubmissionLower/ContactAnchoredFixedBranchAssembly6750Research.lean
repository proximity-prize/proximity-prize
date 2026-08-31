import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeVanish6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research
import ProximityPrize.SubmissionLower.ContactCommonCoreBranchPartition6750Research

 

















namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredFixedBranchAssembly6750Research

open scoped Classical BigOperators
open ContactTranslation
open ContactFlagInterpolation6641Research
open ContactFlagKernelZeroExtension6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactFlagKernelDerivativeVanish6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactFlagBezout6543Research
open ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorFlag6600Research
open ContactGCDCumulativeFlagsResearch
open ContactSimultaneousOccurrenceLedger6750Research
open ContactAnchoredTwoSingularUnion6750Research
open ContactAnchoredParentCapAdapters6750Research
open ContactFlagNestedSpanSpecialization6750Research
open ContactCommonCoreBranchPartition6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

universe v w x

variable {K : Type} [Field K]
variable {I : Type v} [Fintype I]
variable {ι : Type w}

local instance : DecidableEq K := Classical.decEq K

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

 
abbrev selectedHull
    (Lmax : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11407258 131071 (cap i) 18 63 nodes u0 u1)))
    (g : CoefficientIndex 11407258 131071 Lmax 18 → K) :
    Submodule K (CoefficientIndex 11407258 131071 Lmax 18 → K) :=
  adjoinFixedArray g
    (embeddedSelectedKernelFamilySum 11407258 131071 Lmax 18 63
      nodes u0 u1 cap hcap Selected)

 
def selectedHullCore
    (Lmax : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11407258 131071 (cap i) 18 63 nodes u0 u1)))
    (g : CoefficientIndex 11407258 131071 Lmax 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K
      (selectedHull Lmax nodes u0 u1 cap hcap Selected g)) : Poly4 K :=
  commonGCDAtMax (selectedHull Lmax nodes u0 u1 cap hcap Selected g) b

 

 





structure SelectedCellCertificate
    (Lmax : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11407258 131071 (cap i) 18 63 nodes u0 u1)))
    (H : Poly4 K) where
  index : ι
  theta : Selected index
  totalCap : Nat
  ysCap : Nat
  reconstructed_ne_zero :
    reconstruct K 11407258 131071 (cap index) 18 theta.1.1 ≠ 0
  reconstructed_mem_fiveCap :
    reconstruct K 11407258 131071 (cap index) 18 theta.1.1 ∈
      nestedFiveCapCoefficientBox K 11407258 131071 totalCap ysCap 18
  coreContact : Nat
  coreTotal : Nat
  coreYS : Nat
  coreS : Nat
  coreContact_eq :
    MvPolynomial.weightedTotalDegree (contactWeights 131071) H = coreContact
  coreTotal_eq :
    MvPolynomial.weightedTotalDegree residualTotalWeights H = coreTotal
  coreYS_eq :
    MvPolynomial.weightedTotalDegree residualYSWeights H = coreYS
  coreS_eq :
    MvPolynomial.weightedTotalDegree residualSWeights H = coreS

 






structure OriginalSourceCertificate
    (Lmax : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (g : CoefficientIndex 11407258 131071 Lmax 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K) where
  totalCap : Nat
  ysCap : Nat
  sCap : Nat
  source_ne_zero : reconstruct K 11407258 131071 Lmax 18 g ≠ 0
  source_mem_fiveCap : reconstruct K 11407258 131071 Lmax 18 g ∈
    nestedFiveCapCoefficientBox K 11407258 131071 totalCap ysCap sCap
  support : K → Finset I
  selected_degree : ∀ gamma ∈ Gamma,
    (selected gamma).natDegree ≤ 131071
  agreement_card : ∀ gamma ∈ Gamma,
    181874 ≤ (support gamma).card
  agreement_values : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i
  source_vanishes : ∀ gamma ∈ Gamma,
    specialization K (selected gamma) gamma
      (reconstruct K 11407258 131071 Lmax 18 g) = 0

 


structure AnchoredStageCertificate
    (H Q : Poly4 K) (selected : K → Polynomial K) (Gamma : Finset K) where
  supportH : ResidualSupportParameters
  supportQ : ResidualSupportParameters
  pH : FlagDegree
  pQ : FlagDegree
  tH : Nat
  yH : Nat
  sH : Nat
  tQ : Nat
  yQ : Nat
  sQ : Nat
  singularH : Nat
  singularQ : Nat
  Hsupport : ResidualSupportData supportH H
  Qsupport : ResidualSupportData supportQ Q
  singularH_bound :
    (anchoredSingularGSeeds H selected Gamma).card ≤ singularH
  singularQ_bound :
    (anchoredSingularQSeeds H Q selected Gamma).card ≤ singularQ
  regularH_bound : ∀ R : RegularIndex H,
    (regularSeeds H selected (anchoredGoodSeeds H Q selected Gamma) R).card ≤
      ContactRouterCellCosts6750Research.cellCostOf
        (regularCumulativeFlag H R) tH yH sH
  regularQ_bound : ∀ R : RegularIndex Q,
    (regularSeeds Q selected (anchoredGoodSeeds H Q selected Gamma) R).card ≤
      ContactRouterCellCosts6750Research.cellCostOf
        (regularCumulativeFlag Q R) tQ yQ sQ
  H_s_le : supportH.s ≤ pH.all
  H_ys_le : supportH.ys ≤ pH.yz + pH.all
  H_total_le : supportH.total ≤ pH.zOnly + pH.yz + pH.all
  Q_s_le : supportQ.s ≤ pQ.all
  Q_ys_le : supportQ.ys ≤ pQ.yz + pQ.all
  Q_total_le : supportQ.total ≤ pQ.zOnly + pQ.yz + pQ.all

def AnchoredStageCertificate.cost
    {H Q : Poly4 K} {selected : K → Polynomial K} {Gamma : Finset K}
    (C : AnchoredStageCertificate H Q selected Gamma) : Nat :=
  C.singularH + C.singularQ +
    (ContactRouterCellCosts6750Research.cellCostOf C.pH C.tH C.yH C.sH +
      ContactRouterCellCosts6750Research.cellCostOf C.pQ C.tQ C.yQ C.sQ) / 2

 

theorem AnchoredStageCertificate.card_le_cost
    {H Q : Poly4 K} {selected : K → Polynomial K} {Gamma : Finset K}
    (C : AnchoredStageCertificate H Q selected Gamma)
    (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hHzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma H = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (H * Q)) = 0) :
    Gamma.card ≤ C.cost := by
  exact anchored_card_le_of_distinct_regular_and_singular_caps_cell
    H Q hH hQ selected Gamma C.Hsupport C.Qsupport
      C.pH C.pQ C.tH C.yH C.sH C.tQ C.yQ C.sQ C.singularH C.singularQ
      hHzero hproductDerivative C.singularH_bound C.singularQ_bound
      C.regularH_bound C.regularQ_bound
      C.H_s_le C.H_ys_le C.H_total_le
      C.Q_s_le C.Q_ys_le C.Q_total_le

 


def StageBoundProvider
    (H D : Poly4 K) (selected : K → Polynomial K) (Gamma : Finset K)
    (DminusHBox : Poly4 K → Prop) (anchoredCap : Nat) : Prop :=
  ∀ Q : Poly4 K, Q ≠ 0 → D = H * Q → DminusHBox Q →
    ∃ C : AnchoredStageCertificate H Q selected
        (commonCoreZeroSeeds H selected Gamma),
      C.cost ≤ anchoredCap

 


def ResidualCountProvider
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    (g : CoefficientIndex D w0 Lmax s → K)
    (H : Poly4 K) (selected : K → Polynomial K) (Gamma : Finset K)
    (sourceTotal sourceYS sourceS residualCap : Nat) : Prop :=
  reconstruct K D w0 Lmax s g ≠ 0 →
  reconstruct K D w0 Lmax s g ∈
    nestedFiveCapCoefficientBox K D w0 sourceTotal sourceYS sourceS →
  g ∈ V →
  (∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma, ∀ v : V,
    ∀ Q : Poly4 K, reconstruct K D w0 Lmax s v.1 = H * Q →
      specialization K (selected gamma) gamma Q = 0) →
    (commonCoreNonzeroSeeds H selected Gamma).card ≤ residualCap

 

 






theorem fixedSeeds_card_le_of_four_production_seams
    [DecidableEq I]
    (Lmax : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker
        (constraintMap K 11407258 131071 (cap i) 18 63 nodes u0 u1)))
    (g : CoefficientIndex 11407258 131071 Lmax 18 → K)
    {β : Type x} [Fintype β] [Nonempty β]
    (b : Module.Basis β K
      (selectedHull Lmax nodes u0 u1 cap hcap Selected g))
    (selected : K → Polynomial K) (Gamma : Finset K)
    (cell : SelectedCellCertificate Lmax nodes u0 u1 cap Selected
      (selectedHullCore Lmax nodes u0 u1 cap hcap Selected g b))
    (original : OriginalSourceCertificate Lmax nodes u0 u1 g selected Gamma)
    (anchoredCap residualCap : Nat)
    (stageBound : StageBoundProvider
      (selectedHullCore Lmax nodes u0 u1 cap hcap Selected g b)
      (reconstruct K 11407258 131071 (cap cell.index) 18
        cell.theta.1.1)
      selected Gamma
      (fun Q ↦ Q ∈ nestedFiveCapCoefficientBox K
        (11407258 - cell.coreContact) 131071
        (cell.totalCap - cell.coreTotal)
        (cell.ysCap - cell.coreYS) (18 - cell.coreS))
      anchoredCap)
    (residualCount : ResidualCountProvider
      (selectedHull Lmax nodes u0 u1 cap hcap Selected g)
      g
      (selectedHullCore Lmax nodes u0 u1 cap hcap Selected g b)
      selected Gamma original.totalCap original.ysCap original.sCap
      residualCap) :
    Gamma.card ≤ anchoredCap + residualCap := by
  let V := selectedHull Lmax nodes u0 u1 cap hcap Selected g
  let H := selectedHullCore Lmax nodes u0 u1 cap hcap Selected g b
  let D := reconstruct K 11407258 131071 (cap cell.index) 18
    cell.theta.1.1
  have hHne : H ≠ 0 := by
    exact commonGCDAtMax_ne_zero V b
  have hthetaExtended :
      zeroExtendConstraintKernelToArray (K := K) (D := 11407258)
          (w := 131071) (s := 18) (m := 63) (hcap cell.index)
          nodes u0 u1 cell.theta.1 ∈
        embeddedSelectedKernelFamilySum 11407258 131071 Lmax 18 63
          nodes u0 u1 cap hcap Selected :=
    selected_zeroExtend_mem_familySum 11407258 131071 Lmax 18 63
      nodes u0 u1 cap hcap Selected cell.index cell.theta
  have hthetaHull :
      zeroExtendConstraintKernelToArray (K := K) (D := 11407258)
          (w := 131071) (s := 18) (m := 63) (hcap cell.index)
          nodes u0 u1 cell.theta.1 ∈ V :=
    mem_adjoinFixedArray_of_mem g _ hthetaExtended
  let vtheta : V := ⟨_, hthetaHull⟩
  have hHdvdD : H ∣ D := by
    change commonGCDAtMax V b ∣ D
    have hdiv := commonGCDAtMax_dvd V b vtheta
    simpa only [V, D, vtheta,
      zeroExtendConstraintKernelToArray_apply,
      reconstruct_zeroExtendTotal] using hdiv
  obtain ⟨Q, hDQ⟩ := hHdvdD
  have hQne : Q ≠ 0 := by
    intro hQ
    have hDzero : D = 0 := by
      rw [hDQ, hQ, mul_zero]
    apply cell.reconstructed_ne_zero
    simpa only [D] using hDzero
  have hQbox : Q ∈ nestedFiveCapCoefficientBox K
      (11407258 - cell.coreContact) 131071
      (cell.totalCap - cell.coreTotal)
      (cell.ysCap - cell.coreYS) (18 - cell.coreS) := by
    apply quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
      hHne hQne hDQ.symm cell.reconstructed_mem_fiveCap
      cell.coreContact_eq cell.coreTotal_eq cell.coreYS_eq cell.coreS_eq
  obtain ⟨stage, hstageCost⟩ :=
    stageBound Q hQne hDQ hQbox
  have hHzero : ∀ gamma ∈ commonCoreZeroSeeds H selected Gamma,
      specialization K (selected gamma) gamma H = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hproductDerivative :
      ∀ gamma ∈ commonCoreZeroSeeds H selected Gamma,
        specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4) (H * Q)) = 0 := by
    intro gamma hgamma
    have hgammaGamma : gamma ∈ Gamma :=
      commonCoreZeroSeeds_subset H selected Gamma hgamma
    rw [← hDQ]
    exact specialization_pderiv_R_eq_zero_of_mem_m61_kernel
      (cap cell.index) nodes u0 u1 cell.theta.1.1 cell.theta.1.2
      (selected gamma) gamma (original.support gamma)
      (original.selected_degree gamma hgammaGamma)
      (original.agreement_card gamma hgammaGamma)
      (original.agreement_values gamma hgammaGamma)
  have hanchored :
      (commonCoreZeroSeeds H selected Gamma).card ≤ anchoredCap :=
    (stage.card_le_cost hHne hQne hHzero hproductDerivative).trans hstageCost
  have huniversalCancellation :
      ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma, ∀ v : V,
        ∀ T : Poly4 K,
          reconstruct K 11407258 131071 Lmax 18 v.1 = H * T →
          specialization K (selected gamma) gamma T = 0 := by
    intro gamma hgamma v T hfactor
    have hgammaGamma : gamma ∈ Gamma :=
      commonCoreNonzeroSeeds_subset H selected Gamma hgamma
    apply quotient_specialization_eq_zero_of_mul_eq
      (selected gamma) gamma
      (reconstruct K 11407258 131071 Lmax 18 v.1) H T hfactor
    · exact specialization_eq_zero_of_mem_m61_adjoinedSelectedFamily
        Lmax nodes u0 u1 cap hcap Selected g
        (selected gamma) gamma (original.support gamma)
        (original.selected_degree gamma hgammaGamma)
        (original.agreement_card gamma hgammaGamma)
        (original.agreement_values gamma hgammaGamma)
        (original.source_vanishes gamma hgammaGamma) v
    · exact (Finset.mem_filter.mp hgamma).2
  have hresidual :
      (commonCoreNonzeroSeeds H selected Gamma).card ≤ residualCap :=
    residualCount original.source_ne_zero original.source_mem_fiveCap
      (fixed_mem_adjoinFixedArray g
        (embeddedSelectedKernelFamilySum 11407258 131071 Lmax 18 63
          nodes u0 u1 cap hcap Selected))
      huniversalCancellation
  exact card_le_anchoredCap_add_residualCap H selected Gamma
    anchoredCap residualCap hanchored hresidual

end

end ContactAnchoredFixedBranchAssembly6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredFixedBranchAssembly6750Research.AnchoredStageCertificate.card_le_cost
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredFixedBranchAssembly6750Research.fixedSeeds_card_le_of_four_production_seams
