import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6750Research
import ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research
import ProximityPrize.SubmissionLower.ContactMovingProtocol6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactSelectedCount6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactTranslation ContactPrimeSeedIncidence
open ContactRecursiveGCDResearch ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagNestedKernelCommonGCD6750Research
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

 


structure SelectedInterpolants6750 (u0 u1 : I → K) where
  QA : GlobalPoly
  QB : GlobalPoly
  QC : GlobalPoly
  QA_ne_zero : QA ≠ 0
  QB_ne_zero : QB ≠ 0
  QC_ne_zero : QC ≠ 0
  QA_mem : QA ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
    profileA.weightedCap w profileA.totalCap profileA.slopeCap
  QB_mem : QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
    profileB.weightedCap w profileB.totalCap profileB.slopeCap
  QC_mem : QC ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
    profileC.weightedCap w profileC.totalCap profileC.slopeCap
  gcd12_mem : gcd12 QA QB ∈
    ContactFlagInterpolation6641Research.globalCoefficientBox K
      profileA.weightedCap w 1706 profileA.slopeCap
   


  oldCore_dvd_B : ∀ v :
      ContactKernelCommonGCD6750Research.E80270.BKernel u0 u1,
    gcd123 QA QB QC ∣
      ContactFlagInterpolation6641Research.reconstruct K
        17096156 131071 1708 29 v.1
  universal_cover : ∀ gamma P (support : Finset I),
    P.natDegree ≤ w → agreements ≤ support.card →
    (∀ i ∈ support,
      P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
    RecursiveSpecializationBranch P gamma QA QB QC

 
def SelectedInterpolantsProvider6750 : Prop :=
  ∀ u0 u1 : I → K, Nonempty (SelectedInterpolants6750 u0 u1)

def oldCommonCore {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : GlobalPoly :=
  gcd123 S.QA S.QB S.QC

def oldCoreTotal {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Nat :=
  MvPolynomial.weightedTotalDegree residualTotalWeights (oldCommonCore S)

def oldCoreYS {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Nat :=
  MvPolynomial.weightedTotalDegree residualYSWeights (oldCommonCore S)

def oldCoreS {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Nat :=
  MvPolynomial.weightedTotalDegree residualSWeights (oldCommonCore S)

 



structure RoutedFixedCellBounds
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) where
  highT : Nat
  highY : Nat
  highR : Nat
  validity : ResidualCellValidity6750
    (oldCoreTotal S - 1) (oldCoreYS S - 1) (oldCoreS S - 1) (oldCoreS S)
  upstreamCost_le : upstreamCellCost
    (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) ≤
      ContactRouterUniformCaps6750Research.upstreamCap
  hardFixed : HardCell highT highY highR →
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      ContactRouterUniformCaps6750Research.hardAnchoredCap +
        ContactRouterUniformCaps6750Research.hardThirdCap
  shellTotal : FirstDerivativeShell highT highY highR →
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
        (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card +
        (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      ContactRouterUniformCaps6750Research.pairedEasyTotalCap
  easyTotal : ¬ OrdinaryHardCell highT highY highR →
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
        (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card +
        (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      ContactRouterUniformCaps6750Research.easyDiagonalCap

 



def FixedRouterProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    Nonempty (RoutedFixedCellBounds S selected Gamma)

theorem recursive_cover_of_interpolants
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) :
    ∀ gamma ∈ Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC := by
  intro gamma hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (IRSProfile.domain i) =
      u0 i + gamma * u1 i)
  apply S.universal_cover gamma (selected gamma) support
  · exact hdegree gamma hgamma
  · exact hagreement gamma hgamma
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

 

theorem upstream_partition_card_le
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : RoutedFixedCellBounds S selected Gamma)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
        (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card ≤
      upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) := by
  have hcover := recursive_cover_of_interpolants S selected Gamma
    hdegree hagreement
  have hfirst := firstResidualCell_count_lt
    (oldCoreTotal S - 1) (oldCoreYS S - 1) (oldCoreS S - 1) (oldCoreS S)
    R.validity.first S.QA S.QB S.QC S.QA_ne_zero S.QB_ne_zero
    S.QA_mem S.QB_mem
    (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _) (le_refl _)
    selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
  have hsecond := secondResidualCell_count_lt
    (oldCoreTotal S - 1) (oldCoreYS S - 1) (oldCoreS S - 1) (oldCoreS S)
    R.validity.second S.QA S.QB S.QC S.QA_ne_zero S.QC_ne_zero
    S.QC_mem S.gcd12_mem
    (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _) (le_refl _)
    selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
  change
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
        (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card ≤
      residualCost6750 (oldCoreTotal S - 1) (oldCoreYS S - 1)
        (oldCoreS S - 1) (oldCoreS S)
  unfold residualCost6750
  omega

 

theorem selected_card_le_mcaBudget_of_router
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : RoutedFixedCellBounds S selected Gamma)
    (hupstream :
      (firstResidualSeeds selected Gamma S.QA S.QB).card +
          (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card ≤
        upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S)) :
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget := by
  have hpartition := (partition_card selected Gamma S.QA S.QB S.QC).symm
  rcases hard_or_firstDerivativeShell_or_ordinaryEasy
      R.highT R.highY R.highR with hhard | hshell | heasy
  · rw [hpartition]
    have hhardTotal := Nat.add_le_add
      (hupstream.trans R.upstreamCost_le) (R.hardFixed hhard)
    exact hhardTotal.trans (by
      simpa [ContactRouterUniformCaps6750Research.hardTotalCap,
          Nat.add_assoc, ContactMovingProtocol6750Research.mcaBudget,
          ContactMovingSeedless6750Research.mcaBudget]
        using Nat.le_of_lt
          ContactRouterUniformCaps6750Research.hardTotalCap_lt_mcaBudget)
  · rw [hpartition]
    exact (R.shellTotal hshell).trans
      (Nat.le_of_lt
        ContactRouterUniformCaps6750Research.pairedEasyTotalCap_lt_mcaBudget)
  · rw [hpartition]
    exact (R.easyTotal heasy).trans
      (Nat.le_of_lt
        ContactRouterUniformCaps6750Research.easyDiagonalCap_lt_mcaBudget)

 

def SemanticSelectedCount6750 : Prop :=
  ∀ (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget

theorem semantic_selected_card_le_mcaBudget
    (source : SelectedInterpolantsProvider6750)
    (router : FixedRouterProvider6750)
    (u0 u1 : I → K) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget := by
  obtain ⟨S⟩ := source u0 u1
  obtain ⟨R⟩ := router u0 u1 S selected Gamma
    hdegree hagreement hnoPencil
  exact selected_card_le_mcaBudget_of_router S selected Gamma R
    (upstream_partition_card_le S selected Gamma R
      hdegree hagreement hnoPencil)

theorem semanticSelectedCount6750_of_providers
    (source : SelectedInterpolantsProvider6750)
    (router : FixedRouterProvider6750) : SemanticSelectedCount6750 := by
  intro selected Gamma u0 u1 hdegree hagreement hnoPencil
  exact semantic_selected_card_le_mcaBudget source router u0 u1
    selected Gamma hdegree hagreement hnoPencil

theorem original_support_card6750
    (A : K → Finset I) (Gamma : Finset K)
    (hcard : ∀ gamma ∈ Gamma,
      Fintype.card I - ContactMovingProtocol6750Research.errors ≤
        (A gamma).card) :
    ∀ gamma ∈ Gamma, agreements ≤ (A gamma).card := by
  intro gamma hgamma
  have h := hcard gamma hgamma
  simpa [I, IRSProfile.Index, agreements, errors, n,
    ContactMovingProtocol6750Research.errors] using h

theorem agreements_eq_alignment_support :
    agreements = Fintype.card IRSProfile.Index -
      ContactMovingProtocol6750Research.errors := by
  norm_num [agreements, n, errors, ContactMovingProtocol6750Research.errors,
    IRSProfile.Index]

theorem selectedNoLargePencilBound6750_of_semantic
    (hcount : SemanticSelectedCount6750) :
    ContactMovingProtocol6750Research.SelectedNoLargePencilBound6750 := by
  intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
  have hcard : ∀ gamma ∈ seeds,
      agreements ≤ (A gamma).card := by
    intro gamma hgamma
    rw [agreements_eq_alignment_support]
    exact hcardRaw gamma hgamma
  have hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ w := by
    simpa only [w] using hdegreeRaw
  have hagreement : ∀ gamma ∈ seeds, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hgamma
    have hsub : A gamma ⊆ (Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i) := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hvalues gamma hgamma i hi⟩
    exact (hcard gamma hgamma).trans (Finset.card_le_card hsub)
  have hnoPencil : NoLargeSelectedPencil selected seeds w errors := by
    intro P0 P1 hP0 hP1
    have h := hnoRaw P0 P1 (by simpa only [w] using hP0)
      (by simpa only [w] using hP1)
    change (seeds.filter (fun gamma ↦
      selected gamma = P0 + Polynomial.C gamma * P1)).card ≤ 80271
    change (pencilSeeds seeds selected P0 P1).card ≤ 80271 at h
    simpa only [pencilSeeds] using h
  exact hcount selected seeds (U 0) (U 1)
    hdegree hagreement hnoPencil

theorem selectedNoLargePencilBound6750_of_providers
    (source : SelectedInterpolantsProvider6750)
    (router : FixedRouterProvider6750) :
    ContactMovingProtocol6750Research.SelectedNoLargePencilBound6750 :=
  selectedNoLargePencilBound6750_of_semantic
    (semanticSelectedCount6750_of_providers source router)

theorem protocolClaim6750_of_providers
    (source : SelectedInterpolantsProvider6750)
    (router : FixedRouterProvider6750) :
    ProtocolClaim 6751 10274687 33554432 :=
  ContactMovingProtocol6750Research.protocolClaim6750_of_selected_count
    (selectedNoLargePencilBound6750_of_providers source router)

end

end ContactSelectedCount6750Research
end ProximityPrize.SubmissionLower
