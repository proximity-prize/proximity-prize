import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedCount6750Research
import ProximityPrize.SubmissionLower.ContactHighTFixedSeedRepair6750Research

 














namespace ProximityPrize.SubmissionLower
namespace ContactSelectedCountHighTRepair6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactFactorCaps
open ContactPrimeSeedIncidence
open ContactStackedSeedPartition6670Research
open ContactIdentityResidualGlobalFlagResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactHighTDerivativeRouter6750Research
open ContactHighTFirstSurvivalRepairArithmetic6750Research
open ContactHighTFixedSeedRepair6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 
def oldGHighDerivativeOrder {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Nat :=
  highTDerivativeOrder (oldCoreTotal S) (oldCoreYS S) (oldCoreS S)

 


theorem oldCommonCore_ys_le_total {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : oldCoreYS S ≤ oldCoreTotal S := by
  apply (weightedTotalDegree_le_iff residualYSWeights
    (oldCommonCore S) (oldCoreTotal S)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h ⊢
  simp [oldCoreTotal, residualYSWeights, residualTotalWeights] at h ⊢
  omega

 



structure HighTOldGEquationCertificate
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) where
  validity : ResidualCellValidity6750
    (oldCoreTotal S - 1) (oldCoreYS S - 1)
      (oldCoreS S - 1) (oldCoreS S)
  terminal_count :
    (terminalDerivativeSeeds (oldCommonCore S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC)
        (oldGHighDerivativeOrder S)).card ≤
        iteratedDerivativeReplacementCost (oldGHighDerivativeOrder S)
          (oldCoreTotal S) (oldCoreYS S) (oldCoreS S)
  quotient_count : FixedLowQuotientEquationCountProvider S selected
    (fixedSeeds selected Gamma S.QA S.QB S.QC) (oldGHighDerivativeOrder S)

 


def HighTOldGEquationProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    1660 ≤ oldCoreTotal S →
    2 ≤ oldCoreS S →
    oldCoreS S < oldCoreYS S →
    Nonempty (HighTOldGEquationCertificate S selected Gamma)

 

def LegacyOldGCell {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Prop :=
  oldCoreTotal S < 1660 ∨ oldCoreS S < 2 ∨ oldCoreYS S ≤ oldCoreS S

 


def LegacyFixedRouterProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    LegacyOldGCell S →
    Nonempty (RoutedFixedCellBounds S selected Gamma)

 




def LegacyOldGCountProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    LegacyOldGCell S →
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget

 
theorem legacyFixedRouterProvider_of_fixedRouter
    (router : FixedRouterProvider6750) : LegacyFixedRouterProvider6750 := by
  intro u0 u1 S selected Gamma hdegree hagreement hnoPencil _
  exact router u0 u1 S selected Gamma hdegree hagreement hnoPencil

 

theorem legacyOldGCountProvider_of_fixedRouter
    (router : LegacyFixedRouterProvider6750) :
    LegacyOldGCountProvider6750 := by
  intro u0 u1 S selected Gamma hdegree hagreement hnoPencil hlegacy
  obtain ⟨R⟩ := router u0 u1 S selected Gamma
    hdegree hagreement hnoPencil hlegacy
  exact selected_card_le_mcaBudget_of_router S selected Gamma R
    (upstream_partition_card_le S selected Gamma R
      hdegree hagreement hnoPencil)

 


theorem upstream_partition_card_le_of_source_caps
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (validity : ResidualCellValidity6750
      (oldCoreTotal S - 1) (oldCoreYS S - 1)
        (oldCoreS S - 1) (oldCoreS S)) :
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
        (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card ≤
      upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) := by
  have hcover := recursive_cover_of_interpolants S selected Gamma
    hdegree hagreement
  have hfirst := firstResidualCell_count_lt
    (oldCoreTotal S - 1) (oldCoreYS S - 1) (oldCoreS S - 1) (oldCoreS S)
    validity.first S.QA S.QB S.QC S.QA_ne_zero S.QB_ne_zero
    S.QA_mem S.QB_mem
    (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _) (le_refl _)
    selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
  have hsecond := secondResidualCell_count_lt
    (oldCoreTotal S - 1) (oldCoreYS S - 1) (oldCoreS S - 1) (oldCoreS S)
    validity.second S.QA S.QB S.QC S.QA_ne_zero S.QC_ne_zero
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

 
theorem selected_card_le_mcaBudget_of_highT_equations
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hhigh : 1660 ≤ oldCoreTotal S)
    (hr2 : 2 ≤ oldCoreS S)
    (hry : oldCoreS S < oldCoreYS S)
    (C : HighTOldGEquationCertificate S selected Gamma) :
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget := by
  have hyt : oldCoreYS S ≤ oldCoreTotal S := by
    exact oldCommonCore_ys_le_total S
  let tf : Fin 1667 := ⟨oldCoreTotal S,
    Nat.lt_succ_iff.mpr (oldCommonCore_total_le S)⟩
  let yf : Fin 66 := ⟨oldCoreYS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_ys_le S)⟩
  let rf : Fin 15 := ⟨oldCoreS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_slope_le S)⟩
  have hroute : HighTDerivativeRoute
      (oldCoreTotal S) (oldCoreYS S) (oldCoreS S)
        (oldGHighDerivativeOrder S) := by
    have hcert := highTDerivativeOrder_certified tf yf rf hr2 hry hyt hhigh
    simpa only [tf, yf, rf, oldGHighDerivativeOrder] using hcert.1
  have hupstream := upstream_partition_card_le_of_source_caps
    S selected Gamma hdegree hagreement hnoPencil C.validity
  have hfixed := fixedSeeds_card_le_of_highT_route
    S selected Gamma hdegree hagreement (oldGHighDerivativeOrder S)
      hhigh hroute
      C.terminal_count C.quotient_count
  have hpartition := (partition_card selected Gamma S.QA S.QB S.QC).symm
  rw [hpartition]
  calc
    (firstResidualSeeds selected Gamma S.QA S.QB).card +
          (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card +
        (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        (iteratedDerivativeReplacementCost (oldGHighDerivativeOrder S)
            (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
          smallProfileBEquationCap) := Nat.add_le_add hupstream hfixed
    _ = iteratedDerivativeTotalCost (oldGHighDerivativeOrder S)
          (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        smallProfileBEquationCap := by
          unfold iteratedDerivativeTotalCost
          omega
    _ ≤ 270096665443142692 + smallProfileBEquationCap :=
      Nat.add_le_add_right hroute.2.2 _
    _ = repairedHighTCap := rfl
    _ ≤ ContactMovingProtocol6750Research.mcaBudget := by
      exact Nat.le_of_lt repairedHighTCap_lt_mcaBudget

 

theorem selected_card_le_mcaBudget_of_highT_split
    (high : HighTOldGEquationProvider6750)
    (low : LegacyOldGCountProvider6750)
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget := by
  by_cases hhigh : 1660 ≤ oldCoreTotal S
  · by_cases hr2 : 2 ≤ oldCoreS S
    · by_cases hry : oldCoreS S < oldCoreYS S
      · obtain ⟨C⟩ := high u0 u1 S selected Gamma
          hdegree hagreement hnoPencil hhigh hr2 hry
        exact selected_card_le_mcaBudget_of_highT_equations
          S selected Gamma hdegree hagreement hnoPencil hhigh hr2 hry C
      · exact low u0 u1 S selected Gamma hdegree hagreement hnoPencil
          (Or.inr (Or.inr (by omega)))
    · exact low u0 u1 S selected Gamma hdegree hagreement hnoPencil
        (Or.inr (Or.inl (by omega)))
  · exact low u0 u1 S selected Gamma hdegree hagreement hnoPencil
      (Or.inl (by omega))

 
theorem selected_card_le_mcaBudget_of_highT_split_router
    (high : HighTOldGEquationProvider6750)
    (low : LegacyFixedRouterProvider6750)
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card ≤ ContactMovingProtocol6750Research.mcaBudget :=
  selected_card_le_mcaBudget_of_highT_split high
    (legacyOldGCountProvider_of_fixedRouter low) S selected Gamma
      hdegree hagreement hnoPencil

 
theorem semanticSelectedCount6750_of_highT_split
    (source : SelectedInterpolantsProvider6750)
    (high : HighTOldGEquationProvider6750)
    (low : LegacyOldGCountProvider6750) : SemanticSelectedCount6750 := by
  intro selected Gamma u0 u1 hdegree hagreement hnoPencil
  obtain ⟨S⟩ := source u0 u1
  exact selected_card_le_mcaBudget_of_highT_split high low S
    selected Gamma hdegree hagreement hnoPencil

 
theorem semanticSelectedCount6750_of_highT_split_router
    (source : SelectedInterpolantsProvider6750)
    (high : HighTOldGEquationProvider6750)
    (low : LegacyFixedRouterProvider6750) : SemanticSelectedCount6750 :=
  semanticSelectedCount6750_of_highT_split source high
    (legacyOldGCountProvider_of_fixedRouter low)

end

end ContactSelectedCountHighTRepair6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSelectedCountHighTRepair6750Research.upstream_partition_card_le_of_source_caps
#print axioms ProximityPrize.SubmissionLower.ContactSelectedCountHighTRepair6750Research.selected_card_le_mcaBudget_of_highT_equations
#print axioms ProximityPrize.SubmissionLower.ContactSelectedCountHighTRepair6750Research.selected_card_le_mcaBudget_of_highT_split
