import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorHybridCostC2
import ProximityPrize.SubmissionLower.LocatorFactorReplacement
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorReplacementGridCore
namespace ProximityPrize.SubmissionLower.LocatorFixedConsumer
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN275 RCN095 LocatorFactorAggregate
open LocatorReplacementGridData
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
def wholeSupport:ResidualSupportParameters:=
  ⟨22,99,3806,by decide,by decide,by decide,by decide⟩
/-- The exact nonlinear charge used by the replacement grid. -/
def wgt (p:FlagDegree):ℕ:=
  LocatorNonlinearCharge.charge p.all (middle p) (total p)
theorem singularProfile_eq:
    LocatorFixed.singularProfile 13433220 3806 22=LocatorArithmetic.fixedSingular:=rfl
/-- The total, middle, floor-total, and certified slope-knapsack charges fit
inside the exact global charge budget. -/
theorem weighted_budget (H:P4) (hH:H ≠ 0)
    (hSupport:ResidualSupportData wholeSupport H) :
    (∑ R:RegularIndex H,wgt (regularCumulativeFlag H R)) ≤ capSum:=by
  have hb:=regularCumulativeFlag_budgets H hH hSupport
  have hall:(∑ R:RegularIndex H,(regularCumulativeFlag H R).all) ≤ slopeCap:=by
    simpa only [wholeSupport] using hb.1
  have hmid:(∑ R:RegularIndex H,middle (regularCumulativeFlag H R)) ≤ ysCap:=by
    simpa only [wholeSupport,middle] using hb.2.1
  have ht:(∑ R:RegularIndex H,total (regularCumulativeFlag H R)) ≤ totalCap:=by
    simpa only [wholeSupport,total] using hb.2.2
  have hcharge := LocatorNonlinearCharge.sum_charge_le
    (Finset.univ : Finset (RegularIndex H))
    (fun R => (regularCumulativeFlag H R).all)
    (fun R => middle (regularCumulativeFlag H R))
    (fun R => total (regularCumulativeFlag H R)) hall hmid ht
  simpa only [wgt] using hcharge
theorem regular_sum_count
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 13433220 131071 3806 22)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181530 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80614)
    (hown:∀ R,LocatorHybridCostC2.OwnBoundC2 (regularSeeds H selected Gamma R).card
      (regularCumulativeFlag H R))
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.BadCostW capSum
      LocatorHybridCostC2.ordinaryCostOfC2 bound wgt (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hqRate:∀ R,LocatorFactorReplacement.BadCostW capSum
      LocatorHybridCostC2.ordinaryCostOfC2 bound wgt (regularCumulativeFlag H R) →
      capSum * qCost R ≤ bound * wgt (regularCumulativeFlag H R)) :
    (∑ R:RegularIndex H, (regularSeeds H selected Gamma R).card) ≤ bound:=by
  have hw:=weighted_budget H hH hSupport
  have hstage (R:RegularIndex H) :
      (regularSeeds H selected Gamma R).card ≤
        LocatorHybridCostC2.ordinaryCostOfC2 (regularCumulativeFlag H R) :=
    LocatorHybridCostC2.ownBound_le_ordinaryCostOfC2 (hown R)
  exact LocatorFactorReplacement.aggregate_of_rate_replacements_weighted
    (regularCumulativeFlag H)
    (fun R=> (regularSeeds H selected Gamma R).card) qCost
    capSum LocatorHybridCostC2.ordinaryCostOfC2 wgt bound (by decide)
    hw hstage hqCost hqRate
theorem fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 13433220 131071 3806 22)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181530 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80614)
    (hown:∀ R,LocatorHybridCostC2.OwnBoundC2 (regularSeeds H selected Gamma R).card
      (regularCumulativeFlag H R))
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.BadCostW capSum
      LocatorHybridCostC2.ordinaryCostOfC2 bound wgt (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hqRate:∀ R,LocatorFactorReplacement.BadCostW capSum
      LocatorHybridCostC2.ordinaryCostOfC2 bound wgt (regularCumulativeFlag H R) →
      capSum * qCost R ≤ bound * wgt (regularCumulativeFlag H R)) :
    Gamma.card ≤ bound + LocatorArithmetic.fixedSingular.countCap:=by
  have hg:=LocatorFixed.singular_gates 13433220 3806 22
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 13433220 3806 22) H hH hbox
    hg.s_pos hg.s_small hg.w_pos hg.kD hg.algebraic_pos hg.algebraic_small
    selected Gamma hsolution
  have hreg:=regular_sum_count H hH hbox hSupport selected Gamma u0 u1
    hdegree hagreement hno hown qCost hqCost hqRate
  have hsing:=RCN292.TightParameters.singularSeeds_count_le_countCap
    (LocatorFixed.singularProfile 13433220 3806 22) H hH hbox
    hg.s_pos hg.s_small hg.w_pos hg.w_small hg.kD hg.algebraic_pos
    hg.implicit_small hg.algebraic_small hg.mixed_small hg.wa hg.an
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18)) =262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [LocatorFixed.singularProfile,RCN318.TightParameters.errors,
          Nat.reduceSub] using hno)
  have htotal:=hcover.trans (Nat.add_le_add hreg hsing)
  simpa only [singularProfile_eq] using htotal
end
end ProximityPrize.SubmissionLower.LocatorFixedConsumer
