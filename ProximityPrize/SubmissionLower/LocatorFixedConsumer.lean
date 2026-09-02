import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorFixedHybrid
import ProximityPrize.SubmissionLower.LocatorFactorReplacement
import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorFixedConsumer
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN275 LocatorFactorAggregate
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
  ⟨20,92,3319,by decide,by decide,by decide,by decide⟩
theorem singularProfile_eq:
    LocatorFixed.singularProfile 12347372 3319 20=LocatorArithmetic.fixedSingular:=rfl
theorem regular_sum_count
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 12347372 131071 3319 20)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565)
    (hown:∀ R,LocatorHybridCost.OwnBound (regularSeeds H selected Gamma R).card
      (regularCumulativeFlag H R))
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.BadCost 3319 LocatorHybridCost.ordinaryCostOf
      268943401356142843 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hqRate:∀ R,LocatorFactorReplacement.BadCost 3319 LocatorHybridCost.ordinaryCostOf
      268943401356142843 (regularCumulativeFlag H R) →
      3319 * qCost R ≤
        268943401356142843 * total (regularCumulativeFlag H R)) :
    (∑ R:RegularIndex H, (regularSeeds H selected Gamma R).card) ≤
      268943401356142843:=by
  have hb:=regularCumulativeFlag_budgets H hH hSupport
  have ht:(∑ R:RegularIndex H,total (regularCumulativeFlag H R)) ≤ 3319:=by
    simpa only [wholeSupport,total] using hb.2.2
  have hstage (R:RegularIndex H) :
      (regularSeeds H selected Gamma R).card ≤
        LocatorHybridCost.ordinaryCostOf (regularCumulativeFlag H R) :=
    LocatorHybridCost.ownBound_le_ordinaryCostOf (hown R)
  exact LocatorFactorReplacement.aggregate_of_rate_replacements_cost
    (regularCumulativeFlag H)
    (fun R=> (regularSeeds H selected Gamma R).card) qCost
    3319 LocatorHybridCost.ordinaryCostOf 268943401356142843 (by decide)
    ht hstage hqCost hqRate
theorem fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 12347372 131071 3319 20)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565)
    (hown:∀ R,LocatorHybridCost.OwnBound (regularSeeds H selected Gamma R).card
      (regularCumulativeFlag H R))
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.BadCost 3319 LocatorHybridCost.ordinaryCostOf
      268943401356142843 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hqRate:∀ R,LocatorFactorReplacement.BadCost 3319 LocatorHybridCost.ordinaryCostOf
      268943401356142843 (regularCumulativeFlag H R) →
      3319 * qCost R ≤
        268943401356142843 * total (regularCumulativeFlag H R)) :
    Gamma.card ≤ 268943401356142843 + LocatorArithmetic.fixedSingular.countCap:=by
  have hg:=LocatorFixed.singular_gates 12347372 3319 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 12347372 3319 20) H hH hbox
    hg.s_pos hg.s_small hg.w_pos hg.kD hg.algebraic_pos hg.algebraic_small
    selected Gamma hsolution
  have hreg:=regular_sum_count H hH hbox hSupport selected Gamma u0 u1
    hdegree hagreement hno hown qCost hqCost hqRate
  have hsing:=RCN292.TightParameters.singularSeeds_count_le_countCap
    (LocatorFixed.singularProfile 12347372 3319 20) H hH hbox
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
