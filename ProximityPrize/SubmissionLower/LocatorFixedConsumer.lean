import ProximityPrize.SubmissionLower.LocatorFixed
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
  ⟨16,75,2319,by decide,by decide,by decide,by decide⟩
theorem singularProfile_eq:
    LocatorFixed.singularProfile 10358952 2319 16=LocatorArithmetic.fixedSingular:=rfl
theorem regular_sum_count
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 10358952 131071 2319 16)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181736 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.Bad 2319 131072 131073
      271797226259522258 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hcell:∀ R,LocatorFactorReplacement.Bad 2319 131072 131073
      271797226259522258 (regularCumulativeFlag H R) →
      LocatorFactorReplacement.cellCost 2319 75 16 131072 131073
        (regularCumulativeFlag H R) (qCost R) ≤ 271797226259522258) :
    (∑ R:RegularIndex H, (regularSeeds H selected Gamma R).card) ≤
      271797226259522258:=by
  have hb:=regularCumulativeFlag_budgets H hH hSupport
  have hs:(∑ R:RegularIndex H, (regularCumulativeFlag H R).all) ≤ 16:=by
    simpa only [wholeSupport] using hb.1
  have hy:(∑ R:RegularIndex H,middle (regularCumulativeFlag H R)) ≤ 75:=by
    simpa only [wholeSupport,middle] using hb.2.1
  have ht:(∑ R:RegularIndex H,total (regularCumulativeFlag H R)) ≤ 2319:=by
    simpa only [wholeSupport,total] using hb.2.2
  have hstage (R:RegularIndex H) :
      (regularSeeds H selected Gamma R).card ≤
        paddedCost 131072 131073 (regularCumulativeFlag H R) :=
    LocatorFixed.regular_factor_count 10358952 wholeSupport
      (by decide) (by decide) (by decide) (by decide) (by decide)
      H hH hbox hSupport selected Gamma u0 u1 hdegree hagreement hno R
  have hzero (R:RegularIndex H) (hz:(regularCumulativeFlag H R).all=0) :
      (regularSeeds H selected Gamma R).card=0:=by
    have hpos:=regularCumulativeFlag_positive H R
    omega
  exact LocatorFactorReplacement.aggregate_of_bad_cells (regularCumulativeFlag H)
    (fun R=> (regularSeeds H selected Gamma R).card) qCost
    2319 75 16 131072 131073 271797226259522258 (by decide)
    hs hy ht hstage hzero hqCost hcell
theorem fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 10358952 131071 2319 16)
    (hSupport:ResidualSupportData wholeSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181736 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80408)
    (qCost:RegularIndex H → ℕ)
    (hqCost:∀ R,LocatorFactorReplacement.Bad 2319 131072 131073
      271797226259522258 (regularCumulativeFlag H R) →
      (regularSeeds H selected Gamma R).card ≤ qCost R)
    (hcell:∀ R,LocatorFactorReplacement.Bad 2319 131072 131073
      271797226259522258 (regularCumulativeFlag H R) →
      LocatorFactorReplacement.cellCost 2319 75 16 131072 131073
        (regularCumulativeFlag H R) (qCost R) ≤ 271797226259522258) :
    Gamma.card ≤ 271797226259522258 + LocatorArithmetic.fixedSingular.countCap:=by
  have hg:=LocatorFixed.singular_gates 10358952 2319 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 10358952 2319 16) H hH hbox
    hg.s_pos hg.s_small hg.w_pos hg.kD hg.algebraic_pos hg.algebraic_small
    selected Gamma hsolution
  have hreg:=regular_sum_count H hH hbox hSupport selected Gamma u0 u1
    hdegree hagreement hno qCost hqCost hcell
  have hsing:=RCN292.TightParameters.singularSeeds_count_le_countCap
    (LocatorFixed.singularProfile 10358952 2319 16) H hH hbox
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
