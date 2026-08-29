import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFixedMeetSingular6656Research

/-!
# Tight fixed-meet arithmetic at score 66.56

The fixed singular geometry already proves an unpadded one-`gap` bound.
Historically that result was enlarged to `retainedSingularContribution`
before it met the regular-factor ledger.  This module combines the regular
and tight singular bounds directly at their natural quotient scales.

The arithmetic combiner is profile-generic.  The final theorem merely
instantiates it for the current recursive-GCD meet.
-/

namespace ProximityPrize.SubmissionLower.ContactTightFixedMeet6656Research

open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactRegularFactorFlag6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactSingularBranch6600Research
open ContactSingularLedger6600Research
open ContactTightSingularLedgerResearch
open ContactRobustFixedMeet6656Research
open ContactGlobalSelectedFamilies6656Research
open ContactFixedMeetSingular6656Research

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 35000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Quotient-level regular count cap for an arbitrary fixed profile. -/
def tightRegularCountCap (p : Profile) : ℕ :=
  p.regularNumerator / p.gap ^ 2

/-- The sum of the exact quotient-level regular and tight singular caps. -/
def tightFixedCountCap (p : Profile) (t : TightParameters) : ℕ :=
  tightRegularCountCap p + t.countCap

/-- Generic arithmetic join which does not pad the tight singular ledger to
the historical retained-singular contribution. -/
theorem combined_tight_count_bound
    (p : Profile) (t : TightParameters) (regularCount singularCount : ℕ)
    (hpgap : 0 < p.gap) (htgap : 0 < t.gap)
    (hregular : regularCount * p.gap ^ 2 ≤ p.regularNumerator)
    (hsingular : singularCount * t.gap ≤ t.tightNumerator) :
    regularCount + singularCount ≤ tightFixedCountCap p t := by
  apply Nat.add_le_add
  · exact (Nat.le_div_iff_mul_le (pow_pos hpgap 2)).2 hregular
  · exact t.count_le_countCap singularCount htgap hsingular

/-- Tight fixed-meet cap, inclusive. -/
def meetTightFixedCountCap : ℕ :=
  tightFixedCountCap meetProfile meetTightProfile

/-- The corresponding strict ceiling, convenient for APIs stated with `<`. -/
def meetTightFixedCost : ℕ := meetTightFixedCountCap + 1

theorem meet_tight_regular_count_cap_exact :
    tightRegularCountCap meetProfile = 94991970521155972 := by
  rw [show tightRegularCountCap meetProfile =
      meetProfile.regularNumerator / meetProfile.gap ^ 2 by rfl,
    meet_regular_numerator_exact]
  norm_num [meetProfile, Profile.gap]

theorem meet_tight_singular_count_cap_exact :
    meetTightProfile.countCap = 5019737604113 := by
  norm_num [meetTightProfile, meetProfile, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.aggregateCost, TightParameters.agreement,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap, dot]

theorem meet_tight_fixed_costs_exact :
    meetTightFixedCountCap = 94996990258760085 ∧
      meetTightFixedCost = 94996990258760086 := by
  have hcap : meetTightFixedCountCap = 94996990258760085 := by
    rw [show meetTightFixedCountCap =
        tightRegularCountCap meetProfile + meetTightProfile.countCap by rfl,
      meet_tight_regular_count_cap_exact, meet_tight_singular_count_cap_exact]
  exact ⟨hcap, by rw [meetTightFixedCost, hcap]⟩

theorem meet_tight_fixed_strict_saving_exact :
    meetProfile.fixedCost - meetTightFixedCost = 759922684662857 := by
  rw [meet_fixed_cost_exact, meet_tight_fixed_costs_exact.2]

/-- Fixed-meet selected-family count with the same sole regular-factor input
as the historical theorem, but consuming the already-proved tight singular
ledger directly. -/
theorem meet_global_count_le_tightFixedCountCap_of_regular_factors
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    [CharP K prime6656]
    (hbox : Q ∈ globalCoefficientBox K meetProfile.weightedCap meetProfile.w
      meetProfile.seedTotalCap meetProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = meetProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ meetProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      meetProfile.agreements ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma meetProfile.w
      meetProfile.errors)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * meetProfile.gap ^ 2 ≤
        meetProfile.factorRegularLedger (regularFlag Q F)) :
    Gamma.card ≤ meetTightFixedCountCap := by
  have hcover := meet_card_le_regular_sum_add_singular Q hQ hbox selected
    Gamma hsolution
  have hreg := sum_factor_counts_rectangular_le meetProfile Q hQ
    (by norm_num [meetProfile]) hbox
    (fun F : RegularIndex Q => (regularSeeds Q selected Gamma F).card)
    hregular
  have hsing := meet_singularSeeds_tight_gap_bound Q hQ hbox selected Gamma
    nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  exact hcover.trans (combined_tight_count_bound meetProfile meetTightProfile
    (∑ F : RegularIndex Q, (regularSeeds Q selected Gamma F).card)
    (singularSeeds Q selected Gamma).card
    (by norm_num [meetProfile, Profile.gap])
    (by norm_num [meetTightProfile, meetProfile, TightParameters.gap])
    hreg hsing)

theorem meet_global_count_lt_tightFixedCost_of_regular_factors
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    [CharP K prime6656]
    (hbox : Q ∈ globalCoefficientBox K meetProfile.weightedCap meetProfile.w
      meetProfile.seedTotalCap meetProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = meetProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ meetProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      meetProfile.agreements ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma meetProfile.w
      meetProfile.errors)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * meetProfile.gap ^ 2 ≤
        meetProfile.factorRegularLedger (regularFlag Q F)) :
    Gamma.card < meetTightFixedCost := by
  exact (meet_global_count_le_tightFixedCountCap_of_regular_factors Q hQ hbox
    selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement
    hnoPencil hregular).trans_lt (Nat.lt_succ_self _)

end

end ProximityPrize.SubmissionLower.ContactTightFixedMeet6656Research
