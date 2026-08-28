import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularSeeds6630Research
import ProximityPrize.SubmissionLower.ContactSingularBranch6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6641Research

/-!
# Actual global selected-family ledger at score 66.30

The singular union is bounded unconditionally by the tight singular ledger.
This module joins it to the factorwise regular bounds using the cumulative
nested flag. The sole remaining input is one proved count inequality for each
actual positive-`R` factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6630Research

open scoped Classical BigOperators
open ContactParameters6630Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRegularFactorFlag6630Research ContactRegularSeeds6630Research
open ContactSingularBranch6630Research ContactSingularLedger6630Research
open ContactNearPencil6630FactorLedgerResearch
open ContactFlagRegularFactorCaps6641Research
open ContactPrimeSeedIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- The score-66.30 selected solutions are covered by the actual regular
factor families and the already constructed singular union. -/
theorem card_le_regular_sum_add_singular6630
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0) :
    Gamma.card ≤
      (∑ F : RegularIndex Q,
        (regularSeeds6630 Q selected Gamma F).card) +
      (singularSeeds Q selected Gamma).card := by
  classical
  let regularUnion := Finset.univ.biUnion (regularSeeds6630 Q selected Gamma)
  have hsub : Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma := by
    intro gamma hgamma
    obtain ⟨F, hF, hreg⟩ | ⟨q, hq, himp⟩ | hexc :=
      solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
        (by norm_num [slopeCap]) characteristic_gates.2.2.2
        (by norm_num [w])
        (by norm_num [ContactParameters6630Research.w,
          ContactParameters6630Research.weightedCap,
          ContactParameters6630Research.multiplicity,
          ContactParameters6630Research.agreements,
          ContactParameters6630Research.n,
          ContactParameters6630Research.errors,
          ContactParameters6630Research.slopeCap])
        hbox (selected gamma) gamma (hsolution gamma hgamma)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨F, hF⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hgamma, hreg⟩⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨q, hq⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hgamma, himp⟩⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hgamma, hexc⟩
  calc
    Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card :=
      Finset.card_le_card hsub
    _ ≤ regularUnion.card + (singularSeeds Q selected Gamma).card :=
      Finset.card_union_le _ _
    _ ≤ (∑ F : RegularIndex Q,
          (regularSeeds6630 Q selected Gamma F).card) +
        (singularSeeds Q selected Gamma).card :=
      Nat.add_le_add_right Finset.card_biUnion_le _

/-- Cumulative nested factor caps aggregate all actual regular factors into
the sharp score-66.30 regular numerator. -/
theorem regularSeeds_scaled_cumulative_bound6630
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds6630 Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedgerYZ (regularFlag6630 Q F)) :
    (∑ F : RegularIndex Q,
      (regularSeeds6630 Q selected Gamma F).card) * gap ^ 2 ≤
        ContactNearPencil6630ArithmeticResearch.regularNumerator := by
  have hcaps := regularFlag6630_budgets_of_flagBox6641 Q hQ hsharp
  exact sum_factor_counts6630_le
    (fun F : RegularIndex Q ↦
      (regularSeeds6630 Q selected Gamma F).card)
    (regularFlag6630 Q) hregular hcaps.1 hcaps.2.1 hcaps.2.2

theorem tight_singular_contributions_agree6630 :
    ContactSingularLedger6630Research.tightSingularContribution =
      tightSingularContribution6630 := by
  rw [ContactSingularLedger6630Research.exact_values.2.2,
    tight_singular_contribution6630_exact]

/-- Full selected-family scaled count. The cover, cumulative regular
aggregation, and tight singular branch are discharged; only per-factor regular
counts remain as input. -/
theorem global_scaled_bound_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds6630 Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedgerYZ (regularFlag6630 Q F)) :
    Gamma.card * gap ^ 2 ≤ totalNumerator6630 := by
  have hcover := card_le_regular_sum_add_singular6630 Q hQ hbox selected Gamma
    hsolution
  have hreg := regularSeeds_scaled_cumulative_bound6630 Q hQ hbox hsharp selected
    Gamma hregular
  have hsing := singularSeeds_scaled_bound Q hQ hbox selected Gamma nodes
    x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  have hsing' : (singularSeeds Q selected Gamma).card * gap ^ 2 ≤
      tightSingularContribution6630 := by
    rw [← tight_singular_contributions_agree6630]
    exact hsing
  calc
    Gamma.card * gap ^ 2 ≤
        ((∑ F : RegularIndex Q,
          (regularSeeds6630 Q selected Gamma F).card) +
          (singularSeeds Q selected Gamma).card) * gap ^ 2 :=
      Nat.mul_le_mul_right (gap ^ 2) hcover
    _ ≤ totalNumerator6630 :=
      combined_scaled_bound6630 _ _ hreg hsing'

theorem global_count_lt_alignment_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds6630 Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedgerYZ (regularFlag6630 Q F)) :
    Gamma.card < alignmentBudget := by
  have hscaled := global_scaled_bound_of_regular_factors Q hQ hbox hsharp selected
    Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
    hregular
  have hbudget : totalNumerator6630 < alignmentBudget * gap ^ 2 := by
    have hbudget0 := strict_field_budget6630
    rw [show ContactNearPencil6630ArithmeticResearch.gap =
        ContactParameters6630Research.gap by
      norm_num [ContactNearPencil6630ArithmeticResearch.gap,
        ContactNearPencil6630ArithmeticResearch.agreements,
        ContactNearPencil6630ArithmeticResearch.n,
        ContactNearPencil6630ArithmeticResearch.w,
        ContactNearPencil6630ArithmeticResearch.errors,
        ContactParameters6630Research.gap,
        ContactParameters6630Research.agreements,
        ContactParameters6630Research.n,
        ContactParameters6630Research.w,
        ContactParameters6630Research.errors]] at hbudget0
    simpa only [fieldBudget6630, alignmentBudget] using hbudget0
  exact Nat.lt_of_mul_lt_mul_right (hscaled.trans_lt hbudget)

end

end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6630Research
