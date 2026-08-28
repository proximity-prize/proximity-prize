import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research
import ProximityPrize.SubmissionLower.ContactSingularBranch6600Research
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research

/-!
# Actual global selected-family ledger at score 66

The singular union is already bounded unconditionally.  This module joins it
to the factorwise recursive regular bounds, using the robust rectangular
factor flag.  The sole remaining input is one proved count inequality for
each actual positive-`R` factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research

open scoped Classical BigOperators
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRegularFactorFlag6600Research
open ContactSingularBranch6600Research
open ContactNearPencil6600FactorLedgerResearch
open ContactWeightedRegularFactor6600Research
open ContactIdentityResidualGlobalFlagResearch
open ContactPrimeSeedIncidence

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

def regularSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag6600Research.RegularIndex Q) : Finset K :=
  Gamma.filter (fun gamma ↦ RegularSolution F.1 (selected gamma) gamma)

theorem regularSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag6600Research.RegularIndex Q) :
    regularSeeds Q selected Gamma F ⊆ Gamma :=
  Finset.filter_subset _ _

/-- The score-66 selected solutions are covered by the actual regular factor
families and the already constructed singular union. -/
theorem card_le_regular_sum_add_singular
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0) :
    Gamma.card ≤
      (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        (regularSeeds Q selected Gamma F).card) +
      (singularSeeds Q selected Gamma).card := by
  classical
  let regularUnion := Finset.univ.biUnion (regularSeeds Q selected Gamma)
  have hsub : Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma := by
    intro gamma hgamma
    obtain ⟨F, hF, hreg⟩ | ⟨q, hq, himp⟩ | hexc :=
      solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
        (by norm_num [slopeCap]) characteristic_gates.2.2.2
        (by norm_num [w])
        (by norm_num [ContactParameters6600Research.w,
          ContactParameters6600Research.weightedCap,
          ContactParameters6600Research.multiplicity,
          ContactParameters6600Research.agreements,
          ContactParameters6600Research.n,
          ContactParameters6600Research.errors,
          ContactParameters6600Research.slopeCap])
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
    _ ≤ (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) +
        (singularSeeds Q selected Gamma).card :=
      Nat.add_le_add_right Finset.card_biUnion_le _

/-- The actual regular factor family consumes the sharp Newton-weighted
regular numerator. -/
theorem regularSeeds_scaled_weighted_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        weightedLedger
          (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
          (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
          (MvPolynomial.weightedTotalDegree residualSWeights F.1)) :
    (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card) * gap ^ 2 ≤
        weightedRegularNumerator := by
  have hbudget := positiveRFactors_weightedLedger_budget Q hQ hbox
  have hbudget' :
      (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        weightedLedger
          (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
          (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
          (MvPolynomial.weightedTotalDegree residualSWeights F.1)) ≤
        weightedRegularNumerator := by
    change (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
        (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
        (MvPolynomial.weightedTotalDegree residualSWeights F.1)) ≤
      weightedLedger 528 43 8
    have hb := hbudget
    rw [← Finset.sum_coe_sort] at hb
    exact hb
  calc
    (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card) * gap ^ 2 =
        ∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        weightedLedger
          (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
          (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
          (MvPolynomial.weightedTotalDegree residualSWeights F.1) :=
      Finset.sum_le_sum (fun F _ ↦ hregular F)
    _ ≤ weightedRegularNumerator := hbudget'

/-- Full selected-family count using sharp Newton support aggregation. -/
theorem global_scaled_weighted_bound_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
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
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        weightedLedger
          (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
          (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
          (MvPolynomial.weightedTotalDegree residualSWeights F.1)) :
    Gamma.card * gap ^ 2 ≤ weightedTotalNumerator := by
  have hcover := card_le_regular_sum_add_singular Q hQ hbox selected Gamma
    hsolution
  have hreg := regularSeeds_scaled_weighted_bound Q hQ hbox selected Gamma
    hregular
  have hsing := singularSeeds_scaled_bound Q hQ hbox selected Gamma nodes
    x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  calc
    Gamma.card * gap ^ 2 ≤
        ((∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) +
          (singularSeeds Q selected Gamma).card) * gap ^ 2 :=
      Nat.mul_le_mul_right (gap ^ 2) hcover
    _ = (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) * gap ^ 2 +
        (singularSeeds Q selected Gamma).card * gap ^ 2 := by ring
    _ ≤ weightedRegularNumerator +
        ContactParameters6600Research.retainedSingularContribution :=
      Nat.add_le_add hreg hsing
    _ = weightedTotalNumerator := rfl

/-- Sharp weighted global count is strictly below the alignment budget. -/
theorem global_count_lt_alignment_weighted_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
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
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        weightedLedger
          (MvPolynomial.weightedTotalDegree residualTotalWeights F.1)
          (MvPolynomial.weightedTotalDegree residualYSWeights F.1)
          (MvPolynomial.weightedTotalDegree residualSWeights F.1)) :
    Gamma.card < alignmentBudget := by
  have hscaled := global_scaled_weighted_bound_of_regular_factors Q hQ hbox
    selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement
    hnoPencil hregular
  have hlt : Gamma.card * gap ^ 2 < alignmentBudget * gap ^ 2 :=
    hscaled.trans_lt weighted_strict_budget
  exact Nat.lt_of_mul_lt_mul_right hlt


end

end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research
