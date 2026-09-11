import ProximityPrize.SubmissionLower.BoundaryTailCounting

namespace ProximityPrize.SubmissionLower.Lower80801.Geometry
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain Counting BoundaryTailSharedDegreeBudget
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

theorem cover_count (Q T : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K 20129073 131071 21378 33)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ g ∈ Gamma, specialization K (selected g) g Q = 0)
    (hTsolution : ∀ g ∈ Gamma, specialization K (selected g) g T = 0) :
    Gamma.card ≤ (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) +
      (∑ F : RegularIndex Q, factorCharge F.1 selected Gamma) +
      (rfreeSeeds Q selected Gamma).card := by
  have hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ 33 := fun F hF =>
    degreeOf_R_le_of_mem_box F 20129073 131071 21378 33
      (directFactor_data Q F hQ 20129073 131071 21378 33 hbox hF).2.2
  have hcover := cover Q T hQ 2130706433 33 (by decide +kernel) hR selected Gamma hQsolution hTsolution
  have hA := Finset.card_biUnion_le (s := (Finset.univ : Finset (RegularIndex Q)))
    (t := fun F => regularPairSeeds Q T selected Gamma F)
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q,
        ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun F _ => Finset.card_biUnion_le)
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F)
    ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma)
  have he : (∑ F : RegularIndex Q, factorCharge F.1 selected Gamma) =
      (∑ F ∈ positiveRFactors Q, ∑ j ∈ Finset.Ico 1 (chainLength F),
        (chainSeeds F j selected Gamma).card) +
      (∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card) := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ => Iff.rfl)
      (f := fun F => factorCharge F selected Gamma)]
    simp only [factorCharge, Finset.sum_add_distrib]
  omega

def pairParameters : UnequalParameters :=
  ⟨262144,131071,181343,153,33,21378,276,62,7204⟩

theorem pair_count {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}
    (inp : Input u0 u1 selected Gamma) (Q T : P4) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hbox : Q ∈ RCN174.globalCoefficientBox K 20129073 131071 21378 33)
    (hTcaps : T.degreeOf 1 ≤ 276 ∧ T.degreeOf 2 ≤ 62 ∧ T.degreeOf 3 ≤ 7204) :
    (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) ≤ 860903991184427 := by
  have hcount := all_regularPairSeeds_bound pairParameters Q T hQ hrel
    20129073 131071 21378 33 2130706433 hbox
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hTcaps.1 hTcaps.2.1 hTcaps.2.2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by rw [Finset.card_univ]; exact Fintype.card_fin _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    inp.degree inp.agreement (by simpa only [pairParameters, UnequalParameters.errors, (show (262144 - 181343 : ℕ) = 80801 by decide +kernel)] using inp.noPencil)
  have hsum := sum_regular_counts_bound pairParameters Q T selected Gamma
    (regularVector_budgets pairParameters Q hQ 20129073 131071 21378 33
      (by decide +kernel) hbox (by decide +kernel) (by decide +kernel) (by decide +kernel)) hcount
  have hc := pairParameters.regular_count_le _ (by decide +kernel) hsum
  exact hc.trans_eq (by decide +kernel)

end
end ProximityPrize.SubmissionLower.Lower80801.Geometry
