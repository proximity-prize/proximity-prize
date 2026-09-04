import ProximityPrize.SubmissionLower.LocatorGroupedNonRegularCardinality6803
import ProximityPrize.SubmissionLower.LocatorFixedChain

/-!
Cardinality consumers for the grouped exact-derivative cover.  These lemmas
separate the geometric cover from the numeric regular and non-regular ledgers,
so the final fixed and residual bridges only have to instantiate those two
bounds.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedCoverCardinality6803

open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN156 RCN167 RCN319
open LocatorGroupedNonRegularAssembly6803 LocatorFixedChain

set_option autoImplicit false

noncomputable section

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- For a self-pair `(Q,Q)`, the regular side of the grouped cover is bounded
by the usual sum of `regularSeeds`; the other side is the single grouped
non-regular set. -/
theorem fixed_card_le_regular_add_grouped
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (regularCap groupedCap : ℕ)
    (hregular : (∑ F : RegularIndex Q,
      (regularSeeds Q selected Gamma F).card) ≤ regularCap)
    (hgrouped :
      (allGroupedNonRegularSeeds Q selected Gamma).card ≤ groupedCap) :
    Gamma.card ≤ regularCap + groupedCap := by
  classical
  have hcover := cover_regular_or_allGroupedNonRegularSeeds
    Q Q hQ p s hsmall hR selected Gamma hsolution hsolution
  have hregularUnion :
      (Finset.univ.biUnion fun F : RegularIndex Q ↦
        regularPairSeeds Q Q selected Gamma F).card ≤ regularCap := by
    calc
      (Finset.univ.biUnion fun F : RegularIndex Q ↦
          regularPairSeeds Q Q selected Gamma F).card ≤
          ∑ F : RegularIndex Q,
            (regularPairSeeds Q Q selected Gamma F).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ F : RegularIndex Q,
          (regularSeeds Q selected Gamma F).card :=
        Finset.sum_le_sum (fun F _ ↦
          Finset.card_le_card (regularPairSeeds_self_subset Q selected Gamma F))
      _ ≤ regularCap := hregular
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add hregularUnion hgrouped))

/-- Residual form: the regular pair sum and the grouped non-regular set are
supplied independently. -/
theorem residual_card_le_regular_add_grouped
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0)
    (regularCap groupedCap : ℕ)
    (hregular : (∑ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card) ≤ regularCap)
    (hgrouped :
      (allGroupedNonRegularSeeds Q selected Gamma).card ≤ groupedCap) :
    Gamma.card ≤ regularCap + groupedCap := by
  classical
  have hcover := cover_regular_or_allGroupedNonRegularSeeds
    Q T hQ p s hsmall hR selected Gamma hQsolution hTsolution
  have hregularUnion :
      (Finset.univ.biUnion fun F : RegularIndex Q ↦
        regularPairSeeds Q T selected Gamma F).card ≤ regularCap :=
    Finset.card_biUnion_le.trans hregular
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add hregularUnion hgrouped))

end

end ProximityPrize.SubmissionLower.LocatorGroupedCoverCardinality6803
