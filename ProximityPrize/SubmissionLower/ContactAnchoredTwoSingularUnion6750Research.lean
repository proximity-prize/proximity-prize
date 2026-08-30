import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research

 







namespace ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research

open scoped Classical BigOperators
open ContactTranslation ContactSelectedSeedDecomposition
open ContactSimultaneousOccurrenceLedger6750Research
open ContactAnchoredProductOccurrenceCover6800Research

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

 
def anchoredSingularGSeeds
    (G : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma => specialization K (selected gamma) gamma
    (ContactSingularAuxiliary.singularAuxiliary G) = 0)

 

def anchoredSingularQSeeds
    (G Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0 ∧
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) = 0)

 

def anchoredGoodSeeds
    (G Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0 ∧
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0)

 
theorem subset_anchored_singular_union_good
    (G Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) :
    Gamma ⊆
      (anchoredSingularGSeeds G selected Gamma ∪
        anchoredSingularQSeeds G Q selected Gamma) ∪
      anchoredGoodSeeds G Q selected Gamma := by
  intro gamma hgamma
  by_cases hGaux : specialization K (selected gamma) gamma
      (ContactSingularAuxiliary.singularAuxiliary G) = 0
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_filter.mpr ⟨hgamma, hGaux⟩
  · by_cases hQaux : specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) = 0
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hgamma, hGaux, hQaux⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hgamma, hGaux, hQaux⟩

 


theorem anchored_card_le_two_singular_add_regular_of_product_derivative
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (singularG singularQ regularG regularQ : Nat)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hsingularG : (anchoredSingularGSeeds G selected Gamma).card ≤ singularG)
    (hsingularQ :
      (anchoredSingularQSeeds G Q selected Gamma).card ≤ singularQ)
    (hGsum : (∑ R : NormalizedOccurrence G,
      (occurrenceRegularSeeds G selected
        (anchoredGoodSeeds G Q selected Gamma) R).card) ≤ regularG)
    (hQsum : (∑ R : NormalizedOccurrence Q,
      (occurrenceRegularSeeds Q selected
        (anchoredGoodSeeds G Q selected Gamma) R).card) ≤ regularQ) :
    Gamma.card ≤ singularG + singularQ + (regularG + regularQ) / 2 := by
  let Good := anchoredGoodSeeds G Q selected Gamma
  have hGoodSubset : Good ⊆ Gamma := Finset.filter_subset _ _
  have hgood : Good.card ≤ (regularG + regularQ) / 2 := by
    apply anchored_card_le_add_div_two_of_product_derivative
      G Q hG hQ selected Good regularG regularQ
    · intro gamma hgamma
      exact hGzero gamma (hGoodSubset hgamma)
    · intro gamma hgamma
      exact hproductDerivative gamma (hGoodSubset hgamma)
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2.1
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2.2
    · exact hGsum
    · exact hQsum
  have hcover := subset_anchored_singular_union_good G Q selected Gamma
  calc
    Gamma.card ≤
        ((anchoredSingularGSeeds G selected Gamma ∪
          anchoredSingularQSeeds G Q selected Gamma) ∪ Good).card :=
      Finset.card_le_card hcover
    _ ≤ (anchoredSingularGSeeds G selected Gamma ∪
          anchoredSingularQSeeds G Q selected Gamma).card + Good.card :=
      Finset.card_union_le _ _
    _ ≤ ((anchoredSingularGSeeds G selected Gamma).card +
          (anchoredSingularQSeeds G Q selected Gamma).card) + Good.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (singularG + singularQ) + (regularG + regularQ) / 2 :=
      Nat.add_le_add (Nat.add_le_add hsingularG hsingularQ) hgood

end

end ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research.subset_anchored_singular_union_good
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research.anchored_card_le_two_singular_add_regular_of_product_derivative
