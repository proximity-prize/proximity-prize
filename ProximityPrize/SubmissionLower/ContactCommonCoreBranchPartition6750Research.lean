import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredTwoSingularUnion6750Research

 










namespace ProximityPrize.SubmissionLower
namespace ContactCommonCoreBranchPartition6750Research

open scoped Classical BigOperators
open ContactTranslation ContactSelectedSeedDecomposition
open ContactSimultaneousOccurrenceLedger6750Research
open ContactAnchoredProductOccurrenceCover6800Research
open ContactAnchoredTwoSingularUnion6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

 

def commonCoreZeroSeeds
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma ↦
    specialization K (selected gamma) gamma H = 0)

 

def commonCoreNonzeroSeeds
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter (fun gamma ↦
    specialization K (selected gamma) gamma H ≠ 0)

theorem commonCoreZeroSeeds_subset
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    commonCoreZeroSeeds H selected Gamma ⊆ Gamma :=
  Finset.filter_subset _ _

theorem commonCoreNonzeroSeeds_subset
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    commonCoreNonzeroSeeds H selected Gamma ⊆ Gamma :=
  Finset.filter_subset _ _

 
theorem commonCoreZeroSeeds_disjoint_nonzeroSeeds
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    Disjoint (commonCoreZeroSeeds H selected Gamma)
      (commonCoreNonzeroSeeds H selected Gamma) := by
  rw [Finset.disjoint_left]
  intro gamma hzero hnonzero
  exact (Finset.mem_filter.mp hnonzero).2
    (Finset.mem_filter.mp hzero).2

 
theorem commonCoreZeroSeeds_union_nonzeroSeeds
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    commonCoreZeroSeeds H selected Gamma ∪
      commonCoreNonzeroSeeds H selected Gamma = Gamma := by
  ext gamma
  simp only [commonCoreZeroSeeds, commonCoreNonzeroSeeds,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hgamma, _⟩ | ⟨hgamma, _⟩) <;> exact hgamma
  · intro hgamma
    by_cases hzero : specialization K (selected gamma) gamma H = 0
    · exact Or.inl ⟨hgamma, hzero⟩
    · exact Or.inr ⟨hgamma, hzero⟩

 
theorem commonCore_branch_card_partition
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    (commonCoreZeroSeeds H selected Gamma).card +
        (commonCoreNonzeroSeeds H selected Gamma).card = Gamma.card := by
  exact Finset.card_filter_add_card_filter_not
    (s := Gamma)
    (p := fun gamma ↦ specialization K (selected gamma) gamma H = 0)

 

theorem card_le_anchoredCap_add_residualCap
    (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (anchoredCap residualCap : Nat)
    (hanchored :
      (commonCoreZeroSeeds H selected Gamma).card ≤ anchoredCap)
    (hresidual :
      (commonCoreNonzeroSeeds H selected Gamma).card ≤ residualCap) :
    Gamma.card ≤ anchoredCap + residualCap := by
  rw [← commonCore_branch_card_partition H selected Gamma]
  exact Nat.add_le_add hanchored hresidual

 






theorem fixedSeeds_card_le_anchored_add_residual
    (H Q : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (singularH singularQ regularH regularQ residualCap : Nat)
    (hproductDerivative :
      ∀ gamma ∈ commonCoreZeroSeeds H selected Gamma,
        specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4) (H * Q)) = 0)
    (hsingularH :
      (anchoredSingularGSeeds H selected
        (commonCoreZeroSeeds H selected Gamma)).card ≤ singularH)
    (hsingularQ :
      (anchoredSingularQSeeds H Q selected
        (commonCoreZeroSeeds H selected Gamma)).card ≤ singularQ)
    (hHsum :
      (∑ R : NormalizedOccurrence H,
        (occurrenceRegularSeeds H selected
          (anchoredGoodSeeds H Q selected
            (commonCoreZeroSeeds H selected Gamma)) R).card) ≤ regularH)
    (hQsum :
      (∑ R : NormalizedOccurrence Q,
        (occurrenceRegularSeeds Q selected
          (anchoredGoodSeeds H Q selected
            (commonCoreZeroSeeds H selected Gamma)) R).card) ≤ regularQ)
    (hresidual :
      (commonCoreNonzeroSeeds H selected Gamma).card ≤ residualCap) :
    Gamma.card ≤
      singularH + singularQ + (regularH + regularQ) / 2 + residualCap := by
  apply card_le_anchoredCap_add_residualCap H selected Gamma
    (singularH + singularQ + (regularH + regularQ) / 2) residualCap
  · apply anchored_card_le_two_singular_add_regular_of_product_derivative
      H Q hH hQ selected (commonCoreZeroSeeds H selected Gamma)
        singularH singularQ regularH regularQ
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2
    · exact hproductDerivative
    · exact hsingularH
    · exact hsingularQ
    · exact hHsum
    · exact hQsum
  · exact hresidual

end

end ContactCommonCoreBranchPartition6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactCommonCoreBranchPartition6750Research.commonCoreZeroSeeds_disjoint_nonzeroSeeds
#print axioms ProximityPrize.SubmissionLower.ContactCommonCoreBranchPartition6750Research.commonCore_branch_card_partition
#print axioms ProximityPrize.SubmissionLower.ContactCommonCoreBranchPartition6750Research.card_le_anchoredCap_add_residualCap
#print axioms ProximityPrize.SubmissionLower.ContactCommonCoreBranchPartition6750Research.fixedSeeds_card_le_anchored_add_residual
