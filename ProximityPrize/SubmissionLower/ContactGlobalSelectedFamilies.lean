import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactCountingLedger

/-!
# Constructed selected-seed families and the global finite-cover ledger

Model label: gpt-5.

The families are actual filters of the supplied selected seeds, indexed
by the actual factor and implicit-pair sets. Their cover, exceptional
count, and summed degree budgets follow from the verified algebraic
decomposition. Overlap is harmless and no disjoint partition is assumed.

The final theorem in THIS helper still states per-branch estimates as
explicit inputs. ContactGlobalSelectedCount will discharge those inputs
using the separate actual regular-factor and implicit-pair theorems.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies

open ContactAlignmentParameters ContactImplicitLiftParameters ContactCountingLedger
open ContactSelectedSeedDecomposition ContactImplicitPairBudgets ContactImplicitContactLift
open ContactExceptionalSeedAuxiliary ContactSingularAuxiliary ContactSingularDegreeBounds
open ContactInterpolation ContactTranslation ContactFactorCaps
open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) := ↥(positiveRFactors Q)

abbrev ImplicitIndex (Q : MvPolynomial (Fin 4) K) := ↥(implicitPairSet (singularAuxiliary Q))

def regularSeeds (Q : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (F : RegularIndex Q) : Finset K := by
  classical
  exact Γ.filter (fun γ => RegularSolution F.1 (selected γ) γ)

def implicitSeeds (Q : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (q : ImplicitIndex Q) : Finset K := by
  classical
  exact Γ.filter (fun γ => LiftedSolutionPair q.1 (selected γ) γ)

theorem regularSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Γ : Finset K) (F : RegularIndex Q) :
    regularSeeds Q selected Γ F ⊆ Γ := by
  classical
  exact Finset.filter_subset _ _

theorem implicitSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Γ : Finset K) (q : ImplicitIndex Q) :
    implicitSeeds Q selected Γ q ⊆ Γ := by
  classical
  exact Finset.filter_subset _ _

theorem regularSeeds_solution (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Γ : Finset K) (F : RegularIndex Q)
    (γ : K) (hγ : γ ∈ regularSeeds Q selected Γ F) : RegularSolution F.1 (selected γ) γ := by
  classical
  exact (Finset.mem_filter.mp hγ).2

theorem implicitSeeds_solution (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Γ : Finset K) (q : ImplicitIndex Q)
    (γ : K) (hγ : γ ∈ implicitSeeds Q selected Γ q) : LiftedSolutionPair q.1 (selected γ) γ := by
  classical
  exact (Finset.mem_filter.mp hγ).2

def regularVector (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) : DegreeVector :=
  ⟨F.1.degreeOf 1, F.1.degreeOf 2, F.1.degreeOf 3⟩

def implicitVector (Q : MvPolynomial (Fin 4) K) (q : ImplicitIndex Q) : DegreeVector :=
  ⟨pairYCost q.1, pairRCost q.1, pairZCost q.1⟩

theorem card_le_two_family_sums_plus_exception
    {Seed I J : Type} [Fintype I] [Fintype J]
    (Γ E : Finset Seed) (R : I → Finset Seed) (T : J → Finset Seed)
    (hcover : ∀ γ ∈ Γ, γ ∈ E ∨ (∃ i, γ ∈ R i) ∨ (∃ j, γ ∈ T j)) :
    Γ.card ≤ (∑ i, (R i).card) + (∑ j, (T j).card) + E.card := by
  classical
  letI : DecidableEq Seed := Classical.decEq Seed
  have hsub : Γ ⊆ (Finset.univ.biUnion R ∪ Finset.univ.biUnion T) ∪ E := by
    intro γ hγ
    obtain hE | ⟨i, hi⟩ | ⟨j, hj⟩ := hcover γ hγ
    · exact Finset.mem_union.mpr (Or.inr hE)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩))))
  calc
    _ ≤ ((Finset.univ.biUnion R ∪ Finset.univ.biUnion T) ∪ E).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.biUnion R ∪ Finset.univ.biUnion T).card + E.card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.biUnion R).card + (Finset.univ.biUnion T).card) + E.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right
      (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le) _

theorem regularVector_budgets (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    (∑ F : RegularIndex Q, (regularVector Q F).y) ≤ 30 ∧
      (∑ F : RegularIndex Q, (regularVector Q F).r) ≤ 6 ∧
      (∑ F : RegularIndex Q, (regularVector Q F).z) ≤ 318 := by
  classical
  have hb := directFactor_input_budgets Q hQ weightedCap w seedTotalCap slopeCap (by decide) hbox
  have hy : (∑ F ∈ positiveRFactors Q, F.degreeOf (1 : Fin 4)) ≤ 30 := by
    have hh := hb.1
    change (∑ F ∈ positiveRFactors Q, F.degreeOf (1 : Fin 4)) ≤ yCap at hh
    rwa [parameter_values.2.1] at hh
  refine ⟨?_, ?_, ?_⟩
  · simpa only [regularVector, Finset.sum_coe_sort] using hy
  · simpa only [regularVector, Finset.sum_coe_sort, slopeCap] using hb.2.1
  · simpa only [regularVector, Finset.sum_coe_sort, seedTotalCap] using hb.2.2

theorem implicitVector_budgets (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    (∑ q : ImplicitIndex Q, (implicitVector Q q).y) ≤ algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector Q q).r) ≤ 2 * implicitYCap * algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector Q q).z) ≤ implicitYCap := by
  classical
  obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box Q weightedCap w seedTotalCap
    slopeCap prime hQ (by decide) characteristic_gates.2.2.2 hbox
  have hb := implicitPair_input_budgets (singularAuxiliary Q) hJ implicitWeightedCap w
    algebraicCap (by decide) hJbox
  simpa only [implicitVector, Finset.sum_coe_sort, implicitYCap] using hb

theorem constructed_family_cover (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Γ : Finset K)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0) :
    Γ.card ≤ (∑ F : RegularIndex Q, (regularSeeds Q selected Γ F).card) +
        (∑ q : ImplicitIndex Q, (implicitSeeds Q selected Γ q).card) +
        (exceptionalSeeds (singularAuxiliary Q) Γ selected).card ∧
      (exceptionalSeeds (singularAuxiliary Q) Γ selected).card ≤ 2 * algebraicCap ^ 2 := by
  classical
  have hd := selected_seed_decomposition Q hQ weightedCap w seedTotalCap slopeCap prime
    (by decide) characteristic_gates.2.2.2 (by decide)
    (by norm_num [w, slopeCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements])
    (by decide) characteristic_gates.2.2.1 hbox Γ selected hsolution
  refine ⟨?_, hd.1⟩
  apply card_le_two_family_sums_plus_exception
  intro γ hγ
  by_cases hE : γ ∈ exceptionalSeeds (singularAuxiliary Q) Γ selected
  · exact Or.inl hE
  · obtain ⟨F, hF, hreg⟩ | ⟨q, hq, himp⟩ := hd.2.1 γ hγ hE
    · exact Or.inr (Or.inl ⟨⟨F, hF⟩, Finset.mem_filter.mpr ⟨hγ, hreg⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨q, hq⟩, Finset.mem_filter.mpr ⟨hγ, himp⟩⟩)

/-- Helper interface only: branch estimates remain explicit HERE and are
discharged by the final ContactGlobalSelectedCount module. -/
theorem global_count_of_actual_branch_estimates
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Γ : Finset K)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds Q selected Γ F).card * gap ^ 2 ≤ wholeNumerator (regularVector Q F))
    (himplicit : ∀ q : ImplicitIndex Q,
      (implicitSeeds Q selected Γ q).card * gap ≤
        n * dot liftedAgreement (implicitVector Q q) +
          (errors + 1) * gap * (implicitVector Q q).z) : Γ.card < alignmentBudget := by
  have hregCaps := regularVector_budgets Q hQ hbox
  have himpCaps := implicitVector_budgets Q hQ hbox
  have hcover := constructed_family_cover Q hQ hbox selected Γ hsolution
  exact final_family_ledger
    (fun F : RegularIndex Q => (regularSeeds Q selected Γ F).card) (regularVector Q)
    (fun q : ImplicitIndex Q => (implicitSeeds Q selected Γ q).card) (implicitVector Q)
    (exceptionalSeeds (singularAuxiliary Q) Γ selected).card Γ.card
    hregCaps.1 hregCaps.2.1 hregCaps.2.2 hregular
    himpCaps.1 himpCaps.2.1 himpCaps.2.2 himplicit hcover.2 hcover.1

#print axioms regularSeeds_solution
#print axioms implicitSeeds_solution
#print axioms card_le_two_family_sums_plus_exception
#print axioms regularVector_budgets
#print axioms implicitVector_budgets
#print axioms constructed_family_cover
#print axioms global_count_of_actual_branch_estimates

end
end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies
