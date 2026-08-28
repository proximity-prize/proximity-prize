import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount

/-!
# The actual global selected-polynomial count for the fixed witness

Model label: gpt-5.

The nonzero interpolation polynomial supplies actual direct factors,
implicit equation/lift-factor pairs, and an exceptional seed set. Every
branch estimate is proved by the imported branch theorem, on the actual
filtered selected family. The finite cover and summed degree budgets are
then fed to the verified exact numerical ledger.

There is no assumed geometric cover, component degree sum, branch count,
first-tail condition, or all-tail condition in the final theorem. The
no-large-selected-pencil premise is the explicit contrapositive alignment
input, and the nonzero interpolation polynomial is a separate constructed
front-end input.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedCount

open ContactAlignmentParameters ContactImplicitLiftParameters ContactCountingLedger
open ContactGlobalSelectedFamilies ContactSelectedSeedDecomposition
open ContactImplicitPairBudgets ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactImplicitPairSeedCount

noncomputable section

variable (K : Type) [Field K]
variable {ι : Type*}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem global_selected_count [CharP K prime]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0)
    (hagreement : ∀ γ ∈ Γ,
      agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors) : Γ.card < alignmentBudget := by
  classical
  apply global_count_of_actual_branch_estimates Q hQ hbox selected Γ hsolution
  · intro F
    obtain ⟨hirred, hRpos, hFbox⟩ :=
      directFactor_data Q F.1 hQ weightedCap w seedTotalCap slopeCap hbox F.2
    have hsub := regularSeeds_subset Q selected Γ F
    exact original_regular_seed_bound K F.1 hirred hRpos hFbox selected
      (regularSeeds Q selected Γ F) nodes x u₀ u₁ hinj hnodes
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => (regularSeeds_solution Q selected Γ F γ hγ).1)
      (fun γ hγ => (regularSeeds_solution Q selected Γ F γ hγ).2)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w errors hsub hnoPencil)
  · intro q
    obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box Q weightedCap w seedTotalCap
      slopeCap prime hQ (by decide) characteristic_gates.2.2.2 hbox
    obtain ⟨_hA, hG, hGR, hAbox, hGbox, hproper⟩ :=
      implicitPair_data (singularAuxiliary Q) hJ implicitWeightedCap w algebraicCap
        (by decide)
        (by norm_num [w, implicitWeightedCap, slopeCap, weightedCap,
          ContactAlignmentParameters.multiplicity, agreements]) hJbox q.1 q.2
    have hsub := implicitSeeds_subset Q selected Γ q
    exact implicit_pair_seed_bound_fixed (K := K) q.1.1 q.1.2 hG hGR hproper hAbox hGbox
      selected (implicitSeeds Q selected Γ q) nodes x u₀ u₁ hinj hnodes
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).1)
      (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).2.2.1)
      (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).2.2.2)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w errors hsub hnoPencil)

#print axioms global_selected_count

end
end ProximityPrize.SubmissionLower.ContactGlobalSelectedCount
