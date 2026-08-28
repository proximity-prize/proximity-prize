import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6533
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount6533

/-!
# Global 65.67 selected count, conditional only on the regular-shear branch

The interpolation polynomial, finite cover, exceptions, implicit pairs, and
final numerical ledger are fully discharged.  The sole explicit premise is
the componentwise sheared regular-family estimate.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533Conditional

open ContactParameters6533 ContactShearLedger6533
open ContactGlobalSelectedFamilies6533 ContactSelectedSeedDecomposition
open ContactImplicitPairBudgets ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount

noncomputable section

variable (K : Type) [Field K]
variable {ι : Type*}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem global_selected_count_of_regular_estimate [CharP K prime]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0)
    (hagreement : ∀ γ ∈ Γ,
      agreements ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors)
    (hregular : ∀ F : RegularIndex Q,
      (regularSeeds Q selected Γ F).card * gap ^ 2 ≤
        shearedWholeNumerator (regularVector Q F)) :
    Γ.card < alignmentBudget := by
  classical
  apply global_count_of_actual_branch_estimates Q hQ hbox selected Γ hsolution hregular
  intro q
  obtain ⟨hJ, hJbox⟩ := singularAuxiliary_nonzero_mem_box Q weightedCap w seedTotalCap
    slopeCap prime hQ (by norm_num [slopeCap]) implicit_characteristic_gates.2.2.2 hbox
  obtain ⟨_hA, hG, hGR, hAbox, hGbox, hproper⟩ :=
    implicitPair_data (singularAuxiliary Q) hJ implicitWeightedCap w algebraicCap
      (by norm_num [w])
      (by norm_num [w, implicitWeightedCap, slopeCap, weightedCap,
        ContactParameters6533.multiplicity, agreements, n, errors]) hJbox q.1 q.2
  have hsub := implicitSeeds_subset Q selected Γ q
  have h := ContactImplicitPairSeedCount6533.implicit_pair_seed_bound_fixed
    (K := K) q.1.1 q.1.2 hG hGR hproper hAbox hGbox
    selected (implicitSeeds Q selected Γ q) nodes x u₀ u₁ hinj hnodes
    (fun γ hγ => hdegree γ (hsub hγ))
    (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).1)
    (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).2.2.1)
    (fun γ hγ => (implicitSeeds_solution Q selected Γ q γ hγ).2.2.2)
    (fun γ hγ => hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ _ w errors hsub hnoPencil)
  simpa only [implicitVector, ContactImplicitPairSeedCount6533.pairCost] using h

end
end ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533Conditional

#print axioms ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533Conditional.global_selected_count_of_regular_estimate
