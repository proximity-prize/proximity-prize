import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533Conditional
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount6533

/-!
# Unconditional global selected-polynomial count for 65.67

The regular global-shear theorem and the already-discharged implicit branch
are assembled here into the exact finite selected-family bound consumed by
the alignment layer.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533

open ContactParameters6533 ContactShearLedger6533
open ContactGlobalSelectedFamilies6533 ContactSelectedSeedDecomposition
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactFullTriangleAgreement

noncomputable section

variable (K : Type) [Field K]
variable {ι : Type*}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem global_selected_count6533 [CharP K prime]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hfullQ : Q ∈ fullTriangleBox K seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card < alignmentBudget := by
  classical
  apply ContactGlobalSelectedCount6533Conditional.global_selected_count_of_regular_estimate
    K Q hQ hbox selected Gamma nodes x u0 u1 hinj hnodes
      hdegree hsolution hagreement hnoPencil
  intro F
  obtain ⟨hirred, hRpos, hFbox⟩ :=
    directFactor_data Q F.1 hQ weightedCap w seedTotalCap slopeCap hbox F.2
  have hfullF : MvPolynomial.weightedTotalDegree fullSurfaceWeights F.1 ≤
      seedTotalCap :=
    full_wt_le_of_dvd F.1 Q seedTotalCap hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q F.1 F.2).2.1 hfullQ
  have hsub := regularSeeds_subset Q selected Gamma F
  have h := ContactOriginalRegularSeedCount6533.original_regular_seed_bound
    K F.1 hirred hRpos hFbox hfullF selected (regularSeeds Q selected Gamma F)
      nodes x u0 u1 hinj hnodes
      (fun gamma hgamma => hdegree gamma (hsub hgamma))
      (fun gamma hgamma => (regularSeeds_solution Q selected Gamma F gamma hgamma).1)
      (fun gamma hgamma => (regularSeeds_solution Q selected Gamma F gamma hgamma).2)
      (fun gamma hgamma => hagreement gamma (hsub hgamma))
      (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil)
  simpa only [regularVector,
    ContactOriginalRegularSeedCount6533.originalDegreeVector] using h

end
end ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533

#print axioms ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533.global_selected_count6533
