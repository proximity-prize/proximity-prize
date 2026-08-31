import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount6600Research
namespace ProximityPrize.SubmissionLower.ContactSingularBranch6600Research
open scoped BigOperators
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactSelectedSeedDecomposition ContactImplicitPairBudgets
open ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds ContactInterpolation ContactTranslation
open ContactImplicitPairSeedCount6600Research
open ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
  ↥(implicitPairSet (singularAuxiliary Q))
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (q:ImplicitIndex Q):Finset K:=by
  classical
  exact Gamma.filter (fun gamma => LiftedSolutionPair q.1 (selected gamma) gamma)
def implicitVector (Q:MvPolynomial (Fin 4) K)
    (q:ImplicitIndex Q):DegreeVector:=
  ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
def singularSeeds (Q:MvPolynomial (Fin 4) K)
    (selected:K-> Polynomial K) (Gamma:Finset K):Finset K:=by
  classical
  exact Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
    exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (q:ImplicitIndex Q):implicitSeeds Q selected Gamma q ⊆ Gamma:=by
  classical
  exact Finset.filter_subset _ _
theorem implicitSeeds_solution (Q:MvPolynomial (Fin 4) K)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (q:ImplicitIndex Q) (gamma:K)
    (hgamma:gamma∈implicitSeeds Q selected Gamma q):
    LiftedSolutionPair q.1 (selected gamma) gamma:=by
  classical
  exact (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
    (Q:MvPolynomial (Fin 4) K)
    (selected:K-> Polynomial K) (Gamma:Finset K):
    (singularSeeds Q selected Gamma).card ≤
      (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
        (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
  classical
  unfold singularSeeds
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right Finset.card_biUnion_le _)
theorem implicitVector_budgets
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
    (∑ q:ImplicitIndex Q,(implicitVector Q q).y) ≤ algebraicCap∧
      (∑ q:ImplicitIndex Q,(implicitVector Q q).r) ≤
        2*implicitYCap*algebraicCap∧
      (∑ q:ImplicitIndex Q,(implicitVector Q q).z) ≤ implicitYCap:=by
  classical
  obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
    weightedCap w seedTotalCap slopeCap prime hQ
    (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
  have hb:=implicitPair_input_budgets (singularAuxiliary Q) hJ
    implicitWeightedCap w algebraicCap (by norm_num [w]) hJbox
  simpa only [implicitVector,Finset.sum_coe_sort,implicitYCap] using hb
theorem exceptionalSeeds_bound
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K-> Polynomial K) (Gamma:Finset K):
    (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
      2*algebraicCap^2:=by
  classical
  obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
    weightedCap w seedTotalCap slopeCap prime hQ
    (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
  have hcaps:=degree_bounds_of_mem_box (singularAuxiliary Q)
    implicitWeightedCap w algebraicCap 0 (by norm_num [w]) hJbox
  have hJR:(singularAuxiliary Q).degreeOf 2=0:=
    Nat.eq_zero_of_le_zero hcaps.2.1
  apply exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
    algebraicCap prime
  · norm_num [algebraicCap,slopeCap,seedTotalCap]
  · exact characteristic_gates.2.2.1
  · exact hcaps.1.trans (by
      norm_num [implicitYCap,implicitWeightedCap,weightedCap,
        ContactParameters6600Research.multiplicity,agreements,n,errors,
        w,algebraicCap,slopeCap,seedTotalCap])
  · exact hcaps.2.2
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem implicitSeeds_pair_bound
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota-> K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
    (q:ImplicitIndex Q):
    (implicitSeeds Q selected Gamma q).card*gap ≤
      (n-w)*dot liftedAgreement (implicitVector Q q)+
        (errors+1)*gap*(implicitVector Q q).z:=by
  classical
  obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
    weightedCap w seedTotalCap slopeCap prime hQ
    (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
  obtain ⟨_hA,hG,hGR,hAbox,hGbox,hproper⟩:=
    implicitPair_data (singularAuxiliary Q) hJ implicitWeightedCap w
      algebraicCap (by norm_num [w])
      (by norm_num [w,implicitWeightedCap,weightedCap,
        ContactParameters6600Research.multiplicity,agreements,n,errors,
        slopeCap]) hJbox q.1 q.2
  have hsub:=implicitSeeds_subset Q selected Gamma q
  have hpair:=ContactImplicitPairSeedCount6600Research.implicit_pair_seed_bound_fixed
    q.1.1 q.1.2 hG hGR hproper hAbox hGbox selected
    (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
    (fun gamma hgamma => hdegree gamma (hsub hgamma))
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
    (fun gamma hgamma => hagreement gamma (hsub hgamma))
    (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil)
  simpa [implicitVector,
    ContactImplicitPairSeedCount6600Research.pairCost] using hpair
theorem singularSeeds_gap_bound
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota-> K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
    (singularSeeds Q selected Gamma).card*gap ≤
      retainedSingularNumerator:=by
  have hcaps:=implicitVector_budgets Q hQ hbox
  have hexc:=exceptionalSeeds_bound Q hQ hbox selected Gamma
  have hsum:=implicit_with_exceptions_bound
    (fun q:ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
    (implicitVector Q)
    (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
    hcaps.1 hcaps.2.1 hcaps.2.2
    (implicitSeeds_pair_bound Q hQ hbox selected Gamma nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)
    hexc
  exact (Nat.mul_le_mul_right gap
    (singularSeeds_card_le_sum Q selected Gamma)).trans hsum
theorem singularSeeds_scaled_bound
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    [CharP K prime]
    (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected:K-> Polynomial K) (Gamma:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota-> K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
    (singularSeeds Q selected Gamma).card*gap^2 ≤
      retainedSingularContribution:=by
  have h:=singularSeeds_gap_bound Q hQ hbox selected Gamma nodes x u0 u1
    hinj hnodes hdegree hagreement hnoPencil
  calc
    (singularSeeds Q selected Gamma).card*gap^2=
        ((singularSeeds Q selected Gamma).card*gap)*gap:=by ring
    _ ≤ retainedSingularNumerator*gap:=Nat.mul_le_mul_right gap h
    _=retainedSingularContribution:=by
      simp only [retainedSingularContribution]
      ring
end
end ProximityPrize.SubmissionLower.ContactSingularBranch6600Research
