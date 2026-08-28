import ProximityPrize.SubmissionLower.BCHKSFrobeniusScrollInterpolation6400

/-!
# Low-stack kernel extraction

The `2h × |S|` source matrix is represented as the evaluation linear map from
two copies of the degree-`<h` polynomial space.  A nontrivial kernel therefore
produces the exact pair of bounded polynomials required by the gcd-aware
reduction module.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {K : Type} [Field K]

/-- Evaluation map for a two-block low-stack relation
`A(x) * source(x) + B(x) * target(x)`. -/
noncomputable def lowStackRelationMap
    (S : Finset K) (source target : K → K) (h : ℕ) :
    ((Polynomial.degreeLT K h) × (Polynomial.degreeLT K h)) →ₗ[K]
      (S → K) where
  toFun q x :=
    q.1.1.eval x.1 * source x.1 + q.2.1.eval x.1 * target x.1
  map_add' q r := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Polynomial.eval_add, Pi.add_apply]
    ring
  map_smul' a q := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower,
      Polynomial.eval_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- A nontrivial bounded polynomial relation on every point of a source set. -/
structure BoundedKernelRelation
    (S : Finset K) (source target : K → K) (h : ℕ) where
  sourceMultiplier : K[X]
  targetMultiplier : K[X]
  nontrivial : ¬(sourceMultiplier = 0 ∧ targetMultiplier = 0)
  sourceMultiplier_degree : sourceMultiplier.natDegree < h
  targetMultiplier_degree : targetMultiplier.natDegree < h
  relation : ∀ x ∈ S,
    sourceMultiplier.eval x * source x +
      targetMultiplier.eval x * target x = 0

/-- Membership in `degreeLT h` gives the corresponding `natDegree` bound as
soon as `h` is positive, including for the zero polynomial. -/
theorem natDegree_lt_of_mem_degreeLT_of_pos
    (h : ℕ) (hh : 0 < h) (P : Polynomial.degreeLT K h) :
    P.1.natDegree < h := by
  by_cases hP : P.1 = 0
  · simpa [hP] using hh
  · have hdegree := Polynomial.mem_degreeLT.mp P.2
    rw [Polynomial.degree_eq_natDegree hP] at hdegree
    exact_mod_cast hdegree

/-- Extract a bounded polynomial relation from nontrivial kernel of the
low-stack evaluation map. -/
noncomputable def boundedKernelRelation_of_ker_ne_bot
    (S : Finset K) (source target : K → K) (h : ℕ)
    (hker : LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥) :
    BoundedKernelRelation S source target h := by
  classical
  let hex := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let q := Classical.choose hex
  have hqspec := Classical.choose_spec hex
  have hqker : q ∈ LinearMap.ker (lowStackRelationMap S source target h) :=
    hqspec.1
  have hqne : q ≠ 0 := hqspec.2
  have hnontrivial : ¬(q.1.1 = 0 ∧ q.2.1 = 0) := by
    intro hz
    apply hqne
    apply Prod.ext
    · exact Subtype.ext hz.1
    · exact Subtype.ext hz.2
  have hh : 0 < h := by
    rcases not_and_or.mp hnontrivial with hleft | hright
    · have hdegree := Polynomial.mem_degreeLT.mp q.1.2
      rw [Polynomial.degree_eq_natDegree hleft] at hdegree
      have hdegreeNat : q.1.1.natDegree < h := by exact_mod_cast hdegree
      exact Nat.zero_lt_of_lt hdegreeNat
    · have hdegree := Polynomial.mem_degreeLT.mp q.2.2
      rw [Polynomial.degree_eq_natDegree hright] at hdegree
      have hdegreeNat : q.2.1.natDegree < h := by exact_mod_cast hdegree
      exact Nat.zero_lt_of_lt hdegreeNat
  refine
    { sourceMultiplier := q.1.1
      targetMultiplier := q.2.1
      nontrivial := hnontrivial
      sourceMultiplier_degree := natDegree_lt_of_mem_degreeLT_of_pos h hh q.1
      targetMultiplier_degree := natDegree_lt_of_mem_degreeLT_of_pos h hh q.2
      relation := ?_ }
  intro x hx
  have hzero : lowStackRelationMap S source target h q = 0 := hqker
  have heval := congrFun hzero ⟨x, hx⟩
  simpa only [lowStackRelationMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply] using heval

/-- Compose kernel extraction with the checked gcd-aware normalization. -/
noncomputable def reducedKernelRelation_of_ker_ne_bot
    [DecidableEq K]
    (S : Finset K) (source target : K → K) (h : ℕ)
    (hcard : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hker : LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥) :
    ReducedKernelRelation S source target h := by
  let r := boundedKernelRelation_of_ker_ne_bot S source target h hker
  exact reducedKernelRelation_of_polynomial_relation
    r.sourceMultiplier r.targetMultiplier S source target h r.nontrivial
    r.sourceMultiplier_degree r.targetMultiplier_degree
    hcard hsource r.relation

/-- Three nontrivial low-stack kernels feed directly into the checked
normalization and scroll-assembly chain.  After this theorem, the upstream
matrix task is exactly to prove the three `ker ≠ ⊥` hypotheses. -/
noncomputable def scrollAtom_of_lowStack_kernels
    {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
    (S : Finset F) (source target₀ target₁ : F → F)
    (genericSource genericTarget : RatFunc F → RatFunc F) (h : ℕ)
    (hcard : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hgenericSource : ∀ x ∈ S,
      genericSource (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (source x))
    (hgenericTarget : ∀ x ∈ S,
      genericTarget (algebraMap F (RatFunc F) x) =
        algebraMap F (RatFunc F) (target₀ x) +
          (RatFunc.X : RatFunc F) *
            algebraMap F (RatFunc F) (target₁ x))
    (hstrict : 3 * h < S.card)
    (hker : LinearMap.ker
      (lowStackRelationMap
        (S.image (algebraMap F (RatFunc F)))
        genericSource genericTarget h) ≠ ⊥)
    (hker₀ : LinearMap.ker
      (lowStackRelationMap S source target₀ h) ≠ ⊥)
    (hker₁ : LinearMap.ker
      (lowStackRelationMap S source target₁ h) ≠ ⊥) :
    DefectAwareScrollAtom S source target₀ target₁ h := by
  classical
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  have hφ : Function.Injective φ := φ.injective
  have hcardGeneric : h ≤ (S.image φ).card := by
    rw [Finset.card_image_of_injective S hφ]
    exact hcard
  have hsourceGeneric : ∀ y ∈ S.image φ, genericSource y ≠ 0 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
    rw [← hxy, hgenericSource x hxS]
    exact (_root_.map_ne_zero φ).2 (hsource x hxS)
  let r := reducedKernelRelation_of_ker_ne_bot
    (S.image φ) genericSource genericTarget h
    hcardGeneric hsourceGeneric hker
  let r₀ := reducedKernelRelation_of_ker_ne_bot
    S source target₀ h hcard hsource hker₀
  let r₁ := reducedKernelRelation_of_ker_ne_bot
    S source target₁ h hcard hsource hker₁
  exact reduced_kernel_relations_scroll_atom
    S source target₀ target₁ genericSource genericTarget h
    r r₀ r₁ hsource hgenericSource hgenericTarget hstrict

end ProximityPrize.SubmissionLower
