import ProximityPrize.SubmissionLower.BCHKSFrobeniusSourceMatrix6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusDegreeDescent6400

/-!
# Mixed source-stack singularity and degree descent

For a source set of size `s = c + h`, the locator syndrome supplies a
nonzero right-kernel vector for the square matrix with `c` ordinary rows and
`h` Frobenius rows.  This file proves the purely linear-algebraic conversion
from that right kernel to a bounded left polynomial relation.  Given the
already-isolated bad-witness cofactor root count, it then descends the first
multiplier from degree `< c` to degree `< h`, producing the exact low-stack
kernel consumed by the rational-scroll construction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {K : Type} [Field K]

abbrev MixedStackIndex (c h : ℕ) := Fin c ⊕ Fin h

/-- The source-point-by-multiplier matrix with unequal block widths. -/
def mixedStackMatrix
    (S : Finset K) (source target : K → K) (c h : ℕ) :
    Matrix S (MixedStackIndex c h) K
  | x, Sum.inl i => x.1 ^ (i : ℕ) * source x.1
  | x, Sum.inr i => x.1 ^ (i : ℕ) * target x.1

/-- Evaluation of a degree-`<c` source multiplier and a degree-`<h` target
multiplier on every source point. -/
noncomputable def mixedStackRelationMap
    (S : Finset K) (source target : K → K) (c h : ℕ) :
    ((Polynomial.degreeLT K c) × (Polynomial.degreeLT K h)) →ₗ[K]
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

/-- Coefficient coordinates for the two unequal polynomial blocks. -/
noncomputable def mixedStackDomainEquiv (c h : ℕ) :
    ((Polynomial.degreeLT K c) × (Polynomial.degreeLT K h)) ≃ₗ[K]
      (MixedStackIndex c h → K) :=
  LinearEquiv.prodCongr
      (Polynomial.degreeLTEquiv K c) (Polynomial.degreeLTEquiv K h) ≪≫ₗ
    (LinearEquiv.sumArrowLequivProdArrow (Fin c) (Fin h) K K).symm

/-- The abstract mixed evaluation map is multiplication by the explicit
matrix in coefficient coordinates. -/
theorem mixedStackRelationMap_eq_matrix_comp
    (S : Finset K) (source target : K → K) (c h : ℕ) :
    mixedStackRelationMap S source target c h =
      (mixedStackMatrix S source target c h).mulVecLin.comp
        (mixedStackDomainEquiv c h).toLinearMap := by
  apply LinearMap.ext
  intro q
  funext x
  change q.1.1.eval x.1 * source x.1 +
      q.2.1.eval x.1 * target x.1 = _
  rw [Polynomial.eval_eq_sum_degreeLTEquiv q.1.2,
    Polynomial.eval_eq_sum_degreeLTEquiv q.2.2]
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, mixedStackDomainEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr,
    Fintype.sum_sum_type, mixedStackMatrix]
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro i hi <;>
    ring

/-- The transpose-kernel equation is exactly the two families of weighted
moment equations, one for each polynomial block. -/
theorem mixedStack_transpose_mulVec_eq_zero_iff_moments
    (S : Finset K) (source target : K → K) (c h : ℕ) (v : S → K) :
    (mixedStackMatrix S source target c h).transpose.mulVec v = 0 ↔
      (∀ i : Fin c,
        ∑ x : S, x.1 ^ (i : ℕ) * source x.1 * v x = 0) ∧
      (∀ i : Fin h,
        ∑ x : S, x.1 ^ (i : ℕ) * target x.1 * v x = 0) := by
  constructor
  · intro hv
    constructor
    · intro i
      have hi := congrFun hv (Sum.inl i)
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        mixedStackMatrix, Pi.zero_apply] using hi
    · intro i
      have hi := congrFun hv (Sum.inr i)
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        mixedStackMatrix, Pi.zero_apply] using hi
  · rintro ⟨hsource, htarget⟩
    funext i
    rcases i with i | i
    · simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        mixedStackMatrix, Pi.zero_apply] using hsource i
    · simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        mixedStackMatrix, Pi.zero_apply] using htarget i

/-- Nonzero moment data supplies the transpose-kernel hypothesis consumed by
the square-singularity bridge. -/
theorem mixedStack_transpose_ker_ne_bot_of_nonzero_moments
    (S : Finset K) (source target : K → K) (c h : ℕ) (v : S → K)
    (hv : v ≠ 0)
    (hsource : ∀ i : Fin c,
      ∑ x : S, x.1 ^ (i : ℕ) * source x.1 * v x = 0)
    (htarget : ∀ i : Fin h,
      ∑ x : S, x.1 ^ (i : ℕ) * target x.1 * v x = 0) :
    LinearMap.ker
      (mixedStackMatrix S source target c h).transpose.mulVecLin ≠ ⊥ := by
  have hvzero :
      (mixedStackMatrix S source target c h).transpose.mulVec v = 0 :=
    (mixedStack_transpose_mulVec_eq_zero_iff_moments
      S source target c h v).2 ⟨hsource, htarget⟩
  have hvker : v ∈ LinearMap.ker
      (mixedStackMatrix S source target c h).transpose.mulVecLin := hvzero
  intro hbot
  have : v ∈ (⊥ : Submodule K (S → K)) := by
    rw [← hbot]
    exact hvker
  exact hv (by simpa using this)

/-- For a matrix with equally many row and column coordinates, a nontrivial
right kernel for the transpose forces a nontrivial kernel for the original
matrix.  This is the rectangular-index form of “a square matrix is singular
on the right iff it is singular on the left.” -/
theorem matrix_ker_ne_bot_of_transpose_ker_ne_bot_of_card_eq
    {I J : Type} [Fintype I] [Fintype J]
    (M : Matrix J I K) (hcard : Fintype.card I = Fintype.card J)
    (htranspose : LinearMap.ker M.transpose.mulVecLin ≠ ⊥) :
    LinearMap.ker M.mulVecLin ≠ ⊥ := by
  intro hker
  have hinjective : Function.Injective M.mulVecLin :=
    LinearMap.ker_eq_bot.mp hker
  have hrankNullity := M.mulVecLin.finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card] at hrankNullity
  have hrank : M.rank = Fintype.card I := hrankNullity
  have hrankTranspose : M.transpose.rank = Fintype.card J := by
    rw [Matrix.rank_transpose, hrank, hcard]
  have hrankNullityTranspose :=
    M.transpose.mulVecLin.finrank_range_add_finrank_ker
  change M.transpose.rank +
      Module.finrank K (LinearMap.ker M.transpose.mulVecLin) =
        Module.finrank K (J → K) at hrankNullityTranspose
  rw [hrankTranspose,
    Module.finrank_fintype_fun_eq_card] at hrankNullityTranspose
  have hfinrank : Module.finrank K (LinearMap.ker M.transpose.mulVecLin) = 0 := by
    omega
  exact htranspose (Submodule.finrank_eq_zero.mp hfinrank)

/-- A nontrivial locator/syndrome right kernel for the square mixed source
matrix produces a nontrivial bounded polynomial relation. -/
theorem mixedStackRelationMap_ker_ne_bot_of_transpose_ker
    (S : Finset K) (source target : K → K) (c h : ℕ)
    (hcard : c + h = S.card)
    (htranspose : LinearMap.ker
      (mixedStackMatrix S source target c h).transpose.mulVecLin ≠ ⊥) :
    LinearMap.ker (mixedStackRelationMap S source target c h) ≠ ⊥ := by
  rw [mixedStackRelationMap_eq_matrix_comp]
  have hmatrix : LinearMap.ker
      (mixedStackMatrix S source target c h).mulVecLin ≠ ⊥ := by
    apply matrix_ker_ne_bot_of_transpose_ker_ne_bot_of_card_eq
      (mixedStackMatrix S source target c h)
    · simpa [MixedStackIndex, hcard]
    · exact htranspose
  intro hcomp
  apply hmatrix
  rw [LinearMap.ker_eq_bot] at hcomp ⊢
  intro a b hab
  apply (mixedStackDomainEquiv c h).symm.injective
  apply hcomp
  change (mixedStackMatrix S source target c h).mulVecLin
      ((mixedStackDomainEquiv c h) ((mixedStackDomainEquiv c h).symm a)) =
    (mixedStackMatrix S source target c h).mulVecLin
      ((mixedStackDomainEquiv c h) ((mixedStackDomainEquiv c h).symm b))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hab

/-- A mixed-stack relation with both multipliers separately nonzero. -/
structure MixedBoundedKernelRelation
    (S : Finset K) (source target : K → K) (c h : ℕ) where
  sourceMultiplier : K[X]
  targetMultiplier : K[X]
  sourceMultiplier_ne_zero : sourceMultiplier ≠ 0
  targetMultiplier_ne_zero : targetMultiplier ≠ 0
  sourceMultiplier_degree : sourceMultiplier.natDegree < c
  targetMultiplier_degree : targetMultiplier.natDegree < h
  relation : ∀ x ∈ S,
    sourceMultiplier.eval x * source x +
      targetMultiplier.eval x * target x = 0

/-- Extract the two nonzero multipliers.  Pointwise nonvanishing of both
source rows rules out a one-sided kernel relation by root counting. -/
noncomputable def mixedBoundedKernelRelation_of_ker_ne_bot
    (S : Finset K) (source target : K → K) (c h : ℕ)
    (hc : 0 < c) (hh : 0 < h)
    (hcS : c ≤ S.card) (hhS : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (htarget : ∀ x ∈ S, target x ≠ 0)
    (hker : LinearMap.ker (mixedStackRelationMap S source target c h) ≠ ⊥) :
    MixedBoundedKernelRelation S source target c h := by
  classical
  let hex := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let q := Classical.choose hex
  have hqspec := Classical.choose_spec hex
  have hqker : q ∈ LinearMap.ker (mixedStackRelationMap S source target c h) :=
    hqspec.1
  have hqne : q ≠ 0 := hqspec.2
  have hqrelation : ∀ x ∈ S,
      q.1.1.eval x * source x + q.2.1.eval x * target x = 0 := by
    intro x hx
    have hzero : mixedStackRelationMap S source target c h q = 0 := hqker
    have heval := congrFun hzero ⟨x, hx⟩
    simpa only [mixedStackRelationMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply] using heval
  have hAdegree : q.1.1.natDegree < c :=
    natDegree_lt_of_mem_degreeLT_of_pos c hc q.1
  have hBdegree : q.2.1.natDegree < h :=
    natDegree_lt_of_mem_degreeLT_of_pos h hh q.2
  have hAne : q.1.1 ≠ 0 := by
    intro hAzero
    have hBroot : ∀ x ∈ S, q.2.1.eval x = 0 := by
      intro x hx
      have hrel := hqrelation x hx
      rw [hAzero, Polynomial.eval_zero, zero_mul, zero_add] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right (htarget x hx)
    have hBzero : q.2.1 = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        q.2.1 S hBroot (hBdegree.trans_le hhS)
    apply hqne
    apply Prod.ext <;> apply Subtype.ext
    · exact hAzero
    · exact hBzero
  have hBne : q.2.1 ≠ 0 := by
    intro hBzero
    have hAroot : ∀ x ∈ S, q.1.1.eval x = 0 := by
      intro x hx
      have hrel := hqrelation x hx
      rw [hBzero, Polynomial.eval_zero, zero_mul, add_zero] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right (hsource x hx)
    have hAzero : q.1.1 = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        q.1.1 S hAroot (hAdegree.trans_le hcS)
    exact hAne hAzero
  exact
    { sourceMultiplier := q.1.1
      targetMultiplier := q.2.1
      sourceMultiplier_ne_zero := hAne
      targetMultiplier_ne_zero := hBne
      sourceMultiplier_degree := hAdegree
      targetMultiplier_degree := hBdegree
      relation := hqrelation }

/-- Cofactor degree descent turns a square mixed-stack singularity into the
smaller `2h` low-stack kernel used by the scroll argument.  The hypothesis
`hroot` is precisely the remaining bad-witness pointwise identity on its
source-agreement set `E`. -/
theorem lowStackRelationMap_ker_ne_bot_of_mixed_relation_and_cofactor
    (S E : Finset K) (source target : K → K) (c h : ℕ)
    (rel : MixedBoundedKernelRelation S source target c h)
    (C Cp : K[X])
    (hC : C ≠ 0) (hCp : Cp ≠ 0)
    (hcofactorDegree : Cp.natDegree = C.natDegree)
    (hhc : h ≤ c)
    (hcofactorRoom : C.natDegree + c < E.card)
    (hroot : ∀ x ∈ E,
      (rel.sourceMultiplier * C + rel.targetMultiplier * Cp).eval x = 0) :
    LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥ := by
  have hdescent := multiplier_degree_descent
    rel.sourceMultiplier rel.targetMultiplier C Cp E c h
    rel.sourceMultiplier_ne_zero rel.targetMultiplier_ne_zero hC hCp
    hcofactorDegree rel.sourceMultiplier_degree rel.targetMultiplier_degree
    hhc hcofactorRoom hroot
  have hAmem : rel.sourceMultiplier ∈ Polynomial.degreeLT K h := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.degree_eq_natDegree rel.sourceMultiplier_ne_zero]
    exact_mod_cast hdescent.2
  have hBmem : rel.targetMultiplier ∈ Polynomial.degreeLT K h := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.degree_eq_natDegree rel.targetMultiplier_ne_zero]
    exact_mod_cast rel.targetMultiplier_degree
  let q : (Polynomial.degreeLT K h) × (Polynomial.degreeLT K h) :=
    (⟨rel.sourceMultiplier, hAmem⟩, ⟨rel.targetMultiplier, hBmem⟩)
  have hqne : q ≠ 0 := by
    intro hzero
    have hleft := congrArg (fun r => r.1.1) hzero
    exact rel.sourceMultiplier_ne_zero hleft
  have hqker : q ∈ LinearMap.ker (lowStackRelationMap S source target h) := by
    change lowStackRelationMap S source target h q = 0
    funext x
    simpa only [lowStackRelationMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply, q] using rel.relation x.1 x.2
  intro hbot
  have : q ∈ (⊥ : Submodule K
      ((Polynomial.degreeLT K h) × (Polynomial.degreeLT K h))) := by
    rw [← hbot]
    exact hqker
  exact hqne (by simpa using this)

/-- Complete abstract bridge from a nonzero locator/syndrome right kernel to
the low-stack kernel, keeping the concrete syndrome construction as the only
upstream input. -/
theorem lowStackKernel_of_mixed_transpose_kernel
    (S E : Finset K) (source target : K → K) (c h : ℕ)
    (hc : 0 < c) (hh : 0 < h)
    (hcard : c + h = S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (htarget : ∀ x ∈ S, target x ≠ 0)
    (htranspose : LinearMap.ker
      (mixedStackMatrix S source target c h).transpose.mulVecLin ≠ ⊥)
    (C Cp : K[X])
    (hC : C ≠ 0) (hCp : Cp ≠ 0)
    (hcofactorDegree : Cp.natDegree = C.natDegree)
    (hhc : h ≤ c)
    (hcofactorRoom : C.natDegree + c < E.card)
    (hroot : ∀ x ∈ E,
      let rel := mixedBoundedKernelRelation_of_ker_ne_bot
        S source target c h hc hh
        (by omega : c ≤ S.card) (by omega : h ≤ S.card)
        hsource htarget
        (mixedStackRelationMap_ker_ne_bot_of_transpose_ker
          S source target c h hcard htranspose)
      (rel.sourceMultiplier * C + rel.targetMultiplier * Cp).eval x = 0) :
    LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥ := by
  let hmixed := mixedStackRelationMap_ker_ne_bot_of_transpose_ker
    S source target c h hcard htranspose
  let rel := mixedBoundedKernelRelation_of_ker_ne_bot
    S source target c h hc hh
    (by omega : c ≤ S.card) (by omega : h ≤ S.card)
    hsource htarget hmixed
  exact lowStackRelationMap_ker_ne_bot_of_mixed_relation_and_cofactor
    S E source target c h rel C Cp hC hCp hcofactorDegree hhc
    hcofactorRoom (by simpa [rel, hmixed] using hroot)

end ProximityPrize.SubmissionLower
