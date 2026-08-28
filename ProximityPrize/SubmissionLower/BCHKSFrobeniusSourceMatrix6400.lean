import ProximityPrize.SubmissionLower.BCHKSFrobeniusLowStackKernel6400

/-!
# Explicit low-stack source matrix and pencil minors

This module gives the coefficient matrix underlying `lowStackRelationMap`.
Its column index is the disjoint union of the two degree-`<h` monomial
blocks.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators

variable {K : Type} [Field K]

abbrev LowStackIndex (h : ℕ) := Fin h ⊕ Fin h

/-- The explicit weighted two-block Vandermonde matrix. -/
def lowStackMatrix
    (S : Finset K) (source target : K → K) (h : ℕ) :
    Matrix S (LowStackIndex h) K
  | x, Sum.inl i => x.1 ^ (i : ℕ) * source x.1
  | x, Sum.inr i => x.1 ^ (i : ℕ) * target x.1

/-- Coefficient coordinates for the pair of degree-`<h` polynomial spaces. -/
noncomputable def lowStackDomainEquiv (h : ℕ) :
    ((Polynomial.degreeLT K h) × (Polynomial.degreeLT K h)) ≃ₗ[K]
      (LowStackIndex h → K) :=
  LinearEquiv.prodCongr
      (Polynomial.degreeLTEquiv K h) (Polynomial.degreeLTEquiv K h) ≪≫ₗ
    (LinearEquiv.sumArrowLequivProdArrow (Fin h) (Fin h) K K).symm

/-- The abstract evaluation map is the matrix multiplication map in
coefficient coordinates. -/
theorem lowStackRelationMap_eq_matrix_comp
    (S : Finset K) (source target : K → K) (h : ℕ) :
    lowStackRelationMap S source target h =
      (lowStackMatrix S source target h).mulVecLin.comp
        (lowStackDomainEquiv h).toLinearMap := by
  apply LinearMap.ext
  intro q
  funext x
  change q.1.1.eval x.1 * source x.1 +
      q.2.1.eval x.1 * target x.1 = _
  rw [Polynomial.eval_eq_sum_degreeLTEquiv q.1.2,
    Polynomial.eval_eq_sum_degreeLTEquiv q.2.2]
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, lowStackDomainEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr,
    Fintype.sum_sum_type, lowStackMatrix]
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro i hi <;>
    ring

/-- Nontrivial kernel is invariant under the coefficient-coordinate linear
equivalence. -/
theorem lowStackRelationMap_ker_ne_bot_iff_matrix
    (S : Finset K) (source target : K → K) (h : ℕ) :
    LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥ ↔
      LinearMap.ker (lowStackMatrix S source target h).mulVecLin ≠ ⊥ := by
  rw [lowStackRelationMap_eq_matrix_comp]
  change ¬LinearMap.ker
      ((lowStackMatrix S source target h).mulVecLin.comp
        (lowStackDomainEquiv h).toLinearMap) = ⊥ ↔
    ¬LinearMap.ker (lowStackMatrix S source target h).mulVecLin = ⊥
  rw [LinearMap.ker_eq_bot, LinearMap.ker_eq_bot]
  apply not_congr
  constructor
  · intro hcomp a b hab
    apply (lowStackDomainEquiv h).symm.injective
    apply hcomp
    change (lowStackMatrix S source target h).mulVecLin
        ((lowStackDomainEquiv h) ((lowStackDomainEquiv h).symm a)) =
      (lowStackMatrix S source target h).mulVecLin
        ((lowStackDomainEquiv h) ((lowStackDomainEquiv h).symm b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hab
  · intro hmatrix
    exact hmatrix.comp (lowStackDomainEquiv h).injective

/-- An injective rectangular matrix map contains a nonsingular square row
minor of full column size. -/
theorem exists_nonsingular_row_minor_of_mulVecLin_injective
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix J I K) (hinjective : Function.Injective M.mulVecLin) :
    ∃ e : I → J, Function.Injective e ∧
      (M.submatrix e id).det ≠ 0 := by
  classical
  have hker : LinearMap.ker M.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjective
  have hrankNullity := M.mulVecLin.finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card] at hrankNullity
  have hrank : M.rank = Fintype.card I := by
    exact hrankNullity
  have hspanrank :
      Module.finrank K (Submodule.span K (Set.range M.row)) =
        Fintype.card I := by
    rw [← M.rank_eq_finrank_span_row]
    exact hrank
  obtain ⟨t, htSubset, htCard, htSpan, htIndependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn
      K (Set.range M.row)
  have htCardI : t.card = Fintype.card I := by
    rw [htCard, hspanrank]
  let eIt : I ≃ t := Fintype.equivOfCardEq (by
    exact htCardI.symm.trans (Fintype.card_coe t).symm)
  have hrowExists (z : t) : ∃ j : J, M.row j = z.1 :=
    htSubset z.2
  let rowIndex (z : t) : J := Classical.choose (hrowExists z)
  have hrowIndex (z : t) : M.row (rowIndex z) = z.1 :=
    Classical.choose_spec (hrowExists z)
  have hrowIndexInjective : Function.Injective rowIndex := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = M.row (rowIndex a) := (hrowIndex a).symm
      _ = M.row (rowIndex b) := by rw [hab]
      _ = b.1 := hrowIndex b
  let e : I → J := rowIndex ∘ eIt
  have heInjective : Function.Injective e :=
    hrowIndexInjective.comp eIt.injective
  have htLinearIndependent :
      LinearIndependent K (fun z : t ↦ z.1) := by
    exact htIndependent
  have hselectedLinearIndependent :
      LinearIndependent K (fun i : I ↦ M.row (e i)) := by
    have hcomp := htLinearIndependent.comp eIt eIt.injective
    convert hcomp using 1
    funext i
    exact hrowIndex (eIt i)
  have hminorLinearIndependent :
      LinearIndependent K (M.submatrix e id).row := by
    change LinearIndependent K (fun i ↦ (M.submatrix e id) i)
    convert hselectedLinearIndependent using 1
    funext i j
    rfl
  refine ⟨e, heInjective, ?_⟩
  have hunit : IsUnit (M.submatrix e id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hminorLinearIndependent
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

/-- If every full-column row minor vanishes, the rectangular matrix has a
nontrivial kernel. -/
theorem matrix_ker_ne_bot_of_all_maximal_minors_zero
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix J I K)
    (hminor : ∀ e : I → J, Function.Injective e →
      (M.submatrix e id).det = 0) :
    LinearMap.ker M.mulVecLin ≠ ⊥ := by
  intro hker
  have hinjective : Function.Injective M.mulVecLin :=
    LinearMap.ker_eq_bot.mp hker
  obtain ⟨e, he, hdet⟩ :=
    exists_nonsingular_row_minor_of_mulVecLin_injective M hinjective
  exact hdet (hminor e he)

/-- A nontrivial kernel forces every square full-column row minor to vanish. -/
theorem all_maximal_minors_zero_of_matrix_ker_ne_bot
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix J I K) (hker : LinearMap.ker M.mulVecLin ≠ ⊥) :
    ∀ e : I → J, (M.submatrix e id).det = 0 := by
  classical
  intro e
  by_contra hdet
  have hsubInjective :
      Function.Injective (M.submatrix e id).mulVecLin := by
    change Function.Injective (M.submatrix e id).mulVec
    rw [Matrix.mulVec_injective_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hInjective : Function.Injective M.mulVecLin := by
    intro a b hab
    apply hsubInjective
    funext i
    have hi := congrFun hab (e i)
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec,
      Matrix.submatrix_apply, Function.comp_apply, id_eq] using hi
  exact hker (LinearMap.ker_eq_bot.mpr hInjective)

/-- Kernel deficiency of the abstract evaluation map forces all explicit
maximal source-matrix minors to vanish. -/
theorem all_lowStack_maximal_minors_zero_of_ker_ne_bot
    (S : Finset K) (source target : K → K) (h : ℕ)
    (hker : LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥) :
    ∀ e : LowStackIndex h → S,
      ((lowStackMatrix S source target h).submatrix e id).det = 0 := by
  rw [lowStackRelationMap_ker_ne_bot_iff_matrix] at hker
  exact all_maximal_minors_zero_of_matrix_ker_ne_bot
    (lowStackMatrix S source target h) hker

/-- Maximal-minor criterion directly for the polynomial evaluation map. -/
theorem lowStackRelationMap_ker_ne_bot_of_all_maximal_minors_zero
    (S : Finset K) (source target : K → K) (h : ℕ)
    (hminor : ∀ e : LowStackIndex h → S, Function.Injective e →
      ((lowStackMatrix S source target h).submatrix e id).det = 0) :
    LinearMap.ker (lowStackRelationMap S source target h) ≠ ⊥ := by
  rw [lowStackRelationMap_ker_ne_bot_iff_matrix]
  exact matrix_ker_ne_bot_of_all_maximal_minors_zero
    (lowStackMatrix S source target h) hminor

end ProximityPrize.SubmissionLower
