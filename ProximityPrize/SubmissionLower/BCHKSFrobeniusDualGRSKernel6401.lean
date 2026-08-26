import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationKernelBridge6401

/-!
# Dual-GRS polynomialization of the full two-lane Hankel kernel

This is the concrete algebraic input behind the rank-failure branch.  It is
important that both lanes contain all `rows` moments.  A shortened square
minor containing only `t - rows` moments from the second lane does not imply
the second degree bound below.

For a right-kernel coefficient vector `v`, write `f = V v` for its values on
the support.  The two moment-kernel vectors are

`beta i * E i * f i` and `beta i * sigma (E i) * f i`.

Dual generalized Reed--Solomon interpolation represents each as the support
nodal weight times a polynomial of degree `< t - rows`.  The common factors
then cancel without division and give `TwoLaneFailureRelation`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusDualGRSKernel6401

open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusKeyEquationKernelBridge6401
open BCHKSGaoSpecializationCore6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-- Weighted evaluation of a degree-`< t-rows` polynomial.  Its range is the
dual GRS code annihilated by the first `rows` power moments. -/
noncomputable def dualGRSEvaluation
    {F : Type*} [Field F] {t : Nat}
    (alpha : Fin t ↪ F) (rows : Nat) :
    Polynomial.degreeLT F (t - rows) →ₗ[F] (Fin t → F) where
  toFun W i := syndromeWeight alpha i * W.1.eval (alpha i)
  map_add' W Q := by
    funext i
    simp [mul_add]
  map_smul' a W := by
    funext i
    simp [mul_assoc, mul_left_comm, mul_comm]

theorem dualGRSEvaluation_injective
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t) :
    Function.Injective (dualGRSEvaluation alpha rows) := by
  intro W Q hWQ
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := (Finset.univ : Finset (Fin t)))
      alpha.injective.injOn
  · rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.mem_degreeLT.mp W.2).trans_le
      (WithBot.coe_le_coe.mpr (Nat.sub_le t rows))
  · rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.mem_degreeLT.mp Q.2).trans_le
      (WithBot.coe_le_coe.mpr (Nat.sub_le t rows))
  · intro i _hi
    have hi := congrFun hWQ i
    exact mul_left_cancel₀ (syndromeWeight_ne_zero alpha i) hi

private theorem dualGRSEvaluation_range_le_momentKernel
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t) :
    LinearMap.range (dualGRSEvaluation alpha rows) ≤
      LinearMap.ker (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin := by
  intro p hp
  rcases hp with ⟨W, rfl⟩
  rw [LinearMap.mem_ker]
  funext j
  by_cases hW : W.1 = 0
  · simp [dualGRSEvaluation, hW, syndromeLeftVandermonde,
      Matrix.mulVec, dotProduct]
  · have hnW : W.1.natDegree < t - rows :=
      (Polynomial.natDegree_lt_iff_degree_lt hW).2
        (Polynomial.mem_degreeLT.mp W.2)
    have hdegree : W.1.natDegree + j.1 < t - 1 := by
      have hj := j.2
      omega
    have hz := weightedSyndrome_codeword_eq_zero alpha W.1 j.1 (by
      simpa only [Fintype.card_fin] using hdegree)
    simpa [weightedSyndrome, syndromeLeftVandermonde,
      dualGRSEvaluation, Matrix.mulVec, dotProduct,
      mul_assoc, mul_left_comm, mul_comm] using hz

theorem dualGRSEvaluation_range_eq_momentKernel
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t) :
    LinearMap.range (dualGRSEvaluation alpha rows) =
      LinearMap.ker (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin := by
  let H := syndromeLeftVandermonde (rows := rows) alpha
  have hHrank : H.rank = rows := by
    rw [show H = (Vandermonde.nonsquare rows alpha).transpose by rfl,
      Matrix.rank_transpose,
      Vandermonde.rank_nonsquare_rows_eq_min alpha.injective,
      Nat.min_eq_right hrows]
  have hnull := rank_add_finrank_ker_mulVecLin H
  have hkerdim :
      Module.finrank F (LinearMap.ker H.mulVecLin) = t - rows := by
    rw [hHrank] at hnull
    simp only [Fintype.card_fin] at hnull
    omega
  have hinj := dualGRSEvaluation_injective alpha hrows
  have hrangedim := LinearMap.finrank_range_of_inj hinj
  have hdomdim :
      Module.finrank F (Polynomial.degreeLT F (t - rows)) = t - rows := by
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis F (t - rows))]
    simp
  have hrangedim' :
      Module.finrank F (LinearMap.range (dualGRSEvaluation alpha rows)) =
        t - rows := by
    exact hrangedim.trans hdomdim
  apply Submodule.eq_of_le_of_finrank_eq
      (dualGRSEvaluation_range_le_momentKernel alpha hrows)
  simpa [H] using hrangedim'.trans hkerdim.symm

/-- The standard dual-GRS nullspace theorem, in the exact weighted form used
by the two-lane argument. -/
theorem exists_dualGRS_polynomial_of_moments
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t)
    (p : Fin t → F)
    (hp : (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin p = 0) :
    ∃ W : Polynomial.degreeLT F (t - rows),
      ∀ i, p i = syndromeWeight alpha i * W.1.eval (alpha i) := by
  have hmem : p ∈
      LinearMap.ker (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin :=
    LinearMap.mem_ker.mpr hp
  rw [← dualGRSEvaluation_range_eq_momentKernel alpha hrows] at hmem
  rcases hmem with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  intro i
  have hi := congrFun hW i
  simpa [dualGRSEvaluation] using hi.symm

/-- Both full Hankel lanes, stacked vertically.  Columns are the coefficients
of a polynomial of degree `< t`; each lane has all `rows` key-equation
moments. -/
def fullTwoLaneSupportKeyMatrix
    {F : Type*} [Field F] {t : Nat}
    (sigma : F →+* F) (rows : Nat) (alpha : Fin t → F)
    (beta E : Fin t → F) :
    Matrix (Fin rows ⊕ Fin rows) (Fin t) F
  | Sum.inl i, j =>
      supportSyndrome alpha (fun x => beta x * E x) (i.1 + j.1)
  | Sum.inr i, j =>
      supportSyndrome alpha (fun x => beta x * sigma (E x)) (i.1 + j.1)

private theorem fullTwoLane_left_kernel
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t → F) (beta E v : Fin t → F)
    (hv : (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin v = 0) :
    (supportSyndromeMatrix rows t alpha (fun i => beta i * E i)).mulVecLin v = 0 := by
  funext i
  have hi := congrFun hv (Sum.inl i)
  change (supportSyndromeMatrix rows t alpha
    (fun i => beta i * E i)).mulVec v i = 0 at hi
  exact hi

private theorem fullTwoLane_right_kernel
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t → F) (beta E v : Fin t → F)
    (hv : (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin v = 0) :
    (supportSyndromeMatrix rows t alpha
      (fun i => beta i * sigma (E i))).mulVecLin v = 0 := by
  funext i
  have hi := congrFun hv (Sum.inr i)
  change (supportSyndromeMatrix rows t alpha
    (fun i => beta i * sigma (E i))).mulVec v i = 0 at hi
  exact hi

noncomputable def supportCoefficientValues
    {F : Type*} [Field F] {t : Nat}
    (alpha : Fin t → F) (v : Fin t → F) : Fin t → F :=
  (syndromeRightVandermonde alpha).mulVec v

@[simp] theorem supportCoefficientValues_apply
    {F : Type*} [Field F] {t : Nat}
    (alpha : Fin t → F) (v : Fin t → F) (i : Fin t) :
    supportCoefficientValues alpha v i = ∑ j, alpha i ^ j.1 * v j := by
  rfl

private theorem lane_moment_kernel_of_hankel_kernel
    {F : Type*} [Field F] {t rows : Nat}
    (alpha d v : Fin t → F)
    (hv : (supportSyndromeMatrix rows t alpha d).mulVecLin v = 0) :
    (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin
      (fun i => d i * supportCoefficientValues alpha v i) = 0 := by
  have hfactor := supportSyndromeMatrix_factorization
    (rows := rows) alpha d
  have happ := congrArg (fun M : Matrix (Fin rows) (Fin t) F => M.mulVec v)
    hfactor
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at happ
  have hdiag :
      (Matrix.diagonal d).mulVec
          ((syndromeRightVandermonde alpha).mulVec v) =
        (fun i => d i * supportCoefficientValues alpha v i) := by
    funext i
    change (Matrix.diagonal d).mulVec
        ((syndromeRightVandermonde alpha).mulVec v) i =
      d i * (syndromeRightVandermonde alpha).mulVec v i
    exact Matrix.mulVec_diagonal d _ i
  rw [hdiag] at happ
  exact happ.symm.trans hv

/-- Concrete full-stack rank failure gives the two bounded polynomials and
their denominator-free cross-error relation.  The witness is ownerwise: both
`v` and the resulting pair may depend on the specialized error word. -/
theorem exists_failureRelation_of_fullTwoLane_rank_lt
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F) (beta E : Fin t → F)
    (hrows : rows ≤ t)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank : (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).rank < t) :
    ∃ W₀ W₁ : Polynomial F,
      W₀ ≠ 0 ∧
      W₀.degree < (t - rows : Nat) ∧
      W₁.degree < (t - rows : Nat) ∧
      TwoLaneFailureRelation sigma alpha E W₀ W₁ := by
  obtain ⟨v, hvne, hv⟩ :=
    exists_nonzero_mulVec_eq_zero_of_rank_lt_card
      (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E) (by
        simpa using hrank)
  let f := supportCoefficientValues alpha v
  let p₀ : Fin t → F := fun i => beta i * E i * f i
  let p₁ : Fin t → F := fun i => beta i * sigma (E i) * f i
  have hp₀ker :
      (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin p₀ = 0 := by
    apply lane_moment_kernel_of_hankel_kernel alpha
      (fun i => beta i * E i) v
    exact fullTwoLane_left_kernel sigma alpha beta E v hv
  have hp₁ker :
      (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin p₁ = 0 := by
    apply lane_moment_kernel_of_hankel_kernel alpha
      (fun i => beta i * sigma (E i)) v
    exact fullTwoLane_right_kernel sigma alpha beta E v hv
  obtain ⟨W₀, hW₀⟩ :=
    exists_dualGRS_polynomial_of_moments alpha hrows p₀ hp₀ker
  obtain ⟨W₁, hW₁⟩ :=
    exists_dualGRS_polynomial_of_moments alpha hrows p₁ hp₁ker
  have hfne : f ≠ 0 := by
    intro hfzero
    apply hvne
    apply Matrix.eq_zero_of_mulVec_eq_zero
      (Matrix.det_vandermonde_ne_zero_iff.mpr alpha.injective)
    change (Matrix.vandermonde alpha).mulVec v = 0
    change (syndromeRightVandermonde alpha).mulVec v = 0 at hfzero
    exact hfzero
  have hW₀ne : W₀.1 ≠ 0 := by
    intro hzero
    apply hfne
    funext i
    have hi := hW₀ i
    rw [hzero, Polynomial.eval_zero, mul_zero] at hi
    dsimp [p₀] at hi
    rcases mul_eq_zero.mp hi with hleft | hfi
    · rcases mul_eq_zero.mp hleft with hbi | hEi
      · exact (hbeta i hbi).elim
      · exact (hE i hEi).elim
    · exact hfi
  refine ⟨W₀.1, W₁.1, hW₀ne,
    Polynomial.mem_degreeLT.mp W₀.2,
    Polynomial.mem_degreeLT.mp W₁.2, ?_⟩
  intro i
  have h0 := hW₀ i
  have h1 := hW₁ i
  have hnu := syndromeWeight_ne_zero alpha i
  dsimp [p₀, p₁] at h0 h1
  apply mul_left_cancel₀ hnu
  calc
    syndromeWeight alpha i * (W₀.1.eval (alpha i) * sigma (E i)) =
        (syndromeWeight alpha i * W₀.1.eval (alpha i)) * sigma (E i) := by
          ring
    _ = (beta i * E i * f i) * sigma (E i) := by rw [← h0]
    _ = (beta i * sigma (E i) * f i) * E i := by ring
    _ = (syndromeWeight alpha i * W₁.1.eval (alpha i)) * E i := by rw [h1]
    _ = syndromeWeight alpha i * (W₁.1.eval (alpha i) * E i) := by ring

/-- Numerical specialization of the dual-GRS degree window. -/
theorem fullTwoLane_degree_window_exact6401 :
    keyErrors6401 - keyFirstLaneRows6401 = keySecondLaneRows6401 := by
  norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401,
    ownerDegreeCap6401, bchksErrors6401]

end BCHKSFrobeniusDualGRSKernel6401
end ProximityPrize.SubmissionLower
