import ProximityPrize.SubmissionLower.BCHKSFrobeniusFailurePairRankOne6401

/-!
# The full-stack kernel as a linear space of bounded failure pairs

The existential dual-GRS witness is canonical because weighted evaluation is
an isomorphism onto the moment kernel.  This file retains the complete
column-kernel dimension: it builds an injective linear map from the full
two-lane Hankel kernel to pairs of degree-`< t-rows` polynomials.

Consequently a column nullity `delta` gives a `delta`-dimensional bounded
failure-pair space.  Together with the cross-determinant theorem this is the
precise module input for primitive-direction degree descent.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusKernelPairSpace6401

open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusKeyEquationKernelBridge6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusFailurePairRankOne6401

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

@[simp] theorem dualGRSEvaluation_apply
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (W : Polynomial.degreeLT F (t - rows))
    (i : Fin t) :
    dualGRSEvaluation alpha rows W i =
      syndromeWeight alpha i * W.1.eval (alpha i) := rfl

noncomputable def dualGRSKernelMap
    {F : Type*} [Field F] {t : Nat}
    (alpha : Fin t ↪ F) (rows : Nat) (hrows : rows ≤ t) :
    Polynomial.degreeLT F (t - rows) →ₗ[F]
      LinearMap.ker
        (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin :=
  LinearMap.codRestrict _ (dualGRSEvaluation alpha rows) (fun W => by
    have hmem : dualGRSEvaluation alpha rows W ∈
        LinearMap.range (dualGRSEvaluation alpha rows) := ⟨W, rfl⟩
    rwa [dualGRSEvaluation_range_eq_momentKernel alpha hrows] at hmem)

theorem dualGRSKernelMap_bijective
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t) :
    Function.Bijective (dualGRSKernelMap alpha rows hrows) := by
  constructor
  · intro W Q hWQ
    apply dualGRSEvaluation_injective alpha hrows
    exact congrArg Subtype.val hWQ
  · intro p
    have hp : p.1 ∈ LinearMap.range (dualGRSEvaluation alpha rows) := by
      rw [dualGRSEvaluation_range_eq_momentKernel alpha hrows]
      exact p.2
    rcases hp with ⟨W, hW⟩
    refine ⟨W, ?_⟩
    apply Subtype.ext
    exact hW

noncomputable def dualGRSKernelEquiv
    {F : Type*} [Field F] {t : Nat}
    (alpha : Fin t ↪ F) (rows : Nat) (hrows : rows ≤ t) :
    Polynomial.degreeLT F (t - rows) ≃ₗ[F]
      LinearMap.ker
        (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin :=
  LinearEquiv.ofBijective (dualGRSKernelMap alpha rows hrows)
    (dualGRSKernelMap_bijective alpha hrows)

@[simp] theorem dualGRSKernelEquiv_apply_val
    {F : Type*} [Field F] {t rows : Nat}
    (alpha : Fin t ↪ F) (hrows : rows ≤ t)
    (W : Polynomial.degreeLT F (t - rows)) :
    (dualGRSKernelEquiv alpha rows hrows W).1 =
      dualGRSEvaluation alpha rows W := rfl

noncomputable def coefficientValueLinear
    {F : Type*} [Field F] {t : Nat} (alpha : Fin t → F) :
    (Fin t → F) →ₗ[F] (Fin t → F) :=
  (syndromeRightVandermonde alpha).mulVecLin

noncomputable def weightedCoefficientValueLinear
    {F : Type*} [Field F] {t : Nat} (alpha d : Fin t → F) :
    (Fin t → F) →ₗ[F] (Fin t → F) :=
  (Matrix.diagonal d).mulVecLin.comp (coefficientValueLinear alpha)

@[simp] theorem weightedCoefficientValueLinear_apply
    {F : Type*} [Field F] {t : Nat} (alpha d v : Fin t → F) (i : Fin t) :
    weightedCoefficientValueLinear alpha d v i =
      d i * supportCoefficientValues alpha v i := by
  simp [weightedCoefficientValueLinear, coefficientValueLinear,
    supportCoefficientValues, Matrix.mulVec_diagonal]

private theorem weightedCoefficientValue_mem_momentKernel
    {F : Type*} [Field F] {t rows : Nat}
    (alpha d v : Fin t → F)
    (hv : (supportSyndromeMatrix rows t alpha d).mulVecLin v = 0) :
    weightedCoefficientValueLinear alpha d v ∈
      LinearMap.ker
        (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin := by
  rw [LinearMap.mem_ker]
  have hfactor := supportSyndromeMatrix_factorization
    (rows := rows) alpha d
  have happ := congrArg (fun M : Matrix (Fin rows) (Fin t) F => M.mulVec v)
    hfactor
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at happ
  change (syndromeLeftVandermonde alpha).mulVec
    ((Matrix.diagonal d).mulVec
      ((syndromeRightVandermonde alpha).mulVec v)) = 0
  exact happ.symm.trans hv

noncomputable def fullKernelLaneMap
    {F : Type*} [Field F] {t : Nat}
    (sigma : F →+* F) (alpha : Fin t → F) (rows : Nat)
    (beta E d : Fin t → F)
    (hd : d = fun i => beta i * E i) :
    LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin →ₗ[F]
      LinearMap.ker
        (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin where
  toFun v := ⟨weightedCoefficientValueLinear alpha d v.1, by
    apply weightedCoefficientValue_mem_momentKernel alpha d v.1
    funext i
    have hi := congrFun (LinearMap.mem_ker.mp v.2) (Sum.inl i)
    subst d
    change (supportSyndromeMatrix rows t alpha
      (fun i => beta i * E i)).mulVec v.1 i = 0 at hi
    exact hi⟩
  map_add' v w := by
    apply Subtype.ext
    exact map_add (weightedCoefficientValueLinear alpha d) v.1 w.1
  map_smul' a v := by
    apply Subtype.ext
    exact map_smul (weightedCoefficientValueLinear alpha d) a v.1

noncomputable def fullKernelFrobeniusLaneMap
    {F : Type*} [Field F] {t : Nat}
    (sigma : F →+* F) (alpha : Fin t → F) (rows : Nat)
    (beta E : Fin t → F) :
    LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin →ₗ[F]
      LinearMap.ker
        (syndromeLeftVandermonde (rows := rows) alpha).mulVecLin where
  toFun v := ⟨weightedCoefficientValueLinear alpha
      (fun i => beta i * sigma (E i)) v.1, by
    apply weightedCoefficientValue_mem_momentKernel alpha
      (fun i => beta i * sigma (E i)) v.1
    funext i
    have hi := congrFun (LinearMap.mem_ker.mp v.2) (Sum.inr i)
    change (supportSyndromeMatrix rows t alpha
      (fun i => beta i * sigma (E i))).mulVec v.1 i = 0 at hi
    exact hi⟩
  map_add' v w := by
    apply Subtype.ext
    exact map_add
      (weightedCoefficientValueLinear alpha (fun i => beta i * sigma (E i)))
      v.1 w.1
  map_smul' a v := by
    apply Subtype.ext
    exact map_smul
      (weightedCoefficientValueLinear alpha (fun i => beta i * sigma (E i)))
      a v.1

/-- Canonical linear polynomialization of every full-stack kernel vector. -/
noncomputable def fullKernelFailurePairLinear
    {F : Type*} [Field F] {t : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F) (rows : Nat)
    (hrows : rows ≤ t) (beta E : Fin t → F) :
    LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin →ₗ[F]
      (Polynomial.degreeLT F (t - rows) ×
        Polynomial.degreeLT F (t - rows)) :=
  ((dualGRSKernelEquiv alpha rows hrows).symm.toLinearMap.comp
      (fullKernelLaneMap sigma alpha rows beta E
        (fun i => beta i * E i) rfl)).prod
    ((dualGRSKernelEquiv alpha rows hrows).symm.toLinearMap.comp
      (fullKernelFrobeniusLaneMap sigma alpha rows beta E))

theorem fullKernelFailurePairLinear_injective
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F)
    (hrows : rows ≤ t) (beta E : Fin t → F)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0) :
    Function.Injective
      (fullKernelFailurePairLinear sigma alpha rows hrows beta E) := by
  intro v w hvw
  apply Subtype.ext
  have hfirst := congrArg Prod.fst hvw
  have hlane :
      fullKernelLaneMap sigma alpha rows beta E
          (fun i => beta i * E i) rfl v =
        fullKernelLaneMap sigma alpha rows beta E
          (fun i => beta i * E i) rfl w := by
    apply (dualGRSKernelEquiv alpha rows hrows).symm.injective
    exact hfirst
  have hp := congrArg Subtype.val hlane
  change weightedCoefficientValueLinear alpha (fun i => beta i * E i) v.1 =
    weightedCoefficientValueLinear alpha (fun i => beta i * E i) w.1 at hp
  have hvalues : coefficientValueLinear alpha v.1 =
      coefficientValueLinear alpha w.1 := by
    funext i
    have hi := congrFun hp i
    rw [weightedCoefficientValueLinear_apply,
      weightedCoefficientValueLinear_apply] at hi
    exact mul_left_cancel₀ (mul_ne_zero (hbeta i) (hE i)) hi
  have hdiff : v.1 - w.1 = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero
        (Matrix.det_vandermonde_ne_zero_iff.mpr alpha.injective)
    rw [Matrix.mulVec_sub]
    apply sub_eq_zero.mpr
    change coefficientValueLinear alpha v.1 =
      coefficientValueLinear alpha w.1 at hvalues
    exact hvalues
  exact sub_eq_zero.mp hdiff

/-- Every canonical pair satisfies the same denominator-free cross-error
relation.  The construction is linear in the full-stack kernel vector. -/
theorem fullKernelFailurePairLinear_relation
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F)
    (hrows : rows ≤ t) (beta E : Fin t → F)
    (v : LinearMap.ker
      (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) :
    TwoLaneFailureRelation sigma alpha E
      (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1.1
      (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2.1 := by
  have he₀ :
      dualGRSEvaluation alpha rows
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1 =
        weightedCoefficientValueLinear alpha (fun i => beta i * E i) v.1 := by
    have h := congrArg Subtype.val
      ((dualGRSKernelEquiv alpha rows hrows).apply_symm_apply
        (fullKernelLaneMap sigma alpha rows beta E
          (fun i => beta i * E i) rfl v))
    change dualGRSEvaluation alpha rows
        (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1 =
      weightedCoefficientValueLinear alpha (fun i => beta i * E i) v.1 at h
    exact h
  have he₁ :
      dualGRSEvaluation alpha rows
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2 =
        weightedCoefficientValueLinear alpha
          (fun i => beta i * sigma (E i)) v.1 := by
    have h := congrArg Subtype.val
      ((dualGRSKernelEquiv alpha rows hrows).apply_symm_apply
        (fullKernelFrobeniusLaneMap sigma alpha rows beta E v))
    change dualGRSEvaluation alpha rows
        (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2 =
      weightedCoefficientValueLinear alpha
        (fun i => beta i * sigma (E i)) v.1 at h
    exact h
  intro i
  have h₀ := congrFun he₀ i
  have h₁ := congrFun he₁ i
  rw [dualGRSEvaluation_apply] at h₀ h₁
  rw [weightedCoefficientValueLinear_apply] at h₀ h₁
  have h₀' : syndromeWeight alpha i *
      (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1.1.eval
        (alpha i) =
      beta i * E i * supportCoefficientValues alpha v.1 i := by
    simpa only using h₀
  have h₁' : syndromeWeight alpha i *
      (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2.1.eval
        (alpha i) =
      beta i * sigma (E i) * supportCoefficientValues alpha v.1 i := by
    simpa only using h₁
  have hnu := syndromeWeight_ne_zero alpha i
  apply mul_left_cancel₀ hnu
  calc
    syndromeWeight alpha i *
        ((fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1.1.eval
          (alpha i) * sigma (E i)) =
      (syndromeWeight alpha i *
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1.1.eval
            (alpha i)) * sigma (E i) := by ring
    _ = (beta i * E i * supportCoefficientValues alpha v.1 i) *
          sigma (E i) := by rw [h₀']
    _ = (beta i * sigma (E i) * supportCoefficientValues alpha v.1 i) *
          E i := by ring
    _ = (syndromeWeight alpha i *
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2.1.eval
          (alpha i)) * E i := by rw [h₁']
    _ = syndromeWeight alpha i *
        ((fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2.1.eval
          (alpha i) * E i) := by ring

/-- The polynomialized failure-pair space has exactly the full-stack column
nullity. -/
theorem fullKernelFailurePair_range_finrank
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F)
    (hrows : rows ≤ t) (beta E : Fin t → F)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0) :
    Module.finrank F
        (LinearMap.range
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E)) =
      Module.finrank F
        (LinearMap.ker
          (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) := by
  exact LinearMap.finrank_range_of_inj
    (fullKernelFailurePairLinear_injective sigma alpha hrows beta E hbeta hE)

end BCHKSFrobeniusKernelPairSpace6401
end ProximityPrize.SubmissionLower
