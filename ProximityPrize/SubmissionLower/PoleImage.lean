import ProximityPrize.SubmissionLower.PoleTruncation

namespace PoleImage

open PoleBlocks PoleFamily PoleTruncation MvPolynomial
open scoped BigOperators Matrix

noncomputable section

abbrev CutIdeal {R : Type*} [CommRing R] (x : R) (M : ℕ) : Ideal R :=
  Ideal.span {x^M}

/-- The passive polynomial construction as a linear map from source coefficients. -/
def passiveLinear {F : Type*} [Field F] {U B J : ℕ} (u : Fin (U+1)) :
    (Sigma (@Columns U B J) → F) →ₗ[F] MvPolynomial (Fin 4) F where
  toFun v := passivePolynomial v u
  map_add' v w := by
    unfold passivePolynomial
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases h : c.1.1 = u <;> simp [h, add_mul]
  map_smul' a v := by
    unfold passivePolynomial
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases h : c.1.1 = u <;> simp [h, Algebra.smul_def, mul_assoc]

/-- Evaluate the normalized polynomial slices, weight them, and reduce modulo
the cutoff power of the distinguished abscissa. -/
def postcompose {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R) (weight : Fin (U+1) → R) :
    (Sigma (@Columns U B J) → F) →ₗ[F] R ⧸ CutIdeal x (B+J) :=
  ∑ u, (Ideal.Quotient.mkₐ F (CutIdeal x (B+J))).toLinearMap.comp
    ((LinearMap.mulLeft F (weight u)).comp (ev.toLinearMap.comp (passiveLinear u)))

theorem postcompose_apply {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R) (weight : Fin (U+1) → R)
    (v : Sigma (@Columns U B J) → F) :
    postcompose U B J x ev weight v =
      Ideal.Quotient.mk (CutIdeal x (B+J)) (∑ u, weight u * ev (passivePolynomial v u)) := by
  simp [postcompose, passiveLinear, map_sum, Ideal.Quotient.mkₐ_eq_mk]

theorem ker_le_postcompose {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R) (weight : Fin (U+1) → R)
    (hx : ev (X (0 : Fin 4)) = x) :
    (matrix F U B J).mulVecLin.ker ≤ (postcompose U B J x ev weight).ker := by
  intro v hv
  change (matrix F U B J).mulVec v = 0 at hv
  rw [LinearMap.mem_ker, postcompose_apply, map_sum]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  obtain ⟨p, hp⟩ := X_pow_dvd_passivePolynomial v hv u
  have hcut : Ideal.Quotient.mk (CutIdeal x (B+J)) (x^(B+J)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have heval : ev (passivePolynomial v u) = x^(B+J) * ev p := by
    rw [hp, map_mul, map_pow, hx]
  rw [heval, map_mul, map_mul, hcut, zero_mul, mul_zero]

theorem postcompose_rank_le {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R) (weight : Fin (U+1) → R)
    (hx : ev (X (0 : Fin 4)) = x) :
    Module.finrank F (postcompose U B J x ev weight).range ≤ (matrix F U B J).rank := by
  classical
  let A := matrix F U B J
  let f := postcompose U B J x ev weight
  have hker : Module.finrank F A.mulVecLin.ker ≤ Module.finrank F f.ker :=
    Submodule.finrank_mono (ker_le_postcompose U B J x ev weight hx)
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hr : A.rank = Module.finrank F A.mulVecLin.range := by
    rw [A.rank_eq_finrank_range_toLin (Pi.basisFun F _) (Pi.basisFun F _),
      Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  change Module.finrank F f.range ≤ A.rank
  rw [hr]
  omega

theorem postcompose_rank_le_sum {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R) (weight : Fin (U+1) → R)
    (hx : ev (X (0 : Fin 4)) = x) :
    Module.finrank F (postcompose U B J x ev weight).range ≤
      ∑ u : Fin (U+1), ∑ n : Fin (B+(U-u.val)+1), ∑ h : Fin (B+2*J), blockBound ⟨u,n,h⟩ :=
  (postcompose_rank_le U B J x ev weight hx).trans (matrix_rank_le U B J)

end
end PoleImage
