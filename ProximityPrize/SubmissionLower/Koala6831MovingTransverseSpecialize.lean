import ProximityPrize.SubmissionLower.Koala6831MovingTransverseClassify

namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

variable {K : Type*} [Field K]

private abbrev embedPolynomial (K : Type*) [Field K] : Polynomial K →ₐ[K] RatFunc K :=
  IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)

def evalNormalizedCoefficient (q : Polynomial K) : NormalizedCoeff K →ₐ[K] RatFunc K :=
  MvPolynomial.aevalTower (IsScalarTower.toAlgHom K (RatFunc K) (RatFunc K))
    ![embedPolynomial K q, embedPolynomial K q.derivative]

private def evalNormalized (q : Polynomial K) (g : K) : NormalizedPoly K →ₐ[K] RatFunc K :=
  Polynomial.aevalTower (evalNormalizedCoefficient q) (algebraMap K (RatFunc K) g)

private theorem evalNormalized_seed (q : Polynomial K) (g : K) :
    evalNormalized q g Polynomial.X = algebraMap K (RatFunc K) g := by
  simp [evalNormalized]

private theorem embedPolynomial_constant (g : K) :
    embedPolynomial K (Polynomial.C g) = algebraMap K (RatFunc K) g :=
  (embedPolynomial K).commutes g

private theorem evalNormalized_xPolynomial (q : Polynomial K) (g : K) (f : Polynomial K) :
    evalNormalized q g (xPolynomial K f) = embedPolynomial K f := by
  simp [evalNormalized, evalNormalizedCoefficient, xPolynomial_apply]

private theorem evalNormalized_affine (q : Polynomial K) (g : K) (f₀ f₁ : Polynomial K) :
    evalNormalized q g (normalizedAffine f₀ f₁) = embedPolynomial K (f₀ + Polynomial.C g * f₁) := by
  simp only [normalizedAffine, map_add, map_mul, evalNormalized_xPolynomial, evalNormalized_seed,
    embedPolynomial_constant]

private theorem evalNormalized_value (q : Polynomial K) (g : K) :
    evalNormalized q g (normalizedValue K) = embedPolynomial K q := by
  simp [evalNormalized, evalNormalizedCoefficient, normalizedValue]

private theorem evalNormalized_firstJet (q : Polynomial K) (g : K) :
    evalNormalized q g (normalizedFirstJet K) = embedPolynomial K q.derivative := by
  simp [evalNormalized, evalNormalizedCoefficient, normalizedFirstJet]

private theorem embedPolynomial_ne_zero {f : Polynomial K} (hf : f ≠ 0) :
    embedPolynomial K f ≠ 0 := by
  change algebraMap (Polynomial K) (RatFunc K) f ≠ 0
  simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne hf

namespace FlowData

variable (B : FlowData K)

private theorem evalNormalized_invD0 (q : Polynomial K) (g : K) :
    evalNormalized q g B.normalizedInvD0 = (embedPolynomial K B.d0)⁻¹ := by
  change evalNormalized q g
    (Polynomial.C (MvPolynomial.C ((algebraMap (Polynomial K) (RatFunc K) B.d0)⁻¹))) = _
  simp [evalNormalized, evalNormalizedCoefficient]

private theorem evalNormalized_Y (g : K) {f q : Polynomial K}
    (hd0 : B.d0 ≠ 0)
    (hnorm : B.d0 * f + (B.c0 + Polynomial.C g * B.c1) =
      (B.a0 + Polynomial.C g * B.a1) * q) :
    evalNormalized q g B.normalizedY = embedPolynomial K f := by
  have hd := embedPolynomial_ne_zero hd0
  have hh := congrArg (embedPolynomial K) hnorm
  simp only [map_add, map_mul] at hh
  simp only [normalizedY, map_mul, map_sub, B.evalNormalized_invD0, evalNormalized_affine,
    evalNormalized_value]
  apply mul_left_cancel₀ hd
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  simp only [map_add, map_mul]
  linear_combination -hh

private theorem evalNormalized_R (g : K) {f q : Polynomial K}
    (hd0 : B.d0 ≠ 0)
    (hnorm : B.d0 * f + (B.c0 + Polynomial.C g * B.c1) =
      (B.a0 + Polynomial.C g * B.a1) * q) :
    evalNormalized q g B.normalizedR = embedPolynomial K f.derivative := by
  have hd := embedPolynomial_ne_zero hd0
  have hderiv := congrArg Polynomial.derivative hnorm
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add] at hderiv
  have hh := congrArg (embedPolynomial K) hderiv
  simp only [map_add, map_mul] at hh
  simp only [normalizedR, map_add, map_mul, map_sub, B.evalNormalized_invD0,
    evalNormalized_affine, evalNormalized_firstJet, evalNormalized_value,
    evalNormalized_xPolynomial, B.evalNormalized_Y g hd0 hnorm]
  apply mul_left_cancel₀ hd
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  linear_combination -hh

private theorem eval_normalize (g : K) {f q : Polynomial K}
    (hd0 : B.d0 ≠ 0)
    (hnorm : B.d0 * f + (B.c0 + Polynomial.C g * B.c1) =
      (B.a0 + Polynomial.C g * B.a1) * q) (F : P4 K) :
    evalNormalized q g (B.normalize F) = embedPolynomial K (RCN319.specialization K f g F) := by
  have h : (evalNormalized q g).comp B.normalize =
      (embedPolynomial K).comp (RCN319.specialization K f g) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [AlgHom.comp_apply, B.normalize_variable, normalizedCoordinates, RCN319.specialization,
        evalNormalized_xPolynomial, evalNormalized_seed, B.evalNormalized_Y g hd0 hnorm,
        B.evalNormalized_R g hd0 hnorm, embedPolynomial_constant]
  exact DFunLike.congr_fun h F

theorem seed_independent_specializes
    (g : K) {f q : Polynomial K} {F : P4 K} {n : ℕ} {c : NormalizedCoeff K}
    (hd0 : B.d0 ≠ 0) (ha : B.a0 + Polynomial.C g * B.a1 ≠ 0)
    (hnorm : B.d0 * f + (B.c0 + Polynomial.C g * B.c1) =
      (B.a0 + Polynomial.C g * B.a1) * q)
    (hform : B.normalize F = (Polynomial.X - Polynomial.C B.normalizedRoot)^n * Polynomial.C c)
    (hconstant : B.a1 = 0 → n = 0)
    (hF : RCN319.specialization K f g F = 0) :
    evalNormalizedCoefficient q c = 0 := by
  have hvanish := B.eval_normalize g hd0 hnorm F
  rw [hF, hform, map_zero, map_mul] at hvanish
  have hscale :
      evalNormalized q g ((Polynomial.X - Polynomial.C B.normalizedRoot)^n) ≠ 0 := by
    by_cases ha1 : B.a1 = 0
    · simp [hconstant ha1]
    · rw [map_pow]
      apply pow_ne_zero
      intro hz
      have hh := congrArg (evalNormalized q g) (B.normalizedAffine_eq_linear ha1)
      rw [evalNormalized_affine, map_mul, hz, mul_zero] at hh
      exact embedPolynomial_ne_zero ha hh
  have hzero := (mul_eq_zero.mp hvanish).resolve_left hscale
  simpa only [evalNormalized, Polynomial.aevalTower_C] using hzero

end FlowData

end

end ProximityPrize.SubmissionLower.Koala6831Moving
