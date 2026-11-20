import ProximityPrize.SubmissionLower.Koala6831MovingTransverseChange


namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

variable {K : Type*} [Field K]

abbrev SourceFraction (K : Type*) [Field K] := FractionRing (P4 K)

private abbrev sourceEmbed (K : Type*) [Field K] : P4 K →ₐ[K] SourceFraction K :=
  IsScalarTower.toAlgHom K (P4 K) (SourceFraction K)

private theorem liftX_injective : Function.Injective (liftX (K := K)) := by
  let evaluate : P4 K →ₐ[K] Polynomial K := MvPolynomial.aeval ![Polynomial.X, 0, 0, 0]
  have hmap : evaluate.comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) =
      AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    simp [evaluate, AlgHom.comp_apply]
  have hleft : Function.LeftInverse evaluate (liftX (K := K)) :=
    fun f => DFunLike.congr_fun hmap f
  exact hleft.injective

private def liftXFraction (K : Type*) [Field K] : Polynomial K →ₐ[K] SourceFraction K :=
  (sourceEmbed K).comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)))

private def liftXRational (K : Type*) [Field K] : RatFunc K →ₐ[K] SourceFraction K :=
  IsFractionRing.liftAlgHom (g := liftXFraction K)
    ((IsFractionRing.injective (P4 K) (SourceFraction K)).comp (liftX_injective (K := K)))

private theorem liftXRational_apply (f : Polynomial K) :
    liftXRational K (algebraMap (Polynomial K) (RatFunc K) f) = sourceEmbed K (liftX f) := by
  simp only [liftXRational, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap,
    liftXFraction, liftX]
  rfl

namespace FlowData

variable (B : FlowData K)

private def recoverCoeff : NormalizedCoeff K →ₐ[K] SourceFraction K :=
  MvPolynomial.aevalTower (liftXRational K)
    ![sourceEmbed K B.numerator / sourceEmbed K B.A,
      sourceEmbed K B.jetNumerator / (sourceEmbed K B.A)^2]

private def recover : NormalizedPoly K →ₐ[K] SourceFraction K :=
  Polynomial.aevalTower B.recoverCoeff (sourceEmbed K (MvPolynomial.X (3 : Fin 4)))

private theorem recover_xPolynomial (f : Polynomial K) :
    B.recover (xPolynomial K f) = sourceEmbed K (liftX f) := by
  rw [xPolynomial_apply, recover, Polynomial.aevalTower_C, recoverCoeff, MvPolynomial.aevalTower_C,
    liftXRational_apply]

private theorem recover_affine (f₀ f₁ : Polynomial K) :
    B.recover (normalizedAffine f₀ f₁) = sourceEmbed K (affine f₀ f₁) := by
  simp only [normalizedAffine, map_add, map_mul, affine, recover_xPolynomial]
  rw [recover, Polynomial.aevalTower_X]

private theorem recover_value :
    B.recover (normalizedValue K) = sourceEmbed K B.numerator / sourceEmbed K B.A := by
  simp [normalizedValue, recover, recoverCoeff]

private theorem recover_firstJet :
    B.recover (normalizedFirstJet K) = sourceEmbed K B.jetNumerator / (sourceEmbed K B.A)^2 := by
  simp [normalizedFirstJet, recover, recoverCoeff]

private theorem embed_ne_zero {F : P4 K} (hF : F ≠ 0) : sourceEmbed K F ≠ 0 := by
  change (algebraMap (P4 K) (SourceFraction K)) F ≠ 0
  simpa only [map_zero] using (IsFractionRing.injective (P4 K) (SourceFraction K)).ne hF

private theorem recover_normalizedY (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0) :
    B.recover B.normalizedY = sourceEmbed K (MvPolynomial.X (1 : Fin 4)) := by
  have hinv := B.d0_mul_normalizedInvD0 hd0
  have hy :
      xPolynomial K B.d0 * B.normalizedY =
        normalizedAffine B.a0 B.a1 * normalizedValue K - normalizedAffine B.c0 B.c1 := by
    simp only [normalizedY, ← mul_assoc, hinv, one_mul]
  have hy' := congrArg B.recover hy
  simp only [map_mul, map_sub, recover_xPolynomial, recover_affine, recover_value] at hy'
  have hd : sourceEmbed K (liftX B.d0) ≠ 0 :=
    embed_ne_zero (by simpa only [liftX, map_zero] using liftX_injective.ne hd0)
  apply mul_left_cancel₀ hd
  rw [hy']
  have ha' := embed_ne_zero ha
  change sourceEmbed K B.A * (sourceEmbed K B.numerator / sourceEmbed K B.A) -
    sourceEmbed K B.C = _
  field_simp
  simp [numerator]

private theorem recover_normalizedR (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0) :
    B.recover B.normalizedR = sourceEmbed K (MvPolynomial.X (2 : Fin 4)) := by
  have hinv := B.d0_mul_normalizedInvD0 hd0
  have hr :
      xPolynomial K B.d0 * B.normalizedR =
        normalizedAffine B.a0 B.a1 * normalizedFirstJet K +
          normalizedAffine B.a0.derivative B.a1.derivative * normalizedValue K -
          normalizedAffine B.c0.derivative B.c1.derivative -
          xPolynomial K B.d0.derivative * B.normalizedY := by
    simp only [normalizedR, ← mul_assoc, hinv, one_mul]
  have hr' := congrArg B.recover hr
  simp only [map_mul, map_add, map_sub, recover_xPolynomial, recover_affine, recover_value,
    recover_firstJet, B.recover_normalizedY hd0 ha] at hr'
  have hd : sourceEmbed K (liftX B.d0) ≠ 0 :=
    embed_ne_zero (by simpa only [liftX, map_zero] using liftX_injective.ne hd0)
  apply mul_left_cancel₀ hd
  rw [hr']
  have ha' := embed_ne_zero ha
  change sourceEmbed K B.A *
      (sourceEmbed K B.jetNumerator / (sourceEmbed K B.A)^2) +
    sourceEmbed K B.AX * (sourceEmbed K B.numerator / sourceEmbed K B.A) -
    sourceEmbed K B.CX - sourceEmbed K (liftX B.d0.derivative) *
      sourceEmbed K (MvPolynomial.X (1 : Fin 4)) = _
  simp only [jetNumerator, map_mul, map_sub, map_add]
  field_simp
  ring

theorem normalize_injective (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0) :
    Function.Injective B.normalize := by
  have h : B.recover.comp B.normalize = sourceEmbed K := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [AlgHom.comp_apply, normalize_variable, normalizedCoordinates, recover_xPolynomial, liftX]
    · simp [AlgHom.comp_apply, normalize_variable, normalizedCoordinates, recover_normalizedY B hd0 ha]
    · simp [AlgHom.comp_apply, normalize_variable, normalizedCoordinates, recover_normalizedR B hd0 ha]
    · simp [AlgHom.comp_apply, normalize_variable, normalizedCoordinates, recover]
  intro F G hFG
  apply IsFractionRing.injective (P4 K) (SourceFraction K)
  have hrec := congrArg B.recover hFG
  change (B.recover.comp B.normalize) F = (B.recover.comp B.normalize) G at hrec
  rw [h] at hrec
  exact hrec

end FlowData

end

end ProximityPrize.SubmissionLower.Koala6831Moving
