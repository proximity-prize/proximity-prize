import ProximityPrize.SubmissionLower.Koala6831MovingTransverse
import ProximityPrize.SubmissionLower.Koala6831MovingTransverseInverse
import ProximityPrize.SubmissionLower.Koala6831MovingTransverseSupport

namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

variable {K : Type*} [Field K]

namespace FlowData

variable (B : FlowData K)

def normalizedRoot : NormalizedCoeff K :=
  MvPolynomial.C (-(algebraMap (Polynomial K) (RatFunc K) B.a0) /
    algebraMap (Polynomial K) (RatFunc K) B.a1)

private theorem isUnit_xPolynomial {f : Polynomial K} (hf : f ≠ 0) :
    IsUnit (xPolynomial K f) := by
  have h : algebraMap (Polynomial K) (RatFunc K) f ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne hf
  exact (isUnit_iff_ne_zero.mpr h).map (algebraMap (RatFunc K) (NormalizedPoly K))

theorem normalizedAffine_eq_linear (ha1 : B.a1 ≠ 0) :
    normalizedAffine B.a0 B.a1 = xPolynomial K B.a1 * (Polynomial.X - Polynomial.C B.normalizedRoot) := by
  have hne : algebraMap (Polynomial K) (RatFunc K) B.a1 ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne ha1
  have he :
      algebraMap (Polynomial K) (RatFunc K) B.a1 *
          (-(algebraMap (Polynomial K) (RatFunc K) B.a0) /
            algebraMap (Polynomial K) (RatFunc K) B.a1) =
        -(algebraMap (Polynomial K) (RatFunc K) B.a0) := by
    field_simp
  have hroot :
      xPolynomial K B.a1 * Polynomial.C B.normalizedRoot = -xPolynomial K B.a0 := by
    simpa only [xPolynomial_apply, normalizedRoot, map_mul, map_neg] using
      congrArg (fun t : RatFunc K => Polynomial.C (MvPolynomial.C t : NormalizedCoeff K)) he
  unfold normalizedAffine
  linear_combination hroot

private theorem normalized_coeff_after_strip
    (n : ℕ) (c : NormalizedCoeff K) :
    ((Polynomial.X - Polynomial.C B.normalizedRoot)^n * Polynomial.C c).coeff n = c := by
  have hmonic := ((Polynomial.monic_X_sub_C B.normalizedRoot).pow n).coeff_natDegree
  have hone : ((Polynomial.X - Polynomial.C B.normalizedRoot)^n).coeff n = 1 := by
    simpa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] using hmonic
  simp only [Polynomial.coeff_mul_C, hone, one_mul]

theorem seed_independent_of_tangent
    {p : ℕ} [CharP K p] {F : P4 K}
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0) (hF : F ≠ 0)
    (hdegree : (B.normalize F).natDegree < p) (htangent : F ∣ B.flow F) :
    ∃ n : ℕ, ∃ c : NormalizedCoeff K,
      B.normalize F = (Polynomial.X - Polynomial.C B.normalizedRoot)^n * Polynomial.C c ∧
      c ≠ 0 ∧ (B.a1 = 0 → n = 0) ∧ c = (B.normalize F).coeff n := by
  have hnormal : B.normalize F ≠ 0 := by
    simpa only [map_zero] using (B.normalize_injective hd0 ha).ne hF
  have hdvd : B.normalize F ∣ (B.normalize B.denominator)^2 * (B.normalize F).derivative := by
    obtain ⟨W, hW⟩ := htangent
    refine ⟨B.normalize W, ?_⟩
    rw [← B.normalize_flow hd0, ← map_mul, hW]
  by_cases ha1 : B.a1 = 0
  · have ha0 : B.a0 ≠ 0 := by
      intro hz
      apply ha
      simp [A, affine, liftX, ha1, hz]
    have hd : B.normalize B.denominator = xPolynomial K B.d0 * xPolynomial K B.a0 := by
      simp [B.normalize_denominator, normalizedAffine, ha1]
    rw [hd] at hdvd
    have hu := ((isUnit_xPolynomial hd0).mul (isUnit_xPolynomial ha0)).pow 2
    have hC := eq_constant_of_dvd_derivative_of_degree_lt hdegree (hu.dvd_mul_left.mp hdvd)
    refine ⟨0, (B.normalize F).coeff 0, ?_, ?_, fun _ => rfl, rfl⟩
    · simpa only [pow_zero, one_mul] using hC
    · intro hz
      exact hnormal (by rw [hC, hz, map_zero])
  · have hd : (B.normalize B.denominator)^2 =
        (xPolynomial K B.d0 * xPolynomial K B.a1)^2 *
          (Polynomial.X - Polynomial.C B.normalizedRoot)^2 := by
      rw [B.normalize_denominator, B.normalizedAffine_eq_linear ha1, ← mul_assoc, mul_pow]
    rw [hd, mul_assoc] at hdvd
    have hu := ((isUnit_xPolynomial hd0).mul (isUnit_xPolynomial ha1)).pow 2
    obtain ⟨n, c, hC⟩ := pow_mul_constant_of_dvd_linear_sq_mul_derivative B.normalizedRoot hnormal
      hdegree (hu.dvd_mul_left.mp hdvd)
    refine ⟨n, c, hC, ?_, fun h => (ha1 h).elim, ?_⟩
    · intro hz
      exact hnormal (by rw [hC, hz, map_zero, mul_zero])
    · rw [hC, B.normalized_coeff_after_strip]

theorem transverse_or_seed_independent
    {p : ℕ} [CharP K p] {F : P4 K}
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0) (hF : F ≠ 0)
    (hdegree : F.weightedTotalDegree ![0, 1, 1, 1] < p) :
    (¬F ∣ B.flow F) ∨
      ∃ n : ℕ, ∃ c : NormalizedCoeff K,
        B.normalize F = (Polynomial.X - Polynomial.C B.normalizedRoot)^n * Polynomial.C c ∧
        c ≠ 0 ∧ (B.a1 = 0 → n = 0) ∧
        ∀ weights : Fin 2 → ℕ, weights 0 ≤ weights 1 →
          c.weightedTotalDegree weights ≤ F.weightedTotalDegree ![0, weights 0, weights 1, 0] := by
  by_cases htangent : F ∣ B.flow F
  · obtain ⟨n, c, hC, hc, hn, hcoeff⟩ := B.seed_independent_of_tangent hd0 ha hF
      ((B.normalize_natDegree_le F).trans_lt hdegree) htangent
    refine Or.inr ⟨n, c, hC, hc, hn, fun weights hweights => ?_⟩
    rw [hcoeff]
    exact B.normalize_coeff_weightedTotalDegree_le F weights hweights n
  · exact Or.inl htangent

end FlowData

end

end ProximityPrize.SubmissionLower.Koala6831Moving
