import ProximityPrize.SubmissionLower.BCHKSPairSetup
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

theorem setup_selected_pair6399
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ 5279)
    (hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 13141403)
    (hRweightedX : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ 5279 ∧ H.natDegree ≤ 5279 ∧
    Polynomial.Bivariate.totalDegree H ≤ 13141402 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 13141402 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142) ∧
    RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
  have hRirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hHR).irreducible
  have hRdvd : R ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ
  have hHd : H ∣ triSpecializeX R x₀ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHR
  have hRdeg : R.natDegree ≤ 5279 :=
    (Polynomial.natDegree_le_of_dvd hRdvd hQ).trans hQY
  have hRXeq : triSpecializeX R x₀ =
      Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  have hRX0 : triSpecializeX R x₀ ≠ 0 := by
    rw [hRXeq]
    exact hprim.ne_zero
  have hHdeg : H.natDegree ≤ 5279 :=
    (Polynomial.natDegree_le_of_dvd hHd hRX0).trans
      ((triSpecializeX_natDegree_le R x₀).trans hRdeg)
  have hRXtotal : Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 13141402 := by
    have hlt := totalDegree_triSpecializeX_lt R x₀ 13141403 (by norm_num) hRYZ
    omega
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0) (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul hA hC]
    exact Nat.le_add_right _ _
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hHtotal : Polynomial.Bivariate.totalDegree H ≤ 13141402 :=
    (totalDegree_le_of_dvd hH0 hRX0 hHd).trans hRXtotal
  have hHyp : RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
    refine ⟨?_, hprim.ne_zero, ?_⟩
    · simpa [hRXeq] using hHd
    · intro Q hfac hQdeg
      let q₀ : Polynomial F := Q.coeff 0
      have hQC : Q = Polynomial.C q₀ :=
        Polynomial.eq_C_of_natDegree_le_zero hQdeg.le
      have hCdvd : Polynomial.C q₀ ∣
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
        refine ⟨H, ?_⟩
        calc
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R = H * Q := hfac
          _ = H * Polynomial.C q₀ := by rw [hQC]
          _ = Polynomial.C q₀ * H := mul_comm _ _
      exact (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim) q₀ hCdvd
  exact ⟨hRirr, hHirr, hHpos, hHd, hRdeg, hHdeg,
    hHtotal, hRXtotal, hRweightedX, hHyp⟩

/-- Concrete inheritance wrapper from the 63.99 interpolant to a selected pair. -/
theorem bchks_pair_setup6399_of_selected_factors
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ 5279)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 13141403)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ 5279 ∧ H.natDegree ≤ 5279 ∧
    Polynomial.Bivariate.totalDegree H ≤ 13141402 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 13141402 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142) ∧
    RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
  have hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 13141403 :=
    YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ hQYZ
  have hRweightedX : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142 :=
    WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R 131071 692001142 hQ hRQ hQweightedX
  exact setup_selected_pair6399 Q R H x₀ hQ hRQ hHR hHpos hQY hRYZ
    hRweightedX hprim

end ProximityPrize.SubmissionLower
