import ProximityPrize.SubmissionLower.BCHKSWeightedSelection
import ProximityPrize.SubmissionLower.BCHKSHenselSetup

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- The strict concrete interpolation `YZ` support cap survives specializing `X=x₀`. -/
theorem totalDegree_triSpecializeX_lt
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) (D : Nat)
    (hD : 0 < D)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D) :
    Polynomial.Bivariate.totalDegree (triSpecializeX Q x₀) < D := by
  unfold Polynomial.Bivariate.totalDegree
  rw [Finset.sup_lt_iff hD]
  intro j hj
  have hjne : (triSpecializeX Q x₀).coeff j ≠ 0 :=
    Polynomial.mem_support_iff.mp hj
  have hcoeff : (triSpecializeX Q x₀).coeff j =
      Polynomial.eval (Polynomial.C x₀) (Q.coeff j) := by
    simp [triSpecializeX]
  have ha : ∃ a, (Q.coeff j).coeff a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hjne
    rw [hcoeff]
    have hzero : Q.coeff j = 0 := by
      apply Polynomial.ext
      intro a
      exact hn a
    simp [hzero]
  obtain ⟨a₀, ha₀⟩ := ha
  have hjD : j < D := lt_of_le_of_lt (Nat.le_add_left j _ ) (hcap j a₀ ha₀)
  have hdeg : (Polynomial.eval (Polynomial.C x₀) (Q.coeff j)).natDegree ≤ D - 1 - j := by
    rw [Polynomial.eval_eq_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    have hca : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
    have hterm :
        (((Q.coeff j).coeff a) * (Polynomial.C x₀) ^ a).natDegree ≤
          ((Q.coeff j).coeff a).natDegree := by
      calc
        _ ≤ ((Q.coeff j).coeff a).natDegree + ((Polynomial.C x₀) ^ a).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ ((Q.coeff j).coeff a).natDegree + 0 := by
          apply Nat.add_le_add_left
          simp
        _ = _ := by omega
    exact hterm.trans (by have := hcap j a hca; omega)
  rw [hcoeff]
  omega

/-- Weak form retained for callers that only need a non-strict total-degree bound. -/
theorem totalDegree_triSpecializeX_le
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) (D : Nat)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D) :
    Polynomial.Bivariate.totalDegree (triSpecializeX Q x₀) ≤ D := by
  by_cases hD : 0 < D
  · exact (totalDegree_triSpecializeX_lt Q x₀ D hD hcap).le
  · have hDz : D = 0 := Nat.eq_zero_of_not_pos hD
    have hQz : Q = 0 := by
      apply Polynomial.ext
      intro j
      apply Polynomial.ext
      intro a
      by_contra ha
      have := hcap j a ha
      omega
    subst D
    simp [hQz, triSpecializeX, Polynomial.Bivariate.totalDegree]

/-- Package the algebraic and degree facts needed after weighted selection.
The weighted-`X` factor cap is explicit here; it is the remaining inheritance
lemma from divisibility of a trivariate factor.  Separability is likewise an
explicit good-`x₀` input. -/
theorem setup_selected_pair
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ 852)
    (hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 519143)
    (hRweightedX : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ 852 ∧ H.natDegree ≤ 852 ∧
    Polynomial.Bivariate.totalDegree H ≤ 519142 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 519142 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646) ∧
    RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
  have hRirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hHR).irreducible
  have hRdvd : R ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ
  have hHd : H ∣ triSpecializeX R x₀ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHR
  have hRdeg : R.natDegree ≤ 852 :=
    (Polynomial.natDegree_le_of_dvd hRdvd hQ).trans hQY
  have hRXeq : triSpecializeX R x₀ =
      Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  have hRX0 : triSpecializeX R x₀ ≠ 0 := by
    rw [hRXeq]
    exact hprim.ne_zero
  have hHdeg : H.natDegree ≤ 852 :=
    (Polynomial.natDegree_le_of_dvd hHd hRX0).trans
      ((triSpecializeX_natDegree_le R x₀).trans hRdeg)
  have hRXtotal : Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 519142 := by
    have hlt := totalDegree_triSpecializeX_lt R x₀ 519143 (by norm_num) hRYZ
    omega
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0) (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul hA hC]
    exact Nat.le_add_right _ _
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hHtotal : Polynomial.Bivariate.totalDegree H ≤ 519142 :=
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

end ProximityPrize.SubmissionLower
