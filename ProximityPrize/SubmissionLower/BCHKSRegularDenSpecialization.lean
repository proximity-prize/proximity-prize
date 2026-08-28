import ProximityPrize.SubmissionLower.BCHKSFiniteLiftExact
import ProximityPrize.SubmissionLower.BCHKSPairLiftRegularDen

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]


/-- Actual regular denominator, repeated here so this bridge remains usable
independently of the evolving exact-lift packaging module. -/
noncomputable def concreteDenRegularBridge
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H) (t : ℕ) : 𝒪 H :=
  (Ideal.Quotient.mk (Ideal.span {monicize H})
      (Polynomial.C H.leadingCoeff) : 𝒪 H) ^ (t + 1) *
    (HenselNumerators.xi x₀ R H hHyp) ^ FiniteHenselWeight.denominatorExponent t

lemma embedding_concreteDenRegularBridge
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (concreteDenRegularBridge x₀ R hHyp t) =
      Wfield (H := H) ^ (t + 1) * etaField (R := R) (H := H) x₀ hHyp ^
        FiniteHenselWeight.denominatorExponent t := by
  simp [concreteDenRegularBridge, Wfield, etaField, embeddingOf𝒪Into𝕃_mk,
    liftBivariate_C]

lemma embedding_betaRegular_eq_finiteAlpha_mul_denRegularBridge
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0) (N t : ℕ) (ht : t ≤ N) :
    embeddingOf𝒪Into𝕃 H (betaRegular x₀ R H hHyp hzeta N t ht) =
      finiteAlpha (R := R) (H := H) x₀ N t *
        embeddingOf𝒪Into𝕃 H (concreteDenRegularBridge x₀ R hHyp t) := by
  rw [embedding_betaRegular, embedding_concreteDenRegularBridge]
  rfl

lemma embedding_concreteDenRegularBridge_ne_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (concreteDenRegularBridge x₀ R hHyp t) ≠ 0 := by
  rw [embedding_concreteDenRegularBridge]
  have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
  have heta : etaField (R := R) (H := H) x₀ hHyp ≠ 0 := by
    rw [etaField_eq]
    exact mul_ne_zero (pow_ne_zero _ hW) hzeta
  exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)


/-- Canonical regular representatives used in the explicit common numerator. -/
noncomputable def commonWRegular {H : F[X][Y]} [Fact (Irreducible H)] : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C H.leadingCoeff)

noncomputable def commonTRegular {H : F[X][Y]} [Fact (Irreducible H)] : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X

noncomputable def commonConstRegular {H : F[X][Y]} [Fact (Irreducible H)] (a : F) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C (Polynomial.C a))

/-- Explicit regular common numerator for the evaluated finite lift minus an affine value. -/
noncomputable def explicitGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) : 𝒪 H :=
  (∑ i ∈ Finset.range (k + 1),
      concreteBetaUpTo x₀ R hHyp hzeta N i *
        commonConstRegular dx ^ i * commonWRegular ^ (k - i) *
        (HenselNumerators.xi x₀ R H hHyp) ^
          (FiniteHenselWeight.denominatorExponent k -
            FiniteHenselWeight.denominatorExponent i)) -
    (commonConstRegular u₀ + commonTRegular * commonConstRegular u₁) *
      concreteDenRegularBridge x₀ R hHyp k

lemma embedding_commonWRegular
    {H : F[X][Y]} [Fact (Irreducible H)] :
    embeddingOf𝒪Into𝕃 H (commonWRegular (H := H)) = Wfield (H := H) := by
  simp [commonWRegular, Wfield, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

lemma embedding_commonTRegular
    {H : F[X][Y]} [Fact (Irreducible H)] :
    embeddingOf𝒪Into𝕃 H (commonTRegular (H := H)) = functionFieldT (H := H) := by
  simp [commonTRegular, embeddingOf𝒪Into𝕃_mk, liftBivariate_X]

lemma embedding_commonConstRegular
    {H : F[X][Y]} [Fact (Irreducible H)] (a : F) :
    embeddingOf𝒪Into𝕃 H (commonConstRegular (H := H) a) = fieldTo𝕃 (H := H) a := by
  simp [commonConstRegular, fieldTo𝕃, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]



lemma concreteDenRegularBridge_mul_to_common
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H) {i k : ℕ} (hik : i ≤ k) :
    concreteDenRegularBridge x₀ R hHyp i * commonWRegular ^ (k - i) *
        (HenselNumerators.xi x₀ R H hHyp) ^
          (FiniteHenselWeight.denominatorExponent k -
            FiniteHenselWeight.denominatorExponent i) =
      concreteDenRegularBridge x₀ R hHyp k := by
  unfold concreteDenRegularBridge commonWRegular
  have hw : k + 1 = (i + 1) + (k - i) := by omega
  have hemono := denominatorExponent_mono hik
  have he : FiniteHenselWeight.denominatorExponent k =
      FiniteHenselWeight.denominatorExponent i +
        (FiniteHenselWeight.denominatorExponent k -
          FiniteHenselWeight.denominatorExponent i) := by omega
  rw [hw, he, pow_add, pow_add, Nat.add_sub_cancel_left]
  ring

lemma embedding_explicitGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H
      (explicitGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
      gammaDifferenceField (R := R) (H := H) x₀ dx u₀ u₁ hHyp N k := by
  classical
  unfold explicitGammaDifferenceRegular gammaDifferenceField evaluatedFiniteAlpha
  rw [map_sub, map_mul, map_add, map_mul, map_sum,
    embedding_commonConstRegular, embedding_commonTRegular,
    embedding_commonConstRegular, embedding_concreteDenRegularBridge]
  rw [sub_mul]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
  have hiN : i ≤ N := hik.trans hkN
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
    concreteBetaUpTo_eq_betaRegular x₀ R hHyp hzeta N i hiN,
    embedding_betaRegular, embedding_commonConstRegular, embedding_commonWRegular]
  unfold betaField commonDenominator Wfield etaField
  have hw : k + 1 = (i + 1) + (k - i) := by omega
  have hemono := denominatorExponent_mono hik
  have he : FiniteHenselWeight.denominatorExponent k =
      FiniteHenselWeight.denominatorExponent i +
        (FiniteHenselWeight.denominatorExponent k -
          FiniteHenselWeight.denominatorExponent i) := by omega
  rw [hw, he, pow_add, pow_add, Nat.add_sub_cancel_left]
  ring


lemma explicitGammaDifferenceRegular_eq_chosen
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    explicitGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN =
      gammaDifferenceRegular_yz x₀ dx u₀ u₁ R H hHyp hzeta hH hD_H hD_R hRdeg N k hkN := by
  apply embeddingOf𝒪Into𝕃_injective hH
  rw [embedding_explicitGammaDifferenceRegular, embedding_gammaDifferenceRegular_yz]

lemma explicitGammaDifferenceRegular_weight
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some ((2 * k + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  rw [explicitGammaDifferenceRegular_eq_chosen x₀ dx u₀ u₁ R hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN]
  exact gammaDifferenceRegular_weight_yz x₀ dx u₀ u₁ R H hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN


lemma explicitGammaDifferenceRegular_weight_yz
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some ((2 * k + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  rw [explicitGammaDifferenceRegular_eq_chosen x₀ dx u₀ u₁ R hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN]
  exact gammaDifferenceRegular_weight_yz x₀ dx u₀ u₁ R H hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN


/-- Partial specialization of a concrete finite function-field coefficient,
using its actual regular numerator and denominator. -/
noncomputable def concreteSpecializedAlpha
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N : ℕ) (z : F) (root : rationalRoot (monicize H) z) (n : ℕ) : F :=
  piZ z root (concreteBetaUpTo x₀ R hHyp hzeta N n) /
    piZ z root (concreteDenRegularBridge x₀ R hHyp n)

/-- Pointwise vanishing of the explicit common numerator from Taylor specialization. -/
theorem piZ_explicitGammaDifferenceRegular_eq_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ z : F) (root : rationalRoot (monicize H) z)
    (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k →
      concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
        FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k → piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0)
    (heval : P.eval (x₀ + dx) = u₀ + root.1 * u₁) :
    piZ z root (explicitGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0 := by
  classical
  have hTaylorSum :
      (∑ i ∈ Finset.range (k + 1), FiniteHensel.TaylorCoeff P x₀ i * dx ^ i) =
        P.eval (x₀ + dx) := by
    calc
      _ = (FiniteHensel.truncSeries (FiniteHensel.TaylorCoeff P x₀) k).eval dx := by
        unfold FiniteHensel.truncSeries
        change (∑ i ∈ Finset.range (k + 1), _) =
          (Polynomial.evalRingHom dx) (∑ i ∈ Finset.range (k + 1), _)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp
      _ = (P.comp (Polynomial.C x₀ + Polynomial.X)).eval dx := by
        rw [FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg]
      _ = P.eval (x₀ + dx) := by simp [Polynomial.eval_comp]
  have hterm : ∀ i, i ≤ k →
      piZ z root
          (concreteBetaUpTo x₀ R hHyp hzeta N i * commonConstRegular dx ^ i *
            commonWRegular ^ (k - i) *
            (HenselNumerators.xi x₀ R H hHyp) ^
              (FiniteHenselWeight.denominatorExponent k -
                FiniteHenselWeight.denominatorExponent i)) =
        FiniteHensel.TaylorCoeff P x₀ i * dx ^ i *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    intro i hik
    have hs := hspecializes i hik
    unfold concreteSpecializedAlpha at hs
    have hb : piZ z root (concreteBetaUpTo x₀ R hHyp hzeta N i) =
        FiniteHensel.TaylorCoeff P x₀ i *
          piZ z root (concreteDenRegularBridge x₀ R hHyp i) := by
      exact (div_eq_iff (hden i hik)).mp hs
    have hscale := congrArg (piZ z root)
      (concreteDenRegularBridge_mul_to_common x₀ R hHyp hik)
    simp only [map_mul, map_pow] at hscale
    simp only [map_mul, map_pow, hb, commonConstRegular, piZ_mk_C,
      Polynomial.eval_C]
    rw [← hscale]
    ring
  unfold explicitGammaDifferenceRegular
  rw [map_sub, map_sum, map_mul, map_add, map_mul]
  have hC : ∀ a : F, piZ z root (commonConstRegular (H := H) a) = a := by
    intro a
    simp [commonConstRegular, piZ_mk_C]
  simp only [hC]
  have hT : piZ z root (commonTRegular (H := H)) = root.1 := by
    simp [commonTRegular, piZ, piZLift, Polynomial.evalEval]
  rw [hT]
  have hsum :
      ∑ i ∈ Finset.range (k + 1),
          piZ z root
            (concreteBetaUpTo x₀ R hHyp hzeta N i * commonConstRegular dx ^ i *
              commonWRegular ^ (k - i) *
              xi x₀ R H hHyp ^
                (FiniteHenselWeight.denominatorExponent k -
                  FiniteHenselWeight.denominatorExponent i)) =
        (∑ i ∈ Finset.range (k + 1), FiniteHensel.TaylorCoeff P x₀ i * dx ^ i) *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i (by rw [Finset.mem_range] at hi; omega)
  rw [hsum, hTaylorSum, heval]
  ring

/-- If the exact regular-fraction specializations agree with ordinary Taylor
coefficients through `k`, they satisfy the specialized finite-Hensel residual
through `k`.  This removes the previously free `hvanish` assumption. -/
theorem concreteSpecializedAlpha_vanishesThrough
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R₀ : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R₀ H)
    (hzeta : HenselNumerators.zeta R₀ x₀ H ≠ 0)
    (N : ℕ) (z : F) (root : rationalRoot (monicize H) z)
    (R : F[X][Y]) (P : F[X]) (x : F) (k : ℕ)
    (hPdeg : P.natDegree ≤ k) (hExact : R.eval P = 0)
    (hspecializes : ∀ n, n ≤ k →
      concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n =
        FiniteHensel.TaylorCoeff P x n) :
    FiniteHensel.VanishesThrough
      (FiniteHensel.residual R x
        (concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root) k) k := by
  have htrunc :
      FiniteHensel.truncSeries
          (concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root) k =
        FiniteHensel.truncSeries (FiniteHensel.TaylorCoeff P x) k := by
    ext n
    by_cases hn : n ≤ k
    · rw [FiniteHensel.coeff_truncSeries _ _ _ hn,
        FiniteHensel.coeff_truncSeries _ _ _ hn,
        hspecializes n hn]
    · simp [FiniteHensel.truncSeries, hn]
  unfold FiniteHensel.residual
  rw [htrunc]
  exact FiniteHensel.TaylorCoeff_vanishesThrough R P x k hPdeg hExact

/-- Taylor coefficients above the degree of `P` vanish, even after expansion
around an arbitrary point. -/
theorem TaylorCoeff_eq_zero_of_natDegree_lt
    (P : F[X]) (x : F) {k n : ℕ} (hPdeg : P.natDegree ≤ k) (hkn : k < n) :
    FiniteHensel.TaylorCoeff P x n = 0 := by
  unfold FiniteHensel.TaylorCoeff
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hshift : (Polynomial.C x + Polynomial.X : F[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hcomp : (P.comp (Polynomial.C x + Polynomial.X)).natDegree ≤ k := by
    calc
      _ ≤ P.natDegree * (Polynomial.C x + Polynomial.X : F[X]).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ k * 1 := Nat.mul_le_mul hPdeg hshift
      _ = k := Nat.mul_one k
  omega

/-- A zero specialized Taylor coefficient forces direct numerator vanishing,
provided the actual regular denominator is nonzero at the pair. -/
theorem piZ_betaRegular_eq_zero_of_TaylorCoeff_eq_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R₀ : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R₀ H)
    (hzeta : HenselNumerators.zeta R₀ x₀ H ≠ 0)
    (N n : ℕ) (hnN : n ≤ N) (z : F)
    (root : rationalRoot (monicize H) z)
    (P : F[X]) (x : F)
    (hspecializes : concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n =
      FiniteHensel.TaylorCoeff P x n)
    (hTaylor : FiniteHensel.TaylorCoeff P x n = 0)
    (hden : piZ z root (concreteDenRegularBridge x₀ R₀ hHyp n) ≠ 0) :
    piZ z root (betaRegular x₀ R₀ H hHyp hzeta N n hnN) = 0 := by
  have hfrac :
      piZ z root (concreteBetaUpTo x₀ R₀ hHyp hzeta N n) /
          piZ z root (concreteDenRegularBridge x₀ R₀ hHyp n) = 0 := by
    exact hspecializes.trans hTaylor
  have hnum : piZ z root (concreteBetaUpTo x₀ R₀ hHyp hzeta N n) = 0 :=
    ((div_eq_zero_iff).mp hfrac).resolve_right hden
  simpa [concreteBetaUpTo_eq_betaRegular x₀ R₀ hHyp hzeta N n hnN] using hnum

/-- Concrete simultaneous middle-coefficient vanishing using the actual
regular denominator.  Specialization-to-Taylor compatibility is the sole
bridge hypothesis; residual vanishing and direct numerator zeros are derived. -/
theorem concreteFiniteAlpha_middle_vanish_regularDen
    [Fintype F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R₀ : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R₀ H)
    (hzeta : HenselNumerators.zeta R₀ x₀ H ≠ 0)
    (D d k DX e : ℕ) (hD : Bivariate.totalDegree H ≤ D)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (center : T → F)
    (hPdeg : ∀ z : T, (P z).natDegree ≤ k)
    (hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R₀ hHyp hzeta DX (z : F) (root z) n =
        FiniteHensel.TaylorCoeff (P z) (center z) n)
    (hden : ∀ t, k < t → t < DX → ∀ z : T,
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R₀ hHyp t) ≠ 0)
    (hweight : ∀ t, k < t → t < DX →
      regularWeight (Fact.out : 0 < H.natDegree)
        (concreteBetaUpTo x₀ R₀ hHyp hzeta DX t) D ≤
          (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ))
    (hcard : 2 * DX * H.natDegree * d * D + e + 1 < T.card) :
    ∀ t, k < t → t < DX →
      finiteAlpha (R := R₀) (H := H) x₀ DX t = 0 := by
  apply functionField_middle_coefficients_eq_zero_regularDen (T := T) (root := root)
    (Fact.out : 0 < H.natDegree) D d k DX e hD
    (finiteAlpha (R := R₀) (H := H) x₀ DX)
    (concreteBetaUpTo x₀ R₀ hHyp hzeta DX)
    (concreteDenRegularBridge x₀ R₀ hHyp)
  · intro t hkt htDX
    have ht : t ≤ DX := by omega
    rw [concreteBetaUpTo_eq_betaRegular x₀ R₀ hHyp hzeta DX t ht]
    exact embedding_betaRegular_eq_finiteAlpha_mul_denRegularBridge
      x₀ R₀ hHyp hzeta DX t ht
  · intro t _ _
    exact embedding_concreteDenRegularBridge_ne_zero x₀ R₀ hHyp hzeta t
  · exact hweight
  · intro t hkt htDX z
    have ht : t ≤ DX := by omega
    rw [concreteBetaUpTo_eq_betaRegular x₀ R₀ hHyp hzeta DX t ht]
    apply piZ_betaRegular_eq_zero_of_TaylorCoeff_eq_zero
      x₀ R₀ hHyp hzeta DX t ht (z : F) (root z) (P z) (center z)
    · exact hspecializes z t ht
    · exact TaylorCoeff_eq_zero_of_natDegree_lt (P z) (center z) (hPdeg z) hkt
    · exact hden t hkt htDX z
  · exact hcard

end ProximityPrize.SubmissionLower
