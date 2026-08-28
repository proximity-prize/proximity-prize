import ProximityPrize.SubmissionLower.BCHKSInitialValueAffine

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

noncomputable def commonZRegular (H : F[X][Y]) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C Polynomial.X)

@[simp] theorem embedding_commonZRegular
    (H : F[X][Y]) [Fact (Irreducible H)] :
    embeddingOf𝒪Into𝕃 H (commonZRegular H) = liftToFunctionField (H:=H) Polynomial.X := by
  simp [commonZRegular, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

@[simp] theorem piZ_commonZRegular (H : F[X][Y]) (z : F)
    (root : rationalRoot (monicize H) z) : piZ z root (commonZRegular H) = z := by
  simp [commonZRegular, piZ_mk_C]

noncomputable def explicitBaseZGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) : 𝒪 H :=
  (∑ i ∈ Finset.range (k + 1),
      concreteBetaUpTo x₀ R hHyp hzeta N i * commonConstRegular dx ^ i *
        commonWRegular ^ (k-i) * xi x₀ R H hHyp ^
          (FiniteHenselWeight.denominatorExponent k - FiniteHenselWeight.denominatorExponent i)) -
    (commonConstRegular u₀ + commonZRegular H * commonConstRegular u₁) *
      concreteDenRegularBridge x₀ R hHyp k

theorem embedding_explicitBaseZGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
      (evaluatedFiniteAlpha (R:=R) (H:=H) x₀ dx N k -
        (fieldTo𝕃 (H:=H) u₀ + liftToFunctionField (H:=H) Polynomial.X * fieldTo𝕃 (H:=H) u₁)) *
        commonDenominator (R:=R) (H:=H) x₀ hHyp k := by
  unfold explicitBaseZGammaDifferenceRegular
  rw [map_sub, map_sum, map_mul, map_add, map_mul]
  simp only [map_mul, map_pow, embedding_commonConstRegular, embedding_commonZRegular,
    embedding_concreteDenRegularBridge]
  have hsum : (∑ i ∈ Finset.range (k+1),
      embeddingOf𝒪Into𝕃 H (concreteBetaUpTo x₀ R hHyp hzeta N i) *
      fieldTo𝕃 (H:=H) dx^i *
      embeddingOf𝒪Into𝕃 H commonWRegular^(k-i) *
      embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)^
        (FiniteHenselWeight.denominatorExponent k-FiniteHenselWeight.denominatorExponent i)) =
      evaluatedFiniteAlpha (R:=R) (H:=H) x₀ dx N k * commonDenominator (R:=R) (H:=H) x₀ hHyp k := by
    have h := embedding_explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN
    simpa [explicitGammaDifferenceRegular, embedding_commonConstRegular, gammaDifferenceField, commonDenominator] using h
  rw [hsum]
  unfold commonDenominator
  ring

/-- Canonical gamma affine decomposition with the independent base coordinate. -/
theorem canonicalFunctionFieldGamma_baseZ_affine
    [DecidableEq F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ)
    (D : Finset F) (hD : k+1 ≤ D.card) (U₀ U₁ : F → F)
    (hdeg : (canonicalFunctionFieldGamma H x₀ R N k).natDegree ≤ k)
    (heval : ∀ x ∈ D, (canonicalFunctionFieldGamma H x₀ R N k).eval (fieldTo𝕃 (H:=H) x) =
      fieldTo𝕃 (H:=H) (U₀ x) + liftToFunctionField (H:=H) Polynomial.X * fieldTo𝕃 (H:=H) (U₁ x)) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      canonicalFunctionFieldGamma H x₀ R N k = p₀.map (groundToFunctionField H) +
        Polynomial.C (liftToFunctionField (H:=H) Polynomial.X) * p₁.map (groundToFunctionField H) := by
  exact extension_polynomial_eq_affine_of_many_evals (groundToFunctionField H)
    (liftToFunctionField (H:=H) Polynomial.X) _ k D hD U₀ U₁ hdeg (by
      intro x hx; change _; exact heval x hx)

theorem piZ_explicitBaseZGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ z : F) (root : rationalRoot (monicize H) z)
    (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k →
      concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
        FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k → piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0) :
    piZ z root (explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
      (P.eval (x₀+dx) - (u₀ + z*u₁)) *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
  have hTaylor : (∑ i ∈ Finset.range (k+1),
      FiniteHensel.TaylorCoeff P x₀ i * dx^i) = P.eval (x₀+dx) := by
    calc
      _ = (FiniteHensel.truncSeries (FiniteHensel.TaylorCoeff P x₀) k).eval dx := by
        unfold FiniteHensel.truncSeries
        change (∑ i ∈ Finset.range (k+1), _) =
          (Polynomial.evalRingHom dx) (∑ i ∈ Finset.range (k+1), _)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi; simp
      _ = (P.comp (Polynomial.C x₀ + Polynomial.X)).eval dx := by
        rw [FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg]
      _ = _ := by simp [Polynomial.eval_comp]
  have hterm : ∀ i, i ≤ k →
      piZ z root
        (concreteBetaUpTo x₀ R hHyp hzeta N i * commonConstRegular dx^i *
          commonWRegular^(k-i) * xi x₀ R H hHyp ^
            (FiniteHenselWeight.denominatorExponent k -
              FiniteHenselWeight.denominatorExponent i)) =
      FiniteHensel.TaylorCoeff P x₀ i * dx^i *
        piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    intro i hik
    have hs := hspecializes i hik
    unfold concreteSpecializedAlpha at hs
    have hb := (div_eq_iff (hden i hik)).mp hs
    have hc := congrArg (piZ z root)
      (concreteDenRegularBridge_mul_to_common x₀ R hHyp hik)
    simp only [map_mul,map_pow] at hc ⊢
    rw [hb, ← hc]
    simp [commonConstRegular,piZ_mk_C]
    ring
  have hold : piZ z root (explicitGammaDifferenceRegular
      x₀ dx u₀ 0 R hHyp hzeta N k hkN) =
      (P.eval (x₀+dx)-u₀) *
        piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    unfold explicitGammaDifferenceRegular
    rw [map_sub,map_sum,map_mul,map_add,map_mul]
    simp only [map_mul,map_pow]
    have hs : (∑ i ∈ Finset.range (k+1),
        piZ z root (concreteBetaUpTo x₀ R hHyp hzeta N i) *
          piZ z root (commonConstRegular dx)^i *
          piZ z root commonWRegular^(k-i) *
          piZ z root (xi x₀ R H hHyp)^
            (FiniteHenselWeight.denominatorExponent k-
              FiniteHenselWeight.denominatorExponent i)) =
        (∑ i ∈ Finset.range (k+1), FiniteHensel.TaylorCoeff P x₀ i*dx^i) *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [map_mul,map_pow] using hterm i (by simpa using hi)
    rw [hs,hTaylor]
    simp [commonConstRegular,commonTRegular,piZ,piZLift]
    ring
  have hold' := hold
  unfold explicitGammaDifferenceRegular at hold'
  rw [map_sub, map_sum, map_mul, map_add, map_mul] at hold'
  simp [commonConstRegular, piZ_mk_C] at hold'
  unfold explicitBaseZGammaDifferenceRegular
  rw [map_sub, map_sum, map_mul, map_add, map_mul]
  simp [commonZRegular, commonConstRegular, piZ_mk_C]
  linear_combination hold'

/-- Pair agreement is equivalent to vanishing of the corrected numerator at a
non-pole pair. -/
theorem piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ z : F) (root : rationalRoot (monicize H) z)
        (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k → concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
      FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k → piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0) :
    piZ z root (explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0 ↔
      P.eval (x₀+dx) = u₀+z*u₁ := by
  rw [piZ_explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ z root
    R hHyp hzeta N k hkN P hPdeg hspecializes hden]
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (hden k (le_refl k)))
  · intro h
    simp [h]




/-- Regular-weight bound for the base-coordinate affine corrected numerator. -/
theorem explicitBaseZGammaDifferenceRegular_weight_exact
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some (((2*k+1)*Bivariate.natDegreeY R*D)+1) : WithBot ℕ) := by
  let B := (2*k+1)*Bivariate.natDegreeY R*D
  have hold (a b : F) : regularWeight hH
      (explicitGammaDifferenceRegular x₀ dx a b R hHyp hzeta N k hkN) D ≤
      (WithBot.some B : WithBot ℕ) :=
    explicitGammaDifferenceRegular_weight_yz x₀ dx a b R hHyp hzeta hH
      hD_H hD_R hRdeg N k hkN
  have hZ : regularWeight hH (commonZRegular H) D ≤
      (WithBot.some 1 : WithBot ℕ) := by
    exact regularWeight_le_of_regularWeightLe (commonZRegular H) (by
      rw [embedding_commonZRegular]
      exact (regularWeightLe_liftToFunctionField hD_H hH Polynomial.X).mono (by simp))
  have hid : explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN =
      explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN -
      commonZRegular H * (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
        explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN) := by
    unfold explicitBaseZGammaDifferenceRegular explicitGammaDifferenceRegular
    simp [commonConstRegular]
    ring
  rw [hid]
  have hdiff : regularWeight hH
      (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
       explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN) D ≤
      (WithBot.some B : WithBot ℕ) := by
    simpa [sub_eq_add_neg] using ((regularWeight_add_le hD_H hH
    (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN)
    (- explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN)).trans
      (max_le (hold 0 0) (by simpa [regularWeight_neg] using hold u₁ 0)))
  have hmul : regularWeight hH
      (commonZRegular H * (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
       explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN)) D ≤
      (WithBot.some (B+1) : WithBot ℕ) := by
    have ht := regularWeight_mul_le' hD_H hH hdiff hZ
    rw [mul_comm
      (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
        explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN)
      (commonZRegular H)] at ht
    simpa [Nat.add_comm] using ht
  have hsub : regularWeight hH
      (explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN -
       commonZRegular H * (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
        explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN)) D ≤
      (WithBot.some (B+1) : WithBot ℕ) := by
    have hneg : regularWeight hH
        (-(commonZRegular H * (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
          explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN))) D ≤
        (WithBot.some (B+1) : WithBot ℕ) := by
      rw [regularWeight_neg]
      exact hmul
    have hadd := regularWeight_add_le hD_H hH
      (explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN)
      (-(commonZRegular H * (explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN -
        explicitGammaDifferenceRegular x₀ dx u₁ 0 R hHyp hzeta N k hkN)))
    have hbound := hadd.trans
      (max_le ((hold u₀ 0).trans (WithBot.coe_le_coe.mpr (by omega))) hneg)
    simpa only [sub_eq_add_neg] using hbound
  simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsub


/-- Y/Z-cap version of the exact base-coordinate weight bound. -/
theorem explicitBaseZGammaDifferenceRegular_weight_exact_yz
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D) (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some (((2*k+1)*Bivariate.natDegreeY R*D)+1) : WithBot ℕ) := by
  exact explicitBaseZGammaDifferenceRegular_weight_exact x₀ dx u₀ u₁ R hHyp hzeta hH
    hD_H hYZ hRdeg N k hkN

/-- Coarser convenient form of the sharp base-coordinate weight bound. -/
theorem explicitBaseZGammaDifferenceRegular_weight
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitBaseZGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some ((2*k+2)*Bivariate.natDegreeY R*D) : WithBot ℕ) := by
  refine (explicitBaseZGammaDifferenceRegular_weight_exact x₀ dx u₀ u₁ R hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN).trans (WithBot.coe_le_coe.mpr ?_)
  have hd : 1 ≤ Bivariate.natDegreeY R := by omega
  have hHne : H ≠ 0 := by rintro rfl; simp at hH
  have hHin : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHne)
  have hcoef := Bivariate.coeff_totalDegree_le H hHin
  have hDone : 1 ≤ D := by omega
  nlinarith

end ProximityPrize.SubmissionLower
