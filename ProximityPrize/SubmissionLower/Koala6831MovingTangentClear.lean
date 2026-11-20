import Mathlib.RingTheory.MvPolynomial.Localization
import ProximityPrize.SubmissionLower.Koala6831MovingTransverseSpecialize


namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped Classical BigOperators nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K]

private abbrev ClearedCoeff (K : Type*) [Field K] := MvPolynomial (Fin 2) (Polynomial K)

attribute [local instance] MvPolynomial.algebraMvPolynomial

private def coefficientDenominators (K : Type*) [Field K] : Submonoid (ClearedCoeff K) :=
  (nonZeroDivisors (Polynomial K)).map MvPolynomial.C

local instance tangentCoefficientLocalization :
    IsLocalization (coefficientDenominators K) (NormalizedCoeff K) :=
  MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)

private theorem clearCoefficients (c : NormalizedCoeff K) (hc : c ≠ 0) :
    ∃ P : ClearedCoeff K, P ≠ 0 ∧ (∀ i, P.degreeOf i ≤ c.degreeOf i) ∧
      ∀ q, evalNormalizedCoefficient q c = 0 →
        evalNormalizedCoefficient q (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P) = 0 := by
  obtain ⟨⟨P, s⟩, heq⟩ := IsLocalization.surj (coefficientDenominators K) c
  obtain ⟨d, hd, hds⟩ := s.property
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  change c * MvPolynomial.map φ (s : ClearedCoeff K) = MvPolynomial.map φ P at heq
  rw [← hds, MvPolynomial.map_C] at heq
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hφd : φ d ≠ 0 := by simpa only [map_zero] using hinj.ne hd0
  have hne : P ≠ 0 := by
    intro hn
    rw [hn, map_zero] at heq
    exact (mul_ne_zero hc (by simpa using hφd)) heq
  refine ⟨P, hne, fun i => ?_, fun q hq => ?_⟩
  · have hdeg : (MvPolynomial.map φ P).degreeOf i = P.degreeOf i := by
      simp only [MvPolynomial.degreeOf_eq_sup, MvPolynomial.support_map_of_injective P hinj]
    rw [← hdeg, ← heq]
    exact MvPolynomial.degreeOf_mul_C_le _ _ _
  · rw [← heq, map_mul, hq, zero_mul]

private def liftedVariables (K : Type*) [Field K] : Fin 2 → P4 K :=
  ![MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4)]

private def liftCarrier (K : Type*) [Field K] : ClearedCoeff K →ₐ[K] P4 K :=
  MvPolynomial.aevalTower (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) (liftedVariables K)

private theorem degreeOf_liftX (f : Polynomial K) (i : Fin 4) (hi : i ≠ 0) :
    (liftX f).degreeOf i ≤ 0 := by
  induction f using Polynomial.induction_on' with
  | add P Q hP hQ =>
    change (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (P + Q) : P4 K).degreeOf i ≤ 0
    rw [map_add]
    exact (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le hP hQ)
  | monomial n a =>
    simp only [liftX, Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
      (by simp [MvPolynomial.degreeOf_X_of_ne hi])

private theorem degreeOf_liftCarrier_le (F : ClearedCoeff K) (i : Fin 4) (hi : i ≠ 0)
    (weights : Fin 2 → ℕ) (hv : ∀ j, (liftedVariables K j).degreeOf i ≤ weights j) :
    (liftCarrier K F).degreeOf i ≤ F.weightedTotalDegree weights := by
  classical
  change (MvPolynomial.eval₂ _ (liftedVariables K) F : P4 K).degreeOf i ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  refine Finset.sup_le fun d hd => ?_
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  have hconstant : (liftX (F.coeff d)).degreeOf i ≤ 0 := degreeOf_liftX _ i hi
  have hweight := MvPolynomial.le_weightedTotalDegree weights hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hweight
  simp only [nsmul_eq_mul, Nat.cast_id] at hweight
  refine (Nat.add_le_add hconstant (MvPolynomial.degreeOf_prod_le _ _ _)).trans ?_
  rw [zero_add]
  exact (Finset.sum_le_sum fun j _ =>
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left (d j) (hv j))).trans hweight

private theorem coordinate_weight (F : ClearedCoeff K) (i : Fin 2) :
    F.weightedTotalDegree (Pi.single i 1) = F.degreeOf i := by
  rw [MvPolynomial.weightedTotalDegree, MvPolynomial.degreeOf_eq_sup]
  congr 1
  funext d
  exact Finsupp.weight_single_one_apply i d

private theorem degreeOf_liftCarrier (F : ClearedCoeff K) :
    (liftCarrier K F).degreeOf 1 ≤ F.degreeOf 0 ∧
      (liftCarrier K F).degreeOf 2 ≤ F.degreeOf 1 ∧ (liftCarrier K F).degreeOf 3 = 0 := by
  refine ⟨?_, ?_, Nat.eq_zero_of_le_zero ?_⟩
  · rw [← coordinate_weight F 0]
    apply degreeOf_liftCarrier_le F 1 (by decide)
    intro j
    fin_cases j <;> simp [liftedVariables, MvPolynomial.degreeOf_X_of_ne]
  · rw [← coordinate_weight F 1]
    apply degreeOf_liftCarrier_le F 2 (by decide)
    intro j
    fin_cases j <;> simp [liftedVariables, MvPolynomial.degreeOf_X_of_ne]
  · have h := degreeOf_liftCarrier_le F 3 (by decide) (fun _ => 0) (by
      intro j
      fin_cases j <;> simp [liftedVariables, MvPolynomial.degreeOf_X_of_ne])
    have hzero : F.weightedTotalDegree (fun _ => 0) ≤ 0 :=
      Finset.sup_le fun d _ => by simp [Finsupp.weight_apply, Finsupp.sum]
    exact h.trans hzero

private theorem collectX_liftX (f : Polynomial K) :
    RCN136.collectX K (liftX f) = MvPolynomial.C f := by
  have h :
      (RCN136.collectX K).toAlgHom.comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) =
        IsScalarTower.toAlgHom K (Polynomial K) (MvPolynomial (Fin 3) (Polynomial K)) := by
    apply Polynomial.algHom_ext
    simp [AlgHom.comp_apply, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun h f

private theorem liftCarrier_injective :
    Function.Injective (liftCarrier K) := by
  have h : ((RCN136.collectX K).toRingHom.comp (liftCarrier K).toRingHom) =
      (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro f
      simp [RingHom.comp_apply, liftCarrier]
      exact collectX_liftX f
    · intro i
      fin_cases i
      · simp [RingHom.comp_apply, liftCarrier, liftedVariables]
        exact RCN136.collectX_X_succ (K := K) (0 : Fin 3)
      · simp [RingHom.comp_apply, liftCarrier, liftedVariables]
        exact RCN136.collectX_X_succ (K := K) (1 : Fin 3)
  intro P Q hPQ
  have hrename : Function.Injective
      (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) :
        ClearedCoeff K →ₐ[Polynomial K] MvPolynomial (Fin 3) (Polynomial K)).toRingHom :=
    MvPolynomial.rename_injective _ (Fin.castSucc_injective _)
  apply hrename
  have heq := congrArg (RCN136.collectX K) hPQ
  change ((RCN136.collectX K).toRingHom.comp (liftCarrier K).toRingHom) P =
    ((RCN136.collectX K).toRingHom.comp (liftCarrier K).toRingHom) Q at heq
  rwa [h] at heq

private theorem specialize_liftX (f q : Polynomial K) :
    RCN319.specialization K q 0 (liftX f) = f := by
  have h : (RCN319.specialization K q 0).comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) =
      AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    simp [AlgHom.comp_apply, RCN319.specialization]
  exact DFunLike.congr_fun h f

private theorem eval_liftCarrier (F : ClearedCoeff K) (q : Polynomial K) :
    evalNormalizedCoefficient q (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) F) =
      algebraMap (Polynomial K) (RatFunc K) (RCN319.specialization K q 0 (liftCarrier K F)) := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have h : (evalNormalizedCoefficient q).toRingHom.comp (MvPolynomial.map φ) =
      φ.comp ((RCN319.specialization K q 0).comp (liftCarrier K)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro f
      simp [RingHom.comp_apply, liftCarrier, evalNormalizedCoefficient]
      exact congrArg φ (specialize_liftX f q).symm
    · intro i
      fin_cases i <;> simp [RingHom.comp_apply, liftCarrier, liftedVariables,
        evalNormalizedCoefficient, RCN319.specialization, φ]
  exact DFunLike.congr_fun h F

theorem clear_seed_independent_carrier (c : NormalizedCoeff K) (hc : c ≠ 0) :
    ∃ F : P4 K, F ≠ 0 ∧ F.degreeOf 1 ≤ c.degreeOf 0 ∧ F.degreeOf 2 ≤ c.degreeOf 1 ∧
      F.degreeOf 3 = 0 ∧
      ∀ q, evalNormalizedCoefficient q c = 0 → RCN319.specialization K q 0 F = 0 := by
  obtain ⟨P, hP, hdeg, hEval⟩ := clearCoefficients c hc
  have hdegrees := degreeOf_liftCarrier P
  have hne : liftCarrier K P ≠ 0 := by
    simpa only [map_zero] using liftCarrier_injective.ne hP
  refine ⟨liftCarrier K P, hne, hdegrees.1.trans (hdeg 0), hdegrees.2.1.trans (hdeg 1),
    hdegrees.2.2, fun q hq => ?_⟩
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  rw [map_zero, ← eval_liftCarrier]
  exact hEval q hq

end

end ProximityPrize.SubmissionLower.Koala6831Moving
