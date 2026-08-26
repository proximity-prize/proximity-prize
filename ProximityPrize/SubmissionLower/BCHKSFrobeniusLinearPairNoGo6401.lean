import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusLinearPairNoGo6401
open Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
noncomputable def linearFactor
    {K : Type*} [Field K] (beta : K) : Polynomial K :=
  Polynomial.X - Polynomial.C beta
@[simp] theorem linearFactor_eval
    {K : Type*} [Field K] (beta x : K) :
    Polynomial.eval x (linearFactor beta) = x - beta := by
  simp [linearFactor]
theorem linearFactor_map
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K) :
    (linearFactor beta).map sigma = linearFactor (sigma beta) := by
  simp [linearFactor]
def linearHilbertError
    {K I : Type*} [Field K] (beta : K) (x f : I → K) (i : I) : K :=
  (x i - beta) * f i
theorem linearHilbertError_relation
    {K I : Type*} [Field K]
    (sigma : K →+* K) (beta : K) (x f : I → K)
    (hfixedX : ∀ i, sigma (x i) = x i)
    (hfixedF : ∀ i, sigma (f i) = f i) (i : I) :
    Polynomial.eval (x i) (linearFactor beta) *
        sigma (linearHilbertError beta x f i) =
      Polynomial.eval (x i) (linearFactor (sigma beta)) *
        linearHilbertError beta x f i := by
  simp only [linearFactor_eval, linearHilbertError, map_mul, map_sub,
    hfixedX, hfixedF]
  ring
theorem linearHilbertError_eq_zero_iff
    {K I : Type*} [Field K] (beta : K) (x f : I → K) (i : I)
    (hroot : x i ≠ beta) :
    linearHilbertError beta x f i = 0 ↔ f i = 0 := by
  simp [linearHilbertError, sub_ne_zero.mpr hroot]
def linearHilbertNormalize
    {K I : Type*} [Field K] (beta : K) (x E : I → K) (i : I) : K :=
  E i / (x i - beta)
theorem fixed_locator_ne_moving_root
    {K : Type*} [Field K] (sigma : K →+* K) (beta x : K)
    (hmove : beta ≠ sigma beta) (hfixed : sigma x = x) :
    x ≠ beta := by
  intro hxbeta
  apply hmove
  calc
    beta = x := hxbeta.symm
    _ = sigma x := hfixed.symm
    _ = sigma beta := by rw [hxbeta]
theorem linearPair_relation_imp_normalized_fixed
    {K : Type*} [Field K] (sigma : K →+* K) (beta x E : K)
    (hmove : beta ≠ sigma beta) (hfixed : sigma x = x)
    (hrel : (x - beta) * sigma E = (x - sigma beta) * E) :
    sigma (E / (x - beta)) = E / (x - beta) := by
  have hx : x ≠ beta := fixed_locator_ne_moving_root sigma beta x hmove hfixed
  have hden : x - beta ≠ 0 := sub_ne_zero.mpr hx
  have hsden : x - sigma beta ≠ 0 := by
    intro hz
    have hxs : x = sigma beta := sub_eq_zero.mp hz
    apply hmove
    have hsigmaEq : sigma beta = sigma x := by
      rw [hfixed]
      exact hxs.symm
    exact (sigma.injective hsigmaEq).trans hxs
  rw [map_div₀ sigma, map_sub, hfixed]
  field_simp [hden, hsden]
  linear_combination hrel
theorem linearHilbertNormalize_eq_zero_iff
    {K I : Type*} [Field K] (beta : K) (x E : I → K) (i : I)
    (hroot : x i ≠ beta) :
    linearHilbertNormalize beta x E i = 0 ↔ E i = 0 := by
  simp [linearHilbertNormalize, sub_ne_zero.mpr hroot]
theorem linearFactor_injective
    {K : Type*} [Field K] : Function.Injective (linearFactor : K → Polynomial K) := by
  intro beta gamma h
  have heval := congrArg (Polynomial.eval beta) h
  have hsub : beta - gamma = 0 := by
    simpa using heval.symm
  exact sub_eq_zero.mp hsub
theorem linearFactor_isCoprime_conjugate
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K)
    (hmove : beta ≠ sigma beta) :
    IsCoprime (linearFactor beta) (linearFactor (sigma beta)) := by
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  exact (sub_ne_zero.mpr hmove).isUnit
theorem linearPair_natDegree_le_one
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K) :
    (linearFactor beta).natDegree ≤ 1 ∧
      (linearFactor (sigma beta)).natDegree ≤ 1 := by
  constructor <;> simp [linearFactor]
theorem linearFactor_mul_fixedPolynomial_relation
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K)
    (R : Polynomial K) (hR : R.map sigma = R) :
    linearFactor beta * (linearFactor beta * R).map sigma =
      linearFactor (sigma beta) * (linearFactor beta * R) := by
  rw [Polynomial.map_mul, linearFactor_map, hR]
  ring
theorem homogeneous_linearPair_iff_fixedQuotient
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K)
    (hmove : beta ≠ sigma beta) (P : Polynomial K) :
    linearFactor beta * P.map sigma =
        linearFactor (sigma beta) * P ↔
      ∃ R : Polynomial K,
        P = linearFactor beta * R ∧ R.map sigma = R := by
  constructor
  · intro hrel
    have hcoprime := linearFactor_isCoprime_conjugate sigma beta hmove
    have hdvdprod : linearFactor beta ∣
        P * linearFactor (sigma beta) := by
      refine ⟨P.map sigma, ?_⟩
      simpa [mul_comm] using hrel.symm
    have hdvd : linearFactor beta ∣ P :=
      hcoprime.dvd_of_dvd_mul_right hdvdprod
    obtain ⟨R, hP⟩ := hdvd
    refine ⟨R, hP, ?_⟩
    rw [hP, Polynomial.map_mul, linearFactor_map] at hrel
    have hfactor :
        linearFactor beta * linearFactor (sigma beta) ≠ 0 := by
      exact mul_ne_zero (Polynomial.X_sub_C_ne_zero beta)
        (Polynomial.X_sub_C_ne_zero (sigma beta))
    apply mul_left_cancel₀ hfactor
    calc
      linearFactor beta * linearFactor (sigma beta) * R.map sigma =
          linearFactor beta *
            (linearFactor (sigma beta) * R.map sigma) := by ring
      _ = linearFactor (sigma beta) * (linearFactor beta * R) := hrel
      _ = linearFactor beta * linearFactor (sigma beta) * R := by ring
  · rintro ⟨R, rfl, hR⟩
    exact linearFactor_mul_fixedPolynomial_relation sigma beta R hR
theorem linearFactor_mul_natDegree_le
    {K : Type*} [Field K] (beta : K) (R : Polynomial K) (D : Nat)
    (hD : 0 < D) (hR : R.natDegree ≤ D - 1) :
    (linearFactor beta * R).natDegree ≤ D := by
  calc
    (linearFactor beta * R).natDegree ≤
        (linearFactor beta).natDegree + R.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + (D - 1) := by
      apply Nat.add_le_add
      · simp [linearFactor]
      · exact hR
    _ = D := by omega
theorem linearFactor_mul_injective
    {K : Type*} [Field K] (beta : K) :
    Function.Injective (fun R : Polynomial K => linearFactor beta * R) := by
  intro R Q hRQ
  exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero beta) hRQ
theorem weightedSyndrome_linearHilbertError
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (alpha f : I → K) (beta : K) (j : Nat) :
    BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha
        (linearHilbertError beta alpha f) j =
      BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f (j + 1) -
        beta * BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j := by
  classical
  simp only [BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome,
    linearHilbertError, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_succ]
  ring
theorem weightedSyndrome_fixed
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha f : I → K)
    (hfixedAlpha : ∀ i, sigma (alpha i) = alpha i)
    (hfixedWeight : ∀ i,
      sigma (BCHKSFrobeniusKeyEquationFork6401.syndromeWeight alpha i) =
        BCHKSFrobeniusKeyEquationFork6401.syndromeWeight alpha i)
    (hfixedF : ∀ i, sigma (f i) = f i) (j : Nat) :
    sigma (BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j) =
      BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j := by
  classical
  simp only [BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome, map_sum,
    map_mul, map_pow, hfixedWeight, hfixedAlpha, hfixedF]
theorem movingLinearFailureRelation_syndrome_normalForm
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha E : I → K) (beta : K)
    (hmove : beta ≠ sigma beta)
    (hfixedAlpha : ∀ i, sigma (alpha i) = alpha i)
    (hfixedWeight : ∀ i,
      sigma (BCHKSFrobeniusKeyEquationFork6401.syndromeWeight alpha i) =
        BCHKSFrobeniusKeyEquationFork6401.syndromeWeight alpha i)
    (hrel : ∀ i,
      (linearFactor beta).eval (alpha i) * sigma (E i) =
        (linearFactor (sigma beta)).eval (alpha i) * E i) :
    ∃ f : I → K,
      (∀ i, sigma (f i) = f i) ∧
      (∀ i, E i = (alpha i - beta) * f i) ∧
      (∀ i, E i = 0 ↔ f i = 0) ∧
      ∀ j : Nat,
        BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha E j =
          BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f (j + 1) -
            beta *
              BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j ∧
        sigma (BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j) =
          BCHKSFrobeniusKeyEquationFork6401.weightedSyndrome alpha f j := by
  let f : I → K := fun i => E i / (alpha i - beta)
  have hroot : ∀ i, alpha i ≠ beta := by
    intro i
    exact fixed_locator_ne_moving_root sigma beta (alpha i) hmove
      (hfixedAlpha i)
  have hffixed : ∀ i, sigma (f i) = f i := by
    intro i
    exact linearPair_relation_imp_normalized_fixed sigma beta (alpha i) (E i)
      hmove (hfixedAlpha i) (by simpa using hrel i)
  have hEfactor : ∀ i, E i = (alpha i - beta) * f i := by
    intro i
    dsimp [f]
    field_simp [sub_ne_zero.mpr (hroot i)]
  refine ⟨f, hffixed, hEfactor, ?_, ?_⟩
  · intro i
    rw [hEfactor i]
    simp only [mul_eq_zero, sub_ne_zero.mpr (hroot i), false_or]
  · intro j
    constructor
    · rw [show E = linearHilbertError beta alpha f by
        funext i
        exact (hEfactor i).trans (by rfl)]
      exact weightedSyndrome_linearHilbertError alpha f beta j
    · exact weightedSyndrome_fixed sigma alpha f hfixedAlpha
        hfixedWeight hffixed j
theorem fixed_pair_decomposition_unique
    {K : Type*} [Field K] (sigma : K →+* K) (beta : K)
    (hmove : beta ≠ sigma beta)
    (F0 F1 G0 G1 : K)
    (hF0 : sigma F0 = F0) (hF1 : sigma F1 = F1)
    (hG0 : sigma G0 = G0) (hG1 : sigma G1 = G1)
    (heq : F1 - beta * F0 = G1 - beta * G0) :
    F0 = G0 ∧ F1 = G1 := by
  have hsigmaEq := congrArg sigma heq
  simp only [map_sub, map_mul, hF0, hF1, hG0, hG1] at hsigmaEq
  have hprod : (beta - sigma beta) * (F0 - G0) = 0 := by
    linear_combination hsigmaEq - heq
  have hbeta : beta - sigma beta ≠ 0 := sub_ne_zero.mpr hmove
  have hF0G0 : F0 = G0 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hbeta)
  refine ⟨hF0G0, ?_⟩
  rw [hF0G0] at heq
  linear_combination heq
theorem sixLinearFactors_eq_imp_firstRoot
    {K : Type*} [Field K]
    (beta0 beta1 beta2 beta3 beta4 beta5 : K)
    (gamma0 gamma1 gamma2 gamma3 gamma4 gamma5 : K)
    (hprod :
      linearFactor beta0 * linearFactor beta1 * linearFactor beta2 *
          linearFactor beta3 * linearFactor beta4 * linearFactor beta5 =
        linearFactor gamma0 * linearFactor gamma1 * linearFactor gamma2 *
          linearFactor gamma3 * linearFactor gamma4 * linearFactor gamma5) :
    beta0 = gamma0 ∨ beta0 = gamma1 ∨ beta0 = gamma2 ∨
      beta0 = gamma3 ∨ beta0 = gamma4 ∨ beta0 = gamma5 := by
  have heval := congrArg (Polynomial.eval beta0) hprod
  have hzero :
      (beta0 - gamma0) * (beta0 - gamma1) * (beta0 - gamma2) *
          (beta0 - gamma3) * (beta0 - gamma4) * (beta0 - gamma5) = 0 := by
    simpa only [Polynomial.eval_mul, linearFactor_eval, sub_self, zero_mul]
      using heval.symm
  rcases mul_eq_zero.mp hzero with h01234 | h5
  · rcases mul_eq_zero.mp h01234 with h0123 | h4
    · rcases mul_eq_zero.mp h0123 with h012 | h3
      · rcases mul_eq_zero.mp h012 with h01 | h2
        · rcases mul_eq_zero.mp h01 with h0 | h1
          · exact Or.inl (sub_eq_zero.mp h0)
          · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
        · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (sub_eq_zero.mp h4)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (sub_eq_zero.mp h5)))))
theorem sixConjugateLinearNorms_eq_imp_orbit
    {K : Type*} [Field K] (sigma : K →+* K) (beta gamma : K)
    (hprod :
      linearFactor beta * linearFactor (sigma beta) *
          linearFactor (sigma (sigma beta)) *
          linearFactor (sigma (sigma (sigma beta))) *
          linearFactor (sigma (sigma (sigma (sigma beta)))) *
          linearFactor (sigma (sigma (sigma (sigma (sigma beta))))) =
        linearFactor gamma * linearFactor (sigma gamma) *
          linearFactor (sigma (sigma gamma)) *
          linearFactor (sigma (sigma (sigma gamma))) *
          linearFactor (sigma (sigma (sigma (sigma gamma)))) *
          linearFactor (sigma (sigma (sigma (sigma (sigma gamma)))))) :
    beta = gamma ∨ beta = sigma gamma ∨ beta = sigma (sigma gamma) ∨
      beta = sigma (sigma (sigma gamma)) ∨
      beta = sigma (sigma (sigma (sigma gamma))) ∨
      beta = sigma (sigma (sigma (sigma (sigma gamma)))) := by
  exact sixLinearFactors_eq_imp_firstRoot beta (sigma beta)
    (sigma (sigma beta)) (sigma (sigma (sigma beta)))
    (sigma (sigma (sigma (sigma beta))))
    (sigma (sigma (sigma (sigma (sigma beta)))))
    gamma (sigma gamma) (sigma (sigma gamma))
    (sigma (sigma (sigma gamma)))
    (sigma (sigma (sigma (sigma gamma))))
    (sigma (sigma (sigma (sigma (sigma gamma))))) hprod
def movingLinearPairConstraintMatrix
    {K : Type*} [Field K] (z w : K) : Matrix (Fin 3) (Fin 4) K :=
  ![![1, z, 0, 0], ![0, 0, 1, w], ![0, 1, 0, -1]]
def movingLinearPairKernel
    {K : Type*} [Field K] (z w : K) : Fin 4 → K :=
  ![-z, 1, -w, 1]
theorem movingLinearPairKernel_mulVec_eq_zero
    {K : Type*} [Field K] (z w : K) :
    (movingLinearPairConstraintMatrix z w).mulVec
      (movingLinearPairKernel z w) = 0 := by
  funext i
  fin_cases i <;>
    simp [movingLinearPairConstraintMatrix, movingLinearPairKernel,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
theorem movingLinearPairConstraint_kernel_eq_span
    {K : Type*} [Field K] (z w : K) (c : Fin 4 → K)
    (hc : (movingLinearPairConstraintMatrix z w).mulVec c = 0) :
    c = c 1 • movingLinearPairKernel z w := by
  have h0 : c 0 + z * c 1 = 0 := by
    simpa [movingLinearPairConstraintMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] using congrFun hc (0 : Fin 3)
  have h1 : c 2 + w * c 3 = 0 := by
    simpa [movingLinearPairConstraintMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] using congrFun hc (1 : Fin 3)
  have h2 : c 1 + -c 3 = 0 := by
    simpa [movingLinearPairConstraintMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] using congrFun hc (2 : Fin 3)
  funext j
  fin_cases j
  · simp [movingLinearPairKernel, Pi.smul_apply, smul_eq_mul]
    linear_combination h0
  · simp [movingLinearPairKernel, Pi.smul_apply, smul_eq_mul]
  · simp [movingLinearPairKernel, Pi.smul_apply, smul_eq_mul]
    linear_combination h1 + w * h2
  · simp [movingLinearPairKernel, Pi.smul_apply, smul_eq_mul]
    linear_combination -h2
theorem movingLinearPairKernel_ne_zero
    {K : Type*} [Field K] (z w : K) : movingLinearPairKernel z w ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  simpa [movingLinearPairKernel] using h1
theorem movingLinearPairKernel_on_frobeniusGraph
    {K : Type*} [Field K] (sigma : K →+* K) (z : K) :
    movingLinearPairKernel z (sigma z) = ![-z, 1, -(sigma z), 1] := by
  rfl
theorem linearHilbertError_affine_parameter
    {K I : Type*} [Field K]
    (beta0 beta1 z : K) (x f : I → K) (i : I) :
    linearHilbertError (beta0 + z * beta1) x f i =
      linearHilbertError beta0 x f i - z * (beta1 * f i) := by
  simp only [linearHilbertError]
  ring
end BCHKSFrobeniusLinearPairNoGo6401
end ProximityPrize.SubmissionLower
