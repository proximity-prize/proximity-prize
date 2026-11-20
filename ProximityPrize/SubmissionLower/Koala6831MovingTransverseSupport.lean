import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import ProximityPrize.SubmissionLower.Koala6831MovingTransverseChange


namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped Pointwise

theorem natDegree_aeval_le_weightedTotalDegree
    {σ K E : Type*} [CommSemiring K] [CommSemiring E] [Algebra K E]
    (weights : σ → ℕ) (values : σ → Polynomial E) (F : MvPolynomial σ K)
    (hvalues : ∀ i, (values i).natDegree ≤ weights i) :
    (MvPolynomial.aeval values F).natDegree ≤ F.weightedTotalDegree weights := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le F.support _ fun d hd => ?_
  rw [Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  have hweight := MvPolynomial.le_weightedTotalDegree weights hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hweight
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hweight
  simpa only [nsmul_eq_mul, Nat.cast_id] using
    (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d i) (hvalues i)) :
      (values i ^ d i).natDegree ≤ d i * weights i)

section CoefficientBounds

variable {τ E : Type*} [CommSemiring E]

private noncomputable def weightedBox (weights : τ → ℕ) (cap : ℕ) : Submodule E (MvPolynomial τ E) :=
  MvPolynomial.restrictSupport E {d | Finsupp.weight weights d ≤ cap}

private theorem mem_weightedBox_iff {weights : τ → ℕ} {cap : ℕ} {F : MvPolynomial τ E} :
    F ∈ weightedBox weights cap ↔ F.weightedTotalDegree weights ≤ cap := by
  change (∀ d ∈ F.support, Finsupp.weight weights d ≤ cap) ↔ _
  exact Finset.sup_le_iff.symm

private theorem weightedBox_mono (weights : τ → ℕ) {a b : ℕ} (h : a ≤ b) :
    (weightedBox weights a : Submodule E (MvPolynomial τ E)) ≤ weightedBox weights b :=
  MvPolynomial.restrictSupport_mono (R := E) fun _ hd => le_trans hd h

private theorem mul_mem_weightedBox (weights : τ → ℕ) {a b : ℕ} {f g : MvPolynomial τ E}
    (hf : f ∈ weightedBox weights a) (hg : g ∈ weightedBox weights b) :
    f * g ∈ weightedBox weights (a + b) := by
  have hset : {d : τ →₀ ℕ | Finsupp.weight weights d ≤ a} +
      {d : τ →₀ ℕ | Finsupp.weight weights d ≤ b} ⊆
        {d : τ →₀ ℕ | Finsupp.weight weights d ≤ a + b} := by
    rintro _ ⟨d, hd, e, he, rfl⟩
    simpa only [Set.mem_ofPred_eq, map_add] using Nat.add_le_add hd he
  apply MvPolynomial.restrictSupport_mono (R := E) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hf hg

private def coefficientsIn (weights : τ → ℕ) (cap : ℕ) (p : Polynomial (MvPolynomial τ E)) : Prop :=
  ∀ j, p.coeff j ∈ weightedBox weights cap

private theorem coefficientsIn_C (weights : τ → ℕ) (c : E) :
    coefficientsIn weights 0 (Polynomial.C (MvPolynomial.C c)) := by
  classical
  intro j
  apply mem_weightedBox_iff.mpr
  by_cases hj : j = 0
  · subst j
    by_cases hc : c = 0 <;> simp [MvPolynomial.weightedTotalDegree, MvPolynomial.support_C, hc]
  · simp [Polynomial.coeff_C, hj, MvPolynomial.weightedTotalDegree_zero]

private theorem coefficientsIn_mul (weights : τ → ℕ) {a b : ℕ} {p q : Polynomial (MvPolynomial τ E)}
    (hp : coefficientsIn weights a p) (hq : coefficientsIn weights b q) :
    coefficientsIn weights (a + b) (p * q) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact (weightedBox weights (a + b)).sum_mem fun ij _ => mul_mem_weightedBox weights (hp ij.1) (hq ij.2)

private theorem coefficientsIn_pow (weights : τ → ℕ) {cap : ℕ} {p : Polynomial (MvPolynomial τ E)}
    (hp : coefficientsIn weights cap p) (n : ℕ) : coefficientsIn weights (n * cap) (p ^ n) := by
  induction n with
  | zero => simpa using coefficientsIn_C weights (1 : E)
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact coefficientsIn_mul weights ih hp

private theorem coefficientsIn_prod (weights : τ → ℕ) {ι : Type*} (s : Finset ι)
    (values : ι → Polynomial (MvPolynomial τ E)) (caps : ι → ℕ)
    (hvalues : ∀ i ∈ s, coefficientsIn weights (caps i) (values i)) :
    coefficientsIn weights (∑ i ∈ s, caps i) (∏ i ∈ s, values i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefficientsIn_C weights (1 : E)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact coefficientsIn_mul weights (hvalues i (Finset.mem_insert_self i s))
      (ih fun j hj => hvalues j (Finset.mem_insert_of_mem hj))

theorem coeff_weightedTotalDegree_aeval_le
    {σ K : Type*} [CommSemiring K] [Algebra K E]
    (weights : σ → ℕ) (coefficientWeights : τ → ℕ)
    (values : σ → Polynomial (MvPolynomial τ E)) (F : MvPolynomial σ K)
    (hvalues : ∀ i j, ((values i).coeff j).weightedTotalDegree coefficientWeights ≤ weights i)
    (j : ℕ) :
    ((MvPolynomial.aeval values F).coeff j).weightedTotalDegree coefficientWeights ≤
      F.weightedTotalDegree weights := by
  classical
  apply mem_weightedBox_iff.mp
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply (weightedBox coefficientWeights (F.weightedTotalDegree weights)).sum_mem
  intro d hd
  have hterm := coefficientsIn_prod coefficientWeights d.support (fun i => values i ^ d i)
    (fun i => d i * weights i) fun i _ => coefficientsIn_pow coefficientWeights
      (fun k => mem_weightedBox_iff.mpr (hvalues i k)) (d i)
  have hdegree := MvPolynomial.le_weightedTotalDegree weights hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hdegree
  simp only [nsmul_eq_mul, Nat.cast_id] at hdegree
  apply weightedBox_mono coefficientWeights hdegree
  rw [Polynomial.algebraMap_apply, IsScalarTower.algebraMap_apply K E (MvPolynomial τ E),
    MvPolynomial.algebraMap_eq]
  simpa only [Nat.zero_add] using
    coefficientsIn_mul coefficientWeights (coefficientsIn_C coefficientWeights (algebraMap K E (F.coeff d))) hterm j

end CoefficientBounds

namespace FlowData

variable {K : Type*} [Field K]

private theorem natDegree_normalizedAffine_le (f g : Polynomial K) :
    (normalizedAffine f g).natDegree ≤ 1 := by
  simp only [normalizedAffine, xPolynomial_apply]
  rw [mul_comm (Polynomial.X : NormalizedPoly K), add_comm]
  exact Polynomial.natDegree_linear_le

theorem normalize_natDegree_le (B : FlowData K) (F : P4 K) :
    (B.normalize F).natDegree ≤ F.weightedTotalDegree ![0, 1, 1, 1] := by
  have hY : B.normalizedY.natDegree ≤ 1 := by
    unfold normalizedY normalizedInvD0 normalizedValue
    rw [Polynomial.algebraMap_apply]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (natDegree_normalizedAffine_le _ _))
    exact (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_normalizedAffine_le _ _)
  have hR : B.normalizedR.natDegree ≤ 1 := by
    unfold normalizedR normalizedInvD0
    rw [Polynomial.algebraMap_apply]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    apply (Polynomial.natDegree_sub_le _ _).trans
    refine max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (natDegree_normalizedAffine_le _ _))) ?_
    · unfold normalizedValue normalizedFirstJet
      apply Polynomial.natDegree_add_le_of_degree_le <;>
        exact (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_normalizedAffine_le _ _)
    · rw [xPolynomial_apply]
      exact (Polynomial.natDegree_C_mul_le _ _).trans hY
  apply natDegree_aeval_le_weightedTotalDegree
  intro i
  fin_cases i <;> simp [normalizedCoordinates, xPolynomial_apply, hY, hR]

private theorem coefficientsIn_xPolynomial (weights : Fin 2 → ℕ) (f : Polynomial K) :
    coefficientsIn weights 0 (xPolynomial K f) := by
  rw [xPolynomial_apply]
  exact coefficientsIn_C weights _

private theorem coefficientsIn_add (weights : Fin 2 → ℕ) {cap : ℕ} {p q : NormalizedPoly K}
    (hp : coefficientsIn weights cap p) (hq : coefficientsIn weights cap q) :
    coefficientsIn weights cap (p + q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (weightedBox weights cap).add_mem (hp j) (hq j)

private theorem coefficientsIn_sub (weights : Fin 2 → ℕ) {cap : ℕ} {p q : NormalizedPoly K}
    (hp : coefficientsIn weights cap p) (hq : coefficientsIn weights cap q) :
    coefficientsIn weights cap (p - q) := by
  intro j
  rw [Polynomial.coeff_sub]
  exact (weightedBox weights cap : Submodule (RatFunc K) (NormalizedCoeff K)).sub_mem (hp j) (hq j)

private theorem coefficientsIn_X (weights : Fin 2 → ℕ) :
    coefficientsIn weights 0 (Polynomial.X : NormalizedPoly K) := by
  intro j
  rw [Polynomial.coeff_X]
  split_ifs
  · simpa using coefficientsIn_C weights (1 : RatFunc K) 0
  · exact (weightedBox weights 0).zero_mem

private theorem coefficientsIn_normalizedAffine (weights : Fin 2 → ℕ) (f g : Polynomial K) :
    coefficientsIn weights 0 (normalizedAffine f g) := by
  unfold normalizedAffine
  exact coefficientsIn_add weights (coefficientsIn_xPolynomial weights f)
    (coefficientsIn_mul weights (coefficientsIn_X weights) (coefficientsIn_xPolynomial weights g))

private theorem coefficientsIn_C_X (weights : Fin 2 → ℕ) (i : Fin 2) :
    coefficientsIn weights (weights i) (Polynomial.C (MvPolynomial.X i) : NormalizedPoly K) := by
  classical
  intro j
  apply mem_weightedBox_iff.mpr
  by_cases hj : j = 0
  · subst j
    simp [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X, Finsupp.weight_single]
  · simp [Polynomial.coeff_C, hj, MvPolynomial.weightedTotalDegree_zero]

theorem normalize_coeff_weightedTotalDegree_le (B : FlowData K) (F : P4 K)
    (weights : Fin 2 → ℕ) (hweights : weights 0 ≤ weights 1) (j : ℕ) :
    ((B.normalize F).coeff j).weightedTotalDegree weights ≤
      F.weightedTotalDegree ![0, weights 0, weights 1, 0] := by
  have hInvD0 : coefficientsIn weights 0 B.normalizedInvD0 := by
    unfold normalizedInvD0
    rw [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    exact coefficientsIn_C weights _
  have hValue : coefficientsIn weights (weights 0) (normalizedValue K) := coefficientsIn_C_X weights 0
  have hJet : coefficientsIn weights (weights 1) (normalizedFirstJet K) := coefficientsIn_C_X weights 1
  have liftBound {p q : NormalizedPoly K} {cap : ℕ}
      (hp : coefficientsIn weights 0 p) (hq : coefficientsIn weights cap q) :
      coefficientsIn weights cap (p * q) := by
    simpa only [Nat.zero_add] using coefficientsIn_mul weights hp hq
  have weaken {p : NormalizedPoly K} {a b : ℕ} (h : a ≤ b) (hp : coefficientsIn weights a p) :
      coefficientsIn weights b p := fun k => weightedBox_mono weights h (hp k)
  have hY : coefficientsIn weights (weights 0) B.normalizedY := by
    unfold normalizedY
    exact liftBound hInvD0 (coefficientsIn_sub weights
      (liftBound (coefficientsIn_normalizedAffine weights _ _) hValue)
      (weaken (Nat.zero_le _) (coefficientsIn_normalizedAffine weights _ _)))
  have hR : coefficientsIn weights (weights 1) B.normalizedR := by
    unfold normalizedR
    exact liftBound hInvD0 (coefficientsIn_sub weights
      (coefficientsIn_sub weights
        (coefficientsIn_add weights
          (liftBound (coefficientsIn_normalizedAffine weights _ _) hJet)
          (weaken hweights (liftBound (coefficientsIn_normalizedAffine weights _ _) hValue)))
        (weaken (Nat.zero_le _) (coefficientsIn_normalizedAffine weights _ _)))
      (weaken hweights (liftBound (coefficientsIn_xPolynomial weights _) hY)))
  refine coeff_weightedTotalDegree_aeval_le _ weights B.normalizedCoordinates F ?_ j
  intro i k
  apply mem_weightedBox_iff.mp
  fin_cases i
  · simpa [normalizedCoordinates] using coefficientsIn_xPolynomial weights Polynomial.X k
  · simpa [normalizedCoordinates] using hY k
  · simpa [normalizedCoordinates] using hR k
  · simpa [normalizedCoordinates] using coefficientsIn_X weights k

end FlowData

end ProximityPrize.SubmissionLower.Koala6831Moving
