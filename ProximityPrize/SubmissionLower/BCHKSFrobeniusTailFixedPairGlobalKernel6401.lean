import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailFailureSpace6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailFixedPairGlobalKernel6401
open Polynomial
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailKernelSufficiency6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section FixedPair
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
def leftTailVector6401 {d : Nat}
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    Fin (d + 1) ⊕ Fin (d + 1) → F
  | Sum.inl j => v (Sum.inl j)
  | Sum.inr _ => 0
def rightTailVector6401 {d : Nat}
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    Fin (d + 1) ⊕ Fin (d + 1) → F
  | Sum.inl _ => 0
  | Sum.inr j => v (Sum.inr j)
theorem tailPairPolynomial_leftTailVector6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    tailPairPolynomial d (leftTailVector6401 v) =
      ((tailPairPolynomial d v).1, 0) := by
  classical
  apply Prod.ext
  · rfl
  · simp [tailPairPolynomial, leftTailVector6401]
theorem tailPairPolynomial_rightTailVector6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    tailPairPolynomial d (rightTailVector6401 v) =
      (0, (tailPairPolynomial d v).2) := by
  classical
  apply Prod.ext
  · simp [tailPairPolynomial, rightTailVector6401]
  · rfl
theorem receivedTailMatrixZ_mulVec_C_expand6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (r : Fin (Fintype.card I - (k + d + 1))) :
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec
        (fun c ↦ Polynomial.C (v c)) r =
      Polynomial.C
          ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) +
        Polynomial.X ^ q * Polynomial.C
          ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
            (leftTailVector6401 v) r) +
        Polynomial.X * Polynomial.C
          ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
            (rightTailVector6401 v) r) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    receivedTailMatrixZ6401, leftTailVector6401, rightTailVector6401,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [map_add, map_sum, map_mul]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [map_zero, mul_zero, add_zero]
  ring
theorem receivedTailMatrixZ_mulVec_C_natDegree_le6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (hq : 1 ≤ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (r : Fin (Fintype.card I - (k + d + 1))) :
    ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec
      (fun c ↦ Polynomial.C (v c)) r).natDegree ≤ q := by
  classical
  unfold Matrix.mulVec dotProduct
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro c hc
  apply Polynomial.natDegree_mul_le.trans
  cases c with
  | inl j =>
      simpa using
        (receivedTailMatrixZ_entry_natDegree_le6401
          sigma alpha u₀ u₁ q k d r (Sum.inl j))
  | inr j =>
      have hentry := receivedTailMatrixZ_entry_natDegree_le6401
        sigma alpha u₀ u₁ q k d r (Sum.inr j)
      simpa using hentry.trans hq
theorem receivedTailMatrixZ_mulVec_C_eq_zero_of_fixedKernels6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (hq : 1 ≤ q) (S : Finset F)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec v = 0)
    (hmass : q < S.card) :
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec
      (fun c ↦ Polynomial.C (v c)) = 0 := by
  classical
  funext r
  let R : F[X] :=
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec
      (fun c ↦ Polynomial.C (v c)) r
  have hdegree : R.natDegree < S.card := by
    exact (receivedTailMatrixZ_mulVec_C_natDegree_le6401
      sigma alpha u₀ u₁ q k d hq v r).trans_lt hmass
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    R S ?_ hdegree
  intro z hz
  let M := receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d
  let ev := Polynomial.evalRingHom z
  have hspecialized : (M.map ev).mulVec v = 0 := by
    rw [receivedTailMatrixZ_eval6401
      sigma alpha u₀ u₁ q k d z (hsigma z hz)]
    exact hkernel z hz
  have hconstant : ev ∘ (fun c ↦ Polynomial.C (v c)) = v := by
    funext c
    simp [ev]
  have heval : ev (M.mulVec (fun c ↦ Polynomial.C (v c)) r) = 0 := by
    rw [RingHom.map_mulVec]
    rw [hconstant]
    exact congrFun hspecialized r
  change Polynomial.eval z R = 0
  exact heval
theorem receivedTail_fixedPair_threeKernels_of_graphKernel6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (hq : 1 < q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hglobal :
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec
        (fun c ↦ Polynomial.C (v c)) = 0) :
    (receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v = 0 ∧
      (receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
          (leftTailVector6401 v) = 0 ∧
        (receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
          (rightTailVector6401 v) = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hq1 : q ≠ 1 := by omega
  have h0q : 0 ≠ q := Ne.symm hq0
  have h1q : 1 ≠ q := Ne.symm hq1
  constructor
  · funext r
    have hrow :
        Polynomial.C
            ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) +
          Polynomial.X ^ q * Polynomial.C
            ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
              (leftTailVector6401 v) r) +
          Polynomial.X * Polynomial.C
            ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
              (rightTailVector6401 v) r) = 0 := by
      rw [← receivedTailMatrixZ_mulVec_C_expand6401
        sigma alpha u₀ u₁ q k d v r]
      exact congrFun hglobal r
    have hrow' :
        Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (leftTailVector6401 v) r) * Polynomial.X ^ q +
            Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (rightTailVector6401 v) r) * Polynomial.X +
          Polynomial.C
            ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) =
            0 := by
      linear_combination hrow
    have hcoeff := congrArg (fun P : F[X] ↦ P.coeff 0) hrow'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      if_neg h0q, if_neg (by norm_num : 0 ≠ 1), if_pos rfl,
      zero_add, add_zero, Polynomial.coeff_zero] at hcoeff
    exact hcoeff
  · constructor
    · funext r
      have hrow :
          Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) +
            Polynomial.X ^ q * Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (leftTailVector6401 v) r) +
            Polynomial.X * Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (rightTailVector6401 v) r) = 0 := by
        rw [← receivedTailMatrixZ_mulVec_C_expand6401
          sigma alpha u₀ u₁ q k d v r]
        exact congrFun hglobal r
      have hrow' :
          Polynomial.C
                ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                  (leftTailVector6401 v) r) * Polynomial.X ^ q +
              Polynomial.C
                ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                  (rightTailVector6401 v) r) * Polynomial.X +
            Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) =
              0 := by
        linear_combination hrow
      have hcoeff := congrArg (fun P : F[X] ↦ P.coeff q) hrow'
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_pos rfl, if_neg hq1, if_neg hq0,
        zero_add, add_zero, Polynomial.coeff_zero] at hcoeff
      exact hcoeff
    · funext r
      have hrow :
          Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) +
            Polynomial.X ^ q * Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (leftTailVector6401 v) r) +
            Polynomial.X * Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                (rightTailVector6401 v) r) = 0 := by
        rw [← receivedTailMatrixZ_mulVec_C_expand6401
          sigma alpha u₀ u₁ q k d v r]
        exact congrFun hglobal r
      have hrow' :
          Polynomial.C
                ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                  (leftTailVector6401 v) r) * Polynomial.X ^ q +
              Polynomial.C
                ((receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
                  (rightTailVector6401 v) r) * Polynomial.X +
            Polynomial.C
              ((receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v r) =
              0 := by
        linear_combination hrow
      have hcoeff := congrArg (fun P : F[X] ↦ P.coeff 1) hrow'
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg h1q, if_pos rfl, if_neg (by norm_num : 1 ≠ 0),
        zero_add, add_zero, Polynomial.coeff_zero] at hcoeff
      exact hcoeff
theorem receivedTail_fixedPair_threeKernels_of_manyOwners6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (hq : 1 < q) (S : Finset F)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec v = 0)
    (hmass : q < S.card) :
    (receivedTailMatrix6401 sigma alpha u₀ k d).mulVec v = 0 ∧
      (receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
          (leftTailVector6401 v) = 0 ∧
        (receivedTailMatrix6401 sigma alpha u₁ k d).mulVec
          (rightTailVector6401 v) = 0 := by
  apply receivedTail_fixedPair_threeKernels_of_graphKernel6401
    sigma alpha u₀ u₁ q k d hq v
  exact receivedTailMatrixZ_mulVec_C_eq_zero_of_fixedKernels6401
    sigma alpha u₀ u₁ q k d (by omega) S hsigma v hkernel hmass
theorem receivedTail_fixedPair_threeProductDegrees_of_manyOwners6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (hq : 1 < q) (S : Finset F)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec v = 0)
    (hmass : q < S.card) (hwindow : k + d < Fintype.card I) :
    (receivedPairInterpolant6401 sigma alpha u₀
        (tailPairPolynomial d v).1 (tailPairPolynomial d v).2).natDegree
          ≤ k + d ∧
      (receivedPairInterpolant6401 sigma alpha u₁
        (tailPairPolynomial d v).1 0).natDegree
          ≤ k + d ∧
      (receivedPairInterpolant6401 sigma alpha u₁
        0 (tailPairPolynomial d v).2).natDegree
          ≤ k + d := by
  have hkernels := receivedTail_fixedPair_threeKernels_of_manyOwners6401
    sigma alpha u₀ u₁ q k d hq S hsigma v hkernel hmass
  have hbase := (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha u₀ k d v hwindow).mp hkernels.1
  have hleft := (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha u₁ k d (leftTailVector6401 v) hwindow).mp hkernels.2.1
  have hright := (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha u₁ k d (rightTailVector6401 v) hwindow).mp hkernels.2.2
  rw [tailPairPolynomial_leftTailVector6401] at hleft
  rw [tailPairPolynomial_rightTailVector6401] at hright
  exact ⟨hbase, hleft, hright⟩
end FixedPair
end BCHKSFrobeniusTailFixedPairGlobalKernel6401
end ProximityPrize.SubmissionLower
