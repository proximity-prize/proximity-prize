import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailKernelSufficiency6401
import ProximityPrize.SubmissionLower.BCHKSLinearYLowSupport6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusGraphInjectivity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusReceivedTailMatrix6401
open Polynomial
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSLinearYLowSupport6401
open BCHKSFrobeniusGraphInjectivity6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section Generic
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
noncomputable def tailPairPolynomial (d : Nat)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    F[X] × F[X] :=
  (∑ j : Fin (d + 1), Polynomial.C (v (Sum.inl j)) *
      Polynomial.X ^ (j : Nat),
    ∑ j : Fin (d + 1), Polynomial.C (v (Sum.inr j)) *
      Polynomial.X ^ (j : Nat))
theorem tailPairPolynomial_fst_natDegree_le
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    (tailPairPolynomial d v).1.natDegree ≤ d := by
  classical
  unfold tailPairPolynomial
  dsimp only
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro j hj
  exact Polynomial.natDegree_C_mul_X_pow_le (v (Sum.inl j))
    (j : Nat) |>.trans (Nat.le_of_lt_succ j.isLt)
theorem tailPairPolynomial_snd_natDegree_le
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    (tailPairPolynomial d v).2.natDegree ≤ d := by
  classical
  unfold tailPairPolynomial
  dsimp only
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro j hj
  exact Polynomial.natDegree_C_mul_X_pow_le (v (Sum.inr j))
    (j : Nat) |>.trans (Nat.le_of_lt_succ j.isLt)
noncomputable def receivedTailMatrix6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (k d : Nat) :
    Matrix (Fin (Fintype.card I - (k + d + 1)))
      (Fin (d + 1) ⊕ Fin (d + 1)) F
  | r, Sum.inl j =>
      (receivedPairInterpolant6401 sigma alpha u
        (Polynomial.X ^ (j : Nat)) 0).coeff (k + d + 1 + (r : Nat))
  | r, Sum.inr j =>
      (receivedPairInterpolant6401 sigma alpha u
        0 (Polynomial.X ^ (j : Nat))).coeff (k + d + 1 + (r : Nat))
theorem receivedPairInterpolant_tailPairPolynomial6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F) :
    receivedPairInterpolant6401 sigma alpha u
        (tailPairPolynomial d v).1 (tailPairPolynomial d v).2 =
      (∑ j : Fin (d + 1),
        Polynomial.C (v (Sum.inl j)) *
          receivedPairInterpolant6401 sigma alpha u
            (Polynomial.X ^ (j : Nat)) 0) +
      (∑ j : Fin (d + 1),
        Polynomial.C (v (Sum.inr j)) *
          receivedPairInterpolant6401 sigma alpha u
            0 (Polynomial.X ^ (j : Nat))) := by
  classical
  let L := Lagrange.interpolate (Finset.univ : Finset I) alpha
  change L (fun i ↦
      (tailPairPolynomial d v).1.eval (alpha i) * sigma (u i) -
        (tailPairPolynomial d v).2.eval (alpha i) * u i) = _
  have hCsmul (c : F) (Q : F[X]) : Polynomial.C c * Q = c • Q := by
    simp [Algebra.smul_def]
  simp_rw [hCsmul]
  change L _ =
    (∑ j ∈ (Finset.univ : Finset (Fin (d + 1))), v (Sum.inl j) •
      L (fun i ↦ (Polynomial.X ^ (j : Nat)).eval (alpha i) *
        sigma (u i) - (0 : F[X]).eval (alpha i) * u i)) +
    (∑ j ∈ (Finset.univ : Finset (Fin (d + 1))), v (Sum.inr j) •
      L (fun i ↦ (0 : F[X]).eval (alpha i) * sigma (u i) -
        (Polynomial.X ^ (j : Nat)).eval (alpha i) * u i))
  simp_rw [← L.map_smul]
  rw [← map_sum, ← map_sum, ← map_add]
  congr 1
  funext i
  simp only [tailPairPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_zero, zero_mul, sub_zero]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [sub_eq_add_neg]
  apply congrArg₂ (fun a b : F ↦ a + b)
  · apply Finset.sum_congr rfl
    intro x hx
    ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
theorem receivedTailMatrix_mulVec_eq_coeff6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (k d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (r : Fin (Fintype.card I - (k + d + 1))) :
    (receivedTailMatrix6401 sigma alpha u k d).mulVec v r =
      (receivedPairInterpolant6401 sigma alpha u
        (tailPairPolynomial d v).1 (tailPairPolynomial d v).2).coeff
          (k + d + 1 + (r : Nat)) := by
  classical
  unfold receivedTailMatrix6401 Matrix.mulVec dotProduct
  rw [Fintype.sum_sum_type]
  rw [receivedPairInterpolant_tailPairPolynomial6401]
  rw [Polynomial.coeff_add]
  simp_rw [← Polynomial.lcoeff_apply]
  rw [map_sum, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul]
  simp only [mul_comm]
theorem receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (k d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hwindow : k + d < Fintype.card I) :
    (receivedTailMatrix6401 sigma alpha u k d).mulVec v = 0 ↔
      (receivedPairInterpolant6401 sigma alpha u
        (tailPairPolynomial d v).1 (tailPairPolynomial d v).2).natDegree
          ≤ k + d := by
  classical
  let R := receivedPairInterpolant6401 sigma alpha u
    (tailPairPolynomial d v).1 (tailPairPolynomial d v).2
  rw [funext_iff]
  constructor
  · intro hzero
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_cases hncard : n < Fintype.card I
    · have hbase : k + d + 1 ≤ n := by omega
      let r : Fin (Fintype.card I - (k + d + 1)) :=
        ⟨n - (k + d + 1), by omega⟩
      have hr :
          (receivedTailMatrix6401 sigma alpha u k d).mulVec v r = 0 := by
        simpa using hzero r
      rw [receivedTailMatrix_mulVec_eq_coeff6401] at hr
      have hrval : k + d + 1 + (n - (k + d + 1)) = n := by
        omega
      change R.coeff n = 0
      simpa only [R, r, hrval] using hr
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((receivedPairInterpolant_natDegree_lt_card6401 sigma alpha u
          (tailPairPolynomial d v).1 (tailPairPolynomial d v).2).trans_le
            (Nat.le_of_not_gt hncard))
  · intro hdegree r
    rw [receivedTailMatrix_mulVec_eq_coeff6401]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
theorem tailPairVector_ne_zero_of_pair_ne_zero6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hpair : (tailPairPolynomial d v).1 ≠ 0 ∨
      (tailPairPolynomial d v).2 ≠ 0) :
    v ≠ 0 := by
  intro hv
  subst v
  simp [tailPairPolynomial] at hpair
theorem failureRelation_of_receivedTailMatrix_kernel6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (P : F[X]) (agreements : Finset I) (k d : Nat)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card)
    (hkernel : (receivedTailMatrix6401 sigma alpha u k d).mulVec v = 0) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u i - P.eval (alpha i))
      (tailPairPolynomial d v).1 (tailPairPolynomial d v).2 := by
  apply (receivedPairInterpolant_degree_iff_failureRelation6401
    sigma alpha u P (tailPairPolynomial d v).1
      (tailPairPolynomial d v).2 agreements k d hfixed hagree hPdegree
      (tailPairPolynomial_fst_natDegree_le d v)
      (tailPairPolynomial_snd_natDegree_le d v) hwindow hroots).mp
  exact (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha u k d v hwindow).mp hkernel
theorem receivedPairInterpolant_left_affine6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (A : F[X]) (z : F) :
    receivedPairInterpolant6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) A 0 =
      receivedPairInterpolant6401 sigma alpha u₀ A 0 +
        Polynomial.C (sigma z) *
          receivedPairInterpolant6401 sigma alpha u₁ A 0 := by
  classical
  unfold receivedPairInterpolant6401
  let L := Lagrange.interpolate (Finset.univ : Finset I) alpha
  change L _ = L _ + Polynomial.C (sigma z) * L _
  have hCsmul (c : F) (Q : F[X]) : Polynomial.C c * Q = c • Q := by
    simp [Algebra.smul_def]
  rw [hCsmul, ← L.map_smul, ← L.map_add]
  congr 1
  funext i
  simp only [map_add, map_mul, Polynomial.eval_zero, zero_mul, sub_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem receivedPairInterpolant_right_affine6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (B : F[X]) (z : F) :
    receivedPairInterpolant6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) 0 B =
      receivedPairInterpolant6401 sigma alpha u₀ 0 B +
        Polynomial.C z *
          receivedPairInterpolant6401 sigma alpha u₁ 0 B := by
  classical
  unfold receivedPairInterpolant6401
  let L := Lagrange.interpolate (Finset.univ : Finset I) alpha
  change L _ = L _ + Polynomial.C z * L _
  have hCsmul (c : F) (Q : F[X]) : Polynomial.C c * Q = c • Q := by
    simp [Algebra.smul_def]
  rw [hCsmul, ← L.map_smul, ← L.map_add]
  congr 1
  funext i
  simp only [map_add, map_mul, Polynomial.eval_zero, zero_mul, zero_sub,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
noncomputable def receivedTailMatrixZ6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) :
    Matrix (Fin (Fintype.card I - (k + d + 1)))
      (Fin (d + 1) ⊕ Fin (d + 1)) F[X]
  | r, Sum.inl j =>
      Polynomial.C ((receivedTailMatrix6401 sigma alpha u₀ k d) r
        (Sum.inl j)) +
      Polynomial.X ^ q *
        Polynomial.C ((receivedTailMatrix6401 sigma alpha u₁ k d) r
          (Sum.inl j))
  | r, Sum.inr j =>
      Polynomial.C ((receivedTailMatrix6401 sigma alpha u₀ k d) r
        (Sum.inr j)) +
      Polynomial.X *
        Polynomial.C ((receivedTailMatrix6401 sigma alpha u₁ k d) r
          (Sum.inr j))
theorem receivedTailMatrixZ_entry_natDegree_le6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) :
    ∀ r c, (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d r c).natDegree
      ≤ Sum.elim (fun _ : Fin (d + 1) ↦ q)
        (fun _ : Fin (d + 1) ↦ 1) c := by
  intro r c
  cases c with
  | inl j =>
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
  | inr j =>
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
theorem receivedTailMatrixZ_eval6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (z : F) (hz : sigma z = z ^ q) :
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).map
        (Polynomial.evalRingHom z) =
      receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d := by
  ext r c
  cases c with
  | inl j =>
      have h := congrArg
        (fun Q : F[X] ↦ Q.coeff (k + d + 1 + (r : Nat)))
        (receivedPairInterpolant_left_affine6401
          sigma alpha u₀ u₁ (Polynomial.X ^ (j : Nat)) z)
      change Polynomial.eval z
          (Polynomial.C ((receivedTailMatrix6401 sigma alpha u₀ k d) r
              (Sum.inl j)) +
            Polynomial.X ^ q *
              Polynomial.C ((receivedTailMatrix6401 sigma alpha u₁ k d) r
                (Sum.inl j))) =
        (receivedTailMatrix6401 sigma alpha
          (fun i ↦ u₀ i + z * u₁ i) k d) r (Sum.inl j)
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← hz]
      simpa only [receivedTailMatrix6401, Polynomial.coeff_add,
        Polynomial.coeff_C_mul] using h.symm
  | inr j =>
      have h := congrArg
        (fun Q : F[X] ↦ Q.coeff (k + d + 1 + (r : Nat)))
        (receivedPairInterpolant_right_affine6401
          sigma alpha u₀ u₁ (Polynomial.X ^ (j : Nat)) z)
      change Polynomial.eval z
          (Polynomial.C ((receivedTailMatrix6401 sigma alpha u₀ k d) r
              (Sum.inr j)) +
            Polynomial.X *
              Polynomial.C ((receivedTailMatrix6401 sigma alpha u₁ k d) r
                (Sum.inr j))) =
        (receivedTailMatrix6401 sigma alpha
          (fun i ↦ u₀ i + z * u₁ i) k d) r (Sum.inr j)
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
      simpa only [receivedTailMatrix6401, Polynomial.coeff_add,
        Polynomial.coeff_C_mul] using h.symm
theorem receivedTailMinor_eval_det_zero_of_ownerKernel6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (z : F) (hz : sigma z = z ^ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F) (hv : v ≠ 0)
    (hkernel : (receivedTailMatrix6401 sigma alpha
      (fun i ↦ u₀ i + z * u₁ i) k d).mulVec v = 0)
    (rows : Fin (d + 1) ⊕ Fin (d + 1) →
      Fin (Fintype.card I - (k + d + 1))) :
    (((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
      rows id).map (Polynomial.evalRingHom z)).det = 0 := by
  let M := ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
    rows id).map (Polynomial.evalRingHom z)
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (v := v) (i := Classical.choose (Function.ne_iff.mp hv))
  · funext r
    have hmatrix := receivedTailMatrixZ_eval6401
      sigma alpha u₀ u₁ q k d z hz
    have hM : M = (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).submatrix rows id := by
      ext i j
      exact congrArg (fun N ↦ N (rows i) j) hmatrix
    change M.mulVec v r = 0
    rw [hM]
    change (receivedTailMatrix6401 sigma alpha
      (fun i ↦ u₀ i + z * u₁ i) k d).mulVec v (rows r) = 0
    simpa using congrFun hkernel (rows r)
  · exact mem_nonZeroDivisors_of_ne_zero
      (Classical.choose_spec (Function.ne_iff.mp hv))
theorem receivedTailColumnCaps_sum6401 (q d : Nat) :
    (∑ c : Fin (d + 1) ⊕ Fin (d + 1),
      Sum.elim (fun _ : Fin (d + 1) ↦ q)
        (fun _ : Fin (d + 1) ↦ 1) c) = (d + 1) * (q + 1) := by
  rw [Fintype.sum_sum_type]
  simp
  ring
theorem receivedTailMinor_eq_zero_of_many_ownerKernels6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (S : Finset F)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (kernel : F → (Fin (d + 1) ⊕ Fin (d + 1) → F))
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec (kernel z) = 0)
    (hnonzero : ∀ z ∈ S, kernel z ≠ 0)
    (hmass : (d + 1) * (q + 1) < S.card)
    (rows : Fin (d + 1) ⊕ Fin (d + 1) →
      Fin (Fintype.card I - (k + d + 1))) :
    ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
      rows id).det = 0 := by
  classical
  let M := (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
    rows id
  by_contra hdet
  have hcap := polynomialMinor_rootCap M
    (Sum.elim (fun _ : Fin (d + 1) ↦ q)
      (fun _ : Fin (d + 1) ↦ 1))
    (fun r c ↦ receivedTailMatrixZ_entry_natDegree_le6401
      sigma alpha u₀ u₁ q k d (rows r) c)
    hdet S (fun z hz ↦ by
      simpa only [M] using
        receivedTailMinor_eval_det_zero_of_ownerKernel6401
        sigma alpha u₀ u₁ q k d z (hsigma z hz) (kernel z)
          (hnonzero z hz) (hkernel z hz) rows)
  rw [receivedTailColumnCaps_sum6401] at hcap
  omega
noncomputable def receivedTailMatrixZW6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (k d : Nat) :
    Matrix (Fin (Fintype.card I - (k + d + 1)))
      (Fin (d + 1) ⊕ Fin (d + 1)) F[X][X]
  | r, Sum.inl j =>
      Polynomial.C (Polynomial.C
        ((receivedTailMatrix6401 sigma alpha u₀ k d) r (Sum.inl j))) +
      Polynomial.X * Polynomial.C (Polynomial.C
        ((receivedTailMatrix6401 sigma alpha u₁ k d) r (Sum.inl j)))
  | r, Sum.inr j =>
      Polynomial.C
        (Polynomial.C
          ((receivedTailMatrix6401 sigma alpha u₀ k d) r (Sum.inr j)) +
        Polynomial.X * Polynomial.C
          ((receivedTailMatrix6401 sigma alpha u₁ k d) r (Sum.inr j)))
theorem receivedTailMatrixZW_graph6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) :
    (receivedTailMatrixZW6401 sigma alpha u₀ u₁ k d).map
        (frobeniusGraphRingHom q) =
      receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d := by
  ext r c
  cases c <;>
    simp [receivedTailMatrixZW6401, receivedTailMatrixZ6401,
      frobeniusGraphRingHom, Polynomial.C_mul_X_pow_eq_monomial]
theorem receivedTailMatrixZW_entry_coeffDegree_le_one6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (k d : Nat) :
    ∀ r c, BivariateCoeffDegreeLE
      (receivedTailMatrixZW6401 sigma alpha u₀ u₁ k d r c) 1 := by
  intro r c j
  cases c with
  | inl c =>
      by_cases hj0 : j = 0
      · subst j
        simp [receivedTailMatrixZW6401]
      · by_cases hj1 : j = 1
        · subst j
          simp [receivedTailMatrixZW6401]
        · simp [receivedTailMatrixZW6401, Polynomial.coeff_C,
            Polynomial.coeff_X, hj0, hj1, Ne.symm hj1]
  | inr c =>
      by_cases hj0 : j = 0
      · subst j
        rw [receivedTailMatrixZW6401, Polynomial.coeff_C_zero]
        apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · simp
        · exact Polynomial.natDegree_mul_le.trans (by simp)
      · simp [receivedTailMatrixZW6401, Polynomial.coeff_C, hj0]
theorem receivedTailIndependentMinor_eq_zero6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat)
    (hsize : Fintype.card (Fin (d + 1) ⊕ Fin (d + 1)) < q)
    (rows : Fin (d + 1) ⊕ Fin (d + 1) →
      Fin (Fintype.card I - (k + d + 1)))
    (hzero :
      ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
        rows id).det = 0) :
    ((receivedTailMatrixZW6401 sigma alpha u₀ u₁ k d).submatrix
      rows id).det = 0 := by
  classical
  let M := (receivedTailMatrixZW6401 sigma alpha u₀ u₁ k d).submatrix
    rows id
  apply frobeniusGraphEval_eq_zero_imp_eq_zero q M.det
  · have hdet := bivariateCoeffDegree_det_le_sum_rowCaps M
        (fun _ ↦ 1) (by
          intro i j
          exact receivedTailMatrixZW_entry_coeffDegree_le_one6401
            sigma alpha u₀ u₁ k d (rows i) j)
    intro j
    exact (hdet j).trans_lt (by simpa using hsize)
  · change frobeniusGraphRingHom q M.det = 0
    rw [RingHom.map_det]
    have hgraph := receivedTailMatrixZW_graph6401
      sigma alpha u₀ u₁ q k d
    have hminor : (frobeniusGraphRingHom q).mapMatrix M =
        (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
          rows id := by
      apply Matrix.ext
      intro i j
      exact congrArg (fun N ↦ N (rows i) j) hgraph
    rw [hminor, hzero]
end Generic
def receivedTailRows6401 (d : Nat) : Nat :=
  n6401 - (ownerDegreeCap6401 + d + 1)
def receivedTailColumns6401 (d : Nat) : Nat := 2 * (d + 1)
theorem receivedTail_benchmark_maxWindow6401 :
    receivedTailRows6401 22507 = 108565 ∧
      receivedTailColumns6401 22507 = 45016 ∧
      receivedTailColumns6401 22507 < receivedTailRows6401 22507 := by
  native_decide
theorem receivedTail_benchmark_graphMinorCap6401 :
    (22507 + 1) * (q6401 + 1) = 47957940416472 ∧
      47957940416472 < 80251881527475554 := by
  native_decide
end BCHKSFrobeniusReceivedTailMatrix6401
end ProximityPrize.SubmissionLower
