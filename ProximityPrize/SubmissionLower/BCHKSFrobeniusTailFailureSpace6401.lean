import ProximityPrize.SubmissionLower.BCHKSFrobeniusReceivedTailMatrix6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusMomentRecoveryBoundary6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailFailureSpace6401
open Polynomial
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusMomentRecoveryBoundary6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section CoefficientEncoding
variable {F : Type*} [Field F]
noncomputable def boundedPairTailEquiv6401 (d : Nat) :
    (Polynomial.degreeLT F (d + 1) × Polynomial.degreeLT F (d + 1)) ≃ₗ[F]
      (Fin (d + 1) ⊕ Fin (d + 1) → F) :=
  ((Polynomial.degreeLTEquiv F (d + 1)).prodCongr
      (Polynomial.degreeLTEquiv F (d + 1))).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (Fin (d + 1)) (Fin (d + 1)) F F).symm
theorem boundedPairTailEquiv_apply_inl6401
    (d : Nat)
    (Q : Polynomial.degreeLT F (d + 1) ×
      Polynomial.degreeLT F (d + 1))
    (j : Fin (d + 1)) :
    boundedPairTailEquiv6401 d Q (Sum.inl j) = Q.1.1.coeff j.1 := by
  simp [boundedPairTailEquiv6401, Polynomial.degreeLTEquiv]
theorem boundedPairTailEquiv_apply_inr6401
    (d : Nat)
    (Q : Polynomial.degreeLT F (d + 1) ×
      Polynomial.degreeLT F (d + 1))
    (j : Fin (d + 1)) :
    boundedPairTailEquiv6401 d Q (Sum.inr j) = Q.2.1.coeff j.1 := by
  simp [boundedPairTailEquiv6401, Polynomial.degreeLTEquiv]
theorem tailPairPolynomial_fst_coeff_general6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (j : Fin (d + 1)) :
    (tailPairPolynomial d v).1.coeff j.1 = v (Sum.inl j) := by
  classical
  simp [tailPairPolynomial]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hbj
    rw [if_neg]
    intro heq
    exact hbj (Fin.ext heq.symm)
theorem tailPairPolynomial_snd_coeff_general6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (j : Fin (d + 1)) :
    (tailPairPolynomial d v).2.coeff j.1 = v (Sum.inr j) := by
  classical
  simp [tailPairPolynomial]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hbj
    rw [if_neg]
    intro heq
    exact hbj (Fin.ext heq.symm)
theorem degreeLT_natDegree_le6401
    (d : Nat) (Q : Polynomial.degreeLT F (d + 1)) :
    Q.1.natDegree ≤ d := by
  by_cases hQ : Q.1 = 0
  · simp [hQ]
  · rw [← Nat.lt_succ_iff]
    apply (Polynomial.natDegree_lt_iff_degree_lt hQ).2
    simpa only [Polynomial.mem_degreeLT] using Q.2
theorem tailPairPolynomial_boundedPairTailEquiv6401
    (d : Nat)
    (Q : Polynomial.degreeLT F (d + 1) ×
      Polynomial.degreeLT F (d + 1)) :
    tailPairPolynomial d (boundedPairTailEquiv6401 d Q) =
      (Q.1.1, Q.2.1) := by
  apply Prod.ext
  · apply Polynomial.ext
    intro n
    by_cases hn : n < d + 1
    · let j : Fin (d + 1) := ⟨n, hn⟩
      rw [show n = j.1 by rfl,
        tailPairPolynomial_fst_coeff_general6401,
        boundedPairTailEquiv_apply_inl6401]
    · have hn' : d < n := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt
            (tailPairPolynomial_fst_natDegree_le d
              (boundedPairTailEquiv6401 d Q)) hn'),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (degreeLT_natDegree_le6401 d Q.1) hn')]
  · apply Polynomial.ext
    intro n
    by_cases hn : n < d + 1
    · let j : Fin (d + 1) := ⟨n, hn⟩
      rw [show n = j.1 by rfl,
        tailPairPolynomial_snd_coeff_general6401,
        boundedPairTailEquiv_apply_inr6401]
    · have hn' : d < n := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt
            (tailPairPolynomial_snd_natDegree_le d
              (boundedPairTailEquiv6401 d Q)) hn'),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (degreeLT_natDegree_le6401 d Q.2) hn')]
end CoefficientEncoding
section SemanticInjection
variable {F I V : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
noncomputable def failurePairSpaceToTailKernel6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (P : F[X]) (agreements : Finset I) (k d : Nat)
    (pair : V →ₗ[F]
      (Polynomial.degreeLT F (d + 1) ×
        Polynomial.degreeLT F (d + 1)))
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card)
    (hfailure : ∀ v,
      TwoLaneFailureRelation sigma alpha
        (fun i ↦ u i - P.eval (alpha i))
        (pair v).1.1 (pair v).2.1) :
    V →ₗ[F] LinearMap.ker
      (receivedTailMatrix6401 sigma alpha u k d).mulVecLin where
  toFun v := ⟨boundedPairTailEquiv6401 d (pair v), by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      receivedTailMatrix_mulVec_eq_zero_iff_degree6401
        sigma alpha u k d _ hwindow]
    have hiff := receivedPairInterpolant_degree_iff_failureRelation6401
      sigma alpha u P (pair v).1.1 (pair v).2.1 agreements k d
      hfixed hagree hPdegree
      (degreeLT_natDegree_le6401 d (pair v).1)
      (degreeLT_natDegree_le6401 d (pair v).2)
      hwindow hroots
    rw [tailPairPolynomial_boundedPairTailEquiv6401]
    exact hiff.mpr (hfailure v)⟩
  map_add' v w := by
    apply Subtype.ext
    simp
  map_smul' c v := by
    apply Subtype.ext
    simp
theorem semanticTail_kernel_finrank_ge_of_failurePairSpace6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (P : F[X]) (agreements : Finset I) (k d : Nat)
    (pair : V →ₗ[F]
      (Polynomial.degreeLT F (d + 1) ×
        Polynomial.degreeLT F (d + 1)))
    (hpair : Function.Injective pair)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card)
    (hfailure : ∀ v,
      TwoLaneFailureRelation sigma alpha
        (fun i ↦ u i - P.eval (alpha i))
        (pair v).1.1 (pair v).2.1) :
    Module.finrank F V ≤ Module.finrank F
      (LinearMap.ker
        (receivedTailMatrix6401 sigma alpha u k d).mulVecLin) := by
  let f := failurePairSpaceToTailKernel6401 sigma alpha u P agreements k d pair
    hfixed hagree hPdegree hwindow hroots hfailure
  have hf : Function.Injective f := by
    intro v w hvw
    apply hpair
    apply (boundedPairTailEquiv6401 d).injective
    exact congrArg Subtype.val hvw
  exact LinearMap.finrank_le_finrank_of_injective hf
theorem semanticTail_rank_le_two_mul_degree_of_failurePairSpace6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (P : F[X]) (agreements : Finset I) (k d : Nat)
    (pair : V →ₗ[F]
      (Polynomial.degreeLT F (d + 1) ×
        Polynomial.degreeLT F (d + 1)))
    (hpair : Function.Injective pair)
    (hV : 2 ≤ Module.finrank F V)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card)
    (hfailure : ∀ v,
      TwoLaneFailureRelation sigma alpha
        (fun i ↦ u i - P.eval (alpha i))
        (pair v).1.1 (pair v).2.1) :
    (receivedTailMatrix6401 sigma alpha u k d).rank ≤ 2 * d := by
  have hker : 2 ≤ Module.finrank F
      (LinearMap.ker
        (receivedTailMatrix6401 sigma alpha u k d).mulVecLin) :=
    hV.trans (semanticTail_kernel_finrank_ge_of_failurePairSpace6401
      sigma alpha u P agreements k d pair hpair hfixed hagree hPdegree
      hwindow hroots hfailure)
  have hdim :=
    BCHKSGaoSpecializationCore6400.rank_add_finrank_ker_mulVecLin
      (receivedTailMatrix6401 sigma alpha u k d)
  simp only [Fintype.card_sum, Fintype.card_fin] at hdim
  omega
end SemanticInjection
theorem hardCone_forces_nullity_ge_two6401
    (h delta : Nat)
    (hsupportWindow : h + delta ≤ 22508)
    (hhard : 22510 ≤ h + 2 * delta) :
    2 ≤ delta := by
  omega
theorem nullity_one_forces_longMomentCone6401
    (h delta : Nat)
    (hdelta : delta = 1)
    (hsupportWindow : h + delta ≤ 22508) :
    h + 2 * delta ≤ 22509 := by
  omega
end BCHKSFrobeniusTailFailureSpace6401
end ProximityPrize.SubmissionLower
