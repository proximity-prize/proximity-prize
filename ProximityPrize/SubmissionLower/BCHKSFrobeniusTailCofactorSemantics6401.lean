import ProximityPrize.SubmissionLower.BCHKSFrobeniusReceivedTailMatrix6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailCofactorSemantics6401
open Polynomial
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section Generic
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
theorem globalTailKernel_specializes6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hglobal :
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0)
    (z : F) (hz : sigma z = z ^ q) :
    (receivedTailMatrix6401 sigma alpha
      (fun i ↦ u₀ i + z * u₁ i) k d).mulVec
        (fun c ↦ Polynomial.eval z (V c)) = 0 := by
  let ev := Polynomial.evalRingHom z
  have hmap :
      ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).map ev).mulVec
        (ev ∘ V) = 0 := by
    funext r
    rw [← RingHom.map_mulVec]
    rw [hglobal]
    simp
  rw [receivedTailMatrixZ_eval6401 sigma alpha u₀ u₁ q k d z hz]
    at hmap
  change (receivedTailMatrix6401 sigma alpha
    (fun i ↦ u₀ i + z * u₁ i) k d).mulVec
      (fun c ↦ Polynomial.eval z (V c)) = 0 at hmap
  exact hmap
theorem tailPairPolynomial_pair_ne_zero_of_vector_ne_zero6401
    (d : Nat) (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (hv : v ≠ 0) :
    (tailPairPolynomial d v).1 ≠ 0 ∨
      (tailPairPolynomial d v).2 ≠ 0 := by
  by_contra hpair
  push Not at hpair
  apply hv
  funext c
  cases c with
  | inl j =>
      have hc := congrArg (fun Q : F[X] ↦ Q.coeff (j : Nat)) hpair.1
      simp only [tailPairPolynomial, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
      rw [Finset.sum_eq_single j] at hc
      · simpa using hc
      · intro i _hi hij
        have hnat : (j : Nat) ≠ (i : Nat) :=
          fun h ↦ hij (Fin.ext h.symm)
        simp [hnat]
      · simp
  | inr j =>
      have hc := congrArg (fun Q : F[X] ↦ Q.coeff (j : Nat)) hpair.2
      simp only [tailPairPolynomial, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
      rw [Finset.sum_eq_single j] at hc
      · simpa using hc
      · intro i _hi hij
        have hnat : (j : Nat) ≠ (i : Nat) :=
          fun h ↦ hij (Fin.ext h.symm)
        simp [hnat]
      · simp
theorem failureRelation_of_globalTailKernel_specialization6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hglobal :
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0)
    (z : F) (hz : sigma z = z ^ q)
    (P : F[X]) (agreements : Finset I)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements,
      P.eval (alpha i) = u₀ i + z * u₁ i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card) :
    let v : Fin (d + 1) ⊕ Fin (d + 1) → F :=
      fun c ↦ Polynomial.eval z (V c)
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u₀ i + z * u₁ i - P.eval (alpha i))
      (tailPairPolynomial d v).1 (tailPairPolynomial d v).2 := by
  dsimp only
  apply failureRelation_of_receivedTailMatrix_kernel6401
    sigma alpha (fun i ↦ u₀ i + z * u₁ i) P agreements k d
      (fun c ↦ Polynomial.eval z (V c)) hfixed hagree hPdegree
      hwindow hroots
  exact globalTailKernel_specializes6401 sigma alpha u₀ u₁ q k d V
    hglobal z hz
theorem exists_nonzero_failurePair_of_globalTailKernel6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hglobal :
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0)
    (z : F) (hz : sigma z = z ^ q)
    (hVnonzero : (fun c ↦ Polynomial.eval z (V c)) ≠ 0)
    (P : F[X]) (agreements : Finset I)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements,
      P.eval (alpha i) = u₀ i + z * u₁ i)
    (hPdegree : P.natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card) :
    ∃ A B : F[X],
      (A ≠ 0 ∨ B ≠ 0) ∧
      A.natDegree ≤ d ∧ B.natDegree ≤ d ∧
      TwoLaneFailureRelation sigma alpha
        (fun i ↦ u₀ i + z * u₁ i - P.eval (alpha i)) A B := by
  let v : Fin (d + 1) ⊕ Fin (d + 1) → F :=
    fun c ↦ Polynomial.eval z (V c)
  let A := (tailPairPolynomial d v).1
  let B := (tailPairPolynomial d v).2
  have hpair : A ≠ 0 ∨ B ≠ 0 :=
    tailPairPolynomial_pair_ne_zero_of_vector_ne_zero6401 d v hVnonzero
  refine ⟨A, B, hpair, tailPairPolynomial_fst_natDegree_le d v,
    tailPairPolynomial_snd_natDegree_le d v, ?_⟩
  exact failureRelation_of_globalTailKernel_specialization6401
    sigma alpha u₀ u₁ q k d V hglobal z hz P agreements hfixed
      hagree hPdegree hwindow hroots
end Generic
theorem globalTailKernel_benchmark_margins6401 :
    ownerDegreeCap6401 + 22507 < n6401 ∧
      ownerDegreeCap6401 + 22507 < a6401 := by
  native_decide
end BCHKSFrobeniusTailCofactorSemantics6401
end ProximityPrize.SubmissionLower
