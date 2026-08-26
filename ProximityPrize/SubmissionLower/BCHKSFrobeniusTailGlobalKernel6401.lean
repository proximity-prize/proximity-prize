import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailCofactorSemantics6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailGlobalKernel6401
open Polynomial
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailCofactorSemantics6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSMixedHermiteRowSpan6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section RationalClearing
variable {F C : Type*} [Field F] [Fintype C] [DecidableEq C]
noncomputable def tailKernelCommonDenominator6401
    (g : C → RatFunc F) : F[X] :=
  ∏ c, (g c).denom
noncomputable def clearTailKernelCoordinate6401
    (g : C → RatFunc F) (c : C) : F[X] :=
  (g c).num * ∏ j ∈ Finset.univ.erase c, (g j).denom
theorem algebraMap_clearTailKernelCoordinate6401
    (g : C → RatFunc F) (c : C) :
    algebraMap F[X] (RatFunc F) (clearTailKernelCoordinate6401 g c) =
      algebraMap F[X] (RatFunc F)
          (tailKernelCommonDenominator6401 g) * g c := by
  have hden : tailKernelCommonDenominator6401 g = (g c).denom *
      ∏ j ∈ Finset.univ.erase c, (g j).denom := by
    exact (Finset.mul_prod_erase Finset.univ (fun j ↦ (g j).denom)
      (Finset.mem_univ c)).symm
  rw [hden, map_mul]
  simp only [clearTailKernelCoordinate6401, map_mul, map_prod]
  let N := algebraMap F[X] (RatFunc F) (g c).num
  let D := algebraMap F[X] (RatFunc F) (g c).denom
  let E := ∏ x ∈ Finset.univ.erase c,
    algebraMap F[X] (RatFunc F) (g x).denom
  change N * E = (D * E) * g c
  have hD : D ≠ 0 := by
    intro hzero
    exact RatFunc.denom_ne_zero (g c)
      (RatFunc.algebraMap_injective F (by simpa [D] using hzero))
  have hg : N / D = g c := by
    simpa [N, D] using RatFunc.num_div_denom (g c)
  rw [← hg]
  field_simp [hD]
theorem tailKernelCommonDenominator_ne_zero6401
    (g : C → RatFunc F) : tailKernelCommonDenominator6401 g ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c hc
  exact RatFunc.denom_ne_zero (g c)
theorem clearTailKernelCoordinate_ne_zero6401
    (g : C → RatFunc F) (hg : ∃ c, g c ≠ 0) :
    clearTailKernelCoordinate6401 g ≠ 0 := by
  obtain ⟨c, hc⟩ := hg
  intro hv
  have hvc : clearTailKernelCoordinate6401 g c = 0 := congrFun hv c
  have hm := algebraMap_clearTailKernelCoordinate6401 g c
  rw [hvc, map_zero] at hm
  have hmd : algebraMap F[X] (RatFunc F)
      (tailKernelCommonDenominator6401 g) ≠ 0 := by
    intro hd
    exact tailKernelCommonDenominator_ne_zero6401 g
      (RatFunc.algebraMap_injective F (by simpa using hd))
  exact (mul_ne_zero hmd hc) hm.symm
theorem clearTailKernel_mulVec_eq_zero6401
    {R : Type*} [Fintype R]
    (M : Matrix R C F[X]) (g : C → RatFunc F)
    (hg : (M.map (algebraMap F[X] (RatFunc F))).mulVec g = 0) :
    M.mulVec (clearTailKernelCoordinate6401 g) = 0 := by
  funext r
  apply RatFunc.algebraMap_injective F
  rw [RingHom.map_mulVec]
  have hv : (algebraMap F[X] (RatFunc F)) ∘
        clearTailKernelCoordinate6401 g =
      (algebraMap F[X] (RatFunc F)
        (tailKernelCommonDenominator6401 g)) • g := by
    funext c
    simpa [Function.comp_apply, smul_eq_mul] using
      algebraMap_clearTailKernelCoordinate6401 g c
  rw [hv, Matrix.mulVec_smul, hg]
  simp
theorem exists_polynomialKernel_of_all_maximalMinors_zero6401
    {R : Type*} [Fintype R] [DecidableEq R]
    (M : Matrix R C F[X])
    (hminor : ∀ rows : C → R, (M.submatrix rows id).det = 0) :
    ∃ v : C → F[X], v ≠ 0 ∧ M.mulVec v = 0 := by
  let mapP := algebraMap F[X] (RatFunc F)
  let MR := M.map mapP
  have hdep : ¬ LinearIndependent (RatFunc F) MR.col := by
    intro hli
    have hrow : LinearIndependent (RatFunc F) MR.transpose.row := by
      simpa [Matrix.transpose_apply] using hli
    obtain ⟨rows, hdet⟩ :=
      exists_columns_det_ne_zero_of_rows_linearIndependent MR.transpose hrow
    apply hdet
    have hz := hminor rows
    have hmap : mapP ((M.submatrix rows id).det) =
        ((MR.transpose.submatrix id rows).det) := by
      rw [RingHom.map_det]
      rw [← Matrix.det_transpose]
      congr 1
    rw [hz, map_zero] at hmap
    exact hmap.symm
  obtain ⟨g, hg, hgnz⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hsys : MR.mulVec g = 0 := by
    funext r
    have hr := congrFun hg r
    simpa [MR, Matrix.mulVec, dotProduct, Matrix.col_apply,
      Finset.sum_apply, smul_eq_mul, mul_comm] using hr
  exact ⟨clearTailKernelCoordinate6401 g,
    clearTailKernelCoordinate_ne_zero6401 g hgnz,
    clearTailKernel_mulVec_eq_zero6401 M g hsys⟩
end RationalClearing
section ReceivedTail
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
theorem exists_globalTailKernel_of_many_ownerKernels6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat) (S : Finset F)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (kernel : F → (Fin (d + 1) ⊕ Fin (d + 1) → F))
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec (kernel z) = 0)
    (hnonzero : ∀ z ∈ S, kernel z ≠ 0)
    (hmass : (d + 1) * (q + 1) < S.card) :
    ∃ V : Fin (d + 1) ⊕ Fin (d + 1) → F[X],
      V ≠ 0 ∧
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0 := by
  classical
  apply exists_polynomialKernel_of_all_maximalMinors_zero6401
  intro rows
  exact receivedTailMinor_eq_zero_of_many_ownerKernels6401
    sigma alpha u₀ u₁ q k d S hsigma kernel hkernel hnonzero hmass rows
theorem exists_globalTailKernel_with_ownerSemantics6401
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
    (P : F → F[X]) (agreements : F → Finset I)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ z ∈ S, ∀ i ∈ agreements z,
      (P z).eval (alpha i) = u₀ i + z * u₁ i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : ∀ z ∈ S, k + d < (agreements z).card) :
    ∃ V : Fin (d + 1) ⊕ Fin (d + 1) → F[X],
      V ≠ 0 ∧
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0 ∧
      ∀ z ∈ S,
        (fun c ↦ Polynomial.eval z (V c)) ≠ 0 →
        ∃ A B : F[X],
          (A ≠ 0 ∨ B ≠ 0) ∧ A.natDegree ≤ d ∧
          B.natDegree ≤ d ∧
          TwoLaneFailureRelation sigma alpha
            (fun i ↦ u₀ i + z * u₁ i - (P z).eval (alpha i)) A B := by
  obtain ⟨V, hV, hVK⟩ := exists_globalTailKernel_of_many_ownerKernels6401
    sigma alpha u₀ u₁ q k d S hsigma kernel hkernel hnonzero hmass
  refine ⟨V, hV, hVK, ?_⟩
  intro z hz hVz
  exact exists_nonzero_failurePair_of_globalTailKernel6401
    sigma alpha u₀ u₁ q k d V hVK z (hsigma z hz) hVz
      (P z) (agreements z) hfixed (hagree z hz)
      (hPdegree z hz) hwindow (hroots z hz)
end ReceivedTail
end BCHKSFrobeniusTailGlobalKernel6401
end ProximityPrize.SubmissionLower
