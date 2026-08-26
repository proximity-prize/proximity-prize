import ProximityPrize.SubmissionLower.BCHKSFrobeniusLinearYFailureDivisibility6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusEndpointCommonKernel6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusLinearYFailureDivisibility6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSGaoSpecializationCore6400
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
theorem exists_commonKernel_of_two_rank_le6401
    {F Row0 Row1 : Type*} [Field F]
    (h : Nat)
    (M0 : Matrix Row0 (Fin (2 * h + 1)) F)
    (M1 : Matrix Row1 (Fin (2 * h + 1)) F)
    (hM0 : M0.rank ≤ h) (hM1 : M1.rank ≤ h) :
    ∃ v : Fin (2 * h + 1) → F,
      v ≠ 0 ∧ M0.mulVec v = 0 ∧ M1.mulVec v = 0 := by
  let K0 : Submodule F (Fin (2 * h + 1) → F) :=
    LinearMap.ker M0.mulVecLin
  let K1 : Submodule F (Fin (2 * h + 1) → F) :=
    LinearMap.ker M1.mulVecLin
  have hnull0 := rank_add_finrank_ker_mulVecLin M0
  have hnull1 := rank_add_finrank_ker_mulVecLin M1
  simp only [Fintype.card_fin] at hnull0 hnull1
  have hK0 : h + 1 ≤ Module.finrank F K0 := by
    dsimp only [K0]
    omega
  have hK1 : h + 1 ≤ Module.finrank F K1 := by
    dsimp only [K1]
    omega
  have hsup :
      Module.finrank F
          ((K0 ⊔ K1 : Submodule F (Fin (2 * h + 1) → F))) ≤
        2 * h + 1 := by
    calc
      Module.finrank F
            ((K0 ⊔ K1 : Submodule F (Fin (2 * h + 1) → F))) ≤
          Module.finrank F (Fin (2 * h + 1) → F) :=
        Submodule.finrank_le
          ((K0 ⊔ K1 : Submodule F (Fin (2 * h + 1) → F)))
      _ = 2 * h + 1 := by simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq K0 K1
  have hinf :
      0 < Module.finrank F
        ((K0 ⊓ K1 : Submodule F (Fin (2 * h + 1) → F))) := by
    omega
  have hne :
      (K0 ⊓ K1 : Submodule F (Fin (2 * h + 1) → F)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hinf
    simp at hinf
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hvne, ?_, ?_⟩
  · have hv0 : v ∈ K0 := (Submodule.mem_inf.mp hv).1
    simpa [K0, LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv0
  · have hv1 : v ∈ K1 := (Submodule.mem_inf.mp hv).2
    simpa [K1, LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv1
noncomputable def vectorPolynomial6401
    {F : Type*} [Field F] (N : Nat) (v : Fin N → F) : F[X] :=
  ((Polynomial.degreeLTEquiv F N).symm v).1
theorem vectorPolynomial_degree_lt6401
    {F : Type*} [Field F] (N : Nat) (v : Fin N → F) :
    (vectorPolynomial6401 N v).degree < N := by
  have h := ((Polynomial.degreeLTEquiv F N).symm v).2
  rw [Polynomial.mem_degreeLT] at h
  exact h
theorem vectorPolynomial_coeff6401
    {F : Type*} [Field F] (N : Nat) (v : Fin N → F) (c : Fin N) :
    (vectorPolynomial6401 N v).coeff c.1 = v c := by
  have h := LinearEquiv.apply_symm_apply (Polynomial.degreeLTEquiv F N) v
  exact congrFun h c
theorem vectorPolynomial_ne_zero6401
    {F : Type*} [Field F] (N : Nat) (v : Fin N → F) (hv : v ≠ 0) :
    vectorPolynomial6401 N v ≠ 0 := by
  intro hzero
  apply hv
  funext c
  simp only [Pi.zero_apply]
  rw [← vectorPolynomial_coeff6401 N v c, hzero, Polynomial.coeff_zero]
theorem vectorPolynomial_natDegree_lt6401
    {F : Type*} [Field F] (N : Nat) (v : Fin N → F) (hv : v ≠ 0) :
    (vectorPolynomial6401 N v).natDegree < N := by
  rw [Polynomial.natDegree_lt_iff_degree_lt
    (vectorPolynomial_ne_zero6401 N v hv)]
  exact vectorPolynomial_degree_lt6401 N v
noncomputable def productSyndromeShiftMatrix6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows shifts : Nat) (alpha y : ι → F) (B : F[X]) :
    Matrix (Fin rows) (Fin shifts) F :=
  fun i c ↦ weightedSyndrome alpha
    (fun x ↦ B.eval (alpha x) * y x) (i.1 + c.1)
theorem productSyndromeShiftMatrix_mulVec_coeff6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows shifts : Nat) (alpha y : ι → F) (B R : F[X])
    (hR : R.natDegree < shifts) :
    (productSyndromeShiftMatrix6401 rows shifts alpha y B).mulVec
        (polynomialCoefficientVector6401 shifts R) =
      fun i ↦ weightedSyndrome alpha
        (fun x ↦ (R * B).eval (alpha x) * y x) i.1 := by
  classical
  funext i
  simp only [productSyndromeShiftMatrix6401, Matrix.mulVec, dotProduct,
    polynomialCoefficientVector6401]
  rw [weightedSyndrome_coeff_convolution6401 alpha
    (fun x ↦ B.eval (alpha x) * y x) R shifts i.1 hR]
  congr 1
  funext x
  simp only [Polynomial.eval_mul]
  ring
theorem exists_commonProductRecurrence_of_endpointRanks6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows h : Nat) (alpha y0 y1 : ι → F) (B : F[X])
    (h0 : (productSyndromeShiftMatrix6401 rows (2 * h + 1)
      alpha y0 B).rank ≤ h)
    (h1 : (productSyndromeShiftMatrix6401 rows (2 * h + 1)
      alpha y1 B).rank ≤ h) :
    ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ 2 * h ∧
      (∀ j < rows, weightedSyndrome alpha
        (fun x ↦ (R * B).eval (alpha x) * y0 x) j = 0) ∧
      (∀ j < rows, weightedSyndrome alpha
        (fun x ↦ (R * B).eval (alpha x) * y1 x) j = 0) := by
  obtain ⟨v, hv, hv0, hv1⟩ :=
    exists_commonKernel_of_two_rank_le6401 h
      (productSyndromeShiftMatrix6401 rows (2 * h + 1) alpha y0 B)
      (productSyndromeShiftMatrix6401 rows (2 * h + 1) alpha y1 B) h0 h1
  let R : F[X] := vectorPolynomial6401 (2 * h + 1) v
  have hRne : R ≠ 0 := vectorPolynomial_ne_zero6401 (2 * h + 1) v hv
  have hRlt : R.natDegree < 2 * h + 1 :=
    vectorPolynomial_natDegree_lt6401 (2 * h + 1) v hv
  have hcoeff : polynomialCoefficientVector6401 (2 * h + 1) R = v := by
    funext c
    exact vectorPolynomial_coeff6401 (2 * h + 1) v c
  have hz0 : ∀ j < rows, weightedSyndrome alpha
      (fun x ↦ (R * B).eval (alpha x) * y0 x) j = 0 := by
    intro j hj
    have hmul := productSyndromeShiftMatrix_mulVec_coeff6401
      rows (2 * h + 1) alpha y0 B R hRlt
    have hj0 := congrFun hmul ⟨j, hj⟩
    rw [hcoeff, hv0] at hj0
    exact hj0.symm
  have hz1 : ∀ j < rows, weightedSyndrome alpha
      (fun x ↦ (R * B).eval (alpha x) * y1 x) j = 0 := by
    intro j hj
    have hmul := productSyndromeShiftMatrix_mulVec_coeff6401
      rows (2 * h + 1) alpha y1 B R hRlt
    have hj0 := congrFun hmul ⟨j, hj⟩
    rw [hcoeff, hv1] at hj0
    exact hj0.symm
  exact ⟨R, hRne, by omega, hz0, hz1⟩
theorem endpointCommonRecurrence_budget6401
    (h : Nat) (hh : h ≤ 5626) :
    65536 + 2 * h < keyErrors6401 := by
  norm_num [keyErrors6401, keyRedundancy6401,
    BCHKSTwoFrobeniusModuleAudit6401.n6401,
    bchksErrors6401]
  omega
theorem endpointCommonRecurrence_boundary5627_6401 :
    65536 + 2 * 5627 = keyErrors6401 := by
  norm_num [keyErrors6401, keyRedundancy6401,
    BCHKSTwoFrobeniusModuleAudit6401.n6401,
    bchksErrors6401]
theorem exists_commonEndpointHankelKernel_shiftBudget6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (h : Nat) (hh : h ≤ 5626) (alpha y0 y1 : ι → F) (B : F[X])
    (hB : B.natDegree ≤ 65536)
    (h0 : (productSyndromeShiftMatrix6401 keyFirstLaneRows6401
      (2 * h + 1) alpha y0 B).rank ≤ h)
    (h1 : (productSyndromeShiftMatrix6401 keyFirstLaneRows6401
      (2 * h + 1) alpha y1 B).rank ≤ h) :
    ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ 2 * h ∧
      (R * B).natDegree < keyErrors6401 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        alpha y0).mulVec
          (polynomialCoefficientVector6401 keyErrors6401 (R * B)) = 0 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        alpha y1).mulVec
          (polynomialCoefficientVector6401 keyErrors6401 (R * B)) = 0 := by
  obtain ⟨R, hRne, hRdegree, hz0, hz1⟩ :=
    exists_commonProductRecurrence_of_endpointRanks6401
      keyFirstLaneRows6401 h alpha y0 y1 B h0 h1
  have hRB : (R * B).natDegree < keyErrors6401 := by
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    exact (Nat.add_le_add hRdegree hB).trans_lt
      (by simpa [Nat.add_comm] using endpointCommonRecurrence_budget6401 h hh)
  refine ⟨R, hRne, hRdegree, hRB, ?_, ?_⟩
  · exact weightedSyndromeHankel_mulVec_coeff6401
      keyFirstLaneRows6401 keyErrors6401 alpha y0 (R * B) hRB hz0
  · exact weightedSyndromeHankel_mulVec_coeff6401
      keyFirstLaneRows6401 keyErrors6401 alpha y1 (R * B) hRB hz1
theorem exists_commonEndpointHankelKernel_boundary5627_6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha y0 y1 : ι → F) (B : F[X])
    (hB : B.natDegree ≤ 65535)
    (h0 : (productSyndromeShiftMatrix6401 keyFirstLaneRows6401
      (2 * 5627 + 1) alpha y0 B).rank ≤ 5627)
    (h1 : (productSyndromeShiftMatrix6401 keyFirstLaneRows6401
      (2 * 5627 + 1) alpha y1 B).rank ≤ 5627) :
    ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ 2 * 5627 ∧
      (R * B).natDegree < keyErrors6401 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        alpha y0).mulVec
          (polynomialCoefficientVector6401 keyErrors6401 (R * B)) = 0 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        alpha y1).mulVec
          (polynomialCoefficientVector6401 keyErrors6401 (R * B)) = 0 := by
  obtain ⟨R, hRne, hRdegree, hz0, hz1⟩ :=
    exists_commonProductRecurrence_of_endpointRanks6401
      keyFirstLaneRows6401 5627 alpha y0 y1 B h0 h1
  have hRB : (R * B).natDegree < keyErrors6401 := by
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    norm_num [keyErrors6401, keyRedundancy6401,
      BCHKSTwoFrobeniusModuleAudit6401.n6401,
      bchksErrors6401] at hRdegree hB ⊢
    omega
  refine ⟨R, hRne, hRdegree, hRB, ?_, ?_⟩
  · exact weightedSyndromeHankel_mulVec_coeff6401
      keyFirstLaneRows6401 keyErrors6401 alpha y0 (R * B) hRB hz0
  · exact weightedSyndromeHankel_mulVec_coeff6401
      keyFirstLaneRows6401 keyErrors6401 alpha y1 (R * B) hRB hz1
end BCHKSFrobeniusEndpointCommonKernel6401
end ProximityPrize.SubmissionLower
