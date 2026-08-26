import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericMinor6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusDeltaOneCofactor6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGenericMinor6401
open BCHKSGaoSpecializationCore6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section AbstractCofactor
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
def cramerRelationMatrix {R J : Type*} [CommRing R]
    [Fintype J] [DecidableEq J] (A : Matrix J J R) (b : J → R) :
    Matrix J (J ⊕ Unit) R
  | i, Sum.inl j => A i j
  | i, Sum.inr _ => -b i
noncomputable def cramerKernelVector {R J : Type*} [CommRing R]
    [Fintype J] [DecidableEq J] (A : Matrix J J R) (b : J → R) :
    J ⊕ Unit → R
  | Sum.inl j => A.cramer b j
  | Sum.inr _ => A.det
theorem cramerRelationMatrix_mulVec_cramerKernelVector
    (A : Matrix I I F) (b : I → F) :
    (cramerRelationMatrix A b).mulVec (cramerKernelVector A b) = 0 := by
  classical
  ext i
  have hcramer := congrFun (Matrix.mulVec_cramer A b) i
  change (∑ x : I ⊕ Unit,
    cramerRelationMatrix A b i x * cramerKernelVector A b x) = (0 : F)
  rw [Fintype.sum_sum_type]
  simp only [cramerRelationMatrix, cramerKernelVector,
    Finset.univ_unique, Finset.sum_singleton]
  change A.mulVec (A.cramer b) i + -b i * A.det = 0
  rw [hcramer]
  simp [smul_eq_mul, mul_comm]
theorem cramerKernelVector_ne_zero (A : Matrix I I F) (b : I → F)
    (hdet : A.det ≠ 0) : cramerKernelVector A b ≠ 0 := by
  intro hzero
  have := congrFun hzero (Sum.inr ())
  exact hdet (by simpa [cramerKernelVector] using this)
theorem det_smul_eq_last_smul_cramerKernelVector
    (A : Matrix I I F) (b : I → F) (v : I ⊕ Unit → F)
    (hdet : A.det ≠ 0)
    (hv : (cramerRelationMatrix A b).mulVec v = 0) :
    A.det • v = v (Sum.inr ()) • cramerKernelVector A b := by
  classical
  let vLeft : I → F := fun j => v (Sum.inl j)
  let y : F := v (Sum.inr ())
  have hleft : A.mulVec vLeft = y • b := by
    funext i
    have hi := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, cramerRelationMatrix,
      Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton] at hi
    change (∑ j, A i j * vLeft j) = y * b i
    change (∑ j, A i j * v (Sum.inl j)) + -b i * y = 0 at hi
    linear_combination hi
  let w : I → F := A.det • vLeft - y • A.cramer b
  have hw : A.mulVec w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hleft, Matrix.mulVec_cramer]
    ext i
    simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  have hwzero : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  funext col
  cases col with
  | inl j =>
      have hj := congrFun hwzero j
      change A.det * v (Sum.inl j) =
        v (Sum.inr ()) * A.cramer b j
      apply sub_eq_zero.mp
      simpa [w, vLeft, y, smul_eq_mul] using hj
  | inr u =>
      cases u
      simp [cramerKernelVector, smul_eq_mul, mul_comm]
theorem exists_eq_smul_cramerKernelVector
    (A : Matrix I I F) (b : I → F) (v : I ⊕ Unit → F)
    (hdet : A.det ≠ 0)
    (hv : (cramerRelationMatrix A b).mulVec v = 0) :
    ∃ c : F, v = c • cramerKernelVector A b := by
  classical
  have hclear := det_smul_eq_last_smul_cramerKernelVector
    A b v hdet hv
  refine ⟨(A.det)⁻¹ * v (Sum.inr ()), ?_⟩
  funext col
  have hcol := congrFun hclear col
  change A.det * v col =
    v (Sum.inr ()) * cramerKernelVector A b col at hcol
  change v col = ((A.det)⁻¹ * v (Sum.inr ())) *
    cramerKernelVector A b col
  calc
    v col = (A.det)⁻¹ * (A.det * v col) := by
      rw [← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    _ = (A.det)⁻¹ *
        (v (Sum.inr ()) * cramerKernelVector A b col) := by rw [hcol]
    _ = ((A.det)⁻¹ * v (Sum.inr ())) *
        cramerKernelVector A b col := by rw [mul_assoc]
end AbstractCofactor
section PolynomialCofactor
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
theorem cramerKernelVector_natDegree_le_sum_rowCaps
    (A : Matrix I I F[X]) (b : I → F[X]) (rowCap : I → Nat)
    (hA : ∀ i j, (A i j).natDegree ≤ rowCap i)
    (hb : ∀ i, (b i).natDegree ≤ rowCap i)
    (col : I ⊕ Unit) :
    (cramerKernelVector A b col).natDegree ≤ ∑ i, rowCap i := by
  classical
  cases col with
  | inl j =>
      rw [cramerKernelVector, Matrix.cramer_apply]
      apply natDegree_det_le_sum_rowCaps
      intro i k
      by_cases hk : k = j
      · subst k
        simpa [Matrix.updateCol] using hb i
      · simpa [Matrix.updateCol, hk] using hA i k
  | inr u =>
      cases u
      simpa [cramerKernelVector] using
        (natDegree_det_le_sum_rowCaps A rowCap hA)
theorem eval_cramerKernelVector
    (A : Matrix I I F[X]) (b : I → F[X]) (z : F) (col : I ⊕ Unit) :
    Polynomial.eval z (cramerKernelVector A b col) =
      cramerKernelVector (A.map (Polynomial.evalRingHom z))
        (fun i ↦ Polynomial.eval z (b i)) col := by
  classical
  cases col with
  | inl j =>
      simpa [cramerKernelVector] using
        eval_polynomialMatrix_cramer A b z j
  | inr u =>
      cases u
      simpa [cramerKernelVector] using eval_polynomialMatrix_det A z
theorem specialized_kernel_eq_smul_evaluated_cramerKernelVector
    (A : Matrix I I F[X]) (b : I → F[X]) (z : F)
    (v : I ⊕ Unit → F)
    (hdet : Polynomial.eval z A.det ≠ 0)
    (hv : (cramerRelationMatrix
      (A.map (Polynomial.evalRingHom z))
      (fun i ↦ Polynomial.eval z (b i))).mulVec v = 0) :
    ∃ c : F, v = c •
      (fun col ↦ Polynomial.eval z (cramerKernelVector A b col)) := by
  classical
  have hdet' : (A.map (Polynomial.evalRingHom z)).det ≠ 0 := by
    simpa [eval_polynomialMatrix_det] using hdet
  obtain ⟨c, hc⟩ := exists_eq_smul_cramerKernelVector
    (A.map (Polynomial.evalRingHom z))
    (fun i ↦ Polynomial.eval z (b i)) v hdet' hv
  refine ⟨c, ?_⟩
  rw [hc]
  congr 1
  funext col
  exact (eval_cramerKernelVector A b z col).symm
end PolynomialCofactor
section BenchmarkCofactor
noncomputable def genericRankCofactorVectorZ6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    GenericRankMinorRow6401 rho ⊕ Unit → F[X] :=
  cramerKernelVector
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
theorem genericRankCofactorVectorZ_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (col : GenericRankMinorRow6401 rho ⊕ Unit) :
    (genericRankCofactorVectorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow col).natDegree ≤ genericRankMinorDegreeCap6401 rho := by
  classical
  cases col with
  | inl j =>
      exact genericRankKeyCramerNumerator_degree6401
        sigma alpha u₀ u₁ rho frobeniusRow j
  | inr u =>
      cases u
      exact genericRankKeyMinorZ_det_degree6401
        sigma alpha u₀ u₁ rho frobeniusRow
theorem genericRankCofactorVectorZ_specialization_spans6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F)
    (v : GenericRankMinorRow6401 rho ⊕ Unit → F)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0)
    (hv : (cramerRelationMatrix
      ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).map (Polynomial.evalRingHom z))
      (fun row ↦ Polynomial.eval z
        (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row))).mulVec v = 0) :
    ∃ c : F, v = c • (fun col ↦ Polynomial.eval z
      (genericRankCofactorVectorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow col)) := by
  exact specialized_kernel_eq_smul_evaluated_cramerKernelVector
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    z v hdet hv
end BenchmarkCofactor
end BCHKSFrobeniusDeltaOneCofactor6401
end ProximityPrize.SubmissionLower
