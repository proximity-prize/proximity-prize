import ProximityPrize.SubmissionLower.BCHKSQuadraticBranchAlgebra6400
import ProximityPrize.SubmissionLower.BCHKSResultantDegree
namespace ProximityPrize.SubmissionLower
namespace BCHKSQuadraticSquareSpecialization6400
open Polynomial
theorem polynomial_dvd_of_sq_dvd_sq
    {F : Type*} [Field F] (A : Polynomial F) :
    ∀ B : Polynomial F, A ^ 2 ∣ B ^ 2 → A ∣ B := by
  induction A using WfDvdMonoid.induction_on_irreducible with
  | zero =>
      intro B h
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_dvd_iff] at h
      rw [zero_dvd_iff]
      exact (mul_self_eq_zero.mp (by simpa [pow_two] using h))
  | unit U hU =>
      intro B _
      exact hU.dvd
  | mul A P hA hP ih =>
      intro B h
      have hPdASq : P ∣ (P * A) ^ 2 := by
        refine ⟨P * A ^ 2, ?_⟩
        ring
      have hPdBSq : P ∣ B ^ 2 := hPdASq.trans h
      have hPdB : P ∣ B := hP.prime.dvd_of_dvd_pow hPdBSq
      obtain ⟨C, rfl⟩ := hPdB
      obtain ⟨D, hD⟩ := h
      have hAsqdCsq : A ^ 2 ∣ C ^ 2 := by
        refine ⟨D, ?_⟩
        apply mul_left_cancel₀ (pow_ne_zero 2 hP.ne_zero)
        calc
          P ^ 2 * C ^ 2 = (P * C) ^ 2 := by ring
          _ = (P * A) ^ 2 * D := hD
          _ = P ^ 2 * (A ^ 2 * D) := by ring
      obtain ⟨E, rfl⟩ := ih C hAsqdCsq
      exact ⟨E, by simp [mul_assoc]⟩
theorem squarefree_square_kernel_not_square
    {F : Type*} [Field F] {S B W : Polynomial F}
    (hS : Squarefree S) (hB : B ≠ 0) (hSnonunit : ¬ IsUnit S)
    (hEq : B ^ 2 * S = W ^ 2) : False := by
  have hSdvdWsq : S ∣ W ^ 2 := by
    refine ⟨B ^ 2, ?_⟩
    simpa [mul_comm] using hEq.symm
  have hSdvdW : S ∣ W :=
    (hS.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hSdvdWsq
  obtain ⟨T, rfl⟩ := hSdvdW
  have hS0 : S ≠ 0 := hS.ne_zero
  have hcancel : B ^ 2 = S * T ^ 2 := by
    apply mul_right_cancel₀ hS0
    calc
      B ^ 2 * S = (S * T) ^ 2 := hEq
      _ = (S * T ^ 2) * S := by ring
  have hTsqdvdBsq : T ^ 2 ∣ B ^ 2 := by
    refine ⟨S, ?_⟩
    simpa [mul_comm] using hcancel
  have hTdB : T ∣ B :=
    polynomial_dvd_of_sq_dvd_sq T B hTsqdvdBsq
  obtain ⟨C, rfl⟩ := hTdB
  have hT0 : T ≠ 0 := fun hT => hB (by simp [hT])
  have hSq : C ^ 2 = S := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hT0)
    calc
      T ^ 2 * C ^ 2 = (T * C) ^ 2 := by ring
      _ = S * T ^ 2 := hcancel
      _ = T ^ 2 * S := by ring
  have hCsqdS : C * C ∣ S := ⟨1, by simpa [pow_two] using hSq.symm⟩
  have hCunit : IsUnit C := hS C hCsqdS
  exact hSnonunit (hSq ▸ hCunit.pow 2)
theorem resultant_square_derivative_eq_zero
    {F : Type*} [Field F] (W : Polynomial F) (hW : 0 < W.natDegree) :
    Polynomial.resultant (W ^ 2) (W ^ 2).derivative = 0 := by
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨Or.inl ?_, ?_⟩
  · exact pow_ne_zero 2 (Polynomial.ne_zero_of_natDegree_gt hW)
  · intro hcoprime
    have hWdvdSq : W ∣ W ^ 2 := by
      rw [pow_two]
      exact dvd_mul_right W W
    have hWdvdDeriv : W ∣ (W ^ 2).derivative := by
      rw [Polynomial.derivative_sq]
      exact ⟨Polynomial.C 2 * W.derivative, by ring⟩
    have hunit : IsUnit W := hcoprime.isUnit_of_dvd' hWdvdSq hWdvdDeriv
    exact (Polynomial.not_isUnit_of_natDegree_pos W hW) hunit
theorem resultant_fixed_degree_eq_zero_of_resultant_eq_zero
    {F : Type*} [Field F] {P Q : Polynomial F} {m n : ℕ}
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hres : Polynomial.resultant P Q = 0) :
    Polynomial.resultant P Q m n = 0 := by
  have hm : P.natDegree + (m - P.natDegree) = m := Nat.add_sub_of_le hP
  have hn : Q.natDegree + (n - Q.natDegree) = n := Nat.add_sub_of_le hQ
  rw [← hm, ← hn]
  rw [Polynomial.resultant_add_left_deg]
  · rw [Polynomial.resultant_add_right_deg]
    · simp [hres]
    · exact le_rfl
  · exact le_rfl
theorem resultant_square_derivative_fixed_eq_zero
    {F : Type*} [Field F] (W : Polynomial F) (r : ℕ)
    (hr : 0 < r) (hW : 0 < W.natDegree)
    (hSq : (W ^ 2).natDegree ≤ r) :
    Polynomial.resultant (W ^ 2) (W ^ 2).derivative r (r - 1) = 0 := by
  apply resultant_fixed_degree_eq_zero_of_resultant_eq_zero
  · exact hSq
  · exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  · exact resultant_square_derivative_eq_zero W hW
theorem square_specialization_is_resultant_root
    {F : Type} [Field F]
    (S : Polynomial (Polynomial F)) (z : F) (W : Polynomial F) (r : ℕ)
    (hr : 0 < r) (hSY : S.natDegree ≤ r)
    (hSquare : S.map (Polynomial.evalRingHom z) = W ^ 2)
    (hW : 0 < W.natDegree) :
    Polynomial.eval z
      (Polynomial.resultant S S.derivative r (r - 1)) = 0 := by
  rw [bivariate_resultant_eval]
  rw [← Polynomial.derivative_map, hSquare]
  apply resultant_square_derivative_fixed_eq_zero W r hr hW
  rw [← hSquare]
  exact Polynomial.natDegree_map_le.trans hSY
theorem squarefree_resultant_Z_degree_le6400
    {F : Type} [Field F]
    (S : Polynomial (Polynomial F)) (r d : ℕ)
    (hSZ : Polynomial.Bivariate.degreeX S ≤ 2 * d)
    (hderZ : Polynomial.Bivariate.degreeX S.derivative ≤ 2 * d) :
    (Polynomial.resultant S S.derivative r (r - 1)).natDegree ≤
      r * (2 * d) + (r - 1) * (2 * d) := by
  calc
    (Polynomial.resultant S S.derivative r (r - 1)).natDegree ≤
        (r - 1) * Polynomial.Bivariate.degreeX S +
          r * Polynomial.Bivariate.degreeX S.derivative :=
      bivariate_resultant_natDegree_le S S.derivative r (r - 1)
    _ ≤ (r - 1) * (2 * d) + r * (2 * d) :=
      Nat.add_le_add (Nat.mul_le_mul_left (r - 1) hSZ)
        (Nat.mul_le_mul_left r hderZ)
    _ = r * (2 * d) + (r - 1) * (2 * d) := by omega
end BCHKSQuadraticSquareSpecialization6400
end ProximityPrize.SubmissionLower
