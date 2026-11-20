import ProximityPrize.SubmissionLower.LowerGeometry


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open RCN081 RCN234 RCN293

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

variable {K : Type*} [Field K]

private def offset {m n : ℕ} (j : Fin (m+n)) : ℕ := j.addCases Fin.val Fin.val
private def coeffIndex {m n : ℕ} (σ : Equiv.Perm (Fin (m+n))) (j : Fin (m+n)) : ℕ := (σ j).val-offset j

private theorem index_sum (m n : ℕ) (σ : Equiv.Perm (Fin (m+n)))
    (h : ∀ j, offset j ≤ (σ j).val) : (∑ j, coeffIndex σ j) = m*n := by
  have hrow : (∑ j : Fin (m+n), (σ j).val) = ∑ j : Fin (m+n), j.val :=
    Equiv.sum_comp σ Fin.val
  have hsum : (∑ j, coeffIndex σ j) + (∑ j : Fin (m+n), offset j) =
      ∑ j : Fin (m+n), (σ j).val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.sub_add_cancel (h j)
  have hoff : (∑ j : Fin (m+n), j.val) = (∑ j : Fin (m+n), offset j)+m*n := by
    rw [Fin.sum_univ_add,Fin.sum_univ_add (f := fun j : Fin (m+n) => offset j)]
    simp [offset,Finset.sum_add_distrib,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm]
  omega

theorem resultant_weighted_sharp
    (F G : Polynomial (MvPolynomial (Fin 4) K)) (m n a b : ℕ) (w : Fin 4 → ℕ)
    (hF : ∀ j, F.coeff j ≠ 0 → (F.coeff j).weightedTotalDegree w+j ≤ a)
    (hG : ∀ j, G.coeff j ≠ 0 → (G.coeff j).weightedTotalDegree w+j ≤ b) :
    (Polynomial.resultant F G m n).weightedTotalDegree w ≤ m*b+n*a-m*n := by
  classical
  rw [← degree_weightedLift,Polynomial.resultant,Matrix.det_apply',map_sum]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  let M := Polynomial.sylvester F G m n
  by_cases hz : (∏ j : Fin (m+n), M (σ j) j) = 0
  · simp [hz,M]
  have hNZ (j : Fin (m+n)) : M (σ j) j ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ j)
  have hrow (j : Fin (m+n)) : offset j ≤ (σ j).val := by
    induction j using Fin.addCases with
    | left j =>
      have hn := hNZ (Fin.castAdd n j)
      simp only [M,Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left,ne_eq] at hn
      split_ifs at hn with hh
      · simpa [offset] using hh.1
      · exact False.elim (hn rfl)
    | right j =>
      have hn := hNZ (Fin.natAdd m j)
      simp only [M,Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right,ne_eq] at hn
      split_ifs at hn with hh
      · simpa [offset] using hh.1
      · exact False.elim (hn rfl)
  have hscore (j : Fin (m+n)) : (M (σ j) j).weightedTotalDegree w + coeffIndex σ j ≤
      j.addCases (fun _ : Fin m => b) (fun _ : Fin n => a) := by
    induction j using Fin.addCases with
    | left j =>
      have hn := hNZ (Fin.castAdd n j)
      simp only [M,Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left] at hn ⊢
      split_ifs at hn ⊢ with hh
      · simpa [coeffIndex,offset] using hG _ hn
      · exact False.elim (hn rfl)
    | right j =>
      have hn := hNZ (Fin.natAdd m j)
      simp only [M,Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right] at hn ⊢
      split_ifs at hn ⊢ with hh
      · simpa [coeffIndex,offset] using hF _ hn
      · exact False.elim (hn rfl)
  have hbudget := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hscore j)
  have hcolumn : (∑ j : Fin (m+n), j.addCases (fun _ : Fin m => b) (fun _ : Fin n => a)) = m*b+n*a := by
    rw [Fin.sum_univ_add]
    simp
  rw [Finset.sum_add_distrib,index_sum m n σ hrow,hcolumn] at hbudget
  rw [map_mul,map_intCast,← map_intCast (MvPolynomial.C : K →+* MvPolynomial (Fin 5) K)]
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  rw [degree_weightedLift]
  have hp := weightedTotalDegree_prod_le w Finset.univ (fun j : Fin (m+n) => M (σ j) j)
  exact hp.trans (by omega)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
