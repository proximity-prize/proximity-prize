import ProximityPrize.SubmissionLower.Koala6844VirtualHighGlobalBox
import ProximityPrize.SubmissionLower.LowerGeometry


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

noncomputable section
set_option autoImplicit false

open RCN180
open scoped Classical

variable {K : Type} [Field K]

def rectangleWeights (w : ℕ) : Fin 4 → ℕ := ![1, w, 0, 0]

private theorem rectangle_weight (w : ℕ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (rectangleWeights w) e = e 0 + w * e 1 := by
  rw [RCN081.weight_fin4]
  simp [rectangleWeights, Nat.mul_comm]

theorem wall_of_mem_globalBox {D w y b c : ℕ} {P : MvPolynomial (Fin 4) K}
    (hn : P ≠ 0) (hP : P ∈ globalBox K D w y b c) :
    P.weightedTotalDegree (rectangleWeights w) < D ∧
      P.degreeOf 1 ≤ y ∧ P.degreeOf 2 ≤ b ∧ P.degreeOf 3 ≤ c := by
  have h := (mem_globalBox K D w y b c P).mp hP
  have hD : 0 < D := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hn
    exact Nat.zero_lt_of_lt (h e he).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Nat.lt_of_le_pred hD
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    rw [rectangle_weight]
    exact Nat.le_sub_one_of_lt (h e he).1
  all_goals
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    first | exact (h e he).2.1 | exact (h e he).2.2.1 | exact (h e he).2.2.2

theorem mem_globalBox_of_wall {D w y b c : ℕ} {P : MvPolynomial (Fin 4) K}
    (hP : P.weightedTotalDegree (rectangleWeights w) < D ∧
      P.degreeOf 1 ≤ y ∧ P.degreeOf 2 ≤ b ∧ P.degreeOf 3 ≤ c) :
    P ∈ globalBox K D w y b c := by
  rw [mem_globalBox]
  intro e he
  have hw := MvPolynomial.le_weightedTotalDegree (rectangleWeights w) he
  rw [rectangle_weight] at hw
  exact ⟨hw.trans_lt hP.1,
    (MvPolynomial.monomial_le_degreeOf _ he).trans hP.2.1,
    (MvPolynomial.monomial_le_degreeOf _ he).trans hP.2.2.1,
    (MvPolynomial.monomial_le_degreeOf _ he).trans hP.2.2.2⟩

theorem quotient_globalBox {D w y b c : ℕ} {P Q : MvPolynomial (Fin 4) K} (hP : P ≠ 0)
    (hBox : P * Q ∈ globalBox K D w y b c) :
    Q ∈ globalBox K (D - P.weightedTotalDegree (rectangleWeights w)) w
      (y - P.degreeOf 1) (b - P.degreeOf 2) (c - P.degreeOf 3) := by
  by_cases hQ : Q = 0
  · subst Q
    exact Submodule.zero_mem _
  obtain ⟨hw, hy, hb, hc⟩ := wall_of_mem_globalBox (mul_ne_zero hP hQ) hBox
  rw [RCN081.weightedTotalDegree_mul _ _ _ hP hQ] at hw
  rw [MvPolynomial.degreeOf_mul_eq hP hQ] at hy hb hc
  exact mem_globalBox_of_wall ⟨by omega, by omega, by omega, by omega⟩

theorem nonzero_globalBox_of_product {D w y b c : ℕ} {P Q : MvPolynomial (Fin 4) K}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hBox : Q ∈ globalBox K (D - P.weightedTotalDegree (rectangleWeights w)) w
      (y - P.degreeOf 1) (b - P.degreeOf 2) (c - P.degreeOf 3))
    (hy : P.degreeOf 1 ≤ y) (hb : P.degreeOf 2 ≤ b) (hc : P.degreeOf 3 ≤ c) :
    P * Q ∈ globalBox K D w y b c := by
  obtain ⟨hw, hy', hb', hc'⟩ := wall_of_mem_globalBox hQ hBox
  apply mem_globalBox_of_wall
  rw [RCN081.weightedTotalDegree_mul _ _ _ hP hQ]
  simp only [MvPolynomial.degreeOf_mul_eq hP hQ]
  exact ⟨by omega, by omega, by omega, by omega⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

