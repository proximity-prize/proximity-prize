import ProximityPrize.SubmissionLower.LowerFoundation



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators
open RCN002 RCN005 RCN044 RCN135 RCN136 RCN187 RCN234 RCN257 RCN264 RCN271 RCN341 RCN344

noncomputable section

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

theorem regular_zero_bound_of_rectangular_poles
    (base : SeparableLiteralCoordinate P) (H N : MvPolynomial (Fin 3) Ω)
    (cap poleBudget : Fin 3 → ℕ)
    (proper : N ∉ P) (separant : H ∉ P) (degree : ∀ i, N.degreeOf i ≤ cap i)
    (coordinatePoleBudget :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P base.index base.transcendental
      ∀ i (W : Finset (Place Ω (CoordinateField Ω P))),
        (∑ v ∈ W, poleOrder v.val (coordinate Ω P i)) ≤ (poleBudget i : ℤ)) :
    FiniteRegularZeroSetBound P H N (∑ i, cap i * poleBudget i) := by
  classical
  apply finite_regular_zero_bound_of_separator Ω P base H N 0 _ proper separant
  intro W
  simp only [pow_zero, div_one]
  change (∑ v ∈ W, poleOrder v.val (MvPolynomial.aeval (coordinate Ω P) N)) ≤ _
  push_cast
  calc
    _ ≤ ∑ v ∈ W, ∑ i, (cap i : ℤ) * poleOrder v.val (coordinate Ω P i) := by
      apply Finset.sum_le_sum
      intro v _
      letI := v.property.2
      exact poleOrder_eval_le_box v.val (algebraMap Ω (CoordinateField Ω P))
        (Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val) (coordinate Ω P) cap N degree
    _ = ∑ i, (cap i : ℤ) * (∑ v ∈ W, poleOrder v.val (coordinate Ω P i)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (coordinatePoleBudget i W) (Int.natCast_nonneg _)

theorem sum_regular_counts_le_rectangular {A : Type*} [Fintype A]
    (count order : A → ℕ) (cap global : Fin 3 → ℕ) (poleBudget : A → Fin 3 → ℕ)
    (localCount : ∀ a, count a ≤ ∑ i, (order a * cap i) * poleBudget a i)
    (globalBudget : ∀ i, (∑ a, order a * poleBudget a i) ≤ global i) :
    (∑ a, count a) ≤ ∑ i, cap i * global i := by
  classical
  calc
    _ ≤ ∑ a, ∑ i, (order a * cap i) * poleBudget a i :=
      Finset.sum_le_sum fun a _ => localCount a
    _ = ∑ i, cap i * (∑ a, order a * poleBudget a i) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (globalBudget i)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
