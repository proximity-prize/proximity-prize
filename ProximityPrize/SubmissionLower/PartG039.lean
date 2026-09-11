import ProximityPrize.SubmissionLower.PartG038


section Compact_RootMultiplicityHeight
/-! A rational root of high multiplicity has bounded height. The coefficient
pole bound is summed over places using the principal-divisor identity. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem log_sum_zero_of_contains (c : L) (hc : c ≠ 0) (W : Finset (Place K L))
    (hW : placesFor K L c hc ⊆ W) : (∑ v ∈ W, (v.val c).log) = 0 := by
  classical
  have hz : (∑ v ∈ placesFor K L c hc, (v.val c).log) = 0 := by
    simpa only [order, Finset.sum_neg_distrib, neg_eq_zero] using
      sum_placesFor_order_zero K L c hc
  calc
    (∑ v ∈ W, (v.val c).log) = ∑ v ∈ placesFor K L c hc, (v.val c).log := by
      symm
      apply Finset.sum_subset hW
      intro v hv hnot
      have ho : order K L v c = 0 := by
        by_contra h
        exact hnot (placesFor_covers K L c hc v h)
      simpa only [order, neg_eq_zero] using ho
    _ = 0 := hz

theorem root_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B : Place K L → ℤ) (C : ℤ)
    (hcoeff : ∀ v i, v.val (P.coeff i) ≤ WithZero.exp (B v))
    (hbudget : ∀ W : Finset (Place K L), (∑ v ∈ W, B v) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, poleOrder v.val t) ≤ C := by
  classical
  obtain ⟨Q, rfl⟩ := hd
  have hQ : Q ≠ 0 := by intro h; simp [h] at hP
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hQ
  have hi : Q.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  let V := W ∪ placesFor K L (Q.coeff i) hi
  have hbalance := log_sum_zero_of_contains K L (Q.coeff i) hi V
    (Finset.subset_union_right)
  have hheight := finite_log_height_bound V (fun v => v.val) t Q d B
    (fun v _ i => hcoeff v i) i hi hbalance
  simp only [log_max_one] at hheight
  calc
    (d : ℤ)*(∑ v ∈ W, poleOrder v.val t) ≤
        (d : ℤ)*(∑ v ∈ V, poleOrder v.val t) := by
      apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro v _ _
      exact le_max_left _ _
    _ ≤ ∑ v ∈ V, B v := hheight
    _ ≤ C := hbudget V

/-- The moving-coordinate pole target is controlled by a root-height bound.
The two coordinate pole envelopes satisfy `beta ≤ alpha`. -/
theorem moving_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C A : ℤ)
    (hcoeff : ∀ v i, v.val (P.coeff i) ≤ WithZero.exp (B v))
    (hbudget : ∀ W : Finset (Place K L), (∑ v ∈ W, B v) ≤ C)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (halpha : ∀ W : Finset (Place K L), (∑ v ∈ W, alpha v) ≤ A)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤
      2*(d : ℤ)*A+C := by
  have hheight := root_height_bound K L P hP t d hd B C hcoeff hbudget W
  have hlocal : ∀ v, max (2*alpha v) (beta v+poleOrder v.val t) ≤
      2*alpha v+poleOrder v.val t := by
    intro v
    have hp : 0 ≤ poleOrder v.val t := le_max_left _ _
    have hav := ha v
    have hbav := hba v
    exact max_le (by omega) (by omega)
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := W) (fun v _ => hlocal v))
    (Int.natCast_nonneg d)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, ← mul_assoc] at hs
  have hal := mul_le_mul_of_nonneg_left (halpha W)
    (show 0 ≤ 2*(d : ℤ) by positivity)
  nlinarith

end
end ProximityPrize.SubmissionLower.RootMultiplicityHeight

end Compact_RootMultiplicityHeight
