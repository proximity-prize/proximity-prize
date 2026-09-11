import ProximityPrize.SubmissionLower.PartG041


section Compact_RootMultiplicityWeightedValuation
/-! Weighted coefficient bounds retain the degree of the remaining factor.
This is a valuation lemma, not a lower-track protocol claim. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation
open scoped BigOperators WithZero
open RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem weighted_sub_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x-y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_sub x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem weighted_add_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x+y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_add x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem coeff_bound_large (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : b ≤ v t)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*v t ≤ B := by
  intro i
  induction i with
  | zero =>
    simpa [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, map_mul,
      mul_comm] using hP 0
  | succ i ih =>
    have hprev : v (Q.coeff i)*b^(i+1) ≤ B := by
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_right ht _).trans ih
    have heq : t*Q.coeff (i+1) = Q.coeff i-((Polynomial.X-Polynomial.C t)*Q).coeff (i+1) := by
      simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      ring
    have hb := weighted_sub_le v _ _ _ _ hprev (hP (i+1))
    rw [← heq, map_mul] at hb
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

theorem coeff_bound_small (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : v t ≤ b)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*b ≤ B := by
  have hbound : ∀ n i : ℕ, Q.natDegree+1 ≤ i+n → v (Q.coeff i)*b^i*b ≤ B := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul, zero_mul]
      exact zero_le
    | succ n ih =>
      intro i hi
      have hnext := ih (i+1) (by omega)
      have hmul : v (t*Q.coeff (i+1))*b^(i+1) ≤ B := by
        rw [map_mul]
        have hb := (mul_le_mul_right ht (v (Q.coeff (i+1))*b^(i+1))).trans hnext
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hb
      have heq : Q.coeff i = ((Polynomial.X-Polynomial.C t)*Q).coeff (i+1)+t*Q.coeff (i+1) := by
        simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        ring
      rw [mul_assoc, ← pow_succ, heq]
      exact weighted_add_le v _ _ _ _ (hP (i+1)) hmul
  exact fun i => hbound (Q.natDegree+1) i (by omega)

theorem coeff_bound_linear_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*max b (v t) ≤ B := by
  by_cases ht : b ≤ v t
  · rw [max_eq_right ht]
    exact coeff_bound_large v b t Q B ht hP
  · rw [max_eq_left (le_of_not_ge ht)]
    exact coeff_bound_small v b t Q B (le_of_not_ge ht) hP

def weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i)*b^i)

theorem coeff_le_weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) (i : ℕ) :
    v (P.coeff i)*b^i ≤ weightedValue v b P := by
  classical
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)*b^i) hi
  · have hz : P.coeff i = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hi
    rw [hz, map_zero, zero_mul]
    exact zero_le

theorem weightedValue_le (v : Valuation L Value) (b : Value) (P : Polynomial L) (B : Value)
    (h : ∀ i, v (P.coeff i)*b^i ≤ B) : weightedValue v b P ≤ B := by
  exact Finset.sup_le (fun i _ => h i)

theorem weightedValue_linear_factor (v : Valuation L Value) (b : Value) (t : L) (Q : Polynomial L) :
    weightedValue v b Q*max b (v t) ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*Q) := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp [weightedValue]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Q.support
    (Polynomial.support_nonempty.mpr hQ) (fun i => v (Q.coeff i)*b^i)
  change Q.support.sup (fun i => v (Q.coeff i)*b^i)*_ ≤ _
  rw [hi]
  exact coeff_bound_linear_factor v b t Q _ (coeff_le_weightedValue v b _) i

theorem weightedValue_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) :
    weightedValue v b Q*(max b (v t))^d ≤
      weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      weightedValue v b Q*(max b (v t))^(d+1) =
          (weightedValue v b Q*(max b (v t))^d)*max b (v t) := by rw [pow_succ, mul_assoc]
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q)*max b (v t) :=
        mul_le_mul_left ih _
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*((Polynomial.X-Polynomial.C t)^d*Q)) :=
        weightedValue_linear_factor v b t _
      _ = weightedValue v b ((Polynomial.X-Polynomial.C t)^(d+1)*Q) := by
        rw [pow_succ']; congr 1; ring

theorem coeff_bound_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*b^i ≤ B) (i : ℕ) :
    v (Q.coeff i)*b^i*(max b (v t))^d ≤ B := by
  exact (mul_le_mul_left (coeff_le_weightedValue v b Q i) _).trans
    ((weightedValue_pow_factor v b t Q d).trans (weightedValue_le v b _ B hP))

end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation

end Compact_RootMultiplicityWeightedValuation
