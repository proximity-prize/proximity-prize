import ProximityPrize.SubmissionLower.PartG037


section Compact_RootMultiplicityValuation
/-! Coefficient bounds after removing a rational root. This is the local
valuation ingredient for a proposed root-multiplicity height estimate. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityValuation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]
abbrev Value := WithZero (Multiplicative ℤ)

theorem coeff_bound_large (v : Valuation L Value) (t : L) (Q : Polynomial L) (B : Value)
    (ht : 1 ≤ v t) (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i) ≤ B) :
    ∀ i, v (Q.coeff i)*v t ≤ B := by
  intro i
  induction i with
  | zero =>
    simpa [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, map_mul,
      mul_comm] using hP 0
  | succ i ih =>
    have hprev : v (Q.coeff i) ≤ B := by
      calc
        v (Q.coeff i) = v (Q.coeff i)*1 := (mul_one _).symm
        _ ≤ v (Q.coeff i)*v t := mul_le_mul_right ht _
        _ ≤ B := ih
    have heq : t*Q.coeff (i+1) = Q.coeff i-((Polynomial.X-Polynomial.C t)*Q).coeff (i+1) := by
      simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      ring
    have hb := v.map_sub_le hprev (hP (i+1))
    rw [← heq, map_mul] at hb
    simpa only [mul_comm] using hb

theorem coeff_bound_small (v : Valuation L Value) (t : L) (Q : Polynomial L) (B : Value)
    (ht : v t ≤ 1) (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i) ≤ B) :
    ∀ i, v (Q.coeff i) ≤ B := by
  have hbound : ∀ n i : ℕ, Q.natDegree+1 ≤ i+n → v (Q.coeff i) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
      exact zero_le
    | succ n ih =>
      intro i hi
      have hnext := ih (i+1) (by omega)
      have hmul : v (t*Q.coeff (i+1)) ≤ B := by
        rw [map_mul]
        simpa only [one_mul] using mul_le_mul' ht hnext
      have heq : Q.coeff i = ((Polynomial.X-Polynomial.C t)*Q).coeff (i+1)+t*Q.coeff (i+1) := by
        simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        ring
      rw [heq]
      exact v.map_add_le (hP (i+1)) hmul
  exact fun i => hbound (Q.natDegree+1) i (by omega)

theorem coeff_bound_linear_factor (v : Valuation L Value) (t : L) (Q : Polynomial L) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i) ≤ B) :
    ∀ i, v (Q.coeff i)*max 1 (v t) ≤ B := by
  by_cases ht : 1 ≤ v t
  · rw [max_eq_right ht]
    exact coeff_bound_large v t Q B ht hP
  · rw [max_eq_left (le_of_not_ge ht)]
    simpa only [mul_one] using coeff_bound_small v t Q B (le_of_not_ge ht) hP

def polyValue (v : Valuation L Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i))

theorem coeff_le_polyValue (v : Valuation L Value) (P : Polynomial L) (i : ℕ) :
    v (P.coeff i) ≤ polyValue v P := by
  classical
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)) hi
  · have hz : P.coeff i = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hi
    rw [hz, map_zero]
    exact zero_le

theorem polyValue_le (v : Valuation L Value) (P : Polynomial L) (B : Value)
    (h : ∀ i, v (P.coeff i) ≤ B) : polyValue v P ≤ B := by
  exact Finset.sup_le (fun i _ => h i)

theorem polyValue_linear_factor (v : Valuation L Value) (t : L) (Q : Polynomial L) :
    polyValue v Q * max 1 (v t) ≤ polyValue v ((Polynomial.X-Polynomial.C t)*Q) := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp [polyValue]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Q.support
    (Polynomial.support_nonempty.mpr hQ) (fun i => v (Q.coeff i))
  change Q.support.sup (fun i => v (Q.coeff i)) * _ ≤ _
  rw [hi]
  exact coeff_bound_linear_factor v t Q _ (coeff_le_polyValue v _) i

theorem polyValue_pow_factor (v : Valuation L Value) (t : L) (Q : Polynomial L) (d : ℕ) :
    polyValue v Q * (max 1 (v t))^d ≤
      polyValue v ((Polynomial.X-Polynomial.C t)^d*Q) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      polyValue v Q * (max 1 (v t))^(d+1) =
          (polyValue v Q * (max 1 (v t))^d)*max 1 (v t) := by rw [pow_succ, mul_assoc]
      _ ≤ polyValue v ((Polynomial.X-Polynomial.C t)^d*Q)*max 1 (v t) :=
        mul_le_mul_left ih _
      _ ≤ polyValue v ((Polynomial.X-Polynomial.C t)*((Polynomial.X-Polynomial.C t)^d*Q)) :=
        polyValue_linear_factor v t _
      _ = polyValue v ((Polynomial.X-Polynomial.C t)^(d+1)*Q) := by rw [pow_succ']; congr 1; ring

theorem coeff_bound_pow_factor (v : Valuation L Value) (t : L) (Q : Polynomial L)
    (d : ℕ) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i) ≤ B) (i : ℕ) :
    v (Q.coeff i) * (max 1 (v t))^d ≤ B := by
  exact (mul_le_mul_left (coeff_le_polyValue v Q i) _).trans
    ((polyValue_pow_factor v t Q d).trans (polyValue_le v _ B hP))

theorem coeff_log_bound_pow_factor (v : Valuation L Value) (t : L) (Q : Polynomial L)
    (d : ℕ) (B : ℤ)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i) ≤ WithZero.exp B)
    (i : ℕ) (hi : Q.coeff i ≠ 0) :
    (v (Q.coeff i)).log + (d : ℤ)*(max 1 (v t)).log ≤ B := by
  have hv : v (Q.coeff i) ≠ 0 := v.ne_zero_iff.mpr hi
  have ht : max 1 (v t) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
  have hb := (WithZero.log_le_iff_le_exp (mul_ne_zero hv (pow_ne_zero d ht))).2
    (coeff_bound_pow_factor v t Q d (WithZero.exp B) hP i)
  simpa only [WithZero.log_mul hv (pow_ne_zero d ht), WithZero.log_pow,
    nsmul_eq_mul] using hb

theorem finite_log_height_bound {ι : Type*} (W : Finset ι)
    (v : ι → Valuation L Value) (t : L) (Q : Polynomial L) (d : ℕ) (B : ι → ℤ)
    (hP : ∀ w ∈ W, ∀ i,
      v w (((Polynomial.X-Polynomial.C t)^d*Q).coeff i) ≤ WithZero.exp (B w))
    (i : ℕ) (hi : Q.coeff i ≠ 0)
    (hbalance : (∑ w ∈ W, (v w (Q.coeff i)).log) = 0) :
    (d : ℤ)*(∑ w ∈ W, (max 1 (v w t)).log) ≤ ∑ w ∈ W, B w := by
  have hsum := Finset.sum_le_sum (fun w hw =>
    coeff_log_bound_pow_factor (v w) t Q d (B w) (hP w hw) i hi)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hbalance, zero_add] using hsum

end
end ProximityPrize.SubmissionLower.RootMultiplicityValuation

end Compact_RootMultiplicityValuation
