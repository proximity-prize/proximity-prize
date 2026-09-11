import ProximityPrize.SubmissionLower.Part.G042


section Compact_RootMultiplicityWeightedHeight
/-! Weighted root height, including the contribution of the remaining degree.
All coefficient and budget hypotheses are explicit. This module does not
construct a new interpolation space or establish a protocol claim. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation RootMultiplicityHeight
open RootMultiplicityWeightedValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem log_max_exp (v : Valuation L Value) (t : L) (lambda : ℤ) (hl : 0 ≤ lambda) :
    (max (WithZero.exp lambda) (v t)).log = max lambda (poleOrder v t) := by
  by_cases ht : v t = 0
  · simp [ht, poleOrder, max_eq_left hl]
  by_cases h : WithZero.exp lambda ≤ v t
  · have hlog : lambda ≤ (v t).log := by
      rw [← WithZero.exp_log ht] at h
      exact WithZero.exp_le_exp.mp h
    rw [max_eq_right h]
    simp only [poleOrder, max_eq_right (hl.trans hlog), max_eq_right hlog]
  · have hv : v t ≤ WithZero.exp lambda := le_of_not_ge h
    have hlog := (WithZero.log_le_iff_le_exp ht).mpr hv
    rw [max_eq_left hv]
    simp only [WithZero.log_exp, poleOrder, max_eq_left (max_le hl hlog)]

theorem coeff_weighted_of_affine (v : Valuation L Value) (P : Polynomial L)
    (B lambda : ℤ)
    (hP : ∀ i, v (P.coeff i) ≤ WithZero.exp (B-(i : ℤ)*lambda)) :
    ∀ i, v (P.coeff i)*(WithZero.exp lambda)^i ≤ WithZero.exp B := by
  intro i
  calc
    v (P.coeff i)*(WithZero.exp lambda)^i ≤
        WithZero.exp (B-(i : ℤ)*lambda)*(WithZero.exp lambda)^i :=
      mul_le_mul_left (hP i) _
    _ = WithZero.exp B := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
      simp

theorem coeff_log_bound_pow_factor (v : Valuation L Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B lambda : ℤ) (hl : 0 ≤ lambda)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp lambda)^i ≤ WithZero.exp B)
    (i : ℕ) (hi : Q.coeff i ≠ 0) :
    (v (Q.coeff i)).log+(i : ℤ)*lambda+
      (d : ℤ)*max lambda (poleOrder v t) ≤ B := by
  have hv : v (Q.coeff i) ≠ 0 := v.ne_zero_iff.mpr hi
  have hb : (WithZero.exp lambda : Value) ≠ 0 := WithZero.exp_ne_zero
  have ht : max (WithZero.exp lambda) (v t) ≠ 0 := by
    intro h
    have hle := le_max_left (WithZero.exp lambda) (v t)
    rw [h] at hle
    exact hb (le_antisymm hle zero_le)
  have hh := (WithZero.log_le_iff_le_exp
    (mul_ne_zero (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht))).mpr
    (RootMultiplicityWeightedValuation.coeff_bound_pow_factor
      v (WithZero.exp lambda) t Q d (WithZero.exp B) hP i)
  simpa only [WithZero.log_mul (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht),
    WithZero.log_mul hv (pow_ne_zero i hb), WithZero.log_pow, WithZero.log_exp,
    nsmul_eq_mul, log_max_exp v t lambda hl] using hh

theorem finite_log_height_bound {ι : Type*} (W : Finset ι)
    (v : ι → Valuation L Value) (t : L) (Q : Polynomial L) (d : ℕ)
    (B lambda : ι → ℤ) (hl : ∀ w ∈ W, 0 ≤ lambda w)
    (hP : ∀ w ∈ W, ∀ i, v w (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp (lambda w))^i ≤ WithZero.exp (B w))
    (i : ℕ) (hi : Q.coeff i ≠ 0)
    (hbalance : (∑ w ∈ W, (v w (Q.coeff i)).log) = 0) :
    (i : ℤ)*(∑ w ∈ W, lambda w)+
      (d : ℤ)*(∑ w ∈ W, max (lambda w) (poleOrder (v w) t)) ≤ ∑ w ∈ W, B w := by
  have hsum := Finset.sum_le_sum (fun w hw =>
    coeff_log_bound_pow_factor (v w) t Q d (B w) (lambda w) (hl w hw) (hP w hw) i hi)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hbalance, zero_add] using hsum

section FunctionField
variable (K : Type*) [Field K] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- The coefficient budget pays for the root multiplicity and the degree of
its cofactor. The latter contribution was discarded by the unweighted bound. -/
theorem root_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B lambda : Place K L → ℤ) (C : ℤ) (hl : ∀ v, 0 ≤ lambda v)
    (hcoeff : ∀ v i, v.val (P.coeff i)*(WithZero.exp (lambda v))^i ≤ WithZero.exp (B v))
    (hbudget : ∀ V : Finset (Place K L), (∑ v ∈ V, B v) ≤ C)
    (W : Finset (Place K L)) :
    ((P.natDegree-d : ℕ) : ℤ)*(∑ v ∈ W, lambda v)+
      (d : ℤ)*(∑ v ∈ W, max (lambda v) (poleOrder v.val t)) ≤ C := by
  obtain ⟨Q, rfl⟩ := hd
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
  have hf : (Polynomial.X-Polynomial.C t)^d ≠ 0 := left_ne_zero_of_mul hP
  have hi : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg : ((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d = Q.natDegree := by
    rw [Polynomial.natDegree_mul hf hQ, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega
  rw [hdeg]
  let V := W ∪ placesFor K L (Q.coeff Q.natDegree) hi
  have hbalance := log_sum_zero_of_contains K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hh := finite_log_height_bound V (fun v => v.val) t Q d B lambda
    (fun v _ => hl v) (fun v _ i => hcoeff v i) Q.natDegree hi hbalance
  have hmono (f : Place K L → ℤ) (hf : ∀ v, 0 ≤ f v) :
      (∑ v ∈ W, f v) ≤ ∑ v ∈ V, f v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    exact fun v _ _ => hf v
  exact (add_le_add
    (mul_le_mul_of_nonneg_left (hmono lambda hl) (Int.natCast_nonneg Q.natDegree))
    (mul_le_mul_of_nonneg_left (hmono _ (fun v => (hl v).trans (le_max_left _ _)))
      (Int.natCast_nonneg d))).trans (hh.trans (hbudget V))

/-- A moving-pole estimate using the affine coefficient bound with weight
`2*alpha-beta`. Its budget hypothesis retains the cofactor degree exactly. -/
theorem moving_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((P.natDegree-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  obtain ⟨Q, rfl⟩ := hd
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
  have hf : (Polynomial.X-Polynomial.C t)^d ≠ 0 := left_ne_zero_of_mul hP
  have hi : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg : ((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d = Q.natDegree := by
    rw [Polynomial.natDegree_mul hf hQ, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega
  simp only [hdeg] at hbudget
  let V := W ∪ placesFor K L (Q.coeff Q.natDegree) hi
  have hbalance := log_sum_zero_of_contains K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hl : ∀ v, 0 ≤ 2*alpha v-beta v := by intro v; have := ha v; have := hba v; omega
  have hh := finite_log_height_bound V (fun v => v.val) t Q d B
    (fun v => 2*alpha v-beta v) (fun v _ => hl v)
    (fun v _ => coeff_weighted_of_affine v.val _ _ _ (hcoeff v)) Q.natDegree hi hbalance
  have heq (v : Place K L) :
      max (2*alpha v) (beta v+poleOrder v.val t) =
        beta v+max (2*alpha v-beta v) (poleOrder v.val t) := by omega
  have hbound : (d : ℤ)*(∑ v ∈ V, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
    have hbud := hbudget V
    simp_rw [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hbud ⊢
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
    nlinarith
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro v _ _
  exact (by have := ha v; omega : 0 ≤ 2*alpha v).trans (le_max_left _ _)


/-- A lower bound on the polynomial degree is enough to reserve a uniform
cofactor contribution in a family of component budgets. -/
theorem moving_height_bound_of_degree (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (d n0 : ℕ) (hn : n0 ≤ P.natDegree)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((n0-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  apply moving_height_bound K P hP t d hd B alpha beta C ha hba hcoeff _ W
  intro V
  apply le_trans _ (hbudget V)
  apply Finset.sum_le_sum
  intro v _
  have hl : 0 ≤ 2*alpha v-beta v := by have := ha v; have := hba v; omega
  have hsub : ((n0-d : ℕ) : ℤ) ≤ ((P.natDegree-d : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hn d
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsub hl) _

end FunctionField
end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight

end Compact_RootMultiplicityWeightedHeight
