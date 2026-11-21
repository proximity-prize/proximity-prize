import ProximityPrize.SubmissionLower.LcmFlag6929
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff

set_option Elab.async false

/-!
O3 for the two-flag bound: `CofactorBand` holds.

Method: one grading device for three weights.
`weightLift w : Form →ₐ Polynomial Form` sends `X i ↦ C (X i) * Y ^ w i`. The coefficient of `Y^k`
is the `w`-weight-`k` part of the form (`coeff_coeff_weightLift`), so for `p ≠ 0`:
* the largest `w`-weight in the support is `natDegree (weightLift w p)`;
* the smallest is `natTrailingDegree (weightLift w p)`.
Both are additive on products (`Polynomial.natDegree_mul`, `natTrailingDegree_mul`; `Form` is a domain).
The weights used are degree `![1,1,1,1]`, index `![0,1,2,3]` (= jetIndex) and top `![0,0,0,1]`.
For `flagFactor u` the extremes reach `u.maxIndex`, `u.minIndex` and `u.maxTop`. This is shown per
factor at explicit numeric points; the witness coefficients are all `1`, so it holds in any characteristic.
Degenerate cases: `h = 0` is immediate; otherwise every bound is forced, including the Nat-truncated
`d - u.degree` and `top - u.maxTop` (they are attained, so no truncation occurs).

Standalone module (not in the Solution closure), not built here.
-/

section PackSource_K1_13_1_1CofactorFlag
set_option autoImplicit false
namespace K1_13_1_1

open K1_13
noncomputable section

/-! ### The grading lift -/

def weightLift (w : Fin 4 → ℕ) : Form →ₐ[Geom] Polynomial Form :=
  MvPolynomial.aeval fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i

def wDeg : Fin 4 → ℕ := ![1, 1, 1, 1]
def wIdx : Fin 4 → ℕ := ![0, 1, 2, 3]
def wTop : Fin 4 → ℕ := ![0, 0, 0, 1]

theorem weight_four (w : Fin 4 → ℕ) (m : Fin 4 →₀ ℕ) :
    Finsupp.weight w m = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

theorem weight_deg (m : Fin 4 →₀ ℕ) : Finsupp.weight wDeg m = m.degree := by
  rw [weight_four, degree_formula]
  show m 0 * 1 + m 1 * 1 + m 2 * 1 + m 3 * 1 = m 0 + m 1 + m 2 + m 3
  ring

theorem weight_idx (m : Fin 4 →₀ ℕ) : Finsupp.weight wIdx m = m.weight jetIndex := by
  rw [weight_four, jetIndex_formula]
  show m 0 * 0 + m 1 * 1 + m 2 * 2 + m 3 * 3 = m 1 + 2 * m 2 + 3 * m 3
  ring

theorem weight_top (m : Fin 4 →₀ ℕ) : Finsupp.weight wTop m = m 3 := by
  rw [weight_four]
  show m 0 * 0 + m 1 * 0 + m 2 * 0 + m 3 * 1 = m 3
  ring

theorem weightLift_monomial (w : Fin 4 → ℕ) (u : Fin 4 →₀ ℕ) (c : Geom) :
    weightLift w (MvPolynomial.monomial u c) =
      Polynomial.C (MvPolynomial.monomial u c) * Polynomial.X ^ Finsupp.weight w u := by
  rw [weightLift, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_four, weight_four, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, map_pow]
  ring

/-- The `Y^k` coefficient of the lift is the weight-`k` part. -/
theorem coeff_coeff_weightLift (w : Fin 4 → ℕ) (p : Form) (k : ℕ) (m : Fin 4 →₀ ℕ) :
    ((weightLift w p).coeff k).coeff m =
      if Finsupp.weight w m = k then p.coeff m else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [weightLift_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases hum : u = m
    · subst hum
      by_cases hk : k = Finsupp.weight w u
      · rw [if_pos hk, if_pos hk.symm]
      · rw [if_neg hk, if_neg (fun h => hk h.symm), MvPolynomial.coeff_zero]
    · rw [MvPolynomial.coeff_monomial, if_neg hum]
      split_ifs <;> simp [MvPolynomial.coeff_monomial, hum]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp

theorem coeff_weightLift_ne_zero {w : Fin 4 → ℕ} {p : Form} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ p.support) : (weightLift w p).coeff (Finsupp.weight w m) ≠ 0 := by
  intro h
  have hc := coeff_coeff_weightLift w p (Finsupp.weight w m) m
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at hc
  exact (MvPolynomial.mem_support_iff.mp hm) hc.symm

theorem exists_of_coeff_weightLift {w : Fin 4 → ℕ} {p : Form} {k : ℕ}
    (h : (weightLift w p).coeff k ≠ 0) : ∃ m ∈ p.support, Finsupp.weight w m = k := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp h
  rw [coeff_coeff_weightLift] at hm
  by_cases hk : Finsupp.weight w m = k
  · rw [if_pos hk] at hm
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hk⟩
  · rw [if_neg hk] at hm
    exact absurd rfl hm

theorem weightLift_ne_zero {w : Fin 4 → ℕ} {p : Form} (hp : p ≠ 0) : weightLift w p ≠ 0 := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hp
  intro h
  apply coeff_weightLift_ne_zero (w := w) (MvPolynomial.mem_support_iff.mpr hm)
  rw [h, Polynomial.coeff_zero]

theorem weight_le_natDegree {w : Fin 4 → ℕ} {p : Form} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ p.support) : Finsupp.weight w m ≤ (weightLift w p).natDegree :=
  Polynomial.le_natDegree_of_ne_zero (coeff_weightLift_ne_zero hm)

theorem natTrailingDegree_le_weight {w : Fin 4 → ℕ} {p : Form} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ p.support) : (weightLift w p).natTrailingDegree ≤ Finsupp.weight w m :=
  Polynomial.natTrailingDegree_le_of_ne_zero (coeff_weightLift_ne_zero hm)

theorem exists_natDegree {w : Fin 4 → ℕ} {p : Form} (hp : p ≠ 0) :
    ∃ m ∈ p.support, Finsupp.weight w m = (weightLift w p).natDegree := by
  have h : (weightLift w p).coeff (weightLift w p).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (weightLift_ne_zero hp)
  exact exists_of_coeff_weightLift h

theorem exists_natTrailingDegree {w : Fin 4 → ℕ} {p : Form} (hp : p ≠ 0) :
    ∃ m ∈ p.support, Finsupp.weight w m = (weightLift w p).natTrailingDegree := by
  have h : (weightLift w p).coeff (weightLift w p).natTrailingDegree ≠ 0 :=
    mt Polynomial.trailingCoeff_eq_zero.mp (weightLift_ne_zero hp)
  exact exists_of_coeff_weightLift h

theorem natDegree_lift_mul (w : Fin 4 → ℕ) {p q : Form} (hp : p ≠ 0) (hq : q ≠ 0) :
    (weightLift w (p * q)).natDegree =
      (weightLift w p).natDegree + (weightLift w q).natDegree := by
  rw [map_mul]
  exact Polynomial.natDegree_mul (weightLift_ne_zero hp) (weightLift_ne_zero hq)

theorem natTrailingDegree_lift_mul (w : Fin 4 → ℕ) {p q : Form} (hp : p ≠ 0) (hq : q ≠ 0) :
    (weightLift w (p * q)).natTrailingDegree =
      (weightLift w p).natTrailingDegree + (weightLift w q).natTrailingDegree := by
  rw [map_mul]
  exact Polynomial.natTrailingDegree_mul (weightLift_ne_zero hp) (weightLift_ne_zero hq)

/-! ### Extremes forced by a band -/

theorem band_extremes {Q : Form} {d : ℕ} {lo hi : ℤ} {top : ℕ}
    (hQ : Q ∈ bandSpace d lo hi top) (h0 : Q ≠ 0) :
    (weightLift wDeg Q).natDegree = d ∧ (weightLift wDeg Q).natTrailingDegree = d ∧
      ((weightLift wIdx Q).natDegree : ℤ) ≤ hi ∧
      lo ≤ ((weightLift wIdx Q).natTrailingDegree : ℤ) ∧
      (weightLift wTop Q).natDegree ≤ top := by
  have hb : ∀ m ∈ Q.support, BandExponent d lo hi top m :=
    fun m hm => (MvPolynomial.mem_restrictSupport_iff Geom).mp hQ hm
  obtain ⟨m1, hm1, e1⟩ := exists_natDegree (w := wDeg) h0
  obtain ⟨m2, hm2, e2⟩ := exists_natTrailingDegree (w := wDeg) h0
  obtain ⟨m3, hm3, e3⟩ := exists_natDegree (w := wIdx) h0
  obtain ⟨m4, hm4, e4⟩ := exists_natTrailingDegree (w := wIdx) h0
  obtain ⟨m5, hm5, e5⟩ := exists_natDegree (w := wTop) h0
  obtain ⟨b1, -, -, -⟩ := hb m1 hm1
  obtain ⟨b2, -, -, -⟩ := hb m2 hm2
  obtain ⟨-, -, b3, -⟩ := hb m3 hm3
  obtain ⟨-, b4, -, -⟩ := hb m4 hm4
  obtain ⟨-, -, -, b5⟩ := hb m5 hm5
  rw [weight_deg] at e1 e2
  rw [weight_idx] at e3 e4
  rw [weight_top] at e5
  refine ⟨by omega, by omega, ?_, ?_, by omega⟩
  · rw [← e3]
    exact b3
  · rw [← e4]
    exact b4

/-! ### Extremes of the flag factor, per factor at numeric points -/

theorem weightLift_mapAlgHom (w : Fin 4 → ℕ) (x : Fin 4 → Geom) :
    (Polynomial.mapAlgHom (MvPolynomial.aeval x)).comp (weightLift w) =
      MvPolynomial.aeval (fun i => Polynomial.C (x i) * Polynomial.X ^ w i) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [weightLift]

theorem coeff_weightLift_ne_of_eval {w : Fin 4 → ℕ} {f : Form} {k : ℕ} (x : Fin 4 → Geom)
    (h : (MvPolynomial.aeval (fun i => Polynomial.C (x i) * Polynomial.X ^ w i) f).coeff k ≠ 0) :
    (weightLift w f).coeff k ≠ 0 := by
  intro h0
  apply h
  rw [← weightLift_mapAlgHom w x, AlgHom.comp_apply, Polynomial.coe_mapAlgHom,
    Polynomial.coeff_map, h0, map_zero]

private theorem natTrailingDegree_pow' {p : Polynomial Form} (hp : p ≠ 0) (n : ℕ) :
    (p ^ n).natTrailingDegree = n * p.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih]
    ring

private theorem x0_ne : (MvPolynomial.X 0 : Form) ≠ 0 := MvPolynomial.X_ne_zero _
private theorem x2_ne : (MvPolynomial.X 2 : Form) ≠ 0 := MvPolynomial.X_ne_zero _

theorem natDegree_flag (w : Fin 4 → ℕ) (u : FactorPowers) :
    (weightLift w (flagFactor u)).natDegree =
      u.value * (weightLift w (MvPolynomial.X 0)).natDegree +
        u.jetTwo * (weightLift w (MvPolynomial.X 2)).natDegree +
        u.quad * (weightLift w quadForm).natDegree +
        u.cubic * (weightLift w cubicForm).natDegree := by
  have n0 := weightLift_ne_zero (w := w) x0_ne
  have n2 := weightLift_ne_zero (w := w) x2_ne
  have nQ := weightLift_ne_zero (w := w) quadForm_prime.ne_zero
  have nC := weightLift_ne_zero (w := w) cubicForm_prime.ne_zero
  rw [flagFactor_eq]
  simp only [map_mul, map_pow]
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ n0) (pow_ne_zero _ n2)) (pow_ne_zero _ nQ))
      (pow_ne_zero _ nC),
    Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero _ n0) (pow_ne_zero _ n2))
      (pow_ne_zero _ nQ),
    Polynomial.natDegree_mul (pow_ne_zero _ n0) (pow_ne_zero _ n2),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    Polynomial.natDegree_pow]

theorem natTrailingDegree_flag (w : Fin 4 → ℕ) (u : FactorPowers) :
    (weightLift w (flagFactor u)).natTrailingDegree =
      u.value * (weightLift w (MvPolynomial.X 0)).natTrailingDegree +
        u.jetTwo * (weightLift w (MvPolynomial.X 2)).natTrailingDegree +
        u.quad * (weightLift w quadForm).natTrailingDegree +
        u.cubic * (weightLift w cubicForm).natTrailingDegree := by
  have n0 := weightLift_ne_zero (w := w) x0_ne
  have n2 := weightLift_ne_zero (w := w) x2_ne
  have nQ := weightLift_ne_zero (w := w) quadForm_prime.ne_zero
  have nC := weightLift_ne_zero (w := w) cubicForm_prime.ne_zero
  rw [flagFactor_eq]
  simp only [map_mul, map_pow]
  rw [Polynomial.natTrailingDegree_mul
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ n0) (pow_ne_zero _ n2)) (pow_ne_zero _ nQ))
      (pow_ne_zero _ nC),
    Polynomial.natTrailingDegree_mul (mul_ne_zero (pow_ne_zero _ n0) (pow_ne_zero _ n2))
      (pow_ne_zero _ nQ),
    Polynomial.natTrailingDegree_mul (pow_ne_zero _ n0) (pow_ne_zero _ n2),
    natTrailingDegree_pow' n0, natTrailingDegree_pow' n2, natTrailingDegree_pow' nQ,
    natTrailingDegree_pow' nC]

-- Witness coefficients (all equal to 1) at explicit points.
theorem x0_idx_min : (weightLift wIdx (MvPolynomial.X 0)).natTrailingDegree ≤ 0 :=
  Polynomial.natTrailingDegree_le_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 0, 0, 0] (by simp [wIdx]))

theorem x2_idx_max : 2 ≤ (weightLift wIdx (MvPolynomial.X 2)).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (coeff_weightLift_ne_of_eval ![0, 0, 1, 0] (by simp [wIdx]))

theorem x2_idx_min : (weightLift wIdx (MvPolynomial.X 2)).natTrailingDegree ≤ 2 :=
  Polynomial.natTrailingDegree_le_of_ne_zero
    (coeff_weightLift_ne_of_eval ![0, 0, 1, 0] (by simp [wIdx]))

theorem quad_idx_max : 2 ≤ (weightLift wIdx quadForm).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 0, 1, 0] (by simp [wIdx, quadForm]))

theorem quad_idx_min : (weightLift wIdx quadForm).natTrailingDegree ≤ 1 :=
  Polynomial.natTrailingDegree_le_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 1, 0, 0] (by simp [wIdx, quadForm]))

theorem cubic_idx_max : 3 ≤ (weightLift wIdx cubicForm).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 0, 0, 1] (by simp [wIdx, cubicForm]))

theorem cubic_idx_min : (weightLift wIdx cubicForm).natTrailingDegree ≤ 2 :=
  Polynomial.natTrailingDegree_le_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 0, 1, 0] (by simp [wIdx, cubicForm]))

theorem cubic_top_max : 1 ≤ (weightLift wTop cubicForm).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (coeff_weightLift_ne_of_eval ![1, 0, 0, 1] (by simp [wTop, cubicForm]))

theorem flag_extremes (u : FactorPowers) :
    u.maxIndex ≤ (weightLift wIdx (flagFactor u)).natDegree ∧
      (weightLift wIdx (flagFactor u)).natTrailingDegree ≤ u.minIndex ∧
      u.maxTop ≤ (weightLift wTop (flagFactor u)).natDegree := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_flag]
    unfold FactorPowers.maxIndex
    have h2 := Nat.mul_le_mul_left u.jetTwo x2_idx_max
    have hq := Nat.mul_le_mul_left u.quad quad_idx_max
    have hc := Nat.mul_le_mul_left u.cubic cubic_idx_max
    omega
  · rw [natTrailingDegree_flag]
    unfold FactorPowers.minIndex
    have h0 := Nat.mul_le_mul_left u.value x0_idx_min
    have h2 := Nat.mul_le_mul_left u.jetTwo x2_idx_min
    have hq := Nat.mul_le_mul_left u.quad quad_idx_min
    have hc := Nat.mul_le_mul_left u.cubic cubic_idx_min
    omega
  · rw [natDegree_flag]
    unfold FactorPowers.maxTop
    have hc := Nat.mul_le_mul_left u.cubic cubic_top_max
    omega

/-! ### O3 -/

/-- O3 proved: the cofactor of a band element by a flag factor lies in the shifted band. -/
theorem cofactorBand : CofactorBand := by
  intro u h d lo hi top hmem
  by_cases h0 : h = 0
  · rw [h0]
    exact Submodule.zero_mem _
  have hL0 := flagFactor_ne_zero u
  have hP0 : flagFactor u * h ≠ 0 := mul_ne_zero hL0 h0
  obtain ⟨dP, dP', iP, iP', tP⟩ := band_extremes hmem hP0
  obtain ⟨dL, dL', -, -, -⟩ := band_extremes (flagFactor_mem_band u) hL0
  obtain ⟨fI, fI', fT⟩ := flag_extremes u
  have aD := natDegree_lift_mul wDeg hL0 h0
  have aD' := natTrailingDegree_lift_mul wDeg hL0 h0
  have aI := natDegree_lift_mul wIdx hL0 h0
  have aI' := natTrailingDegree_lift_mul wIdx hL0 h0
  have aT := natDegree_lift_mul wTop hL0 h0
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro m hm
  have hm' : m ∈ h.support := Finset.mem_coe.mp hm
  have l1 := weight_le_natDegree (w := wDeg) hm'
  have l2 := natTrailingDegree_le_weight (w := wDeg) hm'
  have l3 := weight_le_natDegree (w := wIdx) hm'
  have l4 := natTrailingDegree_le_weight (w := wIdx) hm'
  have l5 := weight_le_natDegree (w := wTop) hm'
  rw [weight_deg] at l1 l2
  rw [weight_idx] at l3 l4
  rw [weight_top] at l5
  show BandExponent (d - u.degree) (lo - (u.minIndex : ℤ)) (hi - (u.maxIndex : ℤ))
    (top - u.maxTop) m
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Two-flag block bound with O2 and O3 both discharged: no hypotheses beyond the band fits. -/
theorem rank_block_le_twoFlag_proved (s : ℕ) (g : ℤ) (v w : FactorPowers)
    (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10)
    (hw : w.degree ≤ residualDegree s ∧ w.maxIndex ≤ 48 ∧ w.maxTop ≤ 10) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) + (flagKernel s g v + flagKernel s g w) ≤
      bandCount (residualDegree s) (-g) 48 10 + lcmBand s g v w :=
  rank_block_le_twoFlag_of_cofactor cofactorBand s g v w hv hw

end
end K1_13_1_1
end PackSource_K1_13_1_1CofactorFlag
