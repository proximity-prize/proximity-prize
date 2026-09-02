/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Non-toric Hasse-rank defect gate

A ninth-order singular-contact attack asks the first eight positive Hasse derivatives of a
coefficient polynomial to vanish at an extension-field point.  On the dense coefficient window
`X^(s+1), ..., X^(s+8d)`, this is an `8d` by `8d` confluent Vandermonde system over the base
field, where `d` is the degree of the point.

This file records a characteristic-independent polynomial form of the rank argument.  Eight
positive Hasse contacts at a node make the eighth power of its linear factor divide the ordinary
derivative.  At distinct nodes these powers are coprime.  If the derivative is supported in a
dense shifted window, it is `X^s * R` with `deg R < 8d`; at nonzero nodes the `X^s` factor is a
unit modulo the node locator, so the locator's eighth power must divide `R`, forcing `R = 0`.

Thus the only rank-defect loci of the confluent matrix are a zero node, colliding nodes, or an
inseparable derivative column.  The companion exact audit checks the degree-`1,2,3,6` benchmark
matrices and the determinant shift formula.  In the legal chart all exponents are below the
characteristic, so no inseparable column occurs.  What remains outside this gate is a sparse or
nonlinear selector-to-coefficient map that contains no dense `8d` window; this is a scoped
closure, not a score claim.
-/

namespace ProximityPrize.SubmissionUpper.HasseRankDefectGate

open Polynomial

variable {F : Type*} [Field F]

/-- The first eight positive Hasse derivatives vanish at `x`. -/
def eighthContact (P : Polynomial F) (x : F) : Prop :=
  ∀ j, 1 ≤ j → j ≤ 8 → (Polynomial.hasseDeriv j P).eval x = 0

/-- Eight positive Hasse contacts make the node an eightfold root of the ordinary derivative.
This implication does not divide by a factorial and is therefore characteristic-independent. -/
theorem local_eighth_power_dvd_derivative
    (P : Polynomial F) (x : F) (hcontact : eighthContact P x) :
    (Polynomial.X - Polynomial.C x) ^ 8 ∣ P.derivative := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  intro j hj
  change (Polynomial.taylor x P.derivative).coeff j = 0
  rw [Polynomial.taylor_coeff]
  have hcomposition := LinearMap.congr_fun (Polynomial.hasseDeriv_comp j 1) P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hcomposition
  rw [← Polynomial.hasseDeriv_one', hcomposition]
  simp [hcontact (j + 1) (by omega) (by omega)]

/-- Locator of a finite set of distinct contact nodes. -/
noncomputable def nodeLocator (nodes : Finset F) : Polynomial F :=
  ∏ x ∈ nodes, (Polynomial.X - Polynomial.C x)

/-- Contact powers at distinct nodes multiply because their linear factors are pairwise coprime. -/
theorem nodeLocator_eighth_power_dvd_derivative
    (P : Polynomial F) (nodes : Finset F)
    (hcontact : ∀ x ∈ nodes, eighthContact P x) :
    nodeLocator nodes ^ 8 ∣ P.derivative := by
  classical
  rw [nodeLocator, ← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro x _ y _ hxy
    exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy).pow
  · intro x hx
    exact local_eighth_power_dvd_derivative P x (hcontact x hx)

/-- In the unshifted dense chart, a rank defect forces the derivative to vanish.  A nonempty
`d`-node set supplies exactly `8d` independent contact coordinates unless the derivative map
itself is inseparable. -/
theorem dense_eighth_contact_forces_derivative_zero
    (P : Polynomial F) (nodes : Finset F) (hnodes : nodes.Nonempty)
    (hdegree : P.natDegree ≤ 8 * nodes.card)
    (hcontact : ∀ x ∈ nodes, eighthContact P x) :
    P.derivative = 0 := by
  by_contra hderivative
  have hdiv := nodeLocator_eighth_power_dvd_derivative P nodes hcontact
  have hlower : 8 * nodes.card ≤ P.derivative.natDegree := by
    simpa [nodeLocator] using Polynomial.natDegree_le_of_dvd hdiv hderivative
  have hupper : P.derivative.natDegree ≤ P.natDegree - 1 :=
    Polynomial.natDegree_derivative_le P
  have hpositive : 0 < nodes.card := Finset.card_pos.mpr hnodes
  omega

/-- Shifted dense-window form.  If all nodes are nonzero and
`P' = X^offset * R` with `deg R < 8d`, the shift is a unit at every node and cannot create a
confluent-Vandermonde rank defect. -/
theorem shifted_dense_eighth_contact_forces_derivative_zero
    (P R : Polynomial F) (nodes : Finset F) (offset : ℕ)
    (hnodes : ∀ x ∈ nodes, x ≠ 0)
    (hshape : P.derivative = Polynomial.X ^ offset * R)
    (hdegree : R.natDegree < 8 * nodes.card)
    (hcontact : ∀ x ∈ nodes, eighthContact P x) :
    P.derivative = 0 := by
  classical
  have hdiv : nodeLocator nodes ^ 8 ∣ Polynomial.X ^ offset * R := by
    rw [← hshape]
    exact nodeLocator_eighth_power_dvd_derivative P nodes hcontact
  have hcoprimeBase : IsCoprime (nodeLocator nodes) Polynomial.X := by
    rw [nodeLocator]
    apply IsCoprime.prod_left
    intro x hx
    simpa only [Function.onFun, id_eq, Polynomial.C_0, sub_zero] using
      (Polynomial.pairwise_coprime_X_sub_C Function.injective_id (hnodes x hx))
  have hcoprime : IsCoprime (nodeLocator nodes ^ 8) (Polynomial.X ^ offset) :=
    hcoprimeBase.pow
  have hdivR : nodeLocator nodes ^ 8 ∣ R := hcoprime.dvd_of_dvd_mul_left hdiv
  have hRzero : R = 0 := by
    by_contra hR
    have hlower : 8 * nodes.card ≤ R.natDegree := by
      simpa [nodeLocator] using Polynomial.natDegree_le_of_dvd hdivR hR
    omega
  rw [hshape, hRzero, mul_zero]

/-- Below the characteristic, the remaining derivative-zero locus contains only constants. -/
theorem eq_constant_of_derivative_zero_below_characteristic
    {characteristic : ℕ} [CharP F characteristic]
    (P : Polynomial F) (hdegree : P.natDegree < characteristic)
    (hderivative : P.derivative = 0) :
    P = Polynomial.C (P.coeff 0) := by
  ext k
  by_cases hkzero : k = 0
  · subst k
    simp
  by_cases hklarge : P.natDegree < k
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hklarge]
    rw [Polynomial.coeff_C_of_ne_zero hkzero]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
  have hkle : n + 1 ≤ P.natDegree := Nat.le_of_not_gt hklarge
  have hkpositive : 0 < n + 1 := Nat.succ_pos n
  have hkchar : n + 1 < characteristic := hkle.trans_lt hdegree
  have hkcast : (n : F) + 1 ≠ 0 := by
    intro hzero
    have hzero' : ((n + 1 : ℕ) : F) = 0 := by simpa using hzero
    have hdvd : characteristic ∣ n + 1 :=
      (CharP.cast_eq_zero_iff F characteristic (n + 1)).mp hzero'
    exact (Nat.not_dvd_of_pos_of_lt hkpositive hkchar) hdvd
  have hcoefficient : P.coeff (n + 1) = 0 := by
    have hderivativeCoefficient := congrArg (fun Q : Polynomial F ↦ Q.coeff n) hderivative
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hderivativeCoefficient
    exact (mul_eq_zero.mp hderivativeCoefficient).resolve_right hkcast
  rw [hcoefficient, Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero n)]

/-- Complete dense-window injectivity statement in positive characteristic below the first
inseparable exponent. -/
theorem shifted_dense_eighth_contact_eq_constant
    {characteristic : ℕ} [CharP F characteristic]
    (P R : Polynomial F) (nodes : Finset F) (offset : ℕ)
    (hnodes : ∀ x ∈ nodes, x ≠ 0)
    (hshape : P.derivative = Polynomial.X ^ offset * R)
    (hRdegree : R.natDegree < 8 * nodes.card)
    (hPdegree : P.natDegree < characteristic)
    (hcontact : ∀ x ∈ nodes, eighthContact P x) :
    P = Polynomial.C (P.coeff 0) := by
  apply eq_constant_of_derivative_zero_below_characteristic P hPdegree
  exact shifted_dense_eighth_contact_forces_derivative_zero
    P R nodes offset hnodes hshape hRdegree hcontact

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : ℕ := 2130706433
def legalRowDegree : ℕ := 131071
def challengeThreshold : ℕ := 274980728111395088

/-- Every legal differentiated exponent is a nonzero base-field scalar. -/
theorem legal_exponents_below_characteristic :
    48 ≤ legalRowDegree ∧ legalRowDegree < baseFieldCardinality := by
  norm_num [legalRowDegree, baseFieldCardinality]

/-- Every positive legal exponent remains nonzero modulo the benchmark characteristic. -/
theorem legal_exponent_remainder_ne_zero
    (k : ℕ) (hpositive : 1 ≤ k) (hlegal : k ≤ legalRowDegree) :
    k % baseFieldCardinality ≠ 0 := by
  rw [Nat.mod_eq_of_lt]
  · omega
  · exact hlegal.trans_lt legal_exponents_below_characteristic.2

/-- Exact base-coordinate costs for degree-two, degree-three, and degree-six points. -/
theorem benchmark_dense_hasse_costs :
    8 * 2 = 16 ∧ 8 * 3 = 24 ∧ 8 * 6 = 48 := by
  norm_num

/-- A base-field chart cannot itself hold the required challenge family; degree at least two is
the first threshold-capable extension chart, where the dense Hasse cost is already sixteen. -/
theorem benchmark_threshold_window :
    baseFieldCardinality < challengeThreshold ∧
      challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [baseFieldCardinality, challengeThreshold]

#print axioms local_eighth_power_dvd_derivative
#print axioms nodeLocator_eighth_power_dvd_derivative
#print axioms dense_eighth_contact_forces_derivative_zero
#print axioms shifted_dense_eighth_contact_forces_derivative_zero
#print axioms eq_constant_of_derivative_zero_below_characteristic
#print axioms shifted_dense_eighth_contact_eq_constant
#print axioms legal_exponent_remainder_ne_zero
#print axioms benchmark_dense_hasse_costs

end ProximityPrize.SubmissionUpper.HasseRankDefectGate
