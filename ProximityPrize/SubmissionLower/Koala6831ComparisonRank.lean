import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open Polynomial

variable {R I : Type*} [CommRing R] [IsDomain R]

structure SymbolicRow (R : Type*) [CommRing R] where
  beta : Polynomial R
  first : Polynomial R
  second : Polynomial R

def SymbolicRow.atNode (q : SymbolicRow R) (x u v : R) : R :=
  q.beta.eval x + q.first.eval x * u + q.second.eval x * v

theorem eq_zero_of_vanishing_on_nodes (P : Polynomial R)
    (x : I ↪ R) (nodes : Finset I) (hdegree : P.natDegree < nodes.card)
    (hvanish : ∀ i ∈ nodes, P.eval (x i) = 0) :
    P = 0 := by
  classical
  by_contra hp
  apply Nat.not_le_of_gt hdegree
  calc
    nodes.card = (nodes.image x).card :=
      (Finset.card_image_of_injective _ x.injective).symm
    _ ≤ P.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Polynomial.mem_roots hp).mpr (hvanish i hi)

theorem first_cross_beta_eq_of_determinant_zero
    (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (q r : SymbolicRow R) (a b : ℕ) (hbudget : a + b < nodes.card)
    (hqFirst : q.first.natDegree ≤ a) (hrFirst : r.first.natDegree ≤ a)
    (hqBeta : q.beta.natDegree ≤ b) (hrBeta : r.beta.natDegree ≤ b)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0)
    (hr : ∀ i ∈ nodes, r.atNode (x i) (u i) (v i) = 0)
    (hdet : q.first * r.second = r.first * q.second) :
    q.first * r.beta = r.first * q.beta := by
  apply sub_eq_zero.mp
  apply eq_zero_of_vanishing_on_nodes _ x nodes
  · have hleft : (q.first * r.beta).natDegree ≤ a + b := calc
      _ ≤ q.first.natDegree + r.beta.natDegree := Polynomial.natDegree_mul_le
      _ ≤ a + b := Nat.add_le_add hqFirst hrBeta
    have hright : (r.first * q.beta).natDegree ≤ a + b := calc
      _ ≤ r.first.natDegree + q.beta.natDegree := Polynomial.natDegree_mul_le
      _ ≤ a + b := Nat.add_le_add hrFirst hqBeta
    exact ((Polynomial.natDegree_sub_le _ _).trans (max_le hleft hright)).trans_lt hbudget
  · intro i hi
    have hqNode := hq i hi
    have hrNode := hr i hi
    have hdetNode := congrArg (fun P : Polynomial R => P.eval (x i)) hdet
    simp only [SymbolicRow.atNode] at hqNode hrNode
    simp only [Polynomial.eval_mul] at hdetNode
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    linear_combination (q.first.eval (x i)) * hrNode -
      (r.first.eval (x i)) * hqNode - (v i) * hdetNode

theorem cross_beta_eq_of_determinant_zero
    (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (q r : SymbolicRow R) (a b : ℕ) (hbudget : a + b < nodes.card)
    (hqFirst : q.first.natDegree ≤ a) (hrFirst : r.first.natDegree ≤ a)
    (hqSecond : q.second.natDegree ≤ a) (hrSecond : r.second.natDegree ≤ a)
    (hqBeta : q.beta.natDegree ≤ b) (hrBeta : r.beta.natDegree ≤ b)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0)
    (hr : ∀ i ∈ nodes, r.atNode (x i) (u i) (v i) = 0)
    (hdet : q.first * r.second = r.first * q.second) :
    q.first * r.beta = r.first * q.beta ∧ q.second * r.beta = r.second * q.beta := by
  constructor
  · exact first_cross_beta_eq_of_determinant_zero x nodes u v q r a b hbudget
      hqFirst hrFirst hqBeta hrBeta hq hr hdet
  · let q' : SymbolicRow R := ⟨q.beta, q.second, q.first⟩
    let r' : SymbolicRow R := ⟨r.beta, r.second, r.first⟩
    have hq' : ∀ i ∈ nodes, q'.atNode (x i) (v i) (u i) = 0 := by
      intro i hi
      simpa only [q', SymbolicRow.atNode, add_assoc,
        add_comm (q.second.eval (x i) * v i) (q.first.eval (x i) * u i)] using hq i hi
    have hr' : ∀ i ∈ nodes, r'.atNode (x i) (v i) (u i) = 0 := by
      intro i hi
      simpa only [r', SymbolicRow.atNode, add_assoc,
        add_comm (r.second.eval (x i) * v i) (r.first.eval (x i) * u i)] using hr i hi
    have hd' : q'.first * r'.second = r'.first * q'.second := by
      change q.second * r.first = r.second * q.first
      calc
        q.second * r.first = r.first * q.second := mul_comm _ _
        _ = q.first * r.second := hdet.symm
        _ = r.second * q.first := mul_comm _ _
    exact first_cross_beta_eq_of_determinant_zero x nodes v u q' r' a b hbudget
      hqSecond hrSecond hqBeta hrBeta hq' hr' hd'

theorem exists_polynomial_multiplier_of_primitive_first
    [GCDMonoid (Polynomial R)] (q r : SymbolicRow R)
    (hq : q.first ≠ 0) (hprimitive : IsUnit (gcd q.beta (gcd q.first q.second)))
    (hsecond : q.first * r.second = r.first * q.second)
    (hbeta : q.first * r.beta = r.first * q.beta) :
    ∃ m : Polynomial R, r.beta = m * q.beta ∧
      r.first = m * q.first ∧ r.second = m * q.second := by
  have hdBeta : q.first ∣ q.beta * r.first := by
    rw [mul_comm q.beta r.first, ← hbeta]
    exact dvd_mul_right _ _
  have hdSecond : q.first ∣ q.second * r.first := by
    rw [mul_comm q.second r.first, ← hsecond]
    exact dvd_mul_right _ _
  have hdBoth : q.first ∣ gcd q.first q.second * r.first :=
    (dvd_gcd (dvd_mul_right q.first r.first) hdSecond).trans
      (gcd_mul_right' r.first q.first q.second).dvd
  have hdPrimitive : q.first ∣ gcd q.beta (gcd q.first q.second) * r.first :=
    (dvd_gcd hdBeta hdBoth).trans (gcd_mul_right' r.first q.beta (gcd q.first q.second)).dvd
  have hdFirst : q.first ∣ r.first := by
    have hu : gcd q.beta (gcd q.first q.second) ∣ 1 := isUnit_iff_dvd_one.mp hprimitive
    have h := mul_dvd_mul hu (dvd_refl r.first)
    exact hdPrimitive.trans (by simpa only [one_mul] using h)
  obtain ⟨m, hm⟩ := hdFirst
  refine ⟨m, ?_, by rw [hm, mul_comm], ?_⟩
  · apply mul_left_cancel₀ hq
    rw [hbeta, hm, mul_assoc]
  · apply mul_left_cancel₀ hq
    rw [hsecond, hm, mul_assoc]

theorem exists_primitive_factor_of_first_ne_zero
    [GCDMonoid (Polynomial R)] (r : SymbolicRow R) (hr : r.first ≠ 0) :
    ∃ (q : SymbolicRow R) (m : Polynomial R),
      m ≠ 0 ∧ q.first ≠ 0 ∧ IsUnit (gcd q.beta (gcd q.first q.second)) ∧
      r.beta = m * q.beta ∧ r.first = m * q.first ∧ r.second = m * q.second := by
  let m := gcd r.beta (gcd r.first r.second)
  obtain ⟨β, hβ⟩ := gcd_dvd_left r.beta (gcd r.first r.second)
  obtain ⟨α, hα⟩ := (gcd_dvd_right r.beta (gcd r.first r.second)).trans
    (gcd_dvd_left r.first r.second)
  obtain ⟨δ, hδ⟩ := (gcd_dvd_right r.beta (gcd r.first r.second)).trans
    (gcd_dvd_right r.first r.second)
  change r.beta = m * β at hβ
  change r.first = m * α at hα
  change r.second = m * δ at hδ
  have hm : m ≠ 0 := fun h => hr (by simpa [h] using hα)
  have hα₀ : α ≠ 0 := fun h => hr (by simpa [h] using hα)
  have hUnit : IsUnit (gcd β (gcd α δ)) := by
    let d := gcd β (gcd α δ)
    have hdβ : d ∣ β := gcd_dvd_left β (gcd α δ)
    have hdα : d ∣ α := (gcd_dvd_right β (gcd α δ)).trans (gcd_dvd_left α δ)
    have hdδ : d ∣ δ := (gcd_dvd_right β (gcd α δ)).trans (gcd_dvd_right α δ)
    have hd1 : m * d ∣ r.beta := hβ ▸ mul_dvd_mul_left m hdβ
    have hd2 : m * d ∣ r.first := hα ▸ mul_dvd_mul_left m hdα
    have hd3 : m * d ∣ r.second := hδ ▸ mul_dvd_mul_left m hdδ
    have hmd : m * d ∣ m := dvd_gcd hd1 (dvd_gcd hd2 hd3)
    apply isUnit_iff_dvd_one.mpr
    apply (mul_dvd_mul_iff_left hm).mp
    simpa only [mul_one] using hmd
  exact ⟨⟨β, α, δ⟩, m, hm, hα₀, hUnit, hβ, hα, hδ⟩

theorem multiplier_eval_eq_zero_of_bad_node
    (q r : SymbolicRow R) (m : Polynomial R) (x u v : R)
    (hβ : r.beta = m * q.beta) (hα : r.first = m * q.first)
    (hδ : r.second = m * q.second) (hr : r.atNode x u v = 0)
    (hq : q.atNode x u v ≠ 0) :
    m.eval x = 0 := by
  have hfactor : r.atNode x u v = m.eval x * q.atNode x u v := by
    simp only [SymbolicRow.atNode, hβ, hα, hδ, Polynomial.eval_mul]
    ring
  exact (mul_eq_zero.mp (hfactor.symm.trans hr)).resolve_right hq

theorem beta_eq_zero_of_no_active_coefficient
    (q : SymbolicRow R) (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (hβ : q.beta.natDegree < nodes.card)
    (hfirst : q.first = 0) (hsecond : q.second = 0)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0) :
    q.beta = 0 := by
  apply eq_zero_of_vanishing_on_nodes q.beta x nodes hβ
  intro i hi
  simpa [SymbolicRow.atNode, hfirst, hsecond] using hq i hi

noncomputable def badNodeLocator (x : I ↪ R) (bad : Finset I) : Polynomial R := by
  classical
  exact ((bad.image x).val.map fun a => Polynomial.X - Polynomial.C a).prod

theorem badNodeLocator_natDegree (x : I ↪ R) (bad : Finset I) :
    (badNodeLocator x bad).natDegree = bad.card := by
  classical
  rw [badNodeLocator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  exact Finset.card_image_of_injective _ x.injective

theorem badNodeLocator_dvd_of_vanishing (x : I ↪ R) (bad : Finset I) (m : Polynomial R)
    (hm : ∀ i ∈ bad, m.eval (x i) = 0) : badNodeLocator x bad ∣ m := by
  classical
  by_cases hz : m = 0
  · simp [hz]
  unfold badNodeLocator
  apply (Multiset.prod_X_sub_C_dvd_iff_le_roots hz _).mpr
  apply (Multiset.le_iff_subset (bad.image x).nodup).mpr
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr ha)
  exact (Polynomial.mem_roots hz).mpr (hm i hi)

private noncomputable def withSeedVariables {S : Type*}
    (P : Polynomial (MvPolynomial S R)) : MvPolynomial (Option S) R :=
  (MvPolynomial.optionEquivLeft R S).symm P

omit [IsDomain R] in
private theorem withSeedVariables_degree_le_iff {S : Type*}
    (P : Polynomial (MvPolynomial S R)) (i : S) (d : ℕ) :
    (withSeedVariables P).degreeOf (some i) ≤ d ↔
      ∀ n, (P.coeff n).degreeOf i ≤ d := by
  classical
  constructor
  · intro h n
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hsupport : e.optionElim n ∈ (withSeedVariables P).support := by
      apply (MvPolynomial.mem_support_coeff_optionEquivLeft (R := R)).mp
      simpa [withSeedVariables] using he
    simpa only [Finsupp.optionElim_apply_some] using
      MvPolynomial.degreeOf_le_iff.mp h _ hsupport
  · intro h
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hsupport : e.some ∈ (P.coeff (e none)).support := by
      have hpart : e.some.optionElim (e none) ∈ (withSeedVariables P).support := by
        rwa [Finsupp.optionElim_some]
      have hs := (MvPolynomial.mem_support_coeff_optionEquivLeft (R := R)).mpr hpart
      simpa [withSeedVariables] using hs
    simpa only [Finsupp.some_apply] using MvPolynomial.degreeOf_le_iff.mp (h (e none)) _ hsupport

theorem multiplier_seed_coeff_degree_le {S : Type*}
    (m q r : Polynomial (MvPolynomial S R)) (i : S) (d : ℕ)
    (hr : r = m * q) (hr0 : r ≠ 0) (hdegree : ∀ n, (r.coeff n).degreeOf i ≤ d) :
    ∀ n, (m.coeff n).degreeOf i ≤ d := by
  have hm : m ≠ 0 := fun h => hr0 (by simpa [h] using hr)
  have hq : q ≠ 0 := fun h => hr0 (by simpa [h] using hr)
  have hm' : withSeedVariables m ≠ 0 := by
    intro h
    apply hm
    apply (MvPolynomial.optionEquivLeft R S).symm.injective
    simpa [withSeedVariables] using h
  have hq' : withSeedVariables q ≠ 0 := by
    intro h
    apply hq
    apply (MvPolynomial.optionEquivLeft R S).symm.injective
    simpa [withSeedVariables] using h
  have hr' : withSeedVariables r = withSeedVariables m * withSeedVariables q := by
    simp [withSeedVariables, hr]
  have hb := (withSeedVariables_degree_le_iff r i d).mpr hdegree
  rw [hr', MvPolynomial.degreeOf_mul_eq hm' hq'] at hb
  apply (withSeedVariables_degree_le_iff m i d).mp
  omega

end ProximityPrize.SubmissionLower.Koala6831Comparison
