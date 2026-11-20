import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators
open Polynomial

section Triangular

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable {L : ℕ}

noncomputable def triangularMultiplication (q : Polynomial S) (order : Fin L → ℕ) :
    (Fin L → S) →ₗ[K] (Fin L → S) where
  toFun f i := ∑ j, (X ^ (j : ℕ) * q ^ order j).coeff i * f j
  map_add' f g := by
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem triangularMultiplication_apply (q : Polynomial S) (order : Fin L → ℕ)
    (f : Fin L → S) (i : Fin L) :
    triangularMultiplication (K := K) q order f i =
      (∑ j : Fin L, X ^ (j : ℕ) * q ^ order j * C (f j)).coeff i := by
  simp only [triangularMultiplication, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C]

theorem triangularMultiplication_injective [IsDomain S]
    (q : Polynomial S) (q0 : q.coeff 0 ≠ 0) (order : Fin L → ℕ) :
    Function.Injective (triangularMultiplication (K := K) q order) := by
  classical
  intro f g heq
  have conflict : ∀ n (hn : n < L), f ⟨n,hn⟩ = g ⟨n,hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
      intro hn
      let i : Fin L := ⟨n,hn⟩
      let terms (r : Fin L → S) (j : Fin L) : S :=
        (X ^ (j : ℕ) * q ^ order j).coeff i * r j
      have hsum : (∑ j, terms f j) = ∑ j, terms g j := congrFun heq i
      have hother : (∑ j ∈ (Finset.univ : Finset (Fin L)).erase i, terms f j) =
          ∑ j ∈ (Finset.univ : Finset (Fin L)).erase i, terms g j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hne : j ≠ i := (Finset.mem_erase.mp hj).1
        have hvne : (j : ℕ) ≠ (i : ℕ) := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hvne with hlt | hgt
        · have hfg := inductionHypothesis (j : ℕ) hlt j.isLt
          exact congrArg ((X ^ (j : ℕ) * q ^ order j).coeff i * ·) hfg
        · simp only [terms, Polynomial.coeff_X_pow_mul', ite_eq_right (not_le.mpr hgt), zero_mul]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hother] at hsum
      have hdiag := add_left_cancel hsum
      have hq : (X ^ (i : ℕ) * q ^ order i).coeff i ≠ 0 := by
        rw [Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
          Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
          ← Polynomial.coeff_zero_eq_eval_zero]
        exact pow_ne_zero _ q0
      exact mul_left_cancel₀ hq hdiag
  ext i
  exact conflict i i.isLt

theorem term_mem_contact (l m i k : ℕ) (q : Polynomial S) (c : S)
    (hk : k ≤ m) (horder : l * (m - k) ≤ i) :
    X ^ i * q ^ k * C c ∈ Ideal.span ({X ^ l,q} : Set (Polynomial S)) ^ m := by
  let J := Ideal.span ({X ^ l,q} : Set (Polynomial S))
  have hX : X ^ l ∈ J := Ideal.subset_span (by simp)
  have hq : q ∈ J := Ideal.subset_span (by simp)
  have hproduct := Ideal.mul_mem_mul (Ideal.pow_mem_pow hX (m-k)) (Ideal.pow_mem_pow hq k)
  rw [← pow_add, Nat.sub_add_cancel hk, ← pow_mul] at hproduct
  have h := Ideal.mul_mem_left _ (X ^ (i - l*(m-k))) hproduct
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel horder] at h
  exact Ideal.mul_mem_right _ _ h

theorem sum_mem_virtual_contact (l m : ℕ) (q : Polynomial S)
    (order : Fin L → ℕ) (valid : ∀ i, order i ≤ m ∧ l * (m - order i) ≤ (i : ℕ))
    (f : Fin L → S) :
    (∑ i : Fin L, X ^ (i : ℕ) * q ^ order i * C (f i)) ∈
      Ideal.span ({X ^ l,q} : Set (Polynomial S)) ^ m := by
  apply Submodule.sum_mem
  exact fun i _ => term_mem_contact l m i (order i) q (f i) (valid i).1 (valid i).2

theorem order_from_layer (l m i : ℕ) :
    m - i / l ≤ m ∧ l * (m - (m - i / l)) ≤ i := by
  have h : m - (m - i / l) ≤ i / l := by generalize i / l = t; omega
  exact ⟨Nat.sub_le _ _, by
    calc
      _ ≤ l * (i/l) := Nat.mul_le_mul_left l h
      _ = i/l*l := Nat.mul_comm _ _
      _ ≤ i := Nat.div_mul_le_self i l⟩


end Triangular

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
