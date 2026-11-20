import Mathlib.Algebra.Polynomial.Eval.Degree



namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial
open scoped BigOperators

noncomputable section

set_option autoImplicit false

def clearAux {R : Type*} [CommSemiring R]
    (a b : R) (q : ℕ) (P : Polynomial R) : R :=
  ∑ i ∈ Finset.range (q + 1), a ^ (q - i) * (P.coeff i * b ^ i)

theorem clearAux_add {R : Type*} [CommSemiring R]
    (a b : R) (q : ℕ) (P Q : Polynomial R) :
    clearAux a b q (P + Q) = clearAux a b q P + clearAux a b q Q := by
  simp [clearAux, coeff_add, add_mul, mul_add, Finset.sum_add_distrib]


theorem clearAux_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (a b : R) (q : ℕ) (P : Polynomial R) :
    φ (clearAux a b q P) = clearAux (φ a) (φ b) q (P.map φ) := by
  simp [clearAux]

theorem clearAux_pow_mul {R : Type*} [CommSemiring R]
    (a b : R) {q j : ℕ} (P : Polynomial R)
    (hdeg : P.natDegree ≤ j) (hjq : j ≤ q) :
    clearAux a b q P = a ^ (q - j) * clearAux a b j P := by
  unfold clearAux
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range (j + 1), a ^ (q - i) * (P.coeff i * b ^ i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hjq))
      intro i _ hi
      have hji : j < i := by
        exact Nat.lt_of_not_ge fun hij => hi (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hji)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij := Finset.mem_range.mp hi
      rw [← mul_assoc (a ^ (q-j)), ← pow_add,
        show q-j+(j-i) = q-i by omega]

theorem clearAux_mul_normalized {R : Type*} [CommSemiring R]
    (a u : R) (q : ℕ) (P : Polynomial R) (hdeg : P.natDegree ≤ q) :
    clearAux a (a * u) q P = a ^ q * P.eval u := by
  unfold clearAux
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  rw [mul_pow]
  calc
    a ^ (q - i) * (P.coeff i * (a ^ i * u ^ i)) =
        (a ^ (q - i) * a ^ i) * (P.coeff i * u ^ i) := by ac_rfl
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ q)]

private theorem eval_clearAux_top {F : Type*} [Field F] (a b : Polynomial F)
    (z : F) (P : Polynomial (Polynomial F)) (ha : a.eval z = 0) :
    (clearAux a b P.natDegree P).eval z =
      (P.coeff P.natDegree).eval z * (b.eval z) ^ P.natDegree := by
  unfold clearAux
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow]
  rw [Finset.sum_eq_single P.natDegree]
  · simp
  · intro i hi hne
    have hi := Finset.mem_range.mp hi
    have hpos : P.natDegree - i ≠ 0 := by omega
    simp [ha, zero_pow hpos]
  · simp

theorem clearAux_ne_zero_of_seed_free {F : Type*} [Field F]
    (a b : Polynomial F) (z : F) (P : Polynomial (Polynomial F)) (q : ℕ)
    (ha : a ≠ 0) (haroot : a.eval z = 0) (hb : b.eval z ≠ 0)
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ q)
    (hfree : ∀ i, 0 < i → ∃ c : F, P.coeff i = C c) :
    clearAux a b q P ≠ 0 := by
  rw [clearAux_pow_mul a b P le_rfl hdeg]
  apply mul_ne_zero (pow_ne_zero _ ha)
  by_cases hj : P.natDegree = 0
  · have hcoeff : P.coeff 0 ≠ 0 := by
      rw [← hj, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hP
    simpa [hj, clearAux] using hcoeff
  · obtain ⟨c,hc⟩ := hfree P.natDegree (Nat.pos_of_ne_zero hj)
    have hcne : c ≠ 0 := by
      intro hz
      rw [hz, map_zero, Polynomial.coeff_natDegree] at hc
      exact (Polynomial.leadingCoeff_ne_zero.mpr hP) hc
    intro hzero
    have hh := eval_clearAux_top a b z P haroot
    rw [hzero, Polynomial.eval_zero, hc, Polynomial.eval_C] at hh
    exact mul_ne_zero hcne (pow_ne_zero _ hb) hh.symm

theorem clearAux_ne_zero_of_affine {R F : Type*} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (a₀ a₁ b₀ b₁ : R) (ha₁ : a₁ ≠ 0) (hres : a₁*b₀ ≠ a₀*b₁)
    (P : Polynomial (Polynomial R)) (q : ℕ)
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ q)
    (hfree : ∀ i, 0 < i → ∃ c : R, P.coeff i = C c) :
    clearAux (C a₀ + C a₁ * X) (C b₀ + C b₁ * X) q P ≠ 0 := by
  let φ' : Polynomial R →+* Polynomial F := Polynomial.mapRingHom φ
  let z := -φ a₀ / φ a₁
  let a := C (φ a₀) + C (φ a₁) * X
  let b := C (φ b₀) + C (φ b₁) * X
  have hφ' : Function.Injective φ' := Polynomial.map_injective _ hφ
  have hx : φ a₁ ≠ 0 := fun hz => ha₁ (hφ (hz.trans (map_zero φ).symm))
  have hz : φ a₁ * z = -φ a₀ := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hx
  have hane : a ≠ 0 := by
    intro h
    have hh := congrArg (fun p : Polynomial F => p.coeff 1) h
    exact hx (by simpa [a, Polynomial.coeff_C_mul] using hh)
  have haroot : a.eval z = 0 := by
    change (C (φ a₀) + C (φ a₁)*X).eval z = 0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, hz, add_neg_cancel]
  have hbroot : b.eval z ≠ 0 := by
    intro hzero
    apply hres
    apply hφ
    simp only [map_mul]
    simp only [b, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hzero
    have hbz := congrArg (φ a₁ * ·) hzero
    rw [mul_add, mul_zero] at hbz
    have hm : φ a₁ * (φ b₁*z) = -(φ a₀ * φ b₁) := by
      calc
        _ = (φ a₁*z)*φ b₁ := by ac_rfl
        _ = _ := by rw [hz, neg_mul]
    exact sub_eq_zero.mp (by simpa only [hm, sub_eq_add_neg] using hbz)
  have hfree' (i : ℕ) (hi : 0 < i) : ∃ c : F, (P.map φ').coeff i = C c := by
    obtain ⟨c, hc⟩ := hfree i hi
    exact ⟨φ c, by simp [φ', hc]⟩
  have hn := clearAux_ne_zero_of_seed_free a b z (P.map φ') q hane haroot hbroot
    ((Polynomial.map_ne_zero_iff hφ').mpr hP) (Polynomial.natDegree_map_le.trans hdeg) hfree'
  intro hc
  have hh := congrArg φ' hc
  rw [clearAux_map, map_zero] at hh
  apply hn
  simpa [φ', a, b] using hh

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
