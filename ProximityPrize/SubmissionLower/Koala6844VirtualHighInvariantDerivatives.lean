import ProximityPrize.SubmissionLower.Koala6844VirtualHighRawTail


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Function Finset RCN347

section Reconstruction

variable {K R A L : Type*} [CommRing K]
  [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] [Field L]

theorem eval_iterate_mul_zero_of_bounds (δ : Derivation K A A) (ev : A →+* L)
    (a b : A) (aDeg bDeg n : ℕ)
    (ha : ∀ i > aDeg, ev ((δ^[i]) a) = 0)
    (hb : ∀ j > bDeg, ev ((δ^[j]) b) = 0)
    (hn : aDeg+bDeg < n) :
    ev ((δ^[n]) (a*b)) = 0 := by
  rw [iterate_product, map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [map_nsmul, map_mul]
  have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : aDeg < ij.1
  · rw [ha _ hi, zero_mul, nsmul_zero]
  · rw [hb _ (by omega), mul_zero, nsmul_zero]

private theorem iterate_mul_fixed (δ : Derivation K A A) (c z : A) (fixed : δ c = 0) (n : ℕ) :
    (δ^[n]) (c*z) = c * (δ^[n]) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply' δ n z, ih, leibniz_product,
      fixed, zero_mul, zero_add]

theorem eval_persistent_trimmed_to_value (D : Derivation K R R) (δ : Derivation K A A)
    (φ : R →+* A) (ev : A →+* L) (H V W : R) (S theta valueCoordinate : A)
    (commute : ∀ r, φ (D r) = φ H * δ (φ r))
    (hVunit : IsUnit (φ V))
    (hV : ev (φ V) ≠ 0) (hH : ev (φ H) ≠ 0) (hS : ev S ≠ 0)
    (hSfixed : δ S = 0) (hW : φ W = S*valueCoordinate-theta)
    (trimDeg divisorDeg θDeg n : ℕ)
    (later : ∀ j ≥ trimDeg, ev (φ (trimmedNumerator D H V W j)) = 0)
    (divisor : ∀ j > divisorDeg, ev ((δ^[j]) (φ V)) = 0)
    (remainder : ∀ j > θDeg, ev ((δ^[j]) theta) = 0)
    (hdegree : trimDeg+divisorDeg < n) (hθdegree : θDeg < n) :
    ev ((δ^[n]) valueCoordinate) = 0 := by
  obtain ⟨u, hu⟩ := hVunit
  let q : A := (↑u⁻¹ : A) * φ W
  have hq : φ V * q = φ W := by
    rw [← hu]
    simp [q, ← mul_assoc]
  have hclear (j : ℕ) : φ (trimmedNumerator D H V W j) =
      φ V^(j+2) * φ H^(2*j+1) * (δ^[j+1]) q := by
    simpa only [one_mul] using map_trimmedNumerator D δ H V W φ commute
      1 q δ.map_one_eq_zero (by rw [one_mul, hq]) j
  have qtail (j : ℕ) (hj : trimDeg < j) : ev ((δ^[j]) q) = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have h := later k (by omega)
    rw [hclear, map_mul, map_mul, map_pow, map_pow] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero _ hV) (pow_ne_zero _ hH))
  have hreconstructed : S * valueCoordinate = φ V * q + theta := by rw [hq, hW, sub_add_cancel]
  have hprod := eval_iterate_mul_zero_of_bounds δ ev (φ V) q divisorDeg trimDeg n
    divisor qtail (by omega)
  have hypoth := congrArg (fun a : A => ev ((δ^[n]) a)) hreconstructed
  rw [iterate_mul_fixed δ S valueCoordinate hSfixed n, map_mul, RCN347.iterate_add, map_add, hprod,
    remainder _ hθdegree, add_zero] at hypoth
  exact (mul_eq_zero.mp hypoth).resolve_left hS

end Reconstruction

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
