import ProximityPrize.SubmissionLower.Koala6831IntrinsicRegular


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic MvPolynomial Function RCN313

variable {K : Type} [Field K]

private theorem iterate_pderiv_preserves_degree (P : Carrier K) (i : Fin 4)
    (d n : ℕ) (h : P.degreeOf i ≤ d) :
    (((pderiv (0 : Fin 4) : Carrier K → Carrier K)^[n]) P).degreeOf i ≤ d := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [iterate_succ_apply']
    exact pderiv_degree_bound _ _ _ _ ih

private theorem iterate_pderiv_drops_degree (P : Carrier K)
    (d n : ℕ) (h : P.degreeOf 0 ≤ d) :
    (((pderiv (0 : Fin 4) : Carrier K → Carrier K)^[n]) P).degreeOf 0 ≤ d-n := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (pderiv_same_degree_bound _ _ _ ih).trans (by omega)

theorem iterate_regularDerivation_of_value_free (F P : Carrier K) (n : ℕ)
    (hP : P.degreeOf 1 ≤ 0) :
    ((regularDerivation F)^[n]) (regularImage F P) =
      regularImage F (((pderiv (0 : Fin 4) : Carrier K → Carrier K)^[n]) P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih, regularDerivation_image]
    rw [pderiv_eq_zero_of_degree_bound_zero _ _ (iterate_pderiv_preserves_degree P 1 0 n hP),
      map_zero, mul_zero, sub_zero, iterate_succ_apply']

theorem iterate_regularDerivation_eq_zero_of_value_free (F P : Carrier K) (d n : ℕ)
    (hP : P.degreeOf 1 ≤ 0) (hX : P.degreeOf 0 ≤ d) (hn : d < n) :
    ((regularDerivation F)^[n]) (regularImage F P) = 0 := by
  rw [iterate_regularDerivation_of_value_free F P n hP]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hd := iterate_pderiv_drops_degree P d j hX
  have hz : d-j = 0 := by omega
  rw [hz] at hd
  rw [iterate_succ_apply', pderiv_eq_zero_of_degree_bound_zero _ _ hd, map_zero]

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
