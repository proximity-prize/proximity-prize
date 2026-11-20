import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Derivation.Basic



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

section Derivation

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

theorem derivation_drops_power (D : Derivation K R R) (I : Ideal R) (n : ℕ) {x : R}
    (hx : x ∈ I ^ (n + 1)) : D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      apply Ideal.add_mem _
      · exact Ideal.mul_mem_right _ _ ha
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hb (ih ha)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

theorem derivation_preserves_power (D : Derivation K R R) (I : Ideal R)
    (stable : ∀ x ∈ I, D x ∈ I) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      apply Ideal.add_mem _
      · exact Ideal.mul_mem_mul ha (stable b hb)
      · rw [mul_comm b (D a)]
        exact Ideal.mul_mem_mul (ih ha) hb
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

theorem derivation_preserves_contact_ideal (D : Derivation K R R) (d q : R)
    (hd : D d ∈ Ideal.span ({d,q} : Set R))
    (hq : D q ∈ Ideal.span ({d,q} : Set R)) :
    ∀ x ∈ Ideal.span ({d,q} : Set R), D x ∈ Ideal.span ({d,q} : Set R) := by
  intro x hx
  obtain ⟨a,b,h⟩ := Ideal.mem_span_pair.mp hx
  rw [← h, map_add, D.leibniz, D.leibniz, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hd) ?_)
    (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) ?_)
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem iterate_derivation_drops_power (D : Derivation K R R) (I : Ideal R) (n r : ℕ)
    (hr : r ≤ n) {x : R} (hx : x ∈ I ^ n) :
    ((D : R → R)^[r]) x ∈ I ^ (n-r) := by
  induction r with
  | zero => simpa
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hrec := ih (by omega)
    have hn : n - r = (n - (r + 1)) + 1 := by omega
    rw [hn] at hrec
    exact derivation_drops_power D I _ hrec

theorem iterate_derivation_preserves_power (D : Derivation K R R) (I : Ideal R)
    (stable : ∀ x ∈ I, D x ∈ I) (n r : ℕ) {x : R} (hx : x ∈ I ^ n) :
    ((D : R → R)^[r]) x ∈ I ^ n := by
  induction r with
  | zero => simpa
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact derivation_preserves_power D I stable n ih

end Derivation

section Specialization

variable {R S : Type*} [CommRing R] [CommRing S]

theorem virtual_power_dvd_specialization (φ : R →+* S) {F d q : R} {e : S}
    (M : ℕ) (hcontact : F ∈ Ideal.span ({d,q} : Set R) ^ M)
    (hd : e ∣ φ d) (hq : e ∣ φ q) : e ^ M ∣ φ F := by
  have hbase : (Ideal.span ({d,q} : Set R)).map φ ≤ Ideal.span ({e} : Set S) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr hd
    · exact Ideal.mem_span_singleton.mpr hq
  have image : φ F ∈ (Ideal.span ({d,q} : Set R) ^ M).map φ :=
    Ideal.mem_map_of_mem _ hcontact
  rw [Ideal.map_pow] at image
  have hmem : φ F ∈ Ideal.span ({e} : Set S) ^ M :=
    Ideal.pow_right_mono hbase M image
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem

end Specialization

section ContactVanishing

open Polynomial
variable {K : Type*} [Field K] {I : Type*}

private theorem degree_ordinary_product (nodes : Finset I) (x : I → K) (m : ℕ) :
    (∏ i ∈ nodes, (X - C (x i)) ^ m).natDegree = nodes.card * m := by
  rw [Polynomial.natDegree_prod_of_monic nodes _ (fun i _ => (Polynomial.monic_X_sub_C (x i)).pow m)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one,
    Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

theorem eq_zero_of_mixed_contact_divisibility (nodes : Finset I) (x : I → K)
    (hx : Set.InjOn x (nodes : Set I))
    (F d0 d1 : Polynomial K) (m M0 M1 : ℕ)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hcop : IsCoprime d0 d1)
    (off0 : ∀ i ∈ nodes, d0.eval (x i) ≠ 0)
    (off1 : ∀ i ∈ nodes, d1.eval (x i) ≠ 0)
    (ordinary : ∀ i ∈ nodes, (X - C (x i)) ^ m ∣ F)
    (virtual0 : d0 ^ M0 ∣ F) (virtual1 : d1 ^ M1 ∣ F)
    (degree_lt : F.natDegree < nodes.card * m + M0 * d0.natDegree + M1 * d1.natDegree) :
    F = 0 := by
  classical
  let H := ∏ i ∈ nodes, (X - C (x i)) ^ m
  have hH : H ∣ F := by
    apply Finset.prod_dvd_of_coprime _ ordinary
    intro i hi j hj hij
    have hne : x i ≠ x j := fun e => hij (hx hi hj e)
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit).pow
  have off_coprime {d : Polynomial K} (off : ∀ i ∈ nodes, d.eval (x i) ≠ 0)
      (M : ℕ) : IsCoprime H (d ^ M) := by
    refine IsCoprime.prod_left fun i hi => ?_
    apply IsCoprime.pow
    apply (Polynomial.irreducible_X_sub_C (x i)).coprime_iff_not_dvd.mpr
    simpa only [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using off i hi
  have hprod : H * (d0 ^ M0 * d1 ^ M1) ∣ F :=
    ((off_coprime off0 M0).mul_right (off_coprime off1 M1)).mul_dvd hH
      ((hcop.pow (m := M0) (n := M1)).mul_dvd virtual0 virtual1)
  by_contra hne
  have hMonic : H.Monic := Polynomial.monic_prod_of_monic nodes _ fun i _ =>
    (Polynomial.monic_X_sub_C (x i)).pow m
  have hdeg := Polynomial.natDegree_le_of_dvd hprod hne
  rw [Polynomial.natDegree_mul hMonic.ne_zero (mul_ne_zero (pow_ne_zero _ hd0) (pow_ne_zero _ hd1)),
    Polynomial.natDegree_mul (pow_ne_zero _ hd0) (pow_ne_zero _ hd1),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    degree_ordinary_product nodes x m] at hdeg
  omega

end ContactVanishing

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
