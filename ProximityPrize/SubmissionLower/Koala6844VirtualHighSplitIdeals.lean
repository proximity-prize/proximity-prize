import ProximityPrize.SubmissionLower.Koala6844VirtualHighRootContacts
import ProximityPrize.SubmissionLower.Koala6844VirtualHighWitness


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped BigOperators Classical Pointwise

noncomputable section

set_option autoImplicit false

section PairIdeals

variable {R : Type*} [CommRing R]

def pairIdeal (a q : R) : Ideal R :=
  Ideal.span ({a,q} : Set R)

theorem pairIdeal_le {a b q : R} (h : b ∣ a) : pairIdeal a q ≤ pairIdeal b q := by
  apply Ideal.span_le.mpr
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · obtain ⟨u, rfl⟩ := h
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)

theorem pairIdeal_pow_le {a b q : R} (h : b ∣ a) (m : ℕ) :
    pairIdeal a q ^ m ≤ pairIdeal b q ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ]
    exact Ideal.mul_mono ih (pairIdeal_le h)

theorem pairIdeal_one (q : R) : pairIdeal 1 q = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span (by simp))

theorem pairIdeal_product_le (a b q : R) :
    pairIdeal a q * pairIdeal b q ≤ pairIdeal (a*b) q := by
  rw [pairIdeal, pairIdeal, Ideal.span_mul_span]
  apply Ideal.span_le.mpr
  intro t ht
  obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_mul.mp ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  have hprod : a*b ∈ pairIdeal (a*b) q := Ideal.subset_span (by simp)
  have hq : q ∈ pairIdeal (a*b) q := Ideal.subset_span (by simp)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hprod
  · exact Ideal.mul_mem_left _ _ hq
  · exact Ideal.mul_mem_right _ _ hq
  · exact Ideal.mul_mem_right _ _ hq

theorem pairIdeal_pow_product_le (a b q : R) (m : ℕ) :
    (pairIdeal a q * pairIdeal b q)^m ≤ (pairIdeal (a*b) q)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact Ideal.mul_mono ih (pairIdeal_product_le a b q)

theorem pairIdeal_sup_eq_top {a b q : R} (h : IsCoprime a b) :
    pairIdeal a q ⊔ pairIdeal b q = ⊤ := by
  obtain ⟨s,t,hst⟩ := h
  apply (Ideal.eq_top_iff_one _).mpr
  have ha : a ∈ pairIdeal a q := Ideal.subset_span (by simp)
  have hb : b ∈ pairIdeal b q := Ideal.subset_span (by simp)
  rw [← hst]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ ((le_sup_left : pairIdeal a q ≤ _) ha))
    (Ideal.mul_mem_left _ _ ((le_sup_right : pairIdeal b q ≤ _) hb))

theorem mem_pairIdeal_pow_mul {a b q F : R} (m : ℕ) (h : IsCoprime a b)
    (ha : F ∈ pairIdeal a q ^ m) (hb : F ∈ pairIdeal b q ^ m) :
    F ∈ pairIdeal (a*b) q ^ m := by
  have hs := pairIdeal_sup_eq_top (q := q) h
  have hs' : pairIdeal a q ^ m ⊔ pairIdeal b q ^ m = ⊤ :=
    Ideal.pow_sup_pow_eq_top hs
  have hc := Ideal.isCoprime_iff_sup_eq.mpr hs'
  have hm : F ∈ pairIdeal a q ^ m ⊓ pairIdeal b q ^ m := ⟨ha,hb⟩
  have hm' : F ∈ pairIdeal a q ^ m * pairIdeal b q ^ m := by
    rw [Ideal.mul_eq_inf_of_isCoprime hc]
    exact hm
  have hm'' : F ∈ (pairIdeal a q * pairIdeal b q)^m := by
    rw [mul_pow]
    exact hm'
  exact pairIdeal_pow_product_le a b q m hm''

theorem mem_pairIdeal_pow_prod {J : Type*} (s : Finset J) (a : J → R)
    (q F : R) (m : ℕ)
    (cop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (a i) (a j))
    (contacts : ∀ i ∈ s, F ∈ pairIdeal (a i) q ^ m) :
    F ∈ pairIdeal (∏ i ∈ s, a i) q ^ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairIdeal_one, Ideal.top_pow]
  | insert i t hit ih =>
    rw [Finset.prod_insert hit]
    have copProduct : IsCoprime (a i) (∏ j ∈ t, a j) := by
      rw [IsCoprime.prod_right_iff]
      intro j hj
      exact cop i (Finset.mem_insert_self ..) j (Finset.mem_insert_of_mem hj)
        (fun h => hit (h.symm ▸ hj))
    refine mem_pairIdeal_pow_mul m copProduct (contacts i (Finset.mem_insert_self ..)) ?_
    exact ih (fun j hj k hk => cop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj => contacts j (Finset.mem_insert_of_mem hj))

end PairIdeals

variable {K : Type*} [Field K]

theorem mem_divisorIdeal_pow_of_split_local (d : Polynomial K) (q F : GermCarrier K)
    (hsplit : d.Splits) (hd : d ≠ 0) (M : ℕ)
    (hLocal : ∀ a ∈ d.roots.toFinset,
      F ∈ pairIdeal (((Polynomial.X : GermCarrier K) - Polynomial.C (MvPolynomial.C a)) ^
        d.rootMultiplicity a) q ^ M) :
    F ∈ divisorIdeal d q ^ M := by
  classical
  let N (a : K) : GermCarrier K :=
    ((Polynomial.X : GermCarrier K) - Polynomial.C (MvPolynomial.C a)) ^ d.rootMultiplicity a
  have hc (i : K) (_hi : i ∈ d.roots.toFinset) (j : K) (_hj : j ∈ d.roots.toFinset)
      (hne : i ≠ j) : IsCoprime (N i) (N j) := by
    have h := (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit).pow
      (m := d.rootMultiplicity i) (n := d.rootMultiplicity j)
    simpa [N, liftPolynomial, map_pow, map_sub, Polynomial.map_X, Polynomial.map_C]
      using h.map (liftPolynomial : Polynomial K →+* GermCarrier K)
  have hm := mem_pairIdeal_pow_prod d.roots.toFinset N q F M hc hLocal
  have hd0 : IsUnit (liftPolynomial (Polynomial.C d.leadingCoeff)) :=
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hd))).map _
  have he : liftPolynomial d =
      liftPolynomial (Polynomial.C d.leadingCoeff) * ∏ a ∈ d.roots.toFinset, N a := by
    have dh := congrArg (liftPolynomial : Polynomial K →+* GermCarrier K) hsplit.eq_prod_roots
    rw [Polynomial.prod_multiset_root_eq_finset_root, map_mul, map_prod] at dh
    rw [dh]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [N, liftPolynomial, map_sub, map_pow]
  have hdiv : liftPolynomial d ∣ (∏ a ∈ d.roots.toFinset, N a) := by
    rw [he]
    obtain ⟨v,hv⟩ := hd0.exists_right_inv
    refine ⟨v, ?_⟩
    rw [mul_right_comm, hv, one_mul]
  change F ∈ pairIdeal (liftPolynomial d) q ^ M
  exact pairIdeal_pow_le hdiv M hm

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
