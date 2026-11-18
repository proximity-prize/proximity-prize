import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators

noncomputable section

variable {K L : Type*} [Field K] [Field L] {I : Type*}

private theorem nodal_map (c : K →+* L) (D : Finset I) (x : I → K) :
    (Lagrange.nodal D x).map c = Lagrange.nodal D (fun i => c (x i)) := by
  simp only [Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]

private theorem nodal_dvd_of_zero (D : Finset I) (x : I → L) (hx : Set.InjOn x D)
    (P : Polynomial L) (hz : ∀ i ∈ D, P.eval (x i) = 0) : Lagrange.nodal D x ∣ P := by
  rw [Lagrange.nodal]
  refine Finset.prod_dvd_of_coprime (fun i hi j hj hne => ?_) (fun i hi => ?_)
  · have hij : x i ≠ x j := fun h => hne (hx hi hj h)
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hij).isUnit
  · exact Polynomial.dvd_iff_isRoot.mpr (hz i hi)

theorem exists_identity_shortened_tail [DecidableEq I]
    (c : K →+* L) (D : Finset I) (x u₀ u₁ : I → K)
    (hx : Set.InjOn x D) (w : ℕ) (hD : D.card ≤ w) (seed : L)
    (Φ : Polynomial L) (hdegree : Φ.natDegree ≤ w)
    (hident : ∀ i ∈ D, Φ.eval (c (x i)) = c (u₀ i) + seed * c (u₁ i)) :
    let B := (Lagrange.interpolate D x u₀).map c + Polynomial.C seed *
      (Lagrange.interpolate D x u₁).map c
    let H := (Lagrange.nodal D x).map c
    ∃ Q : Polynomial L, Q.natDegree ≤ w - D.card ∧ Φ = B + H * Q ∧
      (∀ i j, (Φ.eval (c (x i)) = j ↔
        H.eval (c (x i)) * Q.eval (c (x i)) = j - B.eval (c (x i)))) := by
  classical
  let P₀ := Lagrange.interpolate D x u₀
  let P₁ := Lagrange.interpolate D x u₁
  let B := P₀.map c + Polynomial.C seed * P₁.map c
  let H := (Lagrange.nodal D x).map c
  have hx' : Set.InjOn (fun i => c (x i)) D := fun _ hi _ hj h => hx hi hj (c.injective h)
  have hBeval (i : I) (hi : i ∈ D) : B.eval (c (x i)) = c (u₀ i) + seed * c (u₁ i) := by
    simp only [B, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map_apply,
      P₀, P₁, Lagrange.eval_interpolate_at_node _ hx hi]
  have hB : B.natDegree ≤ w := by
    apply RCN147.mapped_affine_pencil_natDegree_le c P₀ P₁ w _ _ seed
    · exact (Polynomial.natDegree_le_of_degree_le (Lagrange.degree_interpolate_le u₀ hx)).trans
        ((Nat.sub_le ..).trans hD)
    · exact (Polynomial.natDegree_le_of_degree_le (Lagrange.degree_interpolate_le u₁ hx)).trans
        ((Nat.sub_le ..).trans hD)
  have hdiv : H ∣ Φ - B := by
    change (Lagrange.nodal D x).map c ∣ Φ - B
    rw [nodal_map]
    exact nodal_dvd_of_zero D _ hx' _ fun i hi => by
      simp only [Polynomial.eval_sub, hident i hi, hBeval i hi, sub_self]
  obtain ⟨Q, hQ⟩ := hdiv
  have hfactor : Φ = B + H * Q := by
    have h := sub_eq_iff_eq_add.mp hQ
    simpa only [add_comm] using h
  have hHdeg : H.natDegree = D.card := by
    change ((Lagrange.nodal D x).map c).natDegree = D.card
    rw [nodal_map, Lagrange.natDegree_nodal]
  have hQdegree : Q.natDegree ≤ w - D.card := by
    by_cases hz : Q = 0
    · simp [hz]
    have hH : H ≠ 0 := by
      change (Lagrange.nodal D x).map c ≠ 0
      rw [nodal_map]
      exact Lagrange.nodal_ne_zero
    have hcap := (Polynomial.natDegree_sub_le Φ B).trans (max_le hdegree hB)
    rw [hQ, Polynomial.natDegree_mul hH hz, hHdeg] at hcap
    omega
  refine ⟨Q, hQdegree, hfactor, ?_⟩
  intro i j
  change Φ.eval (c (x i)) = j ↔ H.eval (c (x i)) * Q.eval (c (x i)) = j - B.eval (c (x i))
  nth_rw 1 [hfactor]
  rw [Polynomial.eval_add, Polynomial.eval_mul, eq_sub_iff_add_eq, add_comm]

end

end ProximityPrize.SubmissionLower.Koala6831Moving
