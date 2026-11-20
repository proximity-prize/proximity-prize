import ProximityPrize.SubmissionLower.Koala6844VirtualHighBandExit
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRoom


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

theorem exists_rectangle_exit {K : Type} [Field K]
    (P : MvPolynomial (Fin 4) K) (hp : P ≠ 0) (w gain D y B : ℕ)
    (hy : 0 < P.degreeOf 1) (hz : 0 < max (P.degreeOf 2) (P.degreeOf 3))
    {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ globalBox K D w y B B)
    (hdim : gain * bandRectangle y B (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) <
      Module.finrank K V) :
    ∃ v : V, ∃ j ≤ y, ∃ Q : MvPolynomial (Fin 4) K,
      q v ≠ 0 ∧ q v = P^j * Q ∧ ¬ P ∣ Q ∧
      q v ∈ globalBox K (D-j*gain) w y B B := by
  let n := bandFuel y B (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3)
  have hcut : n = y / P.degreeOf 1 ∨ n = B / max (P.degreeOf 2) (P.degreeOf 3) := by
    unfold n bandFuel
    rcases le_total (y / P.degreeOf 1) (B / max (P.degreeOf 2) (P.degreeOf 3)) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  have hstop : y < (n+1)*P.degreeOf 1 ∨ B < (n+1)*P.degreeOf 2 ∨ B < (n+1)*P.degreeOf 3 := by
    rcases hcut with h | h
    · exact Or.inl ((Nat.div_lt_iff_lt_mul hy).mp (by omega))
    · have hm := (Nat.div_lt_iff_lt_mul hz).mp (show
        B / max (P.degreeOf 2) (P.degreeOf 3) < n + 1 by omega)
      rw [← Nat.mul_max_mul_left] at hm
      exact Or.inr (lt_max_iff.mp hm)
  have hbudget : stripBudget gain y B B (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) n =
      gain * bandRectangle y B (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) := by
    unfold stripBudget bandRectangle
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  obtain ⟨v,j,hj,Q,hnz,he,hnot,hbox⟩ :=
    exists_rectangle_exit_of_budget P hp w gain n D y B B q hq hmem (hbudget ▸ hdim) hstop
  exact ⟨v,j,hj.trans ((min_le_left _ _).trans (Nat.div_le_self _ _)),Q,hnz,he,hnot,hbox⟩

theorem exact_power_has_partner {K : Type} [Field K] {p : ℕ} [CharP K p]
    (hp : p.Prime) (f H J : MvPolynomial (Fin 4) K) (hf : Prime f)
    (j : ℕ) (hj : j < p) (i : Fin 4)
    (hi : 0 < f.degreeOf i) (hic : f.degreeOf i < p)
    (heq : H = f^j * J) (hav : ¬ f ∣ J) :
    ∃ k ≤ j, ¬ f ∣ ((MvPolynomial.pderiv i : _ → _)^[k]) H := by
  have hd : MvPolynomial.pderiv i f ≠ 0 :=
    fun h => (Nat.ne_of_gt hi) ((RCN267.pderiv_zero_iff_degree_zero_below_char i f p hic).mp h)
  have htrans : ¬ f ∣ MvPolynomial.pderiv i f := by
    intro h
    have hcap := RCN313.pderiv_same_degree_bound i f (f.degreeOf i) le_rfl
    have hle := RCN137.coordinate_degree_le_of_dvd i f _ h hd
    omega
  have hpow : ¬ f^(j+1) ∣ H := by
    rintro ⟨Q, hQ⟩
    have he := heq.symm.trans hQ
    rw [pow_succ, mul_assoc] at he
    exact hav ⟨Q,mul_left_cancel₀ (pow_ne_zero _ hf.ne_zero) he⟩
  by_contra! h
  exact hpow (pow_succ_dvd_of_room (MvPolynomial.pderiv i) f H p j hp hj hf htrans h)

variable {K : Type} [Field K]

theorem rectangle_partner_mem {D w y b c : ℕ} (i : Fin 4)
    (hi : i = 2 ∨ i = 3) (k : ℕ) {P : MvPolynomial (Fin 4) K}
    (hp : P ∈ globalBox K D w y b c) :
    ((MvPolynomial.pderiv i : _ → _)^[k]) P ∈ globalBox K D w y b c := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [mem_globalBox] at ih ⊢
    intro e he
    have hh := ih _ (RCN313.support_before_pderiv i _ e he)
    rcases hi with h | h <;> subst i <;> simpa [Finsupp.add_apply, Finsupp.single_apply] using
      (show e 0 + w * e 1 < D ∧ e 1 ≤ y ∧ e 2 ≤ b ∧ e 3 ≤ c by
        simp [Finsupp.add_apply, Finsupp.single_apply] at hh
        omega)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

