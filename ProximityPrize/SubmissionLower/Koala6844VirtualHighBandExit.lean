import ProximityPrize.SubmissionLower.Koala6844VirtualHighBandMap
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBandQuotient
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

noncomputable section
set_option autoImplicit false

open RCN180
open scoped Classical BigOperators

def stripBudget (gain y b c dy db dc n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, gain * (y + 1 - (j + 1) * dy) *
    (b + 1 - (j + 1) * db) * (c + 1 - (j + 1) * dc)

private theorem stripBudget_succ {gain y b c dy db dc n : ℕ}
    (hy : dy ≤ y) (hb : db ≤ b) (hc : dc ≤ c) :
    stripBudget gain y b c dy db dc (n+1) =
      gain * (y-dy+1) * (b-db+1) * (c-dc+1) +
      stripBudget gain (y-dy) (b-db) (c-dc) dy db dc n := by
  unfold stripBudget
  rw [Finset.sum_range_succ']
  rw [Nat.add_comm]
  congr 1
  · simp only [Nat.zero_add, Nat.one_mul]
    rw [show y + 1 - dy = y - dy + 1 by omega,
      show b + 1 - db = b - db + 1 by omega,
      show c + 1 - dc = c - dc + 1 by omega]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.add_mul, Nat.one_mul]
    rw [show y + 1 - (i * dy + dy + dy) = y - dy + 1 - (i * dy + dy) by omega,
      show b + 1 - (i * db + db + db) = b - db + 1 - (i * db + db) by omega,
      show c + 1 - (i * dc + dc + dc) = c - dc + 1 - (i * dc + dc) by omega]

private theorem fits_of_nonzero_mul {K : Type} [Field K]
    {P Q : MvPolynomial (Fin 4) K} (hp : P ≠ 0) (hq : Q ≠ 0)
    {D w y b c : ℕ} (h : P * Q ∈ globalBox K D w y b c) :
    P.degreeOf 1 ≤ y ∧ P.degreeOf 2 ≤ b ∧ P.degreeOf 3 ≤ c := by
  obtain ⟨_,hy,hb,hc⟩ := wall_of_mem_globalBox (mul_ne_zero hp hq) h
  rw [MvPolynomial.degreeOf_mul_eq hp hq] at hy hb hc
  exact ⟨by omega, by omega, by omega⟩

theorem exists_rectangle_exit_of_budget {K : Type} [Field K]
    (P : MvPolynomial (Fin 4) K) (hp : P ≠ 0)
    (w gain n : ℕ) {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (D y b c : ℕ) (q : V →ₗ[K] MvPolynomial (Fin 4) K)
    (hq : Function.Injective q) (hmem : ∀ v, q v ∈ globalBox K D w y b c)
    (hdim : stripBudget gain y b c (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) n <
      Module.finrank K V)
    (hterminal : y < (n+1) * P.degreeOf 1 ∨ b < (n+1) * P.degreeOf 2 ∨
      c < (n+1) * P.degreeOf 3) :
    ∃ v : V, ∃ j ≤ n, ∃ Q : MvPolynomial (Fin 4) K,
      q v ≠ 0 ∧ q v = P^j * Q ∧ ¬ P ∣ Q ∧
      q v ∈ globalBox K (D-j*gain) w y b c := by
  classical
  induction n generalizing V D y b c with
  | zero =>
    have hnd : 0 < Module.finrank K V := by simpa [stripBudget] using hdim
    letI : Nontrivial V := Module.finrank_pos_iff.mp hnd
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hnz : q v ≠ 0 := fun hz => hv (hq (hz.trans (map_zero q).symm))
    have hav : ¬ P ∣ q v := by
      intro hdiv
      obtain ⟨Q, he⟩ := hdiv
      have hQ : Q ≠ 0 := (mul_ne_zero_iff.mp (he ▸ hnz)).2
      have hf := fits_of_nonzero_mul hp hQ (he ▸ hmem v)
      simp only [Nat.zero_add, Nat.one_mul] at hterminal
      omega
    exact ⟨v,0,le_rfl,q v,hnz,by simp,hav,by simpa using hmem v⟩
  | succ n ih =>
    by_cases hdiv : ∀ v, P ∣ q v
    · let quot := quotientLinear q P hp hdiv
      have heq (v : V) : q v = P * quot v := recon_eq_mul_quotientPolynomial q P hdiv v
      have hquot : Function.Injective quot := quotientLinear_injective q hq P hp hdiv
      have hnd : 0 < Module.finrank K V := Nat.zero_le _ |>.trans_lt hdim
      letI : Nontrivial V := Module.finrank_pos_iff.mp hnd
      obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
      have hq₀ : quot v₀ ≠ 0 := fun hz => hv₀ (hquot (hz.trans (map_zero quot).symm))
      obtain ⟨hy,hb,hc⟩ := fits_of_nonzero_mul hp hq₀ (heq v₀ ▸ hmem v₀)
      let Dq := D - P.weightedTotalDegree (rectangleWeights w)
      let yq := y - P.degreeOf 1
      let bq := b - P.degreeOf 2
      let cq := c - P.degreeOf 3
      have hqmem (v : V) : quot v ∈ globalBox K Dq w yq bq cq :=
        quotient_globalBox hp (heq v ▸ hmem v)
      let f := (bandMap K (Dq-gain) w gain yq bq cq).comp quot
      let low := LinearMap.ker f
      let qlow := quot.comp low.subtype
      have hqlow : Function.Injective qlow := hquot.comp Subtype.val_injective
      have hlow (v : low) : qlow v ∈ globalBox K (Dq-gain) w yq bq cq :=
        mem_low_of_bandMap_zero (by omega) (hqmem v.val) (LinearMap.mem_ker.mp v.property)
      have hlowDim := finrank_bandMap_ker_lower (Dq-gain) w gain yq bq cq quot
      rw [stripBudget_succ hy hb hc] at hdim
      have hband : stripBudget gain yq bq cq (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) n <
          Module.finrank K low := by
        change Module.finrank K V ≤ gain * (yq + 1) * (bq + 1) * (cq + 1) +
          Module.finrank K low at hlowDim
        change gain * (yq + 1) * (bq + 1) * (cq + 1) +
          stripBudget gain yq bq cq (P.degreeOf 1) (P.degreeOf 2) (P.degreeOf 3) n < _ at hdim
        omega
      have hstop : yq < (n+1) * P.degreeOf 1 ∨ bq < (n+1) * P.degreeOf 2 ∨
          cq < (n+1) * P.degreeOf 3 := by
        dsimp only [yq,bq,cq]
        simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hterminal ⊢
        omega
      obtain ⟨v,j,hj,Q,hnz,hQ,hnot,hbox⟩ :=
        ih (Dq-gain) yq bq cq qlow hqlow hlow hband hstop
      have hV : q v.val ≠ 0 := by
        rw [heq]
        exact mul_ne_zero hp hnz
      refine ⟨v.val,j+1,by omega,Q,hV,?_,hnot,?_⟩
      · rw [heq, pow_succ', mul_assoc, ← hQ]
        rfl
      · rw [heq]
        apply nonzero_globalBox_of_product hp hnz _ hy hb hc
        have hcut : Dq - gain - j * gain = D - (j+1)*gain -
            P.weightedTotalDegree (rectangleWeights w) := by
          dsimp only [Dq]
          rw [Nat.add_mul, Nat.one_mul]
          omega
        simpa only [hcut] using hbox
    · push_neg at hdiv
      obtain ⟨v, hv⟩ := hdiv
      exact ⟨v,0,Nat.zero_le _,q v,fun hz => hv (hz ▸ dvd_zero _),by simp,hv,
        by simpa using hmem v⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

