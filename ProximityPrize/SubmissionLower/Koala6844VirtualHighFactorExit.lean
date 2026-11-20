import ProximityPrize.SubmissionLower.Koala6844VirtualHighBandPartner


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

variable {K : Type} [Field K]
local notation "R" => MvPolynomial (Fin 4) K

private theorem product_dvd_of_each (A : Finset R) (Q : R)
    (hprime : ∀ f ∈ A, Prime f)
    (hdist : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → ¬ f ∣ g)
    (hd : ∀ f ∈ A, f ∣ Q) : (∏ f ∈ A, f) ∣ Q := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert f A hnot ih =>
    rw [Finset.prod_insert hnot]
    have hf := hprime f (Finset.mem_insert_self f A)
    have hrel : IsRelPrime f (∏ g ∈ A, g) := by
      apply IsRelPrime.prod_right
      intro g hg
      exact hf.irreducible.isRelPrime_iff_not_dvd.mpr
        (hdist f (Finset.mem_insert_self f A) g (Finset.mem_insert_of_mem hg)
          (fun he => hnot (he ▸ hg)))
    exact hrel.mul_dvd (hd f (Finset.mem_insert_self f A))
      (ih (fun g hg => hprime g (Finset.mem_insert_of_mem hg))
        (fun g hg j hj hne => hdist g (Finset.mem_insert_of_mem hg) j (Finset.mem_insert_of_mem hj) hne)
        (fun g hg => hd g (Finset.mem_insert_of_mem hg)))

theorem product_power_dvd_of_each (A : Finset R) (H : R) (n : ℕ)
    (hprime : ∀ f ∈ A, Prime f)
    (hdist : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → ¬ f ∣ g)
    (hall : ∀ f ∈ A, f^n ∣ H) : (∏ f ∈ A, f)^n ∣ H := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert f A hn ih =>
    rw [Finset.prod_insert hn, mul_pow]
    have hf := hprime f (Finset.mem_insert_self f A)
    have hrel : IsRelPrime f (∏ g ∈ A, g) := by
      apply IsRelPrime.prod_right
      intro g hg
      exact hf.irreducible.isRelPrime_iff_not_dvd.mpr
        (hdist f (Finset.mem_insert_self f A) g (Finset.mem_insert_of_mem hg)
          (fun he => hn (he ▸ hg)))
    exact (hrel.pow_left.pow_right).mul_dvd (hall f (Finset.mem_insert_self f A))
      (ih (fun g hg => hprime g (Finset.mem_insert_of_mem hg))
        (fun g hg j hj hne => hdist g (Finset.mem_insert_of_mem hg) j (Finset.mem_insert_of_mem hj) hne)
        (fun g hg => hall g (Finset.mem_insert_of_mem hg)))

theorem exists_factor_exit {p : ℕ} [CharP K p]
    (hp : p.Prime) {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (w gain D y B : ℕ) (hychar : y < p)
    (q : V →ₗ[K] R) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ globalBox K D w y B B)
    (A : Finset R)
    (hprime : ∀ f ∈ A, Prime f)
    (hdist : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → ¬ f ∣ g)
    (haxis : ∀ f ∈ A, ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ 0 < f.degreeOf i ∧ f.degreeOf i < p)
    (hval : 0 < ((∏ f ∈ A, f).degreeOf 1))
    (hseed : 0 < max ((∏ f ∈ A, f).degreeOf 2) ((∏ f ∈ A, f).degreeOf 3))
    (hgate : gain * bandRectangle y B ((∏ f ∈ A, f).degreeOf 1) ((∏ f ∈ A, f).degreeOf 2)
      ((∏ f ∈ A, f).degreeOf 3) < Module.finrank K V) :
    ∃ f ∈ A, ∃ v : V, ∃ i : Fin 4, ∃ j ≤ y, ∃ k ≤ j,
      (i = 2 ∨ i = 3) ∧ ¬ f ∣ ((MvPolynomial.pderiv i : R → R)^[k]) (q v) ∧
        q v ∈ globalBox K (D-j*gain) w y B B := by
  let P : R := ∏ f ∈ A, f
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun f hf => (hprime f hf).ne_zero)
  obtain ⟨v,j,hj,Q,_,he,havoid,hbox⟩ :=
    exists_rectangle_exit P hP w gain D y B hval hseed q hq hmem hgate
  have hsome : ∃ f ∈ A, ¬ f ∣ Q := by
    by_contra! h
    exact havoid (product_dvd_of_each A Q hprime hdist h)
  obtain ⟨f,hf,hfQ⟩ := hsome
  let Bf := ∏ g ∈ A.erase f, g
  have hPsplit : P = f * Bf :=
    (Finset.mul_prod_erase A (fun g => g) hf).symm
  have hnotBf : ¬ f ∣ Bf := by
    apply (hprime f hf).irreducible.isRelPrime_iff_not_dvd.mp
    apply IsRelPrime.prod_right
    intro g hg
    have hm := Finset.mem_erase.mp hg
    exact (hprime f hf).irreducible.isRelPrime_iff_not_dvd.mpr
      (hdist f hf g hm.2 hm.1.symm)
  have hJ : ¬ f ∣ Bf^j * Q := by
    intro h
    rcases (hprime f hf).dvd_mul.mp h with h | h
    · exact hnotBf ((hprime f hf).dvd_of_dvd_pow h)
    · exact hfQ h
  have he' : q v = f^j * (Bf^j * Q) := by rw [he,hPsplit,mul_pow,mul_assoc]
  obtain ⟨i,his,hpos,hcap⟩ := haxis f hf
  obtain ⟨k,hk,hpartner⟩ :=
    exact_power_has_partner hp f (q v) (Bf^j * Q) (hprime f hf) j (hj.trans_lt hychar) i hpos hcap he' hJ
  exact ⟨f,hf,v,i,j,hj,k,hk,his,hpartner,hbox⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

