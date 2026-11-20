import ProximityPrize.SubmissionLower.Koala6844VirtualHighFactorExit


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

variable {K : Type} [Field K]
local notation "R" => MvPolynomial (Fin 4) K

def factorRectangle (A : Finset R) : Rectangle :=
  let P := ∏ f ∈ A, f
  ⟨P.degreeOf 1,P.degreeOf 2,P.degreeOf 3⟩

private theorem degree_pos_of_mem {A : Finset R} {f : R} (hf : f ∈ A) (i : Fin 4)
    (hA : ∀ g ∈ A, g ≠ 0) :
    f.degreeOf i ≤ (∏ g ∈ A, g).degreeOf i := by
  exact RCN137.coordinate_degree_le_of_dvd _ _ _ (Finset.dvd_prod_of_mem (fun g => g) hf)
    (Finset.prod_ne_zero_iff.mpr hA)

theorem room_factor_partition {p room D w y B : ℕ} [CharP K p]
    (hp : p.Prime) (hroom : room < p) (H : R) (hH : H ≠ 0)
    (hbox : H ∈ globalBox K D w y B B)
    (A : Finset R) (hprime : ∀ f ∈ A, Prime f)
    (hdist : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → ¬ f ∣ g)
    (haxis : ∀ f ∈ A, ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ 0 < f.degreeOf i ∧ f.degreeOf i < p) :
    ∃ U ⊆ A,
      ((room+1) * (factorRectangle U).value ≤ y ∧
        (room+1) * (factorRectangle U).first ≤ B ∧
        (room+1) * (factorRectangle U).second ≤ B) ∧
      ∀ f ∈ A \ U, ∃ i : Fin 4, ∃ k ≤ room, (i = 2 ∨ i = 3) ∧
        ¬ f ∣ ((MvPolynomial.pderiv i : R → R)^[k]) H := by
  classical
  let covers (f : R) := ∃ i : Fin 4, ∃ k ≤ room, (i = 2 ∨ i = 3) ∧
    ¬ f ∣ ((MvPolynomial.pderiv i : R → R)^[k]) H
  let U := A.filter fun f => ¬ covers f
  have hsub : U ⊆ A := Finset.filter_subset _ _
  refine ⟨U,hsub,?_,?_⟩
  · have hall (f : R) (hf : f ∈ U) : f^(room+1) ∣ H := by
      have hn := (Finset.mem_filter.mp hf).2
      obtain ⟨i,hi,hpos,hcap⟩ := haxis f (hsub hf)
      have hd : MvPolynomial.pderiv i f ≠ 0 :=
        fun h => (Nat.ne_of_gt hpos)
          ((RCN267.pderiv_zero_iff_degree_zero_below_char i f p hcap).mp h)
      have htrans : ¬ f ∣ MvPolynomial.pderiv i f := by
        intro h
        have hl := RCN137.coordinate_degree_le_of_dvd i _ _ h hd
        have hb := RCN313.pderiv_same_degree_bound i f (f.degreeOf i) le_rfl
        omega
      apply pow_succ_dvd_of_room (MvPolynomial.pderiv i) f H p room hp hroom
        (hprime f (hsub hf)) htrans
      intro k hk
      by_contra h
      exact hn ⟨i,k,hk,hi,h⟩
    have hdvd := product_power_dvd_of_each U H (room+1)
      (fun f hf => hprime f (hsub hf)) (fun f hf g hg => hdist f (hsub hf) g (hsub hg)) hall
    have hUnz : (∏ f ∈ U, f) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun f hf => (hprime f (hsub hf)).ne_zero)
    obtain ⟨_,hy,hb,hc⟩ := wall_of_mem_globalBox hH hbox
    have hd (i : Fin 4) := RCN137.coordinate_degree_le_of_dvd i _ H hdvd hH
    simp only [MvPolynomial.degreeOf_pow_eq _ _ _ hUnz] at hd
    exact ⟨(hd 1).trans hy,(hd 2).trans hb,(hd 3).trans hc⟩
  · intro f hf
    by_contra hz
    exact (Finset.mem_sdiff.mp hf).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hf).1,hz⟩)

theorem adaptive_factor_partition {p : ℕ} [CharP K p] (hp : p.Prime)
    {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (w gain D y B : ℕ) (hychar : y < p)
    (q : V →ₗ[K] R) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ globalBox K D w y B B)
    (A : Finset R) (hprime : ∀ f ∈ A, Prime f)
    (hdist : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → ¬ f ∣ g)
    (haxis : ∀ f ∈ A, ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ 0 < f.degreeOf i ∧ f.degreeOf i < p)
    (hvalue : ∀ f ∈ A, 1 ≤ f.degreeOf 1) :
    ∃ U ⊆ A,
      (U = ∅ ∨ Module.finrank K V ≤ gain *
        bandRectangle y B (factorRectangle U).value (factorRectangle U).first (factorRectangle U).second) ∧
      ∀ f ∈ A \ U, ∃ v : V, ∃ i : Fin 4, ∃ j ≤ y, ∃ k ≤ j,
        (i = 2 ∨ i = 3) ∧ ¬ f ∣ ((MvPolynomial.pderiv i : R → R)^[k]) (q v) ∧
          q v ∈ globalBox K (D-j*gain) w y B B := by
  classical
  let covers (f : R) := ∃ v : V, ∃ i : Fin 4, ∃ j ≤ y, ∃ k ≤ j,
    (i = 2 ∨ i = 3) ∧ ¬ f ∣ ((MvPolynomial.pderiv i : R → R)^[k]) (q v) ∧
      q v ∈ globalBox K (D-j*gain) w y B B
  let U := A.filter fun f => ¬ covers f
  have hs : U ⊆ A := Finset.filter_subset _ _
  refine ⟨U,hs,?_,?_⟩
  · by_cases hU : U = ∅
    · exact Or.inl hU
    right
    by_contra! hgate
    have hprimeU (f : R) (hf : f ∈ U) := hprime f (hs hf)
    obtain ⟨f,hf⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    have hh (i : Fin 4) := degree_pos_of_mem hf i (fun g hg => (hprimeU g hg).ne_zero)
    have hypos : 0 < ((∏ g ∈ U, g).degreeOf 1) := lt_of_lt_of_le (by omega : 0 < 1)
      ((hvalue f (hs hf)).trans (hh 1))
    have hzpos : 0 < max ((∏ g ∈ U, g).degreeOf 2) ((∏ g ∈ U, g).degreeOf 3) := by
      obtain ⟨i,hi,hpos,_⟩ := haxis f (hs hf)
      rcases hi with h | h
      · subst i; exact hpos.trans_le ((hh 2).trans (le_max_left _ _))
      · subst i; exact hpos.trans_le ((hh 3).trans (le_max_right _ _))
    obtain ⟨g,hg,v,i,j,hj,k,hk,hi,hdiv,hbox⟩ :=
      exists_factor_exit hp w gain D y B hychar q hq hmem U hprimeU
        (fun f hf g hg => hdist f (hs hf) g (hs hg)) (fun f hf => haxis f (hs hf))
        hypos hzpos hgate
    exact (Finset.mem_filter.mp hg).2 ⟨v,i,j,hj,k,hk,hi,hdiv,hbox⟩
  · intro f hf
    by_contra hz
    exact (Finset.mem_sdiff.mp hf).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hf).1,hz⟩)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

