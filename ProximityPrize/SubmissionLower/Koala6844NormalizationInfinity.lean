import ProximityPrize.SubmissionLower.Koala6844NormalizationCenter


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

theorem centered_degree_le (A : Fin 2 → Polynomial K) (d0 C1 P Q : Polynomial K)
    (g : K) (w : ℕ) (hden : specializeAffine A g ≠ 0)
    (hfull : (specializeAffine A g).natDegree = affineDegree A)
    (hP : P.natDegree ≤ w) (hC : C1.natDegree ≤ w + d0.natDegree)
    (he : specializeAffine A g * Q = d0 * P + C g * C1) :
    Q.natDegree ≤ w + d0.natDegree - affineDegree A := by
  by_cases hQ : Q = 0
  · simp [hQ]
  have hprod := congrArg natDegree he
  rw [natDegree_mul hden hQ, hfull] at hprod
  have hsum : (d0 * P + C g * C1).natDegree ≤ w + d0.natDegree :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le_of_le le_rfl hP).trans (by omega))
      ((natDegree_C_mul_le _ _).trans hC))
  omega

theorem fixed_field_card_le (σ : K →+* K) (p : ℕ) (hp : 1 < p)
    (hσ : ∀ g : K, σ g = g ^ p) (seeds : Finset K)
    (hfix : ∀ g ∈ seeds, σ g = g) :
    seeds.card ≤ p := by
  let f : Polynomial K := X ^ p - X
  have hf : f ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Polynomial K => f.coeff p) hz
    simp [f, coeff_X, ne_of_lt hp] at h
  have he : seeds.card ≤ f.natDegree := by
    apply card_le_degree_of_subset_roots
    intro g hg
    apply (mem_roots hf).mpr
    have eq := (hσ g).symm.trans (hfix g hg)
    simpa only [Polynomial.IsRoot, f, eval_sub, eval_pow, eval_X, sub_eq_zero] using eq
  exact he.trans ((natDegree_sub_le _ _).trans (by
    simp only [natDegree_pow, natDegree_X, one_mul, Nat.mul_one]
    exact max_eq_left hp.le |>.le))

theorem infinity_excess_card_le (σ : K →+* K) (p w : ℕ) (hp : 1 < p)
    (hσ : ∀ g : K, σ g = g ^ p)
    (A : Fin 2 → Polynomial K) (d0 d1 C1 : Polynomial K)
    (hd1 : d1 ≠ 0) (seeds : Finset K) (selected normalized : K → Polynomial K)
    (hA0 : (A 0).coeff (affineDegree A) ≠ 0)
    (hZero : normalized 0 = 0)
    (hfull : ∀ g ∈ seeds, (specializeAffine A g).natDegree = affineDegree A)
    (hdeg : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hHigh : w + d0.natDegree < C1.natDegree)
    (hEq : ∀ g ∈ seeds, specializeAffine A g * normalized g =
      d0 * selected g + C g * C1)
    (hHom : ∀ g ∈ seeds, d1 * (normalized g).map σ = d0.map σ * normalized g) :
    seeds.card ≤ p := by
  classical
  let a0 := (A 0).coeff (affineDegree A)
  let a1 := (A 1).coeff (affineDegree A)
  have hCne : C1 ≠ 0 := by
    intro h
    simp [h] at hHigh
  have hQne (g : K) (hg : g ∈ seeds) (hn : g ≠ 0) : normalized g ≠ 0 := by
    have hd : (d0 * selected g).natDegree < (C g * C1).natDegree := by
      rw [natDegree_mul (C_ne_zero.mpr hn) hCne, natDegree_C, zero_add]
      exact ((natDegree_mul_le_of_le le_rfl (hdeg g hg)).trans (by omega)).trans_lt hHigh
    intro hQ
    have hz := hEq g hg
    rw [hQ, mul_zero] at hz
    have he := congrArg natDegree hz
    rw [natDegree_zero, natDegree_add_eq_right_of_natDegree_lt hd] at he
    rw [natDegree_mul (C_ne_zero.mpr hn) hCne, natDegree_C, zero_add] at he
    omega
  have hLC (g : K) (hg : g ∈ seeds) :
      (a0 + g * a1) * (normalized g).leadingCoeff = g * C1.leadingCoeff := by
    by_cases hzero : g = 0
    · subst g
      simp [hZero]
    have hd : (d0 * selected g).natDegree < (C g * C1).natDegree := by
      rw [natDegree_mul (C_ne_zero.mpr hzero) hCne, natDegree_C, zero_add]
      exact ((natDegree_mul_le_of_le le_rfl (hdeg g hg)).trans (by omega)).trans_lt hHigh
    have h := congrArg leadingCoeff (hEq g hg)
    rw [leadingCoeff_mul, leadingCoeff_add_of_degree_lt (degree_lt_degree hd), leadingCoeff_mul, leadingCoeff_C] at h
    rw [show (specializeAffine A g).leadingCoeff = a0 + g * a1 by
      change (specializeAffine A g).coeff (specializeAffine A g).natDegree = _
      rw [hfull g hg]
      simp only [specializeAffine, coeff_add, coeff_C_mul, a0, a1]] at h
    exact h
  by_cases hsmall : seeds.card ≤ 1
  · exact hsmall.trans hp.le
  obtain ⟨g0, hg0, hgn⟩ : ∃ g0 ∈ seeds, g0 ≠ 0 := by
    by_contra!
    have h := Finset.card_le_one.mpr fun g hg g' hg' => (this g hg).trans (this g' hg').symm
    omega
  let q0 := (normalized g0).leadingCoeff
  have hq0 : q0 ≠ 0 := leadingCoeff_ne_zero.mpr (hQne g0 hg0 hgn)
  let r (g : K) := (normalized g).leadingCoeff / q0
  have inj : Set.InjOn r (↑seeds : Set K) := by
    intro g hg h hh he
    have hEqLc : (normalized g).leadingCoeff = (normalized h).leadingCoeff :=
      (div_left_inj' hq0).mp he
    by_cases hG : g = 0
    · subst g
      have h := hEqLc.symm
      rw [hZero, leadingCoeff_zero, leadingCoeff_eq_zero] at h
      by_contra hne
      exact hQne _ hh (Ne.symm hne) h
    · have hQ := leadingCoeff_ne_zero.mpr (hQne g hg hG)
      have hL := hLC g hg
      have hR := hLC h hh
      rw [← hEqLc] at hR
      apply mul_right_cancel₀ (mul_ne_zero hA0 hQ)
      linear_combination g * hR - h * hL
  have hc := fixed_field_card_le σ p hp hσ (seeds.image r) fun g hg => by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    exact leadingCoeff_ratio_fixed σ hd1 (hQne g0 hg0 hgn) (hHom h hh) (hHom g0 hg0)
  rw [Finset.card_image_of_injOn inj] at hc
  exact hc

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
