import ProximityPrize.SubmissionLower.Koala6831Comparison

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private def boxExponent {b c : ℕ} (j : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.1.val + Finsupp.single 1 j.2.val

private theorem boxExponent_eq {b c : ℕ} (e : Fin 2 →₀ ℕ) (h₀ : e 0 < b) (h₁ : e 1 < c) :
    boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩) = e := by
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  ext i
  fin_cases i
  · simp [boxExponent, hZero]
  · simp [boxExponent, hOne]

def restrictMultiplierCoefficients (h b c : ℕ) :
    Polynomial (SeedRing K) →ₗ[K] (CoefficientIndex h b c → K) where
  toFun P j := (P.coeff j.1.val).coeff (boxExponent j.2)
  map_add' P Q := by
    funext j
    simp
  map_smul' z P := by
    funext j
    simp [Polynomial.coeff_smul]

def InMultiplierBox (h b c : ℕ) (P : Polynomial (SeedRing K)) : Prop :=
  (∀ n, h ≤ n → P.coeff n = 0) ∧
    (∀ n, (P.coeff n).degreeOf 0 < b ∧ (P.coeff n).degreeOf 1 < c)

theorem multiplierCoefficients_identify {h b c : ℕ} {P Q : Polynomial (SeedRing K)}
    (hP : InMultiplierBox h b c P) (hQ : InMultiplierBox h b c Q)
    (hEq : restrictMultiplierCoefficients h b c P = restrictMultiplierCoefficients h b c Q) :
    P = Q := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < h
  · apply MvPolynomial.ext
    intro e
    by_cases h₀ : e 0 < b
    · by_cases h₁ : e 1 < c
      · have he := congrFun hEq (⟨n, hn⟩, (⟨e 0, h₀⟩, ⟨e 1, h₁⟩))
        change (P.coeff n).coeff (boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩)) =
          (Q.coeff n).coeff (boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩)) at he
        have hbox : boxExponent (b := b) (c := c) (⟨e 0, h₀⟩, ⟨e 1, h₁⟩) = e :=
          boxExponent_eq e h₀ h₁
        simpa only [hbox] using he
      · have hzero (R : Polynomial (SeedRing K)) (hR : InMultiplierBox h b c R) :
            (R.coeff n).coeff e = 0 := by
          by_contra hne
          have hm := MvPolynomial.mem_support_iff.mpr hne
          exact h₁ ((MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 2) hm).trans_lt (hR.2 n).2)
        rw [hzero P hP, hzero Q hQ]
    · have hzero (R : Polynomial (SeedRing K)) (hR : InMultiplierBox h b c R) :
          (R.coeff n).coeff e = 0 := by
        by_contra hne
        have hm := MvPolynomial.mem_support_iff.mpr hne
        exact h₀ ((MvPolynomial.le_degreeOf_of_mem_support (0 : Fin 2) hm).trans_lt (hR.2 n).1)
      rw [hzero P hP, hzero Q hQ]
  · rw [hP.1 n (Nat.le_of_not_gt hn), hQ.1 n (Nat.le_of_not_gt hn)]

theorem finrank_le_of_multiplierBox {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K)) (hL : Function.Injective L)
    (h b c : ℕ) (hbox : ∀ v, InMultiplierBox h b c (L v)) :
    Module.finrank K V ≤ h * b * c := by
  let f := (restrictMultiplierCoefficients h b c).comp L
  have hinj : Function.Injective f := by
    intro u v huv
    apply hL
    exact multiplierCoefficients_identify (hbox u) (hbox v) huv
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at hd
  simpa only [CoefficientIndex, SeedIndex, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using hd

def divideMultiplierLinear {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K))
    (q : Polynomial (SeedRing K)) (hq : q ≠ 0) (hdiv : ∀ v, q ∣ L v) :
    V →ₗ[K] Polynomial (SeedRing K) where
  toFun v := Classical.choose (hdiv v)
  map_add' x y := by
    apply mul_left_cancel₀ hq
    rw [mul_add, ← Classical.choose_spec (hdiv (x + y)),
      ← Classical.choose_spec (hdiv x), ← Classical.choose_spec (hdiv y), map_add]
  map_smul' z x := by
    apply mul_left_cancel₀ hq
    simp only [RingHom.id_apply, mul_smul_comm]
    rw [← Classical.choose_spec (hdiv (z • x)), ← Classical.choose_spec (hdiv x), map_smul]

theorem divideMultiplierLinear_spec {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K))
    (q : Polynomial (SeedRing K)) (hq : q ≠ 0) (hdiv : ∀ v, q ∣ L v) (v : V) :
    L v = q * divideMultiplierLinear L q hq hdiv v :=
  Classical.choose_spec (hdiv v)

end

end ProximityPrize.SubmissionLower.Koala6831Comparison
