import ProximityPrize.SubmissionLower.SeedWeightedDegree

/-!
# The joint `Y + Z` degree of the agreement numerator

The `unitR` projection pair needs the seed-weighted degree of the agreement
polynomial, not just its separate `Y` and `Z` degrees.  Every step of the Taylor
recurrence adds `2 * c` where `c` is the seed-weighted degree of the surface,
exactly as in `ContactTaylorNumerators`' per-variable development; the two
variables the recurrence introduces (`X` and `R`) carry seed weight `0`, so they
cost nothing here.

Conclusion: `wdeg seedWeights (agreementNumerator F w c x u₀ u₁) ≤ 1 + 2 * w * S`
whenever `wdeg seedWeights F ≤ S`.
-/

namespace ProximityPrize.SubmissionLower.SeedTaylorBounds

open ContactDifferentialRing ContactTaylorNumerators ContactFactorCaps
open SeedWeightedDegree

noncomputable section

variable {K : Type*} [Field K]

variable (weights : Fin 4 → ℕ)

theorem wdeg_polyH_le {F : Poly4 K} {c : ℕ} (hF : wdeg weights F ≤ c) :
    wdeg weights (polyH K F) ≤ c :=
  wdeg_pderiv_le weights (2 : Fin 4) hF

theorem wdeg_polyG_le (hR : weights (2 : Fin 4) = 0) {F : Poly4 K} {c : ℕ}
    (hF : wdeg weights F ≤ c) : wdeg weights (polyG K F) ≤ c := by
  unfold polyG
  apply wdeg_neg_le
  apply wdeg_add_le
  · exact wdeg_pderiv_le weights (0 : Fin 4) hF
  · have hX : wdeg weights (MvPolynomial.X (2 : Fin 4) : Poly4 K) ≤ 0 :=
      wdeg_X_le weights (2 : Fin 4) 0 (by omega)
    simpa using wdeg_mul_le weights hX (wdeg_pderiv_le weights (1 : Fin 4) hF)

/-- One recurrence step costs `2 * c` in seed weight. -/
theorem wdeg_numeratorStep_le (hR : weights (2 : Fin 4) = 0)
    (F M : Poly4 K) (b a c : ℕ)
    (hF : wdeg weights F ≤ c) (hM : wdeg weights M ≤ a) :
    wdeg weights (numeratorStep K F b M) ≤ a + 2 * c := by
  have hX : wdeg weights (MvPolynomial.X (2 : Fin 4) : Poly4 K) ≤ 0 :=
    wdeg_X_le weights (2 : Fin 4) 0 (by omega)
  have hH : wdeg weights (polyH K F) ≤ c := wdeg_polyH_le weights hF
  have hG : wdeg weights (polyG K F) ≤ c := wdeg_polyG_le weights hR hF
  have hH2 : wdeg weights (polyH K F ^ 2) ≤ 2 * c := wdeg_pow_le weights 2 hH
  have hMX := wdeg_pderiv_le weights (0 : Fin 4) hM
  have hMY := wdeg_pderiv_le weights (1 : Fin 4) hM
  have hMR := wdeg_pderiv_le weights (2 : Fin 4) hM
  have hHX := wdeg_pderiv_le weights (0 : Fin 4) hH
  have hHY := wdeg_pderiv_le weights (1 : Fin 4) hH
  have hHR := wdeg_pderiv_le weights (2 : Fin 4) hH
  have h1 : wdeg weights (polyH K F ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M) ≤ a + 2 * c := by
    have := wdeg_mul_le weights hH2 hMX
    omega
  have h2 : wdeg weights
      (MvPolynomial.X (2 : Fin 4) * polyH K F ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M)
        ≤ a + 2 * c := by
    have := wdeg_mul_le weights (wdeg_mul_le weights hX hH2) hMY
    omega
  have h3 : wdeg weights
      (polyG K F * polyH K F * MvPolynomial.pderiv (2 : Fin 4) M) ≤ a + 2 * c := by
    have := wdeg_mul_le weights (wdeg_mul_le weights hG hH) hMR
    omega
  have hbx : wdeg weights (polyH K F * MvPolynomial.pderiv (0 : Fin 4) (polyH K F))
      ≤ 2 * c := by
    have := wdeg_mul_le weights hH hHX
    omega
  have hby : wdeg weights
      (MvPolynomial.X (2 : Fin 4) * polyH K F * MvPolynomial.pderiv (1 : Fin 4) (polyH K F))
        ≤ 2 * c := by
    have := wdeg_mul_le weights (wdeg_mul_le weights hX hH) hHY
    omega
  have hbr : wdeg weights (polyG K F * MvPolynomial.pderiv (2 : Fin 4) (polyH K F))
      ≤ 2 * c := by
    have := wdeg_mul_le weights hG hHR
    omega
  have hbrace := wdeg_add_le weights (wdeg_add_le weights hbx hby) hbr
  have hnM : wdeg weights (((2 * b : ℕ) : Poly4 K) * M) ≤ a := by
    have := wdeg_mul_le weights (wdeg_natCast_le weights (2 * b) 0) hM
    omega
  have h4 := wdeg_mul_le weights hnM hbrace
  change wdeg weights (polyH K F ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M +
      MvPolynomial.X (2 : Fin 4) * polyH K F ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M +
      polyG K F * polyH K F * MvPolynomial.pderiv (2 : Fin 4) M -
      ((2 * b : ℕ) : Poly4 K) * M *
        (polyH K F * MvPolynomial.pderiv (0 : Fin 4) (polyH K F) +
          MvPolynomial.X (2 : Fin 4) * polyH K F *
            MvPolynomial.pderiv (1 : Fin 4) (polyH K F) +
          polyG K F * MvPolynomial.pderiv (2 : Fin 4) (polyH K F))) ≤ a + 2 * c
  exact wdeg_sub_le weights (wdeg_add_le weights (wdeg_add_le weights h1 h2) h3) h4

theorem wdeg_numerator_le (hR : weights (2 : Fin 4) = 0)
    (F : Poly4 K) (c a₀ : ℕ) (hF : wdeg weights F ≤ c)
    (hbase : wdeg weights (MvPolynomial.X (1 : Fin 4) : Poly4 K) ≤ a₀) (b : ℕ) :
    wdeg weights (numerator K F b) ≤ a₀ + 2 * b * c := by
  induction b with
  | zero => simpa using hbase
  | succ b ih =>
      rw [numerator_succ]
      have hh := wdeg_numeratorStep_le weights hR F (numerator K F b) b (a₀ + 2 * b * c) c hF ih
      have heq : a₀ + 2 * (b + 1) * c = (a₀ + 2 * b * c) + 2 * c := by ring
      rw [heq]
      exact hh

theorem wdeg_commonNumeratorTerm_le (hR : weights (2 : Fin 4) = 0)
    (hX : weights (0 : Fin 4) = 0)
    (F : Poly4 K) (c a₀ : ℕ) (hF : wdeg weights F ≤ c)
    (hbase : wdeg weights (MvPolynomial.X (1 : Fin 4) : Poly4 K) ≤ a₀)
    (w j : ℕ) (hj : j ≤ w) (weightsK : ℕ → K) (x : K) :
    wdeg weights (commonNumeratorTerm F w weightsK x j) ≤ a₀ + 2 * w * c := by
  have hM := wdeg_numerator_le weights hR F c a₀ hF hbase j
  have hCM : wdeg weights (MvPolynomial.C (weightsK j) * numerator K F j)
      ≤ a₀ + 2 * j * c := by
    have := wdeg_mul_le weights (wdeg_C_le weights (weightsK j) 0) hM
    omega
  have hH : wdeg weights (polyH K F) ≤ c := wdeg_polyH_le weights hF
  have hHP := wdeg_pow_le weights (2 * (w - j)) hH
  have hshift : wdeg weights
      ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K)) ≤ 0 :=
    wdeg_sub_le weights (wdeg_C_le weights x 0) (wdeg_X_le weights (0 : Fin 4) 0 (by omega))
  have hXP : wdeg weights
      ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ^ j) ≤ 0 := by
    simpa using wdeg_pow_le weights j hshift
  have hterm := wdeg_mul_le weights (wdeg_mul_le weights hCM hHP) hXP
  have hsplit : 2 * j * c + 2 * (w - j) * c = 2 * w * c := by
    have : j + (w - j) = w := by omega
    calc 2 * j * c + 2 * (w - j) * c = 2 * (j + (w - j)) * c := by ring
      _ = 2 * w * c := by rw [this]
  unfold commonNumeratorTerm
  omega

theorem wdeg_clearedTaylorNumerator_le (hR : weights (2 : Fin 4) = 0)
    (hX : weights (0 : Fin 4) = 0)
    (F : Poly4 K) (c a₀ : ℕ) (hF : wdeg weights F ≤ c)
    (hbase : wdeg weights (MvPolynomial.X (1 : Fin 4) : Poly4 K) ≤ a₀)
    (w : ℕ) (weightsK : ℕ → K) (x : K) :
    wdeg weights (clearedTaylorNumerator F w weightsK x) ≤ a₀ + 2 * w * c := by
  unfold clearedTaylorNumerator
  apply wdeg_sum_le
  intro j hj
  exact wdeg_commonNumeratorTerm_le weights hR hX F c a₀ hF hbase w j
    (by have := Finset.mem_range.mp hj; omega) weightsK x

/-- The joint `Y + Z` degree of the agreement numerator. -/
theorem wdeg_agreementNumerator_le (hR : weights (2 : Fin 4) = 0)
    (hX : weights (0 : Fin 4) = 0)
    (F : Poly4 K) (c w : ℕ) (hF : wdeg weights F ≤ c)
    (hbase : wdeg weights (MvPolynomial.X (1 : Fin 4) : Poly4 K) ≤ 1)
    (hseed : weights (3 : Fin 4) ≤ 1)
    (weightsK : ℕ → K) (x u₀ u₁ : K) :
    wdeg weights (agreementNumerator F w weightsK x u₀ u₁) ≤ 1 + 2 * w * c := by
  unfold agreementNumerator
  apply wdeg_sub_le
  · exact wdeg_clearedTaylorNumerator_le weights hR hX F c 1 hF hbase w weightsK x
  · have haff : wdeg weights (affineSeedPolynomial u₀ u₁ : Poly4 K) ≤ 1 := by
      unfold affineSeedPolynomial
      apply wdeg_add_le
      · exact wdeg_C_le weights u₀ 1
      · have := wdeg_mul_le weights
          (wdeg_X_le weights (3 : Fin 4) 1 hseed) (wdeg_C_le weights u₁ 0)
        omega
    have hH : wdeg weights (polyH K F) ≤ c := wdeg_polyH_le weights hF
    have hp := wdeg_pow_le weights (2 * w) hH
    have := wdeg_mul_le weights haff hp
    omega

end

end ProximityPrize.SubmissionLower.SeedTaylorBounds
