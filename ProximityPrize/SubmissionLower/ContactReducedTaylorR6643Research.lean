import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research
import ProximityPrize.SubmissionLower.ContactReducedCoefficient6643Research

/-! Exact cancellation of the unique excess R coefficient in each reduced step. -/

namespace ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research

open scoped BigOperators
open ContactDifferentialRing ContactTaylorNumerators ContactSingularDegreeBounds
open ContactReducedCoefficient6643Research

noncomputable section

set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

theorem liftedCoefficient_polyH_top (F : Poly K) (s : ℕ) (hs : 1 ≤ s) :
    liftedCoefficient (polyH K F) (s - 1) = (s : Poly K) * liftedCoefficient F s := by
  simpa only [polyH, map_natCast] using liftedCoefficient_pderiv_R_top F s hs

theorem liftedCoefficient_polyG_top (F : Poly K) (s : ℕ)
    (hF : F.degreeOf (2 : Fin 4) ≤ s) :
    liftedCoefficient (polyG K F) (s + 1) =
      -MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) := by
  have hPX := pderiv_degree_bound (0 : Fin 4) (2 : Fin 4) F s hF
  have hx : liftedCoefficient (MvPolynomial.pderiv (0 : Fin 4) F) (s + 1) = 0 :=
    liftedCoefficient_eq_zero_of_degree_lt _ _ (by omega)
  simp only [polyG, liftedCoefficient_neg, liftedCoefficient_add, hx, zero_add,
    liftedCoefficient_X_R_mul, liftedCoefficient_pderiv_other F 1 (by decide) s]

/-- The leading vector-field coefficient, including a zero-degree input. -/
theorem vectorNumerator_top_coefficient (F P : Poly K) (a s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (hP : P.degreeOf (2 : Fin 4) ≤ a) :
    liftedCoefficient (vectorNumerator F P) (a + s) =
      (s : Poly K) * liftedCoefficient F s *
          MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient P a) -
        (a : Poly K) * MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) *
          liftedCoefficient P a := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly K := MvPolynomial.X (2 : Fin 4)
  have hR : R.degreeOf (2 : Fin 4) ≤ 1 := by simp [R]
  have hH : H.degreeOf (2 : Fin 4) ≤ s - 1 :=
    pderiv_same_degree_bound (2 : Fin 4) F s hF
  have hG : G.degreeOf (2 : Fin 4) ≤ s + 1 :=
    polyG_degree_bound (2 : Fin 4) F s 1 hF hR
  have hPX := pderiv_degree_bound (0 : Fin 4) (2 : Fin 4) P a hP
  have hPY := pderiv_degree_bound (1 : Fin 4) (2 : Fin 4) P a hP
  have hPR := pderiv_same_degree_bound (2 : Fin 4) P a hP
  have hcR : liftedCoefficient R 1 = 1 := by
    simpa only [R, pow_one] using liftedCoefficient_X_R_pow (K := K) 1
  have hcH : liftedCoefficient H (s - 1) = (s : Poly K) * liftedCoefficient F s :=
    liftedCoefficient_polyH_top F s hs
  have hRH : (R * H).degreeOf (2 : Fin 4) ≤ s := by
    have h := degree_mul_bound (2 : Fin 4) hR hH
    omega
  have hcRH : liftedCoefficient (R * H) s = (s : Poly K) * liftedCoefficient F s := by
    have h := liftedCoefficient_mul_top R H 1 (s - 1) hR hH
    rw [show 1 + (s - 1) = s by omega, hcR, hcH, one_mul] at h
    exact h
  have hx : liftedCoefficient (H * MvPolynomial.pderiv (0 : Fin 4) P) (a + s) = 0 := by
    apply liftedCoefficient_eq_zero_of_degree_lt
    have h := degree_mul_bound (2 : Fin 4) hH hPX
    omega
  have hy : liftedCoefficient (R * H * MvPolynomial.pderiv (1 : Fin 4) P) (a + s) =
      (s : Poly K) * liftedCoefficient F s *
        MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient P a) := by
    have h := liftedCoefficient_mul_top (R * H) (MvPolynomial.pderiv (1 : Fin 4) P)
      s a hRH hPY
    rw [hcRH, liftedCoefficient_pderiv_other P 1 (by decide) a] at h
    simpa only [Nat.add_comm] using h
  have hr : liftedCoefficient (G * MvPolynomial.pderiv (2 : Fin 4) P) (a + s) =
      -(a : Poly K) * MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) *
        liftedCoefficient P a := by
    by_cases ha : a = 0
    · have hz := pderiv_eq_zero_of_degree_bound_zero (2 : Fin 4) P (by simpa [ha] using hP)
      simp [ha, hz]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha
      have h := liftedCoefficient_mul_top G (MvPolynomial.pderiv (2 : Fin 4) P)
        (s + 1) (a - 1) hG hPR
      rw [show s + 1 + (a - 1) = a + s by omega,
        liftedCoefficient_polyG_top F s hF,
        liftedCoefficient_pderiv_R_top P a hapos, map_natCast] at h
      rw [h]
      ring
  change liftedCoefficient (H * MvPolynomial.pderiv (0 : Fin 4) P +
    R * H * MvPolynomial.pderiv (1 : Fin 4) P +
      G * MvPolynomial.pderiv (2 : Fin 4) P) (a + s) = _
  rw [liftedCoefficient_add, liftedCoefficient_add, hx, hy, hr]
  ring

theorem vectorNumerator_H_top_coefficient (F : Poly K) (s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s) :
    liftedCoefficient (vectorNumerator F (polyH K F)) (2 * s - 1) =
      (s : Poly K) * liftedCoefficient F s *
        MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) := by
  have hH := pderiv_same_degree_bound (2 : Fin 4) F s hF
  have h := vectorNumerator_top_coefficient F (polyH K F) (s - 1) s hs hF hH
  rw [show s - 1 + s = 2 * s - 1 by omega,
    liftedCoefficient_polyH_top F s hs] at h
  rw [h, MvPolynomial.pderiv_mul]
  simp only [Derivation.map_natCast, zero_mul, mul_zero, add_zero, zero_add]
  rw [Nat.cast_sub hs]
  simp only [Nat.cast_one]
  ring

/-- The excess coefficient is polynomially divisible by the surface's nominal
leading coefficient; this remains true when that coefficient is zero. -/
theorem numeratorStep_top_coefficient (F P : Poly K) (a s b : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (hP : P.degreeOf (2 : Fin 4) ≤ a) :
    liftedCoefficient (numeratorStep K F b P) (a + (2 * s - 1)) =
      liftedCoefficient F s * ((s : Poly K) *
        ((s : Poly K) * liftedCoefficient F s *
            MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient P a) -
          ((a + 2 * b : ℕ) : Poly K) *
            MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F s) *
              liftedCoefficient P a)) := by
  have hH := pderiv_same_degree_bound (2 : Fin 4) F s hF
  have hV := vectorNumerator_R_degree_bound F P a s hs hF hP
  have hVH : (vectorNumerator F (polyH K F)).degreeOf (2 : Fin 4) ≤ 2 * s - 1 := by
    have h := vectorNumerator_R_degree_bound F (polyH K F) (s - 1) s hs hF hH
    omega
  have hfirst := liftedCoefficient_mul_top (polyH K F) (vectorNumerator F P)
    (s - 1) (a + s) hH hV
  rw [show s - 1 + (a + s) = a + (2 * s - 1) by omega,
    liftedCoefficient_polyH_top F s hs,
    vectorNumerator_top_coefficient F P a s hs hF hP] at hfirst
  have hlast := liftedCoefficient_mul_top P (vectorNumerator F (polyH K F))
    a (2 * s - 1) hP hVH
  rw [vectorNumerator_H_top_coefficient F s hs hF] at hlast
  rw [numeratorStep_eq_vector, liftedCoefficient_sub, hfirst]
  rw [show ((2 * b : ℕ) : Poly K) * P * vectorNumerator F (polyH K F) =
    ((2 * b : ℕ) : Poly K) * (P * vectorNumerator F (polyH K F)) by ring,
    liftedCoefficient_natCast_mul, hlast]
  push_cast
  ring

theorem excessFactor_R_degree (F P : Poly K) (s b : ℕ) :
    (excessFactor F P s b).degreeOf (2 : Fin 4) = 0 := by
  have hf : (liftedCoefficient F s).degreeOf (2 : Fin 4) ≤ 0 :=
    (liftedCoefficient_R_degree F s).le
  have hc : (liftedCoefficient P (2 * b * (s - 1))).degreeOf (2 : Fin 4) ≤ 0 :=
    (liftedCoefficient_R_degree P _).le
  have hdf := pderiv_degree_bound (1 : Fin 4) (2 : Fin 4) _ 0 hf
  have hdc := pderiv_degree_bound (1 : Fin 4) (2 : Fin 4) _ 0 hc
  have hs : (s : Poly K).degreeOf (2 : Fin 4) ≤ 0 := (degree_natCast_eq_zero 2 s).le
  have hn : ((2 * b * (s - 1) + 2 * b : ℕ) : Poly K).degreeOf (2 : Fin 4) ≤ 0 :=
    (degree_natCast_eq_zero 2 _).le
  have hleft := degree_mul_bound (2 : Fin 4) (degree_mul_bound (2 : Fin 4) hs hf) hdc
  have hright := degree_mul_bound (2 : Fin 4) (degree_mul_bound (2 : Fin 4) hn hdf) hc
  have hinner := degree_sub_bound (2 : Fin 4) hleft hright
  have h := degree_mul_bound (2 : Fin 4) hs hinner
  exact Nat.eq_zero_of_le_zero (by simpa only [excessFactor, Nat.zero_add] using h)

theorem reducedStep_R_degree_bound (F P : Poly K) (s b : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (hP : P.degreeOf (2 : Fin 4) ≤ 2 * b * (s - 1)) :
    (reducedStep F P s b).degreeOf (2 : Fin 4) ≤ 2 * (b + 1) * (s - 1) := by
  let a := 2 * b * (s - 1)
  let t := a + (2 * s - 1)
  have ht : 0 < t := by dsimp [t]; omega
  have hW := numeratorStep_R_degree_bound F P b a s hs hF hP
  have hcoeff : liftedCoefficient (numeratorStep K F b P) t =
      excessFactor F P s b * liftedCoefficient F s := by
    rw [numeratorStep_top_coefficient F P a s b hs hF hP]
    dsimp [excessFactor, a]
    ring
  have hks : (2 * b + 1) * (s - 1) + s = t := by
    dsimp [t, a]
    have hsi : s = (s - 1) + 1 := by omega
    conv_lhs => rhs; rw [hsi]
    have ht' : 2 * s - 1 = 2 * (s - 1) + 1 := by omega
    rw [ht']
    ring
  have h := degreeR_sub_cancel_top (numeratorStep K F b P) F (excessFactor F P s b)
    t s ((2 * b + 1) * (s - 1)) ht hW hF (excessFactor_R_degree F P s b) hks hcoeff
  have heq : t - 1 = 2 * (b + 1) * (s - 1) := by
    dsimp [t, a]
    have ht' : 2 * s - 1 = 2 * (s - 1) + 1 := by omega
    rw [ht', ← Nat.add_assoc, Nat.add_sub_cancel]
    ring
  simpa only [reducedStep, reductionMultiplier, heq] using h

theorem reducedNumerator_R_degree_bound (F : Poly K) (s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s) (b : ℕ) :
    (reducedNumerator F s b).degreeOf (2 : Fin 4) ≤ 2 * b * (s - 1) := by
  induction b with
  | zero => simp [MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 4) ≠ 1)]
  | succ b ih => exact reducedStep_R_degree_bound F (reducedNumerator F s b) s b hs hF ih

theorem reducedCommonNumeratorTerm_R_degree_bound (F : Poly K) (s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (w j : ℕ) (hj : j ≤ w) (c : ℕ → K) (x : K) :
    (reducedCommonNumeratorTerm F s w c x j).degreeOf (2 : Fin 4) ≤ 2 * w * (s - 1) := by
  have hN := reducedNumerator_R_degree_bound F s hs hF j
  have hCN : (MvPolynomial.C (c j) * reducedNumerator F s j).degreeOf (2 : Fin 4) ≤
      2 * j * (s - 1) :=
    (MvPolynomial.degreeOf_C_mul_le (reducedNumerator F s j) (2 : Fin 4) (c j)).trans hN
  have hH := pderiv_same_degree_bound (2 : Fin 4) F s hF
  have hHP := degree_pow_bound (2 : Fin 4) (2 * (w - j)) hH
  have hXP : ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly K) ^ j).degreeOf
      (2 : Fin 4) ≤ 0 := by
    simpa only [Nat.mul_zero] using
      degree_pow_bound (2 : Fin 4) j (shiftedX_degree_bound (2 : Fin 4) (by decide) x)
  have h := degree_mul_bound (2 : Fin 4) (degree_mul_bound (2 : Fin 4) hCN hHP) hXP
  apply h.trans
  have hw : j + (w - j) = w := by omega
  calc
    2 * j * (s - 1) + 2 * (w - j) * (s - 1) + 0 =
        2 * (j + (w - j)) * (s - 1) := by ring
    _ ≤ 2 * w * (s - 1) := by simp only [hw, le_refl]

theorem reducedClearedTaylorNumerator_R_degree_bound (F : Poly K) (s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (w : ℕ) (c : ℕ → K) (x : K) :
    (reducedClearedTaylorNumerator F s w c x).degreeOf (2 : Fin 4) ≤ 2 * w * (s - 1) := by
  apply degree_sum_bound (2 : Fin 4)
  intro j hj
  exact reducedCommonNumeratorTerm_R_degree_bound F s hs hF w j
    (by have h := Finset.mem_range.mp hj; omega) c x

theorem reducedAgreementNumerator_R_degree_bound (F : Poly K) (s : ℕ)
    (hs : 1 ≤ s) (hF : F.degreeOf (2 : Fin 4) ≤ s)
    (w : ℕ) (c : ℕ → K) (x u₀ u₁ : K) :
    (reducedAgreementNumerator F s w c x u₀ u₁).degreeOf (2 : Fin 4) ≤ 2 * w * (s - 1) := by
  apply degree_sub_bound (2 : Fin 4)
  · exact reducedClearedTaylorNumerator_R_degree_bound F s hs hF w c x
  · have hA := affineSeedPolynomial_degree_bound (2 : Fin 4) 0
      (by simp [MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 4) ≠ 3)]) u₀ u₁
    have hH := pderiv_same_degree_bound (2 : Fin 4) F s hF
    simpa only [polyH, Nat.zero_add] using
      degree_mul_bound (2 : Fin 4) hA (degree_pow_bound (2 : Fin 4) (2 * w) hH)

end


end ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research
