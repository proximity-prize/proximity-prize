import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactTaylorNumerators

/-!
# Refined agreement Y-degree from the contact-weight cap

Differentiating in `R` consumes one unit of `R`-weight.  Near a contact
weight boundary this lowers the `Y`-degree of `H = ∂_R F` by one.  Keeping
that lower degree through the Taylor-numerator recurrence replaces the old
`1 + 2*w*ell` agreement bound by `1 + w*(ell+h)`.
-/

namespace ProximityPrize.SubmissionLower.ContactRefinedAgreementY

open ContactDifferentialRing ContactTaylorNumerators ContactInterpolation

noncomputable section

variable {K : Type*} [Field K]

/-- The contact support inequality sees the `R` exponent before
differentiation, so one positive `R` exponent excludes the top `Y` layer. -/
theorem polyH_Y_degree_le_of_mem_box
    (F : Poly4 K) (D w L s ell : ℕ)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (hw : 0 < w)
    (hthreshold : D ≤ w * ell + (w - 1)) :
    (polyH K F).degreeOf (1 : Fin 4) ≤ ell - 1 := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs := support_before_pderiv (2 : Fin 4) F d hd
  have hwgt := (hbox hs).2.2
  simp only [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2), Nat.add_zero] at hwgt
  by_contra hnot
  have hell : ell ≤ d 1 := by omega
  have hy := Nat.mul_le_mul_left w hell
  have hr : w - 1 ≤ (w - 1) * (d 2 + 1) := by
    have := Nat.mul_le_mul_left (w - 1) (show 1 ≤ d 2 + 1 by omega)
    simpa using this
  have hsum : w * ell + (w - 1) ≤
      w * d 1 + (w - 1) * (d 2 + 1) := Nat.add_le_add hy hr
  have hDle := hthreshold.trans hsum
  have hcore : w * d 1 + (w - 1) * (d 2 + 1) < D := by omega
  exact (Nat.not_lt_of_ge hDle) hcore

/-- One refined recurrence step.  The old proof charged `2*c`; the actual
derivative degree `h` makes the increment `c+h`. -/
theorem numeratorStep_nonR_degree_bound_of_polyH
    (i : Fin 4) (hi : i ≠ 2) (F M : Poly4 K) (b a c h : ℕ)
    (hF : F.degreeOf i ≤ c) (hH : (polyH K F).degreeOf i ≤ h)
    (hhc : h ≤ c) (hM : M.degreeOf i ≤ a) :
    (numeratorStep K F b M).degreeOf i ≤ a + c + h := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly4 K := MvPolynomial.X (2 : Fin 4)
  have hR : R.degreeOf i ≤ 0 := by
    simp only [R, MvPolynomial.degreeOf_X_of_ne hi, le_refl]
  have hG : G.degreeOf i ≤ c := by
    simpa only [Nat.add_zero] using polyG_degree_bound i F c 0 hF hR
  have hH2 := degree_pow_bound i 2 hH
  have hMX := pderiv_degree_bound (0 : Fin 4) i M a hM
  have hMY := pderiv_degree_bound (1 : Fin 4) i M a hM
  have hMR := pderiv_degree_bound (2 : Fin 4) i M a hM
  have hHX := pderiv_degree_bound (0 : Fin 4) i H h hH
  have hHY := pderiv_degree_bound (1 : Fin 4) i H h hH
  have hHR := pderiv_degree_bound (2 : Fin 4) i H h hH
  have h1 : (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M).degreeOf i ≤
      a + c + h := by
    have hh := degree_mul_bound i hH2 hMX
    simpa only [H] using hh.trans (by omega)
  have h2 : (R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M).degreeOf i ≤
      a + c + h := by
    have hh := degree_mul_bound i (degree_mul_bound i hR hH2) hMY
    simpa only [R, H] using hh.trans (by omega)
  have h3 : (G * H * MvPolynomial.pderiv (2 : Fin 4) M).degreeOf i ≤
      a + c + h := by
    have hh := degree_mul_bound i (degree_mul_bound i hG hH) hMR
    simpa only [G, H] using hh.trans (by omega)
  have hbx : (H * MvPolynomial.pderiv (0 : Fin 4) H).degreeOf i ≤ c + h := by
    have hh := degree_mul_bound i hH hHX
    simpa only [H] using hh.trans (by omega)
  have hby : (R * H * MvPolynomial.pderiv (1 : Fin 4) H).degreeOf i ≤ c + h := by
    have hh := degree_mul_bound i (degree_mul_bound i hR hH) hHY
    simpa only [R, H] using hh.trans (by omega)
  have hbr : (G * MvPolynomial.pderiv (2 : Fin 4) H).degreeOf i ≤ c + h := by
    have hh := degree_mul_bound i hG hHR
    simpa only [G, H] using hh
  have hbrace := degree_add_bound i (degree_add_bound i hbx hby) hbr
  have hn : (((2 * b : ℕ) : Poly4 K)).degreeOf i ≤ 0 :=
    le_of_eq (degree_natCast_eq_zero i (2 * b))
  have hnM : (((2 * b : ℕ) : Poly4 K) * M).degreeOf i ≤ a := by
    simpa only [Nat.zero_add] using degree_mul_bound i hn hM
  have h4 : ((((2 * b : ℕ) : Poly4 K) * M) *
      (H * MvPolynomial.pderiv (0 : Fin 4) H +
        R * H * MvPolynomial.pderiv (1 : Fin 4) H +
        G * MvPolynomial.pderiv (2 : Fin 4) H)).degreeOf i ≤ a + c + h := by
    have hh := degree_mul_bound i hnM hbrace
    exact hh.trans (by omega)
  change (H ^ 2 * MvPolynomial.pderiv (0 : Fin 4) M +
      R * H ^ 2 * MvPolynomial.pderiv (1 : Fin 4) M +
      G * H * MvPolynomial.pderiv (2 : Fin 4) M -
      ((2 * b : ℕ) : Poly4 K) * M *
        (H * MvPolynomial.pderiv (0 : Fin 4) H +
          R * H * MvPolynomial.pderiv (1 : Fin 4) H +
          G * MvPolynomial.pderiv (2 : Fin 4) H)).degreeOf i ≤ a + c + h
  exact degree_sub_bound i (degree_add_bound i (degree_add_bound i h1 h2) h3) h4

theorem numerator_nonR_degree_bound_of_polyH
    (i : Fin 4) (hi : i ≠ 2) (F : Poly4 K) (c h a₀ : ℕ)
    (hF : F.degreeOf i ≤ c) (hH : (polyH K F).degreeOf i ≤ h)
    (hhc : h ≤ c) (hbase : (MvPolynomial.X (1 : Fin 4) : Poly4 K).degreeOf i ≤ a₀)
    (b : ℕ) :
    (numerator K F b).degreeOf i ≤ a₀ + b * (c + h) := by
  induction b with
  | zero => simpa only [numerator_zero, Nat.zero_mul, Nat.add_zero] using hbase
  | succ b ih =>
      rw [numerator_succ]
      have hh := numeratorStep_nonR_degree_bound_of_polyH i hi F
        (numerator K F b) b (a₀ + b * (c + h)) c h hF hH hhc ih
      have heq : a₀ + (b + 1) * (c + h) = (a₀ + b * (c + h)) + c + h := by ring
      rw [heq]
      exact hh

theorem commonNumeratorTerm_nonR_degree_bound_of_polyH
    (i : Fin 4) (hi₀ : i ≠ 0) (hi₂ : i ≠ 2)
    (F : Poly4 K) (c h a₀ : ℕ)
    (hF : F.degreeOf i ≤ c) (hH : (polyH K F).degreeOf i ≤ h)
    (hhc : h ≤ c)
    (hbase : (MvPolynomial.X (1 : Fin 4) : Poly4 K).degreeOf i ≤ a₀)
    (w j : ℕ) (hj : j ≤ w) (weights : ℕ → K) (x : K) :
    (commonNumeratorTerm F w weights x j).degreeOf i ≤ a₀ + w * (c + h) := by
  have hM := numerator_nonR_degree_bound_of_polyH i hi₂ F c h a₀
    hF hH hhc hbase j
  have hCM : (MvPolynomial.C (weights j) * numerator K F j).degreeOf i ≤
      a₀ + j * (c + h) :=
    (MvPolynomial.degreeOf_C_mul_le (numerator K F j) i (weights j)).trans hM
  have hHP := degree_pow_bound i (2 * (w - j)) hH
  have hXP : ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ^ j).degreeOf i ≤ 0 := by
    simpa only [Nat.mul_zero] using degree_pow_bound i j (shiftedX_degree_bound i hi₀ x)
  have hterm := degree_mul_bound i (degree_mul_bound i hCM hHP) hXP
  have htwo : 2 * h ≤ c + h := by omega
  have hmul : (w - j) * (2 * h) ≤ (w - j) * (c + h) :=
    Nat.mul_le_mul_left (w - j) htwo
  have hsum : j * (c + h) + 2 * (w - j) * h ≤ w * (c + h) := by
    calc
      j * (c + h) + 2 * (w - j) * h =
          j * (c + h) + (w - j) * (2 * h) := by ring
      _ ≤ j * (c + h) + (w - j) * (c + h) := Nat.add_le_add_left hmul _
      _ = w * (c + h) := by rw [← Nat.add_mul, Nat.add_sub_of_le hj]
  exact hterm.trans (by
    have : (a₀ + j * (c + h)) + 2 * (w - j) * h + 0 ≤
        a₀ + w * (c + h) := by omega
    exact this)

theorem clearedTaylorNumerator_nonR_degree_bound_of_polyH
    (i : Fin 4) (hi₀ : i ≠ 0) (hi₂ : i ≠ 2)
    (F : Poly4 K) (c h a₀ : ℕ)
    (hF : F.degreeOf i ≤ c) (hH : (polyH K F).degreeOf i ≤ h)
    (hhc : h ≤ c)
    (hbase : (MvPolynomial.X (1 : Fin 4) : Poly4 K).degreeOf i ≤ a₀)
    (w : ℕ) (weights : ℕ → K) (x : K) :
    (clearedTaylorNumerator F w weights x).degreeOf i ≤ a₀ + w * (c + h) := by
  unfold clearedTaylorNumerator
  apply degree_sum_bound i
  intro j hj
  exact commonNumeratorTerm_nonR_degree_bound_of_polyH i hi₀ hi₂ F c h a₀
    hF hH hhc hbase w j (by have hh := Finset.mem_range.mp hj; omega) weights x

/-- Refined Y-degree of the actual agreement numerator. -/
theorem agreementNumerator_Y_degree_bound_of_polyH
    (F : Poly4 K) (c h w : ℕ)
    (hF : F.degreeOf (1 : Fin 4) ≤ c)
    (hH : (polyH K F).degreeOf (1 : Fin 4) ≤ h)
    (hhc : h ≤ c) (weights : ℕ → K) (x u₀ u₁ : K) :
    (agreementNumerator F w weights x u₀ u₁).degreeOf (1 : Fin 4) ≤
      1 + w * (c + h) := by
  unfold agreementNumerator
  apply degree_sub_bound (1 : Fin 4)
  · exact clearedTaylorNumerator_nonR_degree_bound_of_polyH
      (1 : Fin 4) (by decide) (by decide) F c h 1 hF hH hhc (by simp)
      w weights x
  · have ha := affineSeedPolynomial_degree_bound (1 : Fin 4) 0
      (by simp [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 4) ≠ 3)]) u₀ u₁
    have hp := degree_pow_bound (1 : Fin 4) (2 * w) hH
    have hm := degree_mul_bound (1 : Fin 4) ha hp
    have htwo : 2 * h ≤ c + h := by omega
    have hmul := Nat.mul_le_mul_left w htwo
    have hcap : 2 * w * h ≤ 1 + w * (c + h) := by
      calc
        2 * w * h = w * (2 * h) := by ring
        _ ≤ w * (c + h) := hmul
        _ ≤ 1 + w * (c + h) := Nat.le_add_left _ _
    exact hm.trans (by omega)

end

end ProximityPrize.SubmissionLower.ContactRefinedAgreementY

#print axioms ProximityPrize.SubmissionLower.ContactRefinedAgreementY.polyH_Y_degree_le_of_mem_box
#print axioms ProximityPrize.SubmissionLower.ContactRefinedAgreementY.agreementNumerator_Y_degree_bound_of_polyH
