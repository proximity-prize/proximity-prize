import ProximityPrize.SubmissionLower.LowerPolynomialFoundation
import ProximityPrize.SubmissionLower.Koala6831MovingDerivation


namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators
open MvPolynomial RCN081 RCN234 RCN235 RCN313 RCN156

noncomputable section

variable {K : Type*} [Field K]

private theorem wt_mul_bound (weights : Fin 4 → ℕ) {F G : P4 K} {a b : ℕ}
    (hF : wt weights F ≤ a) (hG : wt weights G ≤ b) : wt weights (F * G) ≤ a + b :=
  (wt_mul_le weights F G).trans (Nat.add_le_add hF hG)

private theorem wt_add_bound (weights : Fin 4 → ℕ) {F G : P4 K} {a : ℕ}
    (hF : wt weights F ≤ a) (hG : wt weights G ≤ a) : wt weights (F + G) ≤ a :=
  (wt_add_le weights F G).trans (max_le hF hG)

private theorem wt_sub_bound (weights : Fin 4 → ℕ) {F G : P4 K} {a : ℕ}
    (hF : wt weights F ≤ a) (hG : wt weights G ≤ a) : wt weights (F - G) ≤ a :=
  (wt_sub_le weights F G).trans (max_le hF hG)

private theorem wt_liftX_le_zero (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (f : Polynomial K) : wt weights (liftX f) ≤ 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simpa only [liftX, map_add] using wt_add_bound weights hf hg
  | monomial n a =>
      rw [liftX, Polynomial.aeval_monomial]
      change wt weights (MvPolynomial.C a * MvPolynomial.X (0 : Fin 4) ^ n) ≤ 0
      have hp := wt_pow_le weights (MvPolynomial.X (0 : Fin 4) : P4 K) n
      rw [wt_X, hX, Nat.mul_zero] at hp
      simpa only [Nat.add_zero] using wt_mul_bound weights (Nat.le_of_eq (wt_C weights a)) hp

private theorem wt_liftX_le (weights : Fin 4 → ℕ) (f : Polynomial K) :
    wt weights (liftX f) ≤ f.natDegree * weights 0 := by
  classical
  rw [congrArg (liftX (K := K)) (Polynomial.as_sum_support f)]
  simp only [liftX, map_sum]
  apply wt_finset_sum_le
  intro i hi
  rw [Polynomial.aeval_monomial]
  change wt weights (MvPolynomial.C (f.coeff i) * MvPolynomial.X (0 : Fin 4) ^ i) ≤
    f.natDegree * weights 0
  have hx := wt_pow_le weights (MvPolynomial.X (0 : Fin 4) : P4 K) i
  rw [wt_X] at hx
  have hc := wt_mul_bound weights (Nat.le_of_eq (wt_C weights (f.coeff i))) hx
  exact (by simpa only [Nat.zero_add] using hc :
    wt weights (MvPolynomial.C (f.coeff i) * MvPolynomial.X (0 : Fin 4) ^ i) ≤ i * weights 0).trans
      (Nat.mul_le_mul_right _ (Polynomial.le_natDegree_of_mem_supp i hi))

private theorem wt_mul_pderiv_bound (weights : Fin 4 → ℕ) (i : Fin 4)
    (coefficient P : P4 K) (gain : ℕ) (hcoefficient : wt weights coefficient ≤ weights i + gain) :
    wt weights (coefficient * MvPolynomial.pderiv i P) ≤ wt weights P + gain := by
  classical
  by_cases hz : MvPolynomial.pderiv i P = 0
  · simp [hz, wt, MvPolynomial.weightedTotalDegree]
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hz
    have hbefore := MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
    have hpos : weights i ≤ wt weights P := by
      simp only [map_add, Finsupp.weight_single, one_nsmul] at hbefore
      unfold wt
      omega
    have hprod := wt_mul_bound weights hcoefficient (wt_pderiv_le weights P i _ le_rfl)
    exact hprod.trans (by omega)

namespace FlowData

variable (B : FlowData K)

theorem flow_wt_le (weights : Fin 4 → ℕ) (P : P4 K) (gain : ℕ)
    (hz : wt weights (B.denominator ^ 2) ≤ weights 3 + gain)
    (hy : wt weights B.yCoefficient ≤ weights 1 + gain)
    (hr : wt weights B.rCoefficient ≤ weights 2 + gain) :
    wt weights (B.flow P) ≤ wt weights P + gain := by
  rw [B.flow_apply]
  exact wt_add_bound weights
    (wt_add_bound weights
      (wt_mul_pderiv_bound weights 3 _ P gain hz)
      (wt_mul_pderiv_bound weights 1 _ P gain hy))
    (wt_mul_pderiv_bound weights 2 _ P gain hr)

theorem flow_seed_wt_le (weights : Fin 4 → ℕ) (P : P4 K)
    (hX : weights 0 = 0) (hYR : weights 1 ≤ weights 2) :
    wt weights (B.flow P) ≤ wt weights P + weights 3 := by
  have hU := wt_liftX_le_zero (K := K) weights hX
  have hAffine (a b : Polynomial K) : wt weights (affine a b) ≤ weights 3 := by
    unfold affine
    apply wt_add_bound weights ((hU a).trans (Nat.zero_le _))
    simpa only [Nat.add_zero] using
      wt_mul_bound weights (Nat.le_of_eq (wt_X weights (3 : Fin 4) (K := K))) (hU b)
  have hA : wt weights B.A ≤ weights 3 := hAffine _ _
  have hAX : wt weights B.AX ≤ weights 3 := hAffine _ _
  have hD : wt weights B.denominator ≤ weights 3 := by
    simpa only [denominator, Nat.zero_add] using wt_mul_bound weights (hU B.d0) hA
  have hDX : wt weights B.denominatorX ≤ weights 3 := by
    unfold denominatorX
    apply wt_add_bound weights
    · simpa only [Nat.zero_add] using wt_mul_bound weights (hU B.d0.derivative) hA
    · simpa only [Nat.zero_add] using wt_mul_bound weights (hU B.d0) hAX
  have hM : wt weights B.minor ≤ 0 := by
    unfold minor
    exact wt_sub_bound weights
      (wt_mul_bound weights (hU B.a1) (hU B.c0))
      (wt_mul_bound weights (hU B.a0) (hU B.c1))
  have hMX : wt weights B.minorX ≤ 0 := by
    unfold minorX
    exact wt_sub_bound weights
      (wt_add_bound weights
        (wt_mul_bound weights (hU B.a1.derivative) (hU B.c0))
        (wt_mul_bound weights (hU B.a1) (hU B.c0.derivative)))
      (wt_add_bound weights
        (wt_mul_bound weights (hU B.a0.derivative) (hU B.c1))
        (wt_mul_bound weights (hU B.a0) (hU B.c1.derivative)))
  have hD0 : wt weights ((liftX B.d0) ^ 2) ≤ 0 := by
    exact (wt_pow_le weights (liftX B.d0) 2).trans (Nat.mul_le_mul_left 2 (hU B.d0))
  have hY : wt weights (MvPolynomial.X (1 : Fin 4) : P4 K) ≤ weights 1 := (wt_X weights _).le
  have hR : wt weights (MvPolynomial.X (2 : Fin 4) : P4 K) ≤ weights 2 := (wt_X weights _).le
  have hS : wt weights (B.A * (liftX B.d0) ^ 2 * liftX B.a1) ≤ weights 3 := by
    simpa only [Nat.add_zero] using wt_mul_bound weights (wt_mul_bound weights hA hD0) (hU B.a1)
  have hDelta : wt weights (liftX B.a1.derivative * B.A - liftX B.a1 * B.AX) ≤ weights 3 := by
    apply wt_sub_bound weights
    · simpa only [Nat.zero_add] using wt_mul_bound weights (hU B.a1.derivative) hA
    · simpa only [Nat.zero_add] using wt_mul_bound weights (hU B.a1) hAX
  apply B.flow_wt_le weights P (weights 3)
  · exact (wt_pow_le weights B.denominator 2).trans (by omega)
  · unfold yCoefficient
    apply wt_add_bound weights
    · exact (wt_mul_bound weights hS hY).trans (by omega)
    · exact (wt_mul_bound weights hD hM).trans (by omega)
  · unfold rCoefficient
    apply wt_sub_bound weights
    · apply wt_add_bound weights
      · apply wt_add_bound weights
        · exact (wt_mul_bound weights (wt_mul_bound weights hD0 hDelta) hY).trans (by omega)
        · exact (wt_mul_bound weights hS hR).trans (by omega)
      · exact (wt_mul_bound weights hD hMX).trans (by omega)
    · exact (wt_mul_bound weights hDX hM).trans (by omega)

theorem flow_slope_le (P : P4 K) :
    wt residualSWeights (B.flow P) ≤ wt residualSWeights P := by
  have h := B.flow_seed_wt_le residualSWeights P (by decide) (by decide)
  change wt residualSWeights (B.flow P) ≤ wt residualSWeights P + 0 at h
  simpa only [Nat.add_zero] using h

theorem flow_middle_le (P : P4 K) :
    wt residualYSWeights (B.flow P) ≤ wt residualYSWeights P := by
  have h := B.flow_seed_wt_le residualYSWeights P (by decide) (by decide)
  change wt residualYSWeights (B.flow P) ≤ wt residualYSWeights P + 0 at h
  simpa only [Nat.add_zero] using h

theorem flow_total_le (P : P4 K) :
    wt residualTotalWeights (B.flow P) ≤ wt residualTotalWeights P + 1 :=
  B.flow_seed_wt_le residualTotalWeights P (by decide) (by decide)

theorem flow_contact_wt_le (P : P4 K) (w delta : ℕ) (hw : 0 < w) (hdelta : 0 < delta)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ delta)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ w + delta) :
    wt (contactWeights w) (B.flow P) ≤ wt (contactWeights w) P + 2 * delta := by
  let W := contactWeights w
  let d := B.d0.natDegree
  let a := max B.a0.natDegree B.a1.natDegree
  have hda : d + a ≤ delta := hden
  have hx (f : Polynomial K) : wt W (liftX f) ≤ f.natDegree := by
    simpa [W, contactWeights] using wt_liftX_le W f
  have hxf (f : Polynomial K) {c : ℕ} (h : f.natDegree ≤ c) : wt W (liftX f) ≤ c :=
    (hx f).trans h
  have ha0 : B.a0.natDegree ≤ a := le_max_left _ _
  have ha1 : B.a1.natDegree ≤ a := le_max_right _ _
  have hz : wt W (MvPolynomial.X (3 : Fin 4) : P4 K) ≤ 0 := by
    rw [wt_X]
    exact Nat.zero_le 0
  have hA : wt W B.A ≤ a := by
    unfold A affine
    apply wt_add_bound W (hxf B.a0 ha0)
    simpa only [Nat.zero_add] using wt_mul_bound W hz (hxf B.a1 ha1)
  have hAX : wt W B.AX ≤ a - 1 := by
    unfold AX affine
    apply wt_add_bound W
    · exact hxf B.a0.derivative ((B.a0.natDegree_derivative_le).trans (Nat.sub_le_sub_right ha0 1))
    · simpa only [Nat.zero_add] using wt_mul_bound W hz
        (hxf B.a1.derivative ((B.a1.natDegree_derivative_le).trans (Nat.sub_le_sub_right ha1 1)))
  have hD : wt W B.denominator ≤ d + a := wt_mul_bound W (hx B.d0) hA
  have hDX : wt W B.denominatorX ≤ delta - 1 := by
    unfold denominatorX
    apply wt_add_bound W
    · by_cases hd : d = 0
      · simp [Polynomial.derivative_of_natDegree_zero hd, liftX, wt, MvPolynomial.weightedTotalDegree]
      · exact (wt_mul_bound W (hxf B.d0.derivative (B.d0.natDegree_derivative_le)) hA).trans (by omega)
    · by_cases ha : a = 0
      · have h0 := Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (ha ▸ ha0))
        have h1 := Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (ha ▸ ha1))
        simp [AX, affine, h0, h1, liftX, wt, MvPolynomial.weightedTotalDegree]
      · exact (wt_mul_bound W (hx B.d0) hAX).trans (by omega)
  have hM : wt W B.minor ≤ w + delta := by
    simpa only [minor, liftX, map_sub, map_mul] using hxf (B.a1 * B.c0 - B.a0 * B.c1) hminor
  have hMX : wt W B.minorX ≤ w + delta - 1 := by
    let M := B.a1 * B.c0 - B.a0 * B.c1
    have h := hxf M.derivative (M.natDegree_derivative_le.trans (Nat.sub_le_sub_right hminor 1))
    simpa only [M, Polynomial.derivative_sub, Polynomial.derivative_mul, minorX,
      liftX, map_sub, map_add, map_mul, add_comm] using h
  have hD0 : wt W ((liftX B.d0) ^ 2) ≤ 2 * d :=
    (wt_pow_le W _ 2).trans (Nat.mul_le_mul_left 2 (hx B.d0))
  have hS : wt W (B.A * (liftX B.d0) ^ 2 * liftX B.a1) ≤ 2 * delta :=
    (wt_mul_bound W (wt_mul_bound W hA hD0) (hxf B.a1 ha1)).trans (by omega)
  have hY : wt W (MvPolynomial.X (1 : Fin 4) : P4 K) ≤ w := by rw [wt_X]; rfl
  have hR : wt W (MvPolynomial.X (2 : Fin 4) : P4 K) ≤ w - 1 := by rw [wt_X]; rfl
  change wt W (B.flow P) ≤ wt W P + 2 * delta
  apply B.flow_wt_le W P (2 * delta)
  · change wt W (B.denominator ^ 2) ≤ 0 + 2 * delta
    exact (wt_pow_le W _ 2).trans (by omega)
  · change wt W B.yCoefficient ≤ w + 2 * delta
    unfold yCoefficient
    apply wt_add_bound W
    · exact (wt_mul_bound W hS hY).trans (by omega)
    · exact (wt_mul_bound W hD hM).trans (by omega)
  · change wt W B.rCoefficient ≤ (w - 1) + 2 * delta
    unfold rCoefficient
    apply wt_sub_bound W
    · apply wt_add_bound W
      · apply wt_add_bound W
        · by_cases ha : a = 0
          · have h0 := Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (ha ▸ ha0))
            have h1 := Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (ha ▸ ha1))
            simp [AX, affine, h0, h1, liftX, wt, MvPolynomial.weightedTotalDegree]
          · have hA1X := hxf B.a1.derivative
              (B.a1.natDegree_derivative_le.trans (Nat.sub_le_sub_right ha1 1))
            have hdiff : wt W (liftX B.a1.derivative * B.A - liftX B.a1 * B.AX) ≤ a + (a - 1) := by
              apply wt_sub_bound W
              · exact (wt_mul_bound W hA1X hA).trans (by omega)
              · exact wt_mul_bound W (hxf B.a1 ha1) hAX
            exact (wt_mul_bound W (wt_mul_bound W hD0 hdiff) hY).trans (by omega)
        · exact (wt_mul_bound W hS hR).trans (by omega)
      · exact (wt_mul_bound W hD hMX).trans (by omega)
    · exact (wt_mul_bound W hDX hM).trans (by omega)

theorem flow_iterate_wt_le (weights : Fin 4 → ℕ) (gain j : ℕ) (P : P4 K)
    (hstep : ∀ Q, wt weights (B.flow Q) ≤ wt weights Q + gain) :
    wt weights ((B.flow : P4 K → P4 K)^[j] P) ≤ wt weights P + j * gain := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep _).trans (by rw [Nat.succ_mul]; omega)

end FlowData

end

end ProximityPrize.SubmissionLower.Koala6831Moving
