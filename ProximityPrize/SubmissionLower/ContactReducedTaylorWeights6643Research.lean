import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactReducedTaylorR6643Research

/-!
# Cumulative support bounds for the reduced Taylor recurrence

Removing an R coefficient removes its full cumulative weight.  The correction
therefore has the same Y+R and Y+R+Z caps as the unreduced step.
-/

namespace ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research

open scoped BigOperators
open ContactDifferentialRing ContactTaylorNumerators ContactSingularDegreeBounds
open ContactReducedCoefficient6643Research
open ContactPost6464MinkowskiRecurrenceResearch ContactJointTaylorMiddleCap6631Research

noncomputable section

variable {K : Type*} [Field K]

theorem excessFactor_wt_le (weights : Fin 4 → ℕ)
    (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F P : Poly K) (s b C : ℕ) (hs : 1 ≤ s)
    (hF : wt weights F ≤ C) (hP : wt weights P ≤ 1 + 2 * b * (C - 1)) :
    wt weights (excessFactor F P s b) ≤ (2 * b + 1) * (C - s) := by
  by_cases hfzero : liftedCoefficient F s = 0
  · simp [excessFactor, hfzero, wt, MvPolynomial.weightedTotalDegree]
  let f := liftedCoefficient F s
  let c := liftedCoefficient P (2 * b * (s - 1))
  let D := C - s
  have hfadd := liftedCoefficient_weight_add_le weights F s hfzero
  change wt weights f + s * weights 2 ≤ wt weights F at hfadd
  rw [hR, Nat.mul_one] at hfadd
  have hsC : s ≤ C := by omega
  have hf : wt weights f ≤ D := by dsimp [D]; omega
  have hc : wt weights c ≤ 1 + 2 * b * D := by
    have h := liftedCoefficient_weight_le_sub weights P (2 * b * (s - 1))
    change wt weights c ≤ wt weights P - 2 * b * (s - 1) * weights 2 at h
    rw [hR, Nat.mul_one] at h
    have h' := h.trans (Nat.sub_le_sub_right hP (2 * b * (s - 1)))
    have hdecomp : C - 1 = D + (s - 1) := by dsimp [D]; omega
    have heq : 1 + 2 * b * (C - 1) = (1 + 2 * b * D) + 2 * b * (s - 1) := by
      rw [hdecomp]
      ring
    rwa [heq, Nat.add_sub_cancel] at h'
  have hdc : wt weights (MvPolynomial.pderiv (1 : Fin 4) c) ≤ 2 * b * D := by
    have h := wt_pderiv_le weights c 1 (1 + 2 * b * D) hc
    rw [hY] at h
    omega
  have hdf : wt weights (MvPolynomial.pderiv (1 : Fin 4) f) ≤ D - 1 := by
    simpa only [hY] using wt_pderiv_le weights f 1 D hf
  have hsf : wt weights ((s : Poly K) * f) ≤ D := by
    have h := wt_mul_le weights (s : Poly K) f
    rw [wt_natCast, Nat.zero_add] at h
    exact h.trans hf
  have hleft : wt weights ((s : Poly K) * f * MvPolynomial.pderiv (1 : Fin 4) c) ≤
      (2 * b + 1) * D := by
    have h := (wt_mul_le weights ((s : Poly K) * f) (MvPolynomial.pderiv (1 : Fin 4) c)).trans
      (Nat.add_le_add hsf hdc)
    apply h.trans
    apply le_of_eq
    ring
  have hright : wt weights (((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) *
      MvPolynomial.pderiv (1 : Fin 4) f * c) ≤ (2 * b + 1) * D := by
    by_cases hD : D = 0
    · have hz : MvPolynomial.pderiv (1 : Fin 4) f = 0 :=
        pderiv_eq_zero_of_wt_lt weights f 1 (by rw [hY]; omega)
      simp [hz, wt, MvPolynomial.weightedTotalDegree]
    · have hn : wt weights (((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) *
          MvPolynomial.pderiv (1 : Fin 4) f) ≤ D - 1 := by
        have h := wt_mul_le weights (((2 * b * (s - 1) + 2 * b : ℕ) : Poly K))
          (MvPolynomial.pderiv (1 : Fin 4) f)
        rw [wt_natCast, Nat.zero_add] at h
        exact h.trans hdf
      have h := (wt_mul_le weights
        (((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) * MvPolynomial.pderiv (1 : Fin 4) f)
        c).trans (Nat.add_le_add hn hc)
      apply h.trans
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have hinner := (wt_sub_le weights
    ((s : Poly K) * f * MvPolynomial.pderiv (1 : Fin 4) c)
    (((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) * MvPolynomial.pderiv (1 : Fin 4) f * c)).trans
    (max_le hleft hright)
  have h := wt_mul_le weights (s : Poly K)
    ((s : Poly K) * f * MvPolynomial.pderiv (1 : Fin 4) c -
      ((2 * b * (s - 1) + 2 * b : ℕ) : Poly K) * MvPolynomial.pderiv (1 : Fin 4) f * c)
  rw [wt_natCast, Nat.zero_add] at h
  exact h.trans hinner

theorem reductionCorrection_wt_le (weights : Fin 4 → ℕ)
    (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F P : Poly K) (s b C : ℕ) (hs : 1 ≤ s)
    (hF : wt weights F ≤ C) (hP : wt weights P ≤ 1 + 2 * b * (C - 1)) :
    wt weights (reductionMultiplier F P s b * F) ≤ 1 + 2 * (b + 1) * (C - 1) := by
  by_cases hfzero : liftedCoefficient F s = 0
  · simp [reductionMultiplier, excessFactor, hfzero, wt, MvPolynomial.weightedTotalDegree]
  have hfadd := liftedCoefficient_weight_add_le weights F s hfzero
  change wt weights (liftedCoefficient F s) + s * weights 2 ≤ wt weights F at hfadd
  rw [hR, Nat.mul_one] at hfadd
  have hsC : s ≤ C := by omega
  have hCpos : 1 ≤ C := hs.trans hsC
  have hq := excessFactor_wt_le weights hY hR F P s b C hs hF hP
  have hpow : wt weights ((MvPolynomial.X (2 : Fin 4) : Poly K) ^ ((2 * b + 1) * (s - 1))) ≤
      (2 * b + 1) * (s - 1) := by
    have h := wt_pow_le weights (MvPolynomial.X (2 : Fin 4) : Poly K) ((2 * b + 1) * (s - 1))
    simpa only [wt_X, hR, Nat.mul_one] using h
  have hqR := (wt_mul_le weights (excessFactor F P s b)
    ((MvPolynomial.X (2 : Fin 4)) ^ ((2 * b + 1) * (s - 1)))).trans
    (Nat.add_le_add hq hpow)
  have h := (wt_mul_le weights (reductionMultiplier F P s b) F).trans
    (Nat.add_le_add hqR hF)
  apply h.trans
  have hdecomp : (C - s) + (s - 1) = C - 1 := by omega
  apply le_of_eq
  calc
    (2 * b + 1) * (C - s) + (2 * b + 1) * (s - 1) + C =
        (2 * b + 1) * ((C - s) + (s - 1)) + C := by ring
    _ = (2 * b + 1) * (C - 1) + C := by rw [hdecomp]
    _ = (2 * b + 1) * (C - 1) + ((C - 1) + 1) :=
      congrArg (fun n => (2 * b + 1) * (C - 1) + n) (Nat.sub_add_cancel hCpos).symm
    _ = 1 + 2 * (b + 1) * (C - 1) := by ring

theorem reducedStep_wt_le (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F P : Poly K) (s b C : ℕ) (hs : 1 ≤ s) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (hP : wt weights P ≤ 1 + 2 * b * (C - 1)) :
    wt weights (reducedStep F P s b) ≤ 1 + 2 * (b + 1) * (C - 1) := by
  have hstep := numeratorStep_wt_le_equal_weight weights hX F P b
    (1 + 2 * b * (C - 1)) C (by omega) (by omega) (by omega) (by omega) hF hP
  rw [hR] at hstep
  have hstep' : wt weights (numeratorStep K F b P) ≤ 1 + 2 * (b + 1) * (C - 1) := by
    convert hstep using 1 <;> ring
  exact (wt_sub_le weights _ _).trans
    (max_le hstep' (reductionCorrection_wt_le weights hY hR F P s b C hs hF hP))

theorem reducedNumerator_wt_le (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly K) (s C : ℕ) (hs : 1 ≤ s) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (b : ℕ) :
    wt weights (reducedNumerator F s b) ≤ 1 + 2 * b * (C - 1) := by
  induction b with
  | zero => simp only [reducedNumerator_zero, wt_X, hY, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, le_refl]
  | succ b ih => exact reducedStep_wt_le weights hX hY hR F (reducedNumerator F s b) s b C hs hC hF ih

theorem reducedCommonNumeratorTerm_wt_le (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly K) (s C : ℕ) (hs : 1 ≤ s) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (w j : ℕ) (hj : j ≤ w)
    (c : ℕ → K) (x : K) :
    wt weights (reducedCommonNumeratorTerm F s w c x j) ≤ 1 + 2 * w * (C - 1) := by
  have hN := reducedNumerator_wt_le weights hX hY hR F s C hs hC hF j
  have hCN : wt weights (MvPolynomial.C (c j) * reducedNumerator F s j) ≤
      1 + 2 * j * (C - 1) := by
    have h := wt_mul_le weights (MvPolynomial.C (c j)) (reducedNumerator F s j)
    rw [wt_C, Nat.zero_add] at h
    exact h.trans hN
  have hH : wt weights (polyH K F) ≤ C - 1 := by
    simpa only [hR] using wt_polyH_le weights F C hF
  have hHP := (wt_pow_le weights (polyH K F) (2 * (w - j))).trans
    (Nat.mul_le_mul_left _ hH)
  have hXP : wt weights ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly K) ^ j) ≤ 0 := by
    have h := wt_pow_le weights
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly K) j
    simpa only [shiftedX_wt_eq_zero weights hX x, Nat.mul_zero] using h
  have h1 := (wt_mul_le weights (MvPolynomial.C (c j) * reducedNumerator F s j)
    (polyH K F ^ (2 * (w - j)))).trans (Nat.add_le_add hCN hHP)
  have h2 := (wt_mul_le weights
    (MvPolynomial.C (c j) * reducedNumerator F s j * polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j)).trans (Nat.add_le_add h1 hXP)
  apply h2.trans
  have hw : j + (w - j) = w := by omega
  apply le_of_eq
  calc
    (1 + 2 * j * (C - 1) + 2 * (w - j) * (C - 1)) + 0 =
        1 + 2 * (j + (w - j)) * (C - 1) := by ring
    _ = 1 + 2 * w * (C - 1) := by rw [hw]

theorem reducedClearedTaylorNumerator_wt_le (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly K) (s C : ℕ) (hs : 1 ≤ s) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (w : ℕ) (c : ℕ → K) (x : K) :
    wt weights (reducedClearedTaylorNumerator F s w c x) ≤ 1 + 2 * w * (C - 1) := by
  apply wt_sum_le
  intro j hj
  exact reducedCommonNumeratorTerm_wt_le weights hX hY hR F s C hs hC hF w j
    (by have h := Finset.mem_range.mp hj; omega) c x

/-- Applies to both cumulative weights (Y+R) and (Y+R+Z). -/
theorem reducedAgreementNumerator_wt_le (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly K) (s C : ℕ) (hs : 1 ≤ s) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (w : ℕ) (c : ℕ → K) (x u₀ u₁ : K) :
    wt weights (reducedAgreementNumerator F s w c x u₀ u₁) ≤
      max 1 (weights 3) + 2 * w * (C - 1) := by
  have hTaylor := reducedClearedTaylorNumerator_wt_le weights hX hY hR F s C hs hC hF w c x
  have hA := affineSeedPolynomial_wt_le weights u₀ u₁
  have hH : wt weights (polyH K F) ≤ C - 1 := by
    simpa only [hR] using wt_polyH_le weights F C hF
  have hHP := (wt_pow_le weights (polyH K F) (2 * w)).trans
    (Nat.mul_le_mul_left _ hH)
  have hprod := (wt_mul_le weights (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))).trans
    (Nat.add_le_add hA hHP)
  exact (wt_sub_le weights _ _).trans (max_le
    (hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _))
    (hprod.trans (Nat.add_le_add_right (Nat.le_max_right _ _) _)))

end


end ProximityPrize.SubmissionLower.ContactReducedTaylorNumerators6643Research
