import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartCuts


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open RCN081 RCN136 RCN234

noncomputable section

set_option maxHeartbeats 4800000
set_option maxRecDepth 16000
set_option Elab.async false

variable {K L : Type} [Field K] [Field L]

theorem surfaceMap_wt_le (φ : Polynomial K →+* L) (weight : Fin 3 → ℕ) (Q : Carrier K) :
    MvPolynomial.weightedTotalDegree weight (surfaceMap φ Q) ≤
      wt (Fin.cases 0 weight) Q := by
  unfold wt MvPolynomial.weightedTotalDegree
  refine Finset.sup_le fun e he => ?_
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
  have hb := MvPolynomial.le_weightedTotalDegree (Fin.cases 0 weight) hd
  rw [weight_fin4] at hb
  rw [RCN372.weight_fin3]
  have h₁ : Fin.cases 0 weight (1 : Fin 4) = weight 0 := rfl
  have h₂ : Fin.cases 0 weight (2 : Fin 4) = weight 1 := rfl
  have h₃ : Fin.cases 0 weight (3 : Fin 4) = weight 2 := rfl
  have hs₀ : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  have hs₁ : (1 : Fin 3).succ = (2 : Fin 4) := rfl
  have hs₂ : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simpa only [Fin.cases_zero, h₁, h₂, h₃, hs₀, hs₁, hs₂, mul_zero, zero_add,
    Finsupp.tail_apply, MvPolynomial.weightedTotalDegree] using hb

private theorem tail_cap_increase (cap y w delay μ : ℕ)
    (hd : 1 ≤ delay) (hμ : delay ≤ μ) :
    y + (2 * (w + delay) + 1) * (cap - y) ≤
      μ * (y + (2 * w + 3) * (cap - y)) := by
  have hfac : 1 ≤ μ := hd.trans hμ
  have hc : 2 * (w + delay) + 1 ≤ μ * (2 * w + 3) := calc
    _ = (2 * w + 1) + 2 * delay := by omega
    _ ≤ μ * (2 * w + 1) + μ * 2 := Nat.add_le_add
      (by simpa only [one_mul] using Nat.mul_le_mul_right (2 * w + 1) hfac)
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 hμ)
    _ = _ := by ring
  have hyμ : y ≤ μ * y := by
    simpa only [one_mul] using Nat.mul_le_mul_right y hfac
  rw [Nat.mul_add μ y ((2 * w + 3) * (cap - y)),
    ← Nat.mul_assoc μ (2 * w + 3) (cap - y)]
  exact Nat.add_le_add hyμ (Nat.mul_le_mul_right (cap - y) hc)

private theorem numerator_wt_le_order_mul (weights : Fin 4 → ℕ) (F : Carrier K)
    (cap w delay μ : ℕ) (hx : weights 0 = 0) (hy : weights 1 ≤ cap)
    (hcap : wt weights F ≤ cap) (hd : 1 ≤ delay) (hμ : delay ≤ μ) :
    wt weights (tailNumerator F (w + delay)) ≤
      μ * (weights 1 + (2 * w + 3) * (cap - weights 1)) :=
  Nat.le_trans
    (tailNumerator_wt_le weights F cap hx hy hcap (w + delay))
    (tail_cap_increase cap (weights 1) w delay μ hd hμ)

theorem tailNumerator_surface_wt_le_order_mul
    (φ : Polynomial K →+* L) (F : Carrier K) (weight : Fin 3 → ℕ)
    (cap w delay μ : ℕ) (hy : weight 0 ≤ cap) (hcap : wt (Fin.cases 0 weight) F ≤ cap)
    (hd : 1 ≤ delay) (hμ : delay ≤ μ) :
    MvPolynomial.weightedTotalDegree weight (surfaceMap φ (tailNumerator F (w + delay))) ≤
      μ * (weight 0 + (2 * w + 3) * (cap - weight 0)) := by
  let weights : Fin 4 → ℕ := Fin.cases 0 weight
  have hx : weights 0 = 0 := rfl
  have hy' : weights 1 ≤ cap := hy
  have hlift : weights 1 = weight 0 := rfl
  have htail := numerator_wt_le_order_mul weights F cap w delay μ hx hy' hcap hd hμ
  rw [hlift] at htail
  exact Nat.le_trans (surfaceMap_wt_le φ weight (tailNumerator F (w + delay))) htail

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
