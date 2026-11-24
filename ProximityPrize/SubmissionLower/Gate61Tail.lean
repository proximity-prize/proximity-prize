import ProximityPrize.SubmissionLower.Gate61Level
set_option Elab.async false

set_option autoImplicit false

namespace Gate61Cell
open Gate61FreeCard (mx mn mx_eq mn_eq)

theorem hullP (l : Bool) : hB l 4012 1650 = 4012 ∧ hJ l 1650 = 1650 ∧ hT l 1650 550 = 550 := by
  cases l <;> simp [hB, hJ, hT, mx_eq, mn_eq]

theorem hull_le (l : Bool) {yb yj yt : ℕ} (h0 : yb ≤ 4012) (h1 : yj ≤ 1650) (h2 : yt ≤ 550) :
    hB l yb yj ≤ 4012 ∧ hJ l yj ≤ 1650 ∧ hT l yj yt ≤ 550 := by
  cases l <;> simp only [hB, hJ, hT, Bool.cond_true, Bool.cond_false, mx_eq, mn_eq] <;> omega

theorem quad (S Bc Cc ρ0 ρ : ℕ) (h0 : ρ0 ≤ ρ) (h1 : Bc ≤ S * ρ0) (h2 : Bc * ρ0 + Cc ≤ S * (ρ0 * ρ0)) :
    Bc * ρ + Cc ≤ S * (ρ * ρ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h0
  have := Nat.mul_le_mul_right d h1
  nlinarith [Nat.zero_le (S * (d * d)), Nat.zero_le (S * ρ0 * d)]

theorem tail_ok (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (ρ cn vn a amax ρ0 : ℕ)
    (hρ0 : ρ0 ≤ ρ) (hρ1 : 0 < ρ0) (hcn : cn ≤ 2 * ρ) (hvn : vn * (ρ * ρ) ≤ VD * (amax * amax) + ρ * ρ)
    (ha : a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    {yb yj yt hb hj ht : ℕ} (a0 : yb ≤ 4012) (a1 : yj ≤ 1650) (a2 : yt ≤ 550)
    (b0 : hb ≤ 4012) (b1 : hj ≤ 1650) (b2 : ht ≤ 550) :
    LS G ρ cn vn yb yj yt hb hj ht ≤ G.sc * G.A * (2 * ρ * ρ * ρ) * VD := by
  have hP := hullP G.lift
  have m := LS_mono G hG hx ρ cn vn (yb := yb) (yj := yj) (yt := yt) (hb := hb) (hj := hj) (ht := ht)
    (yb' := 4012) (yj' := 1650) (yt' := 550) (hb' := 4012) (hj' := 1650) (ht' := 550) a0 a1 a2 b0 b1 b2
  refine m.trans ?_
  unfold LS
  rw [hP.1, hP.2.1, hP.2.2]
  set TPP := TT G 4012 1650 550 4012 1650 550
  set TXP := TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550
  have hρ : 0 < ρ := lt_of_lt_of_le hρ1 hρ0
  have e1 : (2 * ρ - cn) * VD * TPP ≤ 2 * ρ * VD * TPP := by
    have := Nat.sub_le (2 * ρ) cn; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  have e2 : cn * ρ * VD * TXP ≤ 2 * ρ * ρ * VD * TXP := by
    have : cn * ρ ≤ 2 * ρ * ρ := by nlinarith
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  have e3 : 2 * vn * ρ * ρ * ρ * G.tsep ≤ 2 * ρ * (VD * (amax * amax) + ρ * ρ) * G.tsep := by
    have : 2 * vn * ρ * ρ * ρ = 2 * ρ * (vn * (ρ * ρ)) := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hvn)
  have hamax : a * a ≤ amax * amax := Nat.mul_le_mul ha ha
  have key : 2 * VD * TXP * ρ + VD * (2 * TPP + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ * ρ) :=
    quad _ _ _ ρ0 ρ hρ0 hS1 hS2
  have hX : 2 * VD * TXP * ρ + VD * (2 * TPP + amax * amax * G.tsep) + G.tsep * (ρ * ρ) ≤
      G.sc * G.A * VD * (ρ * ρ) := by
    have h3 : (G.sc * G.A * VD - G.tsep) * (ρ * ρ) + G.tsep * (ρ * ρ) = G.sc * G.A * VD * (ρ * ρ) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hS0]
    linarith [key, h3]
  have h2 := Nat.mul_le_mul_left (2 * ρ) hX
  calc (2 * ρ - cn) * VD * TPP + 2 * ρ * VD * TPP + 2 * ρ * ρ * VD * TXP + cn * ρ * VD * TXP +
        2 * vn * ρ * ρ * ρ * G.tsep
      ≤ 2 * ρ * VD * TPP + 2 * ρ * VD * TPP + 2 * ρ * ρ * VD * TXP + 2 * ρ * ρ * VD * TXP +
        2 * ρ * (VD * (amax * amax) + ρ * ρ) * G.tsep := by
        linarith [e1, e2, e3]
    _ = 2 * ρ * (2 * VD * TXP * ρ + VD * (2 * TPP + amax * amax * G.tsep) + G.tsep * (ρ * ρ)) := by ring
    _ ≤ 2 * ρ * (G.sc * G.A * VD * (ρ * ρ)) := h2
    _ = G.sc * G.A * (2 * ρ * ρ * ρ) * VD := by ring

end Gate61Cell
