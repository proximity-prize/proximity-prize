import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

theorem affine_sum_le_endpoint (u v T lo x hi : Nat)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hT : hi ≤ T) :
    u * x + v * (T - x) ≤
      max (u * lo + v * (T - lo)) (u * hi + v * (T - hi)) := by
  by_cases huv : v ≤ u
  · let d := u - v
    have hd : u = v + d := by dsimp only [d]; omega
    have form (s : Nat) (hs : s ≤ T) : u * s + v * (T - s) = d * s + v * T := by
      rw [hd, Nat.add_mul, Nat.add_comm (v * s) (d * s), Nat.add_assoc, ← Nat.mul_add]
      rw [show s + (T - s) = T by omega]
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    rw [form x (Nat.le_trans hhi hT), form hi hT]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hhi) _
  · let d := v - u
    have hd : v = u + d := by dsimp only [d]; omega
    have form (s : Nat) (hs : s ≤ T) : u * s + v * (T - s) = u * T + d * (T - s) := by
      rw [hd, Nat.add_mul, ← Nat.add_assoc, ← Nat.mul_add]
      rw [show s + (T - s) = T by omega]
    apply Nat.le_trans _ (Nat.le_max_left _ _)
    rw [form x (Nat.le_trans hhi hT), form lo (Nat.le_trans hlo (Nat.le_trans hhi hT))]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left d (Nat.sub_le_sub_left hlo T)) _

theorem scaled_affine_sum_le_endpoint (a b u v den₀ den₁ T lo x hi : Nat)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hT : hi ≤ T) :
    den₁ * (a + u * x) + den₀ * (b + v * (T - x)) ≤
      max
        (den₁ * (a + u * lo) + den₀ * (b + v * (T - lo)))
        (den₁ * (a + u * hi) + den₀ * (b + v * (T - hi))) := by
  have form (s : Nat) :
      den₁ * (a + u * s) + den₀ * (b + v * (T - s)) =
        den₁ * a + den₀ * b + ((den₁ * u) * s + (den₀ * v) * (T - s)) := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  rw [form x, form lo, form hi]
  rcases Nat.le_total ((den₁ * u) * lo + (den₀ * v) * (T - lo))
    ((den₁ * u) * hi + (den₀ * v) * (T - hi)) with h | h
  · exact Nat.le_trans
      (Nat.add_le_add_left (by
        simpa only [Nat.max_eq_right h] using
          affine_sum_le_endpoint (den₁ * u) (den₀ * v) T lo x hi hlo hhi hT) _)
      (Nat.le_max_right _ _)
  · exact Nat.le_trans
      (Nat.add_le_add_left (by
        simpa only [Nat.max_eq_left h] using
          affine_sum_le_endpoint (den₁ * u) (den₀ * v) T lo x hi hlo hhi hT) _)
      (Nat.le_max_left _ _)

end ProximityPrize.SubmissionLower.Koala6844Receipts
