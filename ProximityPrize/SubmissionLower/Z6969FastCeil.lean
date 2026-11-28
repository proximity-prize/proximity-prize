import ProximityPrize.SubmissionLower.Z6969Pack0589
set_option Elab.async false
set_option autoImplicit false

namespace Research6969.JointRouted

theorem ordWeight_eq (d r : ℕ) (hd : d < 179730) :
    ordWeight d r =
      (((2 * 262144 * d * r * (179730 - d) + (262144 - d) * 179730 : ℕ)) + 179730 * (179730 - d) - 1) /
        (179730 * (179730 - d)) + 4 := by
  unfold ordWeight
  rw [show Fintype.card K1.I = 262144 from Fintype.card_fin (2^18)]
  unfold Research6969.MarkedAdaptive.price
  have hy : ((179730 - d : ℕ) : ℚ) ≠ 0 := by
    have : 0 < 179730 - d := by omega
    exact_mod_cast this.ne'
  have : (2 * ((262144 : ℕ) : ℚ) * d / (179730 : ℕ) * r + ((262144 - d : ℕ) : ℚ) / ((179730 - d : ℕ) : ℚ)) =
      ((2 * 262144 * d * r * (179730 - d) + (262144 - d) * 179730 : ℕ) : ℚ) / ((179730 * (179730 - d) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hpos : 0 < 179730 * (179730 - d) := Nat.mul_pos (by norm_num) (by omega)
  rw [this, natCeil_div _ _ hpos]

end Research6969.JointRouted

namespace Lower6960.Prefix6969Early
open Research6969

/-- `Exit.extra` with the two ceiling weights in closed Nat form.  Rewriting by this
lemma (instead of unfolding `Exit.extra` and letting the kernel evaluate `Nat.ceil` over
`Fintype.card K1.I`) avoids a 14 s kernel evaluation per use. -/
theorem extra_eq (x : Exit) (band : Prefix6969Main.Band) (rp : Prefix6969Rescue.EarlyPrice)
    (hd : 131071 + band.last < 179730) :
    x.extra band rp =
      if x.marked then
        (JointLedger.coefficient x.rDegree - rp.credit 1) * x.rWidth + 2 * x.rDegree ^ 2
      else
        (((2 * 262144 * (131071 + band.last) * rp.seed + 179730 - 1) / 179730 + 4) ^ 2 - rp.credit 0) * x.rDegree +
          (2 * ((2 * 262144 * (131071 + band.last) * rp.seed + 179730 - 1) / 179730 + 4) *
              ((((2 * 262144 * (131071 + band.last) * (rp.degree - 1) * (179730 - (131071 + band.last)) +
                  (262144 - (131071 + band.last)) * 179730 : ℕ)) + 179730 * (179730 - (131071 + band.last)) - 1) /
                (179730 * (179730 - (131071 + band.last))) + 4) - rp.credit 1) * x.rWidth := by
  unfold Exit.extra
  dsimp only
  rw [JointRouted.seedWeight_eq, JointRouted.ordWeight_eq _ _ hd]

end Lower6960.Prefix6969Early
