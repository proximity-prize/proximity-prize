import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

/-! The weighted-box sharpening lemmas for the 6735 retune.

The box membership condition for every cell in the two-tail tree is
`d ∈ globalExponents D w L s`:

    d 1 + d 2 + d 3 ≤ L ∧ d 2 ≤ s ∧ d 0 + w * d 1 + (w - 1) * d 2 < D

with `D = multiplicity * agreements`.  The frontier proof only used the crude
per-coordinate budgets (y ≤ L, r ≤ s, z ≤ L); these lemmas extract the sharp
budgets the weighted condition actually implies, which is what the retune needs
to keep the fixed cell inside the MCA budget. -/

namespace ProximityPrize.SubmissionLower.ContactWeightedDegreeSharpening6735Research
open ContactFlagInterpolation6641Research

/-- Every box member has y-degree at most `(D-1)/w`. -/
theorem globalExponents_y_le_weighted (D w L s : ℕ) (hw : 0 < w)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ globalExponents D w L s) :
    d 1 ≤ (D-1)/w := by
  have hwt : d 0 + w * d 1 + (w - 1) * d 2 < D := hd.2.2
  have hle : w * d 1 ≤ d 0 + w * d 1 + (w - 1) * d 2 := by omega
  have hltD : w * d 1 < D := lt_of_le_of_lt hle hwt
  have hleD : w * d 1 ≤ D - 1 := Nat.le_sub_one_of_lt hltD
  have hleD' : d 1 * w ≤ D - 1 := by simpa [Nat.mul_comm] using hleD
  exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (by omega))).mpr hleD'

/-- The target fixed-cell constants: `(41*182032-1)/131071 = 56`. -/
theorem fixed_yCap_exact : (41*182032-1)/131071 = 56 := by decide

/-- In the retuned fixed-cell box, `y + r ≤ 56` — the sharpened `ys` budget
(the frontier proof only had `y + r ≤ 56` via `(D+s-1)/w`; this is the form
`hYR` needs: weights `[0,1,1,0]`). -/
theorem fixedBox_y_plus_r_le {d : Fin 4 →₀ ℕ}
    (hd : d ∈ globalExponents (41*182032) 131071 10000 12) :
    d 1 + d 2 ≤ 56 := by
  have hwt : d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 41 * 182032 := hd.2.2
  have hs : d 2 ≤ 12 := hd.2.1
  have hcomb : 131071 * (d 1 + d 2) ≤ d 0 + 131071 * d 1 + (131071 - 1) * d 2 + 12 := by omega
  have hwt' : d 0 + 131071 * d 1 + (131071 - 1) * d 2 + 12 < 41 * 182032 + 12 := by omega
  have hlt : 131071 * (d 1 + d 2) < 41 * 182032 + 12 := lt_of_le_of_lt hcomb hwt'
  omega

/-- In the retuned fixed-cell box, the total `y + r + z` budget is the box's
`L` — nothing sharper follows from the weighted condition alone, so the
z-slack must come from the meet polynomial's own z-degree (coordinate 3). -/
theorem fixedBox_total_le {d : Fin 4 →₀ ℕ}
    (hd : d ∈ globalExponents (41*182032) 131071 10000 12) :
    d 1 + d 2 + d 3 ≤ 10000 := hd.1

/-- Sanity: the box y-budget sharpening is strict — crude `y ≤ L = 10000`
is replaced by `y ≤ 56`, and that is the only load-bearing cut. -/
theorem fixed_y_sharp : (∀ {d : Fin 4 →₀ ℕ},
    d ∈ globalExponents (41*182032) 131071 10000 12 → d 1 ≤ 56) := by
  intro d hd
  have hy := globalExponents_y_le_weighted (41*182032) 131071 10000 12 (by decide) hd
  simpa only [fixed_yCap_exact] using hy

end ProximityPrize.SubmissionLower.ContactWeightedDegreeSharpening6735Research
