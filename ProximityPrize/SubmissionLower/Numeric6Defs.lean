import ProximityPrize.SubmissionLower.Fast013
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast022
set_option Elab.async false

section PackSource_K1_13_2_3_6Defs
set_option autoImplicit true
namespace K1_13_2_3_6

open K1_13_2 K1_13_2_3
open scoped BigOperators

/-- A cubic for the four-factor denominator, with a single division. -/
private def fastDen (u : ℤ) : ℤ :=
  if u < 0 then 0 else (u * (u * (2 * u + 21) + 66) + 72) / 72

private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private theorem fastDen_eq (u : ℤ) : fastDen u = denominator u := by
  by_cases hu : u < 0
  · simp [fastDen, denominator, hu]
  simp only [fastDen, denominator, hu, ite_false]
  let q := u / 6
  let r := u % 6
  have hr : 0 ≤ r ∧ r < 6 := by dsimp [r]; omega
  have hu' : u = 6 * q + r := by dsimp [q, r]; omega
  have h₁ := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h₁
  let d := 1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
  change (u * (u * (2 * u + 21) + 66) + 72) / 72 = d
  have hpoly : u * (u * (2 * u + 21) + 66) + 72 =
      72 * d + r * (r * (2 * r - 15) + 30) := by
    rw [hu']
    dsimp only [d]
    linear_combination -36 * (h₁ + q * twice_half r + (57 + 6 * r) * twice_half q)
  rw [hpoly]
  have hc : 0 ≤ r * (r * (2 * r - 15) + 30) ∧
      r * (r * (2 * r - 15) + 30) < 72 := by
    obtain ⟨hr₀, hr₁⟩ := hr
    interval_cases r <;> norm_num
  omega

private def fastC (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    let a := fastDen v
    if v ≤ d then a else
      let x := v - d
      let b := a - fastDen (x - 1) - fastDen (x - 2) - fastDen (x - 3)
      if x ≤ d + 2 then b else
        let y := x - d
        b + fastDen (y - 3) + fastDen (y - 4) + fastDen (y - 5)

private theorem fastC_eq (d u : ℤ) : fastC d u = cumulative d u := by
  unfold fastC cumulative
  split
  · rfl
  rename_i h
  simp only [fastDen_eq]
  have hden (x : ℤ) (hx : x < 0) : denominator x = 0 := by simp [denominator, hx]
  have hv : min u (3 * d) ≤ 3 * d := min_le_right _ _
  by_cases h₁ : min u (3 * d) ≤ d
  · simp (disch := omega) only [h₁, ite_true, hden, sub_zero, add_zero]
  · simp only [h₁, ite_false]
    rw [show min u (3 * d) - d - d = min u (3 * d) - 2 * d by ring]
    by_cases h₂ : min u (3 * d) - d ≤ d + 2
    · simp (disch := omega) only [h₂, ite_true, hden, add_zero, sub_zero]
    · simp (disch := omega) only [h₂, ite_false, hden, sub_zero]

/-- The old-index upper bound is three times the cap for each retained factor. -/
private def fastOld (d lower cap : ℤ) : ℤ :=
  fastC d (3 * cap) - fastC d (min (3 * cap) (lower - 1))

private theorem fastOld_eq (d lower cap order : ℤ) (hc : 0 ≤ cap) :
    fastOld d lower cap = oldCount ⟨d, lower, 3 * cap, cap, order⟩ := by
  simp only [fastOld, fastC_eq, oldCount, cappedCount, not_lt.mpr hc, ite_false]
  have hz (u : ℤ) (h : u ≤ 3 * cap) :
      cumulative (d - cap - 1) (u - 3 * (cap + 1)) = 0 := by
    have hu : u - 3 * (cap + 1) < 0 := by omega
    simp [cumulative, hu]
  rw [hz _ le_rfl, hz _ (min_le_left _ _), sub_zero, sub_zero]

private def fastKernel (d lower cap order : ℤ) : ℤ :=
  if d < 0 || cap < 0 then 0 else
    let a := fastOld d lower cap
    let balance := order - 1 - lower + d
    if balance < 0 then a else
      let removed := min d (balance / 4) + 1
      let hi := fastC d (3 * cap)
      let adj := if lower - 1 ≤ 3 * cap then hi else a + fastC d (lower - 1)
      adj - fastC d (order - 1) +
        fastC (d - removed) (order - 1 - 3 * removed) - fastC (d - removed) (lower - 1)

private theorem fastKernel_eq (d lower cap order : ℤ) :
    fastKernel d lower cap order = kernelLower ⟨d, lower, 3 * cap, cap, order⟩ := by
  by_cases hd : d < 0
  · simp [fastKernel, kernelLower, hd]
  by_cases hc : cap < 0
  · simp [fastKernel, kernelLower, hc]
  have hu : ¬ 3 * cap < 0 := by omega
  simp only [fastKernel, kernelLower, targetCount, hd, hc, hu, decide_false, Bool.or_false,
    Bool.false_eq_true, ite_false]
  rw [← fastOld_eq _ _ _ _ (by omega)]
  by_cases hb : order - 1 - lower + d < 0
  · simp [hb]
  simp only [hb, ite_false, fastOld, fastC_eq]
  by_cases h : lower - 1 ≤ 3 * cap
  · simp only [h, ite_true, min_eq_right h]
    ring
  · simp only [h, ite_false]
    ring

/-- Common old count and the two signed lower bounds. -/
def blockSaving (s j : ℕ) (p : Powers) : ℕ :=
  let lower : ℤ := 1650 - j
  let order : ℤ := 4650 - s - j
  let old := fastOld 1650 lower 550
  let initial := max 0 (fastKernel 1650 lower 550 order)
  let residual := fastKernel (1650 - (p.value + (p.top : ℤ) + 3 * p.cubic))
    (lower - (3 * (p.top : ℤ) + 2 * p.cubic)) (550 - (p.top + (p.cubic : ℤ)))
    (order - (2 * (p.top : ℤ) + 3 * p.cubic))
  (old - initial).toNat - (old - max initial residual).toNat

theorem blockSaving_eq (i : BlockIndex) (p : Powers) (hw : w3.Contains i) :
    blockSaving i.1.val i.2.val p = savings i p := by
  rcases hw with ⟨hs, _, _, hj, _, hsum⟩
  change 3012 ≤ i.1.val at hs
  change i.2.val ≤ 408 at hj
  change i.1.val + i.2.val ≤ 3796 at hsum
  have hd : min (i.1.val : ℤ) 1650 = 1650 := min_eq_right (by omega)
  have hu : min (1650 : ℤ) (2999 - offset i) = 1650 := by
    unfold offset
    apply min_eq_left
    omega
  have ho : 0 < (4650 : ℤ) - i.1.val - i.2.val := by omega
  have hi : initialFlag i = ⟨1650, 1650 - (i.2.val : ℤ), 1650, 550,
      4650 - (i.1.val : ℤ) - i.2.val⟩ := by
    unfold initialFlag offset
    rw [hd]
    congr 1 <;> ring
  have hz : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases h : initialFlag i
    simp [residualFlag]
  unfold savings baseline blockBound blockSaving
  dsimp only
  rw [hz, hi]
  simp only [hu,
    not_le.mpr ho, ite_false, max_self, ← max_assoc]
  have hmin (a b : ℤ) (hb : 0 ≤ b) : min a (a - b) = a - b := min_eq_right (by omega)
  rw [hmin _ _ (le_max_left _ _), hmin _ _ ((le_max_left _ _).trans (le_max_left _ _))]
  rw [residualFlag_expand]
  rw [fastOld_eq _ _ _ (4650 - (i.1.val : ℤ) - i.2.val) (by decide), fastKernel_eq,
    fastKernel_eq]
  rw [show 3 * (550 - ((p.top : ℤ) + p.cubic)) =
    1650 - (3 * (p.top : ℤ) + 3 * p.cubic) by ring, show (3 : ℤ) * 550 = 1650 by decide]

/-- Window-free form of `blockSaving_eq`: only the three inequalities used by its proof.
(Added for the 6916 w4 top-factor certificate; the proof is the official one verbatim.) -/
theorem blockSaving_eq_of (i : BlockIndex) (p : Powers) (hs : 1650 ≤ i.1.val)
    (hj : i.2.val ≤ 2999) (hsum : i.1.val + i.2.val < 4650) :
    blockSaving i.1.val i.2.val p = savings i p := by
  have hd : min (i.1.val : ℤ) 1650 = 1650 := min_eq_right (by omega)
  have hu : min (1650 : ℤ) (2999 - offset i) = 1650 := by
    unfold offset
    apply min_eq_left
    omega
  have ho : 0 < (4650 : ℤ) - i.1.val - i.2.val := by omega
  have hi : initialFlag i = ⟨1650, 1650 - (i.2.val : ℤ), 1650, 550,
      4650 - (i.1.val : ℤ) - i.2.val⟩ := by
    unfold initialFlag offset
    rw [hd]
    congr 1 <;> ring
  have hz : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases h : initialFlag i
    simp [residualFlag]
  unfold savings baseline blockBound blockSaving
  dsimp only
  rw [hz, hi]
  simp only [hu,
    not_le.mpr ho, ite_false, max_self, ← max_assoc]
  have hmin (a b : ℤ) (hb : 0 ≤ b) : min a (a - b) = a - b := min_eq_right (by omega)
  rw [hmin _ _ (le_max_left _ _), hmin _ _ ((le_max_left _ _).trans (le_max_left _ _))]
  rw [residualFlag_expand]
  rw [fastOld_eq _ _ _ (4650 - (i.1.val : ℤ) - i.2.val) (by decide), fastKernel_eq,
    fastKernel_eq]
  rw [show 3 * (550 - ((p.top : ℤ) + p.cubic)) =
    1650 - (3 * (p.top : ℤ) + 3 * p.cubic) by ring, show (3 : ℤ) * 550 = 1650 by decide]


theorem blockSaving_zero (s j : ℕ) : blockSaving s j ⟨0, 0, 0⟩ = 0 := by
  simp [blockSaving]

end K1_13_2_3_6
end PackSource_K1_13_2_3_6Defs
