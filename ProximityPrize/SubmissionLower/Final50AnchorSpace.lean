import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Final50AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Inverse grade ceiling for an antitone differentiated-jet profile. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 31 then 125 else if t ≤ 33 then 123 else if t ≤ 35 then 121 else
  if t ≤ 37 then 119 else if t ≤ 40 then 117 else if t ≤ 42 then 115 else
  if t ≤ 44 then 113 else if t ≤ 46 then 111 else if t ≤ 48 then 109 else
  if t ≤ 50 then 107 else 105

def cap (s : ℕ) : ℕ :=
  min s (if s ≤ 105 then 52 else if s ≤ 107 then 50 else if s ≤ 109 then 48 else
    if s ≤ 111 then 46 else if s ≤ 113 then 44 else if s ≤ 115 then 42 else
    if s ≤ 117 then 40 else if s ≤ 119 then 37 else if s ≤ 121 then 35 else
    if s ≤ 123 then 33 else 31)

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 52 := by
  unfold cap
  apply (min_le_right _ _).trans
  split_ifs <;> decide

private theorem gradeLimit_tail {t : ℕ} (ht : 50 < t) : gradeLimit t = 105 := by
  unfold gradeLimit
  split_ifs <;> omega

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 51
  · have steps : ∀ t : Fin 51, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact steps ⟨n, hn⟩
  · rw [gradeLimit_tail (show 50 < n by omega), gradeLimit_tail (show 50 < n+1 by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 52) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have limit {n : ℕ} (hn : gradeLimit (n + 1) < s) : t ≤ n := by
    by_contra! hbad
    exact (not_le_of_gt hn) (h.trans (gradeLimit_antitone (show n + 1 ≤ t by omega)))
  unfold cap
  apply le_min hts
  split_ifs
  · exact ht
  · apply limit; change 105 < s; omega
  · apply limit; change 107 < s; omega
  · apply limit; change 109 < s; omega
  · apply limit; change 111 < s; omega
  · apply limit; change 113 < s; omega
  · apply limit; change 115 < s; omega
  · apply limit; change 117 < s; omega
  · apply limit; change 119 < s; omega
  · apply limit; change 121 < s; omega
  · apply limit; change 123 < s; omega

theorem cap_active (s : ℕ) (hs : s ≤ 125) : s + cap s ≤ 157 := by
  have h : (List.range 126).all (fun g => decide (g + cap g ≤ 157)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 125 ∧ u.some.weight (fun i => i.val) ≤ 52 ∧ u (some 3) ≤ 14 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133475) ≤ 93 * 179925 - 1 + 52

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 93 x y).domRestrict _

end Final50AnchorSpace
