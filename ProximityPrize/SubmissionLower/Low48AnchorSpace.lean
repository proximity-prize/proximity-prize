import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

namespace Low48AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The total jet degree limit for a fixed number of differentiated factors. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 31 then 123
  else if t ≤ 33 then 122
  else if t ≤ 35 then 120
  else if t ≤ 37 then 118
  else if t ≤ 39 then 116
  else if t ≤ 41 then 114
  else if t ≤ 43 then 112
  else if t ≤ 45 then 110
  else if t ≤ 47 then 108
  else if t ≤ 49 then 106
  else 104

/-- The differentiated factor limit at total jet degree `s`. -/
def cap (s : ℕ) : ℕ :=
  min s (if s ≤ 104 then 50
  else if s ≤ 106 then 49
  else if s ≤ 108 then 47
  else if s ≤ 110 then 45
  else if s ≤ 112 then 43
  else if s ≤ 114 then 41
  else if s ≤ 116 then 39
  else if s ≤ 118 then 37
  else if s ≤ 120 then 35
  else if s ≤ 122 then 33
  else 31)

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 50 := by
  unfold cap
  apply (min_le_right _ _).trans
  split_ifs <;> decide

private theorem gradeLimit_tail {t : ℕ} (ht : 49 < t) : gradeLimit t = 104 := by
  unfold gradeLimit
  split_ifs <;> omega

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 50
  · have steps : ∀ t : Fin 50, gradeLimit (t.val + 1) ≤ gradeLimit t.val := by decide +kernel
    exact steps ⟨n, hn⟩
  · rw [gradeLimit_tail (show 49 < n by omega), gradeLimit_tail (show 49 < n+1 by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 50) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have limit {n : ℕ} (hn : gradeLimit (n + 1) < s) : t ≤ n := by
    by_contra! hbad
    exact (not_le_of_gt hn) (h.trans (gradeLimit_antitone (show n + 1 ≤ t by omega)))
  unfold cap
  apply le_min hts
  split_ifs
  · exact ht
  · apply limit; change 104 < s; omega
  · apply limit; change 106 < s; omega
  · apply limit; change 108 < s; omega
  · apply limit; change 110 < s; omega
  · apply limit; change 112 < s; omega
  · apply limit; change 114 < s; omega
  · apply limit; change 116 < s; omega
  · apply limit; change 118 < s; omega
  · apply limit; change 120 < s; omega
  · apply limit; change 122 < s; omega

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 123 ∧ u.some.weight (fun i => i.val) ≤ 50 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133426) ≤ 92 * 179915 + 50 - 1

def SourceEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 123 ∧ u.some.weight (fun i => i.val) ≤ 50 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133426) ≤ 92 * 179915 + u.some.weight (fun i => i.val) - 1

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 92 x y).domRestrict _

end Low48AnchorSpace
