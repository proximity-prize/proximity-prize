import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

namespace Low48AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The total jet degree limit for a fixed number of differentiated factors. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 30 then 121 else if t ≤ 32 then 119 else if t ≤ 34 then 117
  else if t ≤ 36 then 115 else if t ≤ 39 then 113 else if t ≤ 41 then 111
  else if t ≤ 43 then 109 else if t ≤ 45 then 107 else if t ≤ 47 then 105
  else 103

/-- The differentiated factor limit at total jet degree `s`. -/
def cap (s : ℕ) : ℕ :=
  min s (if s ≤ 103 then 49 else if s ≤ 105 then 47 else if s ≤ 107 then 45
    else if s ≤ 109 then 43 else if s ≤ 111 then 41 else if s ≤ 113 then 39
    else if s ≤ 115 then 36 else if s ≤ 117 then 34 else if s ≤ 119 then 32
    else 30)

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 49 := by
  unfold cap
  apply (min_le_right _ _).trans
  split_ifs <;> decide

private theorem gradeLimit_tail {t : ℕ} (ht : 47 < t) : gradeLimit t = 103 := by
  unfold gradeLimit
  split_ifs <;> omega

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 48
  · have steps : ∀ t : Fin 48, gradeLimit (t.val + 1) ≤ gradeLimit t.val := by decide +kernel
    exact steps ⟨n, hn⟩
  · rw [gradeLimit_tail (show 47 < n by omega), gradeLimit_tail (show 47 < n+1 by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 49) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have limit {n : ℕ} (hn : gradeLimit (n + 1) < s) : t ≤ n := by
    by_contra! hbad
    exact (not_le_of_gt hn) (h.trans (gradeLimit_antitone (show n + 1 ≤ t by omega)))
  unfold cap
  apply le_min hts
  split_ifs
  · exact ht
  · apply limit; change 103 < s; omega
  · apply limit; change 105 < s; omega
  · apply limit; change 107 < s; omega
  · apply limit; change 109 < s; omega
  · apply limit; change 111 < s; omega
  · apply limit; change 113 < s; omega
  · apply limit; change 115 < s; omega
  · apply limit; change 117 < s; omega
  · apply limit; change 119 < s; omega

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 121 ∧ u.some.weight (fun i => i.val) ≤ 49 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133426) ≤ 90 * 179935 - 1

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 x y).domRestrict _

end Low48AnchorSpace
