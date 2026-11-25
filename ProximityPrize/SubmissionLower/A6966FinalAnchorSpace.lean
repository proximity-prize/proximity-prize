import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace A6966FinalAnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

def gradeLimit (t : ℕ) : ℕ :=
  if 58 < t then 120 else
  if t ≤ 36 then 142 else
  if t ≤ 37 then 141 else
  if t ≤ 38 then 140 else
  if t ≤ 39 then 139 else
  if t ≤ 40 then 138 else
  if t ≤ 41 then 137 else
  if t ≤ 42 then 136 else
  if t ≤ 43 then 135 else
  if t ≤ 44 then 134 else
  if t ≤ 45 then 133 else
  if t ≤ 46 then 132 else
  if t ≤ 47 then 131 else
  if t ≤ 48 then 130 else
  if t ≤ 49 then 129 else
  if t ≤ 50 then 128 else
  if t ≤ 51 then 127 else
  if t ≤ 52 then 126 else
  if t ≤ 53 then 125 else
  if t ≤ 54 then 124 else
  if t ≤ 55 then 123 else
  if t ≤ 56 then 122 else
  if t ≤ 57 then 121 else
  if t ≤ 58 then 120 else
  120

def cap (s : ℕ) : ℕ :=
  min s (min 58 (
  if s ≤ 120 then 58 else
  if s ≤ 121 then 57 else
  if s ≤ 122 then 56 else
  if s ≤ 123 then 55 else
  if s ≤ 124 then 54 else
  if s ≤ 125 then 53 else
  if s ≤ 126 then 52 else
  if s ≤ 127 then 51 else
  if s ≤ 128 then 50 else
  if s ≤ 129 then 49 else
  if s ≤ 130 then 48 else
  if s ≤ 131 then 47 else
  if s ≤ 132 then 46 else
  if s ≤ 133 then 45 else
  if s ≤ 134 then 44 else
  if s ≤ 135 then 43 else
  if s ≤ 136 then 42 else
  if s ≤ 137 then 41 else
  if s ≤ 138 then 40 else
  if s ≤ 139 then 39 else
  if s ≤ 140 then 38 else
  if s ≤ 141 then 37 else
  if s ≤ 142 then 36 else
  36))

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 58 := (min_le_right _ _).trans (min_le_left _ _)

private theorem gradeLimit_tail {t : ℕ} (ht : 58 < t) : gradeLimit t = 120 := by
  simp only [gradeLimit, if_pos ht]

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 59
  · have checks : ∀ t : Fin 59, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact checks ⟨n, hn⟩
  · rw [gradeLimit_tail (by omega), gradeLimit_tail (by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 58) (hts : t ≤ s) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  have hb : (List.range 59).all (fun i => decide (gradeLimit i ≤ 142)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp hb t (List.mem_range.mpr (by omega)))
  have checks : (List.range 143).all (fun s => (List.range 59).all
      (fun t => decide (t ≤ s → s ≤ gradeLimit t → t ≤ cap s))) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks s
    (List.mem_range.mpr (by omega))) t (List.mem_range.mpr (by omega)))) hts h

theorem cap_active (s : ℕ) (hs : s ≤ 142) : s + cap s ≤ 178 := by
  have checks : (List.range 143).all (fun g => decide (g + cap g ≤ 178)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 142 ∧ u.some.weight (fun i => i.val) ≤ 58 ∧ u (some 3) ≤ 15 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133484) ≤ 106 * 179808 - 1 + 58

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 106 x y).domRestrict _

end A6966FinalAnchorSpace
