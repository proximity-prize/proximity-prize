import ProximityPrize.SubmissionLower.PortLowBase
import ProximityPrize.SubmissionLower.ModelExactPole

set_option maxHeartbeats 2000000

namespace Final50AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

def gradeLimit (t : ℕ) : ℕ :=
  if 55 < t then 110 else
  if t ≤ 33 then 132 else
  if t ≤ 34 then 131 else
  if t ≤ 35 then 130 else
  if t ≤ 36 then 129 else
  if t ≤ 37 then 128 else
  if t ≤ 38 then 127 else
  if t ≤ 39 then 126 else
  if t ≤ 40 then 125 else
  if t ≤ 41 then 124 else
  if t ≤ 42 then 123 else
  if t ≤ 43 then 122 else
  if t ≤ 44 then 121 else
  if t ≤ 45 then 120 else
  if t ≤ 46 then 119 else
  if t ≤ 47 then 118 else
  if t ≤ 48 then 117 else
  if t ≤ 49 then 116 else
  if t ≤ 50 then 115 else
  if t ≤ 51 then 114 else
  if t ≤ 52 then 113 else
  if t ≤ 53 then 112 else
  if t ≤ 54 then 111 else
  if t ≤ 55 then 110 else
  110

def cap (s : ℕ) : ℕ :=
  min s (min 55 (
  if s ≤ 110 then 55 else
  if s ≤ 111 then 54 else
  if s ≤ 112 then 53 else
  if s ≤ 113 then 52 else
  if s ≤ 114 then 51 else
  if s ≤ 115 then 50 else
  if s ≤ 116 then 49 else
  if s ≤ 117 then 48 else
  if s ≤ 118 then 47 else
  if s ≤ 119 then 46 else
  if s ≤ 120 then 45 else
  if s ≤ 121 then 44 else
  if s ≤ 122 then 43 else
  if s ≤ 123 then 42 else
  if s ≤ 124 then 41 else
  if s ≤ 125 then 40 else
  if s ≤ 126 then 39 else
  if s ≤ 127 then 38 else
  if s ≤ 128 then 37 else
  if s ≤ 129 then 36 else
  if s ≤ 130 then 35 else
  if s ≤ 131 then 34 else
  if s ≤ 132 then 33 else
  33))

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 55 := (min_le_right _ _).trans (min_le_left _ _)

private theorem gradeLimit_tail {t : ℕ} (ht : 55 < t) : gradeLimit t = 110 := by
  simp only [gradeLimit, if_pos ht]

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 56
  · have checks : ∀ t : Fin 56, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact checks ⟨n, hn⟩
  · rw [gradeLimit_tail (by omega), gradeLimit_tail (by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 55) (hts : t ≤ s) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  have hb : (List.range 56).all (fun i => decide (gradeLimit i ≤ 132)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp hb t (List.mem_range.mpr (by omega)))
  have checks : (List.range 133).all (fun s => (List.range 56).all
      (fun t => decide (t ≤ s → s ≤ gradeLimit t → t ≤ cap s))) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks s
    (List.mem_range.mpr (by omega))) t (List.mem_range.mpr (by omega)))) hts h

theorem cap_active (s : ℕ) (hs : s ≤ 132) : s + cap s ≤ 165 := by
  have checks : (List.range 133).all (fun g => decide (g + cap g ≤ 165)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 132 ∧ u.some.weight (fun i => i.val) ≤ 55 ∧ u (some 3) ≤ 14 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133484) ≤ 99 * 179886 - 1 + 55

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 99 x y).domRestrict _

end Final50AnchorSpace
