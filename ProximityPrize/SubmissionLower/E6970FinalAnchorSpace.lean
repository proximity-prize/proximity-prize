import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace E6970FinalAnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

def gradeLimit (t : ℕ) : ℕ :=
  min 143 (179 - min 60 t)

def cap (s : ℕ) : ℕ :=
  min s (min 60 (179 - s))

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 60 := (min_le_right _ _).trans (min_le_left _ _)

theorem gradeLimit_antitone : Antitone gradeLimit := by
  intro a b h
  unfold gradeLimit
  exact min_le_min_left _ (Nat.sub_le_sub_left (min_le_min_left _ h) _)

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 60) (hts : t ≤ s) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  have hb : (List.range 61).all (fun i => decide (gradeLimit i ≤ 143)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp hb t (List.mem_range.mpr (by omega)))
  have checks : (List.range 144).all (fun s => (List.range 61).all
      (fun t => decide (t ≤ s → s ≤ gradeLimit t → t ≤ cap s))) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks s
    (List.mem_range.mpr (by omega))) t (List.mem_range.mpr (by omega)))) hts h

theorem cap_active (s : ℕ) (hs : s ≤ 143) : s + cap s ≤ 179 := by
  have checks : (List.range 144).all (fun g => decide (g + cap g ≤ 179)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 143 ∧ u.some.weight (fun i => i.val) ≤ 60 ∧ u (some 3) ≤ 16 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133378) ≤ 107 * 179730 - 1 + 60

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 107 x y).domRestrict _

end E6970FinalAnchorSpace
