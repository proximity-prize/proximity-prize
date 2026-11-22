import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Low53At2389AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The degree ceiling is the inverse of the differentiated-jet cap. -/
def gradeLimit (t : ℕ) : ℕ := min 129 (160 - min t 53)

def cap (s : ℕ) : ℕ := min s (min 53 (160 - min s 129))

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 53 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 53
  · have steps : ∀ t : Fin 53, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact steps ⟨n, hn⟩
  · unfold gradeLimit
    rw [min_eq_right (by omega : 53 ≤ n + 1), min_eq_right (by omega : 53 ≤ n)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 53) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have hlo : ∀ i : Fin 54, gradeLimit i.val ≤ 129 := by decide +kernel
  have hs : s < 130 := Nat.lt_succ_of_le (h.trans (hlo ⟨t, Nat.lt_succ_of_le ht⟩))
  have hn : ∀ (i : Fin 130) (j : Fin 54),
      j.val ≤ i.val → i.val ≤ gradeLimit j.val → j.val ≤ cap i.val := by decide +kernel
  exact hn ⟨s, hs⟩ ⟨t, Nat.lt_succ_of_le ht⟩ hts h

theorem cap_active (s : ℕ) (hs : s ≤ 129) : s + cap s ≤ 160 := by
  have h : (List.range 130).all (fun g => decide (g + cap g ≤ 160)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 129 ∧ u.some.weight (fun i => i.val) ≤ 53 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133460) ≤ 96 * 179896 - 1 + 53

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 96 x y).domRestrict _

end Low53At2389AnchorSpace
