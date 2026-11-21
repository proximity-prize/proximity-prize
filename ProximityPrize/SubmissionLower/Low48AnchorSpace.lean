import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Low48AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Inverse grade ceiling for an antitone differentiated-jet profile. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 30 then 122
  else if t ≤ 32 then 120
  else if t ≤ 34 then 118
  else if t ≤ 36 then 116
  else if t ≤ 38 then 114
  else if t ≤ 40 then 112
  else if t ≤ 42 then 110
  else if t ≤ 44 then 108
  else if t ≤ 46 then 106
  else if t ≤ 47 then 105
  else if t ≤ 48 then 104
  else if t ≤ 49 then 103
  else 102

def cap (s : ℕ) : ℕ :=
  min s (if s < 103 then 50 else
    if s < 104 then 49 else
    if s < 105 then 48 else
    if s < 106 then 47 else
    if s < 107 then 46 else
    if s < 109 then 44 else
    if s < 111 then 42 else
    if s < 113 then 40 else
    if s < 115 then 38 else
    if s < 117 then 36 else
    if s < 119 then 34 else
    if s < 121 then 32 else
    30)

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 50 := by
  unfold cap
  apply (min_le_right _ _).trans
  split_ifs <;> decide

private theorem gradeLimit_tail {t : ℕ} (ht : 50 ≤ t) : gradeLimit t = 102 := by
  unfold gradeLimit
  split_ifs <;> omega

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 50
  · have steps : ∀ t : Fin 50, gradeLimit (t.val + 1) ≤ gradeLimit t.val := by decide +kernel
    exact steps ⟨n, hn⟩
  · rw [gradeLimit_tail (by omega : 50 ≤ n), gradeLimit_tail (by omega : 50 ≤ n+1)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 50) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have htop : gradeLimit t ≤ 122 := by
    unfold gradeLimit
    split_ifs <;> decide
  have hs : s < 123 := Nat.lt_succ_of_le (h.trans htop)
  have checked : ∀ (s : Fin 123) (t : Fin 51),
      t.val ≤ s.val → s.val ≤ gradeLimit t.val → t.val ≤ cap s.val := by decide +kernel
  exact checked ⟨s, hs⟩ ⟨t, Nat.lt_succ_of_le ht⟩ hts h

theorem cap_active (s : ℕ) (hs : s ≤ 122) : s + cap s ≤ 152 := by
  have h : (List.range 123).all (fun g => decide (g + cap g ≤ 152)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 122 ∧ u.some.weight (fun i => i.val) ≤ 50 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133424) ≤ 91 * 179915 - 1 + 50

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 91 x y).domRestrict _

end Low48AnchorSpace
