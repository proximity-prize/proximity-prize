import ProximityPrize.SubmissionLower.PortLowBase
import ProximityPrize.SubmissionLower.ModelExactPole -- serialize candidate build

set_option maxHeartbeats 2000000

namespace Cutter53AnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The degree ceiling is the inverse of the differentiated-jet cap. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 32 then 129
  else if t ≤ 34 then 127
  else if t ≤ 36 then 125
  else if t ≤ 39 then 123
  else if t ≤ 41 then 121
  else if t ≤ 43 then 119
  else if t ≤ 45 then 117
  else if t ≤ 47 then 115
  else if t ≤ 49 then 113
  else if t ≤ 51 then 111
  else 109

def cap (s : ℕ) : ℕ :=
  min s (if s ≤ 109 then 53 else
    if s ≤ 111 then 51 else
    if s ≤ 113 then 49 else
    if s ≤ 115 then 47 else
    if s ≤ 117 then 45 else
    if s ≤ 119 then 43 else
    if s ≤ 121 then 41 else
    if s ≤ 123 then 39 else
    if s ≤ 125 then 36 else
    if s ≤ 127 then 34 else
    32)

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 53 :=
  by
  unfold cap
  apply (min_le_right _ _).trans
  split_ifs <;> decide

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 53
  · have steps : ∀ t : Fin 53, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact steps ⟨n, hn⟩
  · have h (t : ℕ) (ht : 53 ≤ t) : gradeLimit t = 109 := by
      unfold gradeLimit
      split_ifs <;> omega
    rw [h n (by omega), h (n+1) (by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 53) (hts : t ≤ s) (h : s ≤ gradeLimit t) :
    t ≤ cap s := by
  have hlo : ∀ i : Fin 54, gradeLimit i.val ≤ 129 := by decide +kernel
  have hs : s < 130 := Nat.lt_succ_of_le (h.trans (hlo ⟨t, Nat.lt_succ_of_le ht⟩))
  have hn : ∀ (i : Fin 130) (j : Fin 54),
      j.val ≤ i.val → i.val ≤ gradeLimit j.val → j.val ≤ cap i.val := by decide +kernel
  exact hn ⟨s, hs⟩ ⟨t, Nat.lt_succ_of_le ht⟩ hts h

theorem cap_active (s : ℕ) (hs : s ≤ 129) : s + cap s ≤ 162 := by
  have h : (List.range 130).all (fun g => decide (g + cap g ≤ 162)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 129 ∧ u.some.weight (fun i => i.val) ≤ 53 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133461) ≤ 96 * 179895 - 1 + 53

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 96 x y).domRestrict _

end Cutter53AnchorSpace
