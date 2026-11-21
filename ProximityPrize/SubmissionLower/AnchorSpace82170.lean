import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace AnchorSpace82170
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/-- Largest total jet degree allowed for a monomial with t differentiated factors. -/
def gradeLimit (t : ℕ) : ℕ :=
  if t ≤ 30 then 120 else if t ≤ 33 then 119 else if t ≤ 35 then 117
  else if t ≤ 37 then 115 else if t ≤ 39 then 113 else if t ≤ 41 then 111
  else if t ≤ 43 then 109 else if t ≤ 45 then 107 else if t ≤ 46 then 106
  else if t ≤ 47 then 105 else 103

/-- Largest number of differentiated factors at total jet degree s. -/
def cap (s : ℕ) : ℕ :=
  if s ≤ 103 then 48 else if s ≤ 105 then 47 else if s ≤ 106 then 46
  else if s ≤ 107 then 45 else if s ≤ 109 then 43 else if s ≤ 111 then 41
  else if s ≤ 113 then 39 else if s ≤ 115 then 37 else if s ≤ 117 then 35
  else if s ≤ 119 then 33 else 30

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 48) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  unfold gradeLimit at h
  unfold cap
  split_ifs at * <;> omega

theorem gradeLimit_antitone : Antitone gradeLimit := by
  intro a b h
  unfold gradeLimit
  split_ifs <;> omega

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧ u.some.weight (fun i => i.val) ≤ 48 ∧ u (some 3) ≤ 10 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133367) ≤ 90 * 179974 - 1

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 x y).domRestrict _

end AnchorSpace82170
