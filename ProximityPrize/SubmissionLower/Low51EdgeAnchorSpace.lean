import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Low51EdgeAnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Inverse grade ceiling for an antitone differentiated-jet profile. -/
def gradeLimitWithin (t : ℕ) : ℕ :=
  if t ≤ 31 then 126 else
  if t ≤ 33 then 124 else
  if t ≤ 35 then 122 else
  if t ≤ 37 then 120 else
  if t ≤ 39 then 118 else
  if t ≤ 41 then 116 else
  if t ≤ 43 then 114 else
  if t ≤ 45 then 112 else
  if t ≤ 47 then 110 else
  if t ≤ 48 then 109 else
  if t ≤ 49 then 108 else
  if t ≤ 50 then 107 else
  if t ≤ 51 then 106 else
  if t ≤ 52 then 105 else
  104

def capWithin (s : ℕ) : ℕ :=
  if s ≤ 104 then 53 else
  if s ≤ 105 then 52 else
  if s ≤ 106 then 51 else
  if s ≤ 107 then 50 else
  if s ≤ 108 then 49 else
  if s ≤ 109 then 48 else
  if s ≤ 110 then 47 else
  if s ≤ 112 then 45 else
  if s ≤ 114 then 43 else
  if s ≤ 116 then 41 else
  if s ≤ 118 then 39 else
  if s ≤ 120 then 37 else
  if s ≤ 122 then 35 else
  if s ≤ 124 then 33 else
  31

def gradeLimit (t : ℕ) : ℕ := gradeLimitWithin (min t 53)

def cap (s : ℕ) : ℕ := min s (capWithin (min s 126))

theorem cap_le_index (s : ℕ) : cap s ≤ 53 := by
  have h : ∀ t : Fin 127, capWithin t.val ≤ 53 := by decide +kernel
  exact (min_le_right _ _).trans (h ⟨min s 126, Nat.lt_succ_of_le (min_le_right _ _)⟩)

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 126 ∧ u.some.weight (fun i => i.val) ≤ 53 ∧ u (some 3) ≤ 13 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133472) ≤ 94 * 179915 - 1 + 53

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 94 x y).domRestrict _

end Low51EdgeAnchorSpace
