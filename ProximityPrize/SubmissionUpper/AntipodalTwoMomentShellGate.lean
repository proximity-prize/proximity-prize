/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Exact two-moment closure for even antipodal shells

This upper-only gate independently transcribes the mechanism published in Yukon note
`c8b6ede`.  If two orientations of the same antipodal pairs agree in their first and third
moments, their two difference sets have the form `(A, -A)`, and `A` has zero first and third
moment.  Equal product parity makes `|A|` even.

Deleting two elements `x,y` from `A` leaves their sum and cube sum.  A legal completion cannot
have `x+y=0`, since that would select both endpoints of one antipodal pair.  Otherwise

`x*y = ((x+y)^3 - (x^3+y^3)) / (3*(x+y))`,

so the missing unordered pair is unique.  The companion exact audit
`scripts/upper-antipodal-two-moment-shell-closure.py` applies the resulting double-counting cap
to every even shell from 8 through 128.  The unique closest shell is 44, and it reaches only
`0.7635729296049257...` of the score burden.

The scope is exact but narrow: this closes pairwise transversal differences whose partner is
global negation.  It neither asserts that isolated larger signed relations do not exist nor
covers a multipoint mixture with another partner map.  This is a research gate, not a score
claim.
-/

namespace ProximityPrize.SubmissionUpper.AntipodalTwoMomentShellGate

/-! ## Two-element reconstruction -/

variable {F : Type*} [Field F]

/-- The standard identity that recovers the product of two elements from their sum and cube
sum. -/
theorem three_mul_product_mul_sum
    (x y : F) :
    3 * (x * y) * (x + y) = (x + y) ^ 3 - (x ^ 3 + y ^ 3) := by
  ring

/-- In characteristic different from three, a nonzero common sum and a common cube sum force
the products of two candidate pairs to agree. -/
theorem product_eq_of_sum_and_cube_sum
    {x y u v : F} (hthree : (3 : F) ≠ 0)
    (hsum : x + y = u + v) (hcube : x ^ 3 + y ^ 3 = u ^ 3 + v ^ 3)
    (hsum0 : x + y ≠ 0) :
    x * y = u * v := by
  have hmul : 3 * (x + y) * (x * y - u * v) = 0 := by
    calc
      3 * (x + y) * (x * y - u * v) =
          (3 * (x * y) * (x + y)) - (3 * (u * v) * (u + v)) := by
            rw [← hsum]
            ring
      _ = ((x + y) ^ 3 - (x ^ 3 + y ^ 3)) -
          ((u + v) ^ 3 - (u ^ 3 + v ^ 3)) := by
            rw [three_mul_product_mul_sum, three_mul_product_mul_sum]
      _ = 0 := by rw [hsum, hcube]; ring
  rcases mul_eq_zero.mp hmul with hthreeSum | hproduct
  · exact False.elim <| hthree (by
      rcases mul_eq_zero.mp hthreeSum with h3 | hsum'
      · exact h3
      · exact False.elim (hsum0 hsum'))
  · exact sub_eq_zero.mp hproduct

/-- Equal sum and product determine an unordered pair over a field. -/
theorem unordered_pair_eq_of_sum_and_product
    {x y u v : F} (hsum : x + y = u + v) (hproduct : x * y = u * v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hfactor : (x - u) * (x - v) = 0 := by
    calc
      (x - u) * (x - v) = x ^ 2 - x * (u + v) + u * v := by ring
      _ = x ^ 2 - x * (x + y) + x * y := by rw [← hsum, ← hproduct]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfactor with hxu | hxv
  · left
    have hxu' : x = u := sub_eq_zero.mp hxu
    refine ⟨hxu', ?_⟩
    rw [← hxu'] at hsum
    exact add_left_cancel hsum
  · right
    have hxv' : x = v := sub_eq_zero.mp hxv
    refine ⟨hxv', ?_⟩
    rw [← hxv'] at hsum
    linear_combination hsum

/-- A legal signed pair cannot be antipodal.  Therefore its first and third moments determine
it uniquely as an unordered pair. -/
theorem legal_pair_unique_of_sum_and_cube_sum
    {x y u v : F} (hthree : (3 : F) ≠ 0)
    (hlegal : y ≠ -x) (hsum : x + y = u + v)
    (hcube : x ^ 3 + y ^ 3 = u ^ 3 + v ^ 3) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hsum0 : x + y ≠ 0 := by
    intro hzero
    apply hlegal
    linear_combination hzero
  exact unordered_pair_eq_of_sum_and_product hsum
    (product_eq_of_sum_and_cube_sum hthree hsum hcube hsum0)

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088

def shell22Cap : ℕ := 543156458900461232132369066
def shell22Requirement : ℕ := 4403094817684515647882783390192

def worstShell : ℕ := 44
def worstShellCap : ℕ :=
  52668289078603477677003399057983932494414586
def worstShellRequirement : ℕ :=
  68976108288509081018126446754842934848961816

theorem benchmark_characteristic_three_is_unit :
    baseFieldCardinality % 3 ≠ 0 := by
  norm_num [baseFieldCardinality]

/-- Exact shell-22 spot check from the public note. -/
theorem shell22_below_score_burden : shell22Cap < shell22Requirement := by
  norm_num [shell22Cap, shell22Requirement]

/-- The unique worst shell found by the exhaustive exact audit is still strictly below its
score-bearing requirement. -/
theorem worst_shell44_below_score_burden :
    worstShell = 44 ∧ worstShellCap < worstShellRequirement := by
  norm_num [worstShell, worstShellCap, worstShellRequirement]

/-- Rational enclosure of the worst exact ratio, avoiding any floating-point premise. -/
theorem worst_shell44_ratio_window :
    763572929 * worstShellRequirement < 1000000000 * worstShellCap ∧
      1000000000 * worstShellCap < 763572930 * worstShellRequirement := by
  norm_num [worstShellCap, worstShellRequirement]

end ProximityPrize.SubmissionUpper.AntipodalTwoMomentShellGate

#print axioms
  ProximityPrize.SubmissionUpper.AntipodalTwoMomentShellGate.three_mul_product_mul_sum
#print axioms
  ProximityPrize.SubmissionUpper.AntipodalTwoMomentShellGate.legal_pair_unique_of_sum_and_cube_sum
#print axioms
  ProximityPrize.SubmissionUpper.AntipodalTwoMomentShellGate.worst_shell44_below_score_burden
