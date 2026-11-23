import ProximityPrize.SubmissionLower.R6960CubicJump

/-! Whole-family arithmetic for the normalized-cover paper proof. -/
namespace Lower6960.CoverBudget

def triangular (f : ℕ) := f*(f-1)/2

def rate (e : ℕ) :=
  triangular e + 2*e-1 + (8*triangular e+e+1)*(e-1)

def constantCurveRate (e f : ℕ) :=
  2*e-1 + triangular f + (9*triangular f-f+4)*(e-1)

/-- The constant-field reduction cannot exceed the displayed primitive rate
in the profile range. The table is only 45 by 24. -/
theorem table :
    ∀ e : Fin 48, 3≤e.val →
      (12*e.val≤rate e.val) ∧
      (rate e.val≤31000 ↔ e.val≤20) ∧
      ∀ f : Fin 24, 2≤f.val → 2*f.val≤e.val →
        constantCurveRate e.val f.val≤rate e.val := by decide +kernel

theorem matched_shallow_uniform :
    (rate 18)*(2400*2130706433) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_four :
    rate 24*(2400+2130706433*1119) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_five :
    266695718139456639 <
      rate 25*(2400+2130706433*1029) + 48 + 143456202788540 + 143313454876987920 := by decide +kernel

#print axioms table
#print axioms grade_twenty_four
end Lower6960.CoverBudget
