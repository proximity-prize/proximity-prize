import ProximityPrize.SubmissionBinaryLower.Binary6402Table4K
import ProximityPrize.SubmissionBinaryLower.B6401T4Grid

/-! The 237 published Table 4 parameter regions are independent of the
choice of surplus witness. A cover selects a region in one of the five
gap intervals, or the single interval that covers all gaps. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402GridProfile
open B6402T4Rows B6402IntFarkas
set_option autoImplicit false
abbrev Branch := Sum T4ABranch T4BBranch
structure Key where
  branch : Branch
  cLoNum : ℕ
  cLoDen : ℕ
  cHiNum : ℕ
  cHiDen : ℕ
  gap : ℕ×ℕ×ℕ×ℕ
  deriving DecidableEq

def lo (k : Key) : ℚ := k.cLoNum/k.cLoDen
def hi (k : Key) : ℚ := k.cHiNum/k.cHiDen
def single : ℕ×ℕ×ℕ×ℕ := (0,1,1,1)
def coversGap (k : Key) (r : Fin 5) : Prop := k.gap=B6401T4Grid.std5Bounds r ∨ k.gap=single

instance (k : Key) (r : Fin 5) : Decidable (coversGap k r) := inferInstanceAs (Decidable (_ ∨ _))

def covered {n : ℕ} (key : Fin n → Key) (tag : Branch) (r : Fin 5) (finish : ℚ) :
    (current : ℚ) → List (Fin n) → Bool
  | t, [] => decide (finish≤t)
  | t, i::is => decide ((key i).branch=tag ∧ coversGap (key i) r ∧
      0<(key i).cLoDen ∧ 0<(key i).cHiDen ∧ lo (key i)≤t ∧ t≤hi (key i)) &&
      covered key tag r finish (hi (key i)) is

theorem sound {n : ℕ} (key : Fin n → Key) (tag : Branch) (r : Fin 5) (finish start c : ℚ)
    (ids : List (Fin n)) (h : covered key tag r finish start ids=true) (valid : c≤finish) (inRange : start<c) :
    ∃ i : Fin n,(key i).branch=tag ∧ coversGap (key i) r ∧ 0<(key i).cLoDen ∧ 0<(key i).cHiDen ∧
      lo (key i)≤c ∧ c≤hi (key i) := by
  induction ids generalizing start with
  | nil => simp only [covered,decide_eq_true_eq] at h; linarith
  | cons i ids ih =>
    simp only [covered,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases hit : c≤hi (key i)
    · exact ⟨i,h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2.1,h.1.2.2.2.2.1.trans inRange.le,hit⟩
    · exact ih (hi (key i)) h.2 (lt_of_not_ge hit)

/-- Closed left endpoint is important at W_F = 5wY-1. -/
theorem closed_sound {n : ℕ} (key : Fin n → Key) (tag : Branch) (r : Fin 5) (finish start c : ℚ)
    (i : Fin n) (rest : List (Fin n)) (h : covered key tag r finish start (i::rest)=true) (valid : c≤finish) (inRange : start≤c) :
    ∃ j : Fin n,(key j).branch=tag ∧ coversGap (key j) r ∧ 0<(key j).cLoDen ∧ 0<(key j).cHiDen ∧
      lo (key j)≤c ∧ c≤hi (key j) := by
  by_cases hlt : start<c
  · exact sound key tag r finish start c _ h valid hlt
  · simp only [covered,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨i,h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2.1,h.1.2.2.2.2.1.trans inRange,
      (le_of_not_gt hlt).trans h.1.2.2.2.2.2⟩

#print axioms closed_sound
end ProximityPrize.SubmissionBinaryLower.B6402GridProfile
