import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! A finite subdivision certificate for all triples (p₂, W_F/wY, v). -/
namespace ProximityPrize.SubmissionBinaryLower.B6402RectCover
set_option autoImplicit false

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr,Inhabited
structure Box where
  p : Interval
  c : Interval
  v : Interval
  deriving Repr,Inhabited

def Interval.Holds (i : Interval) (x : ℚ) : Prop := (i.lo ≤ x) ∧ (x ≤ i.hi)
def Contains (B : Box) (p c v : ℚ) := B.p.Holds p ∧ B.c.Holds c ∧ B.v.Holds v

def leBox (a b : Box) : Bool :=
  decide (b.p.lo≤a.p.lo ∧ a.p.hi≤b.p.hi ∧ b.c.lo≤a.c.lo ∧ a.c.hi≤b.c.hi ∧ b.v.lo≤a.v.lo ∧ a.v.hi≤b.v.hi)

inductive Axis | p | c | v deriving Repr
inductive Subdivision
| leaf (index : ℕ)
| split (axis : Axis) (cut : ℚ) (lower upper : Subdivision)
deriving Repr

def cutBox (b : Box) (a : Axis) (k : ℚ) : Box × Box :=
  match a with
  | .p => (⟨⟨b.p.lo,k⟩,b.c,b.v⟩,⟨⟨k,b.p.hi⟩,b.c,b.v⟩)
  | .c => (⟨b.p,⟨b.c.lo,k⟩,b.v⟩,⟨b.p,⟨k,b.c.hi⟩,b.v⟩)
  | .v => (⟨b.p,b.c,⟨b.v.lo,k⟩⟩,⟨b.p,b.c,⟨k,b.v.hi⟩⟩)

def check (boxes : Array Box) (b : Box) : Subdivision → Bool
| .leaf i => if h : i<boxes.size then leBox b boxes[i] else false
| .split a k l r => check boxes (cutBox b a k).1 l && check boxes (cutBox b a k).2 r

theorem sound (boxes : Array Box) (b : Box) (t : Subdivision) (ok : check boxes b t=true)
    (p c v : ℚ) (atPoint : Contains b p c v) : ∃ i : Fin boxes.size, Contains boxes[i] p c v := by
  induction t generalizing b with
  | leaf i =>
    simp only [check] at ok
    split at ok
    next hi =>
      refine ⟨⟨i,hi⟩,?_⟩
      simp only [leBox,decide_eq_true_eq] at ok
      unfold Contains Interval.Holds at *
      exact ⟨⟨ok.1.trans atPoint.1.1,atPoint.1.2.trans ok.2.1⟩,
        ⟨ok.2.2.1.trans atPoint.2.1.1,atPoint.2.1.2.trans ok.2.2.2.1⟩,
        ⟨ok.2.2.2.2.1.trans atPoint.2.2.1,atPoint.2.2.2.trans ok.2.2.2.2.2⟩⟩
    next => contradiction
  | split a k l r hl hr =>
    simp only [check,Bool.and_eq_true] at ok
    have enclosed : Contains (cutBox b a k).1 p c v ∨ Contains (cutBox b a k).2 p c v := by
      rcases atPoint with ⟨h1,h2,h3⟩
      cases a with
      | p => rcases le_total p k with h|h; exact Or.inl ⟨⟨h1.1,h⟩,h2,h3⟩; exact Or.inr ⟨⟨h,h1.2⟩,h2,h3⟩
      | c => rcases le_total c k with h|h; exact Or.inl ⟨h1,⟨h2.1,h⟩,h3⟩; exact Or.inr ⟨h1,⟨h,h2.2⟩,h3⟩
      | v => rcases le_total v k with h|h; exact Or.inl ⟨h1,h2,⟨h3.1,h⟩⟩; exact Or.inr ⟨h1,h2,⟨h,h3.2⟩⟩
    rcases enclosed with h|h
    · exact hl _ ok.1 h
    · exact hr _ ok.2 h

#print axioms sound
end ProximityPrize.SubmissionBinaryLower.B6402RectCover
