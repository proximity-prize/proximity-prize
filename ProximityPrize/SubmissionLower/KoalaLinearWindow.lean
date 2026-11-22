import ProximityPrize.SubmissionLower.KoalaPiecewiseTriangle
import ProximityPrize.SubmissionLower.Low48PrimaryPivotAggregate

set_option autoImplicit false

namespace KoalaLinearWindow
open Finset KoalaPiecewiseTriangle

structure Span where
  lo : ℤ
  hi : ℤ

def Span.finset (s : Span) : Finset ℤ := Ico s.lo s.hi

def Span.keep (s : Span) (f : Line) : Span :=
  if 0 < f.d then
    ⟨max s.lo (-(f.a/f.d)), s.hi⟩
  else if f.d < 0 then
    ⟨s.lo, min s.hi (f.a/(-f.d)+1)⟩
  else if 0 ≤ f.a then s
  else ⟨0,0⟩

theorem mem_keep (s : Span) (f : Line) (x : ℤ) :
    x ∈ (s.keep f).finset ↔ x ∈ s.finset ∧ 0 ≤ f.at x := by
  unfold Span.keep
  by_cases hpos : 0 < f.d
  · rw [ite_eq_left hpos]
    simp only [Span.finset, mem_Ico, max_le_iff]
    have h : -(f.a/f.d) ≤ x ↔ 0 ≤ f.at x := by
      rw [neg_le, Int.le_ediv_iff_mul_le hpos, Line.at]
      rw [neg_mul, mul_comm x f.d]
      omega
    tauto
  rw [ite_eq_right hpos]
  by_cases hneg : f.d < 0
  · rw [ite_eq_left hneg]
    simp only [Span.finset, mem_Ico, lt_min_iff]
    have h : x < f.a/(-f.d)+1 ↔ 0 ≤ f.at x := by
      rw [Int.lt_add_one_iff, Int.le_ediv_iff_mul_le (by omega : 0 < -f.d), Line.at]
      rw [mul_neg, mul_comm x f.d]
      omega
    tauto
  rw [ite_eq_right hneg]
  have hz : f.d = 0 := by omega
  simp [Line.at,hz]
  split <;> simp_all [Span.finset]

def Span.split (s : Span) (f : Line) : Span × Span :=
  (s.keep f, s.keep ⟨-f.a-1,-f.d⟩)

theorem split_sum (s : Span) (f : Line) (g : ℤ → ℤ) :
    (∑ x ∈ s.finset, g x) =
      (∑ x ∈ (s.split f).1.finset, g x) + ∑ x ∈ (s.split f).2.finset, g x := by
  unfold Span.split
  have hneg (x : ℤ) : 0 ≤ (Line.mk (-f.a-1) (-f.d)).at x ↔ f.at x < 0 := by
    simp only [Line.at, neg_mul]
    omega
  have hu : (s.keep f).finset ∪ (s.keep ⟨-f.a-1,-f.d⟩).finset = s.finset := by
    ext x
    simp only [mem_union, mem_keep, hneg]
    by_cases hx : x ∈ s.finset <;> simp [hx, le_or_gt 0 (f.at x)]
  have hd : Disjoint (s.keep f).finset (s.keep ⟨-f.a-1,-f.d⟩).finset := by
    refine disjoint_left.mpr fun x h₁ h₂ => ?_
    have ha := ((mem_keep s f x).mp h₁).2
    have hb := (hneg x).mp ((mem_keep s ⟨-f.a-1,-f.d⟩ x).mp h₂).2
    omega
  rw [← hu, sum_union hd]

def Span.size (s : Span) : ℕ := (s.hi-s.lo).toNat

theorem Span.sum_eq_range (s : Span) (g : ℤ → ℤ) :
    (∑ x ∈ s.finset, g x) = ∑ i ∈ range s.size, g (s.lo + (i : ℤ)) := by
  rw [Span.finset, Int.Ico_eq_finset_map, sum_map]
  rfl

open private lineBandSum lineBandSum_eq from ProximityPrize.SubmissionLower.KoalaPiecewiseTriangle

def Span.charge (s : Span) (b : BandCuts) (l q : Line) : ℤ :=
  if s.hi ≤ s.lo ∨ (l.d = 0 ∧ l.a = b.l0) ∨ (q.d = 0 ∧ q.a = b.q1) then 0
  else lineBandSum b l q s.lo s.size

theorem Span.charge_eq (s : Span) (b : BandCuts) (l q : Line) :
    s.charge b l q = ∑ x ∈ s.finset, b.at (l.at x) (q.at x) := by
  unfold charge
  rw [s.sum_eq_range]
  split
  · rename_i hz
    rcases hz with he | ⟨hd,ha⟩ | ⟨hd,ha⟩
    · have hz : s.size = 0 := by unfold size; omega
      simp [hz]
    · simp [band_at,Line.at,hd,ha]
    · simp [band_at,Line.at,hd,ha]
  · exact lineBandSum_eq b l q s.lo s.size

inductive ReceiptTree (α : Type)
  | leaf (a : α)
  | fork (cond : Line) (yes no : ReceiptTree α)

def ReceiptTree.eval {α : Type} : ReceiptTree α → ℤ → α
  | .leaf a, _ => a
  | .fork cond yes no, x => if 0 ≤ cond.at x then yes.eval x else no.eval x

def ReceiptTree.bind {α β : Type} (k : α → ReceiptTree β) : ReceiptTree α → ReceiptTree β
  | .leaf a => k a
  | .fork cond yes no => .fork cond (yes.bind k) (no.bind k)

theorem ReceiptTree.eval_bind {α β : Type} (k : α → ReceiptTree β) (t : ReceiptTree α) (x : ℤ) :
    (t.bind k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf a => rfl
  | fork cond yes no ihy ihn =>
    by_cases h : 0 ≤ cond.at x <;> simp [ReceiptTree.bind, ReceiptTree.eval, h, ihy, ihn]

def chooseMin (f g : Line) : ReceiptTree Line := .fork (g.sub f) (.leaf f) (.leaf g)

def chooseMax (f g : Line) : ReceiptTree Line := .fork (g.sub f) (.leaf g) (.leaf f)

theorem chooseMin_at (f g : Line) (x : ℤ) :
    ((chooseMin f g).eval x).at x = min (f.at x) (g.at x) := by
  have h : (g.sub f).at x = g.at x - f.at x := by simp [Line.sub,Line.at]; ring
  simp only [chooseMin, ReceiptTree.eval, h, sub_nonneg]
  split <;> simp [min_def, *]

theorem chooseMax_at (f g : Line) (x : ℤ) :
    ((chooseMax f g).eval x).at x = max (f.at x) (g.at x) := by
  have h : (g.sub f).at x = g.at x - f.at x := by simp [Line.sub,Line.at]; ring
  simp only [chooseMax, ReceiptTree.eval, h, sub_nonneg]
  split <;> simp [max_def, *]

def ReceiptTree.receipt (b : BandCuts) : ReceiptTree (Line × Line) → Span → ℤ
  | .leaf pair, s => s.charge b pair.1 pair.2
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let parts := s.split cond
      yes.receipt b parts.1 + no.receipt b parts.2

theorem ReceiptTree.receipt_eq (b : BandCuts) (t : ReceiptTree (Line × Line)) (s : Span) :
    t.receipt b s = ∑ x ∈ s.finset, b.at ((t.eval x).1.at x) ((t.eval x).2.at x) := by
  induction t generalizing s with
  | leaf p =>
    exact s.charge_eq b p.1 p.2
  | fork cond yes no ihy ihn =>
    rw [ReceiptTree.receipt]
    split
    · rename_i he
      have hs : s.finset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x h
        have hx := mem_Ico.mp h
        omega
      simp [hs]
    dsimp only
    rw [ihy,ihn,split_sum s cond]
    congr 1
    · apply sum_congr rfl
      intro x hx
      rw [Span.split,mem_keep] at hx
      simp [ReceiptTree.eval,hx.2]
    · apply sum_congr rfl
      intro x hx
      rw [Span.split,mem_keep] at hx
      have hx' : ¬0 ≤ cond.at x := by
        simp only [Line.at,neg_mul] at hx ⊢
        omega
      simp [ReceiptTree.eval,hx']

#print axioms Span.charge_eq
#print axioms ReceiptTree.receipt_eq
end KoalaLinearWindow
