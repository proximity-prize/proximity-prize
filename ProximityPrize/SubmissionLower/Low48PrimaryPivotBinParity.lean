import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect

set_option Elab.async false

-- merged module Low48PrimaryPivotAggregate
section Merged_Low48PrimaryPivotAggregate

-- merged module KoalaAffineTriangle
section Merged_KoalaAffineTriangle

set_option autoImplicit false

namespace KoalaAffineTriangle

open scoped BigOperators

def twiceTriangle (x : ℤ) : ℤ :=
  let q := max 0 x
  q * (q + 1)

private def polynomial (a d : ℤ) (n : ℕ) : ℤ :=
  let m : ℤ := n
  6 * m * a * (a + 1) + 3 * d * (2 * a + 1) * m * (m - 1) +
    d * d * m * (m - 1) * (2 * m - 1)

private def closed (a d : ℤ) (n : ℕ) : ℤ := polynomial a d n / 6

















private def firstPositive (a d : ℤ) : ℕ := ((-a)/d+1).toNat





private def fast (a d : ℤ) (n : ℕ) : ℤ :=
  if 0 < d then
    let j := min n (firstPositive a d)
    if j = n then 0 else closed (a+d*(j : ℤ)) d (n-j)
  else if d < 0 then
    closed a d (min n (firstPositive (-a) (-d)))
  else
    (n : ℤ) * twiceTriangle a


/-- Sum a positive triangular term using the unique sign crossing of the affine argument. -/
def sumFast (a d lo : ℤ) (n : ℕ) : ℤ := fast (a+d*lo) d n



end KoalaAffineTriangle

end Merged_KoalaAffineTriangle

-- merged module KoalaPiecewiseTriangle
section Merged_KoalaPiecewiseTriangle

set_option autoImplicit false
set_option Elab.async false

namespace KoalaPiecewiseTriangle
open Finset
open scoped BigOperators

structure Line where
  a : ℤ
  d : ℤ

def Line.at (f : Line) (x : ℤ) : ℤ := f.a + f.d*x

def Line.sub (f g : Line) : Line := ⟨f.a-g.a,f.d-g.d⟩

inductive Expr
  | affine (f : Line)
  | lower (f g : Expr)
  | upper (f g : Expr)
  | sub (f g : Expr)

def Expr.at : Expr → ℤ → ℤ
  | .affine f, x => f.at x
  | .lower f g, x => min (f.at x) (g.at x)
  | .upper f g, x => max (f.at x) (g.at x)
  | .sub f g, x => f.at x - g.at x

def Expr.const (a : ℤ) : Expr := .affine ⟨a,0⟩

private def ordered (f g : Line) (lo hi : ℤ) : Prop :=
  f.at lo ≤ g.at lo ∧ f.at hi ≤ g.at hi

private instance (f g : Line) (lo hi : ℤ) : Decidable (ordered f g lo hi) := by
  unfold ordered
  infer_instance









structure BandCuts where
  l0 : ℤ
  q1 : ℤ
  first : ℤ
  last : ℤ



private def lineCutSum (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) : ℤ :=
  let sum := KoalaAffineTriangle.sumFast
  sum (l.a-k-q.a) (l.d-q.d) lo n -
    sum (b.l0-k-q.a) (-q.d) lo n -
    (sum (l.a-k-b.q1) l.d lo n -
      (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1))


def lineBandSum (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) : ℤ :=
  lineCutSum b l q b.first lo n - lineCutSum b l q b.last lo n









end KoalaPiecewiseTriangle

end Merged_KoalaPiecewiseTriangle

-- merged module Low48PrimaryPivotAggregate
section Merged_Low48PrimaryPivotAggregate

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle
open scoped BigOperators

def contactExpr (c f r : ℕ) : Expr :=
  .lower (.const (1650-(f : ℤ)))
    (.lower (.affine ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩)
      (.lower (.affine ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩)
        (.affine ⟨1650-(r : ℤ)-(c : ℤ)-(f : ℤ)+(1650-(c : ℤ)-3*(f : ℤ))/2,-3⟩)))

theorem contactExpr_eq (c f r t : ℕ) (hr : r < 3)
    (h : (Triple.mk (3*t+r) c f).index ≤ 1650) :
    (contactExpr c f r).at t = ((Triple.mk (3*t+r) c f).contact : ℤ) := by
  rw [contact_eq]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, Triple.room, Triple.index] at *
  omega












end Low48PrimaryPivot

end Merged_Low48PrimaryPivotAggregate

end Merged_Low48PrimaryPivotAggregate

-- merged module Low48PrimaryPivotBinParity
section Merged_Low48PrimaryPivotBinParity

-- merged module KoalaLinearWindow
section Merged_KoalaLinearWindow

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

open KoalaPiecewiseTriangle (lineBandSum)

def Span.charge (s : Span) (b : BandCuts) (l q : Line) : ℤ :=
  if s.hi ≤ s.lo ∨ (l.d = 0 ∧ l.a = b.l0) ∨ (q.d = 0 ∧ q.a = b.q1) then 0
  else lineBandSum b l q s.lo s.size


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


theorem chooseMin_at (f g : Line) (x : ℤ) :
    ((chooseMin f g).eval x).at x = min (f.at x) (g.at x) := by
  have h : (g.sub f).at x = g.at x - f.at x := by simp [Line.sub,Line.at]; ring
  simp only [chooseMin, ReceiptTree.eval, h, sub_nonneg]
  split <;> simp [min_def, *]


def ReceiptTree.receipt (b : BandCuts) : ReceiptTree (Line × Line) → Span → ℤ
  | .leaf pair, s => s.charge b pair.1 pair.2
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let parts := s.split cond
      yes.receipt b parts.1 + no.receipt b parts.2


end KoalaLinearWindow

end Merged_KoalaLinearWindow

-- merged module Low48PrimaryPivotThreshold
section Merged_Low48PrimaryPivotThreshold
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low48PrimaryPivot
open K1_13_2_3 KoalaLinearWindow KoalaPiecewiseTriangle Finset
open scoped BigOperators
open Low48PrimaryPivot (contactExpr contactExpr_eq)
theorem contact_ge_iff (p : Triple) (q : ℤ) (h : p.index ≤ 1650) :
    q ≤ (p.contact : ℤ) ↔
      (p.f : ℤ) ≤ 1650-q ∧
      (p.c : ℤ)+3*(p.f : ℤ) ≥ 3*q-9900+5*(p.index : ℤ) ∧
      (p.c : ℤ)+2*(p.f : ℤ) ≥ q-4950+3*(p.index : ℤ) ∧
      (p.c : ℤ)+(p.f : ℤ) ≥ 2*q-4950+2*(p.index : ℤ) := by
  rcases p with ⟨b,c,f⟩
  let r := b%3
  let t := b/3
  have hr : r < 3 := Nat.mod_lt _ (by decide)
  have hbt : 3*t+r = b := by dsimp [r,t]; omega
  have he := contactExpr_eq c f r t hr (by rwa [hbt])
  rw [hbt] at he
  rw [← he]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, le_min_iff]
  simp only [Triple.index, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  have hbt' : (b : ℤ) = 3*(t : ℤ)+(r : ℤ) := by omega
  omega
def sectionWidth (j f : ℕ) : ℤ := ((j : ℤ)-3*(f : ℤ))/2+1
def sectionFloor (j f : ℕ) (q : ℤ) : ℤ :=
  max 0 (max
    (3*q-9900+5*(j : ℤ)-3*(f : ℤ))
    (max (q-4950+3*(j : ℤ)-2*(f : ℤ)) (2*q-4950+2*(j : ℤ)-(f : ℤ))))
theorem section_count (j f : ℕ) (q : ℤ) (hf : (f : ℤ) ≤ 1650-q) (hj : j ≤ 1650)
    (h : 3*f ≤ j) :
    (((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)).card : ℤ) =
      max 0 (sectionWidth j f-sectionFloor j f q) := by
  have hset : ((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)) =
      Ico (sectionFloor j f q) (sectionWidth j f) := by
    ext c
    simp only [mem_filter,mem_Ico,sectionFloor,max_le_iff]
    constructor
    · rintro ⟨⟨hc,hu⟩,hq⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx] at hq
      dsimp only at hq
      simp only [Int.toNat_of_nonneg hc] at hq
      omega
    · rintro ⟨⟨hc,h₁,h₂,h₃⟩,hu⟩
      refine ⟨⟨hc,hu⟩,?_⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx]
      dsimp only
      simp only [Int.toNat_of_nonneg hc]
      omega
  rw [hset,Int.card_Ico]
  omega
#print axioms contact_ge_iff
#print axioms section_count
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotThreshold

-- merged module Low48PrimaryPivotSectionSum
section Merged_Low48PrimaryPivotSectionSum

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace KoalaLinearWindow
open Finset KoalaPiecewiseTriangle
open scoped BigOperators

def Span.sumLine (s : Span) (f : Line) : ℤ :=
  if s.lo < s.hi then (s.hi-s.lo)*(2*f.a+f.d*(s.lo+s.hi-1))/2 else 0

private theorem twice_sum_line (a d : ℤ) (n : ℕ) :
    2*(∑ i ∈ range n, (a+d*(i : ℤ))) =
      (n : ℤ)*(2*a+d*((n : ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [Nat.cast_succ]
    ring

theorem Span.sumLine_eq (s : Span) (f : Line) :
    s.sumLine f = ∑ x ∈ s.finset, f.at x := by
  unfold sumLine
  rw [s.sum_eq_range]
  by_cases hs : s.lo < s.hi
  · rw [ite_eq_left hs]
    have h (i : ℕ) : f.at (s.lo+(i : ℤ)) = (f.a+f.d*s.lo)+f.d*(i : ℤ) := by
      simp [Line.at]
      ring
    simp_rw [h]
    have he := twice_sum_line (f.a+f.d*s.lo) f.d s.size
    have hn : (s.size : ℤ) = s.hi-s.lo := by unfold size; omega
    rw [hn] at he
    rw [← Int.mul_ediv_cancel_left (∑ i ∈ range s.size, (f.a+f.d*s.lo+f.d*(i : ℤ)))
      (by decide : (2 : ℤ) ≠ 0),he]
    congr 1
    ring
  · rw [ite_eq_right hs]
    have h : s.size = 0 := by unfold size; omega
    simp [h]

def ReceiptTree.sumPositive : ReceiptTree Line → Span → ℤ
  | .leaf f, s => (s.keep f).sumLine f
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let pair := s.split cond
      yes.sumPositive pair.1 + no.sumPositive pair.2

theorem ReceiptTree.sumPositive_eq (t : ReceiptTree Line) (s : Span) :
    t.sumPositive s = ∑ x ∈ s.finset, max 0 ((t.eval x).at x) := by
  induction t generalizing s with
  | leaf f =>
    rw [ReceiptTree.sumPositive,Span.sumLine_eq,split_sum s f]
    have eq (x : ℤ) : (ReceiptTree.leaf f).eval x = f := rfl
    simp only [eq]
    have hpos : (∑ x ∈ (s.split f).1.finset, max 0 (f.at x)) =
          ∑ x ∈ (s.keep f).finset, f.at x := by
      apply sum_congr rfl
      intro x hx
      rw [max_eq_right (((mem_keep s f x).mp hx).2)]
    have hneg : (∑ x ∈ (s.split f).2.finset, max 0 (f.at x)) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [Span.split,mem_keep] at hx
      simp only [Line.at,neg_mul] at hx
      change max 0 (f.a+f.d*x) = 0
      rw [max_eq_left (by omega)]
    rw [hpos,hneg,add_zero]
  | fork cond yes no ihy ihn =>
    rw [ReceiptTree.sumPositive]
    split
    · rename_i h
      have hz : s.finset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := mem_Ico.mp hx
        omega
      simp [hz]
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
      have hh : ¬0 ≤ cond.at x := by
        simp only [Line.at,neg_mul] at hx ⊢
        omega
      simp [ReceiptTree.eval,hh]

#print axioms Span.sumLine_eq
#print axioms ReceiptTree.sumPositive_eq
end KoalaLinearWindow

namespace Low48PrimaryPivot
open KoalaLinearWindow KoalaPiecewiseTriangle Finset K1_13_2_3
open scoped BigOperators

def paritySpan (fmax r : ℤ) : Span := ⟨0,(fmax-r)/2+1⟩

def widthLine (j r : ℤ) : Line := ⟨(j-3*r)/2+1,-3⟩

def countTree (j q r : ℤ) : ReceiptTree Line :=
  let k := (widthLine j r).a
  let a := widthLine j r
  let b : Line := ⟨k-(3*q-9900+5*j)+3*r,3⟩
  let c : Line := ⟨k-(q-4950+3*j)+2*r,1⟩
  let d : Line := ⟨k-(2*q-4950+2*j)+r,-1⟩
  ((chooseMin c d).bind (chooseMin b)).bind (chooseMin a)

theorem countTree_at (j q r x : ℤ) :
    ((countTree j q r).eval x).at x =
      (j-3*(2*x+r))/2+1 -
        max 0 (max (3*q-9900+5*j-3*(2*x+r))
          (max (q-4950+3*j-2*(2*x+r)) (2*q-4950+2*j-(2*x+r)))) := by
  simp only [countTree,ReceiptTree.eval_bind,chooseMin_at]
  simp only [widthLine,Line.at]
  omega

def uncharged (j q : ℤ) : ℤ :=
  let fmax := min (j/3) (1650-q)
  let c0 := (countTree j q 0).sumPositive (paritySpan fmax 0)
  let c1 := (countTree j q 1).sumPositive (paritySpan fmax 1)
  c0+c1

def totalAtIndex (j : ℤ) : ℤ :=
  let s0 := paritySpan (j/3) 0
  let s1 := paritySpan (j/3) 1
  s0.sumLine (widthLine j 0) + s1.sumLine (widthLine j 1)

def binWeight (w : Window) (j q : ℤ) : ℤ :=
  max 0 (min (min (j+1) (1651-(w.offsetLo : ℤ))) (q+(w.gradeHi : ℤ)-3000) -
    max (1650-(w.offsetHi : ℤ)) (q+(w.gradeLo : ℤ)-3000))

def binAt (w : Window) (j : ℕ) : ℤ :=
  let total := totalAtIndex j
  let q0 := w.diagonalHi
  ((List.range (w.diagonalHi+1-w.diagonalLo)).map fun i : ℕ =>
    let q : ℤ := 4650-(q0 : ℤ)+(i : ℤ)
    let volume := binWeight w j q
    if volume = 0 then 0 else volume*(total-uncharged j q)).sum

#print axioms countTree_at
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotSectionSum

-- merged module Low48PrimaryPivotBinParity
section Merged_Low48PrimaryPivotBinParity

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open Finset KoalaLinearWindow KoalaPiecewiseTriangle
open scoped BigOperators
open Low48PrimaryPivot (paritySpan widthLine countTree countTree_at)

private theorem sum_by_parity (m : ℤ) (f : ℤ → ℤ) :
    (∑ a ∈ Ico (0:ℤ) (m+1), f a) =
      (∑ u ∈ (paritySpan m 0).finset, f (2*u)) +
        ∑ u ∈ (paritySpan m 1).finset, f (2*u+1) := by
  let idx (r : ℤ) := (paritySpan m r).finset
  have htwo : Ico (0:ℤ) 2 = {0,1} := by decide
  have hsum : (∑ r ∈ Ico (0:ℤ) 2, ∑ u ∈ idx r, f (2*u+r)) =
      (∑ u ∈ idx 0, f (2*u)) + (∑ u ∈ idx 1, f (2*u+1)) := by
    rw [htwo]
    simp
  rw [← hsum, Finset.sum_sigma']
  refine sum_bij (fun a _ => (⟨a%2,a/2⟩ : Sigma (fun _ : ℤ => ℤ))) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at ha ⊢
    omega
  · intro a _ b _ he
    have hmod := congrArg Sigma.fst he
    have hdiv := congrArg (fun p : Sigma (fun _ : ℤ => ℤ) => p.snd) he
    change a%2 = b%2 at hmod
    change a/2 = b/2 at hdiv
    omega
  · rintro ⟨r,u⟩ hx
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at hx
    refine ⟨2*u+r,mem_Ico.mpr (by omega),?_⟩
    have hm : (2*u+r)%2 = r := by omega
    have hd : (2*u+r)/2 = u := by omega
    simp [hm,hd]
  · intro a _
    change f a = f (2*(a/2)+a%2)
    congr 1
    omega

theorem totalAtIndex_eq (j : ℤ) :
    totalAtIndex j = ∑ f ∈ Ico (0:ℤ) (j/3+1), ((j-3*f)/2+1) := by
  rw [sum_by_parity]
  unfold totalAtIndex
  simp only [Span.sumLine_eq,widthLine,Line.at]
  congr 1 <;> apply sum_congr rfl <;> intro u _ <;> omega

theorem uncharged_eq (j q : ℤ) :
    uncharged j q = ∑ f ∈ Ico (0:ℤ) (min (j/3) (1650-q)+1),
      max 0 ((j-3*f)/2+1 -
        max 0 (max (3*q-9900+5*j-3*f)
          (max (q-4950+3*j-2*f) (2*q-4950+2*j-f)))) := by
  rw [sum_by_parity]
  simp only [uncharged,ReceiptTree.sumPositive_eq,countTree_at,add_zero]

#print axioms totalAtIndex_eq
#print axioms uncharged_eq
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinParity

end Merged_Low48PrimaryPivotBinParity
