import ProximityPrize.SubmissionLower.Low48PrimaryPivotThreshold

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
      (n:ℤ)*(2*a+d*((n:ℤ)-1)):=by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih]
    simp only [Nat.cast_succ]
    ring

theorem Span.sumLine_eq (s : Span) (f : Line) :
    s.sumLine f = ∑ x ∈ s.finset,f.at x:=by
  unfold sumLine
  rw [s.sum_eq_range]
  by_cases hs:s.lo < s.hi
  · rw [ite_eq_left hs]
    have h (i : ℕ) : f.at (s.lo+(i : ℤ)) = (f.a+f.d*s.lo)+f.d*(i : ℤ) := by
      simp [Line.at]
      ring
    simp_rw [h]
    have he:=twice_sum_line (f.a+f.d*s.lo) f.d s.size
    have hn:(s.size:ℤ)=s.hi-s.lo:=by unfold size; omega
    rw [hn] at he
    rw [← Int.mul_ediv_cancel_left (∑ i ∈ range s.size, (f.a+f.d*s.lo+f.d*(i : ℤ)))
      (by decide:(2:ℤ)≠0),he]
    congr 1
    ring
  · rw [ite_eq_right hs]
    have h:s.size=0:=by unfold size; omega
    simp [h]

def ReceiptTree.sumPositive : ReceiptTree Line → Span → ℤ
  | .leaf f,s => (s.keep f).sumLine f
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let pair:=s.split cond
      yes.sumPositive pair.1+no.sumPositive pair.2

theorem ReceiptTree.sumPositive_eq (t : ReceiptTree Line) (s : Span) :
    t.sumPositive s = ∑ x ∈ s.finset,max 0 ((t.eval x).at x):=by
  induction t generalizing s with
  | leaf f =>
    rw [ReceiptTree.sumPositive,Span.sumLine_eq,split_sum s f]
    have eq (x:ℤ):(ReceiptTree.leaf f).eval x=f:=rfl
    simp only [eq]
    have hpos : (∑ x ∈ (s.split f).1.finset, max 0 (f.at x)) =
          ∑ x ∈ (s.keep f).finset,f.at x:=by
      apply sum_congr rfl
      intro x hx
      rw [max_eq_right (((mem_keep s f x).mp hx).2)]
    have hneg : (∑ x ∈ (s.split f).2.finset, max 0 (f.at x)) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [Span.split,mem_keep] at hx
      simp only [Line.at,neg_mul] at hx
      change max 0 (f.a+f.d*x)=0
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

private def paritySpan (fmax r:ℤ):Span:=⟨0,(fmax-r)/2+1⟩

private def widthLine (j r:ℤ):Line:=⟨(j-3*r)/2+1,-3⟩

private def countTree (j q r : ℤ) : ReceiptTree Line :=
  let k:=(widthLine j r).a
  let a:=widthLine j r
  let b:Line:=⟨k-(3*q-9900+5*j)+3*r,3⟩
  let c:Line:=⟨k-(q-4950+3*j)+2*r,1⟩
  let d:Line:=⟨k-(2*q-4950+2*j)+r,-1⟩
  ((chooseMin c d).bind (chooseMin b)).bind (chooseMin a)

private theorem countTree_at (j q r x : ℤ) :
    ((countTree j q r).eval x).at x =
      (j-3*(2*x+r))/2+1 -
        max 0 (max (3*q-9900+5*j-3*(2*x+r))
          (max (q-4950+3*j-2*(2*x+r)) (2*q-4950+2*j-(2*x+r)))):=by
  simp only [countTree,ReceiptTree.eval_bind,chooseMin_at]
  simp only [widthLine,Line.at]
  omega

def uncharged (j q : ℤ) : ℤ :=
  let fmax:=min (j/3) (1650-q)
  let c0:=(countTree j q 0).sumPositive (paritySpan fmax 0)
  let c1:=(countTree j q 1).sumPositive (paritySpan fmax 1)
  c0+c1

def totalAtIndex (j : ℤ) : ℤ :=
  let s0:=paritySpan (j/3) 0
  let s1:=paritySpan (j/3) 1
  s0.sumLine (widthLine j 0)+s1.sumLine (widthLine j 1)

private def binWeight (w : Window) (j q : ℤ) : ℤ :=
  max 0 (min (min (j+1) (1651-(w.offsetLo : ℤ))) (q+(w.gradeHi : ℤ)-3000) -
    max (1650-(w.offsetHi:ℤ)) (q+(w.gradeLo:ℤ)-3000))

def binAt (w : Window) (j : ℕ) : ℤ :=
  let total:=totalAtIndex j
  let q0:=w.diagonalHi
  ((List.range (w.diagonalHi+1-w.diagonalLo)).map fun i : ℕ =>
    let q:ℤ:=4650-(q0:ℤ)+(i:ℤ)
    let volume:=binWeight w j q
    if volume=0 then 0 else volume*(total-uncharged j q)).sum

#print axioms countTree_at
end Low48PrimaryPivot
