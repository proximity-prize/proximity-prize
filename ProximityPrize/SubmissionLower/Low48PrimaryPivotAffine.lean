import ProximityPrize.SubmissionLower.Low48PrimaryPivotAggregate
import ProximityPrize.SubmissionLower.KoalaLinearWindow

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle KoalaLinearWindow
open scoped BigOperators
open private contactExpr highIndexExpr lowOrderExpr fixedResidue atSecond
  from ProximityPrize.SubmissionLower.Low48PrimaryPivotAggregate

private def fix (a : ℤ) : Line := ⟨a,0⟩

private def contactLines (c f r : ℕ) : ReceiptTree Line :=
  let a := fix (1650-(f : ℤ))
  let b : Line := ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩
  let d : Line := ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩
  let e : Line := ⟨1650-(r : ℤ)-(c : ℤ)-(f : ℤ)+(1650-(c : ℤ)-3*(f : ℤ))/2,-3⟩
  ((chooseMin d e).bind (chooseMin b)).bind (chooseMin a)

private theorem contactLines_at (c f r : ℕ) (x : ℤ) :
    ((contactLines c f r).eval x).at x = (contactExpr c f r).at x := by
  simp [contactLines, ReceiptTree.eval_bind, chooseMin_at, contactExpr, Expr.at, Expr.const, fix]

private def indexLines (w : Window) (c f r : ℕ) : ReceiptTree Line :=
  (chooseMin (fix (1651-(w.offsetLo : ℤ))) ⟨(r : ℤ)+2*(c : ℤ)+3*(f : ℤ)+1,3⟩).bind
    (chooseMax (fix (indexLo w)))

private theorem indexLines_at (w : Window) (c f r : ℕ) (x : ℤ) :
    ((indexLines w c f r).eval x).at x = (highIndexExpr w c f r).at x := by
  simp [indexLines, ReceiptTree.eval_bind, chooseMin_at, chooseMax_at, highIndexExpr, Expr.at, Expr.const, fix]

private def orderLines (w : Window) (c f r : ℕ) : ReceiptTree Line :=
  ((contactLines c f r).bind (fun l =>
    chooseMax (fix (4650-(w.diagonalHi : ℤ))) ⟨l.a+1,l.d⟩)).bind (chooseMin (fix (orderHi w)))

private theorem orderLines_at (w : Window) (c f r : ℕ) (x : ℤ) :
    ((orderLines w c f r).eval x).at x = (lowOrderExpr w c f r).at x := by
  simp only [orderLines, ReceiptTree.eval_bind, chooseMin_at, chooseMax_at, lowOrderExpr,
    Expr.at, Expr.const, fix]
  have h (l : Line) : (Line.mk (l.a+1) l.d).at x = l.at x + 1 := by simp [Line.at]; ring
  rw [h, contactLines_at]
  simp [Line.at]

private def linePairs (w : Window) (c f r : ℕ) : ReceiptTree (Line × Line) :=
  (indexLines w c f r).bind fun l =>
    (orderLines w c f r).bind fun q => .leaf (l,q)

private def directResidue (w : Window) (c f r : ℕ) : ℤ :=
  let n := (1653-(2*c+3*f+r))/3
  let band : BandCuts := ⟨indexLo w,orderHi w,(w.gradeLo : ℤ)-3000,(w.gradeHi : ℤ)-3000⟩
  (linePairs w c f r).receipt band ⟨0,n⟩

private theorem directResidue_eq (w : Window) (c f r : ℕ) :
    directResidue w c f r = fixedResidue w c f r := by
  dsimp only [directResidue,fixedResidue]
  rw [ReceiptTree.receipt_eq, Span.sum_eq_range, sumBand_eq]
  simp only [Span.size, sub_zero, Int.toNat_natCast, zero_add]
  apply sum_congr rfl
  intro i _
  simp only [linePairs, ReceiptTree.eval_bind, ReceiptTree.eval]
  rw [indexLines_at, orderLines_at]

def directRow (w : Window) (f c : ℕ) : ℤ :=
  directResidue w c f 0 + directResidue w c f 1 + directResidue w c f 2

theorem directRow_eq (w : Window) (f c : ℕ) : directRow w f c = atSecond w f c := by
  simp [directRow, atSecond, directResidue_eq]

def directSlab (w : Window) (f : ℕ) : ℤ :=
  ((List.range ((1650-3*f)/2+1)).map (directRow w f)).sum

theorem directSlab_eq (w : Window) (f : ℕ) : directSlab w f = feeSlab w f := by
  unfold directSlab feeSlab
  apply congrArg List.sum
  exact List.map_congr_left fun c _ => directRow_eq w f c

#print axioms directSlab_eq
end Low48PrimaryPivot
