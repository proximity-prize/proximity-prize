import ProximityPrize.SubmissionLower.Z6970PlateauIntegral

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedPlateauSum6970
open KoalaPiecewiseTriangle (Line)
open KoalaLinearWindow (Span)
open ExpandedPlateauIntegral6970 (receipt)

def lines (c f r : ℤ) : Line × List Line :=
  let w := 1679-2*c-3*f
  let u := 500-f
  let base := 1321+2*r+c+f-w
  (⟨base-r-min c u,3⟩, [⟨base-(w+c)/2,6⟩, ⟨base-(2*w-r+u)/3,7⟩,
    ⟨base-w+r,8⟩, ⟨base-w+r-u,9⟩, ⟨base-2*w+2*r,12⟩])

def spanLength (c f r : ℕ) : ℕ := (1682 - (r+2*c+3*f))/3

def strip (f c r : ℕ) : ℤ :=
  let n := spanLength c f r
  if n = 0 then 0 else
    let l := lines c f r
    receipt (⟨0,n⟩ : Span) l.1 l.2

def sumN (k : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m+1 => sumN k m + k m

theorem sumN_eq (k : ℕ → ℤ) (n : ℕ) : sumN k n = ∑ i ∈ Finset.range n, k i := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [sumN,Finset.sum_range_succ,ih]

def column (f c : ℕ) : ℤ := strip f c 0 + strip f c 1 + strip f c 2
def row (f : ℕ) : ℤ := sumN (column f) ((1681-3*f)/2)
def chunk (f len : ℕ) : ℤ := sumN (fun i => row (f+i)) len

theorem chunk_add (f a b : ℕ) : chunk f (a+b) = chunk f a + chunk (f+a) b := by
  simp only [chunk,sumN_eq,Finset.sum_range_add,Nat.add_assoc]

end ExpandedPlateauSum6970
