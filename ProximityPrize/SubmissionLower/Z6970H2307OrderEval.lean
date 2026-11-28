import ProximityPrize.SubmissionLower.Z6970H2307WidePrefix
import ProximityPrize.SubmissionLower.Z6970ExpandedCappedArithmetic
import ProximityPrize.SubmissionLower.Z6970H2307OrderTypes

set_option autoImplicit false
set_option Elab.async false

namespace Height2307WidePrefix
def upperTail (w j : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | fuel+1, start, span =>
    if span=0 then 0 else
      let take := min w span
      (take : ℤ) * Low6969GateCell.cappedN (ExpandedTaper6970.cap start) j 500 +
        upperTail w j fuel (start+take) (span-take)

def countUpper (b j w : ℕ) : ℤ :=
  fastPrefix (min b 3513) j + upperTail w j 512 3514 (b-3513)

end Height2307WidePrefix

namespace Height2307Orders
open K1_13 (Shape)
open Height2307WidePrefix
open scoped BigOperators

def upperRemaining (stride b j : ℕ) : ℕ :=
  if b≤4024 ∧ j≤1679 then
    if b=0 ∧ j=0 then 427286700047
    else (countUpper (4024-b) (1679-j) stride).toNat
  else 0

def upperTerm (stride : ℕ) (r x : Shape) (L k : ℕ) : ℕ :=
  upperRemaining stride ((k+1)*r.b+(k+1-L)*x.b) ((k+1)*r.j+(k+1-L)*x.j)

def upperMass (stride : ℕ) (r x : Shape) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (L+1679/(r.j+x.j)), upperTerm stride r x L k

def checked (r : Shape) (p : Threshold) : Bool :=
  decide (0 < p.m ∧ 0 < p.j ∧ 0 < p.stride ∧
    upperMass p.stride r ⟨p.b,p.j,0⟩ (p.m-1) < 21230822871131)

end Height2307Orders
