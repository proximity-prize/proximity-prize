import ProximityPrize.SubmissionLower.LowPriceData82170
import ProximityPrize.SubmissionLower.LowRetained82170

set_option Elab.async false
namespace LowCaps82170
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one | two deriving DecidableEq
abbrev factorCap : ℕ := 248000000000000000
def reserve : Band → ℕ
  | .empty => 0
  | .one => 26500000000000000
  | .two => 87000000000000000
def start : Band → Shape
  | .empty => zeroShape
  | .one => P0_9_8.oneStart
  | .two => P0_9_8.twoStart

def thresholds : Band → List Threshold
  | .empty => [⟨3,9,15⟩, ⟨5,15,34⟩, ⟨17,6,9⟩, ⟨32,5,22⟩, ⟨13,38,51⟩, ⟨62,4,38⟩, ⟨63,15,44⟩, ⟨65,32,51⟩, ⟨94,38,53⟩]
  | .one => [⟨2,4,4⟩, ⟨2,6,24⟩, ⟨5,14,51⟩, ⟨9,25,61⟩, ⟨12,36,66⟩]
  | .two => [⟨1,3,62⟩, ⟨8,23,104⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def allowance (k : Band) (j : ℕ) : ℕ := P0_9_8.indexBudget (start k) (factorCap-reserve k) j

theorem order_pos (k : Band) (x : Shape) : 0 < order k x :=
  (P0_9_8.orderFor_select x.b x.j (thresholds k)).1
theorem order_mono (k : Band) {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    order k x ≤ order k y := P0_9_8.orderFor_mono hb hj _
end LowCaps82170
