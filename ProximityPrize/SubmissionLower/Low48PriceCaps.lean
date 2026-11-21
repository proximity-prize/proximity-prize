import ProximityPrize.SubmissionLower.Low48Price
import ProximityPrize.SubmissionLower.Low48PriceRetained

set_option Elab.async false
namespace Low48PriceCaps
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one | two deriving DecidableEq
abbrev budget : ℕ := 268648601901754977
def factorCap (top : ℕ) : ℕ := budget - Low48Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one => 38877346089687623
  | .two => 138222946956298194
def start : Band → Shape
  | .empty => zeroShape
  | .one => P0_9_8.oneStart
  | .two => P0_9_8.twoStart

def thresholds : Band → List Threshold
  | .empty => [⟨3,9,7⟩, ⟨4,12,21⟩, ⟨5,15,25⟩, ⟨6,17,27⟩, ⟨8,24,32⟩, ⟨9,27,37⟩, ⟨10,28,39⟩, ⟨10,30,40⟩, ⟨11,31,41⟩, ⟨12,36,42⟩, ⟨17,6,3⟩, ⟨32,5,2⟩, ⟨32,6,5⟩, ⟨33,9,12⟩, ⟨62,4,2⟩, ⟨62,5,3⟩, ⟨62,6,10⟩, ⟨63,9,22⟩, ⟨64,15,37⟩, ⟨65,21,39⟩, ⟨65,24,40⟩, ⟨65,31,45⟩, ⟨66,29,45⟩, ⟨67,36,46⟩, ⟨67,38,47⟩, ⟨67,43,48⟩, ⟨94,33,47⟩, ⟨94,39,48⟩, ⟨95,38,48⟩, ⟨95,46,49⟩, ⟨109,43,49⟩, ⟨118,49,50⟩]
  | .one => [⟨2,5,4⟩, ⟨2,6,11⟩, ⟨3,9,20⟩, ⟨4,12,38⟩, ⟨6,17,44⟩, ⟨7,21,46⟩, ⟨10,30,48⟩, ⟨62,4,2⟩, ⟨63,14,44⟩, ⟨65,25,51⟩, ⟨65,27,56⟩, ⟨65,36,59⟩, ⟨66,30,57⟩, ⟨67,41,60⟩, ⟨94,38,60⟩]
  | .two => [⟨1,3,10⟩, ⟨2,6,30⟩, ⟨3,9,62⟩, ⟨5,14,71⟩, ⟨6,18,73⟩, ⟨9,27,77⟩, ⟨64,24,83⟩, ⟨65,30,85⟩, ⟨93,37,86⟩, ⟨93,40,87⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (49 - r.j)
def allowance (top : ℕ) (k : Band) (j : ℕ) : ℕ := indexBudget (start k) (factorCap top - reserve k) j

theorem factorCap_mono {a b : ℕ} (h : a ≤ b) (hb : b ≤ 13) : factorCap a ≤ factorCap b := by
  have ha := h.trans hb
  interval_cases a <;> interval_cases b <;> decide

theorem allowance_mono {a b j : ℕ} (k : Band) (h : a ≤ b) (hb : b ≤ 13) :
    allowance a k j ≤ allowance b k j :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (factorCap_mono h hb) _))

theorem order_pos (k : Band) (x : Shape) : 0 < order k x :=
  (P0_9_8.orderFor_select x.b x.j (thresholds k)).1
theorem order_mono (k : Band) {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    order k x ≤ order k y := P0_9_8.orderFor_mono hb hj _
end Low48PriceCaps
