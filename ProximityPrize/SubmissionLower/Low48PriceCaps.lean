import ProximityPrize.SubmissionLower.Low48Price
import ProximityPrize.SubmissionLower.Low48PriceRetained

set_option Elab.async false
namespace Low48PriceCaps
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one | two deriving DecidableEq
abbrev budget : ℕ := 268265986140016442
def factorCap (top : ℕ) : ℕ := budget - Low48Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one => 40082370293580951
  | .two => 142454985280391059
def start : Band → Shape
  | .empty => zeroShape
  | .one => P0_9_8.oneStart
  | .two => P0_9_8.twoStart

def thresholds : Band → List Threshold
  | .empty => [⟨1,9,10⟩, ⟨1,10,14⟩, ⟨1,11,18⟩, ⟨1,12,21⟩, ⟨1,13,24⟩, ⟨1,14,26⟩, ⟨1,15,29⟩, ⟨1,16,30⟩, ⟨1,17,32⟩, ⟨1,18,33⟩, ⟨1,19,35⟩, ⟨1,20,36⟩, ⟨1,21,37⟩, ⟨1,22,38⟩, ⟨1,24,39⟩, ⟨1,25,40⟩, ⟨1,26,41⟩, ⟨1,28,42⟩, ⟨1,30,43⟩, ⟨1,32,44⟩, ⟨1,35,45⟩, ⟨1,37,46⟩, ⟨1,41,47⟩, ⟨6,8,7⟩, ⟨7,8,8⟩, ⟨8,44,48⟩, ⟨12,7,6⟩, ⟨17,6,5⟩, ⟨20,5,4⟩, ⟨22,4,2⟩, ⟨46,45,49⟩, ⟨88,46,50⟩, ⟨119,50,51⟩]
  | .one => [⟨1,5,7⟩, ⟨1,6,16⟩, ⟨1,7,22⟩, ⟨1,8,27⟩, ⟨1,9,31⟩, ⟨1,10,35⟩, ⟨1,11,38⟩, ⟨1,12,40⟩, ⟨1,13,42⟩, ⟨1,14,44⟩, ⟨1,15,45⟩, ⟨1,16,47⟩, ⟨1,17,48⟩, ⟨1,18,49⟩, ⟨1,19,50⟩, ⟨1,20,51⟩, ⟨1,21,52⟩, ⟨1,23,53⟩, ⟨1,24,54⟩, ⟨1,26,55⟩, ⟨1,28,56⟩, ⟨6,4,2⟩]
  | .two => [⟨1,2,21⟩, ⟨1,3,38⟩, ⟨1,4,48⟩, ⟨1,5,55⟩, ⟨1,6,61⟩, ⟨1,7,65⟩, ⟨1,8,68⟩, ⟨1,9,70⟩, ⟨1,10,72⟩, ⟨1,11,74⟩, ⟨1,12,76⟩, ⟨1,13,77⟩, ⟨1,14,78⟩, ⟨1,15,79⟩, ⟨1,16,80⟩, ⟨1,17,81⟩, ⟨1,18,82⟩, ⟨1,20,83⟩, ⟨1,22,84⟩, ⟨1,24,85⟩, ⟨1,26,86⟩, ⟨1,29,87⟩, ⟨1,33,88⟩, ⟨1,38,89⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (50 - r.j)
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
