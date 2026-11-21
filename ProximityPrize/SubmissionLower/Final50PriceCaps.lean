import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.Final50PriceRetained

set_option Elab.async false
namespace Final50PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one | two deriving DecidableEq
abbrev budget : ℕ := 272345433993584332
def factorCap (top : ℕ) : ℕ := budget - Final50Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one => 40020463277620184
  | .two => 142238177889030227
def start : Band → Shape
  | .empty => zeroShape
  | .one => P0_9_8.oneStart
  | .two => P0_9_8.twoStart

def Admits (k : Band) (r : Shape) : Prop := InBox (start k) r ∧ (start k).t = r.t

def activeCap (k : Band) : ℕ :=
  152 - max (start k).b (2 * (((start k).j + 2) / 3))

def thresholds : Band → List Threshold
  | .empty => [⟨1,9,3⟩, ⟨1,15,10⟩, ⟨1,27,35⟩, ⟨2,12,4⟩, ⟨2,18,11⟩, ⟨2,29,37⟩, ⟨3,9,11⟩, ⟨3,30,38⟩, ⟨4,12,23⟩, ⟨4,32,39⟩, ⟨7,21,33⟩, ⟨10,30,40⟩, ⟨12,36,43⟩, ⟨14,6,2⟩, ⟨18,6,6⟩, ⟨25,3,2⟩, ⟨32,3,7⟩, ⟨33,6,19⟩, ⟨33,9,21⟩, ⟨36,18,36⟩, ⟨39,33,46⟩, ⟨47,3,10⟩, ⟨48,6,25⟩, ⟨62,3,12⟩, ⟨62,15,33⟩, ⟨62,27,37⟩, ⟨63,6,31⟩, ⟨63,29,38⟩, ⟨64,32,41⟩, ⟨65,21,40⟩, ⟨65,36,48⟩, ⟨66,27,44⟩, ⟨78,3,15⟩, ⟨78,6,37⟩, ⟨93,3,17⟩, ⟨93,9,41⟩, ⟨93,15,44⟩, ⟨93,30,46⟩, ⟨94,22,45⟩, ⟨94,32,47⟩, ⟨94,43,50⟩, ⟨95,33,48⟩, ⟨96,36,49⟩, ⟨102,47,51⟩, ⟨108,3,19⟩, ⟨108,46,51⟩, ⟨109,39,50⟩, ⟨116,44,51⟩, ⟨120,43,51⟩]
  | .one => [⟨1,9,3⟩, ⟨1,15,10⟩, ⟨1,26,36⟩, ⟨2,6,12⟩, ⟨2,27,39⟩, ⟨3,9,26⟩, ⟨4,12,41⟩, ⟨7,21,49⟩, ⟨9,27,53⟩, ⟨17,3,6⟩, ⟨32,3,26⟩, ⟨47,3,35⟩, ⟨62,3,44⟩, ⟨64,18,50⟩, ⟨64,32,59⟩, ⟨92,6,47⟩, ⟨92,26,52⟩, ⟨92,27,55⟩, ⟨92,37,60⟩, ⟨92,38,61⟩, ⟨93,39,62⟩, ⟨94,21,56⟩, ⟨94,24,59⟩]
  | .two => [⟨1,3,26⟩, ⟨1,24,61⟩, ⟨2,6,49⟩, ⟨2,26,63⟩, ⟨3,27,65⟩, ⟨4,12,67⟩, ⟨6,18,80⟩, ⟨8,24,87⟩, ⟨31,3,53⟩, ⟨33,9,75⟩, ⟨61,3,67⟩, ⟨63,15,84⟩, ⟨64,32,90⟩, ⟨91,24,89⟩, ⟨92,6,72⟩, ⟨107,39,91⟩, ⟨107,41,92⟩]

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
end Final50PriceCaps
