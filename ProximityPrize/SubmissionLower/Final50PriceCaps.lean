import ProximityPrize.SubmissionLower.Final50PriceRetained

set_option Elab.async false
namespace Final50PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one3 | one4 | one5 | one6 | one7 | two6thin | two6wide | two7 deriving DecidableEq
abbrev budget : ℕ := 272835953008920747
def factorCap (top : ℕ) : ℕ := budget - Final50Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one3 => 16134172369732502
  | .one4 => 27316190336551897
  | .one5 => 41254742263085612
  | .one6 => 47596490173374667
  | .one7 => 41894803915252695
  | .two6thin => 126258668247061106
  | .two6wide => 169922241534105837
  | .two7 => 165116552226664301
def start : Band → Shape
  | .empty => ⟨0,0,0⟩
  | .one3 => ⟨1,3,1⟩
  | .one4 => ⟨2,4,1⟩
  | .one5 => ⟨2,5,1⟩
  | .one6 => ⟨2,6,1⟩
  | .one7 => ⟨3,7,1⟩
  | .two6thin => ⟨2,6,2⟩
  | .two6wide => ⟨12,6,2⟩
  | .two7 => ⟨3,7,2⟩
def activeCap (k : Band) : ℕ :=
  157 - max (start k).b (2 * (((start k).j + 2) / 3))

def Admits (k : Band) (r : Shape) : Prop :=
  InBox (start k) r ∧ r.j = (start k).j ∧ r.t = (start k).t ∧
    (k = .two6thin → r.b ≤ 11) ∧ (k = .empty → r = zeroShape)

def thresholds : Band → List Threshold
  | .empty => [⟨3,9,9⟩, ⟨4,10,14⟩, ⟨4,12,21⟩, ⟨10,8,8⟩, ⟨11,7,3⟩, ⟨5,15,28⟩, ⟨6,18,33⟩, ⟨18,6,5⟩, ⟨8,24,39⟩, ⟨33,5,17⟩, ⟨33,6,19⟩, ⟨34,9,25⟩, ⟨13,39,45⟩, ⟨64,4,33⟩, ⟨64,5,33⟩, ⟨64,6,34⟩, ⟨65,7,35⟩, ⟨65,9,36⟩, ⟨65,10,36⟩, ⟨65,12,37⟩, ⟨66,16,40⟩, ⟨66,18,40⟩, ⟨67,20,41⟩, ⟨66,22,42⟩, ⟨66,24,43⟩, ⟨67,28,44⟩, ⟨68,27,44⟩, ⟨68,30,45⟩, ⟨68,33,46⟩, ⟨69,45,48⟩, ⟨71,43,48⟩, ⟨69,49,48⟩, ⟨97,28,46⟩, ⟨98,31,46⟩, ⟨84,46,48⟩, ⟨97,36,47⟩, ⟨97,37,47⟩, ⟨98,44,48⟩, ⟨105,43,48⟩, ⟨98,52,49⟩, ⟨112,41,48⟩, ⟨105,51,49⟩, ⟨119,40,48⟩, ⟨111,50,49⟩, ⟨116,49,49⟩, ⟨122,48,49⟩]
  | .one3 => [⟨2,5,6⟩, ⟨2,6,14⟩, ⟨3,9,30⟩, ⟨5,15,44⟩, ⟨7,20,49⟩, ⟨8,24,52⟩, ⟨64,4,44⟩, ⟨64,5,45⟩, ⟨65,15,51⟩, ⟨68,28,56⟩, ⟨67,33,57⟩, ⟨69,34,58⟩, ⟨69,37,58⟩, ⟨97,46,60⟩]
  | .one4 => [⟨2,4,8⟩, ⟨2,5,18⟩, ⟨2,6,26⟩, ⟨3,9,39⟩, ⟨4,12,47⟩, ⟨5,15,52⟩, ⟨6,17,54⟩, ⟨9,27,61⟩, ⟨67,26,62⟩, ⟨67,38,65⟩, ⟨67,39,65⟩]
  | .one5 => [⟨1,3,9⟩, ⟨2,5,32⟩, ⟨2,6,38⟩, ⟨3,9,50⟩, ⟨5,15,61⟩, ⟨7,19,65⟩, ⟨8,24,68⟩, ⟨13,39,72⟩, ⟨67,37,73⟩, ⟨69,38,73⟩]
  | .one6 => [⟨1,3,32⟩, ⟨2,6,55⟩, ⟨6,18,77⟩, ⟨11,33,83⟩]
  | .one7 => [⟨1,3,74⟩, ⟨2,6,91⟩, ⟨4,12,102⟩, ⟨8,24,109⟩]
  | .two6thin => [⟨1,3,32⟩, ⟨2,6,55⟩, ⟨4,12,71⟩, ⟨6,18,77⟩, ⟨7,19,78⟩, ⟨7,21,79⟩, ⟨65,17,79⟩, ⟨66,30,83⟩, ⟨68,35,84⟩, ⟨67,39,85⟩, ⟨96,36,85⟩, ⟨96,43,85⟩, ⟨110,42,85⟩]
  | .two6wide => [⟨1,3,88⟩, ⟨3,9,112⟩, ⟨5,14,118⟩, ⟨63,33,126⟩, ⟨63,36,127⟩, ⟨62,39,127⟩, ⟨89,40,127⟩, ⟨89,45,128⟩, ⟨101,42,128⟩]
  | .two7 => [⟨1,3,74⟩, ⟨4,11,101⟩, ⟨4,12,102⟩, ⟨7,19,107⟩, ⟨8,23,109⟩, ⟨66,32,111⟩, ⟨67,34,112⟩, ⟨66,36,112⟩, ⟨67,35,112⟩, ⟨95,40,112⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (52 - r.j)

def allowance (top : ℕ) (k : Band) (j : ℕ) : ℕ :=
  indexBudget (start k) (factorCap top - reserve k) j

theorem factorCap_mono {a b : ℕ} (h : a ≤ b) (hb : b ≤ 14) : factorCap a ≤ factorCap b := by
  have ha := h.trans hb
  interval_cases a <;> interval_cases b <;> decide

theorem allowance_mono {a b j : ℕ} (k : Band) (h : a ≤ b) (hb : b ≤ 14) :
    allowance a k j ≤ allowance b k j :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (factorCap_mono h hb) _))

theorem order_pos (k : Band) (x : Shape) : 0 < order k x :=
  (P0_9_8.orderFor_select x.b x.j (thresholds k)).1

theorem order_mono (k : Band) {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    order k x ≤ order k y := P0_9_8.orderFor_mono hb hj _
end Final50PriceCaps
