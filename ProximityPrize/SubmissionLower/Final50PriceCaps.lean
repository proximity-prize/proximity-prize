import ProximityPrize.SubmissionLower.Final50PriceRetained

namespace Final50PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one3 | one4 | one5 | one6 | one7 | two6a | two6b | two6c | two6d | two7a | two7b deriving DecidableEq
abbrev budget : ℕ := 272987140666765598
def factorCap (top : ℕ) : ℕ := budget - Final50Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one3 => 16501552670860878
  | .one4 => 28094873359840834
  | .one5 => 42519075367271737
  | .one6 => 49097136154047103
  | .one7 => 43238236495066495
  | .two6a => 75965195419107675
  | .two6b => 130245870501792300
  | .two6c => 152519255545335898
  | .two6d => 175215881615097912
  | .two7a => 137738665506187659
  | .two7b => 170357050644059833

def start : Band → Shape
  | .empty => ⟨0,0,0⟩
  | .one3 => ⟨1,3,1⟩
  | .one4 => ⟨2,4,1⟩
  | .one5 => ⟨2,5,1⟩
  | .one6 => ⟨2,6,1⟩
  | .one7 => ⟨3,7,1⟩
  | .two6a => ⟨2,6,2⟩
  | .two6b => ⟨7,6,2⟩
  | .two6c => ⟨12,6,2⟩
  | .two6d => ⟨14,6,2⟩
  | .two7a => ⟨3,7,2⟩
  | .two7b => ⟨6,7,2⟩

def activeCap (k : Band) : ℕ :=
  162 - max (start k).b (2 * (((start k).j + 2) / 3))

def Admits (k : Band) (r : Shape) : Prop :=
  InBox (start k) r ∧ r.j = (start k).j ∧ r.t = (start k).t ∧
    (k = .two6a → r.b ≤ 6) ∧ (k = .two6b → r.b ≤ 11) ∧ (k = .two6c → r.b ≤ 13) ∧ (k = .two7a → r.b ≤ 5) ∧ (k = .empty → r = zeroShape)

def thresholds : Band → List Threshold
  | .empty => [⟨3,9,8⟩, ⟨4,10,13⟩, ⟨4,12,20⟩, ⟨10,8,7⟩, ⟨11,7,2⟩, ⟨5,15,27⟩, ⟨6,18,31⟩, ⟨18,6,3⟩, ⟨8,24,37⟩, ⟨33,5,16⟩, ⟨33,6,18⟩, ⟨34,9,24⟩, ⟨13,39,44⟩, ⟨64,4,31⟩, ⟨64,5,32⟩, ⟨64,6,33⟩, ⟨65,7,34⟩, ⟨65,9,35⟩, ⟨65,10,35⟩, ⟨65,12,36⟩, ⟨66,16,38⟩, ⟨66,18,39⟩, ⟨67,20,40⟩, ⟨66,22,41⟩, ⟨66,24,42⟩, ⟨67,28,43⟩, ⟨68,27,43⟩, ⟨68,30,43⟩, ⟨68,33,44⟩, ⟨69,45,47⟩, ⟨71,43,46⟩, ⟨69,49,47⟩, ⟨97,28,44⟩, ⟨98,31,45⟩, ⟨84,46,47⟩, ⟨97,36,46⟩, ⟨97,37,46⟩, ⟨98,44,47⟩, ⟨105,43,47⟩, ⟨98,52,48⟩, ⟨112,41,47⟩, ⟨105,51,48⟩, ⟨119,40,47⟩, ⟨111,50,48⟩, ⟨116,49,48⟩, ⟨122,48,48⟩, ⟨129,53,49⟩]
  | .one3 => [⟨2,5,4⟩, ⟨2,6,12⟩, ⟨3,9,28⟩, ⟨5,15,42⟩, ⟨7,20,47⟩, ⟨8,24,50⟩, ⟨64,4,42⟩, ⟨64,5,43⟩, ⟨65,15,49⟩, ⟨68,28,54⟩, ⟨67,33,55⟩, ⟨69,34,56⟩, ⟨69,37,56⟩, ⟨97,46,58⟩]
  | .one4 => [⟨2,4,6⟩, ⟨2,5,16⟩, ⟨2,6,23⟩, ⟨3,9,37⟩, ⟨4,12,45⟩, ⟨5,15,49⟩, ⟨6,17,52⟩, ⟨9,27,58⟩, ⟨67,26,60⟩, ⟨67,38,63⟩, ⟨67,39,63⟩]
  | .one5 => [⟨1,3,6⟩, ⟨2,5,29⟩, ⟨2,6,35⟩, ⟨3,9,47⟩, ⟨5,15,58⟩, ⟨7,19,62⟩, ⟨8,24,65⟩, ⟨13,39,69⟩, ⟨67,37,70⟩, ⟨69,38,70⟩]
  | .one6 => [⟨1,3,26⟩, ⟨2,6,51⟩, ⟨6,18,73⟩, ⟨11,33,79⟩]
  | .one7 => [⟨1,3,63⟩, ⟨2,6,81⟩, ⟨4,12,92⟩, ⟨8,24,100⟩]
  | .two6a => [⟨1,3,26⟩, ⟨2,6,51⟩, ⟨4,12,66⟩, ⟨6,18,73⟩, ⟨7,19,73⟩, ⟨7,21,74⟩, ⟨65,17,75⟩, ⟨66,30,79⟩, ⟨68,35,80⟩, ⟨67,39,80⟩, ⟨96,36,80⟩, ⟨96,43,81⟩, ⟨110,42,81⟩]
  | .two6b => [⟨1,3,42⟩, ⟨2,6,64⟩, ⟨4,12,79⟩, ⟨6,18,85⟩, ⟨7,19,85⟩, ⟨7,21,86⟩, ⟨65,17,87⟩, ⟨66,30,91⟩, ⟨68,35,92⟩, ⟨67,39,92⟩, ⟨96,36,92⟩, ⟨96,43,93⟩, ⟨110,42,93⟩]
  | .two6c => [⟨1,3,72⟩, ⟨3,9,99⟩, ⟨5,14,105⟩, ⟨63,33,114⟩, ⟨63,36,114⟩, ⟨62,39,114⟩, ⟨89,40,115⟩, ⟨89,45,115⟩, ⟨101,42,115⟩]
  | .two6d => [⟨1,3,99⟩, ⟨3,9,121⟩, ⟨5,14,127⟩, ⟨63,33,134⟩, ⟨63,36,135⟩, ⟨62,39,135⟩, ⟨89,40,135⟩, ⟨89,45,136⟩, ⟨101,42,136⟩]
  | .two7a => [⟨1,3,63⟩, ⟨4,11,91⟩, ⟨4,12,92⟩, ⟨7,19,98⟩, ⟨8,23,99⟩, ⟨66,32,102⟩, ⟨67,34,102⟩, ⟨66,36,103⟩, ⟨67,35,103⟩, ⟨95,40,103⟩]
  | .two7b => [⟨1,3,85⟩, ⟨4,11,109⟩, ⟨4,12,110⟩, ⟨7,19,115⟩, ⟨8,23,116⟩, ⟨66,32,119⟩, ⟨67,34,119⟩, ⟨66,36,119⟩, ⟨67,35,119⟩, ⟨95,40,120⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (53 - r.j)

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
