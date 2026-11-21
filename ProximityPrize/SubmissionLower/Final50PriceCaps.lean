import ProximityPrize.SubmissionLower.Final50PriceRetained

set_option Elab.async false
namespace Final50PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one3 | one4 | one5 | one6 | one7 | two6thin | two6wide | two7 deriving DecidableEq
abbrev budget : ℕ := 272535931964746069
def factorCap (top : ℕ) : ℕ := budget - Final50Price.lowerCap top
def reserve : Band → ℕ
  | .empty => 0
  | .one3 => 15914074546309650
  | .one4 => 26847657578113869
  | .one5 => 40493490790958688
  | .one6 => 46693082013552099
  | .one7 => 41086480414160068
  | .two6thin => 123860782663131328
  | .two6wide => 166739208706393408
  | .two7 => 161967347187663841
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
  | .empty => [⟨3,9,7⟩, ⟨4,10,12⟩, ⟨4,12,14⟩, ⟨10,8,2⟩, ⟨11,7,2⟩, ⟨5,15,26⟩, ⟨6,18,30⟩, ⟨18,6,3⟩, ⟨8,24,37⟩, ⟨33,5,3⟩, ⟨33,6,6⟩, ⟨34,9,12⟩, ⟨13,39,44⟩, ⟨64,4,2⟩, ⟨64,5,6⟩, ⟨64,6,11⟩, ⟨65,7,12⟩, ⟨65,9,23⟩, ⟨65,10,24⟩, ⟨65,12,26⟩, ⟨66,16,29⟩, ⟨66,18,32⟩, ⟨67,20,34⟩, ⟨66,22,35⟩, ⟨66,24,38⟩, ⟨67,28,40⟩, ⟨68,27,40⟩, ⟨68,30,43⟩, ⟨68,33,44⟩, ⟨69,45,46⟩, ⟨71,43,46⟩, ⟨69,49,47⟩, ⟨97,28,43⟩, ⟨98,31,45⟩, ⟨84,46,47⟩, ⟨97,36,45⟩, ⟨97,37,46⟩, ⟨98,44,47⟩, ⟨105,43,47⟩, ⟨98,52,48⟩, ⟨112,41,47⟩, ⟨105,51,48⟩, ⟨119,40,47⟩, ⟨111,50,48⟩, ⟨116,49,48⟩, ⟨122,48,48⟩]
  | .one3 => [⟨2,5,2⟩, ⟨2,6,10⟩, ⟨3,9,23⟩, ⟨5,15,38⟩, ⟨7,20,46⟩, ⟨8,24,47⟩, ⟨64,4,2⟩, ⟨64,5,4⟩, ⟨65,15,47⟩, ⟨68,28,54⟩, ⟨67,33,49⟩, ⟨69,34,55⟩, ⟨69,37,56⟩, ⟨97,46,57⟩]
  | .one4 => [⟨2,4,2⟩, ⟨2,5,4⟩, ⟨2,6,21⟩, ⟨3,9,23⟩, ⟨4,12,41⟩, ⟨5,15,44⟩, ⟨6,17,47⟩, ⟨9,27,57⟩, ⟨67,26,54⟩, ⟨67,38,60⟩, ⟨67,39,62⟩]
  | .one5 => [⟨1,3,3⟩, ⟨2,5,4⟩, ⟨2,6,22⟩, ⟨3,9,41⟩, ⟨5,15,46⟩, ⟨7,19,47⟩, ⟨8,24,60⟩, ⟨13,39,67⟩, ⟨67,37,62⟩, ⟨69,38,69⟩]
  | .one6 => [⟨1,3,22⟩, ⟨2,6,49⟩, ⟨6,18,67⟩, ⟨11,33,77⟩]
  | .one7 => [⟨1,3,21⟩, ⟨2,6,40⟩, ⟨4,12,73⟩, ⟨8,24,95⟩]
  | .two6thin => [⟨1,3,9⟩, ⟨2,6,35⟩, ⟨4,12,60⟩, ⟨6,18,62⟩, ⟨7,19,69⟩, ⟨7,21,73⟩, ⟨65,17,71⟩, ⟨66,30,74⟩, ⟨68,35,75⟩, ⟨67,39,78⟩, ⟨96,36,78⟩, ⟨96,43,80⟩, ⟨110,42,80⟩]
  | .two6wide => [⟨1,3,48⟩, ⟨3,9,88⟩, ⟨5,14,100⟩, ⟨63,33,109⟩, ⟨63,36,110⟩, ⟨62,39,102⟩, ⟨89,40,111⟩, ⟨89,45,112⟩, ⟨101,42,112⟩]
  | .two7 => [⟨1,3,48⟩, ⟨4,11,49⟩, ⟨4,12,81⟩, ⟨7,19,94⟩, ⟨8,23,96⟩, ⟨66,32,97⟩, ⟨67,34,98⟩, ⟨66,36,98⟩, ⟨67,35,100⟩, ⟨95,40,101⟩]

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
