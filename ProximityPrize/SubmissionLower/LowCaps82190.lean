import ProximityPrize.SubmissionLower.LowPriceData82190

set_option Elab.async false
namespace LowCaps82190
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold orderFor)
inductive Band | empty | one | two deriving DecidableEq
inductive Tier | small | large

def topCap : Tier → ℕ
  | .small => 8
  | .large => 12

def factorCap : Tier → ℕ
  | .small => 248322016488823220
  | .large => 254842395760710603

def box (tier : Tier) : Shape := ⟨120, 48, topCap tier⟩

def reserve : Band → ℕ
  | .empty => 0
  | .one => 34300000000000000
  | .two => 122000000000000000

def start : Band → Shape
  | .empty => zeroShape
  | .one => P0_9_8.oneStart
  | .two => P0_9_8.twoStart

def thresholds : Band → List Threshold
  | .empty => [⟨3,9,11⟩, ⟨5,15,30⟩, ⟨17,6,6⟩, ⟨9,26,42⟩, ⟨32,5,18⟩, ⟨62,4,34⟩, ⟨65,32,47⟩, ⟨94,41,50⟩, ⟨115,48,51⟩]
  | .one => [⟨2,5,9⟩, ⟨2,6,17⟩, ⟨3,9,33⟩, ⟨5,14,45⟩, ⟨9,25,56⟩, ⟨61,4,46⟩]
  | .two => [⟨1,3,41⟩, ⟨5,13,80⟩, ⟨65,38,92⟩]

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

def allowance (tier : Tier) (k : Band) (j : ℕ) : ℕ := P0_9_8.indexBudget (start k) (factorCap tier - reserve k) j

theorem order_pos (k : Band) (x : Shape) : 0 < order k x :=
  (P0_9_8.orderFor_select x.b x.j (thresholds k)).1
theorem order_mono (k : Band) {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    order k x ≤ order k y := P0_9_8.orderFor_mono hb hj _
end LowCaps82190
