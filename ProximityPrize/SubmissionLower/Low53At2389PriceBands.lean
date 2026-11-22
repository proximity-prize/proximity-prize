import ProximityPrize.SubmissionLower.Low53At2389Price

set_option Elab.async false
namespace Low53At2389PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)

inductive Band where
  | empty
  | one3 | one4 | one5 | one6 | one7
  | two6 (width : Fin 15)
  | two7 (width : Fin 8)
  deriving DecidableEq

abbrev budget : ℕ := 272512621865518327
def factorCap (top : ℕ) : ℕ := budget - Low53At2389Price.lowerCap top

def start : Band → Shape
  | .empty => ⟨0,0,0⟩
  | .one3 => ⟨1,3,1⟩
  | .one4 => ⟨2,4,1⟩
  | .one5 => ⟨2,5,1⟩
  | .one6 => ⟨2,6,1⟩
  | .one7 => ⟨3,7,1⟩
  | .two6 w => ⟨w.val+2,6,2⟩
  | .two7 w => ⟨w.val+3,7,2⟩

def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 => 16671246871199349
  | 1, 4 => 29770896776810809
  | 1, 5 => 44907703023627076
  | 1, 6 => 52127268172174955
  | 1, 7 => 46972353572019977
  | 2, 6 => (match b with
      | 2 => 75922339528029909
      | 3 => 75922339528029919
      | 4 => 75922339528029933
      | 5 => 75922339528029951
      | 6 => 75922339528029973
      | 7 => 86606330925471391
      | 8 => 97344829823969215
      | 9 => 108146386418511441
      | 10 => 119019550904086072
      | 11 => 129972873475681106
      | 12 => 141014904328284545
      | 13 => 152154193656884387
      | 14 => 163399291656468634
      | 15 => 174758748522025285
      | 16 => 186241114448542339
      | _ => 0)
  | 2, 7 => (match b with
      | 3 => 137444269250842341
      | 4 => 137444269250842355
      | 5 => 137444269250842373
      | 6 => 137444269250842395
      | 7 => 137444269250842421
      | 8 => 153641362727092699
      | 9 => 169901513899387382
      | 10 => 186233272962714469
      | _ => 0)
  | _, _ => 0

def reserve (k : Band) : ℕ := charge (start k).b (start k).j (start k).t

def activeCap (k : Band) : ℕ :=
  160 - max (start k).b (2 * (((start k).j + 2) / 3))

def Admits (k : Band) (r : Shape) : Prop :=
  InBox (start k) r ∧ r.j = (start k).j ∧ r.t = (start k).t ∧
    ((start k).t = 2 → r.b = (start k).b) ∧ (k = .empty → r = zeroShape)

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (53 - r.j)

def allowance (top : ℕ) (k : Band) (j : ℕ) : ℕ :=
  indexBudget (start k) (factorCap top - reserve k) j

theorem factorCap_mono {a b : ℕ} (h : a ≤ b) (hb : b ≤ 13) : factorCap a ≤ factorCap b := by
  have ha := h.trans hb
  interval_cases a <;> interval_cases b <;> decide

theorem allowance_mono {a b j : ℕ} (k : Band) (h : a ≤ b) (hb : b ≤ 13) :
    allowance a k j ≤ allowance b k j :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (factorCap_mono h hb) _))

theorem start_or_index (k : Band) : start k = zeroShape ∨ 0 < (start k).j := by
  cases k <;> simp [start, zeroShape]

theorem start_index (k : Band) : (start k).j ≤ 7 := by
  cases k <;> simp [start]

theorem reserve_le (k : Band) {top : ℕ} (htop : top ≤ 13) : reserve k ≤ factorCap top := by
  apply Nat.le_trans _ (factorCap_mono (Nat.zero_le top) htop)
  cases k with
  | two6 w => fin_cases w <;> decide
  | two7 w => fin_cases w <;> decide
  | _ => decide

theorem charge_eq {k : Band} {r : Shape} (h : Admits k r) :
    charge r.b r.j r.t = reserve k := by
  obtain ⟨_, hj, ht, hb, _⟩ := h
  rw [hj, ht]
  cases k
  all_goals
    first
    | rfl
    | rw [hb rfl]
      rfl

end Low53At2389PriceCaps
