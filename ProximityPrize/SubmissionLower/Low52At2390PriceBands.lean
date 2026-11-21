import ProximityPrize.SubmissionLower.Low52At2390Price

set_option Elab.async false
namespace Low52At2390PriceCaps
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape)

inductive Band where
  | empty
  | one3 | one4 | one5 | one6 | one7
  | two6 (width : Fin 15)
  | two7 (width : Fin 8)
  deriving DecidableEq

abbrev budget : ℕ := 272512621865518327
def factorCap (top : ℕ) : ℕ := budget - Low52At2390Price.lowerCap top

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
  | 1, 3 => 16384919681230529
  | 1, 4 => 29229708333932831
  | 1, 5 => 44075586509778549
  | 1, 6 => 51155110979973754
  | 1, 7 => 46074871544799642
  | 2, 6 => (match b with
      | 2 => 74494503259640670
      | 3 => 74494503259640680
      | 4 => 74494503259640694
      | 5 => 74494503259640712
      | 6 => 74494503259640734
      | 7 => 84995410426815001
      | 8 => 95550825911854592
      | 9 => 106169300037874387
      | 10 => 116859383127989265
      | 11 => 127629625505314108
      | 12 => 138488577492963795
      | 13 => 149444789414053205
      | 14 => 160506811591697221
      | 15 => 171683194349010719
      | 16 => 182982488009108582
      | _ => 0)
  | 2, 7 => (match b with
      | 3 => 134946834079433697
      | 4 => 134946834079433711
      | 5 => 134946834079433729
      | 6 => 134946834079433751
      | 7 => 134946834079433777
      | 8 => 150870877673617181
      | 9 => 166857979908780790
      | 10 => 182916691108039482
      | _ => 0)
  | _, _ => 0

def reserve (k : Band) : ℕ := charge (start k).b (start k).j (start k).t

def activeCap (k : Band) : ℕ :=
  158 - max (start k).b (2 * (((start k).j + 2) / 3))

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

end Low52At2390PriceCaps
