import ProximityPrize.SubmissionLower.RectAsymmetricNode

set_option autoImplicit false
set_option Elab.async false

namespace RectAsymmetric

private theorem transfer_le {a b c : ℕ} (hc : c ≤ a - b) :
    a*b ≤ (a-c)*(b+c) := by
  by_cases hzero : c = 0
  · simp [hzero]
  have hac : c ≤ a := hc.trans (Nat.sub_le _ _)
  have hbc : b ≤ a-c := by omega
  calc
    a*b = (a-c)*b + c*b := by rw [← Nat.add_mul, Nat.sub_add_cancel hac]
    _ ≤ (a-c)*b + (a-c)*c := by
      apply Nat.add_le_add_left
      rw [Nat.mul_comm (a-c) c]
      exact Nat.mul_le_mul_left c hbc
    _ = (a-c)*(b+c) := by rw [Nat.mul_add]

/-- Place the larger seed degree on the shorter side of the bank. At fixed
total seed degree, the balanced split then gives an upper bound on the surviving area. -/
theorem slots_le_balanced {u v x y V : ℕ} (huv : v ≤ u) (hxy : x ≤ y) (hV : V ≤ x+y)
    (r : ℕ) : (u+1-r*x)*(v+1-r*y) ≤
      (u+1-r*(V/2))*(v+1-r*((V+1)/2)) := by
  by_cases hz : v+1 ≤ r*y
  · rw [Nat.sub_eq_zero_of_le hz, Nat.mul_zero]
    exact Nat.zero_le _
  let b := (x+y)/2
  let d := (x+y+1)/2
  have hxb : x ≤ b := by dsimp [b]; omega
  have hby : b ≤ y := by dsimp [b]; omega
  have hdy : d ≤ y := by dsimp [d]; omega
  have hb := Nat.mul_le_mul_left r hxb
  have hy := Nat.mul_le_mul_left r hby
  have hd := Nat.mul_le_mul_left r hdy
  have hsum : r*b + r*d = r*x + r*y := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    have hbd : b+d = x+y := by dsimp [b, d]; omega
    rw [hbd]
  have htransfer : r*b-r*x ≤ (u+1-r*x)-(v+1-r*y) := by omega
  have hleft : (u+1-r*x)-(r*b-r*x) = u+1-r*b := by omega
  have hright : (v+1-r*y)+(r*b-r*x) = v+1-r*d := by omega
  have hB : V/2 ≤ b := by dsimp [b]; omega
  have hD : (V+1)/2 ≤ d := by dsimp [d]; omega
  calc
    _ ≤ ((u+1-r*x)-(r*b-r*x))*((v+1-r*y)+(r*b-r*x)) := transfer_le htransfer
    _ = (u+1-r*b)*(v+1-r*d) := by rw [hleft, hright]
    _ ≤ _ := Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r hB) _)
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left r hD) _)

open K1_14 (Shape shapeSum)

theorem rectPhysicalDebit_equal (s : Shape) (u : ℕ) :
    rectPhysicalDebit s u u =
      (u+1)^2*262144*shapeSum s (fun q k => s.m+min q s.J-(q+2*k)) := by
  rw [rectPhysicalDebit, pow_two]

/-- A shorter cap strictly reduces the node debit compared with padding that
cap to the longer side, when the node test space has positive size. -/
theorem rectPhysicalDebit_lt_padded (s : Shape) {u v : ℕ} (h : u<v)
    (hs : 0 < shapeSum s (fun q k => s.m+min q s.J-(q+2*k))) :
    rectPhysicalDebit s u v < rectPhysicalDebit s v v := by
  unfold rectPhysicalDebit
  exact Nat.mul_lt_mul_of_pos_right
    (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by omega)
      (Nat.succ_pos v)) (by decide)) hs

#print axioms slots_le_balanced
end RectAsymmetric
