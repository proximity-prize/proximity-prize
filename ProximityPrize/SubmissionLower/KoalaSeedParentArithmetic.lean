import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace KoalaSeedParent

theorem share_capacity {active seed cap rate fee : ℚ}
    (hcap : active+seed ≤ cap) (hseed : 0 ≤ seed)
    (hfee : 0 ≤ fee) (hrate : fee ≤ rate) :
    rate*active+fee*seed ≤ rate*cap := by
  calc
    _ ≤ rate*active+rate*seed := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrate hseed)
    _ = rate*(active+seed) := by rw [mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (hfee.trans hrate)

theorem replace_first {joint rest rate seed fee points count : ℚ}
    (h : count ≤ joint - rate*seed + rest)
    (hcount : points ≤ fee*seed)
    (hseed : 0 ≤ seed) (hrate : fee ≤ rate) :
    count+points ≤ joint+rest := by
  have hd := mul_le_mul_of_nonneg_right hrate hseed
  linarith only [h,hcount,hd]

#print axioms share_capacity
#print axioms replace_first
end KoalaSeedParent
