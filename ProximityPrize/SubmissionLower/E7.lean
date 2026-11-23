import ProximityPrize.SubmissionLower.ZNc0LBb
set_option Elab.async false
set_option autoImplicit true
section
namespace dn4
open Finset
private def row (x y z :ℤ) (q n:ℕ) :ℤ :=
 (n:ℤ)*(x+y*q+z*((n:ℤ)-1))
private def aJm (x y z :ℤ) (n:ℕ) :ℤ :=
 (n:ℤ)*((n:ℤ)+1)*(3*x+2*(y+z)*((n:ℤ)-1))
private def level (x y z :ℤ) (J n:ℕ) :ℤ :=
 3*(n:ℤ)*((J:ℤ)+1)*(2*(x+(y+z)*J)+y*((n:ℤ)-1))
private theorem df7 (x y z :ℤ) (n:ℕ) :
   6*(∑ q∈range n,row x y z q (q+1))=aJm x y z n:= by
 induction n with
 | zero=>simp [aJm]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   simp only [aJm,row,Nat.cast_succ]
   ring
private theorem df3 (x y z :ℤ) (J n:ℕ) :
   6*(∑ i∈range n,row x y z (J+i) (J+1))=level x y z J n:= by
 induction n with
 | zero=>simp [level]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   simp only [level,row,Nat.cast_succ,Nat.cast_add]
   ring
private def bhM (f :ℕ→ℤ) (k :ℕ) :ℕ→ℤ
 | 0=>0
 | n+1=>bhM f k n+f (k+n)
private theorem dgC (f :ℕ→ℤ) (k n:ℕ) :
   bhM f k n = ∑ i∈range n,f (k+i) := by
 induction n with
 | zero=>simp [bhM]
 | succ n ih=>rw [bhM,sum_range_succ,ih]
private theorem cck {x y lo hi h:ℤ} (hl:lo≤h) (hu:h≤hi)
   (h₀:0<x) (h₁:0<x+(hi-lo)*y) :0<x+(h-lo)*y := by
 by_cases hy :0≤y
 · exact add_pos_of_pos_of_nonneg h₀ (mul_nonneg (sub_nonneg.mpr hl) hy)
 · nlinarith only [h₁,mul_nonneg (sub_nonneg.mpr hu) (neg_nonneg.mpr (le_of_not_ge hy))]
end dn4
end
