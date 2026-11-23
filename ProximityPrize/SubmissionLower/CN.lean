import ProximityPrize.SubmissionLower.Q
import ProximityPrize.SubmissionLower.CL
set_option Elab.async false
set_option autoImplicit true
section
namespace aBa
open K1 cu gT Finset
private theorem bid (a b:ℤ) (n:ℕ) :
   2*(∑ j∈range n,(a+b*(j:ℤ))) =
     n*(2*a+b*((n:ℤ) - 1)) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   push_cast
   ring
private def bJH (k d:ℕ) :ℕ :=
 let n:=min k ((d+1)/2)
 n*(d+1 - n)
private def bfM (s :Shape) :ℕ :=
 triangle s.U*262144 *
  ∑ q∈range (s.B+1),bJH (min q s.J+1) (s.m+min q s.J - q)
private def aWs (s :Shape) :ℕ :=
 2*(s.U + 1) * ∑ q∈range (s.B+1),(min q s.J+1)*((s.B+s.J - q)*(s.B - q))
private def bP2 (s :Shape) :ℤ :=
 ∑ q∈range (s.B+1),(((min q s.J:ℕ) :ℤ)+1) *
   (2*((s.m:ℤ)*180265-(q:ℤ)*131071)+min q s.J)
private def agu (s :Shape) (r mode :ℕ) :ℤ :=
 ∑ q∈range (s.B+1),(((min q s.J:ℕ) :ℤ)+1) *
   (2*((q:ℤ) - 2*r) - 2*mode*min q s.J)
private def byO (s :Shape) :ℤ:=(s.m:ℤ)*180265-(s.B:ℤ)*131071
private def byP (s :Shape) (r :ℕ) :ℤ:=(s.B:ℤ) - 2*r
private def bxk (s :Shape) :ℤ:=(triangle s.U:ℤ)*bP2 s - 2*bfM s
private def bxl (s :Shape) (r mode :ℕ) :ℤ :=
 (triangle s.U:ℤ)*agu s r mode - 2*aWs s
private def Certificate (s :Shape) (r mode :ℕ) :Prop :=
 0<byO s+2601*byP s r ∧
 0<byO s+3554*byP s r ∧
 0<bxk s+2601*bxl s r mode ∧
 0<bxk s+3554*bxl s r mode
private def bjl (s :Ls) :Prop :=
 Certificate s.cheap s.dI 0∧Certificate s.layered s.dI 1∧s.cheap.U<p
private instance (s :Ls) :Decidable (bjl s) := by
 unfold bjl Certificate
 infer_instance
section
set_option maxHeartbeats 0
set_option maxRecDepth 16000
end
end aBa
end
