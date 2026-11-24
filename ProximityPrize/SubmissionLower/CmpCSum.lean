import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
set_option Elab.async false
set_option autoImplicit true
namespace CmpC
def asum (f :ℕ→ℤ) :ℕ→ℤ
 | 0=>0
 | n+1=>asum f n+f n
theorem asum_add (f :ℕ→ℤ) (m n:ℕ) :
   asum f (m+n)=asum f m+asum (fun k=>f (m+k)) n:= by
 induction n with
 | zero=>simp [asum]
 | succ n ih=>rw [← Nat.add_assoc,asum,ih,asum,Int.add_assoc]
def SegLE (f :ℕ→ℤ) (m a :ℕ) (L:List ℕ) (s :ℕ) :Prop :=
 ∀ i<L.length,asum (fun k=>f (m*(a+i)+k)) m≤(L.getD i 0:ℤ)*s
theorem SegLE.sum {f :ℕ→ℤ} {m s :ℕ} {L:List ℕ} (h:SegLE f m 0 L s) :
   asum f (m*L.length)≤asum (fun i=>(L.getD i 0:ℤ)*s) L.length:= by
 suffices ∀ n≤L.length,asum f (m*n)≤asum (fun i=>(L.getD i 0:ℤ)*s) n from this _ le_rfl
 intro n
 induction n with
 | zero=>intro _; exact le_rfl
 | succ n ih =>
   intro hn
   have :=h n (by omega)
   rw [Nat.zero_add] at this
   rw [Nat.mul_succ,asum_add,asum]
   exact Int.add_le_add (ih (by omega)) this
end CmpC
