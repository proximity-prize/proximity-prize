import ProximityPrize.SubmissionLower.BF
set_option Elab.async false
set_option autoImplicit true
section
namespace fP
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
private theorem dfL (n:ℕ) (f :ℕ→ℕ) :
 qI (n+1) f=qI n f+f n:=rfl
theorem aAr (a b:ℕ) (f :ℕ→ℕ) :
   qI (a+b) f=qI a f+qI b (fun i=>f (i+a)) := by
 induction b with
 | zero=>simp [qI]
 | succ b ih =>
   rw [Nat.add_succ,dfL,ih,dfL,Nat.add_assoc,Nat.add_comm a b]
end fP
end
