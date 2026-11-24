import Mathlib.RingTheory.Binomial
import ProximityPrize.SubmissionLower.B0
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AJ
set_option Elab.async false
set_option autoImplicit true
section
namespace oT
open bu MvPolynomial

noncomputable section
abbrev Interpolant:=MvPolynomial (Fin 3) Ground
def weights (j:Fin 3) :ℕ:=j.val+1
abbrev Bounded (d:ℕ) :=restrictWeightedDegree (R:=Ground) weights d
def b9 (e :Exponent) :Interpolant →ₐ[Ground] Ground :=
 MvPolynomial.aeval fun j=>(e j.succ:Ground)
end
end oT
end
section
namespace oT
open bu MvPolynomial

open scoped BigOperators
set_option maxHeartbeats 600000
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
@[simp] theorem mC (e :Exponent) (r :Ground) :b9 e (C r)=r :=
  by simp [b9]
@[simp] theorem BD (e :Exponent) (j:Fin 3) :
   b9 e (MvPolynomial.X j)=(e j.succ:Ground) :=
  by simp [b9]
private def nY (Q:Polynomial Ground) (n:ℕ) :Ground :=
 (n.factorial:Ground)*Q.coeff n
theorem const_mem (d:ℕ) (x :Ground) :C x∈Bounded d :=
 C_mem_restrictWeightedDegree _ _ _
theorem mul_bounded {p q:Interpolant} {d e :ℕ}
  (hp:p∈Bounded d) (hq:q∈Bounded e) :p*q∈Bounded (d+e) :=
 mul_mem_restrictWeightedDegree hp hq
theorem aEi {ι:Type*} (d:ℕ) (s :Finset ι) (p:ι→ Interpolant)
   (h : ∀ i∈s,p i∈Bounded d) : ∏ i∈s,p i∈Bounded (s.card*d) := by
 classical
 induction s using Finset.induction_on with
 | empty=>simpa using const_mem 0 1
 | insert i s hi ih =>
   rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,add_comm]
   exact mul_bounded (h i (Finset.mem_insert_self _ _))
     (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
end
end oT
end
section
namespace oT
open bu MvPolynomial

open scoped BigOperators

noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def cU {R:Type*} [CommRing R] (n:ℕ) (x :R) :R :=
 ∏ i∈Finset.range n,(x-(i:R))
private theorem vT {R:Type*} [CommRing R] {n i:ℕ} (hi:i<n) :
  cU n (i:R)=0 :=
 Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)
private theorem fall_bound {w:ℕ} {p:Interpolant} (h:p∈Bounded w) (n:ℕ) :
  cU n p∈Bounded (n*w) := by
 unfold cU
 simpa only [Finset.card_range] using aEi w (Finset.range n)
  (fun i=>p-(i:Interpolant)) (fun i _=>(Bounded w).sub_mem h
    (by simpa only [map_natCast] using const_mem w (i:Ground)))
end
end oT
end
