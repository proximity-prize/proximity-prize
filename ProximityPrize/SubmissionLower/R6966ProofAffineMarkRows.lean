import ProximityPrize.SubmissionLower.R6966ProofOdeSurfaceBridge
import ProximityPrize.SubmissionLower.R6966ProofWordUnconstrainedPrice

set_option Elab.async false

namespace Research6966.AffineMarkRows
open Polynomial Finset
open NonlinearMarkRows (Eqn evaluate)
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds GenericPhysicalCentre.physical

abbrev S (σ F:Type*) [CommSemiring F] := MvPolynomial σ F
private abbrev within (w:σ→ℕ) (u:ℕ) := MvPolynomial.restrictWeightAtMost (R:=F) w u

private theorem dx {w:σ→ℕ} {u:ℕ} {P:S σ F} (cap:P∈within w u) : Differential.deriv P∈within w u := by
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro e he
  apply MvPolynomial.mem_restrictWeightAtMost.mp cap e (MvPolynomial.mem_support_iff.mpr ?_)
  intro z
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,z,map_zero])

theorem pair_cap (w:σ→ℕ) (A B C₀:S σ F) (u n:ℕ) (hA:A∈within w u) (hB:B∈within w u) (hC:C₀∈within w u) :
    (AffineODE.pair Differential.deriv A B C₀ n).1∈within w (n*u) ∧
      (AffineODE.pair Differential.deriv A B C₀ n).2∈within w (n*u) := by
  induction n with
  | zero=>
    simp only [AffineODE.pair,zero_mul]
    exact ⟨MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl (1:F),Submodule.zero_mem _⟩
  | succ n ih=>
    have step {l m g:S σ F} (hl:l∈within w (n*u)) (hm:m∈within w (n*u)) (hg:g∈within w u) :
        A*Differential.deriv m-(n:S σ F)*Differential.deriv A*m+g*l∈within w ((n+1)*u) := by
      rw [Nat.succ_mul,Nat.add_comm (n*u) u]
      apply Submodule.add_mem _ _ (MvPolynomial.mul_mem_restrictWeightAtMost hg hl)
      apply Submodule.sub_mem _ (MvPolynomial.mul_mem_restrictWeightAtMost hA (dx hm))
      rw [mul_assoc,←nsmul_eq_mul]
      exact nsmul_mem (MvPolynomial.mul_mem_restrictWeightAtMost (dx hA) hm) n
    exact ⟨step ih.1 ih.1 hB,step ih.1 ih.2 hC⟩

private theorem response_cap (w:σ→ℕ) (A:S σ F) (u d:ℕ) (weights:ℕ→F) (P:ℕ→S σ F)
    (hA:A∈within w u) (hP:∀i,P i∈within w (i*u)) :
    AffineODE.response d (fun i=>MvPolynomial.C (weights i)) A P∈within w (d*u) := by
  unfold AffineODE.response
  apply Submodule.sum_mem
  intro j hj
  rw [mul_assoc,←MvPolynomial.smul_eq_C_mul]
  apply Submodule.smul_mem
  have cap:=MvPolynomial.mul_mem_restrictWeightAtMost (MvPolynomial.pow_mem_restrictWeightAtMost hA (d-j)) (hP j)
  have cast : (d-j) • u + j*u=d*u := by
    change (d-j)*u+j*u=d*u
    rw [←Nat.add_mul,Nat.sub_add_cancel (Nat.le_of_lt_succ (mem_range.mp hj))]
  rwa [cast] at cap

def row (A B C₀:S σ F) (d:ℕ) (origin x received:F) : Eqn σ F :=
  let wt:=fun i=>MvPolynomial.C ((x-origin)^i/(i.factorial:F))
  let lr:=AffineODE.response d wt A (fun i=>(AffineODE.pair Differential.deriv A B C₀ i).1)
  let cr:=AffineODE.response d wt A (fun i=>(AffineODE.pair Differential.deriv A B C₀ i).2)
  C lr*Polynomial.X+C (cr-MvPolynomial.C received*A^d)

private theorem linear_degree (a b:S σ F) : (C a*Polynomial.X+C b).natDegree≤1 :=
  (natDegree_add_le (C a*Polynomial.X) (C b)).trans
    (max_le ((show (C a*Polynomial.X).natDegree≤(C a).natDegree+(Polynomial.X:Eqn σ F).natDegree from natDegree_mul_le).trans (by simp))
      (by rw [natDegree_C];decide))

private theorem linear_cap {w:σ→ℕ} {u:ℕ} {a b:S σ F} (ha:a∈within w u) (hb:b∈within w u) :
    NonlinearMarkDegrees.cap w u (C a*Polynomial.X+C b) := by
  intro i
  rw [C_mul_X_eq_monomial,coeff_add,coeff_monomial,coeff_C,Finsupp.single_apply]
  split <;> split
  all_goals first
    | exact Submodule.add_mem _ ha hb
    | simpa only [zero_add,add_zero] using ha
    | simpa only [zero_add,add_zero] using hb
    | simpa only [zero_add] using (Submodule.zero_mem (within (F:=F) w u))

theorem row_degree (A B C₀:S σ F) (d:ℕ) (origin x received:F) :
    (row A B C₀ d origin x received).natDegree≤1 := by
  exact linear_degree _ _

theorem row_cap (w:σ→ℕ) (A B C₀:S σ F) (u d:ℕ) (hA:A∈within w u) (hB:B∈within w u) (hC:C₀∈within w u)
    (origin x received:F) : NonlinearMarkDegrees.cap w (d*u) (row A B C₀ d origin x received) := by
  let wt:=fun i:ℕ=>(x-origin)^i/(i.factorial:F)
  have lin:=response_cap w A u d wt _ hA (fun i=>(pair_cap w A B C₀ u i hA hB hC).1)
  have const:=response_cap w A u d wt _ hA (fun i=>(pair_cap w A B C₀ u i hA hB hC).2)
  have den:MvPolynomial.C received*A^d∈within w (d*u) := by
    rw [←MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (MvPolynomial.pow_mem_restrictWeightAtMost hA d)
  exact linear_cap lin (Submodule.sub_mem _ const den)

private theorem entries (p:σ→F) (fixed:∀ i,Differential.deriv (p i)=0) (A B C₀:S σ F) (y:F)
    (original:MvPolynomial.eval p A*Differential.deriv y=MvPolynomial.eval p B*y+MvPolynomial.eval p C₀) (i:ℕ) :
    MvPolynomial.eval p A^i*Differential.deriv^[i] y=
      MvPolynomial.eval p (AffineODE.pair Differential.deriv A B C₀ i).1*y+
      MvPolynomial.eval p (AffineODE.pair Differential.deriv A B C₀ i).2 := by
  exact AffineODE.cleared_derivatives Differential.deriv Differential.deriv.toAddMonoidHom (MvPolynomial.eval p)
    (by change Differential.deriv (1:F)=0;simp) (by
      intro a b
      change Differential.deriv (a*b)=Differential.deriv a*b+a*Differential.deriv b
      rw [Derivation.leibniz];simp [smul_eq_mul,mul_comm,add_comm])
    (GenericPhysicalCentre.deriv_eval p fixed) A B C₀ y original i

variable {K:Type*} [Field K]
private abbrev E:=GenericPhysicalCentre.Frac K
private abbrev incl:=algebraMap K[X] (E (K:=K))

theorem detects (p:σ→E (K:=K)) (fixed:∀i,Differential.deriv (p i)=0) (A B C₀:S σ E)
    (P:K[X]) (d:ℕ) (degree:P.natDegree≤d) (fac:∀ j≤d,(j.factorial:E (K:=K))≠0)
    (x received:E (K:=K)) (law:MvPolynomial.eval p A*incl P.derivative=MvPolynomial.eval p B*incl P+MvPolynomial.eval p C₀)
    (den:MvPolynomial.eval p A≠0) :
    evaluate p (incl P) (row A B C₀ d (incl Polynomial.X) x received)=0 ↔
      (P.map (algebraMap K _)).eval x=received := by
  let y:=incl P
  let D: E (K:=K)→+E (K:=K):=Differential.deriv.toAddMonoidHom
  let ev:=MvPolynomial.eval p
  let wt (i:ℕ):S σ (E (K:=K)):=MvPolynomial.C ((x-incl Polynomial.X)^i/(i.factorial:E (K:=K)))
  let data :=AffineODE.pair Differential.deriv A B C₀
  have original:ev A*D y=ev B*y+ev C₀:=by
    change ev A*Differential.deriv (incl P)=_
    rw [GenericPhysicalCentre.physical_poly];exact law
  have jet (i:ℕ):ev A^i*D^[i] y=ev (data i).1*y+ev (data i).2 :=
    entries p fixed A B C₀ y original i
  have full:=AffineODE.common_denominator A ev y (fun i=>(data i).1) (fun i=>(data i).2) (fun i=>D^[i] y) d wt (fun i _=>jet i)
  have tay:=NonlinearMarkRows.taylor_at_generic P x d degree fac
  have scalar (i):ev (wt i)=(x-incl Polynomial.X)^i/(i.factorial:E (K:=K)):=MvPolynomial.eval_C _
  simp_rw [scalar] at full
  change ev A^d*(∑i∈range (d+1),((x-incl Polynomial.X)^i/(i.factorial:E (K:=K)))*Differential.deriv^[i] (incl P))=_ at full
  rw [←tay] at full
  let l:=AffineODE.response d wt A (fun i=>(data i).1)
  let m:=AffineODE.response d wt A (fun i=>(data i).2)
  change (eval₂RingHom ev y) (C l*Polynomial.X+C (m-MvPolynomial.C received*A^d))=0 ↔ _
  simp only [coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,eval₂_X]
  rw [map_sub ev,map_mul ev,map_pow ev,show ev (MvPolynomial.C received)=received from MvPolynomial.eval_C _]
  change ev (AffineODE.response d wt A _)*y+(ev (AffineODE.response d wt A _)-received*ev A^d)=0 ↔ _
  rw [←add_sub_assoc,←full,mul_comm received,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ den),sub_eq_zero]

end
end Research6966.AffineMarkRows
