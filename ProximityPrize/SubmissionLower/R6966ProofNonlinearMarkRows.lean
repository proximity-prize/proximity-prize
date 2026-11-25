import ProximityPrize.SubmissionLower.R6966ProofGenericPhysicalCentre
import ProximityPrize.SubmissionLower.R6966ProofAffineODE
import ArkLib.Data.MvPolynomial.WeightAtMost
import Mathlib.Algebra.MvPolynomial.Polynomial

set_option Elab.async false

namespace Research6966.NonlinearMarkRows
open Polynomial Finset
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 600000
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds

private abbrev S (σ F:Type*) [Field F] := MvPolynomial σ F
abbrev Eqn (σ F:Type*) [Field F] := (S σ F)[X]

def coeffRow (A B:Eqn σ F) (d:ℕ) : ℕ→Eqn σ F
  | 0=>Polynomial.X*A^(2*d-1)
  | j+1=>QuadraticWeight.numerator A B j*A^(2*d-1-(2*j+1))

def node (A B:Eqn σ F) (d:ℕ) (centre x received:F) : Eqn σ F :=
  (∑ j∈range (d+1),C (MvPolynomial.C ((x-centre)^j/(j.factorial:F)))*coeffRow A B d j)-
    C (MvPolynomial.C received)*A^(2*d-1)

def evaluate (p:σ→F) (y:F) : Eqn σ F→+*F:=eval₂RingHom (MvPolynomial.eval p) y

private theorem coeffRow_at (p:σ→F) (fixed:∀i,Differential.deriv (p i)=0) (y:F)
    (A B:Eqn σ F) (law:evaluate p y A*Differential.deriv y=evaluate p y B) (d j:ℕ) (le:j≤d) :
    evaluate p y (coeffRow A B d j)=(evaluate p y A)^(2*d-1)*Differential.deriv^[j] y := by
  cases j with
  | zero=>
    rw [coeffRow,map_mul,map_pow]
    change evaluate p y Polynomial.X*_=_*y
    rw [show evaluate p y Polynomial.X=y by simp [evaluate],mul_comm]
  | succ j=>
    letI : Algebra (S σ F) F := (MvPolynomial.eval p).toAlgebra
    letI : DifferentialAlgebra (S σ F) F := ⟨fun c=>GenericPhysicalCentre.deriv_eval p fixed c⟩
    have step:=QuadraticWeight.cleared A B y law j
    change (evaluate p y A)^(2*j+1)*Differential.deriv^[j+1] y=evaluate p y (QuadraticWeight.numerator A B j) at step
    rw [coeffRow,map_mul,map_pow,←step]
    have add:2*j+1+(2*d-1-(2*j+1))=2*d-1:=by omega
    rw [mul_right_comm,←pow_add,add]

variable {K:Type*} [Field K]
private abbrev Q:=GenericPhysicalCentre.Frac K
attribute [local instance] GenericPhysicalCentre.physical
private abbrev xi : Q (K:=K):=algebraMap K[X] (GenericPhysicalCentre.Frac K) Polynomial.X

private theorem generic_eval (P:K[X]) :
    (P.map (algebraMap K (GenericPhysicalCentre.Frac K))).eval xi=algebraMap K[X] (GenericPhysicalCentre.Frac K) P := by
  let E:=GenericPhysicalCentre.Frac K
  have eq:(evalRingHom (xi (K:=K))).comp (mapRingHom (algebraMap K E))=algebraMap K[X] E := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C,coe_evalRingHom,eval_C]
      exact IsScalarTower.algebraMap_apply K K[X] E c
    · simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_X,coe_evalRingHom,eval_X];rfl
  exact RingHom.congr_fun eq P

theorem taylor_at_generic (P:K[X]) (x:GenericPhysicalCentre.Frac K) (d:ℕ) (degree:P.natDegree≤d)
    (fac:∀ j≤d,(j.factorial:GenericPhysicalCentre.Frac K)≠0) :
    (P.map (algebraMap K _)).eval x=∑i∈range (d+1),((x-xi)^i/(i.factorial:GenericPhysicalCentre.Frac K))*
      Differential.deriv^[i] (algebraMap K[X] (GenericPhysicalCentre.Frac K) P) := by
  let E:=GenericPhysicalCentre.Frac K
  let y:=algebraMap K[X] E P
  have tay:=AffineODE.evaluation_from_derivatives (P.map (algebraMap K E)) xi x d
    (natDegree_map_le.trans degree) fac
  have jets (j:ℕ) : (Polynomial.derivative^[j] (P.map (algebraMap K E))).eval xi=Differential.deriv^[j] y := by
    have comm (l:ℕ) : (Polynomial.derivative^[l] (P.map (algebraMap K E)))=
        (Polynomial.derivative^[l] P).map (algebraMap K E) := by
      induction l with
      | zero=>rfl
      | succ l ih=>rw [Function.iterate_succ_apply',Function.iterate_succ_apply' (f:=Polynomial.derivative) (x:=P),ih,derivative_map]
    rw [comm,generic_eval,GenericPhysicalCentre.physical_iterate]
  simp_rw [jets] at tay
  exact tay

theorem detects (p:σ→GenericPhysicalCentre.Frac K) (fixed:∀i,Differential.deriv (p i)=0)
    (A B:Eqn σ (GenericPhysicalCentre.Frac K)) (P:K[X]) (d:ℕ) (degree:P.natDegree≤d)
    (fac:∀ j≤d,(j.factorial:GenericPhysicalCentre.Frac K)≠0) (x received:GenericPhysicalCentre.Frac K)
    (law:evaluate p (algebraMap K[X] _ P) A * algebraMap K[X] _ P.derivative =
      evaluate p (algebraMap K[X] _ P) B) (regular:evaluate p (algebraMap K[X] _ P) A≠0) :
    evaluate p (algebraMap K[X] _ P) (node A B d xi x received)=0 ↔
    (P.map (algebraMap K _)).eval x=received := by
  let E:=GenericPhysicalCentre.Frac K
  let y:=algebraMap K[X] E P
  let ev:=evaluate p y
  have ode: ev A*Differential.deriv y=ev B := by
    rw [show Differential.deriv y=algebraMap K[X] E P.derivative from GenericPhysicalCentre.physical_poly P]
    exact law
  have wt (c:E) : ev (C (MvPolynomial.C c))=c := by simp [ev,evaluate]
  have tay:=taylor_at_generic P x d degree fac
  change ev (node A B d xi x received)=0 ↔ _
  rw [node,map_sub,map_sum,map_mul,wt,map_pow]
  have sum:(∑j∈range (d+1),ev (C (MvPolynomial.C ((x-xi)^j/(j.factorial:E)))*coeffRow A B d j))=
      (ev A)^(2*d-1)*(P.map (algebraMap K E)).eval x := by
    rw [tay,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [map_mul,wt,show ev (coeffRow A B d j)=(ev A)^(2*d-1)*Differential.deriv^[j] y from
      coeffRow_at p fixed y A B ode d j (by simpa using hj)]
    ring
  rw [sum,mul_comm received,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ regular),sub_eq_zero]

#print axioms detects
end
end Research6966.NonlinearMarkRows
