import ProximityPrize.SubmissionLower.R6966ProofGenericPhysicalCentre
import ProximityPrize.SubmissionLower.R6966ProofWordUnconstrainedPrice
import ProximityPrize.SubmissionLower.R6966ProofAffineODE

set_option Elab.async false

namespace Research6966.FixedNodeRows
open Polynomial Finset Module
open WordSurfaceJets (Pol)
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false

variable {K σ:Type*} [Field K]
abbrev Coeff (σ K:Type*) [Field K] := MvPolynomial σ K[X]
abbrev Row (σ K:Type*) [Field K] := (Coeff σ K)[X]

private def makeDifferential {R:Type*} [CommRing R] (D:R→+R) (mul:∀a b,D (a*b)=a*D b+b*D a) : Differential R where
  deriv:=Derivation.mk' D.toIntLinearMap (fun a b=>mul a b)

@[instance_reducible] def ordinary (K:Type*) [Field K] : Differential K[X] :=
  makeDifferential Polynomial.derivative.toAddMonoidHom (fun a b=>by
    change (a*b).derivative=a*b.derivative+b*a.derivative
    rw [Polynomial.derivative_mul];ring)
attribute [local instance] ordinary GenericPhysicalCentre.seeds

def evaluate (z:σ→K) (y:K[X]) : Row σ K→+*K[X] :=
  eval₂RingHom (MvPolynomial.eval (fun i=>C (z i))) y

def centre (x y:K) : Row σ K→+*MvPolynomial σ K :=
  eval₂RingHom (MvPolynomial.map (evalRingHom x)) (MvPolynomial.C y)

theorem specialize (z:σ→K) (S:K[X]) (x:K) :
    (MvPolynomial.eval z).comp (centre x (S.eval x))=(evalRingHom x).comp (evaluate z S) := by
  apply Polynomial.ringHom_ext
  · intro p
    have base:(MvPolynomial.eval z).comp (MvPolynomial.map (evalRingHom x))=
        (evalRingHom x).comp (MvPolynomial.eval (fun i=>C (z i))) := by
      apply MvPolynomial.ringHom_ext
      · intro c;simp
      · intro i;simp
    simpa only [centre,evaluate,RingHom.comp_apply,coe_eval₂RingHom,eval₂_C] using RingHom.congr_fun base p
  · simp [centre,evaluate]

private theorem center_degree (x y:K) {P:Row σ K} {u:ℕ}
    (bound:∀ i,(P.coeff i).totalDegree≤u) : (centre x y P).totalDegree≤u := by
  change (P.eval₂ (MvPolynomial.map (evalRingHom x)) (MvPolynomial.C y)).totalDegree≤_
  rw [eval₂_eq_sum,Polynomial.sum_def]
  apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le _)
  intro i _
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [←map_pow,MvPolynomial.totalDegree_C,add_zero]
  exact (Finset.sup_mono (MvPolynomial.support_map_subset (evalRingHom x) (P.coeff i))).trans (bound i)

private theorem deriv_total (P:Coeff σ K) : (Differential.deriv P).totalDegree≤P.totalDegree := by
  apply Finset.sup_le
  intro e he
  apply MvPolynomial.le_totalDegree
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,zero,map_zero])

def coeffAt (A B:Row σ K) (d:ℕ) (x₀ y₀:K) : ℕ→MvPolynomial σ K
  | 0=>MvPolynomial.C y₀*(centre x₀ y₀ A)^(2*d-1)
  | j+1=>centre x₀ y₀ (QuadraticWeight.numerator A B j)*(centre x₀ y₀ A)^(2*d-1-(2*j+1))

def test (A B:Row σ K) (d:ℕ) (x₀ y₀ x answer:K) : MvPolynomial σ K :=
  (∑ j∈range (d+1),MvPolynomial.C ((x-x₀)^j/(j.factorial:K))*coeffAt A B d x₀ y₀ j)-
    MvPolynomial.C answer*(centre x₀ y₀ A)^(2*d-1)

theorem test_degree (A B:Row σ K) (d u:ℕ) (x₀ y₀ x answer:K) (ha:∀ i,(A.coeff i).totalDegree≤u)
    (hb:∀ i,(B.coeff i).totalDegree≤u) : (test A B d x₀ y₀ x answer).totalDegree≤(2*d-1)*u := by
  let k:=2*d-1
  have den:(centre x₀ y₀ A).totalDegree≤u:=center_degree x₀ y₀ ha
  have power (n:ℕ):((centre x₀ y₀ A)^n).totalDegree≤n*u :=
    (MvPolynomial.totalDegree_pow ..).trans (Nat.mul_le_mul_left n den)
  have cap (j:ℕ) (le:j≤d):(coeffAt A B d x₀ y₀ j).totalDegree≤k*u := by
    cases j with
    | zero=>exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact power k)
    | succ j=>
      have num:=center_degree x₀ y₀ (QuadraticWeight.coefficient_degree A B u deriv_total ha hb j)
      exact (MvPolynomial.totalDegree_mul ..).trans
        ((Nat.add_le_add num (power (k-(2*j+1)))).trans_eq (by rw [←Nat.add_mul];congr 1;dsimp [k];omega))
  unfold test
  apply (MvPolynomial.totalDegree_sub ..).trans (max_le _ _)
  · apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le _)
    intro j hj
    exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact cap j (Nat.le_of_lt_succ (mem_range.mp hj)))
  · exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact power k)

theorem test_detects (z:σ→K) (S:K[X]) (x₀ y₀ x answer:K) (hit:S.eval x₀=y₀) (A B:Row σ K)
    (law:evaluate z S A*S.derivative=evaluate z S B) (regular:(evaluate z S A).eval x₀≠0)
    (d:ℕ) (deg:S.natDegree≤d) (fac:∀ j≤d,(j.factorial:K)≠0) :
    MvPolynomial.eval z (test A B d x₀ y₀ x answer)=0 ↔ S.eval x=answer := by
  subst y₀
  let e:=MvPolynomial.eval z
  let v:=evaluate z S
  let a:=(v A).eval x₀
  have comm (P:Row σ K):e (centre x₀ (S.eval x₀) P)=(v P).eval x₀ :=
    RingHom.congr_fun (specialize z S x₀) P
  have entry (j:ℕ) (le:j≤d):e (coeffAt A B d x₀ (S.eval x₀) j)=a^(2*d-1)*(Polynomial.derivative^[j] S).eval x₀ := by
    cases j with
    | zero=>rw [coeffAt,map_mul,map_pow,comm];simp [e,a,mul_comm]
    | succ j=>
      letI : Algebra (Coeff σ K) K[X] := (MvPolynomial.eval (fun i=>C (z i))).toAlgebra
      letI : DifferentialAlgebra (Coeff σ K) K[X] := ⟨fun P=>GenericPhysicalCentre.deriv_eval
        (fun i=>C (z i)) (fun i=>Polynomial.derivative_C) P⟩
      have raw:=QuadraticWeight.cleared A B S law j
      have dj (n:ℕ):Differential.deriv^[n] S=Polynomial.derivative^[n] S:=rfl
      change v A^(2*j+1)*Differential.deriv^[j+1] S=v (QuadraticWeight.numerator A B j) at raw
      have evaluated:=congrArg (evalRingHom x₀) raw
      simp only [map_mul,map_pow,coe_evalRingHom,dj] at evaluated
      rw [coeffAt,map_mul,map_pow,comm,comm,←evaluated,mul_right_comm,←pow_add]
      rw [show 2*j+1+(2*d-1-(2*j+1))=2*d-1 by omega]
  change e (test A B d x₀ (S.eval x₀) x answer)=0 ↔ _
  rw [test,map_sub,map_sum,map_mul,map_pow,comm]
  have value:e (MvPolynomial.C answer)=answer:=MvPolynomial.eval_C _
  have sum:(∑j∈range (d+1),e (MvPolynomial.C ((x-x₀)^j/(j.factorial:K))*coeffAt A B d x₀ (S.eval x₀) j))=
      a^(2*d-1)*S.eval x := by
    rw [AffineODE.evaluation_from_derivatives S x₀ x d deg fac,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [map_mul,entry j (Nat.le_of_lt_succ (mem_range.mp hj)),show e (MvPolynomial.C ((x-x₀)^j/(j.factorial:K)))=_ from MvPolynomial.eval_C _]
    ring
  rw [sum,value,mul_comm answer,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ regular),sub_eq_zero]

#print axioms test_degree
#print axioms test_detects
end
end Research6966.FixedNodeRows
