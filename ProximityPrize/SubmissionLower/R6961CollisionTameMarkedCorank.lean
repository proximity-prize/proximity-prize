import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameTransverse
import ProximityPrize.SubmissionLower.R6961RetainedCompressionProjection

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1750000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionTame
open Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix Lower6960.NormalizedFiber
open scoped Polynomial Matrix BigOperators

variable {k E : Type} [Field k] [DecidableEq k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

/-- At a simple reduced branch crossing the actual scalar-fibre Gram
determinant has order equal to the generic trace corank along that
branch. The fibre denominator is proved to avoid the branch. -/
theorem simple_frame_corank (δ : Plane k) (nz : δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z x : k) (good : (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (simple : ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x=1)
    (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin (finrank (FractionRing (Plane k)) E)→Order k E)
    (f : (Fin (finrank (FractionRing (Plane k)) E)→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (one : g.eval (C z)=1) (clear : ∀ w : Order k E,∃ t,f t=g • w) :
    let T := tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u
    ∃ (q : Plane k) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      (q.eval (C z)).eval x=0 ∧
      ((T.det).eval (C z)).rootMultiplicity x=
        finrank (FractionRing (Plane k)) E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
  classical
  let A := Plane k
  let F := FractionRing A
  let n := finrank F E
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  let evalZ := evalRingHom (C z)
  have swappnz : Bivariate.swap δ≠0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr nz
  obtain ⟨i,qorder,δorder,exponent⟩ := simple_branch_weight (Bivariate.swap δ) swappnz z x good simple
  let q : A := Bivariate.swap (i:Plane k)
  have qp : Prime q := (MulEquiv.prime_iff Bivariate.swap.toMulEquiv).mpr (branchFactor_prime (Bivariate.swap δ) i)
  let P := Ideal.span {q}
  let : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp
  have qroot : (q.eval (C z)).eval x=0 := by
    change IsRoot (q.eval (C z)) x
    apply (rootMultiplicity_pos'.mp ?_).2
    rw [show q.eval (C z)=(i:Plane k).map (evalRingHom z) from RetainedCompression.eval_swap _ _,qorder]
    decide
  have qout : g∉P := by
    intro hgp
    have qdvd : q∣g := Ideal.mem_span_singleton.mp hgp
    obtain ⟨a,eq⟩ := map_dvd (evalRingHom x) (map_dvd evalZ qdvd)
    change (g.eval (C z)).eval x=((q.eval (C z)).eval x)*a at eq
    rw [one,eval_one,qroot,zero_mul] at eq
    exact one_ne_zero eq
  have core := branch_frame_trace_order P q qp.irreducible rfl p small u f sum inj g qout clear
  have Dmem : T.det∈normalizationDiscriminant (A:=A) (E:=E) F := gramIdeal_mem tr u
  have δmem : δ∈normalizationDiscriminant (A:=A) (E:=E) F := by
    rw [principal]; exact Ideal.subset_span (Set.mem_singleton δ)
  have trace_divides : T.det∣g^(2*n)*δ := by
    have h := gramIdeal_clear tr u g (fun w=>by
      obtain ⟨v,hv⟩ := clear w
      exact ⟨v,(sum v).symm.trans hv⟩) δ δmem
    simpa only [Fintype.card_fin] using h
  have δ_divides : δ∣T.det := Ideal.mem_span_singleton.mp (principal ▸ Dmem)
  have g0 : emultiplicity q g=0 := emultiplicity_eq_zero.mpr fun hv=>qout (Ideal.mem_span_singleton.mpr hv)
  have order_eq : emultiplicity q T.det=emultiplicity q δ := by
    apply le_antisymm _ (emultiplicity_le_emultiplicity_of_dvd_right δ_divides)
    have h := emultiplicity_le_emultiplicity_of_dvd_right (a:=q) trace_divides
    rw [emultiplicity_mul qp,emultiplicity_pow qp,g0,mul_zero,zero_add] at h
    exact h
  have sameExponent : emultiplicity q δ=(branchWeight (Bivariate.swap δ) i:ℕ∞) := calc
    _ = emultiplicity q (Bivariate.swap (Bivariate.swap δ)) :=
      congrArg (emultiplicity q) (Bivariate.swap_swap_apply δ).symm
    _ = emultiplicity (i:Plane k) (Bivariate.swap δ) := emultiplicity_map_eq Bivariate.swap
    _ = _ := exponent
  have idxEq : ((branchWeight (Bivariate.swap δ) i):ℕ∞)=
      ((n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) :=
    sameExponent.symm.trans (order_eq.symm.trans core)
  have δeval : δ.eval (C z)=(Bivariate.swap δ).map (evalRingHom z) := by
    simpa only [Bivariate.swap_swap_apply] using RetainedCompression.eval_swap (Bivariate.swap δ) z
  have δpositive : 0<(δ.eval (C z)).rootMultiplicity x := by
    rw [δeval,δorder]
    exact branch_weight_pos _ _
  have δnonzero := (rootMultiplicity_pos'.mp δpositive).1
  have eval_dvd : evalZ T.det∣evalZ δ := by
    have d := map_dvd evalZ trace_divides
    rw [map_mul,map_pow,show evalZ g=1 from one,one_pow,one_mul] at d
    exact d
  have eval_dvd' : evalZ δ∣evalZ T.det := map_dvd evalZ δ_divides
  have tn : evalZ T.det≠0 := fun zero=>δnonzero (zero_dvd_iff.mp (zero ▸ eval_dvd))
  have eq : (evalZ T.det).rootMultiplicity x=(evalZ δ).rootMultiplicity x :=
    le_antisymm ((le_rootMultiplicity_iff δnonzero).mpr ((evalZ T.det).pow_rootMultiplicity_dvd x |>.trans eval_dvd))
      ((le_rootMultiplicity_iff tn).mpr ((evalZ δ).pow_rootMultiplicity_dvd x |>.trans eval_dvd'))
  refine ⟨q,qp,qroot,?_⟩
  change (evalZ T.det).rootMultiplicity x=n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank
  rw [eq]
  change (δ.eval (C z)).rootMultiplicity x=_
  rw [δeval,δorder]
  exact ENat.natCast_inj.mp idxEq

#print axioms simple_frame_corank
end
end Lower6961.CollisionTame
