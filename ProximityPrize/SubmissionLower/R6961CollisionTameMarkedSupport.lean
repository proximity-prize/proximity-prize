import ProximityPrize.SubmissionLower.R6961CollisionTameMarkedCorank

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionTame
open Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix Lower6960.NormalizedFiber
open scoped Polynomial Matrix BigOperators

variable {k E : Type} [Field k] [DecidableEq k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

/-- The actual simple branch supplies the generic and point matrix maps
in `Lower6960.TraceIndex.transverse_unit`. The only supplied polynomial matrix is
the literal restriction of the lifted trace Gram matrix. -/
theorem transverse_corank_receipt (δ : Plane k) (nz : δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z x : k) (good : (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (simple : ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x=1)
    (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin (finrank (FractionRing (Plane k)) E)→Order k E)
    (f : (Fin (finrank (FractionRing (Plane k)) E)→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (one : g.eval (C z)=1) (clear : ∀ w : Order k E,∃ t,f t=g • w)
    (T : Matrix (Fin (finrank (FractionRing (Plane k)) E)) (Fin (finrank (FractionRing (Plane k)) E)) (Plane k))
    (coefficients : T=tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u) :
    ∃ (q : Plane k) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      ∃ point : Plane k ⧸ P→+*k,
        ((T.map (Ideal.Quotient.mk P)).map point)=(evalRingHom x).mapMatrix (T.map (evalRingHom (C z))) ∧
        ((T.map (evalRingHom (C z))).det).rootMultiplicity x≤
          finrank (FractionRing (Plane k)) E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
  classical
  let R := Plane k
  let F := FractionRing R
  have source : ∃ (q : R) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      (q.eval (C z)).eval x=0 ∧
      (T.det.eval (C z)).rootMultiplicity x=finrank F E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
    rw [coefficients]
    exact simple_frame_corank (E:=E) δ nz principal z x good simple p small u f sum inj g one clear
  obtain ⟨q,qp,qroot,order⟩ := source
  let P := Ideal.span {q}
  let : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp
  let fpoint : R→+*k := (evalRingHom x).comp (evalRingHom (C z))
  let point : R ⧸ P→+*k := Ideal.Quotient.lift P fpoint (fun h hh=>by
    obtain ⟨v,rfl⟩ := Ideal.mem_span_singleton.mp hh
    rw [map_mul,show fpoint q=0 from qroot,zero_mul])
  refine ⟨q,qp,point,?_,?_⟩
  · apply Matrix.ext
    intro i j
    change point (Ideal.Quotient.mk P (T i j))=fpoint (T i j)
    exact Ideal.Quotient.lift_mk _ _ _
  · have detMap : (T.map (evalRingHom (C z))).det=T.det.eval (C z) :=
      ((evalRingHom (C z)).map_det T).symm
    rw [detMap]
    exact le_of_eq order

#print axioms transverse_corank_receipt
end
end Lower6961.CollisionTame
