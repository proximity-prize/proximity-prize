import ProximityPrize.SubmissionLower.R6966ProofOdeSurfaceBridge
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills

set_option Elab.async false

namespace Research6966.NativeSurfaceTariff
open Polynomial Finset
open K1 (K I p)
open K1_14 (L FX Equation Jet atX jetAt graphEval liftPoly seedEmbedding)
open K1_14_3 (SeedField Surface ProjectedProduct)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open scoped Polynomial Differential
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

private def labelPoint (z:K) : Fin 2→FX:=![seedEmbedding z,seedEmbedding z^p]

private theorem constant_power {R:Type*} [Field R] [Differential R] (x:R)
    (constant:Differential.deriv x=0) (n:ℕ):Differential.deriv (x^n)=0:=by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,Derivation.leibniz,constant,ih,smul_zero,smul_zero,add_zero]

private theorem constant_pair {R:Type*} [Field R] [Differential R] (x:R) (n:ℕ)
    (hx:Differential.deriv x=0) (i:Fin 2) : Differential.deriv ((![x,x^n]:Fin 2→R) i)=0 := by
  fin_cases i
  · exact hx
  · exact constant_power _ hx n

private theorem fixed (z:K) (i:Fin 2) : Differential.deriv (labelPoint z i)=0 := by
  apply constant_pair (seedEmbedding z) p _ i
  change Differential.deriv (algebraMap L[X] FX (C (algebraMap K L z)))=0
  rw [GenericPhysicalCentre.physical_poly,derivative_C,map_zero]

private theorem label_inj {u deleted maxHeight} (M:P1.ModelAt maxHeight u deleted) :
    Function.Injective M.label := by intro x y same;exact sub_left_injective (b:=M.shift) same

/-- Surface tariff on a group of the production P1 family. The ownership
predicate is exactly the one exported by the main and rescue terminal
surface constructors. The agreement remains a parameter of the family. -/
theorem price {u deleted maxHeight a} {M:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt a M Γ) (sub:T⊆Γ) {parents:Finset Surface} {H:Equation}
    (project:ProjectedProduct parents H) {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (nonlinear:2≤G.graphDegree) (uSeed:Fin 2→ℕ)
    (axes:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤uSeed z)
    (small:(2*G.graphDegree-1)*uSeed 0<p) (d:ℕ) (physical:(131071:ℤ)+M.overhead≤d)
    (dp:d<p) (gap:d<a)
    (owners:∀ γ∈T,∃ q∈parents,N.poly∈q.asIdeal ∧ ∀ P∈q.asIdeal,jetAt P (M.label γ) (F.scalar γ)=0) :
    let m:=2*d-1
    let h₀:=max 1 (m*uSeed 0)
    let h₁:=max 1 (m*uSeed 1)
    let hY:=m*(G.graphDegree-1)+1
    let fee:=(2*G.graphDegree-1)*(uSeed 0+p*uSeed 1)
    let side:=WordSurfacePrice.side (Fintype.card I) a d
    T.card*(a-d)^2 ≤ fee*(a-d)^2+2*
      (H.natDegree*side h₀*side h₁+KoalaRect.axisDegree H 0*side hY*side h₁+KoalaRect.axisDegree H 1*side hY*side h₀) := by
  classical
  let y (z:K):=atX (F.scalar z)
  let val (z:K) (P:Equation):=P.eval₂ (graphEval (M.label z)) (y z)
  have law z (hz:z∈T):val z (den N)*atX (F.scalar z).derivative=val z (rhs N) := by
    obtain ⟨q,_,own,mark⟩:=owners z hz
    exact NativeGraphMarks.mark_law N gp own mark
  have onH z (hz:z∈T):val z H=0 := by
    obtain ⟨q,hq,_,mark⟩:=owners z hz
    have v:=mark (C H) (project.vanishes q hq)
    simpa [jetAt,val,y] using v
  let bad:=T.filter (fun z=>val z (den N)=0)
  let good:=T\bad
  have gsub:good⊆T:=sdiff_subset
  have nz (z:↥good): val z (den N)≠0 := fun hz=>(mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨gsub z.property,hz⟩)
  have fee:=NativeGraphExceptional.singular_count N gp uSeed axes small bad M.label (label_inj M).injOn y
    (fun z mem=>(mem_filter.mp mem).2) (by
      intro z mem
      obtain ⟨zt,isZero⟩:=mem_filter.mp mem
      have id:=law z zt
      rw [isZero,zero_mul] at id
      exact id.symm)
  let words (z:↥good):=liftPoly (F.scalar z.val)
  have marks (z:↥good):=F.mark z.val (sub (gsub z.property))
  have deg (z:↥good): (words z).natDegree≤d := by
    change ((F.scalar z.val).map (algebraMap K L)).natDegree≤d
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (marks z).scalar_degree with isZero|bound
    · simp [isZero]
    · change ((F.scalar z.val).natDegree:ℤ)≤131071+M.overhead at bound
      omega
  have distinct:Function.Injective words:=fun x z eq=>Subtype.ext (F.distinct (sub (gsub x.property))
    (sub (gsub z.property)) ((map_injective _ (algebraMap K L).injective) eq))
  let nodes (i:I):L:=algebraMap K L (K1.node i)
  let received (i:I):L:=algebraMap K L (M.word i)
  obtain ⟨ca,cb⟩:=NativeGraphMarks.equation_degrees N gp
  have result:=OdeSurfaceBridge.regular (fun z:↥good=>labelPoint (M.label z.val))
    (fun z=>fixed (M.label z.val)) (den N) (rhs N) H project.primitive.ne_zero
    (G.graphDegree-1) d H.natDegree a uSeed (KoalaRect.axisDegree H) (by omega) ca
    (by rw [Nat.sub_add_cancel (by omega : 1≤G.graphDegree)];exact cb) le_rfl
    (fun z i=>axes 1 i z) (fun z i=>by simpa [rhs,coeff_neg] using axes 0 i z)
    (fun z=>(KoalaRect.axisDegree_le_iff H z _).mp le_rfl) words distinct deg
    (by
      intro z
      change val z (den N)*algebraMap L[X] FX (liftPoly (F.scalar z.val)).derivative=val z (rhs N)
      simpa only [liftPoly,derivative_map,atX] using law z (gsub z.property))
    nz (fun z=>onH z (gsub z.property)) nodes
    ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective)
    received (fun i hi=>K1_14_2_4_2.factorial_ne_zero (hi.trans_lt dp)) gap (by
      intro z
      let b:=marks z
      refine ⟨b.bad.support,b.bad.agreement,?_⟩
      intro i hi
      exact (Polynomial.eval_map_apply (algebraMap K L) _).trans (congrArg _ (b.scalar_hits i hi)))
  rw [Fintype.card_coe] at result
  have sizes:good.card+bad.card=T.card:=card_sdiff_add_card_eq_card (filter_subset _ _)
  rw [←sizes,Nat.add_mul]
  exact (Nat.add_le_add result (Nat.mul_le_mul_right _ fee)).trans_eq (Nat.add_comm _ _)

#print axioms price
end
end Research6966.NativeSurfaceTariff
