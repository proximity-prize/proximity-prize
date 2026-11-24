import ProximityPrize.SubmissionLower.R6961CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreBaseChange
import ProximityPrize.SubmissionLower.R6960MonicChartScaled
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6961RetainedCompressionFactors
import Mathlib.LinearAlgebra.Basis.SMul

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open Polynomial Module Lower6960.NormalizedFiber
open scoped Polynomial TensorProduct Lower6960.CollisionMarked Lower6961.CollisionMarked

section Scale
variable {K : Type*} [Field K]

/-- Leading-coefficient normalization preserves separability on a full
fibre whose degree is below the characteristic. -/
theorem integralNormalization_separable (p : ℕ) [CharP K p] (q : (Polynomial K))
    (pos : 0<q.natDegree) (small : q.natDegree<p) (sep : q.Separable) :
    q.integralNormalization.Separable := by
  let a := q.leadingCoeff
  let g := q.scaleRoots a
  have an : a≠0 := leadingCoeff_ne_zero.mpr sep.ne_zero
  have en : (q.natDegree:K)≠0 := by
    intro he
    have dv := (CharP.cast_eq_zero_iff K p q.natDegree).mp he
    exact pos.ne' (Nat.eq_zero_of_dvd_of_lt dv small)
  have d := Lower6960.MonicChart.derivative_degree q pos en
  have gn : g.natDegree=q.natDegree := natDegree_scaleRoots _ _
  have res : g.resultant g.derivative≠0 := by
    change (q.scaleRoots a).resultant (q.scaleRoots a).derivative≠0
    rw [Lower6960.MonicChart.scaleRoots_derivative _ _ d,resultant_scaleRoots]
    exact mul_ne_zero (pow_ne_zero _ an) (resultant_ne_zero q q.derivative sep)
  have gs : g.Separable := by
    have proof := separable_map_of_resultant_derivative_ne_zero (RingHom.id K) g (gn.symm ▸ pos)
      (by simpa only [RingHom.id_apply] using res)
    simpa only [Polynomial.map_id] using proof
  have product : (q.integralNormalization * Polynomial.C a).Separable := by
    rw [integralNormalization_mul_C_leadingCoeff]
    exact gs
  exact product.of_mul_left
end Scale

section Generic
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E]

/-- The actual integral leading-coefficient times ordinate in the surface
order, before reducing the scalar variable. -/
def scaledRoot (P : (Polynomial (Plane k))) (g : E) (pn : P≠0) (root : aeval g P=0) : Order k E :=
  ⟨algebraMap (Plane k) E P.leadingCoeff*g,
    by
      have j : Function.Injective (algebraMap (Plane k) E) := by
        rw [IsScalarTower.algebraMap_eq (Plane k) (FractionRing (Plane k)) E]
        exact (algebraMap (FractionRing (Plane k)) E).injective.comp
          (IsFractionRing.injective (Plane k) (FractionRing (Plane k)))
      exact ⟨P.integralNormalization,monic_integralNormalization pn,
        integralNormalization_aeval_eq_zero root (fun a az=>j (az.trans (map_zero _).symm))⟩⟩

def scaledOrdinate (P : (Polynomial (Plane k))) (g : E) (pn : P≠0) (root : aeval g P=0) (z : k) :
    ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z) :=
  1 ⊗ₜ[(Polynomial k)] quotientMap E z (scaledRoot P g pn root)

/-- The generic abscissa of the original scalar fibre is the actual
specialized ordinate quotient. The idempotent selects the marked word,
after the invertible leading-coefficient change of ordinate. -/
theorem actual_scaled_word_sheet (p : ℕ) [CharP (FractionRing (Polynomial k)) p]
    (P : (Polynomial (Plane k))) (large : 2≤P.natDegree) (small : P.natDegree<p)
    (b : PowerBasis (FractionRing (Plane k)) E) (dim : b.dim=P.natDegree)
    (root : aeval b.gen P=0) (z : k) (S : (Polynomial k))
    (full : (P.map (genericFibreBase z)).natDegree=P.natDegree)
    (sep : (P.map (genericFibreBase z)).Separable)
    (word : (P.map (genericFibreBase z)).eval (algebraMap (Polynomial k) (FractionRing (Polynomial k)) S)=0) :
    let pn : P≠0 := fun h=>by rw [h,natDegree_zero] at large; omega
    let q := P.integralNormalization.map (genericFibreBase z)
    let y := genericFibreBase z P.leadingCoeff*algebraMap (Polynomial k) (FractionRing (Polynomial k)) S
    ∃ (e : AdjoinRoot q ≃ₐ[FractionRing (Polynomial k)]
        ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z)) (H Q : (Polynomial (FractionRing (Polynomial k)))),
      q.Separable ∧ q=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      e (AdjoinRoot.root q)=scaledOrdinate P b.gen pn root z ∧
      let η:=e (AdjoinRoot.mk q H)
      η^2=η ∧ η≠0 ∧ η≠1 ∧
        (scaledOrdinate P b.gen pn root z-(y ⊗ₜ[(Polynomial k)] (1:Fiber E z)))*η=0 := by
  classical
  let A := Plane k
  let F := FractionRing A
  let K := FractionRing (Polynomial k)
  let j := genericFibreBase z
  let raw := P.map j
  have Pn : P≠0 := by intro h; rw [h,natDegree_zero] at large; omega
  have lcn : P.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr Pn
  have rlc : j P.leadingCoeff≠0 := by
    by_contra zero
    have drop := natDegree_map_lt' zero (by omega : 0<P.natDegree)
    exact (full.not_lt drop).elim
  let γ := algebraMap A E P.leadingCoeff*b.gen
  let f := P.integralNormalization
  have fm : f.Monic := monic_integralNormalization Pn
  have fd : f.natDegree=P.natDegree := natDegree_integralNormalization
  have rootγ : aeval γ f=0 := by
    apply integralNormalization_aeval_eq_zero root
    have ai : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    exact fun a az=>ai (az.trans (map_zero _).symm)
  let a := algebraMap A F P.leadingCoeff
  have an : a≠0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr lcn
  let unit := Units.mk0 a an
  let e0 := finCongr (dim.trans fd.symm)
  let B0 : Basis (Fin f.natDegree) F E := b.basis.reindex e0
  let B := B0.unitsSMul (fun i=>unit^(i:ℕ))
  have powers (i : Fin f.natDegree) : B i=γ^(i:ℕ) := by
    rw [show B i=unit^(i:ℕ) • B0 i from Basis.unitsSMul_apply i]
    change (↑(unit^(i:ℕ)):F) • B0 i=_
    rw [Units.val_pow_eq_pow_val]
    rw [show (unit:F)=a from rfl,show B0 i=b.basis (e0.symm i) from Basis.reindex_apply _ _ _,b.basis_eq_pow]
    change (a^(i:ℕ):F) • b.gen^(i:ℕ)=_
    rw [Algebra.smul_def,map_pow,←mul_pow]
    exact congrArg (·^(i:ℕ)) (by
      change algebraMap F E (algebraMap A F P.leadingCoeff)*b.gen=γ
      rw [←IsScalarTower.algebraMap_apply])
  let q := f.map j
  have qeq : q=raw.integralNormalization := (integralNormalization_map j P rlc).symm
  have qs : q.Separable := by
    rw [qeq]
    have d : raw.natDegree=P.natDegree := full
    exact integralNormalization_separable p raw (by rw [d]; omega) (by rw [d]; exact small) sep
  have qdeg : q.natDegree=P.natDegree := (fm.natDegree_map j).trans fd
  let s := algebraMap (Polynomial k) K S
  let y := j P.leadingCoeff*s
  have yroot : q.eval y=0 := by
    have lead : raw.leadingCoeff=j P.leadingCoeff := leadingCoeff_map_of_leadingCoeff_ne_zero _ rlc
    have root' := integralNormalization_eval₂_eq_zero (p:=raw) (z:=s) (RingHom.id K)
      (by change raw.eval s=0; exact word) (fun _ h=>h)
    rw [qeq]
    change raw.integralNormalization.eval (j P.leadingCoeff*s)=0
    change raw.integralNormalization.eval ((RingHom.id K) raw.leadingCoeff*s)=0 at root'
    rw [RingHom.id_apply,lead] at root'
    exact root'
  have simple : q.derivative.eval y≠0 := by
    have one : IsCoprime q q.derivative := qs
    obtain ⟨v,w,h⟩ := one
    intro zero
    have h0 := congrArg (fun t : (Polynomial K)=>t.eval y) h
    rw [eval_add,eval_mul,eval_mul,yroot,zero,mul_zero,mul_zero,zero_add,eval_one] at h0
    exact zero_ne_one h0
  obtain ⟨H,Q,split,one,div,he⟩ := Lower6960.MarkedRoot.sheet (qdeg ▸ large) y yroot simple
  let : Algebra A K := j.toAlgebra
  obtain ⟨E1,gen⟩ := monic_fibre_equiv fm γ rootγ B powers j p (fd.symm ▸ small) qs
  let E2 := (genericFibreAsTensor (E:=E) z).val.symm
  let e := E1.trans E2
  have image : e (AdjoinRoot.root q)=scaledOrdinate P b.gen Pn root z := by
    apply (genericFibreAsTensor (E:=E) z).val.injective
    have forward := (genericFibreAsTensor (E:=E) z).property (scaledRoot P b.gen Pn root)
    change (genericFibreAsTensor (E:=E) z).val (E2 (E1 (AdjoinRoot.root q)))=_
    rw [show (genericFibreAsTensor (E:=E) z).val (E2 (E1 (AdjoinRoot.root q)))=
      E1 (AdjoinRoot.root q) from (genericFibreAsTensor (E:=E) z).val.apply_symm_apply _]
    rw [gen]
    exact forward.symm
  refine ⟨e,H,Q,qs,split,one,div,image,?_⟩
  obtain ⟨idemp,nz,ne⟩ := he
  refine ⟨by rw [←map_pow,idemp],fun h=>nz (e.injective (h.trans (map_zero e).symm)),
    fun h=>ne (e.injective (h.trans (map_one e).symm)),?_⟩
  obtain ⟨J,hJ⟩ := div
  have zero : AdjoinRoot.mk q ((Polynomial.X-C y)*H)=0 := AdjoinRoot.mk_eq_zero.mpr
    ⟨J,by rw [hJ,split,mul_assoc]⟩
  have annih := congrArg e zero
  rw [map_zero,map_mul,map_sub,AdjoinRoot.mk_X,AdjoinRoot.mk_C,map_mul,map_sub,image] at annih
  have ey : e (AdjoinRoot.of q y)=y ⊗ₜ[(Polynomial k)] (1:Fiber E z) := e.commutes y
  rw [ey] at annih
  exact annih
end Generic

#print axioms integralNormalization_separable
#print axioms actual_scaled_word_sheet
end
end Lower6961.CollisionMarked
