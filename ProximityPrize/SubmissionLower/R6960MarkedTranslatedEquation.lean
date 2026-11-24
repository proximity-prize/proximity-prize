import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import Mathlib.LinearAlgebra.Basis.SMul
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6960RetainedAxisTransition
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

-- merged module R6960CollisionMarkedFibreBaseChange
section Merged_R6960CollisionMarkedFibreBaseChange
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Algebra
open scoped Polynomial TensorProduct
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
local instance fibreRing (z : k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)
scoped instance fibreAlgebra (z : k) : Algebra (Polynomial k) (Fiber E z) :=
  @RingHom.toAlgebra (Polynomial k) (Fiber E z) _ (fibreRing (E:=E) z).toCommSemiring (baseMap E z)
def fibreBase (z : k) : Plane k→+*(Polynomial k) := evalRingHom (C z)
def genericFibreBase (z : k) : Plane k→+*FractionRing (Polynomial k) :=
  (algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp (fibreBase z)
def fibreAsTensor (z : k) :
    let : Algebra (Plane k) (Polynomial k) := (fibreBase z).toAlgebra
    { e : Fiber E z ≃ₐ[(Polynomial k)] ((Polynomial k)⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (quotientMap E z x)=(1:(Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let B := Order k E
  let : CommRing B := @Subalgebra.toCommRing A E _ _ (inferInstance : Algebra A E) B
  let : Algebra A R := (fibreBase z).toAlgebra
  let : IsScalarTower A A R := IsScalarTower.of_algebraMap_eq (R:=A) (S:=A) (A:=R) fun a=>by
    change algebraMap A R a=algebraMap A R (algebraMap A A a)
    rw [Algebra.algebraMap_self,RingHom.id_apply]
  let I : Ideal A := Ideal.span {Polynomial.X-C (C z)}
  let : CommRing (A ⧸ I) := Ideal.Quotient.commRing I
  let j := algebraMap A B
  have slice : sliceIdeal E z=I.map j := by
    unfold I sliceIdeal
    rw [Ideal.map_span,Set.image_singleton]
  let eq : Fiber E z ≃+* (B ⧸ I.map j) := Ideal.quotEquivOfEq slice
  let Q := Polynomial.quotientSpanXSubCAlgEquiv (C z)
  let base : (A ⧸ I) ≃ₐ[A] R := {
    Q.toRingEquiv with
    commutes' := fun a=>by
      change Q (Ideal.Quotient.mk I a)=a.eval (C z)
      exact Polynomial.quotientSpanXSubCAlgEquiv_mk (C z) a }
  let tensor := Algebra.TensorProduct.congr base (AlgEquiv.refl (R:=A) (A₁:=B))
  let ring : Fiber E z ≃+* (R⊗[A] B) := eq.trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv.trans tensor.toRingEquiv)
  have apply_q (x : B) : ring (quotientMap E z x)=(1:R) ⊗ₜ[A] x := by
    change tensor ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
      (eq (Ideal.Quotient.mk (sliceIdeal E z) x)))=_
    rw [show eq (Ideal.Quotient.mk (sliceIdeal E z) x)=Ideal.Quotient.mk (I.map j) x from
      Ideal.quotEquivOfEq_mk slice x,Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (base 1) ⊗ₜ[A] x=_
    rw [map_one]
  let e : Fiber E z ≃ₐ[R] (R⊗[A] B) := { ring with
    commutes' := fun c=>by
      change ring (quotientMap E z (j (C c)))=c ⊗ₜ[A] (1:B)
      rw [apply_q,Algebra.algebraMap_eq_smul_one,TensorProduct.tmul_smul]
      change ((C c : A) • (1:R)) ⊗ₜ[A] (1:B)=_
      have h : (C c : A) • (1:R)=c := by
        rw [Algebra.smul_def,mul_one]
        change (C c).eval (C z)=c
        exact eval_C
      rw [h] }
  exact ⟨e,apply_q⟩
def genericFibreAsTensor (z : k) :
    let : Algebra (Plane k) (FractionRing (Polynomial k)) := (genericFibreBase z).toAlgebra
    { e : ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z) ≃ₐ[FractionRing (Polynomial k)]
        ((FractionRing (Polynomial k))⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (1 ⊗ₜ[(Polynomial k)] quotientMap E z x)=(1:FractionRing (Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let K := FractionRing R
  let B := Order k E
  let : Algebra A R := (fibreBase z).toAlgebra
  let : Algebra A K := (genericFibreBase z).toAlgebra
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : SMul A K := (inferInstance : Algebra A K).toSMul
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=K) fun _=>rfl
  let v := fibreAsTensor (E:=E) z
  let c := Algebra.TensorProduct.congr (AlgEquiv.refl (R:=K) (A₁:=K)) v.val
  let d := Algebra.TensorProduct.cancelBaseChange A R K K B
  refine ⟨c.trans d,fun x=>?_⟩
  change d (1 ⊗ₜ[R] v.val (quotientMap E z x))=_
  rw [v.property,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]
#print axioms fibreAsTensor
#print axioms genericFibreAsTensor
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedFibreBaseChange

-- merged module R6960CollisionMarkedActualSheet
section Merged_R6960CollisionMarkedActualSheet
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Module NormalizedFiber
open scoped Polynomial TensorProduct Lower6960.CollisionMarked
section Scale
variable {K : Type*} [Field K]
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
  have d := MonicChart.derivative_degree q pos en
  have gn : g.natDegree=q.natDegree := natDegree_scaleRoots _ _
  have res : g.resultant g.derivative≠0 := by
    change (q.scaleRoots a).resultant (q.scaleRoots a).derivative≠0
    rw [MonicChart.scaleRoots_derivative _ _ d,resultant_scaleRoots]
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
  obtain ⟨H,Q,split,one,div,he⟩ := MarkedRoot.sheet (qdeg ▸ large) y yroot simple
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
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedActualSheet

-- merged module R6960CollisionMarkedProjected
section Merged_R6960CollisionMarkedProjected
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Module
open K1_14 (L)
open RetainedCompression (MarkedFiber specialize incl eval_swap)
open scoped Polynomial TensorProduct Lower6960.CollisionMarked
def projectedRaw (P : CurvatureSquares.Ordinate) : (Polynomial (Plane L)) := P.map Bivariate.swap.toRingHom
theorem projectedRaw_degree (P : CurvatureSquares.Ordinate) :
    (projectedRaw P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective Bivariate.swap.injective _
theorem projectedRaw_fibre (P : CurvatureSquares.Ordinate) (z : L) :
    (projectedRaw P).map (genericFibreBase z)=(specialize P z).map incl := by
  apply Polynomial.ext
  intro i
  simp only [projectedRaw,RetainedCompression.specialize,coeff_map,Polynomial.coe_mapRingHom]
  change incl ((Bivariate.swap (P.coeff i)).eval (Polynomial.C z))=incl ((P.coeff i).map (evalRingHom z))
  rw [eval_swap]
theorem projected_word_sheet {E : Type} [Field E] [Algebra (Plane L) E]
    [Algebra (FractionRing (Plane L)) E] [IsScalarTower (Plane L) (FractionRing (Plane L)) E]
    [FiniteDimensional (FractionRing (Plane L)) E]
    (p : ℕ) [CharP (FractionRing (Polynomial L)) p]
    (P : CurvatureSquares.Ordinate) (large : 2≤P.natDegree) (small : P.natDegree<p)
    (b : PowerBasis (FractionRing (Plane L)) E) (dim : b.dim=P.natDegree)
    (root : aeval b.gen (projectedRaw P)=0) (z : L) (S : (Polynomial L)) (mark : MarkedFiber P z S) :
    let pn : projectedRaw P≠0 := fun h=>by
      have d := projectedRaw_degree P
      rw [h,natDegree_zero] at d
      omega
    let q := (projectedRaw P).integralNormalization.map (genericFibreBase z)
    let y := genericFibreBase z (projectedRaw P).leadingCoeff*incl S
    ∃ (e : AdjoinRoot q ≃ₐ[FractionRing (Polynomial L)] ((FractionRing (Polynomial L))⊗[(Polynomial L)] Fiber E z))
      (H Q : (Polynomial (FractionRing (Polynomial L)))),
      q.Separable ∧ q=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      e (AdjoinRoot.root q)=scaledOrdinate (projectedRaw P) b.gen pn root z ∧
      let η:=e (AdjoinRoot.mk q H)
      η^2=η ∧ η≠0 ∧ η≠1 ∧
        (scaledOrdinate (projectedRaw P) b.gen pn root z-(y ⊗ₜ[(Polynomial L)] (1:Fiber E z)))*η=0 := by
  have full : ((projectedRaw P).map (genericFibreBase z)).natDegree=(projectedRaw P).natDegree := by
    rw [projectedRaw_fibre,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have sep : ((projectedRaw P).map (genericFibreBase z)).Separable := projectedRaw_fibre P z ▸ mark.separable
  have rt : ((projectedRaw P).map (genericFibreBase z)).eval (incl S)=0 := by
    rw [projectedRaw_fibre,Polynomial.eval_map_apply,mark.root,map_zero]
  exact actual_scaled_word_sheet p (projectedRaw P) (projectedRaw_degree P ▸ large)
    (projectedRaw_degree P ▸ small) b (dim.trans (projectedRaw_degree P).symm) root z S full sep rt
#print axioms projected_word_sheet
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedProjected

-- merged module R6960MarkedTranslatedEquation
section Merged_R6960MarkedTranslatedEquation
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedSurfaceClass NormalizedFiber CollisionMarked Polynomial Algebra
open scoped Polynomial Lower6960.MonicChart
open Lower6960.RetainedSurfaceClass (oriented_var oriented_const oriented_line)
def translatedX (c:L) : (Polynomial L)→+*Scalar := (translateField Scalar c).toRingHom.comp (algebraMap (Polynomial L) Scalar)
def rowPlane (c:L) : Plane L→+*(Polynomial Scalar) := eval₂RingHom (C.comp (translatedX c)) Polynomial.X
local notation "fp" => algebraMap (Polynomial Scalar) ChartField
private theorem translatedX_const (c a:L) : translatedX c (C a)=inner a := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar (C a))=_
  rw [translate_polynomial,taylor_C];rfl
private theorem translatedX_var (c:L) : translatedX c Polynomial.X=algebraMap (Polynomial L) Scalar Polynomial.X+inner c := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar Polynomial.X)=_
  rw [translate_polynomial,taylor_X,map_add];rfl
theorem row_plane (c:L) (p:Plane L) :
    rowBase c ((oriented true false p):ChartField)=fp (rowPlane c p) := by
  let f:Plane L→+*ChartField:= (rowBase c).toRingHom.comp ((baseChart _).subtype.comp (oriented true false).toRingHom)
  let g:Plane L→+*ChartField:=(algebraMap (Polynomial Scalar) ChartField).comp (rowPlane c)
  have eq:f=g := by
    apply Polynomial.ringHom_ext
    · intro v
      have innerEq:f.comp C=g.comp C := by
        apply Polynomial.ringHom_ext
        · intro a
          change rowBase c ((oriented true false (C (C a))):ChartField)=fp ((C (C a)).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_const,row_constant,eval₂_C,RingHom.comp_apply,translatedX_const,RatFunc.algebraMap_C];rfl
        · change rowBase c ((oriented true false (C Polynomial.X)):ChartField)=fp ((C Polynomial.X).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_line,eval₂_C,RingHom.comp_apply,translatedX_var,RatFunc.algebraMap_C,map_add]
          exact row_abscissa c
      exact DFunLike.congr_fun innerEq v
    · change rowBase c ((oriented true false Polynomial.X):ChartField)=fp (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X)
      rw [Lower6960.RetainedSurfaceClass.oriented_var,eval₂_X,RatFunc.algebraMap_X];exact row_parameter c
  exact DFunLike.congr_fun eq p
theorem row_specialization (c z:L) :
    (evalRingHom (inner z)).comp (rowPlane c)=(translateField Scalar c).toRingHom.comp (genericFibreBase z) := by
  apply Polynomial.ringHom_ext
  · intro v
    change ((C v).eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar ((C v).eval (C z)))
    rw [eval₂_C,RingHom.comp_apply,eval_C,eval_C];rfl
  · change (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar (Polynomial.X.eval (C z)))
    rw [eval₂_X,eval_X,eval_X];exact (translatedX_const c z).symm
theorem normalized_fibre_separable (z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p)
    (mark:RetainedCompression.MarkedFiber P z S) :
    ((projectedRaw P).integralNormalization.map (genericFibreBase z)).Separable := by
  let raw:=projectedRaw P
  let J:=genericFibreBase z
  have full:(raw.map J).natDegree=raw.natDegree := by
    rw [show raw.map J= _ from projectedRaw_fibre P z,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have nz:J raw.leadingCoeff≠0 := fun bad=>(natDegree_map_lt' bad (projectedRaw_degree P ▸ lo)).ne full
  have base:(raw.map J).Separable := projectedRaw_fibre P z ▸ mark.separable
  rw [←integralNormalization_map J raw nz]
  apply integralNormalization_separable p _ _ _ base <;> rwa [full,projectedRaw_degree]
theorem marked_row_separable (c z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p) (mark:RetainedCompression.MarkedFiber P z S) :
    ((((projectedRaw P).integralNormalization.map (rowPlane c)).map (evalRingHom (inner z)))).Separable := by
  rw [Polynomial.map_map,row_specialization,←Polynomial.map_map]
  exact (normalized_fibre_separable z P S p lo hi mark).map
theorem scaled_row_degree {F E Ω:Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    (b:PowerBasis F E) (σ:F≃+*F) (ev:E→+*Ω)
    (base:∀a,ev (algebraMap F E a)=algebraMap F Ω (σ a)) (a:F) (nz:a≠0) :
    (minpoly F (ev (algebraMap F E a*b.gen))).natDegree=b.dim := by
  let q:=minpoly F b.gen
  let Q:=q.map σ.toRingHom
  have mon:Q.Monic:=(minpoly.monic b.isIntegral_gen).map _
  have irr:Irreducible Q:=(MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mpr (minpoly.irreducible b.isIntegral_gen)
  have h:(algebraMap F Ω).comp σ.toRingHom=ev.comp (algebraMap F E) := RingHom.ext (fun r=>(base r).symm)
  have zero:aeval (ev b.gen) Q=0 := by
    rw [aeval_def,show Q=q.map σ.toRingHom from rfl,eval₂_map,h,←Polynomial.hom_eval₂]
    exact (congrArg ev (minpoly.aeval F b.gen)).trans (map_zero _)
  have eq:=minpoly.eq_of_irreducible_of_monic irr zero mon
  rw [map_mul,base,←Algebra.smul_def,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff _ σ.injective).mpr nz)
    (show IsIntegral F (ev b.gen) from ⟨Q,mon,zero⟩),natDegree_scaleRoots,←eq,
    show Q=q.map σ.toRingHom from rfl,natDegree_map_eq_of_injective σ.injective,b.natDegree_minpoly]
#print axioms row_plane
#print axioms marked_row_separable
#print axioms scaled_row_degree
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedTranslatedEquation
