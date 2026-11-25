import ProximityPrize.SubmissionLower.R6961RetainedAxisTransition
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import ProximityPrize.SubmissionLower.R6960MarkedTranslatedEquation
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6961MarkedScalarPlace
import Mathlib.LinearAlgebra.Basis.SMul
import ProximityPrize.SubmissionLower.R6961MarkedMatrixNorm
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

set_option Elab.async false

-- merged module R6961CollisionMarkedMonicTrace
section Merged_R6961CollisionMarkedMonicTrace

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
noncomputable section
open Polynomial Algebra Module Matrix
open scoped Polynomial Matrix BigOperators

section Trace
variable {A R U V ι : Type*} [CommRing A] [CommRing R] [CommRing U] [CommRing V]
  [Algebra A U] [Algebra R V] [Fintype ι] [DecidableEq ι]

/-- Compatibility with the whole basis and scalar map transports the
multiplication matrices and the trace pairing. -/
theorem trace_matrix_map_of_basis (j : A→+*R) (a : Basis ι A U) (b : Basis ι R V) (φ : U→+*V)
    (scalar : ∀ c,φ (algebraMap A U c)=algebraMap R V (j c))
    (basis : ∀ i,φ (a i)=b i) : (traceMatrix A a).map j=traceMatrix R b := by
  have coords (x : U) (i : ι) : b.repr (φ x) i=j (a.repr x i) := by
    have expand : φ x=∑ l,j (a.repr x l) • b l := by
      rw [←a.sum_repr x,map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Algebra.smul_def,map_mul,scalar,basis,←Algebra.smul_def]
      simp only [a.repr_sum_self]
    rw [expand,b.repr_sum_self]
  have trace_map (x : U) : j (Algebra.trace A U x)=Algebra.trace R V (φ x) := by
    rw [trace_eq_matrix_trace a,trace_eq_matrix_trace b]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply,Matrix.diag_apply,leftMulMatrix_eq_repr_mul,leftMulMatrix_eq_repr_mul,
      ←basis,←map_mul,coords]
  apply Matrix.ext
  intro i l
  simp only [Matrix.map_apply,traceMatrix_apply,traceForm_apply,←basis,←map_mul,trace_map]
end Trace

section Monic
variable {A R V : Type*} [CommRing A] [CommRing R] [CommRing V] [Algebra R V]

/-- The discriminant polynomial comes from the actual monic power-basis
order over the base, before specializing any coefficient. -/
def monicDisc {p : (Polynomial A)} (hp : p.Monic) : A := (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).det

theorem monic_basis_trace {p : (Polynomial A)} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).map j=traceMatrix R b := by
  let ev := (algebraMap R V).comp j
  have rr : p.eval₂ ev γ=0 := by
    rw [aeval_def,eval₂_map] at root
    exact root
  let φ := AdjoinRoot.lift ev γ rr
  have scalar (c : A) : φ (algebraMap A (AdjoinRoot p) c)=algebraMap R V (j c) := by
    change AdjoinRoot.lift ev γ rr (AdjoinRoot.of p c)=_
    exact AdjoinRoot.lift_of rr
  have powers (i : Fin p.natDegree) : φ ((AdjoinRoot.powerBasis' hp).basis i)=b i := by
    rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow,pow,map_pow]
    congr 1
    exact AdjoinRoot.lift_root rr
  exact trace_matrix_map_of_basis j (AdjoinRoot.powerBasis' hp).basis b φ scalar powers

theorem monic_disc_of_basis {p : (Polynomial A)} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    j (monicDisc hp)=Algebra.discr R b := by
  unfold monicDisc
  rw [Algebra.discr_def]
  exact (RingHom.map_det j _).trans (congrArg Matrix.det (monic_basis_trace hp j γ root b pow))
end Monic

section Coordinates
variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra A E] [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

/-- The discriminant of the monic order clears all coordinates of every
actual normalized element, in the original power basis. -/
theorem monic_coordinates {p : (Polynomial A)} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (x : integralClosure A E) :
    ∀ i,∃ c : A,algebraMap A F c=algebraMap A F (monicDisc hp)*b.repr (x:E) i := by
  classical
  let j := algebraMap A F
  have baseRoot : aeval γ (p.map j)=0 := by rw [aeval_map_algebraMap]; exact root
  let T : Matrix (Fin p.natDegree) (Fin p.natDegree) A := traceMatrix A (AdjoinRoot.powerBasis' hp).basis
  have eqT : T.map j=traceMatrix F b := monic_basis_trace hp j γ baseRoot b pow
  have integral : IsIntegral A γ := ⟨p,hp,root⟩
  have ib (i : Fin p.natDegree) : IsIntegral A (b i) := pow i ▸ integral.pow _
  choose t ht using fun i : Fin p.natDegree=>IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L:=F) (x.property.mul (ib i)))
  have exp : (T.map j)*ᵥb.equivFun (x:E)=fun i=>j (t i) := by
    rw [eqT,Algebra.traceMatrix_of_basis_mulVec]
    exact funext fun i=>(ht i).symm
  let v := T.adjugate *ᵥ t
  intro i
  refine ⟨v i,?_⟩
  have all : (fun i=>j (v i))=j T.det • b.equivFun (x:E) := by
    change (fun i=>j ((T.adjugate*ᵥt) i))=_
    have mv : (fun i=>j ((T.adjugate*ᵥt) i))=T.adjugate.map j *ᵥ (fun i=>j (t i)) :=
      funext fun i=>RingHom.map_mulVec j _ _ i
    have adj : T.adjugate.map j=(T.map j).adjugate := j.map_adjugate T
    rw [mv,adj,←exp,Matrix.mulVec_mulVec,
      Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,RingHom.map_det]
    rfl
  exact congrFun all i

/-- At a place where the power-basis discriminant is a unit, the monic
order equals the actual integral closure in the root field. -/
theorem monic_order_eq_normalization {p : (Polynomial A)} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (unit : IsUnit (monicDisc hp)) : Algebra.adjoin A {γ}=integralClosure A E := by
  let B := Algebra.adjoin A ({γ}:Set E)
  have gi : IsIntegral A γ := ⟨p,hp,root⟩
  apply le_antisymm
  · exact Algebra.adjoin_le (fun y hy=>(Set.mem_singleton_iff.mp hy).symm ▸ gi)
  · intro x hx
    choose c hc using monic_coordinates hp γ root b pow (⟨x,hx⟩:integralClosure A E)
    obtain ⟨d,hd⟩ := unit
    have dx : algebraMap A F (monicDisc hp) • x=∑ i,algebraMap A F (c i) • b i := by
      rw [←b.sum_repr x,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,←hc i]
    have isin : monicDisc hp • x∈B := by
      rw [←IsScalarTower.algebraMap_smul F,dx]
      apply B.sum_mem
      intro i _
      rw [IsScalarTower.algebraMap_smul F,pow]
      exact B.smul_mem (B.pow_mem (Algebra.subset_adjoin (Set.mem_singleton γ)) _) _
    have cancel : (↑d⁻¹:A) • (monicDisc hp • x)=x := by
      rw [smul_smul,←hd,Units.inv_mul,one_smul]
    exact cancel ▸ B.smul_mem isin _
end Coordinates

#print axioms monic_disc_of_basis
#print axioms monic_coordinates
#print axioms monic_order_eq_normalization
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedMonicTrace

-- merged module R6961CollisionMarkedMonicFibre
section Merged_R6961CollisionMarkedMonicFibre

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
noncomputable section
open Polynomial Algebra Module
open scoped Polynomial TensorProduct

section Specialized
variable {A K : Type*} [CommRing A] [Field K]

/-- A separable ordinate quotient has no nilpotents, including when the
polynomial has more than one irreducible factor. -/
theorem separable_adjoinRoot_reduced (q : (Polynomial K)) (sep : q.Separable) : IsReduced (AdjoinRoot q) := by
  constructor
  intro x h
  induction x using AdjoinRoot.induction_on with
  | _ r =>
    obtain ⟨n,hn⟩ := h
    by_cases nn : n=0
    · have one0 : (1:AdjoinRoot q)=0 := by simpa only [nn,pow_zero] using hn
      calc AdjoinRoot.mk q r = 1*AdjoinRoot.mk q r := (one_mul _).symm
        _ = 0 := by rw [one0,zero_mul]
    · have qr : q∣r^n := AdjoinRoot.mk_eq_zero.mp (by rw [map_pow]; exact hn)
      exact AdjoinRoot.mk_eq_zero.mpr ((sep.squarefree.dvd_pow_iff_dvd nn).mp qr)

/-- A separable specialized monic equation has nonzero power-basis
trace discriminant in characteristic larger than its degree, even when
the quotient is a product. -/
theorem monic_disc_nonzero_at {f : (Polynomial A)} (hf : f.Monic) (j : A→+*K)
    (p : ℕ) [CharP K p] (small : f.natDegree<p) (sep : (f.map j).Separable) :
    j (monicDisc hf)≠0 := by
  let q := f.map j
  have hq : q.Monic := hf.map j
  have deg : q.natDegree=f.natDegree := hf.natDegree_map j
  let v := AdjoinRoot.powerBasis' hq
  let b : Basis (Fin f.natDegree) K (AdjoinRoot q) := v.basis.reindex (finCongr deg)
  have pw (i : Fin f.natDegree) : b i=AdjoinRoot.root q^(i:ℕ) := by
    rw [show b i=v.basis ((finCongr deg).symm i) from Basis.reindex_apply _ _ _,v.basis_eq_pow]
    rfl
  have root : aeval (AdjoinRoot.root q) q=0 := by rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
  have identity : j (monicDisc hf)=Algebra.discr K b := monic_disc_of_basis hf j _ root b pw
  rw [identity,Algebra.discr_def]
  let : FiniteDimensional K (AdjoinRoot q) := Module.Finite.of_basis b
  have dims : finrank K (AdjoinRoot q)<p := (finrank_eq_card_basis b).trans_lt (by simpa using small)
  let : IsReduced (AdjoinRoot q) := separable_adjoinRoot_reduced q sep
  have nd : (Algebra.traceForm K (AdjoinRoot q)).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro x hx
    change x=0
    exact IsReduced.eq_zero x ((Lower6960.TraceSpecialization.trace_radical p dims x).mp hx)
  have mat : Algebra.traceMatrix K b=(Algebra.traceForm K (AdjoinRoot q)).toMatrix b := by
    apply Matrix.ext
    intro i j
    rw [Algebra.traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
  rw [mat]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp nd
end Specialized

section Fibre
variable {A F E K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [Field K]

/-- Specialize the original integral closure at the selected field map.
At a good monic equation it is the full separable ordinate quotient, with
the ordinate represented by the actual lifted root. -/
theorem monic_fibre_equiv {f : (Polynomial A)} (hf : f.Monic) (γ : E) (root : aeval γ f=0)
    (b : Basis (Fin f.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (j : A→+*K) (p : ℕ) [CharP K p] (small : f.natDegree<p) (sep : (f.map j).Separable) :
    let : Algebra A K := j.toAlgebra
    ∃ e : AdjoinRoot (f.map j) ≃ₐ[K] (K⊗[A] integralClosure A E),
      e (AdjoinRoot.root (f.map j))= (1:K) ⊗ₜ[A] (⟨γ,⟨f,hf,root⟩⟩:integralClosure A E) := by
  let : Algebra A K := j.toAlgebra
  let B := integralClosure A E
  let q := f.map j
  let x : B := ⟨γ,⟨f,hf,root⟩⟩
  have ib (i : Fin f.natDegree) : IsIntegral A (b i) := pow i ▸ x.property.pow _
  have disc : algebraMap A K (monicDisc hf)≠0 := monic_disc_nonzero_at hf j p small sep
  obtain ⟨bt,hbt⟩ := RetainedCrossingBasis.specialized_basis b ib (monicDisc hf)
    (fun x i=>monic_coordinates hf γ root b pow x i) K disc
  let image : B→ₐ[A] (K⊗[A] B) := Algebra.TensorProduct.includeRight
  have xroot : aeval x f=0 := by
    apply Subtype.ext
    exact (aeval_algHom_apply B.val x f).symm.trans root
  have imroot : aeval (image x) f=0 :=
    (aeval_algHom_apply image x f).trans (by rw [xroot,map_zero])
  have rootq : aeval (image x) q=0 := by
    change aeval (image x) (f.map (algebraMap A K))=0
    rw [aeval_map_algebraMap]
    exact imroot
  have qdeg : q.natDegree=f.natDegree := hf.natDegree_map j
  let bq : Basis (Fin f.natDegree) K (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis' (hf.map j)).basis.reindex (finCongr qdeg)
  let h : AdjoinRoot q→ₐ[K](K⊗[A] B) :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId _ _) (image x) rootq
  have β (i : Fin f.natDegree) : bt i=(image x)^(i:ℕ) := by
    rw [hbt,←map_pow]
    congr 1
    apply Subtype.ext
    exact pow i
  let e := bq.equiv bt (Equiv.refl _)
  have mapL : h.toLinearMap=e.toLinearMap := by
    apply bq.ext
    intro i
    change h (bq i)=e (bq i)
    have bi : bq i=AdjoinRoot.root q^(i:ℕ) := by
      rw [show bq i=(AdjoinRoot.powerBasis' (hf.map j)).basis ((finCongr qdeg).symm i) from
        Basis.reindex_apply _ _ _,(AdjoinRoot.powerBasis' (hf.map j)).basis_eq_pow]
      rfl
    rw [show e (bq i)=bt i from Basis.equiv_apply (b:=bq) (b':=bt) (e:=Equiv.refl _) (i:=i),
      bi,map_pow,AdjoinRoot.liftAlgHom_root,β]
  have bij : Function.Bijective h := by
    change Function.Bijective h.toLinearMap
    rw [mapL]
    exact e.bijective
  change ∃ e : AdjoinRoot q ≃ₐ[K] (K⊗[A] B),e (AdjoinRoot.root q)=image x
  refine ⟨AlgEquiv.ofBijective h bij,?_⟩
  change h (AdjoinRoot.root q)=image x
  exact AdjoinRoot.liftAlgHom_root q (Algebra.ofId K (K⊗[A] B)) (image x) rootq
end Fibre

#print axioms monic_disc_nonzero_at
#print axioms monic_fibre_equiv
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedMonicFibre

-- merged module R6961CollisionMarkedActualSheet
section Merged_R6961CollisionMarkedActualSheet

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

end Merged_R6961CollisionMarkedActualSheet

-- merged module R6961CollisionMarkedProjected
section Merged_R6961CollisionMarkedProjected

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open Polynomial Lower6960.NormalizedFiber Module
open K1_14 (L)
open RetainedCompression (MarkedFiber specialize incl eval_swap)
open scoped Polynomial TensorProduct Lower6960.CollisionMarked Lower6961.CollisionMarked

/-- Put the actual scalar coordinate in the outer plane variable, as used
by the quotient defining `Lower6960.NormalizedFiber.Fiber`. -/
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

/-- The native full/separable mark gives the generic word projector in
the actual quotient of the plane normalization. -/
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
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedProjected

-- merged module R6961MarkedTranslatedEquation
section Merged_R6961MarkedTranslatedEquation

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedSurfaceClass Lower6960.NormalizedFiber Lower6960.CollisionMarked Lower6961.CollisionMarked Polynomial Algebra
open scoped Polynomial Lower6960.MonicChart Lower6961.MonicChart
open Lower6961.RetainedSurfaceClass (oriented_var oriented_const oriented_line)

def translatedX (c:L) : (Polynomial L)→+*Scalar := (translateField Scalar c).toRingHom.comp (algebraMap (Polynomial L) Scalar)
def rowPlane (c:L) : Plane L→+*(Polynomial Scalar) := eval₂RingHom (C.comp (translatedX c)) Polynomial.X
local notation "fp" => algebraMap (Polynomial Scalar) ChartField

private theorem translatedX_const (c a:L) : translatedX c (C a)=inner a := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar (C a))=_
  rw [translate_polynomial,taylor_C];rfl
private theorem translatedX_var (c:L) : translatedX c Polynomial.X=algebraMap (Polynomial L) Scalar Polynomial.X+inner c := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar Polynomial.X)=_
  rw [translate_polynomial,taylor_X,map_add];rfl

/-- Every original coefficient becomes a polynomial in the scalar variable
after translating its physical abscissa and exchanging the axes. -/
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
          rw [Lower6961.RetainedSurfaceClass.oriented_const,row_constant,eval₂_C,RingHom.comp_apply,translatedX_const,RatFunc.algebraMap_C];rfl
        · change rowBase c ((oriented true false (C Polynomial.X)):ChartField)=fp ((C Polynomial.X).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6961.RetainedSurfaceClass.oriented_line,eval₂_C,RingHom.comp_apply,translatedX_var,RatFunc.algebraMap_C,map_add]
          exact row_abscissa c
      exact DFunLike.congr_fun innerEq v
    · change rowBase c ((oriented true false Polynomial.X):ChartField)=fp (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X)
      rw [Lower6961.RetainedSurfaceClass.oriented_var,eval₂_X,RatFunc.algebraMap_X];exact row_parameter c
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
    ((Lower6961.CollisionMarked.projectedRaw P).integralNormalization.map (genericFibreBase z)).Separable := by
  let raw:=Lower6961.CollisionMarked.projectedRaw P
  let J:=genericFibreBase z
  have full:(raw.map J).natDegree=raw.natDegree := by
    rw [show raw.map J= _ from Lower6961.CollisionMarked.projectedRaw_fibre P z,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,Lower6961.CollisionMarked.projectedRaw_degree]
  have nz:J raw.leadingCoeff≠0 := fun bad=>(natDegree_map_lt' bad (Lower6961.CollisionMarked.projectedRaw_degree P ▸ lo)).ne full
  have base:(raw.map J).Separable := Lower6961.CollisionMarked.projectedRaw_fibre P z ▸ mark.separable
  rw [←integralNormalization_map J raw nz]
  apply Lower6961.CollisionMarked.integralNormalization_separable p _ _ _ base <;> rwa [full,Lower6961.CollisionMarked.projectedRaw_degree]

theorem marked_row_separable (c z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p) (mark:RetainedCompression.MarkedFiber P z S) :
    ((((Lower6961.CollisionMarked.projectedRaw P).integralNormalization.map (rowPlane c)).map (evalRingHom (inner z)))).Separable := by
  rw [Polynomial.map_map,row_specialization,←Polynomial.map_map]
  exact (normalized_fibre_separable z P S p lo hi mark).map

/-- The horizontal embedding preserves the degree of the actual scaled
ordinate, including its arbitrary nonzero leading-coefficient multiplier. -/
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
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedTranslatedEquation
