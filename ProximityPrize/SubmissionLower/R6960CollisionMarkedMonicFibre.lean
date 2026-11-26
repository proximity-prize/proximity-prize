import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Discriminant
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues

section Merged6967_R6960CollisionMarkedMonicFibre
set_option Elab.async false






set_option Elab.async false

-- merged module R6960CollisionMarkedMonicTrace
section Merged_R6960CollisionMarkedMonicTrace
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Algebra Module Matrix
open scoped Polynomial Matrix BigOperators
section Trace
variable {A R U V ι : Type*} [CommRing A] [CommRing R] [CommRing U] [CommRing V]
  [Algebra A U] [Algebra R V] [Fintype ι] [DecidableEq ι]
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
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedMonicTrace

-- merged module R6960CollisionMarkedMonicFibre
section Merged_R6960CollisionMarkedMonicFibre
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Algebra Module
open scoped Polynomial TensorProduct
section Specialized
variable {A K : Type*} [CommRing A] [Field K]
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
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedMonicFibre

end Merged6967_R6960CollisionMarkedMonicFibre

section Merged6967_R6960RetainedSurfaceClass
set_option Elab.async false





set_option Elab.async false

-- merged module R6960RetainedNodalIndex
section Merged_R6960RetainedNodalIndex
noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedNodalIndex
open Module LinearMap Submodule
variable {k M N U V C : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
def boundaries (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C) :
    Submodule k (U×V) :=
  (LinearMap.ker (x.coprod (-z))).map (d₁.prodMap d₂)
private theorem representative (d : M→ₗ[k]U) :
    ∃ p : U→ₗ[k]M, ∀ x∈d.range, d (p x)=x := by
  obtain ⟨r,hr⟩:=d.rangeRestrict.exists_rightInverse_of_surjective d.range_rangeRestrict
  obtain ⟨q,hq⟩:=d.range.exists_isCompl
  refine ⟨r.comp (d.range.projectionOnto q hq),fun x hx=>?_⟩
  have l:=LinearMap.congr_fun hr (⟨x,hx⟩ : d.range)
  rw [comp_apply,projectionOnto_apply_of_mem_left hq hx]
  exact congrArg Subtype.val l
theorem dimension (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C)
    [FiniteDimensional k (U ⧸ d₁.range)] [FiniteDimensional k (V ⧸ d₂.range)] [FiniteDimensional k C] :
    let B := boundaries d₁ d₂ x z
    let W := d₁.ker.map x ⊔ d₂.ker.map z
    FiniteDimensional k ((U×V) ⧸ B) ∧
      finrank k ((U×V) ⧸ B)+finrank k W ≤
        finrank k (U ⧸ d₁.range)+finrank k (V ⧸ d₂.range)+finrank k C := by
  let B:=boundaries d₁ d₂ x z
  let W:=d₁.ker.map x ⊔ d₂.ker.map z
  let J:=x.coprod (-z)
  obtain ⟨p,hp⟩:=representative d₁
  obtain ⟨q,hq⟩:=representative d₂
  let pick:=p.prodMap q
  let h: (U×V) →ₗ[k] ((U ⧸ d₁.range)×(V ⧸ d₂.range))×(C ⧸ W) :=
    (d₁.range.mkQ.prodMap d₂.range.mkQ).prod (W.mkQ.comp (J.comp pick))
  have kernel : h.ker=B := by
    ext e
    rcases e with ⟨u,v⟩
    have calc_ker : (u,v)∈h.ker ↔ u∈d₁.range ∧ v∈d₂.range ∧ x (p u)-z (q v)∈W := by
      change ((d₁.range.mkQ u,d₂.range.mkQ v),W.mkQ (x (p u)+ -z (q v)))=0 ↔ _
      simp only [Prod.mk_eq_zero,←sub_eq_add_neg,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,and_assoc]
    rw [calc_ker]
    constructor
    · rintro ⟨hu,hv,hj⟩
      obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp hj
      refine ⟨(p u-a,q v+b),?_,?_⟩
      · change x (p u-a)+(-z) (q v+b)=0
        rw [map_sub,LinearMap.neg_apply,map_add]
        calc _ = (x (p u)-z (q v))-(x a+z b) := by abel
             _ = 0 := sub_eq_zero.mpr eq.symm
      · change (d₁ (p u-a),d₂ (q v+b))=(u,v)
        rw [map_sub,map_add,mem_ker.mp ha,mem_ker.mp hb,hp u hu,hq v hv,sub_zero,add_zero]
    · rintro ⟨⟨a,b⟩,join,eq⟩
      obtain ⟨rfl,rfl⟩: d₁ a=u ∧ d₂ b=v :=
        ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
      change x a+(-z) b=0 at join
      have ju : x a=z b := sub_eq_zero.mp (by simpa only [LinearMap.neg_apply,←sub_eq_add_neg] using join)
      have h₁ : p (d₁ a)-a∈d₁.ker := by rw [mem_ker,map_sub,hp _ ⟨a,rfl⟩,sub_self]
      have h₂ : b-q (d₂ b)∈d₂.ker := by rw [mem_ker,map_sub,hq _ ⟨b,rfl⟩,sub_self]
      refine ⟨⟨a,rfl⟩,⟨b,rfl⟩,Submodule.mem_sup.mpr ⟨_,⟨_,h₁,rfl⟩,_,⟨_,h₂,rfl⟩,?_⟩⟩
      rw [map_sub,map_sub,ju]; abel
  let e:=((Submodule.quotEquivOfEq B h.ker kernel.symm).trans h.quotKerEquivRange)
  have : FiniteDimensional k ((U×V) ⧸ B) := FiniteDimensional.of_injective e.toLinearMap e.injective
  have bound:=Submodule.finrank_le h.range
  rw [←e.finrank_eq,Module.finrank_prod,Module.finrank_prod] at bound
  refine ⟨inferInstance,?_⟩
  change finrank k ((U×V) ⧸ B)+finrank k W ≤ _
  have eq:=W.finrank_quotient_add_finrank
  omega
#print axioms dimension
end Lower6960.RetainedNodalIndex

end
end Merged_R6960RetainedNodalIndex

-- merged module R6960RetainedSurfaceClass
section Merged_R6960RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open ChartSections (Chart)
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
abbrev Tor := integralClosure torus E

private def constantsTor : L →+* Tor E :=
  ((algebraMap (↥torus) (Tor E)).comp (constants.codRestrict torus
    (fun c=>base_torus (false,false) (chart_constant _ c))))
scoped instance constantAlgebra : Algebra L (Tor E) := (constantsTor E).toAlgebra
open scoped Lower6960.RetainedSurfaceClass

private def scalar (a:ChartField) (reg:a∈torus) : Tor E :=
  algebraMap (↥torus) (Tor E) ⟨a,reg⟩

def cut (j : Bool) (c:L) : Tor E := scalar E (divisor j c) (torus.sub_mem
  (torus_coordinate j false) (base_torus (false,false) (chart_constant _ c)))

def axisIdeal (j:Bool) (c:L) : Ideal (Tor E) := Ideal.span {cut E j c}
abbrev Axis (j:Bool) (c:L) := (Tor E) ⧸ axisIdeal E j c
abbrev Crossing (x z:L) := Tor E ⧸ (axisIdeal E false x ⊔ axisIdeal E true z)
abbrev red (j:Bool) (c:L) : Tor E →ₗ[L] Axis E j c :=
  (Ideal.Quotient.mkₐ L (axisIdeal E j c)).toLinearMap

def crossingX (x z:L) : Axis E false x →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_left)).toLinearMap
def crossingZ (x z:L) : Axis E true z →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_right)).toLinearMap

def chartSpace (s:Chart) : Submodule L (Tor E) where
  carrier:={u | IsIntegral (baseChart s) (u:E)}
  zero_mem' := isIntegral_zero
  add_mem' a b:=a.add b
  smul_mem' r _ hu:=
    (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul hu

def chartImage (j:Bool) (c:L) (bit:Bool) :=
  (chartSpace E (reference j bit)).map (red E j c)

def difference (j:Bool) (c:L) :
    (chartImage E j c false × chartImage E j c true) →ₗ[L] Axis E j c :=
  (chartImage E j c false).subtype.coprod (-(chartImage E j c true).subtype)

def evalX (x z:L) := (crossingX E x z).comp
  ((chartImage E false x false).subtype.comp (LinearMap.fst L (chartImage E false x false) (chartImage E false x true)))
def evalZ (x z:L) := (crossingZ E x z).comp
  ((chartImage E true z false).subtype.comp (LinearMap.fst L (chartImage E true z false) (chartImage E true z true)))
abbrev Paired (x z:L) := (Axis E false x × Axis E true z) ⧸
  RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)

def potentials : Submodule L (Chart→Tor E) where
  carrier := {u | ∀ s t, IsIntegral (overlapRing s t) ((u s:E)-(u t:E))}
  zero_mem' := fun s t=>by simpa using (isIntegral_zero (B:=E) (R:=overlapRing s t))
  add_mem' {u v} hu hv s t := by
    change IsIntegral _ (((u s:E)+v s)-((u t:E)+v t))
    convert (hu s t).add (hv s t) using 1 <;> abel
  smul_mem' r u hu s t := by
    change IsIntegral _ ((algebraMap ChartField E (constants r))*(u s:E)-(algebraMap ChartField E (constants r))*(u t:E))
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨constants r,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))).mul (hu s t)

def coboundaries : Submodule L (potentials E) where
  carrier := {u | ∃ c:E, ∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)}
  zero_mem' := ⟨0,fun s=>by simpa using (isIntegral_zero (B:=E) (R:=baseChart s))⟩
  add_mem' {u v} hu hv := by
    obtain ⟨c,hc⟩:=hu; obtain ⟨d,hd⟩:=hv
    refine ⟨c+d,fun s=>?_⟩
    change IsIntegral _ (((u.1 s:E)+v.1 s)-(c+d))
    convert (hc s).add (hd s) using 1 <;> abel
  smul_mem' r u hu := by
    obtain ⟨c,hc⟩:=hu
    let scalar:=algebraMap ChartField E (constants r)
    refine ⟨scalar*c,fun s=>?_⟩
    change IsIntegral _ (scalar*(u.1 s:E)-scalar*c)
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul (hc s)

private def atChart (s:Chart) : potentials E→ₗ[L]Tor E :=
  (LinearMap.proj s).comp (potentials E).subtype
def rawMap (x z:L) : potentials E →ₗ[L] Paired E x z :=
  let lines:=(red E false x ∘ₗ (atChart E (false,false)-atChart E (reference false true))).prod
    (red E true z ∘ₗ (atChart E (false,false)-atChart E (reference true true)))
  (RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)).mkQ.comp lines

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

theorem congr_of_eq (j c) (a b:Tor E) (eq : red E j c a=red E j c b) :
    Congruent j c (a:E) (b:E) := by
  obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp eq)
  exact ⟨r,r.property,congrArg Subtype.val hr⟩

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap wordDegree)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
#print axioms restriction_kernel
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedSurfaceClass

end Merged6967_R6960RetainedSurfaceClass

section Merged6967_R6966ProofFarPrefix
set_option Elab.async false



set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.FarMainGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open FarRescueGeometry (Model Family OnMark OnSurface SurfacePass word curveMarks mem_curveMarks
  curve_tariff rated_curve_count fixedFee lambda mu tau)
open Lower6960.FarRescueGeometry (fixedFee_eq)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤33697) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    FarRescueGeometry.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤33697) {i : ℕ} (hi : i<17) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks R.family (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33697) : C.lossMarks.card ≤ (lossLimit).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 17,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33697) : C.paid.card≤mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤33697) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card≤123697974445940554 ∧ (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S,geom,surface⟩ := ini.terminal_surfaces
  refine ⟨C.paid,S,(C.paid_count hi).trans main_fee_bound,geom,?_⟩
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range 17).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
#print axioms Rows.main_prefix
end Lower6960.FarMainGeometry

end
end Merged_R6960MainGeometryFee

section Merged_R6960MainGeometryUnion
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.FarMainGeometry
open Finset
open K1 (K)
open K1_14 (jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_3 (Surface Parent ProjectedProduct)
open FarRescueGeometry (Model Family OnSurface SurfacePass word exceptional_prefix)
open scoped Classical
def prefixCap : ℕ := 244821410607897396
theorem Rows.combined_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (lo : 2523≤M.overhead.toNat) (hi : M.overhead.toNat≤33697)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨main,left,fee,passing,cover⟩ := R.main_prefix hi noPole residues
  rcases R.out.kind with unit | common
  · refine ⟨main,left,fee.trans (by decide +kernel),passing,?_⟩
    intro γ hγ
    apply cover
    exact mem_filter.mpr ⟨hγ,by simp [unit,jetAt]⟩
  · obtain ⟨rescue,right,cost,retains,rescue_cover⟩ :=
      exceptional_prefix F Crt lo hi noPole residues common
    refine ⟨main∪rescue,left∪right,
      (card_union_le _ _).trans ((Nat.add_le_add fee cost).trans (by decide +kernel)),?_,?_⟩
    · intro q hq
      exact (mem_union.mp hq).elim (passing q) (retains q)
    · intro γ hγ
      let lift (paid' : Finset K) (S' : Finset Surface)
          (hp : paid'⊆main∪rescue) (hs : S'⊆left∪right)
          (on : γ∈paid' ∨ ∃ q∈S',OnSurface F q γ) :
          γ∈main∪rescue ∨ ∃ q∈left∪right,OnSurface F q γ := by
        rcases on with mark | ⟨q,hq,hmark⟩
        · exact Or.inl (hp mark)
        · exact Or.inr ⟨q,hs hq,hmark⟩
      by_cases e : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
      · exact lift rescue right subset_union_right subset_union_right (rescue_cover γ hγ e)
      · exact lift main left subset_union_left subset_union_left
          (cover γ (mem_filter.mpr ⟨hγ,e⟩))
theorem combined_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2523≤M.overhead.toNat) (hi : M.overhead.toNat≤33697)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (S.Nonempty → ∃ f,ProjectedProduct S f) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨paid,S,fee,geom,cover⟩ := R.combined_prefix lo hi noPole residues
  exact ⟨paid,S,fee,geom,fun hs=>K1_14_3_7.proof S hs (fun q hq=>(geom q hq).1),cover⟩
#print axioms Rows.combined_prefix
#print axioms combined_prefix
end Lower6960.FarMainGeometry

end
end Merged_R6960MainGeometryUnion

end Merged6967_R6966ProofFarPrefix
