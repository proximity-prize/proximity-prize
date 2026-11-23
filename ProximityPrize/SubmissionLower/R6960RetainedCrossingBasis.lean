import ProximityPrize.SubmissionLower.R6960MonicChartProbes
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedCrossingBasis
open Algebra Module
open scoped TensorProduct BigOperators

variable {A F E : Type*} [CommRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field E]
  [Algebra A E] [Algebra F E] [IsScalarTower A F E]

abbrev Order (A E : Type*) [CommRing A] [Field E] [Algebra A E] := integralClosure A E

/-- One denominator controls all coordinates of all integral elements. -/
theorem normal_frame (A F E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra A E] [Algebra F E]
    [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ b : Basis (Fin (finrank F E)) F E, (∀ i, IsIntegral A (b i)) ∧
      ∃ d : A, d≠0 ∧ ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d * b.repr (x:E) i := by
  classical
  obtain ⟨S,b,hb⟩:=FiniteDimensional.exists_is_basis_integral A F E
  let e := (Fintype.equivFin S).trans (finCongr (finrank_eq_card_basis b).symm)
  let B:=b.reindex e
  have ib (i) : IsIntegral A (B i) := by simpa [B] using hb (e.symm i)
  obtain ⟨d,nd,hd⟩:=exists_integral_multiples A F (Finset.univ.image B.traceDual)
  refine ⟨B,ib,d,nd,fun x i => ?_⟩
  have it:=isIntegral_trace (L:=F) ((hd (B.traceDual i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).mul x.property)
  have eq : trace F E ((d • B.traceDual i)*(x:E))=algebraMap A F d*B.repr (x:E) i := by
    have co:=B.traceDual.traceDual_repr_apply (x:E) i
    rw [Basis.traceDual_traceDual,traceForm_apply] at co
    rw [smul_mul_assoc,←IsScalarTower.algebraMap_smul F,map_smul,smul_eq_mul,mul_comm (B.traceDual i),←co]
  exact IsIntegrallyClosed.isIntegral_iff.mp (eq ▸ it)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion in the integral basis and its cleared inverse, over the original order. -/
theorem frame_maps (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i)) (d : A)
    (coords : ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d*b.repr (x:E) i) :
    ∃ toOrder : (ι→A) →ₗ[A] Order A E, ∃ back : Order A E →ₗ[A] (ι→A),
      (∀ i,toOrder (Pi.single i 1)=⟨b i,ib i⟩) ∧
      back.comp toOrder=d • LinearMap.id ∧ toOrder.comp back=d • LinearMap.id := by
  classical
  let inj:=IsFractionRing.injective A F
  choose c hc using coords
  let back : Order A E →ₗ[A] (ι→A) :=
    { toFun:=c
      map_add':=by
        intro u v; ext i; apply inj
        simp only [hc,map_add,Pi.add_apply,Subalgebra.coe_add,Finsupp.add_apply,mul_add]
      map_smul':=by
        intro r u; ext i; apply inj
        change algebraMap A F (c (r • u) i)=algebraMap A F (r*c u i)
        rw [hc,map_mul,hc]
        change _*b.repr (r • (u:E)) i=_
        rw [←IsScalarTower.algebraMap_smul F r (u:E),map_smul,Finsupp.smul_apply,smul_eq_mul]
        ring }
  let vec (i:ι) : Order A E := ⟨b i,ib i⟩
  let synth := (Pi.basisFun A ι).constr A vec
  have synth_eq (v : ι→A) : synth v=∑i,v i • vec i := by
    simp [synth,Basis.constr_apply_fintype]
  have std (i : ι) : synth (Pi.single i 1)=vec i := by
    rw [←Pi.basisFun_apply]
    exact Basis.constr_basis ..
  refine ⟨synth,back,std,?_,?_⟩
  · apply (Pi.basisFun A ι).ext
    intro i
    rw [Pi.basisFun_apply]
    change back (synth (Pi.single i 1))=d • Pi.single i 1
    rw [std]
    funext j
    apply inj
    change algebraMap A F (c (vec i) j)=algebraMap A F (d * (Pi.single i (1:A) : ι→A) j)
    rw [hc,map_mul]
    simp [vec,Basis.repr_self,Pi.single_apply,Finsupp.single_apply,eq_comm]
  · apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (synth (c u):E)=d • (u:E)
    rw [synth_eq,←IsScalarTower.algebraMap_smul F d (u:E)]
    push_cast
    calc ∑ i, c u i • (b i) = ∑ i, (algebraMap A F d*b.repr (u:E) i) • b i := by
           apply Finset.sum_congr rfl
           intro i _
           rw [←IsScalarTower.algebraMap_smul F, hc]
         _ = _ := by simp only [mul_smul,←Finset.smul_sum,b.sum_repr]

#print axioms normal_frame
#print axioms frame_maps

theorem specialized_basis (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i)) (d : A)
    (coords : ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d*b.repr (x:E) i)
    (k : Type*) [Field k] [Algebra A k] (unit : algebraMap A k d≠0) :
    ∃ B : Basis ι k (k ⊗[A] Order A E), ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E) := by
  obtain ⟨front,back,standard,left,right⟩:=frame_maps b ib d coords
  let f:=front.baseChange k
  let g:=back.baseChange k
  have l (x) : g (f x)=algebraMap A k d • x := by
    have eq := congrArg (LinearMap.baseChange k) left
    rw [LinearMap.baseChange_comp,LinearMap.baseChange_smul,LinearMap.baseChange_id] at eq
    simpa [f,g,algebraMap_smul] using LinearMap.congr_fun eq x
  have r (x) : f (g x)=algebraMap A k d • x := by
    have eq := congrArg (LinearMap.baseChange k) right
    rw [LinearMap.baseChange_comp,LinearMap.baseChange_smul,LinearMap.baseChange_id] at eq
    simpa [f,g,algebraMap_smul] using LinearMap.congr_fun eq x
  let equiv := LinearEquiv.ofBijective f (show Function.Bijective f from ⟨
    fun x y eq => by
      have v := congrArg g eq; rw [l,l] at v
      exact (smul_right_injective _ unit) v,
    fun x => ⟨(algebraMap A k d)⁻¹ • g x,by rw [map_smul,r,inv_smul_smul₀ unit]⟩⟩)
  refine ⟨((Pi.basisFun A ι).baseChange k).map equiv,fun i=>?_⟩
  change f (((Pi.basisFun A ι).baseChange k) i)=_
  rw [Basis.baseChange_apply,Pi.basisFun_apply]
  change 1 ⊗ₜ[A] front (Pi.single i 1)=_
  rw [standard]

#print axioms specialized_basis
end Lower6960.RetainedCrossingBasis
