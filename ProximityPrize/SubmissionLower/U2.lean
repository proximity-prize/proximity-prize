import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
open Module
namespace Ideal
variable {ι R S:Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]
noncomputable def basisSpanSingleton (b:Basis ι R S) {x:S} (hx:x≠0):
   Basis ι R (span ({x}:Set S)):=
 b.map <|
   LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
       LinearEquiv.ofEq _ _
         (by
           ext
           simp [mem_span_singleton',mul_comm]) ≪≫ₗ
     (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x}:Set S))).restrictScalars R
@[simp]
theorem basisSpanSingleton_apply (b:Basis ι R S) {x:S} (hx:x≠0) (i:ι):
   (basisSpanSingleton b hx i:S)=x*b i:=by
 simp only [basisSpanSingleton,Basis.map_apply,LinearEquiv.trans_apply,
   Submodule.restrictScalarsEquiv_apply,LinearEquiv.ofInjective_apply,LinearEquiv.coe_ofEq_apply,
   LinearEquiv.restrictScalars_apply,LinearMap.mulLeft_apply]
@[simp]
theorem constr_basisSpanSingleton {N:Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
   (b:Basis ι R S) {x:S} (hx:x≠0):
   (b.constr N).toFun (((↑):_ → S) ∘ (basisSpanSingleton b hx))=Algebra.lmul R S x:=
 b.ext fun i => by simp
end Ideal
theorem Basis.mem_ideal_iff {ι R S:Type*} [CommSemiring R] [Semiring S] [Algebra R S]
   {I:Ideal S} (b:Basis ι R I) {x:S}:
   x∈I ↔ ∃ c:ι →₀ R,x=Finsupp.sum c fun i x => x • (b i:S):=
 (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff
theorem Basis.mem_ideal_iff' {ι R S:Type*} [Fintype ι] [CommSemiring R] [Semiring S] [Algebra R S]
   {I:Ideal S} (b:Basis ι R I) {x:S}:x∈I ↔ ∃ c:ι → R,x=∑ i,c i • (b i:S):=
 (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
