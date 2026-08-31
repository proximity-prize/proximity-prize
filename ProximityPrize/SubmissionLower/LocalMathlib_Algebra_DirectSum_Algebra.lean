/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Eric Wieser
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_Algebra_DirectSum_Ring
section ProximityFlatProofPort
universe uι uR uA uB
variable {ι:Type uι}
namespace DirectSum
open DirectSum
variable (R:Type uR) (A:ι → Type uA) {B:Type uB}
variable [CommSemiring R] [∀ i,AddCommMonoid (A i)] [∀ i,Module R (A i)]
variable [AddMonoid ι] [GSemiring A]
section
class GAlgebra where
  toFun:R →+A 0
  map_one:toFun 1=GradedMonoid.GOne.one
  map_mul:
    ∀ r s,GradedMonoid.mk _ (toFun (r*s))=.mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
  commutes:∀ (r) (x:GradedMonoid A),.mk _ (toFun r)*x=x*.mk _ (toFun r)
  smul_def:∀ (r) (x:GradedMonoid A),r • x=.mk _ (toFun r)*x
end
variable [Semiring B] [GAlgebra R A] [Algebra R B]
instance _root_.GradedMonoid.smulCommClass_right:
    SMulCommClass R (GradedMonoid A) (GradedMonoid A) where
  smul_comm s x y:=by
    dsimp
    rw [GAlgebra.smul_def,GAlgebra.smul_def, ←mul_assoc,GAlgebra.commutes,mul_assoc]
instance _root_.GradedMonoid.isScalarTower_right:
    IsScalarTower R (GradedMonoid A) (GradedMonoid A) where
  smul_assoc s x y:=by
    dsimp
    rw [GAlgebra.smul_def,GAlgebra.smul_def, ←mul_assoc]
variable [DecidableEq ι]
set_option backward.defeqAttrib.useBackward true in
instance:Algebra R (⨁ i,A i) where
  algebraMap:=
  { toFun:=(DirectSum.of A 0).comp GAlgebra.toFun
    map_zero':=map_zero _
    map_add':=map_add _
    map_one':=DFunLike.congr_arg (DirectSum.of A 0) GAlgebra.map_one
    map_mul' a b:=by
      simp only [AddMonoidHom.comp_apply]
      rw [of_mul_of]
      apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b)}
  commutes' r x:=by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x=AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi:2
    dsimp only [AddMonoidHom.comp_apply,AddMonoidHom.mul_apply,AddMonoidHom.flip_apply]
    rw [of_mul_of,of_mul_of]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i,xi⟩)
  smul_def' r x:=by
    change DistribSMul.toAddMonoidHom _ r x=AddMonoidHom.mul (DirectSum.of _ _ _) x
    apply DFunLike.congr_fun _ x
    ext i xi:2
    dsimp only [AddMonoidHom.comp_apply,DistribSMul.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of, ←of_smul]
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i,xi⟩)
theorem algebraMap_apply (r:R):
    algebraMap R (⨁ i,A i) r=DirectSum.of A 0 (GAlgebra.toFun r):=
  rfl
theorem algebraMap_toAddMonoid_hom:
    ↑(algebraMap R (⨁ i,A i))=(DirectSum.of A 0).comp (GAlgebra.toFun:R →+A 0):=
  rfl
@[simps]
def toAlgebra (f:∀ i,A i →ₗ[R] B) (hone:f _ GradedMonoid.GOne.one=1)
    (hmul:∀ {i j} (ai:A i) (aj:A j),f _ (GradedMonoid.GMul.mul ai aj)=f _ ai*f _ aj):
    (⨁ i,A i) →ₐ[R] B:=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun:=toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes':=fun r => by
      change toModule R _ _ f (algebraMap R _ r)=_
      rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,map_smul,one_def,
        ←lof_eq_of R,toModule_lof,hone]}
@[ext]
theorem algHom_ext' ⦃f g:(⨁ i,A i) →ₐ[R] B⦄
    (h:∀ i,f.toLinearMap.comp (lof _ _ A i)=g.toLinearMap.comp (lof _ _ A i)):f=g:=
  AlgHom.toLinearMap_injective <| DirectSum.linearMap_ext _ h
theorem algHom_ext ⦃f g:(⨁ i,A i) →ₐ[R] B⦄ (h:∀ i x,f (of A i x)=g (of A i x)):f=g:=
  algHom_ext' R A fun i => LinearMap.ext <| h i
@[simps]
def gMulLHom {i j}:A i →ₗ[R] A j →ₗ[R] A (i+j) where
  toFun a:=
    { toFun:=fun b => GradedMonoid.GMul.mul a b
      map_smul':=fun r x => by
        injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
      map_add':=GNonUnitalNonAssocSemiring.mul_add _}
  map_smul' r x:=LinearMap.ext fun y => by
    injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
  map_add' _ _:=LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _
end DirectSum
@[simps]
instance Algebra.directSumGAlgebra {R A:Type*} [AddMonoid ι] [CommSemiring R]
    [Semiring A] [Algebra R A]:DirectSum.GAlgebra R fun _:ι => A where
  toFun:=(algebraMap R A).toAddMonoidHom
  map_one:=(algebraMap R A).map_one
  map_mul a b:=Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes:=fun _ ⟨_,_⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def:=fun _ ⟨_,_⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
