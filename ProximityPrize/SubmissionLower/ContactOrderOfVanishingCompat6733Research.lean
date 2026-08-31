/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Raphael Douglas Giles
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_LocalRing_Length
open LinearMap Pointwise Ideal WithZero
variable {R:Type*} {M:Type*} [AddCommMonoid M]
namespace Ring
variable (R) [Ring R]
noncomputable def ord (x:R):ℕ∞:=Module.length R (R ⧸ Ideal.span {x})
@[simp] lemma ord_one:ord R 1=0:=by
  simp_all [ord,Ideal.span_singleton_one,Submodule.Quotient.subsingleton_iff]
end Ring
variable [CommRing R] [Module R M]
def Ideal.mulQuot (a:R) (I:Ideal R):
    R ⧸ I →ₗ[R] R ⧸ (a • I):=
  Submodule.mapQ _ _ (LinearMap.mul R R a) (Submodule.le_comap_map _ _)
lemma Ideal.mulQuot_injective {a:R} (I:Ideal R) (ha:a∈nonZeroDivisors R):
    Function.Injective (Ideal.mulQuot a I):=by
  simp only [mulQuot,Submodule.mapQ, ←ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot'
  apply le_antisymm
  · have:Submodule.map (mul R R a) I=a • I:=rfl
    rw [le_ker_iff_map,Submodule.map_comp,this,Submodule.mkQ_map_self]
  · have m:I=Submodule.comap (mul R R a) (a • I):=by
      ext b
      exact (Submodule.mul_mem_smul_iff ha).symm
    simp [←m,ker_comp]
def Ideal.quotOfMul (a:R) (I:Ideal R):
    (R ⧸ a • I) →ₗ[R] (R ⧸ Ideal.span {a}):=
  Submodule.factor <| Submodule.singleton_set_smul I a ▸ Submodule.smul_le_span {a} I
lemma Ideal.quotOfMul_surjective {a:R} (I:Ideal R):
    Function.Surjective (Ideal.quotOfMul a I):=by
  simp only [Ideal.quotOfMul]
  exact Submodule.factor_surjective <|
    Submodule.singleton_set_smul I a ▸ Submodule.smul_le_span {a} I
lemma Ideal.exact_mulQuot_quotOfMul {a:R} (I:Ideal R):
    Function.Exact (Ideal.mulQuot a I) (Ideal.quotOfMul a I):=by
  simp only [exact_iff]
  have:ker (Ideal.quotOfMul a I)=a • ⊤:=by
    simp only [←submodule_span_eq,quotOfMul,Submodule.factor,Submodule.mapQ,comp_id,
      Submodule.ker_liftQ,Submodule.ker_mkQ,Submodule.map_span,Submodule.mkQ_apply,
      Quotient.mk_eq_mk,Set.image_singleton,Quotient.smul_top]
  simp [this,Ideal.mulQuot,Submodule.mapQ.eq_1,Submodule.range_liftQ,
    range_comp,Ideal.Quotient.smul_top, ←Ideal.submodule_span_eq,LinearMap.map_span]
namespace Ring
variable (R)
theorem ord_mul {a b:R} (hb:b∈nonZeroDivisors R):
    ord R (a*b)=ord R a+ord R b:=by
  have hlen:=Module.length_eq_add_of_exact (Ideal.mulQuot b (Ideal.span {a}))
      (Ideal.quotOfMul b (Ideal.span {a}))
      (Ideal.mulQuot_injective (Ideal.span {a}) hb)
      (Ideal.quotOfMul_surjective (Ideal.span {a}))
      (Ideal.exact_mulQuot_quotOfMul (Ideal.span {a}))
  simp only [Ring.ord, ←hlen]
  have lem:(({b}:Set R) • Ideal.span {a})=Ideal.span {b*a}:=by
    simp [←Ideal.submodule_span_eq,Submodule.set_smul_span]
  have hs:(({b}:Set R) • Ideal.span {a})=b • Ideal.span {a}:=
    Submodule.singleton_set_smul (Ideal.span {a}) b
  rw [hs] at lem
  rw [lem,mul_comm]
lemma ord_mul' {a b:R} (ha:a∈nonZeroDivisors R):
    ord R (a*b)=ord R a+ord R b:=by
  rw [mul_comm,ord_mul R ha,add_comm]
variable {R}
@[simp] theorem ord_pow {x:R} (hx:x∈nonZeroDivisors R) (n:ℕ):
    ord R (x^n)=n • ord R x:=by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ord_mul,ih,succ_nsmul]
    exact hx
@[simp] lemma ord_mul_of_isUnit_left {a:R} (h:IsUnit a) (x:R):
    ord R (a*x)=ord R x:=by
  rw [ord,ord,Ideal.span_singleton_mul_left_unit h x]
@[simp] lemma ord_mul_of_isUnit_right {a:R} (h:IsUnit a) (x:R):
    ord R (x*a)=ord R x:=by
  rw [ord,ord,Ideal.span_singleton_mul_right_unit h x]
lemma ord_eq_of_associated {x y:R} (h:Associated x y):ord R x=ord R y:=by
  obtain ⟨a,rfl⟩:=h
  simp
@[simp] lemma ord_smul_of_isUnit {S:Type*} [CommRing S] [Algebra S R]
    {a:S} (h:IsUnit a) (x:R):ord R (a • x)=ord R x:=by
  rw [Algebra.smul_def a x]
  exact ord_mul_of_isUnit_left (RingHom.isUnit_map (algebraMap S R) h) x
@[simp] lemma ord_of_isUnit {x:R} (hx:IsUnit x):ord R x=0:=by
  simpa using ord_smul_of_isUnit hx (1:R)
section IsPrincipalIdealRing
variable [IsPrincipalIdealRing R]
theorem ord_of_irreducible {ϖ:R} (hϖ:Irreducible ϖ):ord R ϖ=1:=by
  rw [Ring.ord,Module.length_eq_one_iff]
  have:(Ideal.span {ϖ}).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hϖ
  rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (S:=R ⧸ Ideal.span {ϖ}) Ideal.Quotient.mk_surjective]
  letI:=Ideal.Quotient.field (Ideal.span {ϖ})
  exact instIsSimpleModule _
end IsPrincipalIdealRing
end Ring
