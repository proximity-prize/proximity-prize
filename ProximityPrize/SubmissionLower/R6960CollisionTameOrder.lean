import ProximityPrize.SubmissionLower.R6960CollisionTameSmith
import ProximityPrize.SubmissionLower.R6960TameTrace
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Trace.Quotient

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Matrix Module IsLocalRing
open scoped Matrix BigOperators

section Pairing
variable {A B K C ι : Type*} [CommRing A] [IsDomain A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B] [Algebra A B]
  [Field K] [CommRing C] [Algebra K C] [FiniteDimensional K C] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem trace_one_layer (π : A) (pn : π≠0) (bn : algebraMap A B π≠0)
    (base : A→+*K) (red : B→+*C) (onto : Function.Surjective red)
    (kerA : ∀ z,base z=0 ↔ π∣z) (kerB : ∀ z,red z=0 ↔ algebraMap A B π∣z)
    (tr : ∀ z,base (Algebra.trace A B z)=Algebra.trace K C (red z))
    (p : ℕ) [CharP K p] (small : finrank K C<p) (b : Basis ι A B) :
    ∀ u : ι→A,(∀ i,π^2∣((Algebra.traceMatrix A b)*ᵥu) i) → ∀ i,π∣u i := by
  intro u deep
  let w := b.equivFun.symm u
  have wsum : (∑ i,u i • b i)=w := (b.equivFun_symm_apply u).symm
  have row (i : ι) : Algebra.trace A B (w*b i)=((Algebra.traceMatrix A b)*ᵥu) i := by
    rw [←wsum,Finset.sum_mul,map_sum]
    change (∑ j, Algebra.trace A B ((u j • b j)*b i)) =
      ∑ j,Algebra.traceMatrix A b i j * u j
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc,map_smul]
    simp only [smul_eq_mul,Algebra.traceMatrix_apply,Algebra.traceForm_apply,mul_comm (b j),mul_comm (u j)]
  have killed (z : B) : π^2∣Algebra.trace A B (w*z) := by
    have eq : (∑ i,b.equivFun z i • b i)=z :=
      (b.equivFun_symm_apply (b.equivFun z)).symm.trans (b.equivFun.symm_apply_apply z)
    conv_rhs => rw [←eq,Finset.mul_sum,map_sum]
    apply Finset.dvd_sum
    intro i _
    rw [mul_smul_comm,map_smul,smul_eq_mul,row]
    exact dvd_mul_of_dvd_right (deep i) _
  obtain ⟨q,hq⟩ := TameTrace.no_second_layer π pn bn base red onto kerA kerB tr p small w killed
  have eq : w=π • q := by simpa only [Algebra.smul_def] using hq
  have uv : u=π • b.equivFun q := by
    have exp := congrArg b.equivFun eq
    rw [b.equivFun.map_smul] at exp
    exact (b.equivFun.apply_symm_apply u).symm.trans exp
  intro i
  exact ⟨b.equivFun q i,congrFun uv i⟩
end Pairing

section Normalization
attribute [local instance] Ideal.Quotient.field
variable {A E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field E] [Algebra A E]

abbrev LocalOrder (A E : Type*) [CommRing A] [Field E] [Algebra A E] := integralClosure A E

abbrev ClosedOrder (A E : Type*) [CommRing A] [IsLocalRing A] [Field E] [Algebra A E] :=
  LocalOrder A E ⧸ (Ideal.map (algebraMap A (LocalOrder A E)) (maximalIdeal A))

omit [IsDomain A] [IsDiscreteValuationRing A] in
private theorem scalar_inj (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] : Function.Injective (algebraMap A E) := by
  rw [IsScalarTower.algebraMap_eq A F E]
  exact (algebraMap F E).injective.comp (IsFractionRing.injective _ _)

private theorem torsionFreeField (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] : Module.IsTorsionFree A E := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x zero
  rw [Algebra.smul_def,mul_eq_zero] at zero
  exact zero.imp (fun ha=>scalar_inj F (ha.trans (map_zero _).symm)) id

/-- The integral closure of a DVR in a finite separable field extension is
semilocal Dedekind and hence principal. All its maximal ideals lie over
the one residue point of the base. -/
theorem normalization_pid (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsPrincipalIdealRing (LocalOrder A E) := by
  let B := LocalOrder A E
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A F E B
  have baseInj : Function.Injective (algebraMap A B) := fun _ _ eq=>
    scalar_inj F (congrArg Subtype.val eq)
  let : Module.IsTorsionFree A B := Module.IsTorsionFree.of_smul_eq_zero fun a x eq=>by
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun ha=>baseInj (ha.trans (map_zero _).symm)) id
  have covers : {I : Ideal B | I.IsMaximal} ⊆ (maximalIdeal A).primesOver B := by
    intro P hp
    let : P.IsMaximal := hp
    have pm : (P.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    exact ⟨hp.isPrime,⟨(IsLocalRing.eq_maximalIdeal pm).symm⟩⟩
  exact IsPrincipalIdealRing.of_finite_maximals ((IsDedekindDomain.primesOver_finite (maximalIdeal A) B).subset covers)

variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] [Algebra F E]
  [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The order of the trace discriminant of the actual normalized local
order is the residue corank. In particular there is no higher-order
Smith factor. The residue field need not split the generic cover. -/
theorem normalized_trace_order (p : ℕ) [CharP (ResidueField A) p] (small : finrank F E<p)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι A (LocalOrder A E))
    (π : A) (pir : Irreducible π) :
    IsDiscreteValuationRing.addVal A ((Algebra.traceMatrix A b).det) =
      ((Fintype.card ι-((Algebra.traceMatrix A b).map (residue A)).rank : ℕ):ℕ∞) := by
  classical
  let B := LocalOrder A E
  let m := maximalIdeal A
  let mx := m.map (algebraMap A B)
  let red : B→+*ClosedOrder A E := Ideal.Quotient.mk mx
  let base : A→+*(A ⧸ maximalIdeal A) := Ideal.Quotient.mk _
  let : IsPrincipalIdealRing B := normalization_pid (A:=A) (E:=E) F
  let : Module.Finite A B := Module.Finite.of_basis b
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.IsTorsionFree A E := torsionFreeField F
  let : CharP (A ⧸ maximalIdeal A) p := inferInstanceAs (CharP (ResidueField A) p)
  let rb := IsLocalRing.basisQuotient b
  let : FiniteDimensional (A ⧸ maximalIdeal A) (ClosedOrder A E) := Module.Finite.of_basis rb
  have dim : finrank (A ⧸ maximalIdeal A) (ClosedOrder A E)<p := by
    rw [IsLocalRing.finrank_quotient_map,IsIntegralClosure.rank A F E B]
    exact small
  have kerA (z : A) : base z=0 ↔ π∣z := by
    change Ideal.Quotient.mk m z=0 ↔ _
    exact (Ideal.Quotient.eq_zero_iff_mem).trans (by
      change z∈maximalIdeal A ↔ π∣z
      rw [pir.maximalIdeal_eq,Ideal.mem_span_singleton])
  have kerB (z : B) : red z=0 ↔ algebraMap A B π∣z := by
    change Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) z=0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem,pir.maximalIdeal_eq,Ideal.map_span,Set.image_singleton,
      Ideal.mem_span_singleton]
  have comp (z : B) : base (Algebra.trace A B z)=Algebra.trace (A ⧸ maximalIdeal A) (ClosedOrder A E) (red z) :=
    (Algebra.trace_quotient_mk z).symm
  have nonunit (z : A) : ¬IsUnit z ↔ π∣z := by
    change z∈(maximalIdeal A) ↔ _
    rw [pir.maximalIdeal_eq,Ideal.mem_span_singleton]
  have bn : algebraMap A B π≠0 := by
    intro bad
    apply pir.ne_zero
    apply scalar_inj (A:=A) (E:=E) F
    rw [map_zero]
    exact congrArg Subtype.val bad
  have smith := matrix_order_corank π pir (Algebra.traceMatrix A b) base kerA nonunit
    (trace_one_layer π pir.ne_zero bn base red Ideal.Quotient.mk_surjective kerA kerB comp p dim b)
  have eq := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr smith
  rwa [AddValuation.map_pow,IsDiscreteValuationRing.addVal_uniformizer pir,nsmul_eq_mul,mul_one] at eq

#print axioms normalization_pid
#print axioms normalized_trace_order
end Normalization
end
end Lower6960.CollisionTame
