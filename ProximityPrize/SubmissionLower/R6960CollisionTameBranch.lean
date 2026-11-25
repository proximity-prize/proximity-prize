import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ProximityPrize.SubmissionLower.R6960CollisionTameSmith
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

set_option Elab.async false

-- merged module R6960TraceSpecialization
section Merged_R6960TraceSpecialization
noncomputable section
set_option Elab.async false
namespace Lower6960.TraceSpecialization
open LinearMap
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
theorem idempotent_multiple [IsArtinianRing A] (x : A) (nx : ¬IsNilpotent x) :
    ∃ h : A,(x*h)^2=x*h ∧ x*h≠0 := by
  obtain ⟨n,y,hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1:A)
  let r:=x*y
  have stable {s t : A} (fix : s*t=s) (j : ℕ) : s*t^j=s := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,←mul_assoc,ih,fix]
  have fixed : x^n*r=x^n := by simpa [r,pow_succ,mul_assoc] using hy
  have last : r^n*r=r^n := by
    have eq := congrArg (·*y^n) fixed
    simpa only [r,mul_pow,mul_assoc,mul_left_comm,mul_comm] using eq
  let h:=y*r^n
  have he : x*h=r^n := by dsimp [h]; rw [←mul_assoc,mul_comm (x*y)]; exact last
  refine ⟨h,?_,?_⟩
  · rw [he,pow_two]; exact stable last n
  · intro z
    have vanish:=stable fixed n
    rw [←he,z,mul_zero] at vanish
    exact nx ⟨n,vanish.symm⟩
theorem trace_radical (p : ℕ) [CharP K p] (small : Module.finrank K A<p) (x : A) :
    x∈LinearMap.ker (Algebra.traceForm K A) ↔ IsNilpotent x := by
  constructor
  · intro hx
    by_contra nx
    have : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
    obtain ⟨y,idemp,ne⟩ := idempotent_multiple x nx
    let e:=Algebra.lmul K A (x*y)
    have proj : IsIdempotentElem e := by
      change e*e=e
      change Algebra.lmul K A (x*y)*Algebra.lmul K A (x*y)=_
      rw [←map_mul,←pow_two,idemp]
    have trace : LinearMap.trace K A e=0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
    rw [proj.isProj_range.trace] at trace
    have low := (Submodule.finrank_le (LinearMap.range e)).trans_lt small
    have dim := Nat.eq_zero_of_dvd_of_lt ((CharP.cast_eq_zero_iff K p _).mp trace) low
    have bot : LinearMap.range e = ⊥ := Submodule.finrank_eq_zero.mp dim
    have zero := LinearMap.range_eq_bot.mp bot
    have bad := LinearMap.congr_fun zero (1:A)
    change (x*y)*1=0 at bad
    exact ne (by simpa only [mul_one] using bad)
  · intro nil
    apply LinearMap.mem_ker.mpr
    ext y
    change Algebra.trace K A (x*y)=0
    rw [Algebra.trace_apply]
    apply (LinearMap.isNilpotent_trace_of_isNilpotent _).eq_zero
    exact ((Commute.all x y).isNilpotent_mul_right nil).map (Algebra.lmul K A)
theorem radical_specialization {B : Type*} [CommRing B] [Algebra K B] [FiniteDimensional K B]
    (p : ℕ) [CharP K p] (a : Module.finrank K A<p) (b : Module.finrank K B<p)
    (φ : A →ₐ[K] B) :
    Module.finrank K (LinearMap.ker (Algebra.traceForm K A)) ≤
      Module.finrank K (LinearMap.ker φ.toLinearMap) + Module.finrank K (LinearMap.ker (Algebra.traceForm K B)) := by
  let U:=LinearMap.ker (Algebra.traceForm K A)
  let V:=LinearMap.ker (Algebra.traceForm K B)
  let g : U→ₗ[K]V := (φ.toLinearMap.comp U.subtype).codRestrict V (fun x=>
    (trace_radical p b _).mpr (((trace_radical p a _).mp x.property).map φ))
  let lift : LinearMap.ker g →ₗ[K] LinearMap.ker φ.toLinearMap :=
    (U.subtype.comp (LinearMap.ker g).subtype).codRestrict _ (fun x=>by
      apply LinearMap.mem_ker.mpr
      exact congrArg Subtype.val (LinearMap.mem_ker.mp x.property))
  have inj : Function.Injective lift := by
    intro x y eq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : LinearMap.ker φ.toLinearMap=>(w:A)) eq
  have ker := LinearMap.finrank_le_finrank_of_injective (f:=lift) inj
  have ran := Submodule.finrank_le (LinearMap.range g)
  have both := g.finrank_range_add_finrank_ker
  change Module.finrank K U≤_+Module.finrank K V
  omega
#print axioms trace_radical
#print axioms radical_specialization
end Lower6960.TraceSpecialization

end
end Merged_R6960TraceSpecialization

-- merged module R6960TameTrace
section Merged_R6960TameTrace
noncomputable section
set_option Elab.async false
namespace Lower6960.TameTrace
open Algebra
variable {A B K C : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] [Algebra A B] [Field K] [CommRing C]
    [Algebra K C] [FiniteDimensional K C]
private theorem first_layer (b : B) (bn : b≠0) (w : B) (nw : ¬b∣w)
    (red : B→+*C) (ker : ∀z,red z=0 ↔ b∣z) :
    ∃ m u:B,w*m=b*u ∧ ¬IsNilpotent (red u) := by
  obtain ⟨b',u,g,cop,gb,gu⟩ := UniqueFactorizationMonoid.exists_reduced_factors b bn w
  have nu : ¬IsUnit b' := by
    intro unit
    apply nw
    rw [←gb,←gu]
    exact mul_dvd_mul_left g unit.dvd
  refine ⟨b',u,by rw [←gb,←gu]; ring,?_⟩
  rintro ⟨n,hn⟩
  have dvd : b∣u^n := (ker _).mp (by rw [map_pow,hn])
  have part : b'∣b := gb ▸ dvd_mul_left ..
  have rel : IsRelPrime b' (u^n) := cop.pow_right
  exact nu (rel dvd_rfl (part.trans dvd))
theorem no_second_layer (π : A) (πn : π≠0) (bn : algebraMap A B π≠0)
    (base : A→+*K) (red : B→+*C) (surj : Function.Surjective red)
    (kerA : ∀z,base z=0 ↔ π∣z) (kerB : ∀z,red z=0 ↔ algebraMap A B π∣z)
    (trace_comp : ∀z,base (Algebra.trace A B z)=Algebra.trace K C (red z))
    (p : ℕ) [CharP K p] (small : Module.finrank K C<p)
    (w : B) (deep : ∀s,π^2∣Algebra.trace A B (w*s)) :
    algebraMap A B π∣w := by
  by_contra nw
  obtain ⟨m,u,eq,nu⟩ := first_layer (algebraMap A B π) bn w nw red kerB
  apply nu
  apply (TraceSpecialization.trace_radical p small _).mp
  apply LinearMap.mem_ker.mpr
  ext y
  obtain ⟨s,rfl⟩ := surj y
  change Algebra.trace K C (red u*red s)=0
  rw [←map_mul,←trace_comp]
  apply (kerA _).mpr
  have multiple := deep (m*s)
  rw [←mul_assoc,eq,mul_assoc,←Algebra.smul_def,map_smul,smul_eq_mul,pow_two] at multiple
  exact (mul_dvd_mul_iff_left πn).mp multiple
#print axioms no_second_layer
end Lower6960.TameTrace

end
end Merged_R6960TameTrace

-- merged module R6960CollisionTameOrder
section Merged_R6960CollisionTameOrder
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

end Merged_R6960CollisionTameOrder

-- merged module R6960CollisionTameBranch
section Merged_R6960CollisionTameBranch
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Ideal IsLocalRing
open scoped Matrix
variable {R : Type*} [CommRing R] [IsDomain R]
private theorem primeCompl_le (P : Ideal R) [P.IsPrime] : P.primeCompl≤nonZeroDivisors R := by
  intro z hz
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  rintro rfl
  exact (Ideal.mem_primeCompl_iff.mp hz) (P.zero_mem)
theorem branch_algebraMap_injective (P : Ideal R) [P.IsPrime] :
    Function.Injective (algebraMap R (Localization.AtPrime P)) :=
  IsLocalization.injective _ (primeCompl_le P)
omit [IsDomain R] in
theorem branch_maximal (P : Ideal R) [P.IsPrime] (q : R) (span : P=Ideal.span {q}) :
    maximalIdeal (Localization.AtPrime P)=Ideal.span {algebraMap R (Localization.AtPrime P) q} := by
  let A := Localization.AtPrime P
  calc
    _ = P.map (algebraMap R A) := (IsLocalization.AtPrime.map_eq_maximalIdeal P A).symm
    _ = (Ideal.span {q}).map (algebraMap R A) := congrArg (Ideal.map (algebraMap R A)) span
    _ = _ := by rw [Ideal.map_span,Set.image_singleton]
theorem principal_prime_dvr [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (q : R) (nonzero : q≠0)
    (span : P=Ideal.span {q}) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  let A := Localization.AtPrime P
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  have ideal := branch_maximal P q span
  have field : ¬IsField A := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq,ideal,Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (branch_algebraMap_injective P)).mpr nonzero
  have principal : (maximalIdeal A).IsPrincipal := ⟨_,ideal⟩
  exact ((IsDiscreteValuationRing.TFAE A field).out 5 1).mp principal
theorem branch_uniformizer (P : Ideal R) [P.IsPrime] (q : R) (nonzero : q≠0)
    (span : P=Ideal.span {q}) : Irreducible (algebraMap R (Localization.AtPrime P) q) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    ((map_ne_zero_iff _ (branch_algebraMap_injective P)).mpr nonzero) (branch_maximal P q span)
omit [IsDomain R] in
private theorem residue_kernel (P : Ideal R) [P.IsPrime] (x : R) :
    residue (Localization.AtPrime P) (algebraMap R _ x)=0 ↔ x∈P := by
  change Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime P)) (algebraMap R _ x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x∈(maximalIdeal (Localization.AtPrime P)).under R ↔ x∈P
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P]
def branchResidue (P : Ideal R) [P.IsPrime] : R ⧸ P →+* ResidueField (Localization.AtPrime P) :=
  Ideal.Quotient.lift P ((residue (Localization.AtPrime P)).comp (algebraMap R _))
    (fun x h=>(residue_kernel P x).mpr h)
omit [IsDomain R] in
@[simp] theorem branchResidue_mk (P : Ideal R) [P.IsPrime] (x : R) :
    branchResidue P (Ideal.Quotient.mk P x)=residue (Localization.AtPrime P) (algebraMap R _ x) :=
  rfl
omit [IsDomain R] in
theorem branchResidue_injective (P : Ideal R) [P.IsPrime] : Function.Injective (branchResidue P) := by
  apply (injective_iff_map_eq_zero (branchResidue P)).mpr
  intro a hz
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((residue_kernel P x).mp hz)
omit [IsDomain R] in
theorem branch_power_dvd_iff [DecompositionMonoid R] (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (n : ℕ) (a : R) :
    (algebraMap R (Localization.AtPrime P) q)^n∣algebraMap R (Localization.AtPrime P) a ↔ q^n∣a := by
  let A := Localization.AtPrime P
  let j := algebraMap R A
  constructor
  · intro hd
    have hP : (P^n).map j=Ideal.span {(j q)^n} := by
      rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal P A,
        branch_maximal P q span,Ideal.span_singleton_pow]
    have hz : j a∈(P^n).map j := hP.symm ▸ Ideal.mem_span_singleton.mpr hd
    obtain ⟨m,hm,hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl A (P^n) a).mp hz
    have notdiv : ¬q∣m := by
      intro dv
      apply (Ideal.mem_primeCompl_iff.mp hm)
      rw [span]
      exact Ideal.mem_span_singleton.mpr dv
    have src : q^n∣m*a := by
      have eq : P^n=Ideal.span {q^n} := congrArg (fun I : Ideal R=>I^n) span |>.trans (Ideal.span_singleton_pow _ _)
      exact Ideal.mem_span_singleton.mp (eq ▸ hma)
    exact ((pir.isRelPrime_iff_not_dvd).mpr notdiv).pow_left.dvd_of_dvd_mul_left src
  · intro dv
    rw [←map_pow]
    exact map_dvd (algebraMap R A) dv
theorem branch_order [IsNoetherianRing R] [DecompositionMonoid R] (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (a : R) :
    let : IsDiscreteValuationRing (Localization.AtPrime P) := principal_prime_dvr P q pir.ne_zero span
    IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R (Localization.AtPrime P) a)=
      emultiplicity q a := by
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := principal_prime_dvr P q pir.ne_zero span
  let j := algebraMap R A
  change IsDiscreteValuationRing.addVal A (j a)=_
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  have val : IsDiscreteValuationRing.addVal A ((j q)^n)=(n:ℕ∞) := by
    rw [AddValuation.map_pow,IsDiscreteValuationRing.addVal_uniformizer (branch_uniformizer P q pir.ne_zero span),
      nsmul_eq_mul,mul_one]
  rw [←pow_dvd_iff_le_emultiplicity,←val,IsDiscreteValuationRing.addVal_le_iff_dvd]
  exact branch_power_dvd_iff P q pir span n a
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
def branchFractionHom (P : Ideal R) [P.IsPrime] : Localization.AtPrime P →+* F :=
  IsLocalization.lift (M:=P.primeCompl) (g:=algebraMap R F) fun r=>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (primeCompl_le P r.property)))
@[simp] theorem branchFractionHom_apply (P : Ideal R) [P.IsPrime] (x : R) :
    branchFractionHom (F:=F) P (algebraMap R (Localization.AtPrime P) x)=algebraMap R F x :=
  IsLocalization.lift_eq _ _
theorem branchFraction_isFractionRing (P : Ideal R) [P.IsPrime] :
    let : Algebra (Localization.AtPrime P) F := (branchFractionHom (F:=F) P).toAlgebra
    IsFractionRing (Localization.AtPrime P) F := by
  let A := Localization.AtPrime P
  let : Algebra A F := (branchFractionHom (F:=F) P).toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (R:=R) (S:=A) (A:=F)
    (branchFractionHom_apply (F:=F) P · |>.symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A F
theorem trace_order_from_local_matrix [IsNoetherianRing R] [DecompositionMonoid R]
    (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q) (span : P=Ideal.span {q})
    {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq ι]
    [Algebra (Localization.AtPrime P) F] [IsFractionRing (Localization.AtPrime P) F]
    [Algebra (Localization.AtPrime P) E] [Algebra F E] [IsScalarTower (Localization.AtPrime P) F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (p : ℕ) [CharP (ResidueField (Localization.AtPrime P)) p] (small : Module.finrank F E<p)
    (b : Module.Basis ι (Localization.AtPrime P) (LocalOrder (Localization.AtPrime P) E))
    (M : Matrix ι ι R)
    (actual : M.map (algebraMap R (Localization.AtPrime P)) = Algebra.traceMatrix (Localization.AtPrime P) b) :
    emultiplicity q M.det=
      ((Fintype.card ι-((M.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) := by
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := principal_prime_dvr P q pir.ne_zero span
  let j := algebraMap R A
  have det : j M.det=(Algebra.traceMatrix A b).det := by
    have eq : (M.map j).det=j M.det := ((algebraMap R A).map_det M).symm
    exact eq.symm.trans (congrArg Matrix.det actual)
  have mapped : (Algebra.traceMatrix A b).map (residue A)=
      (M.map (Ideal.Quotient.mk P)).map (branchResidue P) := by rw [←actual]; rfl
  have ord := normalized_trace_order p small b (j q) (branch_uniformizer P q pir.ne_zero span)
  rw [←det,branch_order P q pir span,mapped] at ord
  exact ord
#print axioms principal_prime_dvr
#print axioms branchResidue_injective
#print axioms branchFraction_isFractionRing
#print axioms branch_order
#print axioms trace_order_from_local_matrix
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameBranch
