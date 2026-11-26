import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_RingTheory_MvPolynomial_Bidegree
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_PID
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Trace_Quotient
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6960LineEulerFree

section Merged6967_R6960CollisionMarkedDiscTransport
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open CollisionTame Module Algebra Matrix Polynomial

variable {A B F K E : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Field F] [Field K] [Field E]
    [Algebra A F] [IsFractionRing A F] [Algebra B K] [IsFractionRing B K]
    [Algebra A E] [Algebra B E] [Algebra F E] [Algebra K E]
    [IsScalarTower A F E] [IsScalarTower B K E]
    [FiniteDimensional F E] [FiniteDimensional K E]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable K E]

/-- The same normalized surface has the same trace-discriminant ideal
in different coordinates, under the literal base-ring isomorphism. -/
theorem discriminant_transport (e:A≃+*B) (f:F≃+*K)
    (base : ∀ a,algebraMap B K (e a)=f (algebraMap A F a))
    (root : ∀ x,algebraMap K E (f x)=algebraMap F E x) :
    (normalizationDiscriminant (A:=A) (E:=E) F).map e.toRingHom =
      normalizationDiscriminant (A:=B) (E:=E) K := by
  classical
  have hbase (a:A) : algebraMap B E (e a)=algebraMap A E a := by
    rw [IsScalarTower.algebraMap_apply B K E,base,root,←IsScalarTower.algebraMap_apply]
  have int (x:E) : IsIntegral A x↔IsIntegral B x := by
    constructor
    · rintro ⟨p,pm,hp⟩
      refine ⟨p.map e.toRingHom,pm.map _,?_⟩
      rw [eval₂_map,show (algebraMap B E).comp e.toRingHom=algebraMap A E from RingHom.ext hbase]
      exact hp
    · rintro ⟨p,pm,hp⟩
      have back (b:B) : algebraMap A E (e.symm b)=algebraMap B E b := by rw [←hbase,e.apply_symm_apply]
      refine ⟨p.map e.symm.toRingHom,pm.map _,?_⟩
      rw [eval₂_map,show (algebraMap A E).comp e.symm.toRingHom=algebraMap B E from RingHom.ext back]
      exact hp
  let Q : integralClosure A E≃integralClosure B E := {
    toFun := fun a=>⟨a,(int _).mp a.property⟩
    invFun := fun b=>⟨b,(int _).mpr b.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  let b := Module.finBasis F E
  let c := b.mapCoeffs f (fun a x=>by simp only [Algebra.smul_def,root])
  have eq : finrank K E=finrank F E :=
    (finrank_eq_card_basis c).trans (Fintype.card_fin _)
  have tr (x:E) : f (Algebra.trace F E x)=Algebra.trace K E x := by
    have same : (algebraMap K E).comp f.toRingHom=
      (RingEquiv.refl E).toRingHom.comp (algebraMap F E) := RingHom.ext root
    have h := Algebra.trace_eq_of_equiv_equiv f (RingEquiv.refl E) same x
    exact (congrArg f h).trans (f.apply_symm_apply _)
  let u := integralTraceForm (A:=A) (E:=E) F
  let v := integralTraceForm (A:=B) (E:=E) K
  have fm (a b:integralClosure A E) : e (u a b)=v (Q a) (Q b) := by
    apply IsFractionRing.injective B K
    rw [base]
    change f (algebraMap A F (integralTraceForm (A:=A) (E:=E) F a b)) =
      algebraMap B K (integralTraceForm (A:=B) (E:=E) K (Q a) (Q b))
    rw [integralTraceForm_map,integralTraceForm_map]
    exact tr _
  let I := Fin (finrank F E)
  have det (a:I→integralClosure A E) : e ((tupleGram u a).det) = (tupleGram v (Q ∘ a)).det := by
    have mat : (tupleGram u a).map e=(tupleGram v (Q ∘ a)) := by
      apply Matrix.ext
      intro i l
      exact fm (a i) (a l)
    exact (e.toRingHom.map_det _).trans (congrArg Matrix.det mat)
  unfold normalizationDiscriminant
  rw [eq]
  change (gramIdeal (ι:=I) u).map e.toRingHom=gramIdeal (ι:=I) v
  apply le_antisymm
  · apply (Ideal.map_le_iff_le_comap).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change e (tupleGram u a).det∈gramIdeal (ι:=I) v
    rw [det]
    exact gramIdeal_mem v _
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have h : Q ∘ (Q.symm ∘ a)=a := by funext i; exact Q.apply_symm_apply (a i)
    have hd := det (Q.symm ∘ a)
    rw [h] at hd
    change (tupleGram v a).det∈(gramIdeal (ι:=I) u).map e.toRingHom
    rw [←hd]
    exact Ideal.mem_map_of_mem e.toRingHom (gramIdeal_mem u (Q.symm ∘ a))

#print axioms discriminant_transport
end
end Lower6960.CollisionMarked

end Merged6967_R6960CollisionMarkedDiscTransport

section Merged6967_R6960CollisionTameFibreTrace
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module NormalizedFiber
open scoped Polynomial Matrix BigOperators
open Lower6960.NormalizedFiber (specialize)
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
local instance fibreRing (z : k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)
local instance fibreAlgebra (z : k) : Algebra (Polynomial k) (Fiber E z) :=
  @RingHom.toAlgebra (Polynomial k) (Fiber E z) _ (fibreRing (E:=E) z).toCommSemiring (baseMap E z)
private abbrev FieldDegree (k E : Type) [Field k] [Field E] [Algebra (FractionRing (Plane k)) E] :=
  Fin (finrank (FractionRing (Plane k)) E)
omit [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E] in
private theorem quotient_smul (z : k) (a : Plane k) (x : Order k E) :
    quotientMap E z (a • x)=a.eval (C z) • quotientMap E z x := by
  rw [Algebra.smul_def,map_mul,Algebra.smul_def]
  change quotientMap E z (algebraMap (Plane k) (Order k E) a)*quotientMap E z x=
    baseMap E z (a.eval (C z))*quotientMap E z x
  exact congrArg (· * quotientMap E z x) (Lower6960.NormalizedFiber.specialize E z a)
theorem trace_reduces_on_fibre (z : k) (b : Basis (FieldDegree k E) (Polynomial k) (Fiber E z))
    (bf : Basis (FieldDegree k E) (FractionRing (Plane k)) E)
    (u : FieldDegree k E→Order k E) (g : Plane k)
    (red : ∀ i,quotientMap E z (u i)=b i) (gen : ∀ i,bf i=(u i:E))
    (one : g.eval (C z)=1)
    (patch : ∀ w : Order k E,∃ t : FieldDegree k E→Plane k,(∑ i,t i • u i)=g • w)
    (x : Order k E) :
    (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) x 1).eval (C z)=
      Algebra.trace (Polynomial k) (Fiber E z) (quotientMap E z x) := by
  let A := Plane k
  let F := FractionRing A
  let j := algebraMap A F
  let ev := evalRingHom (C z)
  choose c hc using fun i=>patch (x*u i)
  have sumF (i : FieldDegree k E) :
      (∑ l,j (c i l) • bf l)=((g • x:Order k E):E)*bf i := by
    calc
      _ = ((∑ l,c i l • u l : Order k E):E) := by
        rw [show (((∑ l,c i l • u l : Order k E)):E) = ∑ l,((c i l • u l : Order k E):E)
          from (map_sum (Order k E).val _ _)]
        apply Finset.sum_congr rfl
        intro l _
        rw [gen,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      _ = _ := by
        rw [hc,gen]
        change g • ((x:E)*(u i:E))=(g • (x:E))*(u i:E)
        rw [smul_mul_assoc]
  have sumk (i : FieldDegree k E) :
      (∑ l,ev (c i l) • b l)=quotientMap E z x*b i := by
    calc
      _ = quotientMap E z (∑ l,c i l • u l) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun l _=>by rw [quotient_smul,red]; rfl
      _ = _ := by rw [hc,quotient_smul,one,one_smul,map_mul,red]
  have eq : integralTraceForm (A:=A) (E:=E) F (g • x) 1=∑ i,c i i := by
    apply IsFractionRing.injective A F
    rw [integralTraceForm_map,Subalgebra.coe_one,mul_one,map_sum,Algebra.trace_eq_matrix_trace bf]
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply,Algebra.leftMulMatrix_eq_repr_mul,←sumF i,bf.repr_sum_self]
  have fromA := congrArg ev eq
  rw [(integralTraceForm (A:=A) (E:=E) F).map_smul,LinearMap.smul_apply,smul_eq_mul,map_mul,map_sum] at fromA
  change g.eval (C z)*(integralTraceForm (A:=A) (E:=E) F x 1).eval (C z)=∑ i,ev (c i i) at fromA
  rw [one,one_mul] at fromA
  rw [fromA,Algebra.trace_eq_matrix_trace b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply,Algebra.leftMulMatrix_eq_repr_mul,←sumk i,b.repr_sum_self]
theorem gram_reduces_on_fibre (z : k) (b : Basis (FieldDegree k E) (Polynomial k) (Fiber E z))
    (bf : Basis (FieldDegree k E) (FractionRing (Plane k)) E)
    (u : FieldDegree k E→Order k E) (g : Plane k)
    (red : ∀ i,quotientMap E z (u i)=b i) (gen : ∀ i,bf i=(u i:E))
    (one : g.eval (C z)=1)
    (patch : ∀ w : Order k E,∃ t : FieldDegree k E→Plane k,(∑ i,t i • u i)=g • w) :
    (tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u).map (evalRingHom (C z))=
      Algebra.traceMatrix (Polynomial k) b := by
  apply Matrix.ext
  intro i j
  have same : integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i) (u j)=
      integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i*u j) 1 := by
    apply IsFractionRing.injective (Plane k) (FractionRing (Plane k))
    rw [integralTraceForm_map,integralTraceForm_map,Subalgebra.coe_mul,Subalgebra.coe_one,mul_one]
  change (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i) (u j)).eval (C z)=_
  rw [same,trace_reduces_on_fibre z b bf u g red gen one patch,map_mul,red,red,
    Algebra.traceMatrix_apply,Algebra.traceForm_apply]
theorem fibre_trace_det_associated (δ : Plane k)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z : k) :
    ∃ b : Basis (FieldDegree k E) (Polynomial k) (Fiber E z),
      Associated (Algebra.traceMatrix (Polynomial k) b).det (δ.eval (C z)) := by
  obtain ⟨b,bf,u,g,red,gen,one,patch⟩ := scalar_fibre_frames (E:=E) z
  let tr := integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))
  let n := Fintype.card (FieldDegree k E)
  let D := (tupleGram tr u).det
  let j := evalRingHom (C z)
  have divides : δ∣D := by
    have mem : D∈normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k)) :=
      gramIdeal_mem tr u
    rw [principal,Ideal.mem_span_singleton] at mem
    exact mem
  have δmem : δ∈normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k)) := by
    rw [principal]; exact Ideal.subset_span (Set.mem_singleton δ)
  have clear : D∣g^(2*n)*δ := gramIdeal_clear tr u g patch δ δmem
  have rev : j D∣j δ := by
    have d := map_dvd j clear
    rw [map_mul,map_pow,show j g=1 from one,one_pow,one_mul] at d
    exact d
  have eq := congrArg Matrix.det (gram_reduces_on_fibre z b bf u g red gen one patch)
  have det : j D=(Algebra.traceMatrix (Polynomial k) b).det := (RingHom.map_det j _).trans eq
  exact ⟨b,det ▸ (dvd_dvd_iff_associated.mp ⟨rev,map_dvd j divides⟩)⟩
#print axioms trace_reduces_on_fibre
#print axioms gram_reduces_on_fibre
#print axioms fibre_trace_det_associated
end
end Lower6960.CollisionTame

end Merged6967_R6960CollisionTameFibreTrace

section Merged6967_R6960CollisionTameBranch
set_option Elab.async false










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

end Merged6967_R6960CollisionTameBranch

section Merged6967_R6966ProofWordUnconstrainedPrice
set_option Elab.async false



set_option Elab.async false

namespace Research6966.WordUnconstrainedPrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceMarks
variable {σ K ι I:Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 600000

private theorem low_shift (p:σ→K) (k:ℕ) (pos:0<k) (Q:low σ K k) (w:σ→ℕ) (hw:∀ j,w j≤1) :
    shift p Q.val ∈ restrictWeightAtMost w (k-1) := by
  have h:Q.val∈restrictWeightAtMost (fun _:σ=>1) (k-1) := by
    apply mem_restrictWeightAtMost.mpr
    intro e he
    have d:e.degree<k:=Q.property he
    have eq:e.weight (fun _:σ=>1)=e.degree:=by rw [Finsupp.degree_eq_weight_one]
    omega
  apply bind₁_mem_restrictWeightAtMost (w:=fun _:σ=>1) _ h
  intro i
  exact (restrictWeightAtMost w 1).add_mem (X_mem_restrictWeightAtMost _ _ (hw i))
    (C_mem_restrictWeightAtMost _ (Nat.zero_le 1) _)

private theorem sep_weight (p:ι→σ→K) (rows:I→Pol σ K) (A D:ℕ) (w:σ→ℕ)
    (h:∀ i,rows i∈restrictWeightAtMost w D) (enough:∀ x,A≤(hits (p x) rows).card) (x:ι) :
    separator p rows 1 x∈restrictWeightAtMost w ((Fintype.card I-A)*D) := by
  classical
  let miss:=univ\hits (p x) rows
  have count:miss.card≤Fintype.card I-A := by
    have sz:=card_sdiff_add_card_eq_card (subset_univ (hits (p x) rows))
    rw [card_univ] at sz;dsimp [miss];have:=enough x;omega
  have tot: (∑_i∈miss,D)≤(Fintype.card I-A)*D := by simpa using Nat.mul_le_mul_right D count
  change (∏i∈miss,rows i)^1∈_
  rw [pow_one]
  exact restrictWeightAtMost_mono _ tot (prod_mem_restrictWeightAtMost (w:=w) miss (a:=fun _=>D)
    (p:=rows) (fun i _=>h i))

private theorem separator_orders (p:ι→σ→K) (rows:I→Pol σ K) (A d:ℕ) (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    (∀ x,eval (p x) (separator p rows 1 x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (separator p rows 1 y)∈high σ K (A-d)) := by
  have s:=separator_spec p rows (fun j=>∑i,(rows i).degreeOf j)
    (fun i j=>single_le_sum (fun u _=>Nat.zero_le ((rows u).degreeOf j)) (mem_univ i)) A d 1 enough shared
  simpa only [one_mul] using s.2

private theorem choose2 (k:ℕ) : (k+1).choose 2*2=k*(k+1) := by
  have eq:=Nat.choose_succ_right_eq (k+1) 1
  simpa only [Nat.choose_one_right,Nat.add_sub_cancel,Nat.mul_comm] using eq

private theorem choose3 (k:ℕ) : (k+2).choose 3*6=k*(k+1)*(k+2) := by
  have e:=Nat.choose_succ_right_eq (k+2) 2
  rw [Nat.add_sub_cancel] at e
  have b:=choose2 (k+1)
  nlinarith only [congrArg (·*2) e,congrArg (·*k) b]

/-- With a fixed initial value, the seed plane has one total-degree cap,
so its leading coefficient is half that of the two-axis rectangle. -/
theorem plane (p:ι→Fin 2→K) (rows:I→Pol (Fin 2) K) (h A d:ℕ) (gap:d<A)
    (height:∀ i,rows i∈restrictWeightAtMost (fun _=>1) h)
    (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    Fintype.card ι*(A-d)^2≤((Fintype.card I-A)*h+(A-d))^2 := by
  let k:=A-d
  let β:=(Fintype.card I-A)*h+k
  have kp:0<k:=by dsimp [k];omega
  have kb:k≤β:=Nat.le_add_left _ _
  obtain ⟨own,other⟩:=separator_orders p rows A d enough shared
  have onto:=interpolate_on p k (low (Fin 2) K β) (separator p rows 1) (by
    intro x Q
    have bound:=mul_mem_restrictWeightAtMost (sep_weight p rows A h (fun _=>1) height enough x)
      (low_shift (-(p x)) k kp Q (fun _=>1) (fun _=>le_rfl))
    intro e he
    have small:=mem_restrictWeightAtMost.mp bound e he
    change e.degree<β
    rw [Finsupp.degree_eq_weight_one]
    dsimp only [β];omega) own other
  have dim:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    (LinearEquiv.ofBijective _ (read_bijective (σ:=Fin 2) (K:=K) β)).finrank_eq] at dim
  have size (l:ℕ) (pos:0<l):finrank K (Local (Fin 2) K l)=(l+1).choose 2 := by
    obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
    simpa only [Fintype.card_fin,show m+1+1=m+2 by omega] using local_dimension (σ:=Fin 2) (K:=K) m
  rw [size k kp,size β (kp.trans_le kb)] at dim
  have sides: Fintype.card ι*(k*(k+1))≤β*(β+1):=by
    have h:=Nat.mul_le_mul_right 2 dim
    rwa [Nat.mul_assoc,choose2,choose2] at h
  have scaled: (k+1)*(Fintype.card ι*k^2)≤(k+1)*β^2 := by
    nlinarith only [Nat.mul_le_mul_right k sides,Nat.mul_le_mul_right β kb]
  exact Nat.le_of_mul_le_mul_left scaled (Nat.succ_pos _)

#print axioms plane

private def ordinate : Option (Fin 2)→ℕ:=fun i=>i.elim 1 (fun _=>0)
private def seed : Option (Fin 2)→ℕ:=fun i=>i.elim 0 (fun _=>1)

private theorem bidegree {P:Pol (Option (Fin 2)) K} {a b:ℕ} :
    P∈restrictBidegree (Fin 2) K a b ↔
    P∈restrictWeightAtMost ordinate a ∧ P∈restrictWeightAtMost seed b := by
  rw [mem_restrictBidegree,mem_restrictWeightAtMost,mem_restrictWeightAtMost]
  change (∀ e∈P.support,e none≤a ∧ e.some.degree≤b) ↔
    (∀ e∈P.support,e.weight ordinate≤a) ∧ (∀ e∈P.support,e.weight seed≤b)
  have aeq (e:Option (Fin 2)→₀ℕ):e.weight ordinate=e none:=Finsupp.weight_elim_one_zero e
  have beq (e:Option (Fin 2)→₀ℕ):e.weight seed=e.some.degree:=Finsupp.weight_elim_zero_one e
  constructor
  · intro h
    exact ⟨fun e he=>(aeq e).le.trans (h e he).1,fun e he=>(beq e).le.trans (h e he).2⟩
  · rintro ⟨h,g⟩ e he
    exact ⟨(aeq e).ge.trans (h e he),(beq e).ge.trans (g e he)⟩

/-- The unrestricted affine family has one initial-value coordinate
and a common total degree for its two seeds. The coefficient three
comes from the bidegree dimension of that exact space. -/
theorem affine (p:ι→Option (Fin 2)→K) (rows:I→Pol (Option (Fin 2)) K) (y s A d:ℕ) (gap:d<A)
    (height:∀ i,rows i∈restrictBidegree (Fin 2) K y s)
    (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x z,x≠z → ((hits (p x) rows)∩(hits (p z) rows)).card≤d) :
    Fintype.card ι*(A-d)^3≤3*((Fintype.card I-A)*y+(A-d))*((Fintype.card I-A)*s+(A-d))^2 := by
  let k:=A-d
  let «Y»:=(Fintype.card I-A)*y+k
  let S:=(Fintype.card I-A)*s+k
  have kp:0<k:=by dsimp [k];omega
  have ky:k≤«Y»:=Nat.le_add_left _ _
  have ks:k≤S:=Nat.le_add_left _ _
  obtain ⟨own,other⟩:=separator_orders p rows A d enough shared
  have onto:=interpolate_on p k (restrictBidegree (Fin 2) K («Y»-1) (S-1)) (separator p rows 1) (by
    intro x Q
    apply bidegree.mpr
    have first:=mul_mem_restrictWeightAtMost (sep_weight p rows A y ordinate (fun i=>(bidegree.mp (height i)).1) enough x)
      (low_shift (-(p x)) k kp Q ordinate (fun q=>by cases q <;> simp [ordinate]))
    have second:=mul_mem_restrictWeightAtMost (sep_weight p rows A s seed (fun i=>(bidegree.mp (height i)).2) enough x)
      (low_shift (-(p x)) k kp Q seed (fun q=>by cases q <;> simp [seed]))
    exact ⟨restrictWeightAtMost_mono _ (by dsimp only [«Y»];omega) first,
      restrictWeightAtMost_mono _ (by dsimp only [S];omega) second⟩) own other
  have dim:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul,finrank_restrictBidegree] at dim
  have localDim:finrank K (Local (Option (Fin 2)) K k)=(k+2).choose 3 := by
    have v:=local_dimension (σ:=Option (Fin 2)) (K:=K) (k-1)
    rw [Nat.sub_add_cancel kp,Fintype.card_option,Fintype.card_fin] at v
    rwa [show k-1+(2+1)=k+2 by omega] at v
  rw [localDim,Nat.card_fin,Nat.sub_add_cancel (kp.trans_le ky),show S-1+2=S+1 by omega] at dim
  have base:Fintype.card ι*(k*(k+1)*(k+2))≤3*«Y»*(S*(S+1)) := by
    nlinarith only [Nat.mul_le_mul_right 6 dim,congrArg (Fintype.card ι*·) (choose3 k),
      congrArg ((3*«Y»)*·) (choose2 S)]
  have cross:k*(S+1)≤S*(k+1):=by nlinarith only [ks]
  have ck:k^2*(S+1)≤S*(k+1)*(k+2):=by
    nlinarith only [Nat.mul_le_mul_left k cross,Nat.zero_le (S*(k+1))]
  have scaled:((k+1)*(k+2))*(Fintype.card ι*k^3)≤((k+1)*(k+2))*(3*«Y»*S^2):=by
    nlinarith only [Nat.mul_le_mul_right (k^2) base,Nat.mul_le_mul_left (3*«Y»*S) ck]
  exact Nat.le_of_mul_le_mul_left scaled (by positivity)

#print axioms affine

/-- Independent seed ceilings give the rectangular three-parameter
tariff. The common total-degree version above supplies the coefficient
three when the two seeds share their ceiling. -/
theorem three_axes (p:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (h:Fin 3→ℕ) (A d:ℕ) (gap:d<A)
    (height:∀ i j,(rows i).degreeOf j≤h j) (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    Fintype.card ι*(A-d)^3≤6*∏ j,WordSurfacePrice.side (Fintype.card I) A d (h j) := by
  classical
  let k:=A-d
  have pos:0<k:=by dsimp [k];omega
  obtain ⟨sep,cap,own,other⟩:=separators p rows h height A d 1 enough shared
  simp only [one_mul] at cap other
  have onto:=interpolate p k pos _ sep cap own other
  have rank:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,sum_const,card_univ,smul_eq_mul,rectangle_dimension] at rank
  have dim:finrank K (Local (Fin 3) K k)=(k+2).choose 3 := by
    have b:=local_dimension (σ:=Fin 3) (K:=K) (k-1)
    rw [Nat.sub_add_cancel pos,Fintype.card_fin] at b
    rwa [show k-1+3=k+2 by omega] at b
  rw [dim] at rank
  have scale (j:Fin 3):(Fintype.card I-A)*h j+(k-1)+1=WordSurfacePrice.side (Fintype.card I) A d (h j) := by
    rw [Nat.add_assoc,Nat.sub_add_cancel pos];rfl
  simp_rw [scale] at rank
  have fact:=choose3 k
  have lower:k^3≤k*(k+1)*(k+2):=by nlinarith
  have rhs:=Nat.mul_le_mul_right 6 rank
  change Fintype.card ι*k^3≤_
  nlinarith only [rhs,congrArg (Fintype.card ι*·) fact,Nat.mul_le_mul_left (Fintype.card ι) lower]

#print axioms three_axes
end
end Research6966.WordUnconstrainedPrice

end Merged6967_R6966ProofWordUnconstrainedPrice
