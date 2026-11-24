import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import ProximityPrize.SubmissionLower.Zdj6KNe
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace qIGP9Qa
noncomputable section
open Polynomial IsDedekindDomain
open scoped WithZero nonZeroDivisors
set_option maxSynthPendingDepth 12
open cu (L)
open E7 (CurvePlace)
open qNu3xvc qoCymac
variable {E :Type} [Field E] [Algebra L E]
omit [Algebra L E] in
theorem physical_injective (A:Equation E) :
  Function.Injective ((a7W A).comp Polynomial.C) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro a ha
 have hz :AdjoinRoot.mk A.f (Polynomial.C a)=0:= by
  apply IsFractionRing.injective (AdjoinRoot A.f) (EC A)
  rw [map_zero]
  exact ha
 by_contra hn
 have hd:=natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp hz) (C_ne_zero.mpr hn)
 rw [natDegree_C] at hd
 exact (not_le_of_gt A.positive) hd
def seedRingHom (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    w.value.valuationSubring →+* Chart A w r :=
  ((seed A).comp (algebraMap w.value.valuationSubring E)).codRestrict
    (Chart A w r).toSubring (fun a=>(aee A w r a).property)
def RH (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    (w.value.valuationSubring)[X] →+* Chart A w r :=
  eval₂RingHom (seedRingHom A w r) (xAt A w r)
private theorem chartPolynomial_comp (A:Equation E) (w:CurvePlace L E) (r :Bool) :
   (algebraMap (Chart A w r) (EC A)).comp (RH A w r) =
     ((a7W A).comp C).comp (mapRingHom (algebraMap w.value.valuationSubring E)) := by
 apply Polynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply,RH,coe_eval₂RingHom,eval₂_C,coe_mapRingHom,map_C]
   rfl
 · simp only [RingHom.comp_apply,RH,coe_eval₂RingHom,eval₂_X,coe_mapRingHom,map_X]
   rfl
theorem chartPolynomial_injective (A:Equation E) (w:CurvePlace L E) (r :Bool) :
  Function.Injective (RH A w r) := by
 apply Function.Injective.of_comp (f :=algebraMap (Chart A w r) (EC A))
 change Function.Injective ((algebraMap (Chart A w r) (EC A)).comp (RH A w r))
 rw [chartPolynomial_comp]
 exact (physical_injective A).comp (Polynomial.map_injective _ Subtype.val_injective)
private theorem poly_mem {R F:Type} [CommRing R] [Field F] (f :R[X] →+* F)
   (T:Subfield F) (hC : ∀ a,f (C a)∈T) (hX:f Polynomial.X∈T)
   (q:R[X]) :f q∈T:= by
 induction q using Polynomial.induction_on' with
 | add a b ha hb=>rw [map_add]; exact T.add_mem ha hb
 | monomial n a=>rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]; exact T.mul_mem (hC _) (T.pow_mem hX _)
theorem chartFraction (A:Equation E) (w:CurvePlace L E) (r :Bool) :
  IsFractionRing (Chart A w r) (EC A) := by
 let D:=Chart A w r
 let F:=EC A
 let g:FractionRing D →ₐ[D] F:=IsFractionRing.liftAlgHom (g:=Algebra.ofId D F) Subtype.val_injective
 let T:=g.toRingHom.fieldRange
 have hD (z :D) : (z :F)∈T:=⟨algebraMap D (FractionRing D) z,g.commutes z⟩
 have hseed (a :E) :seed A a∈T:= by
  obtain ⟨b,s,_,rfl⟩:=IsFractionRing.div_surjective w.value.valuationSubring a
  rw [map_div₀]
  exact T.div_mem (hD (aee A w r b)) (hD (aee A w r s))
 have hy :a7W A Polynomial.X∈T:= by
  have h:=hD ⟨jU A r,Algebra.subset_adjoin (Or.inr (by simp))⟩
  cases r
  · exact h
  · exact inv_mem_iff.mp h
 have hinner (p:E[X]) :a7W A (C p)∈T :=
  poly_mem ((a7W A).comp C) T hseed (hD (xAt A w r)) p
 have hroot (b:AdjoinRoot A.f) :algebraMap (AdjoinRoot A.f) F b∈T:= by
  obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective b
  exact poly_mem (a7W A) T hinner hy p
 refine IsFractionRing.of_algEquiv (AlgEquiv.ofBijective g ⟨g.injective,fun a => ?_⟩)
 apply (RingHom.mem_fieldRange (f :=g.toRingHom)).mp
 obtain ⟨b,s,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot A.f) a
 exact T.div_mem (hroot b) (hroot s)
theorem normalFraction (A:Equation E) (w:CurvePlace L E) (r :Bool) :
  IsFractionRing (Normal A w r) (EC A) := by
 let F:=EC A
 have :=chartFraction A w r
 exact integralClosure.isFractionRing_of_finite_extension F F
private theorem localValuation {N K:Type*} [CommRing N] [IsDomain N] [Field K] [Algebra N K]
    [IsFractionRing N K] [IsNoetherianRing N] [IsIntegrallyClosed N]
    (P:Ideal N) [P.IsPrime] (hp:P.height = 1) :
    ∃ v :Valuation K ℤᵐ⁰,Function.Surjective v ∧
      (∀ n:N,v (algebraMap N K n)<1↔n∈P) ∧
      (∀ n:N,v (algebraMap N K n)≤1) ∧
      (∀ u:K,v u≤1 ↔ ∃ a :N,a∉P ∧ ∃ b:N,
        algebraMap N K a*u=algebraMap N K b) := by
  let B:=Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  have :IsLocalRing B:=IsLocalization.AtPrime.isLocalRing B P
  have :IsNoetherianRing B:=IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have :IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hd:ringKrullDim B=1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P B,hp]
    rfl
  have :Ring.KrullDimLE 1 B:=Ring.krullDimLE_iff.mpr hd.le
  have :Ring.DimensionLEOne B:=⟨fun hn h=>h.isMaximal_of_ne_bot hn⟩
  have :IsDedekindDomain B:=(isDedekindDomain_iff B K).mpr
    ⟨inferInstance,inferInstance,inferInstance,fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩
  have hne :IsLocalRing.maximalIdeal B ≠ ⊥ := by
    intro h
    have hh:=IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R:=B)
    rw [h,hd,Ideal.height_bot] at hh
    exact zero_ne_one hh
  have :IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B (IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hne)).out 3 1).mp
      (show IsDedekindDomain B from inferInstance)
  let p:=IsDiscreteValuationRing.maximalIdeal B
  refine ⟨p.valuation K,p.valuation_surjective K,?_,?_,?_⟩
  · intro n
    change p.valuation K (algebraMap B K (algebraMap N B n))<1↔n∈P
    exact (p.valuation_lt_one_iff_mem _).trans (IsLocalization.AtPrime.to_map_mem_maximal_iff B P n)
  · intro n
    exact p.valuation_le_one (algebraMap N B n)
  · intro u
    have h:p.valuation K u≤1↔u∈B :=
      ⟨fun hu=> by
        obtain ⟨b,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one hu
        exact b.property,
        fun hu=>p.valuation_le_one ⟨u,hu⟩⟩
    have hn (a :N) (ha :a∉P) :algebraMap N K a≠0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors ha)
    rw [h]
    change (∃ (b a :N) (_:a∈P.primeCompl),u=algebraMap N K b*(algebraMap N K a)⁻¹)↔_
    constructor
    · rintro ⟨b,a,ha,e⟩
      exact ⟨a,ha,b,by rw [e,mul_comm (algebraMap N K a),mul_assoc,
        inv_mul_cancel₀ (hn a ha),mul_one]⟩
    · rintro ⟨a,ha,b,e⟩
      exact ⟨b,a,ha,by rw [← div_eq_mul_inv,eq_div_iff_mul_eq (hn a ha),mul_comm]; exact e⟩
theorem graphValuation (A:Equation E) (w:CurvePlace L E) (r :Bool)
    [IsNoetherianRing (Normal A w r)] (P:Ideal (Normal A w r)) [P.IsPrime] (hp:P.height = 1) :
    ∃ v :GraphVal A r,
      (∀ a :Chart A w r,v.val (a :EC A)≤1) ∧
      (∀ a :Chart A w r,
        v.val (a :EC A)<1↔algebraMap (Chart A w r) (Normal A w r) a∈P) ∧
      (∀ u:EC A,v.val u≤1↔NormalRegular (A:=A) (w:=w) (r :=r) P u) := by
  let R:=Chart A w r
  let N :=Normal A w r
  let K:=EC A
  have :IsFractionRing N K:=normalFraction A w r
  have :IsIntegrallyClosed N :=(isIntegrallyClosed_iff_isIntegrallyClosedIn (R:=N) K).mpr inferInstance
  obtain ⟨v,hv,hcenter,hreg,hu⟩:=localValuation (N :=N) (K:=K) P hp
  have hchart (a :R) :v (a :K)≤1 :=hreg (algebraMap R N a)
  have hc (a :L) (ha :a≠0) :v (constant A a)=1 := by
    let b:N :=algebraMap R N (algebraMap L R a)
    change v (b:K)=1
    exact le_antisymm (hreg b) (le_of_not_gt fun h =>
      ‹P.IsPrime›.ne_top (P.eq_top_of_isUnit_mem ((hcenter b).mp h)
        (((isUnit_iff_ne_zero.mpr ha).map (algebraMap L R)).map (algebraMap R N))))
  let y :R:=⟨jU A r,Algebra.subset_adjoin (Or.inr (by simp))⟩
  let j:R:=⟨jet A r,Algebra.subset_adjoin (Or.inr (by simp))⟩
  let V:GraphVal A r :=⟨v,hv,hc,hchart (xAt A w r),hchart y,hchart j⟩
  exact ⟨V,hchart,fun a=>hcenter (algebraMap R N a),hu⟩
end
end qIGP9Qa
