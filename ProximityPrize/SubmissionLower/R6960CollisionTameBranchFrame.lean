import ProximityPrize.SubmissionLower.R6960CollisionTamePlaneDiscriminant
import Mathlib.RingTheory.Localization.Integral
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch

-- merged module R6960CollisionTameDiscriminantLocalization
section Merged_R6960CollisionTameDiscriminantLocalization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Module Matrix
open scoped Matrix BigOperators

variable {A R F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field F] [Field E] [Algebra A R] [Algebra A F] [Algebra A E] [Algebra R F] [Algebra R E] [Algebra F E]
  [IsScalarTower A R F] [IsScalarTower A R E] [IsScalarTower A F E] [IsScalarTower R F E]
  [IsFractionRing A F] [IsFractionRing R F] [FiniteDimensional F E] [Algebra.IsSeparable F E]

def integralsIncl : integralClosure A E→+*integralClosure R E :=
  Subring.inclusion (show (integralClosure A E).toSubring≤(integralClosure R E).toSubring
    from fun _ h=>(show IsIntegral A _ from h).tower_top)

theorem gram_map {ι : Type*} (u : ι→integralClosure A E) :
    (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A R) =
      tupleGram (integralTraceForm (A:=R) (E:=E) F) (fun i=>integralsIncl (R:=R) (u i)) := by
  apply Matrix.ext
  intro i j
  apply IsFractionRing.injective R F
  change algebraMap R F (algebraMap A R (integralTraceForm (A:=A) (E:=E) F (u i) (u j)))=
    algebraMap R F (integralTraceForm (A:=R) (E:=E) F (integralsIncl (u i)) (integralsIncl (u j)))
  rw [←IsScalarTower.algebraMap_apply,integralTraceForm_map,integralTraceForm_map]
  rfl

/-- The normalized discriminant ideal commutes with localization of the
base chart. Every full-size local tuple has one common denominator. -/
theorem normalizationDiscriminant_map (S : Submonoid A) [IsLocalization S R] :
    (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)=
      normalizationDiscriminant (A:=R) (E:=E) F := by
  let e := finrank F E
  let trA := integralTraceForm (A:=A) (E:=E) F
  let trR := integralTraceForm (A:=R) (E:=E) F
  let iR := (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)
  let j := algebraMap A R
  apply le_antisymm
  · apply (Ideal.map_le_iff_le_comap).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨u,rfl⟩
    change j (tupleGram trA u).det∈gramIdeal (ι:=Fin e) trR
    have det : j (tupleGram trA u).det=(tupleGram trR (fun i=>integralsIncl (u i))).det :=
      (RingHom.map_det j _).trans (congrArg Matrix.det (gram_map u))
    rw [det]
    exact gramIdeal_mem trR _
  · change gramIdeal (ι:=Fin e) trR ≤ iR
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    classical
    choose a ha using fun i : Fin e=>IsIntegral.exists_multiple_integral_of_isLocalization S (v i:E) (v i).property
    let s : S := ∏ i,a i
    have clear (i : Fin e) : IsIntegral A ((s:A) • (v i:E)) := by
      obtain ⟨t,ht⟩ : a i∣s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have es : (s:A)=(t:A)*(a i:A) := by rw [ht]; exact mul_comm _ _
      rw [es,mul_smul]
      exact (ha i).smul (t:A)
    let u (i : Fin e) : integralClosure A E := ⟨_,clear i⟩
    have scale (i : Fin e) : integralsIncl (u i)=j (s:A) • v i := by
      apply Subtype.ext
      change (s:A) • (v i:E)=_
      rw [Subalgebra.coe_smul,←IsScalarTower.algebraMap_smul R]
    have mapped : (tupleGram trA u).map j=(j (s:A))^2 • tupleGram trR v := by
      rw [gram_map,show (fun i=>integralsIncl (u i))=(fun i=>j (s:A) • v i) from funext scale,
        tupleGram_smul]
    have det : j (tupleGram trA u).det=(j (s:A))^(2*e)*(tupleGram trR v).det := by
      rw [show j (tupleGram trA u).det=((tupleGram trA u).map j).det from RingHom.map_det j _,
        mapped,det_smul,←pow_mul,Fintype.card_fin]
    have mem : j (tupleGram trA u).det∈iR := Ideal.mem_map_of_mem j (gramIdeal_mem trA u)
    rw [det] at mem
    exact (Ideal.unit_mul_mem_iff_mem iR ((IsLocalization.map_units R s).pow (2*e))).mp mem

#print axioms normalizationDiscriminant_map
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameDiscriminantLocalization

-- merged module R6960CollisionTameBranchFrame
section Merged_R6960CollisionTameBranchFrame
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Ideal IsLocalRing Module Polynomial Matrix NormalizedFiber
open scoped Polynomial Matrix BigOperators
open Lower6960.CollisionTame (gram_map integralsIncl)
open Lower6960.CollisionTame (integralClosure_torsionFree)
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
theorem branch_frame_trace_order {n : ℕ}
    (P : Ideal (Plane k)) [P.IsPrime] (q : Plane k) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin n→Order k E) (f : (Fin n→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (outside : g∉P) (clear : ∀ x : Order k E,∃ t,f t=g • x) :
    let T := tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u
    emultiplicity q T.det=((n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) := by
  classical
  let A := Plane k
  let F := FractionRing A
  let D := Localization.AtPrime P
  let : IsDiscreteValuationRing D := principal_prime_dvr P q pir.ne_zero span
  let : Algebra D F := (branchFractionHom (F:=F) P).toAlgebra
  let : IsFractionRing D F := branchFraction_isFractionRing (F:=F) P
  let : IsScalarTower A D F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=F) fun r=>
    (branchFractionHom_apply (F:=F) P r).symm
  let : Algebra D E := ((algebraMap F E).comp (branchFractionHom (F:=F) P)).toAlgebra
  let : IsScalarTower D F E := IsScalarTower.of_algebraMap_eq (R:=D) (S:=F) (A:=E) fun _=>rfl
  let : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=E) fun r=>by
    change algebraMap A E r=algebraMap F E (branchFractionHom P (algebraMap A D r))
    rw [branchFractionHom_apply,IsScalarTower.algebraMap_apply A F E]
  let C := integralClosure D E
  let : CommRing C := @Subalgebra.toCommRing D E _ _ (inferInstance : Algebra D E) C
  let B := Order k E
  let incl : B→+*C := Lower6960.CollisionTame.integralsIncl
  let : Algebra B C := incl.toAlgebra
  let : Algebra A C := C.algebra'
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=C) fun r=>by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply A D E r
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=B) (A:=C) fun a=>by
    apply Subtype.ext
    change algebraMap A E a=(incl (algebraMap A B a):E)
    rfl
  let : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq (R:=B) (S:=C) (A:=E) fun _=>rfl
  let M := P.primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid E M) E := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨a,ha,rfl⟩
    have nz : a≠0 := fun eq=>(Ideal.mem_primeCompl_iff.mp ha) (eq.symm ▸ P.zero_mem)
    have ainj : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ ainj).mpr nz)
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) C :=
    IsLocalization.integralClosure (S:=E) (Rf:=D) (Sf:=E) M
  let j := (IsScalarTower.toAlgHom A B C).toLinearMap
  let : IsLocalizedModule M j := inferInstanceAs (IsLocalizedModule M (IsScalarTower.toAlgHom A B C).toLinearMap)
  have jinj : Function.Injective j := fun x y eq=>Subtype.ext (congrArg (fun t : C=>(t:E)) eq)
  obtain ⟨b,basis⟩ := localized_fibre_frame (A:=A) (R:=D) (M:=B) (P:=C) M j jinj f inj
    ⟨g,Ideal.mem_primeCompl_iff.mpr outside⟩ clear
  have repr (i : Fin n) : b i=incl (u i) := by
    rw [basis]
    have l : f (Pi.single i 1)=u i := by
      rw [sum,Finset.sum_eq_single i]
      · simp
      · intro j _ ji
        simp [Ne.symm ji]
        exact zero_smul A (u j)
      · simp
    rw [l]
    rfl
  let : Module.Free D C := Module.Free.of_basis b
  let : Module.Finite D C := Module.Finite.of_basis b
  let : Module.IsTorsionFree D C := Lower6960.CollisionTame.integralClosure_torsionFree (A:=D) (E:=E) F
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  have localMatrix : T.map (algebraMap A D)=Algebra.traceMatrix D b := by
    calc
      _ = tupleGram (integralTraceForm (A:=D) (E:=E) F) (fun i=>incl (u i)) :=
        Lower6960.CollisionTame.gram_map (A:=A) (R:=D) (F:=F) (E:=E) u
      _ = _ := by
        rw [show (fun i=>incl (u i))=(b:Fin n→C) from funext fun i=>(repr i).symm]
        apply Matrix.ext
        intro i j
        change Algebra.intTrace D C (b i*b j)=Algebra.trace D C (b i*b j)
        rw [Algebra.intTrace_eq_trace]
  let charMap : k→+*ResidueField D := (residue D).comp ((algebraMap A D).comp (Polynomial.C.comp Polynomial.C))
  let : CharP (ResidueField D) p := charP_of_injective_ringHom charMap.injective p
  have h := trace_order_from_local_matrix P q pir span p small b T localMatrix
  simpa only [Fintype.card_fin] using h
#print axioms branch_frame_trace_order
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameBranchFrame
