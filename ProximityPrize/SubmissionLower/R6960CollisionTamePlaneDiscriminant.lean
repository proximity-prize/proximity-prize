import ProximityPrize.SubmissionLower.R6960CollisionTameFrames
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminant
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Polynomial.Bivariate

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix
open scoped Polynomial Matrix BigOperators

section FieldTrace
variable {A E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [Field E] [Algebra A E]
variable (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]

omit [IsIntegrallyClosed A] [IsNoetherianRing A] in
theorem integralClosure_torsionFree (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] : Module.IsTorsionFree A (integralClosure A E) := by
  have inj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  let : Module.IsTorsionFree A E := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x eq
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun h=>inj (h.trans (map_zero _).symm)) id
  infer_instance

/-- The field trace restricted to the actual integral closure. Neither
this form nor the discriminant ideal needs the entire order to be free. -/
def integralTraceForm (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] : LinearMap.BilinForm A (integralClosure A E) := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  exact LinearMap.compr₂ (Algebra.lmul A B).toLinearMap (Algebra.intTrace A B)

theorem integralTraceForm_map (x y : integralClosure A E) :
    algebraMap A F (integralTraceForm (A:=A) (E:=E) F x y)=Algebra.trace F E ((x:E)*(y:E)) := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  change algebraMap A F (Algebra.intTrace A B (x*y))=Algebra.trace F E ((x:E)*(y:E))
  exact Algebra.algebraMap_intTrace (K:=F) (L:=E) (x*y)

/-- The discriminant of the actual normalized order is an ideal generated
by full-size trace determinants, using the generic field degree. -/
def normalizationDiscriminant (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] : Ideal A :=
  gramIdeal (ι:=Fin (finrank F E)) (integralTraceForm (A:=A) (E:=E) F)

/-- For an actual free chart the globally defined ideal agrees with the
ordinary trace determinant of any basis of the correct rank. -/
theorem normalizationDiscriminant_basis
    (b : Basis (Fin (finrank F E)) A (integralClosure A E)) :
    normalizationDiscriminant (A:=A) (E:=E) F=Ideal.span {(Algebra.traceMatrix A b).det} := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  let : Module.Free A B := Module.Free.of_basis b
  have matrix : tupleGram (integralTraceForm (A:=A) (E:=E) F) b=Algebra.traceMatrix A b := by
    apply Matrix.ext
    intro i j
    change Algebra.intTrace A B (b i*b j)=Algebra.trace A B (b i*b j)
    rw [Algebra.intTrace_eq_trace]
  change gramIdeal (ι:=Fin (finrank F E)) (integralTraceForm (A:=A) (E:=E) F)=_
  rw [gramIdeal_basis _ b,matrix]

theorem normalizationDiscriminant_ne_bot : normalizationDiscriminant (A:=A) (E:=E) F≠⊥ := by
  classical
  obtain ⟨I,b,h⟩ := FiniteDimensional.exists_is_basis_integral A F E
  let e : I ≃ Fin (finrank F E) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let be := b.reindex e
  let u (i : Fin (finrank F E)): integralClosure A E := ⟨be i,by
    change IsIntegral A (be i)
    simpa only [be,Basis.reindex_apply] using h (e.symm i)⟩
  have map_eq : (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A F)=
      (Algebra.traceForm F E).toMatrix be := by
    apply Matrix.ext
    intro i j
    change algebraMap A F (integralTraceForm (A:=A) (E:=E) F (u i) (u j))=(Algebra.traceForm F E).toMatrix be i j
    rw [integralTraceForm_map,LinearMap.BilinForm.toMatrix_apply,Algebra.traceForm_apply]
  have right : ((Algebra.traceForm F E).toMatrix be).det≠0 :=
    det_traceForm_ne_zero be
  intro bot
  have mem := gramIdeal_mem (integralTraceForm (A:=A) (E:=E) F) u
  change (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).det∈normalizationDiscriminant (A:=A) (E:=E) F at mem
  rw [bot,Ideal.mem_bot] at mem
  apply right
  have dm : ((tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A F)).det =
      algebraMap A F (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).det :=
    ((algebraMap A F).map_det (tupleGram (integralTraceForm (A:=A) (E:=E) F) u)).symm
  rw [←map_eq,dm,mem,map_zero]
end FieldTrace

section Plane
open NormalizedFiber
variable {k E : Type} [Field k] [IsAlgClosed k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

/-- Every maximal ideal of the affine plane meets an actual scalar fibre. -/
theorem maximal_contains_scalar (P : Ideal (Plane k)) (hp : P.IsMaximal) :
    ∃ z : k, (Polynomial.X-C (C z) : Plane k)∈P := by
  let e := Bivariate.equivMvPolynomial k
  let Q := P.map e.toRingHom
  have hQ : Q.IsMaximal := hp.map_bijective _ e.bijective
  obtain ⟨x,hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hQ
  refine ⟨x 1,?_⟩
  have inside : e (Polynomial.X-C (C (x 1)))∈Q := by
    rw [hx,MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp [e,Bivariate.equivMvPolynomial_X,Bivariate.equivMvPolynomial_C_C]
  change (Polynomial.X-C (C (x 1)) : Plane k)∈Q.comap e.toRingHom at inside
  rwa [show Q.comap e.toRingHom=P from Ideal.comap_map_of_bijective _ e.bijective] at inside

private theorem plane_form_principal (tr : LinearMap.BilinForm (Plane k) (Order k E)) :
    (gramIdeal (A:=Plane k) (M:=Order k E) (ι:=Fin (finrank (FractionRing (Plane k)) E)) tr).IsPrincipal := by
  let A := Plane k
  let n := finrank (FractionRing A) E
  refine principal_of_clears (gramIdeal (ι:=Fin n) tr) fun P hp=>?_
  obtain ⟨z,cut⟩ := maximal_contains_scalar P hp
  obtain ⟨u,g,one,clears⟩ := scalar_fibre_ranked_lifts (E:=E) z
  have gn : g∉P := by
    intro inside
    have dvd : (Polynomial.X-C (C z))∣g-1 := dvd_iff_isRoot.mpr (by
      rw [IsRoot,eval_sub,one,eval_one,sub_self])
    obtain ⟨r,hr⟩ := dvd
    have diff : g-1∈P := hr.symm ▸ P.mul_mem_right r cut
    have uno : (1:A)∈P := by simpa only [sub_sub_cancel] using P.sub_mem inside diff
    apply hp.ne_top
    rw [Ideal.eq_top_iff_one]
    exact uno
  have patch : ∀ a∈gramIdeal (ι:=Fin n) tr, (tupleGram tr u).det∣g^(2*Fintype.card (Fin n))*a :=
    gramIdeal_clear tr u g clears
  exact ⟨g,(tupleGram tr u).det,2*Fintype.card (Fin n),gn,gramIdeal_mem tr u,patch⟩

/-- The actual normalized discriminant on the factorial affine plane is
principal. Its local generators come from the lifts of the actual free
scalar fibres. -/
theorem plane_discriminant_principal :
    (normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))).IsPrincipal :=
  plane_form_principal (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)))

end Plane

#print axioms normalizationDiscriminant_ne_bot
#print axioms plane_discriminant_principal
end
end Lower6960.CollisionTame
