import ProximityPrize.SubmissionLower.R6960CollisionTameLocalizedDegree
import Mathlib.RingTheory.Localization.Algebra

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LaurentPolynomial LineEuler Module
open scoped Polynomial BigOperators

variable (k : Type) [Field k]

abbrev PlaneRing := k[X][X]
abbrev PlaneField := FractionRing (PlaneRing k)
abbrev GenericCoefficients := FractionRing k[X]
abbrev GenericLine := (GenericCoefficients k)[X]

private abbrev coeffDenominators : Submonoid (PlaneRing k) := (nonZeroDivisors k[X]).map Polynomial.C

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

private theorem coeffDenominators_regular : coeffDenominators k≤nonZeroDivisors (PlaneRing k) := by
  rintro _ ⟨a,ha,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (C_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp ha))

/-- The finite polynomial ring on the generic line maps into the original
plane fraction field by the actual coefficient localization. -/
def genericFinite : GenericLine k→+*PlaneField k :=
  IsLocalization.lift (M:=coeffDenominators k) (g:=algebraMap _ _) fun s=>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (PlaneRing k) _)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (coeffDenominators_regular k s.property)))

private theorem genericFinite_on_plane (a : PlaneRing k) :
    genericFinite k (algebraMap (PlaneRing k) (GenericLine k) a)=algebraMap (PlaneRing k) (PlaneField k) a :=
  IsLocalization.lift_eq _ _

private theorem genericFinite_fraction :
    let : Algebra (GenericLine k) (PlaneField k) := (genericFinite k).toAlgebra
    IsFractionRing (GenericLine k) (PlaneField k) := by
  let : Algebra (GenericLine k) (PlaneField k) := (genericFinite k).toAlgebra
  let : IsScalarTower (PlaneRing k) (GenericLine k) (PlaneField k) :=
    IsScalarTower.of_algebraMap_eq (fun p=>(genericFinite_on_plane k p).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (coeffDenominators k) _ _

private theorem genericFinite_injective : Function.Injective (genericFinite k) := by
  let : Algebra (GenericLine k) (PlaneField k) := (genericFinite k).toAlgebra
  let : IsFractionRing (GenericLine k) (PlaneField k) := genericFinite_fraction k
  exact IsFractionRing.injective _ _

private abbrev t : PlaneField k := genericFinite k (Polynomial.X (R:=GenericCoefficients k))

private theorem t_ne : t k≠0 := (map_ne_zero_iff _ (genericFinite_injective k)).mpr Polynomial.X_ne_zero

/-- The Laurent overlap of the generic line inside the original plane
function field. -/
def genericLaurent : Laurent (GenericCoefficients k)→+*PlaneField k :=
  LaurentPolynomial.eval₂ ((genericFinite k).comp Polynomial.C) (Units.mk0 (t k) (t_ne k))

private theorem genericLaurent_finite :
    (genericLaurent k).comp (chartEmbedding false).toRingHom=genericFinite k := by
  apply Polynomial.ringHom_ext
  · intro a
    change genericLaurent k (Polynomial.toLaurent (Polynomial.C a)) = _
    rw [genericLaurent,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_C]
    rfl
  · change genericLaurent k (Polynomial.toLaurent (Polynomial.X (R:=GenericCoefficients k))) = _
    rw [genericLaurent,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_X]
    rfl

private abbrev genericInverse : GenericLine k→+*PlaneField k :=
  Polynomial.eval₂RingHom ((genericFinite k).comp Polynomial.C) ((t k)⁻¹)

private theorem genericLaurent_inverse :
    (genericLaurent k).comp (chartEmbedding true).toRingHom=genericInverse k := by
  apply Polynomial.ringHom_ext
  · intro a
    change genericLaurent k (invert (Polynomial.toLaurent (Polynomial.C a))) = _
    rw [Polynomial.toLaurent_C,invert_C,genericLaurent,LaurentPolynomial.eval₂_C]
    exact (Polynomial.eval₂_C _ _).symm
  · change genericLaurent k (invert (Polynomial.toLaurent (Polynomial.X (R:=GenericCoefficients k)))) = _
    rw [Polynomial.toLaurent_X,invert_T]
    have val := LaurentPolynomial.eval₂_T_neg_n ((genericFinite k).comp Polynomial.C) (Units.mk0 (t k) (t_ne k)) 1
    simpa only [genericLaurent,genericInverse,Int.natCast_one,pow_one,Units.val_inv_eq_inv_val,
      Units.val_mk0,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using val

private theorem genericInverse_fractions :
    let : Algebra (GenericLine k) (PlaneField k) := (genericInverse k).toAlgebra
    IsFractionRing (GenericLine k) (PlaneField k) := by
  let J := (genericFinite k).comp Polynomial.C
  let : Algebra (GenericCoefficients k) (PlaneField k) := J.toAlgebra
  have finite_eval : Polynomial.eval₂RingHom J (t k)=genericFinite k :=
    Polynomial.ringHom_ext (fun _=>Polynomial.eval₂_C _ _) (Polynomial.eval₂_X _ _)
  have transcend : Transcendental (GenericCoefficients k) (t k) := by
    apply transcendental_iff_injective.mpr
    change Function.Injective (Polynomial.eval₂RingHom J (t k))
    rw [finite_eval]
    exact genericFinite_injective k
  have inv_transcend : Transcendental (GenericCoefficients k) ((t k)⁻¹) := by
    simpa only [Transcendental,IsAlgebraic.inv_iff] using transcend
  have inj : Function.Injective (genericInverse k) := transcendental_iff_injective.mp inv_transcend
  have repr (a : PlaneField k) : ∃ x y : GenericLine k,genericFinite k x/genericFinite k y=a := by
    let : Algebra (GenericLine k) (PlaneField k) := (genericFinite k).toAlgebra
    let : IsFractionRing (GenericLine k) (PlaneField k) := genericFinite_fraction k
    obtain ⟨x,y,_,eq⟩ := IsFractionRing.div_surjective (GenericLine k) a
    exact ⟨x,y,eq⟩
  let : Algebra (GenericLine k) (PlaneField k) := (genericInverse k).toAlgebra
  let : FaithfulSMul (GenericLine k) (PlaneField k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr inj
  apply IsFractionRing.of_field
  intro a
  obtain ⟨x,y,eq⟩ := repr a
  let N := max x.natDegree y.natDegree
  let : Invertible (t k) := invertibleOfNonzero (t_ne k)
  have reflect (p : GenericLine k) (hp : p.natDegree≤N) :
      genericInverse k (p.reflect N)=genericFinite k p*((t k)⁻¹)^N := by
    have h := Polynomial.eval₂_reflect_mul_pow J (t k) N p hp
    rw [invOf_eq_inv] at h
    change genericInverse k (p.reflect N)*(t k)^N=(Polynomial.eval₂RingHom J (t k)) p at h
    rw [finite_eval] at h
    apply mul_right_cancel₀ (pow_ne_zero N (t_ne k))
    rw [h,mul_assoc,←mul_pow,inv_mul_cancel₀ (t_ne k),one_pow,mul_one]
  refine ⟨x.reflect N,y.reflect N,?_⟩
  change a=genericInverse k (x.reflect N)/genericInverse k (y.reflect N)
  rw [reflect x (le_max_left _ _),reflect y (le_max_right _ _),
    mul_div_mul_right _ _ (pow_ne_zero _ (inv_ne_zero (t_ne k)))]
  exact eq.symm

variable {E : Type} [Field E] [Algebra (PlaneRing k) E] [Algebra (PlaneField k) E]
  [IsScalarTower (PlaneRing k) (PlaneField k) E]
  [FiniteDimensional (PlaneField k) E] [Algebra.IsSeparable (PlaneField k) E]

/-- The actual generic Laurent module comes from the original extension
of the original plane fraction field. -/
scoped instance genericLaurentAlgebra : Algebra (Laurent (GenericCoefficients k)) E :=
  ((algebraMap (PlaneField k) E).comp (genericLaurent k)).toAlgebra

omit [Algebra (PlaneRing k) E] [IsScalarTower (PlaneRing k) (PlaneField k) E] in
/-- Both affine pieces of the actual generic line have full-rank bases
of their normalizations. -/
theorem genericLine_basis (s : Bool) :
    Nonempty (Basis (Fin (finrank (PlaneField k) E)) (GenericLine k)
      (chartOrder (k:=GenericCoefficients k) (E:=E) s)) := by
  let A := GenericLine k
  let F := PlaneField k
  let j := (genericLaurent k).comp (chartEmbedding s).toRingHom
  let : Algebra A F := j.toAlgebra
  let : IsFractionRing A F := by
    cases s with
    | false =>
      exact ((congrArg (fun f : A→+*F=>@IsFractionRing A _ F _ f.toAlgebra) (genericLaurent_finite k)).symm ▸
        genericFinite_fraction k)
    | true => exact ((congrArg (fun f : A→+*F=>@IsFractionRing A _ F _ f.toAlgebra) (genericLaurent_inverse k)).symm ▸
        genericInverse_fractions k)
  let : Algebra A E := ((algebraMap F E).comp j).toAlgebra
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=F) (A:=E) fun _=>rfl
  let C := integralClosure A E
  have inj : Function.Injective (algebraMap A E) := (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  let : Module.IsTorsionFree A E := Module.IsTorsionFree.of_smul_eq_zero fun a x eq=>by
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun h=>inj (h.trans (map_zero _).symm)) id
  let : Module.Finite A C := IsIntegralClosure.finite A F E C
  let : Module.Free A C := IsIntegralClosure.module_free A F E C
  have rank : finrank A C=finrank F E := IsIntegralClosure.rank A F E C
  exact ⟨Module.finBasisOfFinrankEq A C rank⟩

/-- The ordinary outer-variable degree of the actual plane discriminant
is bounded by twice the actual determinant deficit on the generic line. -/
theorem plane_generic_outer_degree (δ : PlaneRing k) (nz : δ≠0)
    (generator : normalizationDiscriminant (A:=PlaneRing k) (E:=E) (PlaneField k)=Ideal.span {δ}) :
    ∃ (bf : Basis (Fin (finrank (PlaneField k) E)) (GenericLine k)
        (chartOrder (k:=GenericCoefficients k) (E:=E) false))
      (bi : Basis (Fin (finrank (PlaneField k) E)) (GenericLine k)
        (chartOrder (k:=GenericCoefficients k) (E:=E) true)) (d : ℤ),
      (normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧ (δ.natDegree:ℤ)≤-2*d := by
  let A := PlaneRing k
  let R := GenericLine k
  let F := PlaneField k
  let j := (genericLaurent k).comp (chartEmbedding false).toRingHom
  let : Algebra R F := j.toAlgebra
  let : IsFractionRing R F := by
    exact ((congrArg (fun f : R→+*F=>@IsFractionRing R _ F _ f.toAlgebra) (genericLaurent_finite k)).symm ▸
      genericFinite_fraction k)
  let : IsScalarTower A R F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=F) fun r=>by
    change algebraMap A F r=j (algebraMap A R r)
    rw [show j=genericFinite k from genericLaurent_finite k,genericFinite_on_plane]
  let : Algebra R E := ((algebraMap F E).comp j).toAlgebra
  let : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq (R:=R) (S:=F) (A:=E) fun _=>rfl
  let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=E) fun r=>by
    rw [IsScalarTower.algebraMap_apply A F E,IsScalarTower.algebraMap_apply A R F,
      ←IsScalarTower.algebraMap_apply R F E]
  obtain ⟨bf⟩ := genericLine_basis (E:=E) k false
  obtain ⟨bi⟩ := genericLine_basis (E:=E) k true
  obtain ⟨d,dd,cap⟩ := localized_line_discriminant_degree (F:=F) (E:=E) (coeffDenominators k) δ nz generator bf bi
  change ((δ.map (algebraMap k[X] (GenericCoefficients k))).natDegree:ℤ)≤-2*d at cap
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _)] at cap
  exact ⟨bf,bi,d,dd,cap⟩

#print axioms genericLine_basis
#print axioms plane_generic_outer_degree
end
end Lower6960.CollisionTame
