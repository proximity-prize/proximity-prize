import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import Mathlib.RingTheory.Localization.Algebra
import ProximityPrize.SubmissionLower.R6960CollisionMarkedPlaneOverlap

set_option Elab.async false

-- merged module R6960CollisionTameLocalizedDegree
section Merged_R6960CollisionTameLocalizedDegree
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LineEuler Module Matrix
open scoped Polynomial Matrix
variable {k A F E : Type*} [Field k] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [IsNoetherianRing A] [Field F] [Field E] [Algebra (Laurent k) E]
local instance finiteLineAlgebra : Algebra (Polynomial k) E :=
  ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra
variable [Algebra A (Polynomial k)] [Algebra A F] [Algebra A E] [Algebra (Polynomial k) F] [Algebra F E]
  [IsScalarTower A (Polynomial k) F] [IsScalarTower A (Polynomial k) E] [IsScalarTower A F E] [IsScalarTower (Polynomial k) F E]
  [IsFractionRing A F] [IsFractionRing (Polynomial k) F] [FiniteDimensional F E] [Algebra.IsSeparable F E]
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameLocalizedDegree

-- merged module R6960CollisionTameCoefficientLine
section Merged_R6960CollisionTameCoefficientLine
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LaurentPolynomial LineEuler Module
open scoped Polynomial BigOperators
variable (k : Type) [Field k]
abbrev PlaneRing := (Polynomial (Polynomial k))
abbrev PlaneField := FractionRing (PlaneRing k)
abbrev GenericCoefficients := FractionRing (Polynomial k)
abbrev GenericLine := (Polynomial (GenericCoefficients k))
abbrev coeffDenominators : Submonoid (PlaneRing k) := (nonZeroDivisors (Polynomial k)).map Polynomial.C
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
private theorem coeffDenominators_regular : coeffDenominators k≤nonZeroDivisors (PlaneRing k) := by
  rintro _ ⟨a,ha,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (C_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp ha))
def genericFinite : GenericLine k→+*PlaneField k :=
  IsLocalization.lift (M:=coeffDenominators k) (g:=algebraMap _ _) fun s=>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (PlaneRing k) _)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (coeffDenominators_regular k s.property)))
theorem genericFinite_on_plane (a : PlaneRing k) :
    genericFinite k (algebraMap (PlaneRing k) (GenericLine k) a)=algebraMap (PlaneRing k) (PlaneField k) a :=
  IsLocalization.lift_eq _ _
theorem genericFinite_fraction :
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
def genericLaurent : Laurent (GenericCoefficients k)→+*PlaneField k :=
  LaurentPolynomial.eval₂ ((genericFinite k).comp Polynomial.C) (Units.mk0 (t k) (t_ne k))
theorem genericLaurent_finite :
    (genericLaurent k).comp (chartEmbedding false).toRingHom=genericFinite k := by
  apply Polynomial.ringHom_ext
  · intro a
    change genericLaurent k (Polynomial.toLaurent (Polynomial.C a)) = _
    rw [genericLaurent,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_C]
    rfl
  · change genericLaurent k (Polynomial.toLaurent (Polynomial.X (R:=GenericCoefficients k))) = _
    rw [genericLaurent,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_X]
    rfl
abbrev genericInverse : GenericLine k→+*PlaneField k :=
  Polynomial.eval₂RingHom ((genericFinite k).comp Polynomial.C) ((t k)⁻¹)
theorem genericLaurent_inverse :
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
theorem genericInverse_fractions :
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
scoped instance genericLaurentAlgebra : Algebra (Laurent (GenericCoefficients k)) E :=
  ((algebraMap (PlaneField k) E).comp (genericLaurent k)).toAlgebra
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameCoefficientLine

-- merged module R6960CollisionMarkedGenericFrames
section Merged_R6960CollisionMarkedGenericFrames
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass MonicFourChartDescent
open Polynomial Module CollisionTame LineEuler
open scoped Polynomial Lower6960.MonicChartProbes
open Lower6960.CollisionMarked (outerPlane outerField outer_X outer_CC outer_CX outerField_fraction)
open Lower6960.CollisionTame (genericFinite_on_plane genericFinite_fraction genericLaurent_finite genericLaurent_inverse genericInverse_fractions genericInverse coeffDenominators)
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
def genericPlaneField (j:Bool) : FractionRing (Plane L)≃+*ChartField :=
  IsFractionRing.ringEquivOfRingEquiv (K:=FractionRing (Plane L)) (L:=ChartField)
    (Lower6960.CollisionMarked.outerPlane j false)
private theorem genericPlaneField_apply (j:Bool) (p:Plane L) :
    genericPlaneField j (algebraMap (Plane L) (FractionRing (Plane L)) p)=
      Lower6960.CollisionMarked.outerField j false p :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
def lineEmbedding (j b:Bool) : GenericLine L→+*ChartField :=
  (genericPlaneField j).toRingHom.comp ((genericLaurent L).comp (chartEmbedding b).toRingHom)
private theorem lineEmbedding_fraction (j b:Bool) :
    let : Algebra (GenericLine L) ChartField := (lineEmbedding j b).toAlgebra
    IsFractionRing (GenericLine L) ChartField := by
  let R := GenericLine L
  let F := FractionRing (Plane L)
  let g := (genericLaurent L).comp (chartEmbedding b).toRingHom
  let : Algebra R F := g.toAlgebra
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : IsFractionRing R F := by
    cases b
    · exact ((congrArg (fun h:R→+*F=>@IsFractionRing R _ F _ h.toAlgebra)
        (Lower6960.CollisionTame.genericLaurent_finite L)).symm ▸
          Lower6960.CollisionTame.genericFinite_fraction L)
    · exact ((congrArg (fun h:R→+*F=>@IsFractionRing R _ F _ h.toAlgebra)
        (Lower6960.CollisionTame.genericLaurent_inverse L)).symm ▸
          Lower6960.CollisionTame.genericInverse_fractions L)
  let e : F≃ₐ[R]ChartField := { genericPlaneField j with commutes' := fun _=>rfl }
  exact IsFractionRing.of_algEquiv e
theorem lineEmbedding_on_plane (j b:Bool) (p:Plane L) :
    lineEmbedding j b (algebraMap (Plane L) (GenericLine L) p)=
      Lower6960.CollisionMarked.outerField j b p := by
  let A := Plane L
  let R := GenericLine L
  let F := FractionRing A
  change ((genericPlaneField j).toRingHom.comp
    ((genericLaurent L).comp (chartEmbedding b).toRingHom)) (algebraMap A R p)=_
  cases b with
  | false =>
    rw [Lower6960.CollisionTame.genericLaurent_finite]
    change genericPlaneField j (genericFinite L (algebraMap A R p))=_
    rw [Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply]
  | true =>
    have map_eq :
        ((genericPlaneField j).toRingHom.comp (Lower6960.CollisionTame.genericInverse L)).comp (algebraMap A R)=
          Lower6960.CollisionMarked.outerField j true := by
      apply Polynomial.ringHom_ext
      · intro a
        have scalar : Lower6960.CollisionMarked.outerField j false (C a)=
            Lower6960.CollisionMarked.outerField j true (C a) := by
          apply DFunLike.congr_fun
            (f:=(Lower6960.CollisionMarked.outerField j false).comp C)
            (g:=(Lower6960.CollisionMarked.outerField j true).comp C)
          apply Polynomial.ringHom_ext
          · exact fun c=>(Lower6960.CollisionMarked.outer_CC j false c).trans
              (Lower6960.CollisionMarked.outer_CC j true c).symm
          · exact (Lower6960.CollisionMarked.outer_CX j false).trans
              (Lower6960.CollisionMarked.outer_CX j true).symm
        change genericPlaneField j (Lower6960.CollisionTame.genericInverse L
          ((C a : A).map (algebraMap (Polynomial L) (GenericCoefficients L))))=_
        rw [map_C]
        change genericPlaneField j ((C (algebraMap (Polynomial L) (GenericCoefficients L) a)).eval₂
          ((genericFinite L).comp C) ((genericFinite L Polynomial.X)⁻¹))=_
        rw [eval₂_C]
        change genericPlaneField j (genericFinite L (C (algebraMap (Polynomial L) (GenericCoefficients L) a)))=_
        rw [show C (algebraMap (Polynomial L) (GenericCoefficients L) a)=algebraMap A R (C a) from
          (map_C (algebraMap (Polynomial L) (GenericCoefficients L))).symm]
        rw [Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply,scalar]
      · change genericPlaneField j (Lower6960.CollisionTame.genericInverse L
          ((Polynomial.X:A).map (algebraMap (Polynomial L) (GenericCoefficients L))))=_
        rw [map_X]
        change genericPlaneField j (Polynomial.X.eval₂ ((genericFinite L).comp C)
          ((genericFinite L Polynomial.X)⁻¹))=_
        rw [eval₂_X,map_inv₀]
        have rel : genericPlaneField j (genericFinite L Polynomial.X)=coordinate (!j) := by
          have idX : (Polynomial.X:R)=algebraMap A R (Polynomial.X:A) := (map_X _).symm
          rw [idX,Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply,
            Lower6960.CollisionMarked.outer_X]
          rfl
        rw [rel,Lower6960.CollisionMarked.outer_X]
        rfl
    rw [Lower6960.CollisionTame.genericLaurent_inverse]
    exact DFunLike.congr_fun map_eq p
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]
@[instance_reducible] def genericLineAlgebra (j:Bool) : Algebra (Laurent (GenericCoefficients L)) E :=
  (((algebraMap ChartField E).comp (genericPlaneField j).toRingHom).comp (genericLaurent L)).toAlgebra
theorem generic_line_basis (j b:Bool) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    Nonempty (Basis (Fin (finrank ChartField E)) (GenericLine L)
      (chartOrder (k:=GenericCoefficients L) (E:=E) b)) := by
  let R := GenericLine L
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : SMul R ChartField := (inferInstance : Algebra R ChartField).toSMul
  let : IsFractionRing R ChartField := lineEmbedding_fraction j b
  let : Algebra R E := ((algebraMap ChartField E).comp (lineEmbedding j b)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let C := integralClosure R E
  have inj : Function.Injective (algebraMap R E) := (algebraMap ChartField E).injective.comp
    (IsFractionRing.injective R ChartField)
  let : Module.IsTorsionFree R E := Module.IsTorsionFree.of_smul_eq_zero fun a x eq=>by
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun h=>inj (h.trans (map_zero _).symm)) id
  let : Module.Finite R C := IsIntegralClosure.finite R ChartField E C
  let : Module.Free R C := IsIntegralClosure.module_free R ChartField E C
  have rank : finrank R C=finrank ChartField E := IsIntegralClosure.rank R ChartField E C
  exact ⟨Module.finBasisOfFinrankEq R C rank⟩
theorem generic_line_trace_associated (j b:Bool) (δ:Plane L)
    (principal:lineDiscriminant (E:=E) j b=Ideal.span {δ}) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    ∀ a : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) b),
      Associated (Algebra.traceMatrix (GenericLine L) a).det
        ((Bivariate.swap δ).map (algebraMap (Polynomial L) (GenericCoefficients L))) := by
  let A := Plane L
  let B := A
  let F := FractionRing A
  let R := GenericLine L
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  let aA : Algebra A E := linePlaneAlgebra j b
  let : Algebra A E := aA
  let : Algebra F E := lineFractionAlgebra j b
  let : SMul A F := (inferInstance : Algebra A F).toSMul
  let tA : IsScalarTower A F E := linePlaneTower j b
  let : FiniteDimensional F E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable F E := lineFraction_separable j b
  let : Algebra B ChartField := (Lower6960.CollisionMarked.outerField j b).toAlgebra
  let : SMul B ChartField := (inferInstance : Algebra B ChartField).toSMul
  let : IsFractionRing B ChartField := Lower6960.CollisionMarked.outerField_fraction j b
  let aB : Algebra B E := ((algebraMap ChartField E).comp (Lower6960.CollisionMarked.outerField j b)).toAlgebra
  let : Algebra B E := aB
  let tB : IsScalarTower B ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower B ChartField E := tB
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : SMul R ChartField := (inferInstance : Algebra R ChartField).toSMul
  let : IsFractionRing R ChartField := lineEmbedding_fraction j b
  let : Algebra R E := ((algebraMap ChartField E).comp (lineEmbedding j b)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower B R ChartField := IsScalarTower.of_algebraMap_eq
    (R:=B) (S:=R) (A:=ChartField) fun p=>(lineEmbedding_on_plane j b p).symm
  let : IsScalarTower B R E := IsScalarTower.of_algebraMap_eq (R:=B) (S:=R) (A:=E) fun p=>by
    change algebraMap ChartField E (Lower6960.CollisionMarked.outerField j b p)=
      algebraMap ChartField E (lineEmbedding j b (algebraMap B R p))
    rw [lineEmbedding_on_plane]
  let e := Bivariate.swap.toRingEquiv (R:=L)
  have coord (p:A) : algebraMap B ChartField (e p)=linePlaneFractionEquiv j b (algebraMap A F p) := by
    rw [linePlaneFractionEquiv_apply]
    change (oriented j b (Bivariate.swap (Bivariate.swap p)):ChartField)=_
    rw [Bivariate.swap_swap_apply]
  have transport :=
    @discriminant_transport A B F ChartField E
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      aA aB inferInstance inferInstance tA tB
      inferInstance inferInstance inferInstance inferInstance
      e (linePlaneFractionEquiv j b) coord (fun _=>rfl)
  change (lineDiscriminant (E:=E) j b).map e.toRingHom=
    normalizationDiscriminant (A:=B) (E:=E) ChartField at transport
  rw [principal,Ideal.map_span,Set.image_singleton] at transport
  have loc := normalizationDiscriminant_map (A:=B) (R:=R) (F:=ChartField) (E:=E)
    (Lower6960.CollisionTame.coeffDenominators L)
  rw [←transport,Ideal.map_span,Set.image_singleton] at loc
  dsimp only
  intro a
  let aa : Basis (Fin (finrank ChartField E)) R (integralClosure R E) := a
  have basisDisc : normalizationDiscriminant (A:=R) (E:=E) ChartField=
      Ideal.span {(Algebra.traceMatrix R aa).det} :=
    normalizationDiscriminant_basis (A:=R) (E:=E) ChartField aa
  rw [basisDisc] at loc
  exact Ideal.span_singleton_eq_span_singleton.mp loc.symm
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedGenericFrames
