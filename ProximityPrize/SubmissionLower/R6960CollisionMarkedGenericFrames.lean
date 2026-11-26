import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisFamily
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRow

section Merged6967_R6960CollisionMarkedGenericFrames
set_option Elab.async false





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
theorem localized_line_discriminant_degree (S : Submonoid A) [IsLocalization S (Polynomial k)]
    (δ : A) (nz : δ≠0) (principal : normalizationDiscriminant (A:=A) (E:=E) F=Ideal.span {δ})
    (bf : Basis (Fin (finrank F E)) (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis (Fin (finrank F E)) (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      ((algebraMap A (Polynomial k) δ).natDegree:ℤ)≤-2*d := by
  let j := algebraMap A (Polynomial k)
  let b : Basis (Fin (finrank F E)) (Polynomial k) (integralClosure (Polynomial k) E) := bf
  let G := (Algebra.traceMatrix (Polynomial k) bf).det
  have h : (Ideal.span {j δ} : Ideal (Polynomial k))=Ideal.span {G} := by
    have localEq := normalizationDiscriminant_map (R:=(Polynomial k)) (A:=A) (F:=F) (E:=E) S
    rw [principal,Ideal.map_span,Set.image_singleton,normalizationDiscriminant_basis F b] at localEq
    exact localEq
  have associated : Associated (j δ) G := Ideal.span_singleton_eq_span_singleton.mp h
  have inj : Function.Injective j := by
    intro x y eq
    apply IsFractionRing.injective A F
    rw [IsScalarTower.algebraMap_apply A (Polynomial k) F,IsScalarTower.algebraMap_apply A (Polynomial k) F]
    exact congrArg (algebraMap (Polynomial k) F) eq
  have nonzero : G≠0 := by
    intro z
    have div : (j δ)∣0 := z ▸ associated.dvd
    have div' : 0∣j δ := z ▸ associated.dvd'
    exact (map_ne_zero_iff _ inj).mpr nz (zero_dvd_iff.mp div')
  obtain ⟨d,dd,cap⟩ := normalized_line_discriminant_degree bf bi nonzero
  exact ⟨d,dd,(congrArg (fun n : ℕ=>(n:ℤ)) (natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated associated))).trans_le cap⟩
#print axioms localized_line_discriminant_degree
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
omit [Algebra (PlaneRing k) E] [IsScalarTower (PlaneRing k) (PlaneField k) E] in
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
  change ((δ.map (algebraMap (Polynomial k) (GenericCoefficients k))).natDegree:ℤ)≤-2*d at cap
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _)] at cap
  exact ⟨bf,bi,d,dd,cap⟩
#print axioms genericLine_basis
#print axioms plane_generic_outer_degree
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
#print axioms generic_line_basis
#print axioms generic_line_trace_associated
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedGenericFrames

end Merged6967_R6960CollisionMarkedGenericFrames

section Merged6967_R6960MarkedActualCount
set_option Elab.async false







set_option Elab.async false

-- merged module R6960CollisionMarkedGlobalSum
section Merged_R6960CollisionMarkedGlobalSum
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial LaurentPolynomial CollisionTame Finset
open scoped Polynomial BigOperators
private theorem overlap_degree_one {R:Type} [CommRing R] [IsDomain R]
    (δf δi:(Polynomial R)) (nf:δf≠0) (c:R) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C c*T m*invert δi.toLaurent) :
    (δf.natDegree:ℤ)≤m := by
  let n : ℤ := δf.natDegree
  have left : δf.toLaurent.coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nf,rfl⟩)
  by_contra! bad
  change m<n at bad
  have right : δi.toLaurent.coeff (-(n-m))=0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [support_coeff_toLaurent]
    intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp h
    change (j:ℤ)=-(n-m) at hj
    omega
  have eq := congrArg (fun f:LaurentPolynomial R=>f.coeff n) overlap
  rw [←single_eq_C_mul_T,AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (n-m) (by intro v _; omega),
    invert_apply,right,mul_zero] at eq
  exact left eq
theorem plane_overlap_degree_caps {k:Type} [Field k]
    (δf δi:(Polynomial (Polynomial k))) (nf:δf≠0) (c:k) (cn:c≠0) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δi.toLaurent) :
    (δf.natDegree:ℤ)≤m ∧ (δi.natDegree:ℤ)≤m := by
  refine ⟨overlap_degree_one δf δi nf (C c) m overlap,?_⟩
  have ni : δi≠0 := by
    rintro rfl
    apply nf
    exact Polynomial.toLaurent_injective (by simpa only [map_zero,mul_zero] using overlap)
  have moved := congrArg (invert (R:=(Polynomial k))) overlap
  rw [map_mul,map_mul,invert_C,invert_T,involutive_invert] at moved
  have mirror : δi.toLaurent=LaurentPolynomial.C (Polynomial.C c⁻¹)*T m*invert δf.toLaurent := by
    rw [moved]
    calc _ = (LaurentPolynomial.C (Polynomial.C c⁻¹) * LaurentPolynomial.C (Polynomial.C c)) *
              (T m * T (-m)) * δi.toLaurent := by
                 rw [←map_mul,←map_mul,inv_mul_cancel₀ cn,map_one,map_one,←T_add,add_neg_cancel,T_zero,one_mul,one_mul]
         _ = _ := by ring
  exact overlap_degree_one δi δf ni (C c⁻¹) m mirror
theorem plane_degree_from_line_transition {k:Type} [Field k]
    (δf δi:(Polynomial (Polynomial k))) (nf:δf≠0) (c:k) (cn:c≠0) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δi.toLaurent)
    (z:k) (good:δf.map (evalRingHom z)≠0)
    (df di:(Polynomial k)) (af:Associated df (δf.map (evalRingHom z))) (ai:Associated di (δi.map (evalRingHom z)))
    (G:LaurentPolynomial k) (unit:IsUnit G) (trace:invert di.toLaurent=G^2*df.toLaurent)
    (s:ℕ) (measure:G.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    δf.natDegree≤2*s ∧ δi.natDegree≤2*s := by
  obtain ⟨d,gdeg,exponent⟩ := overlap_transition_exponent δf δi c cn m overlap
    (evalRingHom z) good df di af ai G unit trace
  have d_eq := WithBot.coe_injective (gdeg.symm.trans measure)
  obtain ⟨f,i⟩ := plane_overlap_degree_caps δf δi nf c cn m overlap
  omega
theorem native_index_sum {k:Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p:ℕ) [CharP (FractionRing (Polynomial k)) p]
    (δ:(Polynomial (Polynomial k))) (nz:δ≠0) (s t:ℕ)
    (xc:CurvatureSquares.height δ≤2*s) (zc:δ.natDegree≤2*t) (tame:2*s<p)
    (U:Finset k) (idx:k→(Polynomial k))
    (good:∀z∈U,(branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (support:∀z∈U,∀x∈(idx z).roots,
      2≤((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x)
    (square:∀ z∈U,(idx z)^2∣δ.eval (Polynomial.C z)) :
    (∑ z∈U,(idx z).natDegree)≤8*s*t := by
  let D := Bivariate.swap δ
  have nD : D≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
  have xD : D.natDegree≤2*s := xc
  have zD : CurvatureSquares.height D≤2*t := by
    change (Bivariate.swap (Bivariate.swap δ)).natDegree≤2*t
    rwa [Bivariate.swap_swap_apply]
  have small : (branchProduct D).natDegree<p :=
    (natDegree_le_of_dvd (branch_dvd D nD) nD).trans_lt (xD.trans_lt tame)
  have sep := BranchCollisions.tame_separable p (branch_squarefree D) small
  apply branch_index_of_discriminant D nD sep U good idx support ?_ xD zD
  intro z hz
  have eq : δ.eval (Polynomial.C z)=D.map (evalRingHom z) := by
    simpa only [D,Bivariate.swap_swap_apply] using RetainedCompression.eval_swap D z
  exact eq ▸ square z hz
#print axioms plane_degree_from_line_transition
#print axioms native_index_sum
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedGlobalSum

-- merged module R6960MarkedActualCount
section Merged_R6960MarkedActualCount
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open CollisionMarked NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass
open RetainedTwistedRestriction Polynomial Finset Algebra Module Submodule
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (finite_along)
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
local notation "aE" => algebraMap ChartField E

/-- Count the original word fibres with the independently measured chart
deficits. All finite collision losses, marked residues, and evaluation rows
are produced from this same original polynomial. -/
theorem actual_good_count (p:ℕ) [CharP L p] [CharP Scalar p] [DecidableEq L]
    (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0) (lo:2≤P.natDegree) (hi:P.natDegree<p)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root:let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (s t:ℕ) (positive:0<s) (tame:2*s<p) (surface:Budget E (s-1) (s+s*t))
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:axisDiscriminant (E:=E) false=Ideal.span {δf}) (di:axisDiscriminant (E:=E) true=Ideal.span {δi})
    (xc:CurvatureSquares.height δf≤2*s) (zc:δf.natDegree≤2*t)
    (U:Finset L) (nz:∀z∈U,z≠0) (words:L → Polynomial L) (mark:∀z∈U,RetainedCompression.MarkedFiber P z (words z))
    (boundary:∀z∈U,(Bivariate.swap δi).trailingCoeff.eval z≠0)
    (vertical:∀(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j))→
      finrank Scalar (span Scalar (Set.range v))+s≤P.natDegree*s) :
    U.card≤9*P.natDegree*t+P.natDegree*(P.natDegree-1) := by
  classical
  let ord:=axisScaledOrdinate P pn b.gen root
  let word (z:L):Tor E:=axisScaledWord P z (words z)
  have one (z:U):=(actual_axis_marked_family (E:=E) p P pn lo hi b dim root z.val (nz _ z.property) (words z)
    (mark _ z.property) (s-1) δf δi nf ni df di (boundary _ z.property))
  choose good d dn square support v indep reg kills using one
  let index (z:L):(Polynomial L):=if hz:z∈U then d ⟨z,hz⟩ else 1
  have sum:=native_index_sum p δf nf s t xc zc tame U index (fun z hz=>good ⟨z,hz⟩)
    (fun z hz=>by rw [show index z=d ⟨z,hz⟩ from dif_pos hz];exact support ⟨z,hz⟩)
    (fun z hz=>by rw [show index z=d ⟨z,hz⟩ from dif_pos hz];exact square ⟨z,hz⟩)
  let J (z:U):=Fin (s-1+1-(d z).natDegree)
  obtain ⟨m,f,li,columns,lifts⟩:=family_from_fibres (E:=E) (s-1) (s+s*t) surface U nz J v reg indep ord word kills
  let raw:=projectedRaw P
  let a:=planeFinite raw.leadingCoeff
  have scale : (ord:E)=aE a*b.gen := rfl
  have aa : Function.Injective planeFinite:=Subtype.val_injective.comp (oriented true false).injective
  have an : a≠0 := (map_ne_zero_iff _ aa).mpr (leadingCoeff_ne_zero.mpr pn)
  have rr : raw.eval₂ ((algebraMap ChartField E).comp planeFinite) b.gen=0 := root
  have scaledRoot : raw.integralNormalization.eval₂ ((algebraMap ChartField E).comp planeFinite) (ord:E)=0 := by
    let j:Plane L→+*E:=(algebraMap ChartField E).comp planeFinite
    letI := j.toAlgebra
    exact integralNormalization_aeval_eq_zero (z:=b.gen) (show aeval b.gen raw=0 from rr)
      (fun a h=>((algebraMap ChartField E).injective.comp aa) (h.trans (map_zero j).symm))
  have wordBase (z:L) (_:z∈U):∃w:ChartField,(word z:E)=aE w := by
    let w:=raw.leadingCoeff.eval (C z)*words z
    refine ⟨planeFinite (C w),?_⟩
    have eq:=Lower6960.RetainedSurfaceClass.finite_along E true false w
    exact congrArg (fun v:Tor E=>(v:E)) eq.symm
  obtain ⟨r,poles,rank,dimBound,orbit⟩:=native_norm f li (s-1) U nz ord word columns b
    (Algebra.IsSeparable.isSeparable ChartField b.gen) a an scale raw.integralNormalization scaledRoot
    (fun z hz=>normalized_fibre_separable z P _ p (by omega) hi (mark z hz)) wordBase
  have rle := vertical m f (fun j=>(columns j).1)
  rw [←rank] at rle
  let loss:=∑z∈U,(index z).natDegree
  have localSize :
      U.card*s≤loss+∑z:U,Fintype.card (J z) := by
    rw [show U.card*s=∑z:U,s from (by simp)]
    have together := Finset.sum_le_sum (s:=Finset.univ) (fun (z:U) _=>
      show s≤(index z.val).natDegree+Fintype.card (J z) from by
        rw [show index z.val=d z from dif_pos z.property]
        change s≤(d z).natDegree+Fintype.card (Fin (s-1+1-(d z).natDegree))
        rw [Fintype.card_fin];omega)
    rw [Finset.sum_add_distrib] at together
    have matched : ∑ z:U,(index z.val).natDegree=loss := by
      change ∑ z∈U.attach,(index z.val).natDegree=_
      exact Finset.sum_attach U (fun a=>(index a).natDegree)
    rwa [matched] at together
  rw [dim] at orbit
  rw [Fintype.card_fin] at dimBound
  apply price (loss:=loss) (obstructions:=s+s*t) (ordinary:=s) (meromorphic:=m) (rank:=r) (pole:=poles)
    positive (by omega) rle sum le_rfl le_rfl _ dimBound orbit
  omega

#print axioms actual_good_count
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedActualCount

end Merged6967_R6960MarkedActualCount
