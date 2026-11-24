import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapUnit
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport

-- merged module R6960CollisionTameOverlapDiscriminant
section Merged_R6960CollisionTameOverlapDiscriminant
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LaurentPolynomial
open scoped Polynomial
variable (k : Type) [Field k]
abbrev OverlapPlane := (Polynomial (Polynomial k))
abbrev OverlapLaurent := LaurentPolynomial (Polynomial k)
def overlapChart (s : Bool) : OverlapPlane k→+*OverlapLaurent k :=
  if s then invert.toRingEquiv.toRingHom.comp Polynomial.toLaurent else Polynomial.toLaurent
theorem overlapChart_localizes (s : Bool) :
    let : Algebra (OverlapPlane k) (OverlapLaurent k) := (overlapChart k s).toAlgebra
    IsLocalization.Away (Polynomial.X : OverlapPlane k) (OverlapLaurent k) := by
  let A := OverlapPlane k
  let L := OverlapLaurent k
  let : Algebra A L := (overlapChart k s).toAlgebra
  have inj : Function.Injective (overlapChart k s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact invert.injective.comp Polynomial.toLaurent_injective
  apply IsLocalization.Away.mk (Polynomial.X : A)
  · have image : overlapChart k s (Polynomial.X:A)=T (if s then -1 else 1) := by
      cases s <;> simp [overlapChart,Polynomial.toLaurent_X]
    change IsUnit (overlapChart k s (Polynomial.X:A))
    rw [image]
    exact isUnit_T _
  · intro u
    cases s with
    | false =>
      obtain ⟨n,p,eq⟩ := LaurentPolynomial.exists_T_pow u
      refine ⟨n,p,?_⟩
      change u*(overlapChart k false (Polynomial.X:A))^n=overlapChart k false p
      rw [←map_pow]
      change u*(Polynomial.X^n:A).toLaurent=p.toLaurent
      simpa only [Polynomial.toLaurent_X_pow] using eq.symm
    | true =>
      obtain ⟨n,p,eq⟩ := LaurentPolynomial.exists_T_pow (invert u)
      refine ⟨n,p,?_⟩
      change u*(overlapChart k true (Polynomial.X:A))^n=overlapChart k true p
      rw [←map_pow]
      change u*invert (Polynomial.X^n:A).toLaurent=invert p.toLaurent
      have h := congrArg (invert (R:=(Polynomial k))) eq
      rw [map_mul,involutive_invert u,invert_T] at h
      simpa only [Polynomial.toLaurent_X_pow,invert_T] using h.symm
  · intro a b eq
    exact ⟨0,by rw [inj eq]⟩
variable (F E : Type*) [Field F] [Field E]
  [IsDomain (OverlapLaurent k)] [IsIntegrallyClosed (OverlapLaurent k)] [IsNoetherianRing (OverlapLaurent k)]
  [Algebra (OverlapLaurent k) F] [IsFractionRing (OverlapLaurent k) F]
  [Algebra (OverlapLaurent k) E] [Algebra F E] [IsScalarTower (OverlapLaurent k) F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
omit [Field E] [Algebra (OverlapLaurent k) E] [Algebra F E]
  [IsScalarTower (OverlapLaurent k) F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [IsDomain (OverlapLaurent k)] [IsIntegrallyClosed (OverlapLaurent k)] [IsNoetherianRing (OverlapLaurent k)] in
theorem overlapChart_fraction (s : Bool) :
    let : Algebra (OverlapPlane k) F := ((algebraMap (OverlapLaurent k) F).comp (overlapChart k s)).toAlgebra
    IsFractionRing (OverlapPlane k) F := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  have injR : Function.Injective (overlapChart k s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact invert.injective.comp Polynomial.toLaurent_injective
  have inj : Function.Injective (algebraMap A F) := (IsFractionRing.injective R F).comp injR
  let : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective _ _).mpr inj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨r,u,_,ratio⟩ := IsFractionRing.div_surjective R z
  obtain ⟨n,a,ra⟩ := IsLocalization.Away.surj (Polynomial.X:A) r
  obtain ⟨m,b,ub⟩ := IsLocalization.Away.surj (Polynomial.X:A) u
  let j := algebraMap A R
  let h := algebraMap R F
  let t := j (Polynomial.X:A)
  have tn : h t≠0 := (map_ne_zero_iff _ inj).mpr X_ne_zero
  change r*t^n=j a at ra
  change u*t^m=j b at ub
  have ra' : algebraMap A F (a*Polynomial.X^m)=h r*(h t)^(n+m) := by
    change h (j (a*Polynomial.X^m))=h r*(h t)^(n+m)
    rw [map_mul j,map_pow j]
    change h (j a*t^m)=_
    rw [←ra,map_mul h,map_mul h,map_pow h,map_pow h,mul_assoc,←pow_add]
  have ub' : algebraMap A F (b*Polynomial.X^n)=h u*(h t)^(n+m) := by
    change h (j (b*Polynomial.X^n))=h u*(h t)^(n+m)
    rw [map_mul j,map_pow j]
    change h (j b*t^n)=_
    rw [←ub,map_mul h,map_mul h,map_pow h,map_pow h,mul_assoc,←pow_add,Nat.add_comm m n]
  refine ⟨a*Polynomial.X^m,b*Polynomial.X^n,?_⟩
  rw [ra',ub',mul_div_mul_right _ _ (pow_ne_zero _ tn)]
  exact ratio.symm
def overlapChartDiscriminant (s : Bool) : Ideal (OverlapPlane k) := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=F) fun _=>rfl
  let : IsFractionRing A F := overlapChart_fraction k F s
  let : Algebra A E := ((algebraMap R E).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=F) (A:=E) fun a=>by
    change algebraMap R E (overlapChart k s a)=algebraMap F E (algebraMap R F (overlapChart k s a))
    exact IsScalarTower.algebraMap_apply R F E _
  exact normalizationDiscriminant (A:=A) (E:=E) F
theorem overlapChart_discriminant_map (s : Bool) :
    (overlapChartDiscriminant k F E s).map (overlapChart k s)=
      normalizationDiscriminant (A:=OverlapLaurent k) (E:=E) F := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=F) fun _=>rfl
  let : IsFractionRing A F := overlapChart_fraction k F s
  let : Algebra A E := ((algebraMap R E).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=E) fun _=>rfl
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=F) (A:=E) fun a=>by
    change algebraMap R E (overlapChart k s a)=algebraMap F E (algebraMap R F (overlapChart k s a))
    exact IsScalarTower.algebraMap_apply R F E _
  exact normalizationDiscriminant_map (A:=A) (R:=R) (F:=F) (E:=E) (Submonoid.powers (Polynomial.X:A))
theorem actual_overlap_unit (δfin δinf : OverlapPlane k)
    (f : overlapChartDiscriminant k F E false=Ideal.span {δfin})
    (i : overlapChartDiscriminant k F E true=Ideal.span {δinf}) :
    ∃ (c : k) (m : ℤ),c≠0 ∧
      δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent := by
  have a := overlapChart_discriminant_map k F E false
  have b := overlapChart_discriminant_map k F E true
  rw [f,Ideal.map_span,Set.image_singleton] at a
  rw [i,Ideal.map_span,Set.image_singleton] at b
  exact plane_overlap_unit δfin δinf (a.trans b.symm)
#print axioms actual_overlap_unit
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameOverlapDiscriminant

-- merged module R6960CollisionMarkedPlaneOverlap
section Merged_R6960CollisionMarkedPlaneOverlap
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus MonicFourChartDescent
open CollisionTame Polynomial LaurentPolynomial Module
open scoped Lower6960.MonicChartProbes Polynomial
open Lower6960.RetainedSurfaceClass (oriented_var oriented_line oriented_const)
open Lower6960.CollisionTame (overlapChart_localizes overlapChart_fraction)
def outerPlane (j b:Bool) : Plane L≃+*baseChart (reference j b) :=
  Bivariate.swap.toRingEquiv.trans (oriented j b)
def outerField (j b:Bool) : Plane L→+*ChartField :=
  (baseChart (reference j b)).subtype.comp (outerPlane j b).toRingHom
private theorem outerField_injective (j b:Bool) : Function.Injective (outerField j b) :=
  Subtype.val_injective.comp (outerPlane j b).injective
theorem outer_X (j b:Bool) :
    outerField j b Polynomial.X=chartCoordinate b (coordinate (!j)) := by
  change ((oriented j b (Bivariate.swap Polynomial.X)):ChartField)=_
  rw [Bivariate.swap_Y]
  exact Lower6960.RetainedSurfaceClass.oriented_line j b
theorem outer_CX (j b:Bool) :
    outerField j b (Polynomial.C Polynomial.X)=coordinate j := by
  change ((oriented j b (Bivariate.swap (Polynomial.C Polynomial.X))):ChartField)=_
  rw [Bivariate.swap_X]
  exact Lower6960.RetainedSurfaceClass.oriented_var j b
theorem outer_CC (j b:Bool) (c:L) :
    outerField j b (Polynomial.C (Polynomial.C c))=constants c := by
  change ((oriented j b (Bivariate.swap (Polynomial.C (Polynomial.C c)))):ChartField)=_
  rw [Bivariate.swap_C_C]
  exact Lower6960.RetainedSurfaceClass.oriented_const j b c
theorem outerField_fraction (j b:Bool) :
    let : Algebra (Plane L) ChartField := (outerField j b).toAlgebra
    IsFractionRing (Plane L) ChartField := by
  let : Algebra (Plane L) ChartField := (outerField j b).toAlgebra
  exact IsFractionRing.of_ringEquiv_left (outerPlane j b) (fun _=>rfl)
private def overlapField (j:Bool) : OverlapLaurent L→+*ChartField := by
  let A := Plane L
  let R := OverlapLaurent L
  let : Algebra A R := (overlapChart L false).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
  apply IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:A)) (g:=outerField j false)
  intro u
  have une : (u:A)≠0 := by
    obtain ⟨n,hn⟩ := u.property
    rw [←hn]
    exact pow_ne_zero _ Polynomial.X_ne_zero
  exact IsUnit.mk0 _ ((map_ne_zero_iff _ (outerField_injective j false)).mpr une)
private theorem overlap_finite (j:Bool) (a:Plane L) :
    overlapField j a.toLaurent=outerField j false a := by
  let : Algebra (Plane L) (OverlapLaurent L) := (overlapChart L false).toAlgebra
  let : IsLocalization.Away (Polynomial.X:Plane L) (OverlapLaurent L) :=
    Lower6960.CollisionTame.overlapChart_localizes L false
  exact IsLocalization.lift_eq _ _
private theorem overlap_field_chart (j b:Bool) :
    (overlapField j).comp (overlapChart L b)=outerField j b := by
  cases b with
  | false => exact RingHom.ext (overlap_finite j)
  | true =>
    apply Polynomial.ringHom_ext
    · intro r
      change overlapField j (invert ((Polynomial.C r).toLaurent))=outerField j true (Polynomial.C r)
      rw [Polynomial.toLaurent_C,invert_C,←Polynomial.toLaurent_C,overlap_finite]
      have eq : (outerField j false).comp Polynomial.C=(outerField j true).comp Polynomial.C :=
        Polynomial.ringHom_ext (fun c=>(outer_CC j false c).trans (outer_CC j true c).symm)
          ((outer_CX j false).trans (outer_CX j true).symm)
      exact DFunLike.congr_fun eq r
    · change overlapField j (invert ((Polynomial.X:Plane L).toLaurent))=outerField j true Polynomial.X
      rw [Polynomial.toLaurent_X,invert_T,outer_X]
      have finite : overlapField j (T 1)=coordinate (!j) := by
        rw [←Polynomial.toLaurent_X,overlap_finite,outer_X]
        rfl
      change overlapField j (T (-1))=(coordinate (!j))⁻¹
      have rel : overlapField j (T (-1))*coordinate (!j)=1 := by
        rw [←finite,←map_mul,←T_add]
        norm_num
      calc _ = (overlapField j (T (-1))*coordinate (!j))*(coordinate (!j))⁻¹ := by
             rw [mul_assoc,mul_inv_cancel₀ (coord_ne _),mul_one]
           _ = _ := by rw [rel,one_mul]
private theorem overlapField_fraction (j:Bool) :
    let : Algebra (OverlapLaurent L) ChartField := (overlapField j).toAlgebra
    IsFractionRing (OverlapLaurent L) ChartField := by
  let A := Plane L
  let R := OverlapLaurent L
  let : Algebra A R := (overlapChart L false).toAlgebra
  let : Algebra A ChartField := (outerField j false).toAlgebra
  let : IsFractionRing A ChartField := outerField_fraction j false
  let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
  let : Algebra R ChartField := (overlapField j).toAlgebra
  let : IsScalarTower A R ChartField := IsScalarTower.of_algebraMap_eq
    (R:=A) (S:=R) (A:=ChartField) (fun x=>(overlap_finite j x).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (Polynomial.X:A)) R ChartField
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]
def lineDiscriminant (j b:Bool) : Ideal (Plane L) :=
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := linePlaneTower j b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := lineFraction_separable j b
  normalizationDiscriminant (A:=Plane L) (E:=E) (FractionRing (Plane L))
theorem line_discriminant_axis (b:Bool) : lineDiscriminant (E:=E) true b=axisDiscriminant (E:=E) b := rfl
theorem line_discriminant_swap :
    (lineDiscriminant (E:=E) true false).map Bivariate.swap.toRingHom =
      lineDiscriminant (E:=E) false false := by
  let A := Plane L
  let F := FractionRing A
  let e := Bivariate.swap (R:=L)
  let T := baseChart (false,false)
  let t : A≃+*T := oriented false false
  let s : A≃+*T := oriented true false
  let D := normalizationDiscriminant (A:=T) (E:=E) ChartField
  have compare (j:Bool) :
      (lineDiscriminant (E:=E) j false).map (oriented j false).toRingHom=
        normalizationDiscriminant (A:=baseChart (reference j false)) (E:=E) ChartField := by
    let : Algebra A E := linePlaneAlgebra j false
    let : Algebra F E := lineFractionAlgebra j false
    let : SMul A F := (inferInstance : Algebra A F).toSMul
    let : IsScalarTower A F E := linePlaneTower j false
    let : FiniteDimensional F E := Module.Finite.of_basis
      (lineFractionBasis (E:=E) j false (Module.finBasis ChartField E)).val
    let : Algebra.IsSeparable F E := lineFraction_separable j false
    exact discriminant_transport (oriented j false) (linePlaneFractionEquiv j false)
      (fun a=>(linePlaneFractionEquiv_apply j false a).symm) (fun _=>rfl)
  have left : (lineDiscriminant (E:=E) true false).map s.toRingHom=D := compare true
  have right : (lineDiscriminant (E:=E) false false).map t.toRingHom=D := compare false
  have both : ((lineDiscriminant (E:=E) true false).map e.toRingHom).map t.toRingHom=
      (lineDiscriminant (E:=E) false false).map t.toRingHom := by
    rw [right,Ideal.map_map]
    exact left
  have h := congrArg (Ideal.comap t.toRingHom) both
  simpa only [Ideal.comap_map_of_bijective t.toRingHom t.bijective] using h
theorem line_overlap_unit (j:Bool) (δf δi:Plane L)
    (f:lineDiscriminant (E:=E) j false=Ideal.span {δf})
    (i:lineDiscriminant (E:=E) j true=Ideal.span {δi}) :
    ∃ (c:L) (m:ℤ),c≠0 ∧
      (Bivariate.swap δf).toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*
        invert (Bivariate.swap δi).toLaurent := by
  let A := Plane L
  let R := OverlapLaurent L
  let F := FractionRing A
  let : Algebra R ChartField := (overlapField j).toAlgebra
  let : Algebra R E := ((algebraMap ChartField E).comp (overlapField j)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsFractionRing R ChartField := overlapField_fraction j
  let : IsNoetherianRing R := by
    let : Algebra A R := (overlapChart L false).toAlgebra
    let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
    exact IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X:A)) R inferInstance
  let : IsIntegrallyClosed R := by
    let : Algebra A R := (overlapChart L false).toAlgebra
    let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
    exact isIntegrallyClosed_of_isLocalization R (Submonoid.powers (Polynomial.X:A)) (by
      rintro _ ⟨n,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ Polynomial.X_ne_zero))
  have transport (b:Bool) :
    (lineDiscriminant (E:=E) j b).map Bivariate.swap.toRingHom =
      overlapChartDiscriminant L ChartField E b := by
    let aA : Algebra A E := linePlaneAlgebra j b
    let : Algebra A E := aA
    let : Algebra F E := lineFractionAlgebra j b
    let : SMul A F := (inferInstance : Algebra A F).toSMul
    let ta : IsScalarTower A F E := linePlaneTower j b
    let : IsScalarTower A F E := ta
    let : FiniteDimensional F E := Module.Finite.of_basis
      (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
    let : Algebra.IsSeparable F E := lineFraction_separable j b
    let : Algebra A ChartField := ((overlapField j).comp (overlapChart L b)).toAlgebra
    let B := A
    let aB : Algebra B E := ((algebraMap R E).comp (overlapChart L b)).toAlgebra
    let : Algebra B E := aB
    let : IsFractionRing B ChartField := Lower6960.CollisionTame.overlapChart_fraction L ChartField b
    let tb : IsScalarTower B ChartField E := IsScalarTower.of_algebraMap_eq
      (R:=B) (S:=ChartField) (A:=E) fun _=>rfl
    have same (x:A) : algebraMap B ChartField (Bivariate.swap x)=
        linePlaneFractionEquiv j b (algebraMap A F x) := by
      change ((overlapField j).comp (overlapChart L b)) (Bivariate.swap x)=_
      rw [overlap_field_chart,linePlaneFractionEquiv_apply]
      change ((oriented j b (Bivariate.swap (Bivariate.swap x))):ChartField)=_
      rw [Bivariate.swap_swap_apply]
    exact @discriminant_transport A B F ChartField E
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      aA aB inferInstance inferInstance ta tb
      inferInstance inferInstance inferInstance inferInstance
      Bivariate.swap.toRingEquiv (linePlaneFractionEquiv j b) same (fun _=>rfl)
  have df := (transport false).symm.trans (congrArg (Ideal.map Bivariate.swap.toRingHom) f)
  have di := (transport true).symm.trans (congrArg (Ideal.map Bivariate.swap.toRingHom) i)
  rw [Ideal.map_span,Set.image_singleton] at df di
  exact actual_overlap_unit L ChartField E _ _ df di
#print axioms line_overlap_unit
#print axioms line_discriminant_swap
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedPlaneOverlap
