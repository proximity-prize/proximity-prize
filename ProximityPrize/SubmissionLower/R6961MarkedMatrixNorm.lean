import ProximityPrize.SubmissionLower.R6961MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6961MonicChartProbes

set_option Elab.async false

-- merged module R6961MarkedScalarAxis
section Merged_R6961MarkedScalarAxis

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6960.MonicChart (Infinity)
open Lower6961.MonicChart (ChartField Scalar)
open MonicFourChartDescent (scalarCoordinate constants baseChart chartCoordinate)
open MonicChartProbes (planeMap)
open Polynomial
open scoped Polynomial Lower6960.MonicChart Lower6961.MonicChart
open Lower6961.MonicChartProbes (planeMap_finite)

def swapBase : ChartField≃+*ChartField :=
  letI := MonicChart.plane_fractionRing
  IsFractionRing.ringEquivOfRingEquiv (K:=ChartField) (L:=ChartField) (Bivariate.swap (R:=L)).toRingEquiv

theorem swap_plane (p:Lower6960.PlaneConstants.Plane L) :
    swapBase (planeMap (false,false) p)=planeMap (false,false) (Bivariate.swap p) := by
  letI:=MonicChart.plane_fractionRing
  rw [Lower6961.MonicChartProbes.planeMap_finite]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

theorem swap_x : swapBase RatFunc.X=scalarCoordinate := by
  simpa only [Bivariate.swap_Y,MonicChartProbes.planeMap_abscissa,MonicChartProbes.planeMap_scalar,chartCoordinate,ite_false,
    Bool.false_eq_true] using swap_plane Polynomial.X
theorem swap_z : swapBase scalarCoordinate=RatFunc.X := by
  simpa only [Bivariate.swap_X,MonicChartProbes.planeMap_abscissa,MonicChartProbes.planeMap_scalar,chartCoordinate,ite_false,
    Bool.false_eq_true] using swap_plane (C Polynomial.X)
theorem swap_constant (c:L) : swapBase (constants c)=constants c := by
  simpa only [Bivariate.swap_C_C,MonicChartProbes.planeMap_constants] using swap_plane (C (C c))

def inner : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
def rowBase (c:L) : ChartField≃+*ChartField := (translateField ChartField (inner c)).trans swapBase

private theorem translate_const (c:L) (r:Scalar) : translateField ChartField (inner c) (RatFunc.C r)=RatFunc.C r := by
  rw [←RatFunc.algebraMap_C,translate_polynomial,taylor_C]

theorem row_abscissa (c:L) : rowBase c RatFunc.X=scalarCoordinate+constants c := by
  change swapBase (translateField ChartField (inner c) RatFunc.X)=_
  rw [←RatFunc.algebraMap_X,translate_polynomial,taylor_X,map_add,RatFunc.algebraMap_X,RatFunc.algebraMap_C,map_add,swap_x]
  exact congrArg (scalarCoordinate+·) (swap_constant c)
theorem row_parameter (c:L) : rowBase c scalarCoordinate=RatFunc.X := by
  change swapBase (translateField ChartField (inner c) (RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))))=_
  rw [translate_const]; exact swap_z
theorem row_constant (c a:L) : rowBase c (constants a)=constants a := by
  change swapBase (translateField ChartField (inner c) (RatFunc.C (algebraMap (Polynomial L) Scalar (C a))))=_
  rw [translate_const]; exact swap_constant a

/-- In the scalar orientation, the physical abscissa and every translated
abscissa are constants. A finite scalar chart therefore remains polynomial,
and the scalar infinity chart remains integral at infinity. -/
theorem finite_base (c:L) {a:ChartField} (h:a∈baseChart (false,false)) :
    rowBase c a ∈ (algebraMap (Polynomial Scalar) ChartField).range := by
  have le : baseChart (false,false)≤(algebraMap (Polynomial Scalar) ChartField).range.comap (rowBase c).toRingHom := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact ⟨C (inner r),(RatFunc.algebraMap_C _).trans (row_constant c r).symm⟩
    · change _=chartCoordinate false RatFunc.X at eq;subst_vars
      refine ⟨C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c),?_⟩
      rw [RatFunc.algebraMap_C,map_add]
      exact (row_abscissa c).symm
    · change _=chartCoordinate false scalarCoordinate at eq;subst_vars
      exact ⟨Polynomial.X,RatFunc.algebraMap_X.trans (row_parameter c).symm⟩
  exact le h

theorem infinity_base (c:L) [DecidableEq ChartField] {a:ChartField} (h:a∈baseChart (false,true)) :
    rowBase c a ∈ (algebraMap (Infinity Scalar) ChartField).range := by
  have le : baseChart (false,true)≤(algebraMap (Infinity Scalar) ChartField).range.comap (rowBase c).toRingHom := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact ⟨Lower6960.MonicChart.inftyRingEval Scalar (C (inner r)),(aeval_C _ _).trans (row_constant c r).symm⟩
    · change _=chartCoordinate false RatFunc.X at eq;subst_vars
      refine ⟨Lower6960.MonicChart.inftyRingEval Scalar (C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c)),?_⟩
      change Lower6960.MonicChart.AtInfinity Scalar (C _) = rowBase c RatFunc.X
      rw [show Lower6960.MonicChart.AtInfinity Scalar (C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c))=
        RatFunc.C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c) from aeval_C _ _,map_add,row_abscissa];rfl
    · change _=chartCoordinate true scalarCoordinate at eq;subst_vars
      refine ⟨Lower6960.MonicChart.inftyRingEval Scalar Polynomial.X,?_⟩
      change _=rowBase c scalarCoordinate⁻¹
      rw [map_inv₀,row_parameter];exact Lower6960.MonicChart.mapped_X_infty
  exact le h

theorem row_seed_polynomial (c:L) (p:(Polynomial L)) :
    rowBase c (RatFunc.C (algebraMap (Polynomial L) Scalar p))=
      algebraMap (Polynomial Scalar) ChartField (p.map inner) := by
  let f: (Polynomial L)→+*ChartField := (rowBase c).toRingHom.comp (RatFunc.C.comp (algebraMap (Polynomial L) Scalar))
  let g: (Polynomial L)→+*ChartField := (algebraMap (Polynomial Scalar) ChartField).comp (Polynomial.mapRingHom inner)
  have eq : f=g := by
    apply Polynomial.ringHom_ext
    · intro a
      change rowBase c (constants a)=algebraMap (Polynomial Scalar) ChartField ((C a).map inner)
      rw [row_constant,Polynomial.map_C,RatFunc.algebraMap_C];rfl
    · change rowBase c scalarCoordinate=algebraMap (Polynomial Scalar) ChartField ((Polynomial.X:(Polynomial L)).map inner)
      rw [row_parameter,Polynomial.map_X,RatFunc.algebraMap_X]
  exact DFunLike.congr_fun eq p

/-- Move an actual integral section across a horizontal embedding into the
appropriate scalar chart. The chart test is only on the base coefficients. -/
theorem integral_section {E Ω A : Type*} [Field E] [Field Ω] [CommRing A]
    [Algebra ChartField E] [Algebra ChartField Ω] [Algebra A ChartField]
    [Algebra A Ω] [IsScalarTower A ChartField Ω] (c:L) (s:Lower6960.ChartSections.Chart)
    (emb:E→+*Ω) (on_base:∀v,emb (algebraMap ChartField E v)=algebraMap ChartField Ω (rowBase c v))
    (inj:Function.Injective (algebraMap A ChartField))
    (base:∀a∈baseChart s,rowBase c a∈(algebraMap A ChartField).range)
    {v:E} (iv:IsIntegral (baseChart s) v) : IsIntegral A (emb v) := by
  let m := ((rowBase c).toRingHom.comp (baseChart s).subtype)
  let j:=algebraMap A ChartField
  let e : A≃+*j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b eq=>inj (congrArg Subtype.val eq),j.rangeRestrict_surjective⟩
  let lift:baseChart s→+*A := e.symm.toRingHom.comp (m.codRestrict j.range (fun x=>base x x.property))
  have comm (a:baseChart s) : algebraMap A Ω (lift a)=emb (algebraMap (baseChart s) E a) := by
    rw [IsScalarTower.algebraMap_apply A ChartField Ω]
    change algebraMap ChartField Ω (j (lift a))=emb (algebraMap ChartField E (a:ChartField))
    rw [on_base]
    exact congrArg (algebraMap ChartField Ω) (congrArg Subtype.val (e.apply_symm_apply ⟨m a,base a a.property⟩))
  obtain ⟨p,mon,root⟩:=iv
  refine ⟨p.map lift,mon.map _,?_⟩
  have eq: (algebraMap A Ω).comp lift=emb.comp (algebraMap (baseChart s) E) := RingHom.ext comm
  rw [eval₂_map,eq,←Polynomial.hom_eval₂,root,map_zero]

#print axioms finite_base
#print axioms infinity_base
#print axioms integral_section
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedScalarAxis

-- merged module R6961MarkedMatrixNorm
section Merged_R6961MarkedMatrixNorm

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Module Matrix Algebra Polynomial Finset
open scoped Polynomial Matrix BigOperators
variable {k K E I J:Type} [Field k] [Field K] [DecidableEq (RatFunc K)] [Field E]
  [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
  [Algebra (Lower6960.SheetNorm.Infinity K) E] [IsScalarTower (Lower6960.SheetNorm.Infinity K) (RatFunc K) E]
  [Fintype I] [DecidableEq I] [Fintype J]
local notation "ι" => algebraMap (RatFunc K) E
local notation "basePoly" => algebraMap (Polynomial K) (RatFunc K)

def polePolynomial (T:Finset K) : (Polynomial K) := ∏ z∈T,(Polynomial.X-C z)
theorem polePolynomial_monic (T:Finset K) : (polePolynomial T).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun z _=>monic_X_sub_C z)
theorem polePolynomial_degree (T:Finset K) : (polePolynomial T).natDegree=T.card := by
  rw [polePolynomial,Polynomial.natDegree_prod _ _ (fun z _=>X_sub_C_ne_zero z)]
  simp

theorem leading_unit (P:(Polynomial K)) (nz:P≠0) :
    let u:=basePoly P/(RatFunc.X^P.natDegree)
    u∈Lower6960.SheetNorm.Infinity K ∧ u⁻¹∈Lower6960.SheetNorm.Infinity K := by
  let u:=basePoly P/(RatFunc.X^P.natDegree)
  have val : RatFunc.inftyValuation K u=1 := by
    change RatFunc.inftyValuation K (basePoly P/(RatFunc.X^P.natDegree))=1
    rw [map_div₀,←zpow_natCast,RatFunc.inftyValuation.X_zpow]
    change RatFunc.inftyValuationDef K (basePoly P)/_=_
    rw [RatFunc.inftyValuation.polynomial _ nz,div_self (by simp)]
  exact ⟨show RatFunc.inftyValuation K u≤1 from val.le,
    show RatFunc.inftyValuation K u⁻¹≤1 from by rw [map_inv₀,val,inv_one]⟩

theorem integral_infty {u:RatFunc K} (h:u∈Lower6960.SheetNorm.Infinity K) :
    IsIntegral (Lower6960.SheetNorm.Infinity K) (ι u:E) := by
  have e := isIntegral_algebraMap (A:=E) (x:=(⟨u,h⟩:Lower6960.SheetNorm.Infinity K))
  rw [IsScalarTower.algebraMap_apply (Lower6960.SheetNorm.Infinity K) (RatFunc K) E] at e
  exact e

theorem count_from_original_columns [IsGalois (RatFunc K) E] (inK:k→+*K) (labels:Finset K)
    (Q:Matrix I J (Polynomial k)) (T:Matrix J I (Polynomial k)) (pick:I↪J) (pnonzero:(Q.submatrix _root_.id pick).det≠0)
    (A:Matrix I J E) (B:Matrix I I E) (det:B.det≠0)
    (repr : A=B*Q.map ((algebraMap (Polynomial K) E).comp (Polynomial.mapRingHom inK)))
    (generated : B=A*T.map ((algebraMap (Polynomial K) E).comp (Polynomial.mapRingHom inK)))
    (finite:∀i j,IsIntegral (Polynomial K) (algebraMap (Polynomial K) E (polePolynomial labels)*A i j))
    (infty:∀i j,IsIntegral (Lower6960.SheetNorm.Infinity K) (A i j))
    (e:ℕ) (ep:0<e)
    (O:K→Type) [∀z,CommRing (O z)] [∀z,IsDomain (O z)] [∀z,IsLocalRing (O z)]
    (φ:∀z,(Polynomial K)→+*O z) (incl:∀z,O z→+*E) (inj:∀z,Function.Injective (incl z))
    (base:∀z,(incl z).comp (φ z)=(algebraMap (RatFunc K) E).comp basePoly)
    (π:∀z,O z) (place:∀z∈labels,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (localA:∀z,Lower6960.SheetNorm.Aut K E→Matrix I J (O z)) (rows:K→Lower6960.SheetNorm.Aut K E→Finset I)
    (realize:∀z∈labels,∀g i j,incl z (localA z g i j)=g (algebraMap (Polynomial K) E (polePolynomial labels)*A i j))
    (off:∀z∈labels,∀g,∀i∈rows z g,∀j,π z∣localA z g i j)
    (freq:∀z∈labels,e*(∑g:Lower6960.SheetNorm.Aut K E,(rows z g).card)=
      Fintype.card (Lower6960.SheetNorm.Aut K E)*((e-1)*Fintype.card I)) :
    e*(Q.submatrix _root_.id pick).det.natDegree≤labels.card*Fintype.card I := by
  classical
  let D:=polePolynomial labels
  let q:=(Q.submatrix _root_.id pick).det
  let P:=q.map inK
  let d:=q.natDegree
  let r:=Fintype.card I
  let j:=algebraMap (Polynomial K) E
  let inc:=j.comp (Polynomial.mapRingHom inK)
  let H:Matrix I I E:=j D • B
  have dn:D≠0 := (polePolynomial_monic labels).ne_zero
  have ji : Function.Injective j := by
    rw [show j=(algebraMap (RatFunc K) E).comp basePoly from IsScalarTower.algebraMap_eq (Polynomial K) (RatFunc K) E]
    exact (algebraMap (RatFunc K) E).injective.comp (IsFractionRing.injective _ _)
  have hn:H.det≠0 := by
    rw [show H.det=(j D)^r*B.det from Matrix.det_smul ..]
    exact mul_ne_zero (pow_ne_zero _ (ji.ne_iff.mpr dn |> fun p=>by simpa using p)) det
  have fe:IsIntegral (Polynomial K) H.det := by
    apply IsIntegral.det
    intro u v
    change IsIntegral _ (j D*B u v)
    rw [generated,Matrix.mul_apply,Finset.mul_sum]
    apply IsIntegral.sum;intro l _
    rw [←mul_assoc]
    exact (finite u l).mul (isIntegral_algebraMap (A:=E) (x:=(T l v).map inK))
  have sub:(A.submatrix _root_.id pick).det=B.det*j P := by
    rw [repr,Matrix.submatrix_mul _ _ _root_.id _root_.id pick Function.bijective_id,Matrix.submatrix_id_id,Matrix.det_mul]
    exact congrArg (B.det*·) (RingHom.map_det inc (Q.submatrix _root_.id pick)).symm
  have pn:P≠0 := (Polynomial.map_ne_zero_iff inK.injective).mpr pnonzero
  have pd:P.natDegree=d := natDegree_map_eq_of_injective inK.injective q
  have normalized:=integral_infty (E:=E) (leading_unit (K:=K) P pn).2
  have weight:=integral_infty (E:=E) (leading_unit (K:=K) D dn).1
  have detInf:IsIntegral (Lower6960.SheetNorm.Infinity K) (A.submatrix _root_.id pick).det :=
    IsIntegral.det (fun u v=>infty u (pick v))
  have wz : IsIntegral (Lower6960.SheetNorm.Infinity K) ((ι RatFunc.X)^d*H.det/ι (RatFunc.X^(labels.card*r))) := by
    have ok:=((weight.pow r).mul normalized).mul detInf
    rw [sub] at ok
    rw [show H.det=(j D)^r*B.det from Matrix.det_smul ..]
    have J (p:(Polynomial K)) : ι (basePoly p)=j p := (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) E _).symm
    rw [map_inv₀,map_div₀,map_div₀,J P,J D,map_pow,map_pow,pd,polePolynomial_degree] at ok
    have xeq:ι (RatFunc.X^(labels.card*r))=(ι RatFunc.X ^labels.card)^r := by rw [map_pow,pow_mul]
    rw [xeq]
    have hP:j P≠0 := (map_ne_zero_iff _ ji).mpr pn
    have hX:(ι RatFunc.X:E)≠0 := (map_ne_zero_iff _ (algebraMap (RatFunc K) E).injective).mpr RatFunc.X_ne_zero
    have alg {x y z b:E} (yx:x≠0) (nz:z≠0) (n r d:ℕ) :
        x^d*(y^r*b)/(x^n)^r=(y/x^n)^r*(z/x^d)⁻¹*(b*z) := by
      rw [div_pow,inv_div]; field_simp [yx,nz] <;> ring
    exact (alg hX hP labels.card r d).symm ▸ ok
  let localH (z:K) (g:Lower6960.SheetNorm.Aut K E):=localA z g * T.map ((φ z).comp (Polynomial.mapRingHom inK))
  apply conjugate_bound e d ep labels H hn fe wz O φ incl inj base π place localH rows _ _ freq
  · intro z hz g u v
    change incl z (∑l,localA z g u l*φ z ((T l v).map inK))=g (j D*B u v)
    rw [generated,Matrix.mul_apply,Finset.mul_sum,map_sum,map_sum]
    apply Finset.sum_congr rfl; intro l _
    have coeff:=DFunLike.congr_fun (base z) ((T l v).map inK)
    change incl z (φ z ((T l v).map inK))=ι (basePoly ((T l v).map inK)) at coeff
    rw [map_mul,realize z hz g u l,coeff]
    change g (j D*A u l)*ι (basePoly ((T l v).map inK))=g (j D*(A u l*j ((T l v).map inK)))
    rw [←mul_assoc,map_mul g (j D*A u l)]
    exact congrArg (g (j D*A u l)*·) (by
      rw [show j ((T l v).map inK)=ι (basePoly ((T l v).map inK)) from IsScalarTower.algebraMap_apply _ _ _ _,g.commutes])
  · intro z hz g u hu v
    change π z∣∑l,localA z g u l*φ z ((T l v).map inK)
    exact Finset.dvd_sum (fun l _=>(off z hz g u hu l).trans (dvd_mul_right ..))

#print axioms count_from_original_columns
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedMatrixNorm
