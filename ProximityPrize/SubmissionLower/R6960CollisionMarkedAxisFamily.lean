import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionMarkedIndexSpecialization
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960CollisionMarkedAxisFamily
set_option Elab.async false







set_option Elab.async false

-- merged module R6960CollisionMarkedAxisWord
section Merged_R6960CollisionMarkedAxisWord
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra Module
open RetainedRestrictionTorus
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
variable {E : Type} [Field E] [Algebra ChartField E]
local instance wordAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
local instance wordFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)
private def relocatedPowerBasis (b:PowerBasis ChartField E) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
    PowerBasis (FractionRing (Plane L)) E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let m := axisFractionBasis (E:=E) false b.basis
  exact { gen := b.gen, dim := b.dim, basis := m.val
          basis_eq_pow := fun i=>(m.property i).trans (b.basis_eq_pow i) }
def axisScaledOrdinate (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0) (g:E)
    (root : let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval g (projectedRaw P)=0) : Tor E := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  exact intoTorus E (reference true false)
    (axisPlaneOrder false (scaledRoot (projectedRaw P) g pn root))
def axisScaledWord (P:CurvatureSquares.Ordinate) (z:L) (S:(Polynomial L)) : Tor E :=
  along E true false ((projectedRaw P).leadingCoeff.eval (C z)*S)
theorem actual_axis_projector [FiniteDimensional ChartField E] (p:ℕ)
    [CharP (FractionRing (Polynomial L)) p]
    (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0)
    (large:2≤P.natDegree) (small:P.natDegree<p)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root : let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (z:L) (nz:z≠0) (S:(Polynomial L)) (mark:RetainedCompression.MarkedFiber P z S) :
    ∃ η:AxisGeneric (E:=E) z, IsReduced (AxisGeneric (E:=E) z) ∧ η^2=η ∧ η≠0 ∧
      axisToGeneric (E:=E) z (red E true z
        (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S))*η=0 := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  let c := relocatedPowerBasis b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis c.basis
  let G := axisGenericData (E:=E) false z nz
  let q := (projectedRaw P).integralNormalization.map (genericFibreBase z)
  let g := G.val
  obtain ⟨e,H,_,sep,_,_,_,_,idem,nonzero,_,kills⟩ :=
    projected_word_sheet p P large small c dim root z S mark
  let η := g (e (AdjoinRoot.mk q H))
  have r : IsReduced (AdjoinRoot q) := separable_adjoinRoot_reduced q sep
  let f := g.symm.trans e.toRingEquiv.symm
  have redV : IsReduced (AxisGeneric (E:=E) z) := by
    constructor
    intro x hx
    apply f.injective
    rw [map_zero]
    exact r.eq_zero _ (hx.map f.toRingHom)
  refine ⟨η,redV,?_,fun h=>nonzero (g.map_eq_zero_iff.mp h),?_⟩
  · exact (map_pow g _ 2).symm.trans (congrArg g idem)
  let y := (projectedRaw P).leadingCoeff.eval (C z)*S
  let U := Axis E true z
  let V := FibreGeneric (E:=E) z
  let K := FractionRing (Polynomial L)
  let a := scaledRoot (projectedRaw P) b.gen pn root
  let φ := axisFibreData (E:=E) false z nz
  have wordVal : genericFibreBase z (projectedRaw P).leadingCoeff*RetainedCompression.incl S=
      algebraMap (Polynomial L) K y := by
    rw [map_mul]
    rfl
  have kills' : ((1 ⊗ₜ[(Polynomial L)] quotientMap E z a : V)-algebraMap (Polynomial L) V y)*
      e (AdjoinRoot.mk q H)=0 := by
    rw [wordVal] at kills
    exact kills
  have mapped := congrArg g kills'
  rw [map_mul,map_sub,map_zero,G.property.1,axisGenericData_scalar,φ.property.2.1] at mapped
  change (axisToGeneric (E:=E) z (red E true z (axisScaledOrdinate P pn b.gen root))-
    axisToGeneric (E:=E) z (red E true z (axisScaledWord P z S)))*η=0 at mapped
  change axisToGeneric (E:=E) z (Ideal.Quotient.mk (axisIdeal E true z)
    (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S))*η=0
  rw [map_sub,map_sub]
  exact mapped
#print axioms actual_axis_projector
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisWord

-- merged module R6960CollisionMarkedAxisFamily
section Merged_R6960CollisionMarkedAxisFamily
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4600000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus MarkedEvaluation Polynomial
open CollisionTame Finset Module
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
open Lower6960.CollisionMarked (chart_poly_mem chartSubring)
variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]
local instance familyAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
theorem actual_axis_marked_family (p:ℕ) [CharP L p] [CharP (FractionRing (Polynomial L)) p]
    (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0)
    (large:2≤P.natDegree) (small:P.natDegree<p)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root : let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (z:L) (nz:z≠0) (S:(Polynomial L)) (mark:RetainedCompression.MarkedFiber P z S) (s:ℕ)
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:axisDiscriminant (E:=E) false=Ideal.span {δf})
    (di:axisDiscriminant (E:=E) true=Ideal.span {δi})
    [DecidableEq L]
    (gi:(Bivariate.swap δi).trailingCoeff.eval z≠0) :
    (branchProduct (Bivariate.swap δf)).map (evalRingHom z)≠0 ∧
    ∃ d:(Polynomial L), d≠0 ∧ d^2∣δf.eval (C z) ∧
      (∀ x∈d.roots,2≤((branchProduct (Bivariate.swap δf)).map (evalRingHom z)).rootMultiplicity x) ∧
      ∃ v:Fin (s+1-d.natDegree)→Axis E true z,
        LinearIndependent L v ∧
        (∀i,FibreSection (E:=E) s z (v i)) ∧
        ∀i,red E true z (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S)*v i=0 := by
  classical
  let U := Axis E true z
  let V := AxisGeneric (E:=E) z
  let ρ := axisToGeneric (E:=E) z
  obtain ⟨η,reduced,idem,nonzero,kills⟩ := actual_axis_projector p P pn large small b dim root z nz S mark
  let : IsReduced V := reduced
  have size : finrank ChartField E<p := by rw [b.finrank,dim]; exact small
  obtain ⟨gf,d,dn,dsquare,dsupport,clearF⟩ := actual_axis_finite_index (E:=E) p size z nz δf nf df
  obtain ⟨D,d0,clearI⟩ := actual_axis_infinity_index (E:=E) p size z nz δi ni di gi
  let J := Fin (s+1-d.natDegree)
  let h (i:J) : (Polynomial L) := d*Polynomial.X^i.val
  have degree (i:J) : (h i).natDegree≤s := by
    unfold h
    rw [natDegree_mul dn (pow_ne_zero _ Polynomial.X_ne_zero),natDegree_X_pow]
    have lt := i.isLt
    change i.val<s+1-d.natDegree at lt
    omega
  obtain ⟨a,am,ae⟩ := clearF η idem
  have clear_prod (i:J) : ∃ v∈chartImage E true z false,
      ρ v=ρ (polyMap E true z false (h i))*η := by
    let c := polyMap E true z false (Polynomial.X^i.val)
    refine ⟨c*a,(Lower6960.CollisionMarked.chartSubring (E:=E) false z).mul_mem
      (Lower6960.CollisionMarked.chart_poly_mem false z nz _) am,?_⟩
    rw [map_mul,ae]
    change ρ (polyMap E true z false (Polynomial.X^i.val))*_=
      ρ (polyMap E true z false (d*Polynomial.X^i.val))*η
    rw [map_mul,map_mul]
    ring
  choose v vreg vvalue using fun i:J=>marked_axis_multiple z nz η (h i) D s (degree i) d0
    (clear_prod i) (clearI η idem)
  refine ⟨gf,d,dn,dsquare,dsupport,v,?_,vreg,?_⟩
  · have units_poly (w:(Polynomial L)) (wne:w≠0) : IsUnit (ρ (polyMap E true z false w)) := by
      let : Algebra (Plane L) E := axisPlaneAlgebra false
      let R := (Polynomial L)
      let K := FractionRing R
      let W := FibreGeneric (E:=E) z
      let e := (axisGenericData (E:=E) false z nz).val
      rw [←axisGenericData_scalar (E:=E) false z nz w]
      have wu := IsUnit.mk0 (algebraMap R K w) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr wne)
      change IsUnit (e (algebraMap R W w))
      rw [IsScalarTower.algebraMap_apply R K W]
      let jW : K→+*W := Algebra.TensorProduct.includeLeftRingHom (R:=R) (A:=K) (B:=Fiber E z)
      have out : IsUnit ((e.toRingHom.comp jW) (algebraMap R K w)) := RingHom.isUnit_map (e.toRingHom.comp jW) wu
      exact out
    apply Fintype.linearIndependent_iff.mpr
    intro c zero i
    let H : (Polynomial L) := ∑ j:J,Polynomial.monomial j.val (c j)
    let f : (Polynomial L)→+*V := ρ.comp (polyMap E true z false)
    have HC (q:L) : f (C q)=ρ (algebraMap L U q) := by
      change ρ (polyMap E true z false (C q))=_
      rw [axis_polyEval,eval₂_C]
    have eq : f (d*H)*η=0 := by
      have mapped := congrArg ρ zero
      rw [map_sum,map_zero] at mapped
      unfold H
      rw [mul_sum,map_sum,Finset.sum_mul]
      apply Eq.trans _ mapped
      apply Finset.sum_congr rfl
      intro j _
      rw [←C_mul_X_pow_eq_monomial]
      have changePoly : d*(C (c j)*Polynomial.X^j.val)=C (c j)*h j := by dsimp [h]; ring
      rw [changePoly,map_mul,HC]
      change ρ (algebraMap L U (c j))*ρ (polyMap E true z false (h j))*η =
        ρ (algebraMap L U (c j)*v j)
      rw [map_mul ρ,show ρ (v j)=ρ (polyMap E true z false (h j))*η from vvalue j]
      ring
    have Hzero : H=0 := by
      by_contra Hn
      have u : IsUnit (f (d*H)) := units_poly _ (mul_ne_zero dn Hn)
      obtain ⟨u,hu⟩ := u
      have k := congrArg (fun x:V=>(↑u⁻¹:V)*x) eq
      rw [mul_zero,←mul_assoc,←hu,Units.inv_mul,one_mul] at k
      exact nonzero k
    have c0 := congrArg (fun f:(Polynomial L)=>f.coeff i.val) Hzero
    simp only [H,Polynomial.finsetSum_coeff,coeff_monomial,Finsupp.single_apply,←Fin.ext_iff,coeff_zero] at c0
    have val : (∑ j:J, if j=i then c j else 0)=c i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ ne; simp [ne]
      · simp
    exact val.symm.trans c0
  · intro i
    apply axisToGeneric_injective z nz
    rw [map_mul,map_zero,vvalue]
    calc _ = (ρ (red E true z (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S))*η)*
          ρ (polyMap E true z false (h i)) := by ring
         _ = _ := by rw [kills,zero_mul]
#print axioms actual_axis_marked_family
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisFamily

end Merged6967_R6960CollisionMarkedAxisFamily

section Merged6967_R6960CollisionMarkedPlaneOverlap
set_option Elab.async false





set_option Elab.async false

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

end Merged6967_R6960CollisionMarkedPlaneOverlap

section Merged6967_R6960MarkedZeroDegree
set_option Elab.async false



set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6960.MarkedEvaluation
open LineEuler Horner LaurentPolynomial Polynomial Module Matrix Algebra Submodule
open scoped Polynomial Matrix BigOperators Lower6960.Horner
variable {k E J:Type} [Field k] [Field E] [Algebra (RatFunc k) E] [Algebra k E] [IsScalarTower k (RatFunc k) E]
  [Fintype J] [DecidableEq J] [FiniteDimensional (RatFunc k) E] [DecidableEq (RatFunc k)]
local notation "Ord" => chartOrder (k:=k) (E:=E)

private theorem global_is_integral (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    {v:E} (f:v∈Ord false) (h:v∈Ord true) : IsIntegral k v := by
  by_contra no
  have tr:Transcendental k v:=fun alg=>no alg.isIntegral
  let G:=twist 0 (normalizedTransition bf bi)
  let N:=finrank k (H0 G)+1
  let powers (n:Fin N):E:=v^n.val
  have poly:LinearIndependent k (fun n:Fin N=>(Polynomial.X:(Polynomial k))^n.val) := by
    have t:LinearIndependent k (fun a:ℕ=>(Polynomial.X:(Polynomial k))^a) :=by
      simpa only [Polynomial.coe_basisMonomials,Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials k).linearIndependent
    exact t.comp Fin.val Fin.val_injective
  have inds : LinearIndependent k powers := by
    have I:=poly.map' (aeval v).toLinearMap (LinearMap.ker_eq_bot_of_injective (transcendental_iff_injective.mp tr))
    simpa only [Function.comp_def,AlgHom.toLinearMap_apply,map_pow,aeval_X,powers] using I
  have count:=span_le_global bf bi 0 powers (by
    intro j
    refine ⟨?_,?_⟩
    · letI : Algebra (Polynomial k) E:=((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra
      exact (Ord false).pow_mem f _
    · letI : Algebra (Polynomial k) E:=((algebraMap (Laurent k) E).comp (chartEmbedding true).toRingHom).toAlgebra
      rw [neg_zero,zpow_zero,one_mul];exact (Ord true).pow_mem h _)
  rw [finrank_span_eq_card inds,Fintype.card_fin] at count
  exact Nat.not_succ_le_self _ count

private theorem zero_coeff (f:(Polynomial k)) : f.toLaurent.coeff (0:ℤ)=f.eval 0 := by
  rw [←Polynomial.coeff_zero_eq_eval_zero,LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ 0

/-- When the normalized line has determinant degree zero, its degree-e
function field has e independent functions algebraic over the constants. -/
theorem constant_frame (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (deg:(normalizedTransition bf bi).det.degree=(0:WithBot ℤ)) :
    ∃ w:J→E,LinearIndependent (RatFunc k) w ∧ ∀j,IsIntegral k (w j) := by
  classical
  let G:=normalizedTransition bf bi
  obtain ⟨fd,_,d,ed,chi⟩:=normalized_euler bf bi
  have dz:d=0:=WithBot.coe_injective (ed.symm.trans deg)
  have inj:Function.Injective (crossingEval G) := by
    apply LinearMap.ker_eq_bot.mp;apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    let ker:(crossingEval G).ker:=⟨u,hu⟩
    let eq:=crossingKernel G
    have z:=congrArg eq (negative_section_zero bf bi (eq.symm ker))
    rw [LinearEquiv.apply_symm_apply,map_zero] at z;exact congrArg Subtype.val z
  have bound:=LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_pi] at bound
  have size:finrank k (H0 G)=Fintype.card J := by
    change (finrank k (H0 G):ℤ)-(finrank k (H1 G):ℤ)=_ at chi;omega
  let B:Basis J k (H0 G):=(Module.finBasisOfFinrankEq k _ size).reindex (Fintype.equivFin J).symm
  let u (i:J):Ord false:=⟨decode bf (B i).val,(decode_finite bf _).mp (B i).property.1⟩
  let M:=chartMatrix bf u
  have coord (i j:J) : (M i j).toLaurent=(B j).val i := by
    have eq: chartOrderMap false (u j)=(localBasis false bf).equivFun.symm (B j).val:=Subtype.ext rfl
    rw [show (M i j).toLaurent=(localBasis false bf).equivFun (chartOrderMap false (u j)) i from
      (localBasis_repr false bf (u j) i).symm,eq,LinearEquiv.apply_symm_apply]
  have cmp:(M.map (evalRingHom 0)).col=(crossingEval G)∘B := by
    funext i j;change (M j i).eval 0=((B i).val j).coeff 0
    rw [←zero_coeff,coord]
  have indep:LinearIndependent k (M.map (evalRingHom 0)).col :=
    cmp ▸ B.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective inj)
  have mn:M.det≠0 := by
    have n:=((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp indep)).ne_zero
    intro z;apply n;rw [←show (evalRingHom (0:k)) M.det=(M.map (evalRingHom 0)).det from RingHom.map_det _ _,z,map_zero]
  let jpoly: (Polynomial k)→+*E:=(algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom
  letI := jpoly.toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) E:=IsScalarTower.of_algebraMap_eq (fun r=>
    congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun Horner.rationalLaurent_finite r))
  have iu:LinearIndependent (Polynomial k) u := by
    apply Fintype.linearIndependent_iff.mpr
    intro a h i
    have eq:M*ᵥa=0 := by
      funext t
      have st:=congrArg (fun x:Ord false=>bf.repr x t) h
      simpa only [map_sum,map_smul,map_zero,Finsupp.finsetSum_apply,Finsupp.smul_apply,
        smul_eq_mul,Finsupp.zero_apply,Matrix.mulVec,dotProduct,M,chartMatrix,mul_comm,Pi.zero_apply] using st
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero mn eq) i
  let w (j:J):E:=(u j:E)
  have iw:LinearIndependent (Polynomial k) w:=iu.map' (Ord false).val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  refine ⟨w,(LinearIndependent.iff_fractionRing (Polynomial k) (RatFunc k)).mp iw,fun i=>?_⟩
  have g0:twist 0 G=G:=by simp [twist]
  have hi: (B i).val∈transitionLattice (twist 0 G):=g0.symm ▸ (B i).property.2
  apply global_is_integral bf bi (u i).property
  simpa only [neg_zero,zpow_zero,one_mul] using (decode_infinity bf bi 0 _).mp hi

#print axioms constant_frame
end Lower6960.MarkedEvaluation

end
end Merged6967_R6960MarkedZeroDegree
