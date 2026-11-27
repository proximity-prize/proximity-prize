import ProximityPrize.SubmissionLower.R6960CollisionMarkedCommonAxis
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960MarkedTranslatedEquation
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisMultiples
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex

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
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisFamily
