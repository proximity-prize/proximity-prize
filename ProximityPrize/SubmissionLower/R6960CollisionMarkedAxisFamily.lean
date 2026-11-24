import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisMultiples
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisWord
set_option synthInstance.maxHeartbeats 200000

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

/-- The original marked fibre has exactly the needed family of regular
polynomial multiples of its nonzero projector. The only degree loss is
the affine determinant, with its actual collision support. -/
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
      have out : IsUnit (e (jW (algebraMap R K w))) := (wu.map jW).map e
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
