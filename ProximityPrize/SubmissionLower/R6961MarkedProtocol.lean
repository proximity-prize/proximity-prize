import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisFamily
import ProximityPrize.SubmissionLower.R6961MonicChartProbes
import ProximityPrize.SubmissionLower.R6961CollisionMarkedGenericMeasure
import ProximityPrize.SubmissionLower.R6961MarkedVerticalProfile
import ProximityPrize.SubmissionLower.R6961MarkedAllLabels

set_option Elab.async false

-- merged module R6961CollisionMarkedRootTransport
section Merged_R6961CollisionMarkedRootTransport

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (Scalar ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass MonicChartProbes Polynomial
open scoped Polynomial Lower6960.MonicChart Lower6961.MonicChart
open Lower6961.MonicChartProbes (planeMap_finite)

variable {E:Type} [Field E] [Algebra ChartField E]

/-- The root used in the actual bounded surface theorem is the root of
the same ordinate equation in the scalar-outside plane model. -/
theorem projected_root_of_seed (P:CurvatureSquares.Ordinate) (α:E)
    (root : aeval α ((RetainedLinear.toSeed P).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    let : Algebra (Plane L) E := axisPlaneAlgebra false
    aeval α (projectedRaw P)=0 := by
  let A := Plane L
  let : Algebra A E := axisPlaneAlgebra false
  let i := Polynomial.mapRingHom (algebraMap (Polynomial L) Scalar)
  let j := algebraMap (Polynomial Scalar) ChartField
  let k := algebraMap ChartField E
  have co : (algebraMap A E).comp (Bivariate.swap (R:=L)).toRingHom=
      (k.comp j).comp i := by
    apply RingHom.ext
    intro p
    change k ((oriented true false (Bivariate.swap p)):ChartField)=k (j (i p))
    have x : ((oriented true false (Bivariate.swap p)):ChartField)=
        planeMap (false,false) p := by
      change planeMap (false,false) (Bivariate.swap (Bivariate.swap p))=_
      rw [Bivariate.swap_swap_apply]
    rw [x,Lower6961.MonicChartProbes.planeMap_finite]
    rfl
  change (P.map Bivariate.swap.toRingHom).eval₂ (algebraMap A E) α=0
  rw [eval₂_map,co]
  change ((P.map i).map j).eval₂ k α=0 at root
  rw [eval₂_map,eval₂_map] at root
  exact root

#print axioms projected_root_of_seed
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedRootTransport

-- merged module R6961CollisionMarkedHorizontalHorner
section Merged_R6961CollisionMarkedHorizontalHorner
set_option synthInstance.maxHeartbeats 200000

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (Scalar ChartField)
open RetainedCompression (Curve ordinate parameter view view_y view_z)
open RetainedSurfaceClass (Crossing chartImage transition)
open Lower6961.MarkedEvaluation (swapBase)
open Polynomial Module Lower6960.LineEuler
open scoped Polynomial Lower6960.MonicChart Lower6961.MonicChart Lower6961.RetainedSurfaceClass
open Lower6961.MarkedEvaluation (swap_plane)
open Lower6961.MonicChartProbes (planeMap_finite)
open Lower6961.MonicChart (root_finrank)

variable {E : Type} [Field E] [original : Algebra ChartField E]

@[instance_reducible] private def horizontalFieldAlgebra : Algebra ChartField E :=
  ((algebraMap ChartField E).comp swapBase.toRingHom).toAlgebra

private theorem horizontalSeedRoot (P : CurvatureSquares.Ordinate) (y : E)
    (root : aeval y ((RetainedLinear.toSeed P).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    let : Algebra ChartField E := horizontalFieldAlgebra (E:=E)
    aeval y ((RetainedLinear.toSeed (projectedRaw P)).map (algebraMap (Polynomial Scalar) ChartField))=0 := by
  let k := algebraMap ChartField E
  let j := algebraMap (Polynomial Scalar) ChartField
  let c := Polynomial.mapRingHom (algebraMap (Polynomial L) Scalar)
  let a := horizontalFieldAlgebra (E:=E)
  let : Algebra ChartField E := a
  have coordinate : (((k.comp swapBase.toRingHom).comp j).comp c).comp Bivariate.swap.toRingHom =
      (k.comp j).comp c := by
    apply RingHom.ext
    intro p
    have pmap (q : Lower6960.PlaneConstants.Plane L) :
        MonicChartProbes.planeMap (false,false) q=j (c q) :=
      DFunLike.congr_fun Lower6961.MonicChartProbes.planeMap_finite q
    change k (swapBase (j (c (Bivariate.swap p))))=k (j (c p))
    rw [←pmap,Lower6961.MarkedEvaluation.swap_plane,Bivariate.swap_swap_apply,pmap]
  change (((P.map Bivariate.swap.toRingHom).map c).map j).eval₂ (k.comp swapBase.toRingHom) y=0
  rw [eval₂_map,eval₂_map,eval₂_map,coordinate]
  change ((P.map c).map j).eval₂ k y=0 at root
  rwa [eval₂_map,eval₂_map] at root

private theorem horizontalMinpolyDegree (b : PowerBasis ChartField E) :
    let y := b.gen
    let n := b.dim
    let : Algebra ChartField E := horizontalFieldAlgebra (E:=E)
    (minpoly ChartField y).natDegree=n := by
  let y := b.gen
  let n := b.dim
  have oldInt : Algebra.IsIntegral ChartField E := by
    let : FiniteDimensional ChartField E := b.finite
    infer_instance
  let mp := minpoly ChartField y
  have md : mp.natDegree=n := b.natDegree_minpoly
  let a := horizontalFieldAlgebra (E:=E)
  let : Algebra ChartField E := a
  have co : a.algebraMap.comp swapBase.symm.toRingHom =
      (RingEquiv.refl E).toRingHom.comp original.algebraMap := by
    apply RingHom.ext
    intro x
    change original.algebraMap (swapBase (swapBase.symm x))=original.algebraMap x
    rw [swapBase.apply_symm_apply]
  have eq : mp.map swapBase.symm.toRingHom=minpoly ChartField y :=
    @minpoly.map_eq_of_equiv_equiv ChartField _ ChartField E E _ _ _ _ _ _
      original a oldInt swapBase.symm (RingEquiv.refl E) co y
  change (minpoly ChartField y).natDegree=n
  rw [←eq]
  exact (natDegree_map_eq_of_injective (f:=swapBase.symm.toRingHom) swapBase.symm.injective mp).trans md

private theorem horner_of_degree
    (Q : (Polynomial (Polynomial Scalar))) (v : ℕ) (pos : 0<Q.natDegree)
    (width : ∀ i, (Q.coeff i).natDegree≤v) (y : E)
    (root : aeval y (Q.map (algebraMap (Polynomial Scalar) ChartField))=0)
    (mindeg : (minpoly ChartField y).natDegree=Q.natDegree) {n : ℕ}
    (size : n=Q.natDegree)
    (af : let : Algebra (Laurent Scalar) E := Lower6960.Horner.rationalLaurentAlgebra
          Basis (Fin n) (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) false))
    (ai : let : Algebra (Laurent Scalar) E := Lower6960.Horner.rationalLaurentAlgebra
          Basis (Fin n) (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) true))
    (t : ℕ)
    (det : let : Algebra (Laurent Scalar) E := Lower6960.Horner.rationalLaurentAlgebra
           (normalizedTransition af ai).det.degree=((-(t:ℤ):ℤ):WithBot ℤ)) :
    t≤(Q.natDegree-1)*v := by
  subst n
  let : Algebra (Laurent Scalar) E := Lower6960.Horner.rationalLaurentAlgebra
  obtain ⟨d,dd,cap⟩ := Lower6960.Horner.actual_horner_budget Q v pos width y root mindeg af ai
  rw [det] at dd
  have de : d=-(t:ℤ) := (WithBot.coe_injective dd).symm
  rw [de,neg_neg,←Int.natCast_mul] at cap
  exact_mod_cast cap

local instance horizontalCrossRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (RetainedSurfaceClass.Tor E) inferInstance
    (RetainedSurfaceClass.axisIdeal E false x⊔RetainedSurfaceClass.axisIdeal E true z)

/-- The horizontal determinant deficit measured on the selected original
line is bounded by the parameter degree of the same ordinate equation. -/
theorem actual_horizontal_horner
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<K1.p)
    (b : PowerBasis ChartField E)
    (root : aeval b.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (nx : x≠0) (nz : z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p : ℕ) [CharP L p] (small : finrank L (Crossing E x z)<p)
    {m : ℕ} (xf : Basis (Fin m) (Polynomial L) (chartImage E false x false))
    (xi : Basis (Fin m) (Polynomial L) (chartImage E false x true))
    (t : ℕ) (dt : (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ)) :
    t≤(f.degreeOf ordinate-1)*f.degreeOf parameter := by
  let : FiniteDimensional ChartField E := b.finite
  let : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi b root
  let : Algebra (Polynomial Scalar) E := ((algebraMap ChartField E).comp (algebraMap (Polynomial Scalar) ChartField)).toAlgebra
  let : IsScalarTower (Polynomial Scalar) ChartField E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial Scalar)) (S:=ChartField) (A:=E) fun _=>rfl
  have root' : aeval b.gen (RetainedLinear.toSeed (view f))=0 := by
    rw [aeval_map_algebraMap] at root
    exact root
  have rank := Lower6961.MonicChart.root_finrank f ir lo b root'
  have dim : b.dim=f.degreeOf ordinate := b.finrank.symm.trans rank
  let Q := RetainedLinear.toSeed (projectedRaw (view f))
  have deg : Q.natDegree=f.degreeOf ordinate :=
    (RetainedLinear.toSeed_degree _).trans ((projectedRaw_degree _).trans (view_y f))
  have pos : 0<Q.natDegree := by rw [deg]; omega
  have width (i : ℕ) : (Q.coeff i).natDegree≤f.degreeOf parameter := by
    change ((((projectedRaw (view f)).map (mapRingHom (RetainedLinear.incl L))).coeff i)).natDegree≤_
    rw [coeff_map]
    change (((projectedRaw (view f)).coeff i).map (RetainedLinear.incl L)).natDegree≤_
    apply natDegree_map_le.trans
    have h := (CurvatureSquares.coeff_caps (view f) i).2
    rw [view_z] at h
    change (Bivariate.swap ((view f).coeff i)).natDegree≤f.degreeOf parameter at h
    rw [projectedRaw,coeff_map]
    change (Bivariate.swap ((view f).coeff i)).natDegree≤f.degreeOf parameter
    exact h
  have fr := generic_measure_eq_native (E:=E) false x z nx nz p small xf xi t dt
  rw [generic_algebra_horizontal] at fr
  have hroot := horizontalSeedRoot (view f) b.gen root
  let y := b.gen
  have md := horizontalMinpolyDegree b
  let : Algebra ChartField E := horizontalFieldAlgebra (E:=E)
  let : Algebra (Laurent Scalar) E := Lower6960.Horner.rationalLaurentAlgebra
  obtain ⟨af,ai,da⟩ := fr
  have mindeg : (minpoly ChartField y).natDegree=Q.natDegree := md.trans (dim.trans deg.symm)
  have cap := horner_of_degree Q (f.degreeOf parameter) pos width y
    hroot mindeg (rank.trans deg.symm) af ai t da
  rwa [deg] at cap

#print axioms actual_horizontal_horner
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedHorizontalHorner

-- merged module R6961MarkedProtocol
section Merged_R6961MarkedProtocol
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open Lower6961.MonicChart (Scalar ChartField)
open RetainedCompression (Curve ordinate parameter view view_y height heightCap MarkedBand scalar MarkedFiber)
open RetainedTwistedRestriction RetainedSurfaceClass Lower6960.CollisionMarked Lower6961.CollisionMarked Polynomial Module Algebra Finset
open scoped Polynomial Lower6960.MarkedEvaluation Lower6961.MarkedEvaluation Lower6961.RetainedSurfaceClass
local instance protocolScalarDec : DecidableEq Scalar := Classical.decEq _
local instance protocolFieldDec : DecidableEq ChartField := Classical.decEq _
local instance protocolNodeRing {E:Type} [Field E] [Algebra ChartField E] (x z:L):CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

theorem nonlinear_price (B : MarkedBand) : NonlinearPrice B := by
  classical
  intro u deleted M Γ F T sub words f ir lo hi seed bounded nonlin marks
  let P:=view f
  let Q:(Polynomial ChartField):=(RetainedLinear.toSeed P).map (algebraMap (Polynomial Scalar) ChartField)
  have pi:Irreducible P:=(MulEquiv.irreducible_iff view).mpr ir
  have degP:P.natDegree=f.degreeOf ordinate:=view_y f
  have seedI:=RetainedLinear.toSeed_irreducible pi (by omega : 0<P.natDegree)
  have degS: (RetainedLinear.toSeed P).natDegree=P.natDegree:=RetainedLinear.toSeed_degree P
  have qi:Irreducible Q := (seedI.isPrimitive (by omega)).irreducible_iff_irreducible_map_fraction_map.mp seedI
  letI : Fact (Irreducible Q):=⟨qi⟩
  let E:=AdjoinRoot Q
  let b:PowerBasis ChartField E:=AdjoinRoot.powerBasis qi.ne_zero
  have root:aeval b.gen Q=0 := (AdjoinRoot.aeval_eq Q).trans (AdjoinRoot.mk_self)
  have dim:b.dim=P.natDegree:=(natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) ChartField)
    (RetainedLinear.toSeed P)).trans degS
  have : FiniteDimensional ChartField E:=b.finite
  have hiP : f.degreeOf ordinate < K1.p := hi.trans B.small_E
  have : Algebra.IsSeparable ChartField E:=MonicChartProbes.actual_separable f ir lo hiP b root
  letI : CharP Scalar K1.p:=charP_of_injective_ringHom inner.injective K1.p
  obtain ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B_bas⟩,reduced,surface⟩:=
    actual_all_twists E B f ir lo hi bounded b root
  have : FiniteDimensional L (Crossing E x z):=Module.Finite.of_basis B_bas
  have small:finrank L (Crossing E x z)<K1.p := by
    rw [finrank_eq_card_basis B_bas,Fintype.card_fin]; exact hiP
  obtain ⟨positive,tame,vrank⟩:=vertical_profile B f ir lo hi bounded nonlin b dim root x z nx nz small zf zi s ds
  have tariff:=actual_horizontal_horner f ir lo hiP b root x z nx nz K1.p small xf xi t dt
  obtain ⟨δf,δi,nf,ni,df,di,xc,zc,tail⟩:=
    actual_measured_discriminants x z nx nz K1.p small xf xi zf zi s t ds dt
  let S:=T.image (scalar M)
  let wt (z:L):(Polynomial L):=liftPoly (F.scalar (Function.invFun (scalar M) z))
  have mark (z:L) (mem:z∈S):MarkedFiber P z (wt z) := by
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp mem
    change MarkedFiber P _ (liftPoly (F.scalar (Function.invFun (scalar M) (scalar M a))))
    rw [Function.leftInverse_invFun (RetainedCompression.scalar_injective M)];exact marks a ha
  have pn:Lower6961.CollisionMarked.projectedRaw P≠0:=by intro zero;have eq:=Lower6961.CollisionMarked.projectedRaw_degree P;rw [zero,natDegree_zero] at eq;omega
  have bound:=all_labels (E:=E) K1.p P pn (by omega) (degP ▸ hiP)
    (f.degreeOf parameter) seed b dim (projected_root_of_seed P b.gen root) s t positive tame
    (degP.symm ▸ tariff) (by simpa only [Nat.sub_add_cancel positive] using surface (s-1))
    δf δi nf ni df di xc zc tail S wt mark vrank
  rwa [show S.card=T.card from card_image_of_injective _ (RetainedCompression.scalar_injective M),degP] at bound

end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedProtocol
