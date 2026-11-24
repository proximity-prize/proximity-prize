import ProximityPrize.SubmissionLower.R6961MarkedAllLabels
import ProximityPrize.SubmissionLower.R6961MarkedVerticalProfile
import ProximityPrize.SubmissionLower.R6961CollisionMarkedHorizontalHorner
import ProximityPrize.SubmissionLower.R6961CollisionMarkedRootTransport
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
  have pn:projectedRaw P≠0:=by intro zero;have eq:=projectedRaw_degree P;rw [zero,natDegree_zero] at eq;omega
  have bound:=all_labels (E:=E) K1.p P pn (by omega) (degP ▸ hiP)
    (f.degreeOf parameter) seed b dim (projected_root_of_seed P b.gen root) s t positive tame
    (degP.symm ▸ tariff) (by simpa only [Nat.sub_add_cancel positive] using surface (s-1))
    δf δi nf ni df di xc zc tail S wt mark vrank
  rwa [show S.card=T.card from card_image_of_injective _ (RetainedCompression.scalar_injective M),degP] at bound

end Lower6961.MarkedEvaluation
