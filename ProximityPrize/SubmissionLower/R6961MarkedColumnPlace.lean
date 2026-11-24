import ProximityPrize.SubmissionLower.R6961MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6961MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6961MarkedFunctionSpace
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open MonicFourChartDescent ChartOverlapTests RetainedRestrictionTorus RetainedSurfaceClass RetainedTwistedRestriction
open Polynomial Finset Algebra
open scoped Polynomial BigOperators Lower6961.RetainedSurfaceClass Lower6961.MarkedEvaluation
open scoped Lower6960.MonicChart Lower6961.MonicChart
local instance : DecidableEq Scalar := Classical.decEq _
local instance : DecidableEq ChartField := Classical.decEq _
local instance (priority := 2200) : Algebra (Polynomial Scalar) ChartField :=
  inferInstanceAs (Algebra (Polynomial Scalar) (RatFunc Scalar))
local instance (priority := 2200) : SMul (Polynomial Scalar) ChartField :=
  (inferInstance : Algebra (Polynomial Scalar) ChartField).toSMul
open Lower6961.MarkedEvaluation (leading_unit integral_infty)
variable {E Ω:Type} [Field E] [Field Ω] [Algebra ChartField E] [Algebra ChartField Ω]
variable [Algebra (Polynomial Scalar) Ω] [IsScalarTower (Polynomial Scalar) ChartField Ω]
local notation "ι" => algebraMap ChartField Ω
local notation "poly" => algebraMap (Polynomial Scalar) ChartField
local notation "jo" => algebraMap (Polynomial Scalar) Ω
variable (c:L) (ev:E→+*Ω) (base:∀a,ev (algebraMap ChartField E a)=algebraMap ChartField Ω (rowBase c a))

private theorem row_cut (z:L) : rowBase c (divisor true z)=poly (Polynomial.X-C (inner z)) := by
  change rowBase c (scalarCoordinate-constants z)=_
  rw [map_sub,row_parameter,row_constant,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C];rfl

private theorem pole_image (T:Finset L) :
    polePolynomial (T.image inner)=∏z∈T,(Polynomial.X-C (inner z)) := by
  classical
  exact Finset.prod_image (f:=fun z:Scalar=>Polynomial.X-C z) (fun _ _ _ _ h=>inner.injective h)

include base in
theorem mapped_denom (T:Finset L) (b:Bool) :
    ev (chartDenom E T (false,b))=jo (polePolynomial (T.image inner))/
      (if b then ι RatFunc.X else 1)^T.card := by
  classical
  rw [chartDenom,map_prod,pole_image,map_prod,←Finset.prod_const,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl;intro z _
  change ev (algebraMap ChartField E (zcut (false,b) z:ChartField))=_
  rw [base,zcut_value,map_div₀,map_div₀,row_cut,←IsScalarTower.algebraMap_apply]
  cases b <;> simp [localFrame,axisBit,coordinate,row_parameter]

include base in
theorem mapped_finite {i:ℕ} {T:Finset L} {v:E} (reg:controlled E i T v) :
    IsIntegral (Polynomial Scalar) (jo (polePolynomial (T.image inner))*ev v) := by
  have h:IsIntegral (baseChart (false,false)) (chartDenom E T (false,false)*v) := by
    simpa [Regular,fr,localFrame,axisBit] using reg (false,false)
  have v':=integral_section c _ ev base (IsFractionRing.injective (Polynomial Scalar) ChartField) (fun _ h=>finite_base c h) h
  simpa only [map_mul,mapped_denom c ev base,Bool.false_eq_true,ite_false,one_pow,div_one] using v'

include base in
theorem mapped_infty [FiniteDimensional ChartField Ω]
    [Algebra (Lower6960.SheetNorm.Infinity Scalar) Ω] [IsScalarTower (Lower6960.SheetNorm.Infinity Scalar) ChartField Ω]
    {i:ℕ} {T:Finset L} {v:E} (reg:controlled E i T v) :
    IsIntegral (Lower6960.SheetNorm.Infinity Scalar) (ev v) := by
  classical
  let D:=polePolynomial (T.image inner)
  have d:D.natDegree=T.card := (polePolynomial_degree _).trans (card_image_of_injective _ inner.injective)
  have h:IsIntegral (baseChart (false,true)) (chartDenom E T (false,true)*v) := by
    simpa [Regular,fr,localFrame,axisBit] using reg (false,true)
  have v':=integral_section c _ ev base (show Function.Injective (algebraMap (Lower6960.SheetNorm.Infinity Scalar) ChartField)
    from Subtype.val_injective) (fun _ h=>infinity_base c h) h
  rw [map_mul,mapped_denom c ev base,if_pos rfl] at v'
  have u:=Lower6961.MarkedEvaluation.leading_unit (K:=Scalar) D (polePolynomial_monic _).ne_zero
  have inv:=Lower6961.MarkedEvaluation.integral_infty (E:=Ω) u.2
  rw [map_inv₀,map_div₀,←IsScalarTower.algebraMap_apply,map_pow,d] at inv
  have nz:jo D/(ι RatFunc.X)^T.card≠0 := by
    refine div_ne_zero ?_ (pow_ne_zero _ ((map_ne_zero_iff _ (algebraMap ChartField Ω).injective).mpr RatFunc.X_ne_zero))
    rw [IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω]
    exact (map_ne_zero_iff _ (algebraMap ChartField Ω).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (polePolynomial_monic _).ne_zero)
  change IsIntegral (Lower6960.SheetNorm.Infinity Scalar) ((jo D/(ι RatFunc.X)^T.card)*ev v) at v'
  have t:=inv.mul v';rwa [←mul_assoc,inv_mul_cancel₀ nz,one_mul] at t

private def boundaryPolynomial (c:L) : (Polynomial Scalar) := C (algebraMap (Polynomial L) Scalar Polynomial.X+inner c)*Polynomial.X
private theorem row_boundary : rowBase c (boundary (false,false) (true,true))=poly (boundaryPolynomial c) := by
  change rowBase c (RatFunc.X*scalarCoordinate)=_
  rw [map_mul,row_abscissa,row_parameter,boundaryPolynomial,map_mul,RatFunc.algebraMap_X,RatFunc.algebraMap_C,map_add]
  rfl

include base in
theorem torus_mem {z:Scalar} (P:MarkPlace Scalar Ω z) (nz:z≠0) (v:Tor E) : ev (v:E)∈P.V := by
  classical
  obtain ⟨n,regular⟩:=clear_torus (false,false) (v:E) v.property
  have fd:=integral_section c _ ev base (IsFractionRing.injective (Polynomial Scalar) ChartField) (fun _ h=>finite_base c h) regular
  let p:=boundaryPolynomial c
  have hn: (algebraMap (Polynomial L) Scalar Polynomial.X+inner c)≠0 := by
    change algebraMap (Polynomial L) Scalar Polynomial.X+algebraMap (Polynomial L) Scalar (C c)≠0
    rw [←map_add];exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_add_C_ne_zero _)
  have unit:IsUnit (P.lift p) := P.lift_unit (by simpa [p,boundaryPolynomial] using mul_ne_zero hn nz)
  have scaled:=P.integral_mem fd
  rw [map_mul,map_pow,base,show opposite (false,false)=(true,true) from rfl,row_boundary,←P.value] at scaled
  obtain ⟨u,hu⟩:=unit
  let undo: P.V:=↑(u⁻¹)^n
  have val:((undo:P.V):Ω)*(P.lift p:Ω)^n=1 := by
    rw [←hu];change ((↑(u⁻¹):P.V):Ω)^n*((↑u:P.V):Ω)^n=1
    have iu : ((↑(u⁻¹):P.V):Ω)*((↑u:P.V):Ω)=1 := congrArg (fun w:P.V=>(w:Ω)) u.inv_mul
    rw [←mul_pow,iu,one_pow]
  change (P.lift p:Ω)^n * ev (v:E)∈P.V at scaled
  have m:=P.V.toSubring.mul_mem undo.property scaled
  rw [←mul_assoc,val,one_mul] at m
  exact m

def mapped_torus (c:L) (ev:E→+*Ω) (base:∀a,ev (algebraMap ChartField E a)=ι (rowBase c a))
    (z:Scalar) (P:MarkPlace Scalar Ω z) (nz:z≠0) : Tor E→+*P.V :=
  (ev.comp (Tor E).val.toRingHom).codRestrict P.V.toSubring (torus_mem c ev base P nz)

include base in
theorem local_cut (z:L) (P:MarkPlace Scalar Ω (inner z)) (nz:inner z≠0) :
    mapped_torus c ev base _ P nz (cut E true z)=P.pi := by
  apply Subtype.ext
  change ev (algebraMap ChartField E (divisor true z))=(P.lift (Polynomial.X-C (inner z)):Ω)
  rw [base,row_cut,P.value]

include base in
theorem local_annihilation (z:L) (P:MarkPlace Scalar Ω (inner z)) (nz:inner z≠0)
    (u o w:Tor E) (killed:cut E true z∣(o-w)*u) :
    P.pi∣(mapped_torus c ev base _ P nz o-mapped_torus c ev base _ P nz w)*mapped_torus c ev base _ P nz u := by
  have h:=map_dvd (mapped_torus c ev base _ P nz) killed
  rwa [local_cut,map_mul,map_sub] at h

#print axioms mapped_finite
#print axioms mapped_infty
#print axioms mapped_torus
end Lower6961.MarkedEvaluation
