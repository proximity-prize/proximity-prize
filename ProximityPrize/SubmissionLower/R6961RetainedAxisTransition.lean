import ProximityPrize.SubmissionLower.R6961RetainedAxisFree

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections RetainedRestrictionTorus ChartOverlapTests
open Module Submodule Algebra Polynomial Lower6960.LineEuler LaurentPolynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
variable (E : Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def torVar (j b:Bool) : Tor E := ⟨ι (chartCoordinate b (coordinate j)),
  isIntegral_algebraMap (x:=(⟨_,torus_coordinate j b⟩:torus))⟩
def varUnit (j:Bool) : (Tor E)ˣ := ⟨torVar E j false,torVar E j true,by
  apply Subtype.ext; change ι (coordinate j)*ι ((coordinate j)⁻¹)=1
  rw [←map_mul,mul_inv_cancel₀ (coord_ne j),map_one],by
  apply Subtype.ext; change ι ((coordinate j)⁻¹)*ι (coordinate j)=1
  rw [←map_mul,inv_mul_cancel₀ (coord_ne j),map_one]⟩

def axisLaurent (j:Bool) (c:L) : Laurent L→+*Axis E j c :=
  (Ideal.Quotient.mk _).comp (LaurentPolynomial.eval₂ (algebraMap L (Tor E)) (varUnit E (!j)))
scoped instance axisAlgebra (j:Bool) (c:L) : Algebra (Laurent L) (Axis E j c) :=
  @RingHom.toAlgebra (Laurent L) (Axis E j c) _ (Ideal.Quotient.commSemiring (axisIdeal E j c)) (axisLaurent E j c)
scoped instance chartModule (j:Bool) (c:L) (b:Bool) : Module (Polynomial L) (chartImage E j c b) :=
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  (polyImage E j c b).module

theorem signed_chart (j:Bool) (c:L) (b:Bool) :
    (axisLaurent E j c).comp (chartEmbedding b).toRingHom=polyMap E j c b := by
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  apply Polynomial.ringHom_ext
  · intro r
    change π (LaurentPolynomial.eval₂ _ _ (chartEmbedding b (Polynomial.C r)))=π (along E j b (Polynomial.C r))
    have co : chartEmbedding b (Polynomial.C r)=LaurentPolynomial.C r := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply]
    have eq : along E j b (Polynomial.C r)=algebraMap L (Tor E) r := eval₂_C _ _
    rw [co,LaurentPolynomial.eval₂_C,eq]
  · have v : chartEmbedding b (Polynomial.X : (Polynomial L))=T (if b then (-1:ℤ) else 1) := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply]
    change π (LaurentPolynomial.eval₂ _ _ (chartEmbedding b Polynomial.X))=π (along E j b Polynomial.X)
    rw [v,LaurentPolynomial.eval₂_T]
    have alongX:along E j b Polynomial.X=torVar E (!j) b := eval₂_X _ _
    rw [alongX]
    cases b <;> simp [varUnit]

theorem laurent_scalar_tower (j:Bool) (c:L) : IsScalarTower L (Laurent L) (Axis E j c) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply]
  change algebraMap L (Axis E j c) r=axisLaurent E j c (LaurentPolynomial.C r)
  simp [axisLaurent]

def nativeMap (j:Bool) (c:L) (b:Bool) : ChartMap (k:=L) b (chartImage E j c b) (Axis E j c) :=
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (chartEmbedding (k:=L) b).toRingHom
  { toFun := fun u=>u.val
    map_add' := fun _ _=>rfl
    map_smul' := fun p u=>by
      change polyMap E j c b p*u.val=axisLaurent E j c (chartEmbedding b p)*u.val
      exact congrArg (·*u.val) (DFunLike.congr_fun (signed_chart E j c b) p).symm }

theorem fixed_value (j:Bool) (c:L) : red E j c (torVar E j false)=algebraMap L (Axis E j c) c := by
  apply Ideal.Quotient.eq.mpr
  have eq : torVar E j false-algebraMap L (Tor E) c=cut E j c := by
    apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
  rw [eq]; exact Ideal.subset_span (Set.mem_singleton _)

/-- Inverting the running coordinate of either actual line chart gives its entire
torus fibre. The transverse coordinate specializes to a nonzero scalar. -/
theorem native_localization (j:Bool) (c:L) (nc:c≠0) (b:Bool) : IsChartLocalization b (nativeMap E j c b) := by
  apply isChartLocalization_of_clearing b _ (fun _ _ h=>Subtype.ext h)
  intro v
  obtain ⟨u,rfl⟩:=Ideal.Quotient.mk_surjective v
  let s:=reference j b
  obtain ⟨n,h⟩:=clear_torus s (u:E) u.property
  let V:=torVar E (!j) b
  let W:=torVar E j false
  have bw : boundary s (opposite s)=chartCoordinate b (coordinate (!j))*coordinate j := by
    cases j <;> cases b <;> simp [s,reference,boundary,opposite,coordinate,chartCoordinate,mul_comm]
  let y:Tor E:=(V*W)^n*u
  have yi : IsIntegral (baseChart s) (y:E) := by
    rw [bw,map_mul] at h
    exact h
  let w : chartImage E j c b := ⟨red E j c y,⟨y,yi,rfl⟩⟩
  refine ⟨n, (c⁻¹^n) • w,?_⟩
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  change (axisLaurent E j c ((chartEmbedding b Polynomial.X)^n))*π u=algebraMap L (Axis E j c) (c⁻¹^n)*π y
  have xe : axisLaurent E j c (chartEmbedding b Polynomial.X)=π V := by
    exact (DFunLike.congr_fun (signed_chart E j c b) Polynomial.X).trans
      (congrArg π (show along E j b Polynomial.X=V from eval₂_X (algebraMap L (Tor E)) V))
  have we : π W=algebraMap L (Axis E j c) c := fixed_value E j c
  rw [map_pow,xe,show π y= (π V*π W)^n*π u by simp [y,π],we,
    mul_pow (π V) ((algebraMap L (Axis E j c)) c) n,map_pow]
  -- The residue ring need not be a field, so cancel using its scalar action.
  have cancel : (algebraMap L (Axis E j c) c⁻¹)^n * (algebraMap L (Axis E j c) c)^n=1 := by
    have scalar : c⁻¹^n*c^n=1 := by rw [←mul_pow,inv_mul_cancel₀ nc,one_pow]
    simpa only [map_mul,map_pow,map_one] using congrArg (algebraMap L (Axis E j c)) scalar
  calc _ = 1*((π V)^n*π u) := (one_mul _).symm
       _ = _ := by rw [←cancel]; ring

#print axioms native_localization
end Lower6961.RetainedSurfaceClass
