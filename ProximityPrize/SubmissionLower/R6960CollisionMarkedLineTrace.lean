import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicTrace
import ProximityPrize.SubmissionLower.R6960CollisionTameFibreTrace
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceDimension

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus LineEuler CollisionTame
open Polynomial Module Algebra Matrix
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial Matrix TensorProduct
open private Lower6960.RetainedSurfaceClass.nodeRing Lower6960.RetainedSurfaceClass.eval_subtype
  Lower6960.RetainedSurfaceClass.vanishing_divides from ProximityPrize.SubmissionLower.R6960RetainedGlobalEvaluation
open private Lower6960.RetainedSurfaceClass.point_polynomial from ProximityPrize.SubmissionLower.R6960RetainedSurfaceDimension

variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]

local instance traceAxisRing (j:Bool) (z:L) : CommRing (Axis E j z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E j z)

local instance traceFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

/-- The native chart module carries the subring multiplication from
the actual torus quotient. -/
abbrev lineChartRing (j b:Bool) (z:L) : Subring (Axis E j z) :=
  (imageAlg E j z b).toSubring

@[instance_reducible] def lineChartAlgebra (j b:Bool) (z:L) (_nz:z≠0) :
    Algebra L[X] (lineChartRing (E:=E) j b z) :=
  imagePolyAlgebra E j z b

/-- The geometric line frame and the original quotient frame have the
same ring and scalar actions, so the trace can be read on either. -/
def lineFibreRingEquiv (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    let : Algebra L[X] (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    Fiber E z ≃ₐ[L[X]] lineChartRing (E:=E) j b z := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let C := lineChartRing (E:=E) j b z
  let : Algebra L[X] C := lineChartAlgebra j b z nz
  let d := lineFibreData (E:=E) j b z nz
  let f := d.val.codRestrict C fun x=>(d.property.2.2 _).mp ⟨x,rfl⟩
  let g : Fiber E z→ₐ[L[X]] C := {
    f with
    commutes' := fun p=>Subtype.ext (lineFibreData_scalar j b z nz p) }
  exact AlgEquiv.ofBijective g
    ⟨fun _ _ h=>d.property.1 (congrArg Subtype.val h),
      fun v=>by
        obtain ⟨u,hu⟩ := (d.property.2.2 _).mpr v.property
        exact ⟨u,Subtype.ext hu⟩⟩

def lineChartLinearEquiv (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra L[X] (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    chartImage E j z b ≃ₗ[L[X]] lineChartRing (E:=E) j b z := by
  let : Algebra L[X] (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
  exact {
    toFun := fun v=>⟨v.val,v.property⟩
    invFun := fun v=>⟨v.val,v.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }

private theorem trace_basis_associated {R S:Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] {m n:ℕ} (a:Basis (Fin m) R S) (b:Basis (Fin n) R S) :
    Associated (traceMatrix R a).det (traceMatrix R b).det := by
  classical
  have eq : m=n := by
    have am := finrank_eq_card_basis a
    have bm := finrank_eq_card_basis b
    simpa only [Fintype.card_fin] using am.symm.trans bm
  subst n
  apply Ideal.span_singleton_eq_span_singleton.mp
  have h := (gramIdeal_basis (traceForm R S) a).symm.trans (gramIdeal_basis (traceForm R S) b)
  exact h

/-- The discriminant generator restricts to the trace determinant in
the exact selected free chart frame. -/
theorem selected_line_trace_associated (j b:Bool) (z:L) (nz:z≠0) {m:ℕ}
    (bf:Basis (Fin m) L[X] (chartImage E j z b)) (δ:Plane L)
    (principal : let : Algebra (Plane L) E := linePlaneAlgebra j b
      let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
      let : SMul (Plane L) (FractionRing (Plane L)) :=
        (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
      let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := linePlaneTower j b
      let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis
        (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
      ∀ [Algebra.IsSeparable (FractionRing (Plane L)) E],
        normalizationDiscriminant (A:=Plane L) (E:=E) (FractionRing (Plane L))=Ideal.span {δ})
    [Algebra.IsSeparable ChartField E] :
    let : Algebra L[X] (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    Associated (traceMatrix L[X] (bf.map (lineChartLinearEquiv j b z nz))).det (δ.eval (C z)) := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := linePlaneTower j b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := lineFraction_separable j b
  let : Algebra L[X] (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
  let bf' := bf.map (lineChartLinearEquiv j b z nz)
  let g := lineFibreRingEquiv (E:=E) j b z nz
  obtain ⟨u,assoc⟩ := fibre_trace_det_associated (E:=E) δ principal z
  let v := u.map g.toLinearEquiv
  have same : traceMatrix L[X] u=traceMatrix L[X] v := by
    have eq := trace_matrix_map_of_basis (RingHom.id L[X]) u v g.toRingHom
      (fun a=>g.commutes a) (fun i=>(Basis.map_apply u g.toLinearEquiv i).symm)
    apply Matrix.ext
    intro i l
    exact congrFun (congrFun eq i) l
  change Associated (traceMatrix L[X] bf').det (δ.eval (C z))
  exact (trace_basis_associated bf' v).trans ((congrArg Matrix.det same) ▸ assoc)

omit [FiniteDimensional ChartField E] in
/-- Switching from the native chart module to the same chart as a ring
preserves exactly the free Laurent localization and the chosen basis. -/
private theorem subring_localization (j b:Bool) (z:L) (nz:z≠0)
    [Algebra L[X] (lineChartRing (E:=E) j b z)]
    (f : ChartMap (k:=L) b (lineChartRing (E:=E) j b z) (Axis E j z))
    (value : ∀ u,f u=u.val) : IsChartLocalization b f := by
  apply isChartLocalization_of_clearing b f (fun x y h=>Subtype.ext ((value x).symm.trans (h.trans (value y))))
  intro x
  let S := Submonoid.powers (Polynomial.X:L[X])
  let : Module L[X] (Axis E j z) := Module.compHom _ (chartEmbedding (k:=L) b).toRingHom
  let g := nativeMap E j z b
  let : IsLocalizedModule S g := native_localization E j z nz b
  obtain ⟨⟨u,w⟩,eq⟩ := IsLocalizedModule.surj S g x
  obtain ⟨n,hn⟩ := w.property
  refine ⟨n,⟨u.val,u.property⟩,?_⟩
  change (chartEmbedding b (w:L[X])) • x=u.val at eq
  rw [←hn,map_pow] at eq
  exact eq.trans (value _).symm

omit [FiniteDimensional ChartField E] in
/-- The selected native polynomial bases give exactly the trace-square
law for the determinant measured by the surface budget. -/
theorem selected_line_trace_transition (j:Bool) (z:L) (nz:z≠0) {m:ℕ}
    (bf:Basis (Fin m) L[X] (chartImage E j z false))
    (bi:Basis (Fin m) L[X] (chartImage E j z true)) :
    let : Algebra L[X] (lineChartRing (E:=E) j false z) := lineChartAlgebra j false z nz
    let : Algebra L[X] (lineChartRing (E:=E) j true z) := lineChartAlgebra j true z nz
    let df := (traceMatrix L[X] (bf.map (lineChartLinearEquiv j false z nz))).det
    let di := (traceMatrix L[X] (bi.map (lineChartLinearEquiv j true z nz))).det
    LaurentPolynomial.invert di.toLaurent =
      (transition E j z nz bf bi).det^2*df.toLaurent := by
  let df := lineChartRing (E:=E) j false z
  let di := lineChartRing (E:=E) j true z
  let : Algebra L[X] df := lineChartAlgebra j false z nz
  let : Algebra L[X] di := lineChartAlgebra j true z nz
  let e := lineChartLinearEquiv (E:=E) j false z nz
  let r := lineChartLinearEquiv (E:=E) j true z nz
  let af := bf.map e
  let ai := bi.map r
  let ff : ChartMap (k:=L) false df (Axis E j z) :=
    (nativeMap E j z false).comp e.symm.toLinearMap
  let fi : ChartMap (k:=L) true di (Axis E j z) :=
    (nativeMap E j z true).comp r.symm.toLinearMap
  have of (u:df) : ff u=u.val := rfl
  have oi (u:di) : fi u=u.val := rfl
  let lf := subring_localization j false z nz ff of
  let li := subring_localization j true z nz fi oi
  have cmpf : localFreeBasis false af ff lf =
      localFreeBasis false bf (nativeMap E j z false) (native_localization E j z nz false) := by
    apply DFunLike.ext
    intro i
    rw [localFreeBasis_apply,localFreeBasis_apply]
    change (nativeMap E j z false) (e.symm (af i))=_
    rw [show af i=e (bf i) from Basis.map_apply bf e i,LinearEquiv.symm_apply_apply]
  have cmpi : localFreeBasis true ai fi li =
      localFreeBasis true bi (nativeMap E j z true) (native_localization E j z nz true) := by
    apply DFunLike.ext
    intro i
    rw [localFreeBasis_apply,localFreeBasis_apply]
    change (nativeMap E j z true) (r.symm (ai i))=_
    rw [show ai i=r (bi i) from Basis.map_apply bi r i,LinearEquiv.symm_apply_apply]
  have trans : freeTransition af ai ff fi lf li=transition E j z nz bf bi := by
    unfold transition freeTransition
    rw [cmpf,cmpi]
  have eq := free_trace_transition af ai ff fi lf li df.subtype di.subtype of oi
  rw [trans] at eq
  exact eq

private theorem trace_nonzero_over_actual_point {k U V : Type*} [Field k] [CommRing U]
    [CommRing V] [Algebra k[X] U] [Algebra k V] [IsReduced V] [FiniteDimensional k V]
    {m:ℕ} (p:ℕ) [CharP k p] (small:finrank k V<p) (x:k)
    (b:Basis (Fin m) k[X] U) (F:U→+*V) (onto:Function.Surjective F)
    (scalar:∀ r:k[X],F (algebraMap k[X] U r)=algebraMap k V (r.eval x))
    (kernel:∀ u:U,F u=0→algebraMap k[X] U (Polynomial.X-Polynomial.C x)∣u) :
    (traceMatrix k[X] b).det≠0 := by
  classical
  let basis (i:Fin m) := F (b i)
  have spans : ⊤≤Submodule.span k (Set.range basis) := by
    intro w _
    obtain ⟨u,rfl⟩ := onto w
    rw [←b.sum_repr u,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [Algebra.smul_def,map_mul,scalar,←Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  have lin : LinearIndependent k basis := by
    apply Fintype.linearIndependent_iff.mpr
    intro w zero i
    let y : U := ∑ j,Polynomial.C (w j) • b j
    have hz : F y=0 := by
      unfold y
      rw [map_sum]
      apply Eq.trans _ zero
      apply Finset.sum_congr rfl
      intro l _
      rw [Algebra.smul_def,map_mul,scalar,←Algebra.smul_def]
      change (Polynomial.C (w l)).eval x • basis l=w l • basis l
      rw [eval_C]
    obtain ⟨v,clear⟩ := kernel y hz
    have y_eq : y=(Polynomial.X-Polynomial.C x) • v := by
      rwa [Algebra.smul_def]
    have repr := congrArg (fun t:U=>b.repr t i) y_eq
    dsimp only [y] at repr
    rw [b.repr_sum_self,b.repr.map_smul,Finsupp.smul_apply,smul_eq_mul] at repr
    have ev := congrArg (eval x) repr
    rw [eval_C,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul] at ev
    exact ev
  let bc : Basis (Fin m) k V := Basis.mk lin spans
  have actual (i:Fin m) : F (b i)=bc i := by
    exact (congrFun (Basis.coe_mk lin spans) i).symm
  let spec := evalRingHom x
  have trace : (traceMatrix k[X] b).map spec=traceMatrix k bc :=
    trace_matrix_map_of_basis spec b bc F scalar actual
  have nd : (traceForm k V).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro v hv
    change v=0
    exact IsReduced.eq_zero _ ((TraceSpecialization.trace_radical p small v).mp hv)
  have mat : traceMatrix k bc=(traceForm k V).toMatrix bc := by
    apply Matrix.ext
    intro i l
    rw [traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
  intro zero
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bc).mp nd
  rw [←mat,←trace]
  change (spec.mapMatrix (traceMatrix k[X] b)).det=0
  rw [←RingHom.map_det,zero,map_zero]

omit [FiniteDimensional ChartField E] in
/-- The selected finite line trace is nonzero when its actual crossing
point is reduced and tame. -/
theorem selected_line_trace_nonzero (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    {m:ℕ} (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p)
    (bf:Basis (Fin m) L[X] (chartImage E j (atCoord j x z) false)) :
    let : Algebra L[X] (lineChartRing (E:=E) j false (atCoord j x z)) :=
      lineChartAlgebra j false (atCoord j x z) (by cases j <;> assumption)
    (traceMatrix L[X] (bf.map (lineChartLinearEquiv j false (atCoord j x z) (by cases j <;> assumption)))).det≠0 := by
  let c := atCoord j x z
  have nc : c≠0 := by cases j <;> assumption
  let V := Crossing E x z
  let U := lineChartRing (E:=E) j false c
  let : Algebra L[X] U := lineChartAlgebra j false c nc
  let chart := lineChartLinearEquiv (E:=E) j false c nc
  let b := bf.map chart
  let F : U→+*V := (Lower6960.RetainedSurfaceClass.nodeRing E j x z).toRingHom.comp U.subtype
  have scalar (r:L[X]) : F (algebraMap L[X] U r)=algebraMap L V (r.eval (atCoord (!j) x z)) :=
    Lower6960.RetainedSurfaceClass.point_polynomial E j x z r
  have onto : Function.Surjective F := by
    intro w
    obtain ⟨u,hu⟩ := onto_at_node E j x z nx nz w
    refine ⟨chart u,?_⟩
    change Lower6960.RetainedSurfaceClass.nodeRing E j x z u.val=w
    rw [Lower6960.RetainedSurfaceClass.eval_subtype]
    exact hu
  have kernel (u:U) (hu:F u=0) :
      algebraMap L[X] U (Polynomial.X-Polynomial.C (atCoord (!j) x z))∣u :=
    Lower6960.RetainedSurfaceClass.vanishing_divides E j x z nx nz u hu
  exact trace_nonzero_over_actual_point (k:=L) (U:=U) (V:=V) p small
    (atCoord (!j) x z) b F onto scalar kernel

#print axioms selected_line_trace_associated
#print axioms selected_line_trace_transition
#print axioms selected_line_trace_nonzero
end
end Lower6960.CollisionMarked
