import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960ChartImage
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisFamily
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionMarkedGenericFrames
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceDimension

section Merged6967_R6960CollisionMarkedGenericMeasure
set_option Elab.async false









set_option Elab.async false

-- merged module R6960CollisionMarkedLineTrace
section Merged_R6960CollisionMarkedLineTrace
set_option synthInstance.maxHeartbeats 200000
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
open Lower6960.RetainedSurfaceClass (nodeRing eval_subtype vanishing_divides)
open Lower6960.RetainedSurfaceClass (point_polynomial)
variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
local instance traceAxisRing (j:Bool) (z:L) : CommRing (Axis E j z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E j z)
local instance traceFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)
abbrev lineChartRing (j b:Bool) (z:L) : Subring (Axis E j z) :=
  (imageAlg E j z b).toSubring
@[instance_reducible] def lineChartAlgebra (j b:Bool) (z:L) (_nz:z≠0) :
    Algebra (Polynomial L) (lineChartRing (E:=E) j b z) :=
  imagePolyAlgebra E j z b
def lineFibreRingEquiv (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    Fiber E z ≃ₐ[(Polynomial L)] lineChartRing (E:=E) j b z := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let C := lineChartRing (E:=E) j b z
  let : Algebra (Polynomial L) C := lineChartAlgebra j b z nz
  let d := lineFibreData (E:=E) j b z nz
  let f := d.val.codRestrict C fun x=>(d.property.2.2 _).mp ⟨x,rfl⟩
  let g : Fiber E z→ₐ[(Polynomial L)] C := {
    f with
    commutes' := fun p=>Subtype.ext (lineFibreData_scalar j b z nz p) }
  exact AlgEquiv.ofBijective g
    ⟨fun _ _ h=>d.property.1 (congrArg Subtype.val h),
      fun v=>by
        obtain ⟨u,hu⟩ := (d.property.2.2 _).mpr v.property
        exact ⟨u,Subtype.ext hu⟩⟩
def lineChartLinearEquiv (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    chartImage E j z b ≃ₗ[(Polynomial L)] lineChartRing (E:=E) j b z := by
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
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
theorem selected_line_trace_associated (j b:Bool) (z:L) (nz:z≠0) {m:ℕ}
    (bf:Basis (Fin m) (Polynomial L) (chartImage E j z b)) (δ:Plane L)
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
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
    Associated (traceMatrix (Polynomial L) (bf.map (lineChartLinearEquiv j b z nz))).det (δ.eval (C z)) := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := linePlaneTower j b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := lineFraction_separable j b
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j b z) := lineChartAlgebra j b z nz
  let bf' := bf.map (lineChartLinearEquiv j b z nz)
  let g := lineFibreRingEquiv (E:=E) j b z nz
  obtain ⟨u,assoc⟩ := fibre_trace_det_associated (E:=E) δ principal z
  let v := u.map g.toLinearEquiv
  have same : traceMatrix (Polynomial L) u=traceMatrix (Polynomial L) v := by
    have eq := trace_matrix_map_of_basis (RingHom.id (Polynomial L)) u v g.toRingHom
      (fun a=>g.commutes a) (fun i=>(Basis.map_apply u g.toLinearEquiv i).symm)
    apply Matrix.ext
    intro i l
    exact congrFun (congrFun eq i) l
  change Associated (traceMatrix (Polynomial L) bf').det (δ.eval (C z))
  exact (trace_basis_associated bf' v).trans ((congrArg Matrix.det same) ▸ assoc)
omit [FiniteDimensional ChartField E] in
private theorem subring_localization (j b:Bool) (z:L) (nz:z≠0)
    [Algebra (Polynomial L) (lineChartRing (E:=E) j b z)]
    (f : ChartMap (k:=L) b (lineChartRing (E:=E) j b z) (Axis E j z))
    (value : ∀ u,f u=u.val) : IsChartLocalization b f := by
  apply isChartLocalization_of_clearing b f (fun x y h=>Subtype.ext ((value x).symm.trans (h.trans (value y))))
  intro x
  let S := Submonoid.powers (Polynomial.X:(Polynomial L))
  let : Module (Polynomial L) (Axis E j z) := Module.compHom _ (chartEmbedding (k:=L) b).toRingHom
  let g := nativeMap E j z b
  let : IsLocalizedModule S g := native_localization E j z nz b
  obtain ⟨⟨u,w⟩,eq⟩ := IsLocalizedModule.surj S g x
  obtain ⟨n,hn⟩ := w.property
  refine ⟨n,⟨u.val,u.property⟩,?_⟩
  change (chartEmbedding b (w:(Polynomial L))) • x=u.val at eq
  rw [←hn,map_pow] at eq
  exact eq.trans (value _).symm
omit [FiniteDimensional ChartField E] in
theorem selected_line_trace_transition (j:Bool) (z:L) (nz:z≠0) {m:ℕ}
    (bf:Basis (Fin m) (Polynomial L) (chartImage E j z false))
    (bi:Basis (Fin m) (Polynomial L) (chartImage E j z true)) :
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j false z) := lineChartAlgebra j false z nz
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j true z) := lineChartAlgebra j true z nz
    let df := (traceMatrix (Polynomial L) (bf.map (lineChartLinearEquiv j false z nz))).det
    let di := (traceMatrix (Polynomial L) (bi.map (lineChartLinearEquiv j true z nz))).det
    LaurentPolynomial.invert di.toLaurent =
      (transition E j z nz bf bi).det^2*df.toLaurent := by
  let df := lineChartRing (E:=E) j false z
  let di := lineChartRing (E:=E) j true z
  let : Algebra (Polynomial L) df := lineChartAlgebra j false z nz
  let : Algebra (Polynomial L) di := lineChartAlgebra j true z nz
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
    [CommRing V] [Algebra (Polynomial k) U] [Algebra k V] [IsReduced V] [FiniteDimensional k V]
    {m:ℕ} (p:ℕ) [CharP k p] (small:finrank k V<p) (x:k)
    (b:Basis (Fin m) (Polynomial k) U) (F:U→+*V) (onto:Function.Surjective F)
    (scalar:∀ r:(Polynomial k),F (algebraMap (Polynomial k) U r)=algebraMap k V (r.eval x))
    (kernel:∀ u:U,F u=0→algebraMap (Polynomial k) U (Polynomial.X-Polynomial.C x)∣u) :
    (traceMatrix (Polynomial k) b).det≠0 := by
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
  have trace : (traceMatrix (Polynomial k) b).map spec=traceMatrix k bc :=
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
  change (spec.mapMatrix (traceMatrix (Polynomial k) b)).det=0
  rw [←RingHom.map_det,zero,map_zero]
section
-- The `finrank` of the two `Module` instance paths on `Crossing` is otherwise unfolded on Lean 4.36.
attribute [local irreducible] Module.finrank
omit [FiniteDimensional ChartField E] in
theorem selected_line_trace_nonzero (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    {m:ℕ} (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p)
    (bf:Basis (Fin m) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    let : Algebra (Polynomial L) (lineChartRing (E:=E) j false (atCoord j x z)) :=
      lineChartAlgebra j false (atCoord j x z) (by cases j <;> assumption)
    (traceMatrix (Polynomial L) (bf.map (lineChartLinearEquiv j false (atCoord j x z) (by cases j <;> assumption)))).det≠0 := by
  let c := atCoord j x z
  have nc : c≠0 := by cases j <;> assumption
  let V := Crossing E x z
  let U := lineChartRing (E:=E) j false c
  let : Algebra (Polynomial L) U := lineChartAlgebra j false c nc
  let chart := lineChartLinearEquiv (E:=E) j false c nc
  let b := bf.map chart
  let F : U→+*V := (Lower6960.RetainedSurfaceClass.nodeRing E j x z).toRingHom.comp U.subtype
  have scalar (r:(Polynomial L)) : F (algebraMap (Polynomial L) U r)=algebraMap L V (r.eval (atCoord (!j) x z)) :=
    Lower6960.RetainedSurfaceClass.point_polynomial E j x z r
  have onto : Function.Surjective F := by
    intro w
    obtain ⟨u,hu⟩ := onto_at_node E j x z nx nz w
    refine ⟨chart u,?_⟩
    change Lower6960.RetainedSurfaceClass.nodeRing E j x z u.val=w
    rw [Lower6960.RetainedSurfaceClass.eval_subtype]
    exact hu
  have kernel (u:U) (hu:F u=0) :
      algebraMap (Polynomial L) U (Polynomial.X-Polynomial.C (atCoord (!j) x z))∣u :=
    Lower6960.RetainedSurfaceClass.vanishing_divides E j x z nx nz u hu
  exact trace_nonzero_over_actual_point (k:=L) (U:=U) (V:=V) p small
    (atCoord (!j) x z) b F onto scalar kernel
#print axioms selected_line_trace_associated
#print axioms selected_line_trace_transition
end
#print axioms selected_line_trace_nonzero
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedLineTrace

-- merged module R6960CollisionMarkedMeasuredSum
section Merged_R6960CollisionMarkedMeasuredSum
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus LineEuler CollisionTame
open Polynomial LaurentPolynomial Module Algebra Matrix Finset
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial Matrix
private theorem laurent_nat_coeff {k:Type} [CommRing k] (P:(Polynomial k)) (n:ℕ) :
    P.toLaurent.coeff (n:ℤ)=P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ _
theorem plane_overlap_height_le {k:Type} [Field k] (A B:(Polynomial (Polynomial k))) (an:A≠0)
    (u:k) (un:u≠0) (m:ℤ)
    (glue : A.toLaurent=LaurentPolynomial.C (Polynomial.C u)*T m*invert B.toLaurent) :
    CurvatureSquares.height B≤CurvatureSquares.height A := by
  obtain ⟨_,bd⟩ := plane_overlap_degree_caps A B an u un m glue
  have cdeg (n:ℕ) : (B.coeff n).natDegree≤CurvatureSquares.height A := by
    by_cases h : (n:ℤ)≤m
    · let j := (m-(n:ℤ)).toNat
      have js : (j:ℤ)=m-(n:ℤ) := Int.toNat_of_nonneg (sub_nonneg.mpr h)
      have r := congrArg (fun P:LaurentPolynomial (Polynomial k)=>P.coeff (j:ℤ)) glue
      rw [laurent_nat_coeff,←single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff ((j:ℤ)-m) (by intro v _; omega),
        invert_apply,show -((j:ℤ)-m)=(n:ℤ) by omega,laurent_nat_coeff] at r
      have eq := congrArg Polynomial.natDegree r
      rw [natDegree_C_mul_of_isUnit (IsUnit.mk0 u un)] at eq
      exact eq ▸ CurvatureSquares.coeff_height A j
    · have s : B.natDegree<n := by omega
      rw [coeff_eq_zero_of_natDegree_lt s,natDegree_zero]
      exact Nat.zero_le _
  change (Bivariate.swap B).natDegree≤CurvatureSquares.height A
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n high
  apply Polynomial.ext
  intro i
  rw [CurvatureSquares.coeff_swap,coeff_eq_zero_of_natDegree_lt ((cdeg i).trans_lt high),coeff_zero]
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]
local instance measuredCrossRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)
theorem line_principal_discriminant (j b:Bool) :
    ∃ δ:Plane L, δ≠0 ∧ lineDiscriminant (E:=E) j b=Ideal.span {δ} := by
  let A := Plane L
  let F := FractionRing A
  let : Algebra A E := linePlaneAlgebra j b
  let : Algebra F E := lineFractionAlgebra j b
  let : SMul A F := (inferInstance : Algebra A F).toSMul
  let : IsScalarTower A F E := linePlaneTower j b
  let : FiniteDimensional F E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable F E := lineFraction_separable j b
  have hn := normalizationDiscriminant_ne_bot (A:=A) (E:=E) (F:=F)
  obtain ⟨δ,hδ⟩ := plane_discriminant_principal (k:=L) (E:=E)
  refine ⟨δ,?_,hδ⟩
  intro zero
  apply hn
  rw [hδ,zero]
  change Ideal.span ({0}:Set A)=⊥
  exact Ideal.span_singleton_zero
theorem original_line_degree_cap (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) true))
    (s:ℕ) (measure:(transition E j (atCoord j x z) (by cases j <;> assumption) bf bi).det.degree=
      ((-(s:ℤ):ℤ):WithBot ℤ))
    (δf δi:Plane L) (nf:δf≠0)
    (df:lineDiscriminant (E:=E) j false=Ideal.span {δf})
    (di:lineDiscriminant (E:=E) j true=Ideal.span {δi}) :
    (CurvatureSquares.height δf≤2*s ∧ CurvatureSquares.height δi≤2*s) ∧
    ∃ u:L,u≠0 ∧ (Bivariate.swap δf).toLaurent=
      LaurentPolynomial.C (Polynomial.C u)*T (2*(s:ℤ))*invert (Bivariate.swap δi).toLaurent := by
  let c := atCoord j x z
  have nc : c≠0 := by cases j <;> assumption
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j false c) := lineChartAlgebra j false c nc
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j true c) := lineChartAlgebra j true c nc
  let f := (traceMatrix (Polynomial L) (bf.map (lineChartLinearEquiv (E:=E) j false c nc))).det
  let i := (traceMatrix (Polynomial L) (bi.map (lineChartLinearEquiv (E:=E) j true c nc))).det
  let A := Bivariate.swap δf
  let B := Bivariate.swap δi
  have an : A≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have af' : Associated f (δf.eval (Polynomial.C c)) :=
    selected_line_trace_associated j false c nc bf δf (by intro _; exact df)
  have ai' : Associated i (δi.eval (Polynomial.C c)) :=
    selected_line_trace_associated j true c nc bi δi (by intro _; exact di)
  have hswap (δ:Plane L) : δ.eval (Polynomial.C c)=(Bivariate.swap δ).map (evalRingHom c) := by
    simpa only [Bivariate.swap_swap_apply] using RetainedCompression.eval_swap (Bivariate.swap δ) c
  have af : Associated f (A.map (evalRingHom c)) := hswap δf ▸ af'
  have ai : Associated i (B.map (evalRingHom c)) := hswap δi ▸ ai'
  have fn : f≠0 := selected_line_trace_nonzero j x z nx nz p small bf
  have good : A.map (evalRingHom c)≠0 := fun z=>fn (zero_dvd_iff.mp (z ▸ af.dvd'))
  obtain ⟨u,m,un,glue⟩ := line_overlap_unit j δf δi df di
  let G := (transition E j c nc bf bi).det
  have unit : IsUnit G := (Matrix.isUnit_iff_isUnit_det _).mp
    (freeTransition_unit bf bi (nativeMap E j c false) (nativeMap E j c true)
      (native_localization E j c nc false) (native_localization E j c nc true))
  have trace : invert i.toLaurent=G^2*f.toLaurent := selected_line_trace_transition j c nc bf bi
  have caps := plane_degree_from_line_transition A B an u un m glue c good f i af ai G unit trace s measure
  obtain ⟨d,dd,eq⟩ := overlap_transition_exponent A B u un m glue (evalRingHom c)
    good f i af ai G unit trace
  have de := WithBot.coe_injective (dd.symm.trans measure)
  have mx : m=2*(s:ℤ) := by omega
  exact ⟨caps,u,un,mx ▸ glue⟩
theorem actual_measured_discriminants (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p)
    {m n:ℕ} (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false))
    (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false))
    (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true))
    (s t:ℕ)
    (ds:(transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ))
    (dt:(transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ)) :
    ∃ δf δi:Plane L, δf≠0 ∧ δi≠0 ∧
      axisDiscriminant (E:=E) false=Ideal.span {δf} ∧
      axisDiscriminant (E:=E) true=Ideal.span {δi} ∧
      CurvatureSquares.height δf≤2*s ∧ δf.natDegree≤2*t ∧
      ((Bivariate.swap δi).trailingCoeff).natDegree≤2*t := by
  classical
  obtain ⟨δf,nf,df⟩ := line_principal_discriminant (E:=E) true false
  obtain ⟨δi,ni,di⟩ := line_principal_discriminant (E:=E) true true
  obtain ⟨δt,_,dti⟩ := line_principal_discriminant (E:=E) false true
  have swap : lineDiscriminant (E:=E) false false=Ideal.span {Bivariate.swap δf} := by
    rw [←line_discriminant_swap,df,Ideal.map_span,Set.image_singleton]
    rfl
  have xcap := (original_line_degree_cap true x z nx nz p small zf zi s ds δf δi nf df di).1.1
  have nzswap : Bivariate.swap δf≠0 :=
    (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have zcap := (original_line_degree_cap false x z nx nz p small xf xi t dt _ δt nzswap swap dti).1.1
  change (Bivariate.swap (Bivariate.swap δf)).natDegree≤2*t at zcap
  rw [Bivariate.swap_swap_apply] at zcap
  obtain ⟨u,l,un,glue⟩ := line_overlap_unit true δf δi df di
  have zi_le := plane_overlap_height_le _ _ nzswap u un l glue
  change (Bivariate.swap (Bivariate.swap δi)).natDegree≤(Bivariate.swap (Bivariate.swap δf)).natDegree at zi_le
  rw [Bivariate.swap_swap_apply,Bivariate.swap_swap_apply] at zi_le
  have cap := (boundary_seed_polynomial δi ni).2.1
  exact ⟨δf,δi,nf,ni,(line_discriminant_axis false).symm.trans df,
    (line_discriminant_axis true).symm.trans di,xcap,zcap,(cap.trans zi_le).trans zcap⟩
#print axioms actual_measured_discriminants
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedMeasuredSum

-- merged module R6960CollisionMarkedGenericMeasure
section Merged_R6960CollisionMarkedGenericMeasure
set_option synthInstance.maxHeartbeats 200000

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler CollisionTame
open LaurentPolynomial Polynomial Module Matrix
open scoped Polynomial Lower6960.RetainedSurfaceClass Matrix

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

local instance genericMeasureNodeRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

/-- The exact deficit of a selected native line agrees with the
determinant deficit of its generic normalized line. The same overlap
unit is used in both comparisons. -/
theorem generic_measure_eq_native (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) true))
    (s:ℕ) (measure:(transition E j (atCoord j x z) (by cases j <;> assumption) bf bi).det.degree=
      ((-(s:ℤ):ℤ):WithBot ℤ)) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    ∃ (f : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) false))
      (i : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) true)),
      (normalizedTransition f i).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) := by
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  obtain ⟨δf,nf,pf⟩ := line_principal_discriminant (E:=E) j false
  obtain ⟨δi,_,pi⟩ := line_principal_discriminant (E:=E) j true
  obtain ⟨_,u,un,glue⟩ := original_line_degree_cap j x z nx nz p small bf bi s measure δf δi nf pf pi
  obtain ⟨f⟩ := generic_line_basis (E:=E) j false
  obtain ⟨i⟩ := generic_line_basis (E:=E) j true
  let R := GenericLine L
  let K := GenericCoefficients L
  let A := Bivariate.swap δf
  let B := Bivariate.swap δi
  let spec := algebraMap (Polynomial L) K
  have an : A≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have nonzero : A.map spec≠0 :=
    (map_ne_zero_iff (Polynomial.mapRingHom spec)
      (Polynomial.map_injective _ (IsFractionRing.injective _ _))).mpr an
  have af := generic_line_trace_associated j false δf pf f
  have ai := generic_line_trace_associated j true δi pi i
  let G := (normalizedTransition f i).det
  have unit : IsUnit G := (Matrix.isUnit_iff_isUnit_det _).mp (normalizedTransition_unit f i)
  have trace := normalized_trace_transition f i
  obtain ⟨d,dd,eq⟩ := overlap_transition_exponent A B u un (2*(s:ℤ)) glue
    spec nonzero _ _ af ai G unit trace
  have de : d=-(s:ℤ) := by omega
  exact ⟨f,i,de ▸ dd⟩

#print axioms generic_measure_eq_native
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedGenericMeasure

end Merged6967_R6960CollisionMarkedGenericMeasure

section Merged6967_R6960MarkedAllLabels
set_option Elab.async false




set_option Elab.async false

-- merged module R6960MarkedEvaluationEndpoint
section Merged_R6960MarkedEvaluationEndpoint

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open RetainedCompression
open RetainedLinear (GeometricallyLinear)
open scoped Polynomial

/-- Only the nonlinear marked factors of the actual high family need the
single-determinant estimate. The protocol, scalar list, and all other cases
are supplied by the verified 69.61 pipeline. -/
def NonlinearPrice : Prop :=
  ∀ {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ) (T:Finset K), T⊆Γ →
    Word 179818 wordDegree M.word F.scalar T →
    ∀ f:Curve (Polynomial L),Irreducible f → 3≤f.degreeOf ordinate → f.degreeOf ordinate<48 →
      0<f.degreeOf parameter → height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T,MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate

theorem protocol_of_price (gates : Low6960Allocation.Gates) (price:NonlinearPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6961 ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q := by
  have mono:Monotone rate:=by
    intro e n en
    exact Nat.sub_le_sub_right (Nat.add_le_add
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 en) _) (Nat.sub_le_sub_right en 1))
      (Nat.mul_le_mul_left 2 en)) 1
  apply Lower6960.protocol_claim_of_retained gates
  have proper (e:ℕ) (he:3≤e) (hi:e<48) : 12*e≤rate e :=
    (by decide +kernel : ∀ i:Fin 48, 3 ≤ i.val → 12*i.val≤rate i.val) ⟨e,hi⟩ he
  apply retained_of_tariff rate mono (by decide) proper budget
  · intro u deleted M Γ F T sub words f ir lo hi sv cap marks
    by_cases g:GeometricallyLinear (view f)
    · have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
      have pos : 0<(view f).natDegree := by rw [view_y];omega
      have pure:=RetainedLinear.pure_of_geometrically_linear M.word (view f) irr pos g
      have bound:=pure_node_price words (scalar M) (scalar_injective M).injOn (view f) irr pos pure marks
      rw [view_z] at bound
      exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (mono lo)))
        (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
    · exact price F T sub words f ir lo hi sv cap g marks

#print axioms protocol_of_price
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedEvaluationEndpoint

-- merged module R6960MarkedAllLabels
section Merged_R6960MarkedAllLabels
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open RetainedTwistedRestriction RetainedSurfaceClass CollisionMarked NormalizedFiber Polynomial Finset Module Submodule
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]

/-- Reinsert every marked parameter, including zero and all reciprocal
boundary exceptions. They are roots of a single polynomial of degree at
most 2t+1. -/
theorem all_labels [DecidableEq L] (p:ℕ) [CharP L p] [CharP Scalar p] (P:CurvatureSquares.Ordinate)
    (pn:projectedRaw P≠0) (lo:3≤P.natDegree) (hi:P.natDegree<p) (v:ℕ) (vp:0<v)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root:let : Algebra (Plane L) E:=axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (s t:ℕ) (positive:0<s) (tame:2*s<p) (tariff:t≤(P.natDegree-1)*v) (surface:Budget E (s-1) (s+s*t))
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:axisDiscriminant (E:=E) false=Ideal.span {δf}) (di:axisDiscriminant (E:=E) true=Ideal.span {δi})
    (xc:CurvatureSquares.height δf≤2*s) (zc:δf.natDegree≤2*t) (tail:((Bivariate.swap δi).trailingCoeff).natDegree≤2*t)
    (S:Finset L) (word:L → Polynomial L) (mark:∀z∈S,RetainedCompression.MarkedFiber P z (word z))
    (vertical:∀(U:Finset L)(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j))→
      finrank Scalar (span Scalar (Set.range v))+s≤P.natDegree*s) :
    S.card≤rate P.natDegree*v+(P.natDegree-1)*P.natDegree := by
  classical
  let B:=(Bivariate.swap δi).trailingCoeff
  have bn:B≠0 := trailingCoeff_nonzero_iff_nonzero.mpr ((map_ne_zero_iff _ Bivariate.swap.injective).mpr ni)
  let D:=(Polynomial.X:(Polynomial L))*B
  have dn:D≠0:=mul_ne_zero Polynomial.X_ne_zero bn
  let bad:=D.roots.toFinset
  let U:=S\bad
  have valid (z:L) (hz:z∈U) : z≠0 ∧ B.eval z≠0 := by
    have no:= (Finset.mem_sdiff.mp hz).2
    have noeval:D.eval z≠0:=fun h=>no (Multiset.mem_toFinset.mpr ((mem_roots dn).mpr h))
    rw [show D=Polynomial.X*B from rfl,eval_mul,eval_X] at noeval
    exact mul_ne_zero_iff.mp noeval
  have good:=actual_good_count (E:=E) p P pn (by omega) hi b dim root s t positive tame surface δf δi nf ni df di xc zc U
    (fun z hz=>(valid z hz).1) word (fun z hz=>mark z (Finset.mem_sdiff.mp hz).1)
    (fun z hz=>(valid z hz).2) (vertical U)
  have exceptions:bad.card≤1+2*t :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (by
      rw [show D=Polynomial.X*B from rfl,natDegree_mul Polynomial.X_ne_zero bn,natDegree_X]
      exact Nat.add_le_add_left tail 1))
  have combined : S.card≤9*P.natDegree*t+P.natDegree*(P.natDegree-1)+(1+2*t) :=
    Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add good exceptions)
  let e:=P.natDegree
  have base:1≤(2*e-1)*v:=Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by dsimp [e];omega) vp.ne')
  have rate_eq:rate e=(9*e+2)*(e-1)+(2*e-1) := by unfold rate;omega
  have charge:9*e*t+e*(e-1)+(1+2*t)=(9*e+2)*t+1+(e-1)*e := by ring
  change S.card≤rate e*v+(e-1)*e
  change S.card≤9*e*t+e*(e-1)+(1+2*t) at combined
  rw [charge] at combined
  rw [rate_eq,Nat.add_mul,Nat.mul_assoc]
  exact combined.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ tariff) base) _)

#print axioms all_labels
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedAllLabels

end Merged6967_R6960MarkedAllLabels
