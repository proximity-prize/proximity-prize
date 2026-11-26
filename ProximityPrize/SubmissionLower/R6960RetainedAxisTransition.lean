import ProximityPrize.SubmissionLower.R6960RetainedCrossingComparison
import ProximityPrize.SubmissionLower.R6960LineEulerFree

set_option Elab.async false

-- merged module R6960RetainedAxisCharts
section Merged_R6960RetainedAxisCharts
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]
def oriented (j b : Bool) : PlaneConstants.Plane L ≃+*baseChart (reference j b) :=
  if j then Bivariate.swap.toRingEquiv.trans (planeEquiv _) else planeEquiv _
theorem oriented_var (j b : Bool) :
    ((oriented j b Polynomial.X):ChartField)=coordinate j := by
  cases j <;> change planeMap _ _=_
  · simp [reference,coordinate,chartCoordinate]
  · change planeMap _ (Bivariate.swap Polynomial.X)=_
    rw [Bivariate.swap_Y,planeMap_scalar]; rfl
theorem oriented_line (j b : Bool) :
    ((oriented j b (C Polynomial.X)):ChartField)=chartCoordinate b (coordinate (!j)) := by
  cases j <;> change planeMap _ _=_
  · rw [planeMap_scalar]; rfl
  · change planeMap _ (Bivariate.swap (C Polynomial.X))=_
    rw [Bivariate.swap_X,planeMap_abscissa]; rfl
theorem oriented_const (j b : Bool) (r:L) :
    ((oriented j b (C (C r))):ChartField)=constants r := by
  cases j <;> change planeMap _ _=_
  · exact planeMap_constants ..
  · change planeMap _ (Bivariate.swap (C (C r)))=_
    rw [Bivariate.swap_C_C,planeMap_constants]
def along (j b:Bool) : (Polynomial L)→+* Tor E :=
  let x:=chartCoordinate b (coordinate (!j))
  let t : Tor E:=⟨algebraMap ChartField E x,
    isIntegral_algebraMap (x:=(⟨x,torus_coordinate (!j) b⟩:torus))⟩
  eval₂RingHom (algebraMap L (Tor E)) t
def intoTorus (s:Chart) : integralClosure (baseChart s) E →+* Tor E :=
  Subring.inclusion (show (integralClosure (baseChart s) E).toSubring≤(Tor E).toSubring
    from fun _ h=>order_mono (base_torus s) h)
def embedBase (s:Chart) : baseChart s→+*Tor E :=
  (intoTorus E s).comp (algebraMap (baseChart s) (integralClosure (baseChart s) E))
theorem finite_along (j b:Bool) (P:(Polynomial L)) :
    embedBase E (reference j b) (oriented j b (C P))=along E j b P := by
  let h:=(embedBase E (reference j b)).comp ((oriented j b).toRingHom.comp C)
  have eq : h=along E j b := Polynomial.ringHom_ext
    (fun r=>by
      apply Subtype.ext
      change algebraMap ChartField E ((oriented j b (C (C r))):ChartField) = _
      rw [oriented_const]
      simp [along,eval₂RingHom]; rfl)
    (by
      apply Subtype.ext
      change algebraMap ChartField E ((oriented j b (C Polynomial.X)):ChartField)=_
      rw [oriented_line]
      simp [along,eval₂RingHom])
  exact DFunLike.congr_fun eq P
def polyMap (j:Bool) (c:L) (b:Bool) : (Polynomial L)→+*Axis E j c :=
  (Ideal.Quotient.mk (axisIdeal E j c)).comp (along E j b)
private theorem eval_fixed (j:Bool) (c:L) (b:Bool) (P:PlaneConstants.Plane L) :
    red E j c (embedBase E (reference j b) (oriented j b P))=polyMap E j c b (P.eval (C c)) := by
  let s:=reference j b
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  let F:=π.comp ((embedBase E s).comp (oriented j b).toRingHom)
  let G:=(polyMap E j c b).comp (evalRingHom (C c))
  have eq : F=G := by
    apply Polynomial.ringHom_ext
    · intro q
      change π (embedBase E s (oriented j b (C q)))=polyMap E j c b ((C q).eval (C c))
      rw [finite_along,eval_C]; rfl
    · change π (embedBase E s (oriented j b Polynomial.X)) = polyMap E j c b (Polynomial.X.eval (C c))
      rw [eval_X]
      change π (embedBase E s (oriented j b Polynomial.X))=π (along E j b (C c))
      apply Ideal.Quotient.eq.mpr
      have diff : embedBase E s (oriented j b Polynomial.X) - along E j b (C c)=cut E j c := by
        rw [←finite_along]
        apply Subtype.ext
        change algebraMap ChartField E ((oriented j b Polynomial.X):ChartField) -
          algebraMap ChartField E ((oriented j b (C (C c))):ChartField) = _
        rw [oriented_var,oriented_const]
        exact (map_sub (algebraMap ChartField E) _ _).symm
      rw [diff]; exact Ideal.subset_span (Set.mem_singleton _)
  exact DFunLike.congr_fun eq P
def polyImage (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Submodule (Polynomial L) (Axis E j c) := by
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  refine { carrier := (chartImage E j c b : Set _)
           zero_mem' := (chartImage E j c b).zero_mem
           add_mem' := (chartImage E j c b).add_mem
           smul_mem' := ?_ }
  rintro p _ ⟨u,hu,rfl⟩
  let s:=reference j b
  have inChart:IsIntegral (baseChart s) ((along E j b p):E) := by
    rw [←finite_along]; exact isIntegral_algebraMap
  refine ⟨along E j b p*u,inChart.mul hu,?_⟩
  exact map_mul (Ideal.Quotient.mk (axisIdeal E j c)) _ _
theorem chart_finite [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Module.Finite (Polynomial L) (polyImage E j c b) := by
  classical
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  let s:=reference j b
  let A:=baseChart s
  let O:=integralClosure A E
  have fin := IsIntegralClosure.finite A ChartField E O
  obtain ⟨G,gen⟩:=fin.1
  let V : Submodule (Polynomial L) (Axis E j c) := polyImage E j c b
  let : Module (Polynomial L) V := V.module
  let f (a:O):V:=⟨red E j c (intoTorus E s a),⟨_,a.property,rfl⟩⟩
  let h: Submodule (Polynomial L) V := Submodule.span (Polynomial L) ((G.image f : Finset V):Set V)
  refine ⟨⟨G.image f,top_unique (fun v _ => ?_)⟩⟩
  suffices covers : ∀ w:O, w∈Submodule.span A (G:Set O) → f w∈h by
    obtain ⟨u,hu,eq⟩:=v.property
    let w:O:=⟨u,hu⟩
    have hval:f w=v := Subtype.ext eq
    exact hval ▸ covers w (gen ▸ mem_top)
  intro w all
  induction all using Submodule.span_induction with
  | mem u hu => exact Submodule.subset_span (Finset.mem_image_of_mem f hu)
  | zero => exact h.zero_mem
  | add u v _ _ a b => exact h.add_mem a b
  | smul r u _ ih =>
    let p:=(oriented j b).symm r
    convert h.smul_mem (p.eval (C c)) ih using 1
    apply Subtype.ext
    rw [Submodule.coe_smul (p:=V),Algebra.smul_def r u]
    change Ideal.Quotient.mk _ (intoTorus E s (algebraMap A O r*u)) =
      polyMap E j c b (p.eval (C c))*Ideal.Quotient.mk _ (intoTorus E s u)
    rw [map_mul,map_mul]
    have scalar:=eval_fixed E j c b p
    rw [show oriented j b p=r from (oriented j b).apply_symm_apply r] at scalar
    exact congrArg (·*_) scalar
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisCharts

-- merged module R6960RetainedAxisFree
section Merged_R6960RetainedAxisFree
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass Lower6960.MonicChartProbes
open Lower6960.RetainedSurfaceClass (oriented_var oriented_const finite_along embedBase)
open Lower6960.RetainedRestrictionTorus (rel_equiv)
variable (E : Type) [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
local notation "ι" => algebraMap ChartField E
theorem no_axis_torsion (j:Bool) (c:L) (b:Bool) (p:(Polynomial L)) (pn:p≠0) (u:Tor E)
    (zero : polyMap E j c b p * red E j c u=0) : red E j c u=0 := by
  let s:=reference j b
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let i:=algebraMap A E
  let h:=oriented j b (Polynomial.X-C (C c))
  let a:=oriented j b (C p)
  have hn : h≠0 := (map_ne_zero_iff _ (oriented j b).injective).mpr (X_sub_C_ne_zero _)
  have an : a≠0 := (map_ne_zero_iff _ (oriented j b).injective).mpr (C_ne_zero.mpr pn)
  have cop : IsRelPrime a h := by
    apply Lower6960.RetainedRestrictionTorus.rel_equiv (oriented j b)
    simpa using TwoRulings.independent_denominators p (Polynomial.X-C c) pn (X_sub_C_ne_zero _)
  have hf : (h:ChartField)=divisor j c := by
    change ((oriented j b (Polynomial.X-C (C c))):ChartField)=_
    rw [map_sub]
    change ((oriented j b Polynomial.X):ChartField)-((oriented j b (C (C c))):ChartField)=_
    rw [Lower6960.RetainedSurfaceClass.oriented_var,Lower6960.RetainedSurfaceClass.oriented_const]; rfl
  have cp : (along E j b p:E)=i a := by
    rw [←Lower6960.RetainedSurfaceClass.finite_along]; rfl
  let D:=ι (divisor j c)
  have dn : D≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne j c)
  obtain ⟨v,hv⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp
    (show Ideal.Quotient.mk (axisIdeal E j c) (along E j b p*u)=0 from (map_mul ..).trans zero))
  let y:=(u:E)/D
  have uy : i h*y=u := by
    change ι (h:ChartField)*((u:E)/D)=_
    rw [hf]; change D*((u:E)/D)=_
    field_simp
  have vy : i a*y=v := by
    have eq := congrArg (fun r:Tor E=>(r:E)) hv
    change (along E j b p:E)*(u:E)=D*(v:E) at eq
    rw [cp] at eq
    change i a*((u:E)/D)=_
    rw [←mul_div_assoc,eq,mul_div_cancel_left₀ _ dn]
  obtain ⟨m,hm⟩:=clear_torus s _ u.property
  obtain ⟨n,hn'⟩:=clear_torus s _ v.property
  let G:=edge s (opposite s)
  change IsIntegral A (i G^m*(u:E)) at hm
  change IsIntegral A (i G^n*(v:E)) at hn'
  have extra (q:A) (v:E) (iv:IsIntegral A v) : IsIntegral A (i q*v) := isIntegral_algebraMap.mul iv
  have whole : IsIntegral A (i G^(m+n)*y) := by
    apply NormalizedFiber.integral_of_coprime_clearings ChartField hn an cop.symm _
    · change IsIntegral A (i h*(i G^(m+n)*y))
      have hh:= extra (G^n) _ hm
      rw [←uy,map_pow] at hh
      convert hh using 1 <;> rw [pow_add] <;> ring
    · change IsIntegral A (i a*(i G^(m+n)*y))
      have hh:= extra (G^m) _ hn'
      rw [←vy,map_pow] at hh
      convert hh using 1 <;> rw [pow_add] <;> ring
  have gn : i G≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s (opposite s))
  have inv : (boundary s (opposite s))⁻¹∈torus := by
    rw [all_charts s]
    exact ⟨1,by simp [edge_ne]⟩
  have torInv : IsIntegral torus (i G)⁻¹ := by
    have t:IsIntegral torus (ι ((boundary s (opposite s))⁻¹)) := isIntegral_algebraMap (x:=(⟨_,inv⟩:torus))
    change IsIntegral torus (ι (boundary s (opposite s)))⁻¹
    simpa only [map_inv₀] using t
  have iy := (torInv.pow (m+n)).mul (order_mono (base_torus s) whole)
  rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ gn,one_pow,one_mul] at iy
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  refine Ideal.mem_span_singleton.mpr ⟨⟨y,iy⟩,Subtype.ext ?_⟩
  change (u:E)=D*y
  change (u:E)=ι (divisor j c)*y
  rw [←hf]; exact uy.symm
theorem chart_free [Algebra.IsSeparable ChartField E] (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Module.Free (Polynomial L) (polyImage E j c b) := by
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  have :=chart_finite E j c b
  have : Module.IsTorsionFree (Polynomial L) (polyImage E j c b) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro p u hz
    by_cases pn:p=0
    · exact Or.inl pn
    right
    obtain ⟨w,_,ew⟩:=u.property
    apply Subtype.ext
    rw [←ew]
    apply no_axis_torsion E j c b p pn
    rw [ew]
    exact congrArg Subtype.val hz
  infer_instance
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisFree

-- merged module R6960RetainedAxisTransition
section Merged_R6960RetainedAxisTransition
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus ChartOverlapTests
open Module Submodule Algebra Polynomial LineEuler LaurentPolynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
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
  have cancel : (algebraMap L (Axis E j c) c⁻¹)^n * (algebraMap L (Axis E j c) c)^n=1 := by
    have scalar : c⁻¹^n*c^n=1 := by rw [←mul_pow,inv_mul_cancel₀ nc,one_pow]
    simpa only [map_mul,map_pow,map_one] using congrArg (algebraMap L (Axis E j c)) scalar
  calc _ = 1*((π V)^n*π u) := (one_mul _).symm
       _ = _ := by rw [←cancel]; ring
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisTransition
