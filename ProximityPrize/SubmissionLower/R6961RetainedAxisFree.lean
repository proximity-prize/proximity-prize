import ProximityPrize.SubmissionLower.R6961RetainedAxisCharts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass Lower6961.MonicChartProbes
open Lower6961.RetainedSurfaceClass (oriented_var oriented_const finite_along embedBase)
open Lower6961.RetainedRestrictionTorus (rel_equiv)

variable (E : Type) [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
local notation "ι" => algebraMap ChartField E

/-- On a chosen line, a nonzero polynomial in its running coordinate cannot kill
a nonzero section, including on a reducible fibre. Both coordinate orientations use
divisibility in the original surface normalization. -/
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
    apply Lower6961.RetainedRestrictionTorus.rel_equiv (oriented j b)
    simpa using Lower6960.TwoRulings.independent_denominators p (Polynomial.X-C c) pn (X_sub_C_ne_zero _)
  have hf : (h:ChartField)=divisor j c := by
    change ((oriented j b (Polynomial.X-C (C c))):ChartField)=_
    rw [map_sub]
    change ((oriented j b Polynomial.X):ChartField)-((oriented j b (C (C c))):ChartField)=_
    rw [Lower6961.RetainedSurfaceClass.oriented_var,Lower6961.RetainedSurfaceClass.oriented_const]; rfl
  have cp : (along E j b p:E)=i a := by
    rw [←Lower6961.RetainedSurfaceClass.finite_along]; rfl
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
    apply Lower6960.NormalizedFiber.integral_of_coprime_clearings ChartField hn an cop.symm _
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

#print axioms no_axis_torsion
#print axioms chart_free
end Lower6961.RetainedSurfaceClass
