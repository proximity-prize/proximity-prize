import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreNormalization
import ProximityPrize.SubmissionLower.R6960LineEulerFree

section Merged6967_R6960CollisionMarkedFibreIndex
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Module Matrix Polynomial CollisionTame
open scoped Matrix Polynomial BigOperators
variable {A K B V : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Algebra A B] [CommRing V] [IsReduced V] [Algebra A V]
  [Algebra K V] [IsScalarTower A K V] [FiniteDimensional K V]
theorem reduced_fibre_index {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ) [CharP K p] (small : finrank K V<p)
    (φ : B→ₐ[A]V) (b : Basis I A B)
    (bk : Basis I K V) (induced : ∀ i,bk i=φ (b i)) :
    ∃ (n : Basis I A (integralClosure A V)) (D : Matrix I I A),
      D.det≠0 ∧ (traceMatrix A n).det≠0 ∧
      (∃ lift : B→ₐ[A]integralClosure A V,
        (∀ x,(lift x:V)=φ x) ∧ D=n.toMatrix (fun i=>lift (b i))) ∧
      traceMatrix A b=D.transpose*traceMatrix A n*D ∧
      (∀ v : V,IsIntegral A v→∃ u : B,φ u=algebraMap A V D.det*v) := by
  classical
  let N := integralClosure A V
  let : Module.Finite A B := Module.Finite.of_basis b
  let lift : B→ₐ[A]N := φ.codRestrict N (fun x=>(Algebra.IsIntegral.isIntegral x).map φ)
  obtain ⟨n0,nk0,h0⟩ := reduced_normalization_basis (A:=A) p small
  let t : Fin (finrank K V) ≃ I := (Fintype.equivFinOfCardEq (finrank_eq_card_basis bk).symm).symm
  let n := n0.reindex t
  let nk := nk0.reindex t
  have hn (i : I) : nk i=(n i:V) := by
    rw [show nk i=nk0 (t.symm i) from Basis.reindex_apply _ _ _,
      show n i=n0 (t.symm i) from Basis.reindex_apply _ _ _]
    exact h0 _
  let D : Matrix I I A := fun i j=>n.repr (lift (b j)) i
  let j := algebraMap A K
  have expand (i : I) : (∑ l,j (D l i) • nk l)=bk i := by
    calc
      _ = (↑(∑ l,D l i • n l : N):V) := by
        rw [show ((∑ l,D l i • n l : N):V)=∑ l,((D l i • n l : N):V) from map_sum N.val _ _]
        apply Finset.sum_congr rfl
        intro l _
        rw [hn,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      _ = (lift (b i):V) := congrArg Subtype.val (n.sum_repr (lift (b i)))
      _ = _ := (induced i).symm
  have ae : D.map j=nk.toMatrix bk := by
    apply Matrix.ext
    intro i l
    change j (D i l)=nk.repr (bk l) i
    rw [←expand l,nk.repr_sum_self]
  have an : (D.map j).det≠0 := by
    have h : (bk.toMatrix nk)*(D.map j)=1 := by rw [ae,Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.det_ne_zero_of_left_inverse h
  have dn : D.det≠0 := fun zero=>an (((RingHom.map_det j D).symm).trans (zero ▸ map_zero j))
  have map_b : (traceMatrix A b).map j=traceMatrix K bk :=
    trace_matrix_map_of_basis j b bk φ.toRingHom (fun a=>(φ.commutes a).trans (IsScalarTower.algebraMap_apply A K V a))
      (fun i=>(induced i).symm)
  have map_n : (traceMatrix A n).map j=traceMatrix K nk :=
    trace_matrix_map_of_basis j n nk N.val.toRingHom (fun a=>IsScalarTower.algebraMap_apply A K V a)
      (fun i=>(hn i).symm)
  have identity : traceMatrix A b=D.transpose*traceMatrix A n*D := by
    apply Matrix.map_injective (f:=j) (IsFractionRing.injective A K)
    have joined : (D.transpose*traceMatrix A n*D).map j =
        D.transpose.map j * (traceMatrix A n).map j * D.map j := by
      change j.mapMatrix (D.transpose*traceMatrix A n*D)=
        j.mapMatrix D.transpose * j.mapMatrix (traceMatrix A n) * j.mapMatrix D
      rw [map_mul,map_mul]
    change (traceMatrix A b).map j=(D.transpose*traceMatrix A n*D).map j
    rw [map_b,joined]
    have trans : D.transpose.map j=(D.map j).transpose := rfl
    change tupleGram (traceForm K V) bk=D.transpose.map j * (traceMatrix A n).map j * D.map j
    rw [trans,map_n]
    change tupleGram (traceForm K V) bk=(D.map j).transpose*tupleGram (traceForm K V) nk*(D.map j)
    rw [←tupleGram_change]
    exact congrArg (tupleGram (traceForm K V)) (funext fun i=>(expand i).symm)
  have nn : (traceMatrix A n).det≠0 := by
    have nd : (traceForm K V).Nondegenerate := by
      apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
      apply bot_unique
      intro x hx
      change x=0
      exact IsReduced.eq_zero x ((Lower6960.TraceSpecialization.trace_radical p small x).mp hx)
    have mat : traceMatrix K nk=(traceForm K V).toMatrix nk := by
      apply Matrix.ext
      intro i l
      rw [traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
    intro zero
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero nk).mp nd
    rw [←mat,←map_n]
    change (j.mapMatrix (traceMatrix A n)).det = 0
    rw [←RingHom.map_det]
    exact zero ▸ map_zero j
  refine ⟨n,D,dn,nn,⟨lift,fun _=>rfl,rfl⟩,identity,?_⟩
  intro v hv
  let x : N := ⟨v,hv⟩
  let c := D.adjugate *ᵥ n.equivFun x
  let u := b.equivFun.symm c
  have ueq : u=∑ i,c i • b i := b.equivFun_symm_apply c
  have mapped : n.equivFun (lift u)=D*ᵥc := by
    rw [ueq,map_sum,map_sum]
    funext i
    simp only [Finset.sum_apply,Basis.equivFun_apply,Matrix.mulVec,dotProduct,D]
    apply Finset.sum_congr rfl
    intro l _
    have csmul : lift (c l • b l) = c l • lift (b l) := lift.toLinearMap.map_smul _ _
    rw [csmul,n.repr.map_smul,Finsupp.smul_apply,smul_eq_mul,mul_comm]
  have by_det : D*ᵥc=D.det • n.equivFun x := by
    change D*ᵥ(D.adjugate*ᵥn.equivFun x)=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
  have lift_eq : lift u=D.det • x := by
    apply n.equivFun.injective
    rw [mapped,by_det,n.equivFun.map_smul]
  refine ⟨u,?_⟩
  have h := congrArg Subtype.val lift_eq
  rw [Subalgebra.coe_smul] at h
  change φ u = (D.det:A) • v at h
  simpa only [Algebra.smul_def] using h
omit [IsPrincipalIdealRing A] [IsReduced V] in
theorem idempotent_integral (v : V) (idem : v^2=v) : IsIntegral A v := by
  refine ⟨Polynomial.X^2-Polynomial.X,monic_X_pow_sub (by rw [degree_X]; norm_num),?_⟩
  simp [idem]
#print axioms reduced_fibre_index
end
end Lower6960.CollisionMarked

end Merged6967_R6960CollisionMarkedFibreIndex

section Merged6967_R6960RetainedAxisTransition
set_option Elab.async false



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
#print axioms chart_finite
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
#print axioms no_axis_torsion
#print axioms chart_free
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
#print axioms native_localization
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisTransition

end Merged6967_R6960RetainedAxisTransition
