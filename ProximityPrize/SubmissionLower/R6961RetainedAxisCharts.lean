import ProximityPrize.SubmissionLower.R6961RetainedCrossingComparison
import ProximityPrize.SubmissionLower.R6960LineEulerFree

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
open Lower6961.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]

/-- The orientation places the fixed coordinate outside and the variable along the
line inside the iterated polynomial ring. The latter may be reciprocal. -/
def oriented (j b : Bool) : Lower6960.PlaneConstants.Plane L ≃+*baseChart (reference j b) :=
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

private theorem eval_fixed (j:Bool) (c:L) (b:Bool) (P:Lower6960.PlaneConstants.Plane L) :
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

/-- The finite chart of the selected line is the image of the surface order, as a
module over the ordinary polynomial ring of the line. -/
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
end Lower6961.RetainedSurfaceClass
