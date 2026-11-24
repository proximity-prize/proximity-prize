import ProximityPrize.SubmissionLower.R6961RetainedSurfaceDimension
import ProximityPrize.SubmissionLower.R6960RetainedCodimension
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6961.RetainedTwistedRestriction
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes
open RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Lower6961.RetainedSurfaceClass Lower6961.MonicChartProbes Polynomial
open Lower6961.RetainedRestrictionTorus (frame_integral)
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E
def fr (s:Chart) : E := ι (localFrame s false)
abbrev Regular (s:Chart) (i:ℕ) (v:E) := IsIntegral (baseChart s) ((fr s)⁻¹^i*v)
abbrev Over (s t:Chart) (i:ℕ) (v:E) := IsIntegral (overlapRing s t) ((fr s)⁻¹^i*v)
private theorem fn (s:Chart) : (fr s:E)≠0 :=
  (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)
private theorem baseReg {s:Chart} {v:ChartField} (h:v∈baseChart s) : IsIntegral (baseChart s) (ι v:E) :=
  isIntegral_algebraMap (x:=(⟨v,h⟩:baseChart s))
private theorem invFrame (s:Chart) : (localFrame s false)⁻¹∈baseChart s := by
  by_cases i:s.1=true
  · have h:chartCoordinate s.1 RatFunc.X∈baseChart s:=Subring.subset_closure (Or.inr (Or.inl rfl))
    simpa [localFrame,coordinate,axisBit,chartCoordinate,i] using h
  · simp [localFrame,axisBit,i]

private theorem ratio (s t:Chart) : localFrame t false/localFrame s false∈baseChart s := by
  have h:chartCoordinate s.1 RatFunc.X∈baseChart s:=Subring.subset_closure (Or.inr (Or.inl rfl))
  by_cases a:s.1=true <;> by_cases b:t.1=true <;>
    simp [localFrame,coordinate,axisBit,a,b,RatFunc.X_ne_zero] at * <;>
    simpa [chartCoordinate,a] using h

theorem regular_on_overlap (s t:Chart) (i:ℕ) (v:E) (ok:Regular t i v) : Over s t i v := by
  have r:= (order_mono (into_cleared _ (edge s t)) (baseReg (E:=E) (ratio s t))).pow i
  have a:=r.mul (order_mono (chart_cover s t) ok)
  have eq : ι (localFrame t false/localFrame s false)^i * ((fr t)⁻¹^i*v)=(fr s)⁻¹^i*v := by
    rw [map_div₀]; change ((fr t)/(fr s))^i*(((fr t)⁻¹)^i*v)=_
    rw [div_eq_mul_inv,mul_pow]
    calc _ = ((fr t)^i*((fr t)⁻¹)^i)*(((fr s)⁻¹)^i*v) := by ring
         _ = _ := by rw [←mul_pow,mul_inv_cancel₀ (fn t),one_pow,one_mul]
  rwa [eq] at a

theorem cancel_equation [FiniteDimensional ChartField E] (s t:Chart) (a:baseChart s) (an:a≠0)
    (cop : IsRelPrime a (edge s (opposite s))) (y:E)
    (tw : IsIntegral (overlapRing s t) (algebraMap (baseChart s) E a*y))
    (yes : IsIntegral torus y) : IsIntegral (overlapRing s t) y := by
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let g:=edge s (opposite s); let h:=edge s t; let f:=algebraMap A E
  obtain ⟨n,hn⟩:=clear_torus s y yes
  obtain ⟨m,hm⟩:=localize_integral A _ h (edge_ne s t) le_rfl _ tw
  change IsIntegral A (f g^n*y) at hn
  change IsIntegral A (f h^m*(f a*y)) at hm
  have gn : g≠0 := fun eq=>edge_ne s (opposite s) (congrArg Subtype.val eq)
  have clean : IsIntegral A (f h^m*y) := by
    apply Lower6960.NormalizedFiber.integral_of_coprime_clearings ChartField an (pow_ne_zero _ gn) cop.pow_right _
    · change IsIntegral A (f a*(f h^m*y)); convert hm using 1 <;> ring
    · change IsIntegral A (f (g^n)*(f h^m*y))
      have v:=(isIntegral_algebraMap (A:=E) (x:=h^m)).mul hn
      convert v using 1 <;> simp only [map_pow] <;> ring
  let T:=overlapRing s t
  have hi : (boundary s t)⁻¹∈T := ⟨1,by simp [edge_ne]⟩
  have inv : IsIntegral T ((f h)⁻¹) := by
    change IsIntegral T (ι (boundary s t))⁻¹
    rw [←map_inv₀]; exact isIntegral_algebraMap (x:=(⟨_,hi⟩:T))
  have hnz : f h≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s t)
  simpa only [←mul_assoc,←mul_pow,inv_mul_cancel₀ hnz,one_pow,one_mul] using
    (inv.pow m).mul (order_mono (into_cleared A h) clean)

private theorem axis_cancel [FiniteDimensional ChartField E] (s t:Chart) (x:L) (nx:x≠0) (y:E)
    (tw : IsIntegral (overlapRing s t) (algebraMap (baseChart s) E (xcut s x)*y))
    (yes : IsIntegral torus y) : IsIntegral (overlapRing s t) y := by
  have : UniqueFactorizationMonoid (baseChart s) := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  apply cancel_equation s t (xcut s x) _ _ y tw yes
  · intro h
    have eq:=congrArg (fun p:baseChart s=>(p:ChartField)) h
    exact (div_ne_zero (divisor_ne false x) (localFrame_ne s false)) ((xcut_value s x).symm.trans eq)
  · exact (IsRelPrime.mul_right_iff.mp (boundary_rel s x 1 nx one_ne_zero)).1.symm

/-- A twist-i transition that splits on the abscissa line is the sum of a
twist-i boundary and the line equation times a twist-(i-1) transition. -/
theorem descend_line [FiniteDimensional ChartField E] (i:ℕ) (x:L) (nx:x≠0) (u:Chart→E)
    (reg:∀ s t, Over s t (i+1) (u s-u t)) (v:Bool→E) (data:LineData false x u v) :
    ∃ w l:Chart→E, (∀ s,IsIntegral torus (w s)) ∧ (∀ s,Regular s (i+1) (l s)) ∧
      (∀ s t,Over s t i (w s-w t)) ∧ ∀s, u s-ι (divisor false x)*w s=l s+(u (false,false)-v false) := by
  let c:=u (false,false)-v false
  let D:=ι (divisor false x)
  have dn : D≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne false x)
  have locals (s:Chart) : ∃ l:E, Regular s (i+1) l ∧ Congruent false x (u s-c) l := by
    let t:=reference false s.2
    have same : axisBit s (!false)=axisBit t (!false) := rfl
    let candidate:=u s-u t+v s.2
    have re: IsIntegral (overlapRing s t) ((fr s)⁻¹^(i+1)*candidate) := by
      rw [show (fr s)⁻¹^(i+1)*candidate=(fr s)⁻¹^(i+1)*(u s-u t)+(fr s)⁻¹^(i+1)*v s.2 by dsimp [candidate];ring]
      apply (reg s t).add
      have inv:IsIntegral (baseChart s) ((fr s:E)⁻¹) := by rw [fr,←map_inv₀];exact baseReg (invFrame s)
      exact ((order_mono (into_cleared _ (edge s t)) inv).pow _).mul (order_mono (chart_cover s t) (data.1 s.2))
    obtain ⟨q,iq,r,ir,eq⟩:=line_representative false x nx s t same _ re
    let l:=fr s^(i+1)*q
    have cancel : (fr s:E)⁻¹^(i+1)*fr s^(i+1)=1 := by rw [←mul_pow,inv_mul_cancel₀ (fn s),one_pow]
    have cg : Congruent false x candidate l := by
      refine ⟨fr s^(i+1)*r,((Lower6961.RetainedRestrictionTorus.frame_integral s false).1.pow _).mul ir,?_⟩
      have zz := congrArg (fun h:E=>fr s^(i+1)*h) eq
      change fr s^(i+1)*((fr s)⁻¹^(i+1)*candidate-q)=fr s^(i+1)*(ι (divisor false x)*r) at zz
      dsimp only [l]
      rw [mul_sub,←mul_assoc,mul_comm (fr s^(i+1)) _,cancel,one_mul] at zz
      rw [zz]; ring
    have atref : Congruent false x (u (false,false)-u t) (v false-v s.2) := by
      cases h:s.2
      · have e:t=(false,false) := by simp [t,reference,h]
        rw [e,sub_self,sub_self]; exact Congruent.refl _ _ _
      · simpa only [t,h] using data.2
    obtain ⟨r',ir',er⟩:=atref.symm
    refine ⟨l,?_,Congruent.trans (v:=candidate) ⟨r',ir',?_⟩ cg⟩
    · change IsIntegral _ ((fr s)⁻¹^(i+1)*(fr s^(i+1)*q)); rw [←mul_assoc,cancel,one_mul]; exact iq
    · rw [←er]; dsimp only [candidate,c]; abel
  choose l il coef icoef val using locals
  refine ⟨coef,l,icoef,il,fun s t=>?_,fun s=>by rw [←val]; dsimp [c]; abel⟩
  have residual : (u s-u t)-(l s-l t)=D*(coef s-coef t) := by
    rw [mul_sub]; change _=ι (divisor false x)*coef s-ι (divisor false x)*coef t
    rw [←val,←val]; abel
  have here:=order_mono (into_cleared _ (edge s t)) (il s)
  have both: IsIntegral (overlapRing s t) ((fr s)⁻¹^(i+1)*((u s-u t)-(l s-l t))) := by
    rw [mul_sub,mul_sub _ (l s) (l t)]
    exact (reg s t).sub (here.sub (regular_on_overlap s t _ _ (il t)))
  apply axis_cancel s t x nx _
  · have cut : algebraMap (baseChart s) E (xcut s x)=D/fr s := by
      change ι (xcut s x:ChartField)=_;rw [xcut_value,map_div₀];rfl
    rw [residual,pow_succ] at both
    rw [cut,div_eq_mul_inv]
    convert both using 1 <;> ring
  · have inv:IsIntegral torus (fr s:E)⁻¹ := by rw [fr,←map_inv₀];exact isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).2⟩:torus))
    exact (inv.pow _).mul ((icoef s).sub (icoef t))

#print axioms descend_line
end Lower6961.RetainedTwistedRestriction
