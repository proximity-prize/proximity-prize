import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceDimension
import ProximityPrize.SubmissionLower.R6960RetainedAxisTransition

-- merged module R6960RetainedCodimension
section Merged_R6960RetainedCodimension

noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedCodimension
open Module Submodule LinearMap
variable {k U V W : Type*} [Field k] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def Fits (P : Submodule k U) (n:ℕ) : Prop :=
  FiniteDimensional k (U ⧸ P) ∧ finrank k (U ⧸ P)≤n

theorem from_map [FiniteDimensional k V] (f : U→ₗ[k]V) (P:Submodule k U)
    (ker : f.ker=P) {n:ℕ} (bound:finrank k V≤n) : Fits P n := by
  subst P
  let e:=f.quotKerEquivRange
  exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    (e.finrank_eq.trans_le (Submodule.finrank_le f.range)).trans bound⟩

/-- An obstruction vanishing on a line comes from the preceding twist.
The cokernel therefore grows by at most the obstruction dimension of that line. -/
theorem step [FiniteDimensional k W] (P:Submodule k U) (Q:Submodule k V)
    (f:U→ₗ[k]V) (r:V→ₗ[k]W) (inc:P≤Q.comap f)
    (lift:∀ x∈r.ker,∃ y, x-f y∈Q) {n t:ℕ} (old:Fits P n) (width:finrank k W≤t) :
    Fits Q (n+t) := by
  obtain ⟨fin,dim⟩:=old
  obtain ⟨sectionMap,inverse⟩:=r.rangeRestrict.exists_rightInverse_of_surjective r.range_rangeRestrict
  let cover := (P.mapQ Q f inc).coprod (Q.mkQ.comp sectionMap)
  have sur : Function.Surjective cover := by
    intro x
    obtain ⟨v,rfl⟩:=Q.mkQ_surjective x
    let z:=r.rangeRestrict v
    have rz : r (sectionMap z)=r v := congrArg Subtype.val (LinearMap.congr_fun inverse z)
    have kv : v-sectionMap z∈r.ker := by rw [mem_ker,map_sub,rz,sub_self]
    obtain ⟨y,hy⟩:=lift _ kv
    refine ⟨(P.mkQ y,z),?_⟩
    change P.mapQ Q f inc (P.mkQ y)+Q.mkQ (sectionMap z)=Q.mkQ v
    change Q.mkQ (f y)+Q.mkQ (sectionMap z)=Q.mkQ v
    rw [←map_add]
    apply (Submodule.Quotient.eq Q).mpr
    convert Q.neg_mem hy using 1 <;> abel
  have :=FiniteDimensional.of_surjective cover sur
  have b:=LinearMap.finrank_le_finrank_of_surjective sur
  rw [Module.finrank_prod] at b
  exact ⟨inferInstance,b.trans (Nat.add_le_add dim ((Submodule.finrank_le r.range).trans width))⟩

#print axioms from_map
#print axioms step

theorem pullback [FiniteDimensional k U] (P:Submodule k V) (f:U→ₗ[k]V) {n:ℕ} (size:Fits P n) :
    finrank k U≤n+finrank k (P.comap f) := by
  obtain ⟨finite,dim⟩:=size
  let q:=P.mkQ.comp f
  have ker:q.ker=P.comap f := by
    ext v
    change P.mkQ (f v)=0 ↔ _
    exact Submodule.Quotient.mk_eq_zero _
  have r:=q.finrank_range_add_finrank_ker
  rw [ker] at r
  exact r ▸ Nat.add_le_add_right ((Submodule.finrank_le q.range).trans dim) _

#print axioms pullback
theorem large_subspace [FiniteDimensional k U] (P:Submodule k V) (f:U→ₗ[k]V) {n:ℕ} (size:Fits P n) :
    ∃ D:Submodule k U,finrank k U≤n+finrank k D ∧ ∀u:D,f u.val∈P :=
  ⟨P.comap f,pullback P f size,fun u=>u.property⟩
end Lower6960.RetainedCodimension

end
end Merged_R6960RetainedCodimension

-- merged module R6960RetainedTwistedRestriction
section Merged_R6960RetainedTwistedRestriction
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6960.RetainedTwistedRestriction
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent MonicChartProbes
open RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Lower6960.RetainedSurfaceClass Lower6960.MonicChartProbes Polynomial
open Lower6960.RetainedRestrictionTorus (frame_integral)
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
    apply NormalizedFiber.integral_of_coprime_clearings ChartField an (pow_ne_zero _ gn) cop.pow_right _
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
      refine ⟨fr s^(i+1)*r,((Lower6960.RetainedRestrictionTorus.frame_integral s false).1.pow _).mul ir,?_⟩
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
end Lower6960.RetainedTwistedRestriction

end
end Merged_R6960RetainedTwistedRestriction

-- merged module R6960RetainedTwistedBudget
section Merged_R6960RetainedTwistedBudget
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwistedRestriction
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (chartSpace congr_of_eq)
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def charts (i:ℕ) : Submodule L (Chart→Tor E) where
  carrier:={u | ∀ s t,Over s t i ((u s:E)-(u t:E))}
  zero_mem':=fun s t=>by simpa [Over] using (isIntegral_zero (R:=overlapRing s t) (B:=E))
  add_mem' {u v} hu hv s t:=by
    change IsIntegral _ (_*(((u s:E)+v s)-((u t:E)+v t)))
    convert (hu s t).add (hv s t) using 1 <;> ring
  smul_mem' r u hu s t:=by
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u s:E)-ι (constants r)*(u t:E)))
    have scalar:IsIntegral (overlapRing s t) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))
    convert scalar.mul (hu s t) using 1 <;> ring

def trivial (i:ℕ) : Submodule L (charts E i) where
  carrier:={u | ∃c:E,∀s,Regular s i ((u.1 s:E)-c)}
  zero_mem':=⟨0,fun s=>by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))⟩
  add_mem' {u v} hu hv:=by
    obtain ⟨a,ha⟩:=hu;obtain ⟨b,hb⟩:=hv
    refine ⟨a+b,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(((u.1 s:E)+v.1 s)-(a+b)))
    convert (ha s).add (hb s) using 1 <;> ring
  smul_mem' r u hu:=by
    obtain ⟨a,ha⟩:=hu; refine ⟨ι (constants r)*a,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u.1 s:E)-ι (constants r)*a))
    have scalar : IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    convert scalar.mul (ha s) using 1 <;> ring

private def shift (i:ℕ) (x:L) : charts E i →ₗ[L] charts E (i+1) where
  toFun u:=⟨fun s=>cut E false x*u.1 s, fun s t=>by
    have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
      have p : IsIntegral (baseChart s) (algebraMap (baseChart s) E (xcut s x)):=isIntegral_algebraMap
      change IsIntegral (baseChart s) (ι (xcut s x:ChartField)) at p
      rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
    change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*(u.1 t:E)))
    have loc : IsIntegral (overlapRing s t) (ι (divisor false x)*(fr s:E)⁻¹) :=
      order_mono (into_cleared _ (edge s t)) d
    convert loc.mul (u.property s t) using 1 <;> rw [pow_succ] <;> ring⟩
  map_add' a b:=by apply Subtype.ext; funext s; exact mul_add _ _ _
  map_smul' r a:=by
    apply Subtype.ext; funext s; apply Subtype.ext
    change ι (divisor false x)*(ι (constants r)*(a.1 s:E))=ι (constants r)*(ι (divisor false x)*(a.1 s:E))
    ring

private def lineMap (i:ℕ) (x:L) : charts E i→ₗ[L] LineObstructions E false x :=
  let ev (s:Chart) : (Chart→Tor E) →ₗ[L] Tor E := LinearMap.proj s
  let values := ev (false,false)-ev (false,true)
  (chartImage E false x false⊔chartImage E false x true).mkQ.comp
    ((red E false x).comp (values.comp (charts E i).subtype))

abbrev Budget (i n:ℕ) := RetainedCodimension.Fits (k:=L) (U:=↥(charts E i)) (trivial E i) n

theorem budget_subspace {J:Type} [Fintype J] (i n:ℕ) (H:Budget E i n)
    (f:(J→L) →ₗ[L] charts E i) :
    ∃ D:Submodule L (J→L),finrank L (J→L)≤n+finrank L D ∧
      ∀v:D,∃c:E,∀s,Regular s i (((f v.val).val s:E)-c) := by
  exact @RetainedCodimension.large_subspace L (J→L) ↥(charts E i) inferInstance inferInstance
    inferInstance (charts E i).addCommGroup (charts E i).module inferInstance
    (trivial E i) f n H

private theorem shift_trivial (i:ℕ) (x:L) : trivial E i ≤ (trivial E (i+1)).comap (shift E i x) := by
  rintro u ⟨c,hc⟩
  refine ⟨ι (divisor false x)*c,fun s=>?_⟩
  have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
    have p : IsIntegral (baseChart s) (ι (xcut s x:ChartField):E) := isIntegral_algebraMap (x:=xcut s x)
    rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*c))
  convert d.mul (hc s) using 1 <;> rw [pow_succ] <;> ring

theorem grow [FiniteDimensional ChartField E] (i:ℕ) (x:L) (nx:x≠0)
    [FiniteDimensional L (LineObstructions E false x)] {n t:ℕ}
    (previous:Budget E i n)
    (width:finrank L (LineObstructions E false x)≤t) :
    Budget E (i+1) (n+t) := by
  apply RetainedCodimension.step (k:=L) (U:=↥(charts E i)) (V:=↥(charts E (i+1))) (W:=LineObstructions E false x)
    _ _ (shift E i x) (lineMap E (i+1) x) (shift_trivial E i x) _ previous width
  intro u hu
  change Submodule.Quotient.mk (p:=chartImage E false x false⊔chartImage E false x true)
    (red E false x (u.1 (false,false)-u.1 (false,true)))=0 at hu
  have res := (Submodule.Quotient.mk_eq_zero _).mp hu
  obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp res
  let reps (j:Bool):E:=if j then -(b:E) else a
  have data:LineData false x (fun s=>(u.1 s:E)) reps := by
    refine ⟨fun j=>?_,?_⟩
    · cases j
      · exact ha
      · exact (show IsIntegral (baseChart (reference false true)) (b:E) from hb).neg
    · have e : red E false x (u.1 (false,false)-u.1 (false,true))=red E false x (a+b) :=
        eq.symm.trans (map_add ..).symm
      change Congruent false x ((u.1 (false,false):E)-u.1 (false,true)) ((a:E)- -(b:E))
      rw [sub_neg_eq_add]
      exact Lower6960.RetainedSurfaceClass.congr_of_eq E false x _ _ e
  obtain ⟨w,l,iw,lr,wr,eq⟩:=descend_line i x nx (fun s=>(u.1 s:E)) u.property reps data
  let y:charts E i:=⟨fun s=>⟨w s,iw s⟩,wr⟩
  refine ⟨y,u.1 (false,false)-reps false,fun s=>?_⟩
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(((u.1 s:E)-ι (divisor false x)*w s)-((u.1 (false,false):E)-reps false)))
  rw [eq,add_sub_cancel_right]
  exact lr s

open RetainedCompression (Curve ordinate view height heightCap MarkedBand)

theorem initial (B:MarkedBand) (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<B.maxOrd)
    (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [FiniteDimensional L (Paired E x z)] {b:ℕ}
    (size:finrank L (Paired E x z)≤b) : Budget E 0 b := by
  have spaces:charts E 0=potentials E := by
    ext u; change (∀s t,Over s t 0 _ )↔_
    simp only [Over,pow_zero,one_mul]; rfl
  let e:=LinearEquiv.ofEq _ _ spaces
  let f₀:=(rawMap E x z).comp e.toLinearMap
  apply RetainedCodimension.from_map f₀ _ _ size
  ext u
  change e u∈(rawMap E x z).ker ↔ ∃ c:E,∀s, Regular s 0 ((u.1 s:E)-c)
  rw [restriction_kernel E B f ir lo hi bounded basis root x z nx nz]
  simp only [Regular,pow_zero,one_mul]; rfl

#print axioms grow
#print axioms initial

/-- Uniform surface bound for every positive abscissa twist of the same actual
factor. The degrees s,t are measured on its own two specialized chart orders. -/
theorem actual_all_twists (B:MarkedBand) (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<B.maxOrd)
    (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
        (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)),
        (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
        (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
        Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧ IsReduced (Crossing E x z) ∧
        ∀ i:ℕ, Budget E i (s+(i+1)*t) := by
  have : FiniteDimensional ChartField E := basis.finite
  have hiP : f.degreeOf ordinate < K1.p := hi.trans B.small_E
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hiP basis root
  obtain ⟨x,z,nx,nz,⟨B_bas⟩,red⟩:=actual_crossing E f ir lo hiP basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B_bas
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,base⟩:=paired_bound E x z nx nz xf xi zf zi
  obtain ⟨fg,fo,d,ed,index⟩:=native_euler E false x nx xf xi
  have de : d= -(t:ℤ) := WithBot.coe_injective (ed.symm.trans dt)
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fg
  have inject:=global_eval_injective E false x z nx nz xf
  have eRank := LinearMap.finrank_le_finrank_of_injective inject
  change finrank L (LineGlobals E false x)≤finrank L (Crossing E x z) at eRank
  have mrank:=node_rank_le E false x z nx nz xf
  have line : finrank L (LineObstructions E false x)≤t := by omega
  refine ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B_bas⟩,red,fun i=>?_⟩
  induction i with
  | zero => simpa only [zero_add,one_mul] using initial E B f ir lo hi bounded basis root x z nx nz base
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,Nat.add_assoc] using grow E i x nx ih line

#print axioms actual_all_twists
end Lower6960.RetainedTwistedRestriction

end
end Merged_R6960RetainedTwistedBudget

-- merged module R6960MarkedPrincipalParts
section Merged_R6960MarkedPrincipalParts
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open RetainedTwistedRestriction RetainedSurfaceClass Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open Lower6960.RetainedRestrictionTorus (frame_integral)
variable {E:Type} [Field E] [Algebra ChartField E] {J:Type} [Fintype J]
local notation "ι" => algebraMap ChartField E

scoped instance constantFieldAlgebra (E:Type) [Field E] [Algebra ChartField E] : Algebra L E :=
  ((algebraMap ChartField E).comp constants).toAlgebra
open scoped Lower6960.MarkedEvaluation

def principalValue (p:J→Chart→E) (s:Chart) : (J→L) →ₗ[L] E :=
  (Pi.basisFun L J).constr L (fun j=>p j s)

private def regularSpace (i:ℕ) (s:Chart) : Submodule L E where
  carrier:={v|Regular s i v}
  zero_mem':=by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))
  add_mem' {u v} a b:=by change IsIntegral _ (_*(u+v)); rw [mul_add];exact a.add b
  smul_mem' r v a:=by
    have ci:IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*v))
    rw [mul_left_comm]; exact ci.mul a

private theorem anchored (i:ℕ) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ family : (J→L) →ₗ[L] charts E i, ∀ v s,
      ((family v).val s:E)=principalValue p s v-principalValue p (false,false) v := by
  classical
  let a:Chart:=(false,false)
  have regular (j:J) (s:Chart) : IsIntegral torus (p j s-p j a) := by
    have m:=order_mono (to_torus s a) (compatible j s a)
    have inv:= (Lower6960.RetainedRestrictionTorus.frame_integral (E:=E) s false).1.pow i
    have h:=inv.mul m
    change IsIntegral torus (fr s^i*((fr s)⁻¹^i*(p j s-p j a))) at h
    simpa only [←mul_assoc,←mul_pow,mul_inv_cancel₀
      ((map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)),one_pow,one_mul,fr] using h
  let transition (j:J) : charts E i := ⟨fun s=>⟨_,regular j s⟩,fun s t=>by
    change Over s t i ((p j s-p j a)-(p j t-p j a)); rw [sub_sub_sub_cancel_right]; exact compatible j s t⟩
  let family:=(Pi.basisFun L J).constr L transition
  let ev (s:Chart) : charts E i→ₗ[L]E :=
    {toFun:=fun v=>(v.val s:E),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
  have identity (s:Chart) : (ev s).comp family=principalValue p s-principalValue p a := by
    apply (Pi.basisFun L J).ext
    intro j
    rw [LinearMap.comp_apply,LinearMap.sub_apply]
    change ev s (((Pi.basisFun L J).constr L transition) _) =
      ((Pi.basisFun L J).constr L (fun j=>p j s)) _ - ((Pi.basisFun L J).constr L (fun j=>p j a)) _
    simp only [Basis.constr_basis];rfl
  exact ⟨family,fun v s=>LinearMap.congr_fun (identity s) v⟩

private theorem linear_choices {k V U I:Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (eval:I→U→ₗ[k]V) (S:I→Submodule k V) (works:∀u,∃v,∀s,eval s u-v∈S s) :
    ∃ value:U→ₗ[k]V,∀ u s,eval s u-value u∈S s := by
  classical
  let B:=Module.finBasis k U
  choose lift localReg using fun j=>works (B j)
  let value:=B.constr k lift
  refine ⟨value,fun u s=>?_⟩
  let diff:=eval s-value
  have into (j) : diff (B j)∈S s := by
    change eval s (B j)-value (B j)∈S s
    rw [show value (B j)=lift j from B.constr_basis ..]
    exact localReg j s
  change diff u∈S s
  have m : diff (∑ j,B.repr u j • B j) ∈ S s := by
    rw [map_sum]
    exact (S s).sum_mem (fun j _=>by rw [map_smul]; exact (S s).smul_mem _ (into j))
  rwa [B.sum_repr] at m

/-- From local principal parts on the actual surface, construct honest meromorphic
functions in its root field. At most the surface codimension is lost. -/
theorem lift_principal_parts (i n:ℕ) (budget:Budget E i n) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ D:Submodule L (J→L), ∃ value:D→ₗ[L]E,
      Fintype.card J≤n+finrank L D ∧ ∀ (v:D) s,Regular s i (principalValue p s v.val-value v) := by
  classical
  let a:Chart:=(false,false)
  obtain ⟨family,coord⟩:=anchored i p compatible
  obtain ⟨D,count,corr⟩:=budget_subspace E i n budget family
  have works (v:D) : ∃ c:E,∀s,Regular s i (principalValue p s v.val-c) := by
    have hv : ∃ c:E,∀s,Regular s i (((family v.val).val s:E)-c):=corr v
    obtain ⟨c,hc⟩:=hv
    refine ⟨principalValue p a v.val+c,fun s=>?_⟩
    have h:Regular s i (((family v.val).val s:E)-c):=hc s
    rw [coord] at h
    rwa [sub_add_eq_sub_sub]
  have finD : FiniteDimensional L D := FiniteDimensional.of_injective
    (D.subtype : D→ₗ[L](J→L)) Subtype.val_injective
  obtain ⟨value,ok⟩:=linear_choices (k:=L) (U:=↥D) (V:=E) (I:=Chart)
    (fun s=>(principalValue p s).comp D.subtype) (regularSpace i) works
  refine ⟨D,value,?_,?_⟩
  · simpa only [Module.finrank_pi] using count
  · exact fun v s=>ok v s

#print axioms lift_principal_parts
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedPrincipalParts

-- merged module R6960MarkedWordResidues
section Merged_R6960MarkedWordResidues
set_option synthInstance.maxHeartbeats 200000
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent RetainedRestrictionTorus
open RetainedSurfaceClass RetainedTwistedRestriction ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass Lower6960.MarkedEvaluation
open Lower6960.RetainedTwistedRestriction (regular_on_overlap)
open Lower6960.RetainedSurfaceClass (congr_of_eq)
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E
def torFrame (E:Type) [Field E] [Algebra ChartField E] (s:Chart) : Tor E :=
  ⟨fr s,isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).1⟩:torus))⟩
def FibreSection (i:ℕ) (z:L) (v:Axis E true z) : Prop :=
  ∀ b:Bool, ∃u:Tor E, IsIntegral (baseChart (reference true b)) (u:E) ∧
    red E true z ((torFrame E (reference true b))^i*u)=v
private theorem equal_residues (j c) (u v:Tor E) (h:Congruent j c (u:E) (v:E)) :
    red E j c u=red E j c v := by
  obtain ⟨r,ir,eq⟩:=h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨⟨r,ir⟩,Subtype.ext eq⟩)
theorem word_principal_parts [FiniteDimensional ChartField E]
    (i:ℕ) (z:L) (nz:z≠0) (v:Axis E true z) (sectionOnLine:FibreSection i z v) :
    ∃ w:Chart→Tor E, (∀s,Regular s i (w s:E)) ∧ (∀s, red E true z (w s)=v) ∧
      ∀s t,Over s t i ((w s:E)/ι (divisor true z)-(w t:E)/ι (divisor true z)) := by
  classical
  have atChart (s:Chart):∃w:Tor E,Regular s i (w:E) ∧ red E true z w=v := by
    let t:=reference true s.1
    obtain ⟨a,ia,eq⟩:=sectionOnLine s.1
    have parallel:axisBit s (!true)=axisBit t (!true):=rfl
    obtain ⟨q,iq,matchValue⟩:=line_representative true z nz s t parallel (a:E) (order_mono (chart_cover s t) ia)
    let Q:Tor E:=⟨q,order_mono (base_torus s) iq⟩
    have frameEq:torFrame E t=torFrame E s := rfl
    have eqQ:=equal_residues true z a Q matchValue
    let w:=torFrame E s^i*Q
    refine ⟨w,?_,?_⟩
    · change IsIntegral _ ((fr s)⁻¹^i*(fr s^i*q))
      have nzf : (fr s:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)
      rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ nzf,one_pow,one_mul]
      exact iq
    · change Ideal.Quotient.mk _ ((torFrame E s)^i*Q)=v
      change Ideal.Quotient.mk _ a=Ideal.Quotient.mk _ Q at eqQ
      rw [map_mul,←eqQ,←map_mul,←frameEq];exact eq
  choose w regular value using atChart
  refine ⟨w,regular,value,fun s t=>?_⟩
  let D:=ι (divisor true z)
  let V:=(fr s)⁻¹^i*((w s:E)/D-(w t:E)/D)
  have dn:D≠0:=(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne _ _)
  have zn:zcut s z≠0:=by
    intro zero
    exact (div_ne_zero (divisor_ne true z) (localFrame_ne s true))
      ((zcut_value s z).symm.trans (congrArg (fun a:baseChart s=>(a:ChartField)) zero))
  have : UniqueFactorizationMonoid (baseChart s) := (MonicChartProbes.planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  apply cancel_equation s t (zcut s z) zn (IsRelPrime.mul_right_iff.mp (boundary_rel s 1 z one_ne_zero nz)).2.symm V
  · have lhs:=order_mono (into_cleared _ (edge s t)) (regular s)
    have rhs:=Lower6960.RetainedTwistedRestriction.regular_on_overlap s t i _ (regular t)
    have base:(localFrame s true)⁻¹∈baseChart s := by
      have h:chartCoordinate s.2 scalarCoordinate∈baseChart s:=Subring.subset_closure (Or.inr (Or.inr rfl))
      by_cases ht:s.2=true <;> simp [localFrame,axisBit,coordinate,ht,chartCoordinate] at * <;> assumption
    have inv:IsIntegral (baseChart s) (ι ((localFrame s true)⁻¹):E) := isIntegral_algebraMap (x:=(⟨_,base⟩:baseChart s))
    have reg:= (order_mono (into_cleared _ (edge s t)) inv).mul (lhs.sub rhs)
    change IsIntegral _ (ι (zcut s z:ChartField)*V)
    rw [zcut_value,map_div₀]
    have eq : (D/ι (localFrame s true))*V = ι ((localFrame s true)⁻¹)*((fr s)⁻¹^i*(w s:E)-(fr s)⁻¹^i*(w t:E)) := by
      dsimp only [V];rw [map_inv₀];field_simp [dn,(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s true)]
      <;> ring
    rw [eq];exact reg
  · obtain ⟨r,ir,rr⟩:=Lower6960.RetainedSurfaceClass.congr_of_eq E true z (w s) (w t) ((value s).trans (value t).symm)
    have inv : IsIntegral torus (fr s:E)⁻¹ := by rw [fr,←map_inv₀];exact isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).2⟩:torus))
    change IsIntegral torus ((fr s)⁻¹^i*((w s:E)/D-(w t:E)/D))
    rw [←sub_div,rr,show ι (divisor true z)=D from rfl,mul_div_cancel_left₀ _ dn]
    exact (inv.pow _).mul ir
#print axioms word_principal_parts
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedWordResidues
