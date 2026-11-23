import ProximityPrize.SubmissionLower.ZbIpgzb
import ProximityPrize.SubmissionLower.P5_7_1_7_4_3_4_2Split
set_option Elab.async false
open _root_ renaming Finsupp.single → zhf, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qFQL0Vc
noncomputable section
open Finset
open scoped Classical
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil)
open qfbIfsd (Slot Index baseCap ordCap form)
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
private abbrev Third (A:Equation E) :=Slot A.s (baseCap A 2) (ordCap A 2)
private def thirdSlot (r :Index A) (h:r.1=2) :Third A :=
  cast (congrArg (fun k=>Slot A.s (baseCap A k) (ordCap A k)) h) r.2
private def tweak (z :Direction A) (w:Third A→L) (r :Index A) :L :=
  z r+if h:r.1=2 then w (thirdSlot r h) else 0
omit [Algebra L E] in
private theorem tweak_zero (z :Direction A) :tweak z (fun _=>0)=z := by
  funext r
  simp [tweak]
private def samplePoly (C:Pencil A) (R:z3y (Index A) L) (z :Direction A) :
    z3y (Third A) (Closure E) :=
  R.eval₂ (MvPolynomial.C.comp constants) (fun r =>
    znf (alpha C r+constants (z r)) +
      if h:r.1=2 then z9v (thirdSlot r h) else 0)
private theorem samplePoly_eval (C:Pencil A) (R:z3y (Index A) L)
    (z :Direction A) (w:Third A→L) :
    zY9 (constants ∘ w) (samplePoly C R z)=sample C R (tweak z w) := by
  let j:=zY9 ((constants (E :=E)) ∘ w)
  change j (samplePoly C R z)= _
  rw [samplePoly,MvPolynomial.eval₂_comp_left j,sample]
  have hc:j.comp (MvPolynomial.C.comp constants)=constants := by
    ext a
    simp [j]
  have hv :j ∘ (fun (r :Index A) =>
      znf (alpha C r+constants (z r)) +
        if h:r.1=2 then z9v (thirdSlot r h) else 0) =
      fun r=>alpha C r+constants (tweak z w r) := by
    funext r
    by_cases h:r.1=2 <;> simp [j,z9X,tweak,h,add_assoc]
  rw [hc,hv]
variable {C:Pencil A} {B:Fiber C} {z :Direction A}
private def normalized (i:Fin B.size) (u:Third A) :Closure E :=
  B.x i^u.2.val*B.y i^u.1.val/form (beta C) 2 (B.x i) (B.y i)
private def first (U:Lift B z) (i:Fin B.size) :z3y (Third A) (Closure E) :=
  znf (z2o 1 (value U z i)) -
    ∑ u,znf (normalized (B:=B) i u)*z9v u
private theorem first_eval (U:Lift B z) (i:Fin B.size) (w:Third A→L) :
    zY9 (constants ∘ w) (first U i) =
      z2o 1 (value U (tweak z w) i) := by
  let T:=(PowerSeries.X:Series E)
  let p:Series E := ∑ u:Third A,
    PowerSeries.C (constants (w u))*U.x i^u.2.val*U.y i^u.1.val
  have hform :form (ic C (tweak z w)) 2 (U.x i) (U.y i) =
      form (ic C z) 2 (U.x i) (U.y i)+T*p:= by
    simp only [form,p,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    simp [ic,tweak,T,thirdSlot,add_mul]
    ring
  have hvalue :value U (tweak z w) i=value U z i - T*(p*(scale U i)⁻¹) := by
    unfold value
    rw [hform]
    ring
  rw [hvalue,map_sub]
  have hT:z2o 1 (T*(p*(scale U i)⁻¹)) =
      zbO (p*(scale U i)⁻¹) := by
    simp [T]
  rw [hT,map_mul,PowerSeries.constantCoeff_inv,scale₀]
  simp only [p,map_sum,map_mul,PowerSeries.constantCoeff_C,map_pow,U.x₀,U.y₀,
    first,map_sub,z9X,MvPolynomial.eval_X,Function.comp_apply,
    normalized,div_eq_mul_inv,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ring
private theorem first_ne (U:Lift B z) (i j:Fin B.size) (h:i≠j) :
    first U i - first U j≠0:= by
  obtain ⟨u,hu⟩:=B.separates i j h
  have hsingle : (zhf u 1 :Third A →₀ ℕ)≠0:= by simp
  have hc (k :Fin B.size) :
      (first U k).coeff (zhf u 1) = -normalized (B:=B) k u:= by
    simp [first,MvPolynomial.coeff_C_of_ne_zero hsingle,
      MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,Finsupp.single_eq_single_iff]
  intro hz
  have he :=congrArg (fun f :z3y (Third A) (Closure E) =>
    f.coeff (zhf u 1)) (sub_eq_zero.mp hz)
  exact hu (neg_injective ((hc i).symm.trans (he.trans (hc j))))
theorem bXf (U:Lift B z) (R:z3y (Index A) L)
    (hz :sample C R z≠0) :
    ∃ z' : Direction A,(∀ r,r.1≠2→z' r=z r) ∧
      sample C R z' ≠ 0∧Function.Injective (value U z') := by
  let j:=constants (E :=E)
  let S:=(univ :Finset (Fin B.size×Fin B.size)).filter (fun p=>p.1≠p.2)
  let q:=samplePoly C R z
  let d (p:Fin B.size×Fin B.size) :=first U p.1 - first U p.2
  have hq:q≠0:= by
    intro h
    apply hz
    rw [← tweak_zero z,← samplePoly_eval,show samplePoly C R z=0 from h,map_zero]
  let P:=q * ∏ p∈S,d p
  have hP:P≠0:=mul_ne_zero hq (prod_ne_zero_iff.mpr fun p hp =>
    first_ne U p.1 p.2 (mem_filter.mp hp).2)
  obtain ⟨w,hw⟩ : ∃ w:Third A→L,zY9 (j ∘ w) P≠0:= by
    by_contra! h
    apply hP
    apply MvPolynomial.funext_set (fun _=>Set.range j)
      (fun _=>Set.infinite_range_of_injective j.injective)
    intro x hx
    choose w hw using fun u=>hx u (Set.mem_univ u)
    rw [show x=j ∘ w from funext fun u=>(hw u).symm,map_zero]
    exact h w
  simp only [P,map_mul,map_prod,mul_ne_zero_iff,prod_ne_zero_iff] at hw
  refine ⟨tweak z w,fun r hr=> by simp [tweak,hr],?_,?_⟩
  · exact (samplePoly_eval C R z w) ▸ hw.1
  · intro i k h
    by_contra hne
    have hh:=hw.2 (i,k) (mem_filter.mpr ⟨mem_univ _,hne⟩)
    apply hh
    simp only [d,map_sub,j,first_eval,h,sub_self]
end
end qFQL0Vc
end
section
set_option autoImplicit true
namespace qFQL0Vc
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil relativePolar bix)

def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d →
    ∀ C:Pencil A,Nonempty (Fiber C)
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] {A:Equation E} {C:Pencil A}
    (B:Fiber C) (z :Direction A),Nonempty (Lift B z)
theorem of_children (fiber :c1) (lift:c2) :qfbIfsd.c2 := by
  intro E _ _ A hd C R hR hdet
  obtain ⟨B⟩:=fiber A hd C
  obtain ⟨z,hz⟩:=exists_sample C hR
  obtain ⟨U⟩:=lift B z
  obtain ⟨z',h01,hz',hinj⟩:=bXf U R hz
  let N :=bix C.base (relativePolar C) C.finite
  have hN :N.Monic:= by
    let _:=C.base.toAlgebra
    let _:=C.finite
    exact (Algebra.lmul (RatFunc E) (qNu3xvc.EC A) (relativePolar C)).charpoly_monic
  have hprod:N.map (algebraMap (RatFunc E) (Closure E)) =
      ∏ i,(Polynomial.X-Polynomial.C (zbO (value U z' i))) := by
    simpa only [N,value₀] using B.product
  obtain ⟨n,hn,hdiv⟩:=extract_dvd _ (deform_ne C R z' hz') _ hinj
    (value_root U z' h01 R hdet) N hN hprod
  exact ⟨z',n,hn,hdiv⟩
end
end qFQL0Vc
end
