import ProximityPrize.SubmissionLower.ZQ2Yete
set_option Elab.async false
open _root_ renaming Algebra.subset_adjoin → zkk, IsFractionRing.injective → zxb, IsLocalization.Away.algebraMap_isUnit → z4z, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_eq → zaz, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace q53i3jb
noncomputable section
open Polynomial
open cu (L FX)
open E7 (CurvePlace)
open P5_7_7 (phys)
open qNu3xvc
open qoCymac
variable {E :Type} [Field E] [Algebra L E]
omit [Algebra L E] in
theorem eval_false (A:Equation E) (g:E[X][X]) :
    KM A false g=a7W A g:= by
  change g.eval₂ ((a7W A).comp C) (a7W A z7y)= _
  rw [← hom_eval₂,eval₂_C_X]
private def atY (A:Equation E) (w:CurvePlace L E) :Chart A w false :=
  ⟨jU A false,zkk (Or.inr (by simp))⟩
private def cK (A:Equation E) (w:CurvePlace L E) :Chart A w false :=
  ⟨jet A false,zkk (Or.inr (by simp))⟩
private def coeffIn (A:Equation E) (w:CurvePlace L E) :Integers w →+* Chart A w false :=
  ((seed A).comp (inc w)).codRestrict (Chart A w false).toSubring (fun a=>(aee A w false a).property)
def evalIn (A:Equation E) (w:CurvePlace L E) :
    (Integers w)[X][X] →+* Chart A w false :=
  eval₂RingHom (eval₂RingHom (coeffIn A w) (xAt A w false)) (atY A w)
theorem coe_evalIn (A:Equation E) (w:CurvePlace L E) (g: (Integers w)[X][X]) :
    (evalIn A w g:EC A)=a7W A (map₂ (inc w) g) := by
  change ((Chart A w false).val.toRingHom.comp (evalIn A w)) g=((a7W A).comp (map₂ (inc w))) g
  congr 1
  apply z86
  · intro a
    have h: ((Chart A w false).val.toRingHom.comp
          (eval₂RingHom (coeffIn A w) (xAt A w false))) =
        ((a7W A).comp C).comp (mapRingHom (inc w)) := by
      apply z86
      · intro c
        simp only [zQb,coe_eval₂RingHom,eval₂_C,coe_mapRingHom,map_C]
        rfl
      · simp only [zQb,coe_eval₂RingHom,eval₂_X,coe_mapRingHom,map_X]
        rfl
    simpa only [zQb,evalIn,coe_eval₂RingHom,eval₂_C,map₂,
      coe_mapRingHom,map_C] using RingHom.congr_fun h a
  · simp [evalIn,atY,jU]
private theorem map_inv_unit {R F:Type} [CommRing R] [Field F] (j:R →+* F) (u:Rˣ) :
    j (↑u⁻¹:R)=(j (↑u:R))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
private theorem div_mem_range {R F:Type} [CommRing R] [Field F]
    (j:R →+* F) (d b:R) (hd:IsUnit d) :j b/j d∈j.range := by
  obtain ⟨u,rfl⟩:=hd
  exact ⟨b * ↑u⁻¹,by rw [map_mul,map_inv_unit,div_eq_mul_inv]⟩
theorem affine_map (A:Equation E) (w:CurvePlace L E)
    (f b d: (Integers w)[X][X])
    (hf :map₂ (inc w) f=A.f)
    (hunit : ∃ j k,w.value (((f.coeff j).coeff k :Integers w) :E)=1)
    (hb:map₂ (inc w) b=physicalDerivative A.f)
    (hd:map₂ (inc w) d=A.f.derivative)
    (red:Integers w →+* L) (P:L[X])
    (hconstant : ∀ a :L,red ⟨algebraMap L E a,by
      by_cases ha :a=0
      · simp [ha]
      · exact (w.on_constants a ha).le⟩=a)
    (hroot :f.eval₂ (mapRingHom red) P=0)
    (hsimple :d.eval₂ (mapRingHom red) P≠0)
    (hjet : -(b.eval₂ (mapRingHom red) P) =
      P.derivative*d.eval₂ (mapRingHom red) P) :
    ∃ φ:Chart A w false →ₐ[L] FX,
      (∀ g,φ (evalIn A w g)=phys (g.eval₂ (mapRingHom red) P)) ∧
      φ (cK A w)=phys P.derivative := by
  obtain ⟨i,hi,him⟩:=eval_lift_injective A w f hf hunit
  let t:=phys.comp (AdjoinRoot.lift (mapRingHom red) P hroot)
  let s :=AdjoinRoot.mk f d
  have hts :t s≠0:=(map_ne_zero_iff _ (zxb L[X] FX)).mpr hsimple
  have his :i s≠0:= fun e=>hts (by rw [hi (e.trans (map_zero i).symm),map_zero])
  let B:=Localization.Away s
  let J:B →+* EC A:=ztx s his.isUnit
  let T:B →+* FX:=ztx s hts.isUnit
  let I:AdjoinRoot f →+* B:=algebraMap _ _
  have hJ (g: (Integers w)[X][X]) :J (I (AdjoinRoot.mk f g))=a7W A (map₂ (inc w) g) :=
    (zaz s his.isUnit _).trans (him g)
  have hT (g: (Integers w)[X][X]) :T (I (AdjoinRoot.mk f g))=phys (g.eval₂ (mapRingHom red) P) := by
    rw [show T (I (AdjoinRoot.mk f g))=t (AdjoinRoot.mk f g) from
      zaz s _ _]
    simp only [t,zQb,AdjoinRoot.lift_mk]
  have hJinj:Function.Injective J:= by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) J).mpr
    intro a b
    simp only [J,zaz,hi.eq_iff]
    exact ⟨fun h=>hi (by
      simpa only [J,zaz] using congrArg J h),congrArg I⟩
  let e :=RingEquiv.ofBijective J.rangeRestrict ⟨fun _ _ h=>hJinj (congrArg Subtype.val h),RingHom.rangeRestrict_surjective _⟩
  have hsep:J (I s)=polar A false := by
    rw [hJ,hd,polar,eval_false]
    rfl
  have hnum :J (I (AdjoinRoot.mk f (-b))) = -(a7W A (physicalDerivative A.f)) := by
    rw [hJ,map_neg,hb,map_neg]
  have hjetJ:jet A false=J (I (AdjoinRoot.mk f (-b)))/J (I s) := by
    rw [hnum,hsep,jet,eval_false]
    rfl
  have hconst (a :L) : (algebraMap L (EC A) a)∈J.range := by
    let c:Integers w:=⟨algebraMap L E a,by
      by_cases ha :a=0
      · simp [ha]
      · exact (w.on_constants a ha).le⟩
    refine ⟨I (AdjoinRoot.mk f (C (C c))),?_⟩
    rw [hJ]
    simp only [map₂,coe_mapRingHom,map_C]
    rfl
  have hrange : (Chart A w false).toSubring≤J.range := by
    intro a ha
    change a∈Chart A w false at ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases ha with ⟨c,rfl⟩ | ha
      · refine ⟨I (AdjoinRoot.mk f (C (C c))),?_⟩
        rw [hJ]
        simp only [map₂,coe_mapRingHom,map_C]
        rfl
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · refine ⟨I (AdjoinRoot.mk f (C z7y)),?_⟩
          rw [hJ]
          simp only [map₂,coe_mapRingHom,map_C,map_X,amm]
        · refine ⟨I (AdjoinRoot.mk f z7y),?_⟩
          rw [hJ]
          simp only [map₂,coe_mapRingHom,map_X,jU,Bool.false_eq_true,ite_false]
        · rw [hjetJ]
          exact div_mem_range J _ _ (z4z s)
    | algebraMap a=>exact hconst a
    | add a b _ _ ha hb=>exact J.range.add_mem ha hb
    | mul a b _ _ ha hb=>exact J.range.mul_mem ha hb
  let ψ:=e.symm.toRingHom.comp (Subring.inclusion hrange)
  have hψ (a :Chart A w false) (q:B) (hq:J q=(a :EC A)) :ψ a=q:= by
    apply e.injective
    change e (e.symm (Subring.inclusion hrange a))=e q
    rw [RingEquiv.apply_symm_apply]
    exact Subtype.ext hq.symm
  let φ:Chart A w false →ₐ[L] FX :=
    { toRingHom:=T.comp ψ
      commutes' := fun a=> by
        let c:Integers w:=⟨algebraMap L E a,by
          by_cases ha :a=0
          · simp [ha]
          · exact (w.on_constants a ha).le⟩
        change T (ψ (algebraMap L (Chart A w false) a))= _
        rw [hψ _ (I (AdjoinRoot.mk f (C (C c)))) (by
          rw [hJ]
          simp only [map₂,coe_mapRingHom,map_C]
          rfl),hT,eval₂_C,coe_mapRingHom,map_C,hconstant]
        rfl }
  refine ⟨φ,fun g => ?_,?_⟩
  · change T (ψ (evalIn A w g))= _
    rw [hψ _ _ ((hJ g).trans (coe_evalIn _ _ _).symm),hT]
  · have hunit' : IsUnit (I s) :=z4z s
    have hq :
        J (I (AdjoinRoot.mk f (-b)) * ↑hunit'.unit⁻¹)=(cK A w:EC A) := by
      change _=jet A false
      rw [map_mul,map_inv_unit,IsUnit.unit_spec,hjetJ,div_eq_mul_inv]
    have hz :phys (d.eval₂ (mapRingHom red) P)≠0 :=
      (map_ne_zero_iff phys (zxb L[X] FX)).mpr hsimple
    change T (ψ (cK A w))= _
    rw [hψ _ _ hq,map_mul,hT,eval₂_neg,hjet,map_mul,map_inv_unit,IsUnit.unit_spec,
      hT,mul_assoc,mul_inv_cancel₀ hz,mul_one]
end
end q53i3jb
end
section
namespace qhFwyvc
noncomputable section
open Polynomial
open cu (L)
open E7 (CurvePlace)
open qNu3xvc qoCymac
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E]
theorem j9 (w:CurvePlace L E) (f :E[X][X])
  (h : ∀ i j,w.value ((f.coeff i).coeff j)≤1) :
  ∃ F:nC w,includeCoeffs w F=f := by
 apply (mem_lifts _).mp
 apply (lifts_iff_coeff_lifts _).mpr
 intro i
 apply (mem_lifts _).mp
 apply (lifts_iff_coeff_lifts _).mpr
 exact fun j=>⟨⟨(f.coeff i).coeff j,h i j⟩,rfl⟩
private theorem chartIntegral (A:Equation E) (w:CurvePlace L E) (h:qg A w)
   (r :Bool) (i j:ℕ) :
   w.value (((chartEq A r).coeff i).coeff j)≤1 := by
 cases r
 · exact h.1 i j
 · change w.value ((A.f.reverse.coeff i).coeff j)≤1
   rw [coeff_reverse]
   exact h.1 _ _
theorem integralJets (A:Equation E) (w:CurvePlace L E) (h:qg A w)
   {a :E →ₐ[L] LaurentSeries L} (δ:Derivation L E E) (hδ:LocalDerivation a w δ)
   (r :Bool) :Nonempty (EM A w δ r) := by
 let F:=chartEq A r
 have hr (i j:ℕ) :w.value ((F.coeff i).coeff j)≤1 :=chartIntegral A w h r i j
 have hn (n:ℕ) :w.value (n:E)≤1 := by
   have h:=(n:Integers w).property
   change w.value ((n:Integers w) :E)≤1 at h
   simpa only [SubringClass.coe_natCast] using h
 obtain ⟨s,hs⟩:=j9 w F.derivative fun i j=> by
   rw [coeff_derivative,← Nat.cast_succ,coeff_mul_natCast,map_mul]
   exact mul_le_of_le_one_right' (hn (i+1)) |>.trans (hr _ _)
 obtain ⟨d,hd⟩:=j9 w (-physicalDerivative F) fun i j=> by
   rw [coeff_neg,coeff_neg,w.value.map_neg,physicalDerivative,sum_coeff _ (by simp),
     coeff_derivative,← Nat.cast_succ,map_mul]
   exact mul_le_of_le_one_right' (hn (j+1)) |>.trans (hr _ _)
 obtain ⟨n,hnum⟩:=j9 w (-seedDerivative δ F) fun i j=> by
   rw [coeff_neg,coeff_neg,w.value.map_neg,seedDerivative,
     sum_coeff _ (by simp [Polynomial.sum_def]),sum_coeff _ (by simp)]
   exact (hδ _ (hr i j)).1
 exact ⟨⟨s,d,n,hs,hd,hnum⟩⟩
end
end qhFwyvc
end
