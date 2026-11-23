import ProximityPrize.SubmissionLower.Z3IN5pc
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qTFhFCb
noncomputable section
open Polynomial qNu3xvc
open P5_7_1_7_4_3_4 (Pencil PencilBound gauge)
open qFD8jve (aFA sheetPole)
open P5 (p)
open cu (L)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),A.d<p →
    ∀ H :EC A,∃ a :L,∃ m:RatFunc E →+* EC A,
      (∀ c,m (RatFunc.C c)=seed A c) ∧
      m RatFunc.X=constant A a*amm A+H ∧
      (letI:=m.toAlgebra; Module.Finite (RatFunc E) (EC A)) ∧
      (letI:=m.toAlgebra; Algebra.IsSeparable (RatFunc E) (EC A))
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d →
    ∀ a b l:L,gauge A l≠0→polar A false≠0 →
      ∃ N D:E[X][X],PencilBound A N∧PencilBound A D ∧
        (∀ w:E7.CurvePlace L E,aFA w.value N (sheetPole w.value A.f)) ∧
        (∀ w:E7.CurvePlace L E,aFA w.value D (sheetPole w.value A.f)) ∧
        KM A false D =gauge A l^2*polar A false ∧
        KM A false N/ KM A false D =
          constant A a*amm A+(constant A b*pencilOrd A l+pencilJet A l)
variable {E :Type} [Field E] [Algebra L E] {A:Equation E} {r :Bool}
private abbrev O (v :GraphVal A r) :=v.val.valuationSubring
private abbrev res (v :GraphVal A r) :=IsLocalRing.residue (O v)
private def constIn (v :GraphVal A r) :L →+* O v :=
 ((seed A).comp (algebraMap L E)).codRestrict (O v).toSubring fun c=> by
   obtain rfl | hc:=eq_or_ne c 0
   · simp
   · exact (v.constants _ hc).le
private abbrev resConst (v :GraphVal A r) :=(res v).comp (constIn v)
private theorem residue_zero (v :GraphVal A r) (t:O v) :
   res v t=0↔v.val (t:EC A)<1 :=
 (IsLocalRing.residue_eq_zero_iff t).trans (v.val.mem_maximalIdeal_iff (a :=t))
private theorem res_mem (v :GraphVal A r) (t:O v) :
  res v t∈(resConst v).fieldRange↔ResidueConstant v (t:EC A) := by
 rw [RingHom.mem_fieldRange]
 change (∃ c,res v (constIn v c)=res v t)↔_
 apply exists_congr
 intro c
 change _↔v.val ((t - constIn v c:O v) :EC A)<1
 rw [← residue_zero,map_sub,sub_eq_zero,eq_comm]
private def gaugeIn (v :GraphVal A r) (l:L) :O v :=
 let y :O v :=⟨jU A r,v.ordinate_regular⟩
 if r then y+constIn v l else 1+constIn v l*y
private theorem gaugeIn_val (v :GraphVal A r) (l:L) :
  (gaugeIn v l:EC A) =
    if r then jU A true+constant A l else gauge A l:= by
 cases r <;> rfl
private theorem res_gaugeIn (v :GraphVal A r) (l:L) :
  let y :=res v (⟨jU A r,v.ordinate_regular⟩:O v)
  res v (gaugeIn v l)=if r then y+resConst v l else 1+resConst v l*y := by
 cases r <;> simp [gaugeIn]
private theorem bad_gauge (v :GraphVal A r) :
   ({l:L | res v (gaugeIn v l)=0} : Set L).Subsingleton := by
 let y :=res v (⟨jU A r,v.ordinate_regular⟩:O v)
 let e :=resConst v
 intro a ha b hb
 change res v (gaugeIn v a)=0 at ha
 change res v (gaugeIn v b)=0 at hb
 rw [res_gaugeIn] at ha hb
 apply e.injective
 cases r
 · change 1+e a*y=0 at ha
   change 1+e b*y=0 at hb
   have hy :y≠0:= by
     intro h
     simp [h] at ha
   exact mul_right_cancel₀ hy (add_left_cancel (ha.trans hb.symm))
 · exact add_left_cancel (ha.trans hb.symm)
private theorem avoid {ι:Type} [Finite ι] (S:ι→Set L)
  (hS : ∀ i,(S i).Subsingleton) (T:Set L) (hT:T.Finite) :
  ∃ a,a∉T ∧ ∀ i,a∉S i:= by
 obtain ⟨a,-,ha⟩:=Set.infinite_univ.exists_notMem_finite
  (hT.union (Set.finite_iUnion fun i=>(hS i).finite))
 exact ⟨a,fun h=>ha (Or.inl h),fun i h=>ha (Or.inr (Set.mem_iUnion_of_mem i h))⟩
private theorem bad_zero_gauge :
  ({l:L | gauge A l=0} : Set L).Subsingleton := by
 let e :=(seed A).comp (algebraMap L E)
 intro a ha b hb
 change 1+e a*jU A false=0 at ha
 change 1+e b*jU A false=0 at hb
 have hy :jU A false≠0:= by
  intro h
  simp [h] at ha
 exact e.injective (mul_right_cancel₀ hy (add_left_cancel (ha.trans hb.symm)))
private theorem gauged_coords (v :GraphVal A r) (l:L) (hg:gauge A l≠0)
    (hd:2≤A.d) (hp:A.d<p)
    (hG:res v (gaugeIn v l)≠0)
    (hn : ¬ ResidueConstant v (jU A r) ∨ ¬ ResidueConstant v (jet A r)) :
    (v.val (polar A false/gauge A l^(A.d-2))=v.val (polar A r)) ∧
    ∃ u j:O v,(u:EC A)=pencilOrd A l∧(j:EC A)=pencilJet A l ∧
      (res v u∉(resConst v).fieldRange∨res v j∉(resConst v).fieldRange) := by
  let G:=gaugeIn v l
  have hv :v.val (G:EC A)=1 :=
    le_antisymm G.property (le_of_not_gt fun h=>hG ((residue_zero v G).2 h))
  have hg' : (G:EC A)≠0:=v.val.ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  let I:O v :=⟨(G:EC A)⁻¹,by
    change v.val ((G:EC A)⁻¹)≤1
    rw [map_inv₀,hv,inv_one]⟩
  have hGI:G* I=1 :=Subtype.ext (mul_inv_cancel₀ hg')
  let y₀:O v :=⟨jU A r,v.ordinate_regular⟩
  let j₀:O v :=⟨jet A r,v.jet_regular⟩
  let ρ:=res v
  let k :=(resConst v).fieldRange
  let a :=resConst v l
  have ha :a∈k :=(resConst v).mem_fieldRange_self l
  have hI:ρ I*ρ G=1 := by rw [mul_comm,← map_mul,hGI,map_one]
  have hYJ:ρ y₀∉k∨ρ j₀∉k := by
    simpa only [k,ρ,res_mem,y₀,j₀] using hn
  have hv' := hv
  rw [gaugeIn_val] at hv'
  cases r
  · change v.val (gauge A l)=1 at hv'
    refine ⟨by rw [map_div₀,map_pow,hv',one_pow,div_one],y₀*I,j₀*I^2,?_,?_,?_⟩
    · change jU A false*(G:EC A)⁻¹= _
      rw [gaugeIn_val]
      rfl
    · change jet A false*((G:EC A)⁻¹)^2= _
      rw [gaugeIn_val]
      simp [pencilJet,div_eq_mul_inv,inv_pow]
    · by_contra! h
      simp only [map_mul,map_pow] at h
      have hG' : ρ G=1+a*ρ y₀:=res_gaugeIn v l
      have hu: (ρ y₀*ρ I)*ρ G=ρ y₀:= by rw [mul_assoc,hI,mul_one]
      have he :ρ y₀*(1-a*(ρ y₀*ρ I))=ρ y₀*ρ I:= by
        rw [hG'] at hu
        linear_combination -hu
      have hc:1-a*(ρ y₀*ρ I)≠0:= by
        intro hz
        rw [hz,mul_zero] at he
        simp [← he] at hz
      have hy :ρ y₀∈k :=(eq_div_iff hc).2 he ▸
        k.div_mem h.1 (k.sub_mem k.one_mem (k.mul_mem ha h.1))
      have hkG:ρ G∈k :=hG'.symm ▸ k.add_mem k.one_mem (k.mul_mem ha hy)
      have hj: (ρ j₀*ρ I^2)*ρ G^2=ρ j₀:= by rw [mul_assoc,← mul_pow,hI,one_pow,mul_one]
      exact (hYJ.resolve_left (not_not_intro hy)) (hj ▸ k.mul_mem h.2 (k.pow_mem hkG _))
  · change v.val (jU A true+constant A l)=1 at hv'
    have hnG:jU A true+constant A l≠0 :=
      v.val.ne_zero_iff.mp (by rw [hv']; exact one_ne_zero)
    obtain ⟨hu,hj,hp⟩:=(chart_transition A hd hp).2 l hg hnG
    refine ⟨by rw [hp,v.val.map_neg,map_div₀,map_pow,hv',one_pow,div_one],
      I,-j₀*I^2,?_,?_,?_⟩
    · rw [hu]
      change (G:EC A)⁻¹= _
      rw [gaugeIn_val]
      rfl
    · rw [hj]
      change -jet A true*((G:EC A)⁻¹)^2= _
      rw [gaugeIn_val]
      simp [div_eq_mul_inv,inv_pow]
    · by_contra! h
      simp only [map_mul,map_neg,map_pow] at h
      have hG' : ρ G=ρ y₀+a :=res_gaugeIn v l
      have he :ρ G=(ρ I)⁻¹:=(eq_div_iff (show ρ I≠0 from
        fun hz=> by rw [hz,zero_mul] at hI; exact zero_ne_one hI)).2
        (by rw [mul_comm,hI]) |>.trans (one_div _)
      have hkG:ρ G∈k :=he.symm ▸ k.inv_mem h.1
      have hy :ρ y₀∈k :=(show ρ G-a=ρ y₀ by rw [hG',add_sub_cancel_right]) ▸
        k.sub_mem hkG ha
      have hJ: (-ρ j₀*ρ I^2)*ρ G^2 = -ρ j₀:= by
        rw [mul_assoc,← mul_pow,hI,one_pow,mul_one]
      exact (hYJ.resolve_left (not_not_intro hy))
        (neg_neg (ρ j₀) ▸ k.neg_mem (hJ ▸ k.mul_mem h.2 (k.pow_mem hkG _)))
private theorem a1v {F:Type} [Field F] (e :L →+* F) (u j:F)
  (hn:u∉e.fieldRange∨j∉e.fieldRange) :
  ({b:L | e b*u+j∈e.fieldRange} : Set L).Subsingleton := by
 let k :=e.fieldRange
 intro a ha b hb
 by_contra hab
 have hne :e a-e b≠0:=sub_ne_zero.mpr (e.injective.ne hab)
 have hd: (e a-e b)*u∈k := by
  change e a*u+j∈k at ha
  change e b*u+j∈k at hb
  simpa only [add_sub_add_right_eq_sub,sub_mul] using k.sub_mem ha hb
 have hu:=k.div_mem hd (k.sub_mem (e.mem_fieldRange_self a) (e.mem_fieldRange_self b))
 rw [mul_comm,mul_div_cancel_right₀ _ hne] at hu
 exact hn.elim (fun h=>h hu) (fun h=>h
  (add_sub_cancel_left (e a*u) j ▸ k.sub_mem ha (k.mul_mem (e.mem_fieldRange_self a) hu)))
private theorem fresh (v :GraphVal A r) (t:O v) (ht:res v t∉(resConst v).fieldRange)
   (g:L[X]) (hg:g≠0) :
   v.val (g.eval₂ ((seed A).comp (algebraMap L E)) (t:EC A))=1 := by
 let z :=g.eval₂ (constIn v) t
 have hz : (z :EC A)=g.eval₂ ((seed A).comp (algebraMap L E)) (t:EC A) :=
   Polynomial.hom_eval₂ g (constIn v) (O v).subtype t
 rw [← hz]
 refine le_antisymm z.property (le_of_not_gt fun h=>ht ?_)
 let:Algebra L (IsLocalRing.ResidueField (O v)) :=(resConst v).toAlgebra
 have ha :IsAlgebraic L (res v t) :=⟨g,hg,by
   change g.eval₂ (resConst v) (res v t)=0
   rw [← hom_eval₂]
   exact (residue_zero v z).2 h⟩
 let B:=IntermediateField.adjoin L {res v t}
 let:Algebra.IsAlgebraic L B :=
   IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp ha)
 have hm:res v t∈(⊥ : IntermediateField L (IsLocalRing.ResidueField (O v))) :=
   IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic B ▸
     IntermediateField.mem_adjoin_simple_self L (res v t)
 exact RingHom.mem_fieldRange.mpr (IntermediateField.mem_bot.mp hm)
theorem of_children (h1 :c1) (h2 :c2) :q55F46a.c1 := by
 intro E _ _ A hd hp ι _ w x r v hover
 have q0:=(chart_transition A hd hp).1
 obtain ⟨l,hl,hG⟩:=avoid (fun i => {l | res (v i) (gaugeIn (v i) l)=0})
   (fun i=>bad_gauge (v i)) _ (bad_zero_gauge (A:=A)).finite
 have hg:gauge A l≠0:=hl
 have q1 (i:ι) :=gauged_coords (v i) l hg hd hp (hG i) (hover i).2.2
 choose u j hu hj hn using fun i=>(q1 i).2
 obtain ⟨b,-,hb⟩:=avoid
   (fun i => {b | resConst (v i) b*res (v i) (u i)+res (v i) (j i) ∈
     (resConst (v i)).fieldRange})
   (fun i=>a1v _ _ _ (hn i)) ∅ Set.finite_empty
 obtain ⟨a,m,hmC,hmX,hfin,hsep⟩ :=
   h1 A hp (constant A b*pencilOrd A l+pencilJet A l)
 obtain ⟨N,D,hN,hD,hNh,hDh,hDe,hratio⟩:=h2 A hd a b l hg q0
 let C:Pencil A :=
   { num :=N,den:=D,tilt:=l,num_weight:=hN,den_weight:=hD
     num_height:=hNh,den_height:=hDh
     den_ne :=hDe.symm ▸ mul_ne_zero (pow_ne_zero _ hg) q0
     gauge_ne :=hg,polar_ne :=q0
     base :=m,base_seed :=hmC,base_X:=hmX.trans hratio.symm
     finite :=hfin,separable :=hsep }
 refine ⟨C,fun i=>(q1 i).1,fun i g hgn => ?_⟩
 let X₀:O (v i) :=⟨amm A,(v i).base_regular⟩
 let t:=constIn (v i) a*X₀+(constIn (v i) b*u i+j i)
 have ht: (t:EC A)=m RatFunc.X:= by
   change constant A a*amm A+(constant A b*(u i:EC A)+(j i:EC A))= _
   rw [hu,hj,hmX]
 rw [show C.base=m from rfl,← ht]
 refine fresh (v i) t (fun h=>hb i ?_) g hgn
 let k :=(resConst (v i)).fieldRange
 have hX:res (v i) X₀∈k :=(res_mem _ _).mpr ⟨x i,(hover i).2.1⟩
 have ha :resConst (v i) a∈k :=(resConst (v i)).mem_fieldRange_self a
 change res (v i) t∈k at h
 change _∈k
 simpa only [t,map_add,map_mul,RingHom.comp_apply,add_sub_cancel_left] using
   k.sub_mem h (k.mul_mem ha hX)
end
end qTFhFCb
