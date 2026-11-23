import ProximityPrize.SubmissionLower.ZLrBvqe
set_option Elab.async false
open _root_ renaming CommRing → za6, Nat.add_le_add_right → zlr, Polynomial.C → z1z, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
set_option synthInstance.maxSize 512
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace qO4AyGb
noncomputable section
open Polynomial qrKC9pb qj0Yp9c
open P5_7_7 (Dg)
open cu (L)
open scoped WithZero
def c1 :Prop :=
  ∀ (J:Input) (τ b:L),gauge J τ≠0 →
    ∃ G H :Dg,fits J.s J.l (J.b+J.s) J.h G ∧
      fits J.s J.l (J.b+J.s) J.h H∧a7W J H≠0 ∧
      a7W J G=qW J τ b*a7W J H
def c2 :Prop :=
  ∀ J:Input,Prime (liftedEquation J) ∧
    ∀ G H :Dg,a7W J H≠0 → ¬ liftedEquation J∣liftedCutter G H
private theorem b1W {J:Input} (C:Chart J) (G:Dg) :
    m8 C (extend C.scalar G)=a7W J G:= by
  let f :=(m8 C).comp (extend C.scalar)
  suffices hf :f=a7W J from zLs hf G
  apply z86
  · intro g
    suffices he :f.comp z1z=(a7W J).comp z1z from
      zLs he g
    apply z86
    · intro h
      suffices he : (f.comp z1z).comp z1z =
          ((a7W J).comp z1z).comp z1z from zLs he h
      apply z86
      · intro a
        simpa only [f,extend,m8,zQb,coe_mapRingHom,zrL,
          coe_eval₂RingHom,eval₂_C,Subfield.subtype_apply,constant] using C.scalar_eq a
      · simp only [f,extend,m8,zQb,coe_mapRingHom,zrL,
          zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
        rfl
    · simp only [f,extend,m8,zQb,coe_mapRingHom,zrL,
        zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
      rfl
  · simp only [f,extend,m8,zQb,coe_mapRingHom,zSo,
      coe_eval₂RingHom,eval₂_X]
    rfl
private theorem extend_fits {E :Type} [Field E] (e :L →+* E) {s a b c:ℕ}
   {G:Dg} (hG:fits s a b c G) :fits s a b c (extend e G) := by
 refine ⟨natDegree_map_le.trans hG.1,fun k => ?_,fun k j hj => ?_⟩
 · simp only [extend,coe_mapRingHom,coeff_map]
   exact natDegree_map_le.trans (hG.2.1 k)
 · simp only [extend,coe_mapRingHom,coeff_map] at hj ⊢
   have h:=hG.2.2 k j (fun h₀=>hj (by rw [h₀,Polynomial.map_zero]))
   exact (zlr natDegree_map_le _).trans h
private theorem fits_sub_scaled {E :Type} [Field E] {s a b c:ℕ} {G H :E[X][X][X]}
    (hG:fits s a b c G) (hH :fits s a b c H) (t:E) :
    fits s a b c (G-Polynomial.C (z1z (z1z t))*H) := by
  let B:=z1z (z1z (z1z t))*H
  have hb:B.natDegree≤a :=(natDegree_C_mul_le _ _).trans hH.1
  have hb' : (G-B).natDegree≤a :=(natDegree_sub_le _ _).trans (max_le hG.1 hb)
  refine ⟨hb',fun k => ?_,fun k j hn => ?_⟩
  · simp only [coeff_sub,coeff_C_mul]
    exact (natDegree_sub_le _ _).trans
      (max_le (hG.2.1 k) ((natDegree_C_mul_le _ _).trans (hH.2.1 k)))
  · change ((G-B).coeff k).coeff j≠0 at hn
    have hk :k≤a :=
      (le_natDegree_of_ne_zero (fun h₀=>hn (by rw [h₀,coeff_zero]))).trans hb'
    have weight (P:E[X][X][X]) (hP:fits s a b c P) :
        ((P.coeff k).coeff j).natDegree+k*s≤b+a*s := by
      by_cases hp: (P.coeff k).coeff j=0
      · rw [hp,natDegree_zero,zero_add]
        exact (Nat.mul_le_mul_right s hk).trans (Nat.le_add_left _ _)
      · exact hP.2.2 k j hp
    simp only [coeff_sub,coeff_C_mul]
    have hh:=(zlr (natDegree_C_mul_le t ((H.coeff k).coeff j)) _).trans
      (weight H hH)
    have hg:=weight G hG
    have hd:=natDegree_sub_le ((G.coeff k).coeff j) (z1z t*(H.coeff k).coeff j)
    rw [max_def] at hd
    split_ifs at hd <;> omega
private theorem mapEquiv_coeff {A B:Type} [za6 A] [za6 B]
  (e :A ≃+* B) (P:A[X]) (k :ℕ) :
  (mapEquiv e P).coeff k=e (P.coeff k) :=
 coeff_map _ _
private theorem mapEquiv_const {A B:Type} [za6 A] [za6 B]
  (e :A ≃+* B) (a :A) :
  mapEquiv e (z1z a)=z1z (e a) :=
 zrL _
private theorem extend_map {E :Type} [Field E] (e :RatFunc L ≃+* E) (G:Dg) :
   (mapEquiv (mapEquiv (mapEquiv e))) (extend RatFunc.C G) =
     extend (e.toRingHom.comp RatFunc.C) G:= by
 ext k j i
 simp only [mapEquiv_coeff,extend,coe_mapRingHom,coeff_map,zQb]
 rfl
private theorem prime_transport {A B:Type} [za6 A] [za6 B]
   (e :A ≃+* B) {p:A} (hp:Prime p) :Prime (e p) :=
 (MulEquiv.prime_iff (p:=p) e.toMulEquiv).mpr hp
private theorem transport_lift {M:Type} [Field M] (e :RatFunc L ≃+* M)
    (J:Input) (G H :Dg) (hp:Prime (liftedEquation J))
    (hd : ¬ liftedEquation J∣liftedCutter G H) :
    let a :=e.toRingHom.comp RatFunc.C
    Prime (extend a J.F) ∧ ¬ extend a J.F∣extend a G -
      z1z (z1z (z1z (e RatFunc.X)))*extend a H := by
  let E :=mapEquiv (mapEquiv (mapEquiv e))
  have hEq:E (liftedEquation J)=extend (e.toRingHom.comp RatFunc.C) J.F:=extend_map e J.F
  have hP:E (liftedCutter G H)=extend (e.toRingHom.comp RatFunc.C) G -
      z1z (z1z (z1z (e RatFunc.X))) *
        extend (e.toRingHom.comp RatFunc.C) H := by
    unfold liftedCutter independentParameter
    rw [map_sub E,map_mul E]
    simp only [E,extend_map,mapEquiv_const]
  dsimp only
  rw [← hEq,← hP]
  have hprime :=prime_transport (A:=(RatFunc L)[X][X][X]) (B:=M[X][X][X])
    E (p:=liftedEquation J) hp
  exact ⟨hprime,fun h=>hd ((map_dvd_iff E.toMulEquiv).mp h)⟩
private theorem cutter_vanish {J:Input} (C:Chart J) (T:C.base) (G H :Dg)
   (h:a7W J G=(T:EC J)*a7W J H) :
   m8 C (extend C.scalar G -
     z1z (z1z (z1z T))*extend C.scalar H)=0:= by
 let A:=extend C.scalar G
 let B:=z1z (z1z (z1z T))
 let D:=extend C.scalar H
 have hs :m8 C (A-B*D)=m8 C A - m8 C (B*D) :=
   map_sub (m8 C) A (B*D)
 have hm:m8 C (B*D)=m8 C B*m8 C D:=map_mul (m8 C) B D
 have hc:m8 C B=(T:EC J) := by
   simp only [B,m8,coe_eval₂RingHom,eval₂_C,Subfield.subtype_apply]
 change m8 C (A-B*D)=0
 rw [hs,hm,hc,show m8 C A=a7W J G from b1W C G,
   show m8 C D =a7W J H from b1W C H,← h,sub_self]
private theorem range_unit {J:Input} {r :Bool} (D:GraphPrime J r)
   (m:RatFunc L →+* EC J) (t:EC J)
   (hm : ∀ g:L[X],m (algebraMap L[X] (RatFunc L) g)=g.eval₂ (constMap J) t)
   (hv : ∀ g:L[X],g≠0→D.val (g.eval₂ (constMap J) t)=1)
   (z :m.fieldRange) (hz :z≠0) :D.val (z :EC J)=1 := by
 obtain ⟨w,hw⟩:=RingHom.mem_fieldRange.mp z.property
 have hne :w≠0:= by
   intro h
   apply hz
   apply Subtype.ext
   simpa only [h,map_zero,Subfield.coe_zero] using hw.symm
 rw [← hw]
 induction w using RatFunc.induction_on with
 | _ p q hq =>
   have hp:p≠0:= fun he=>hne (by rw [he,map_zero,zero_div])
   rw [map_div₀,map_div₀,hm,hm,hv _ hp,hv _ hq,div_one]
private theorem ring_regular {J:Input} {r :Bool} (C:Chart J) (D:GraphPrime J r)
    (hu : ∀ z :C.base,z≠0→D.val (z :EC J)=1)
    (hv :D.val (numeratorV C)≤1) :
    ∀ z∈aho C,D.val z≤1 := by
  let S:Subalgebra C.base (EC J) :=
    { D.val.valuationSubring.toSubring with
      algebraMap_mem' := fun z=> by
        change D.val (z :EC J)≤1
        obtain rfl | hz :=eq_or_ne z 0
        · simp
        · exact (hu z hz).le }
  have hU:numeratorU C∈S:= by
    have h:numeratorU C=1-(C.scalar C.tilt:EC J)*numeratorV C:= by
      rw [C.scalar_eq,eq_sub_iff_add_eq]
      exact chart_identity C
    rw [h]
    exact S.sub_mem S.one_mem (S.mul_mem (S.algebraMap_mem (C.scalar C.tilt)) hv)
  have hle :aho C≤S:= by
    apply Algebra.adjoin_le
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact D.regular 0
    · exact D.regular 1
    · exact hU
    · exact hv
  exact fun z hz=>hle hz
theorem of_children (h1 :c1) (h2 :c2) :qj0Yp9c.c1 := by
  intro J ι _ a x r D hι hover
  obtain ⟨τ,b,hτ,hv⟩:=exists_pencil J ι a x r D hover
  let t:=qW J τ b
  let f :=eval₂RingHom (constMap J) t
  obtain ⟨i₀⟩:=hι
  have hf :Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro g hg
    by_contra h
    have he :=(hv i₀).2.2 g h
    change (D i₀).val (f g)=1 at he
    rw [hg,map_zero] at he
    exact zero_ne_one he
  let m:=IsFractionRing.lift (K:=RatFunc L) hf
  have hm (g:L[X]) :m (algebraMap L[X] (RatFunc L) g)=g.eval₂ (constMap J) t :=
    IsFractionRing.lift_algebraMap hf g
  let e :=m.rangeRestrictFieldEquiv
  let C:Chart J :=
    ⟨m.fieldRange,e.toRingHom.comp RatFunc.C,fun c=> by
      change m (RatFunc.C c)=constant J c
      rw [← RatFunc.algebraMap_comp_C,zQb,hm,eval₂_C]
      rfl,τ,hτ⟩
  obtain ⟨G,H,hG,hH,hn,he⟩:=h1 J τ b hτ
  let T:C.base :=e RatFunc.X
  have hl:=transport_lift e J G H (h2 J).1 ((h2 J).2 G H hn)
  have hX: (T:EC J)=t:= by
    change m RatFunc.X=t
    rw [← RatFunc.algebraMap_X,hm,eval₂_X]
  let K:Cut J :=
    { toChart:=C
      an1 :=extend C.scalar G -
        z1z (z1z (z1z T))*extend C.scalar H
      fits_cutter :=fits_sub_scaled (extend_fits C.scalar hG) (extend_fits C.scalar hH) T
      vanish:=cutter_vanish C T G H (by rw [hX]; exact he)
      prime_eq :=hl.1
      proper :=hl.2 }
  refine ⟨K,fun i => ?_⟩
  have hu:=range_unit (D i) m t hm (hv i).2.2
  exact ⟨hu,ring_regular C (D i) hu (hv i).1,(hv i).2.1⟩
end
end qO4AyGb
