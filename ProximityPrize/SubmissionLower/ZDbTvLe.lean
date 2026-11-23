import ProximityPrize.SubmissionLower.ZKzStyc
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZkL5N7c
import ProximityPrize.SubmissionLower.Z32V4rd
import ProximityPrize.SubmissionLower.Z6coWda
import ProximityPrize.SubmissionLower.ZBcmVie
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZYcqQEc
set_option Elab.async false
open _root_ renaming AlgHom.toRingHom_eq_coe → ziQ, Algebra → zZE, Algebra.FormallyEtale → zk2, Algebra.IsSeparable → zw7, Algebra.toModule → zXs, Algebra.toSMul → zGD, Field → zrb, Finset.sum_congr → zUo, IsScalarTower → zsf, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, RingHom.Finite.comp → zfr, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
section
section
set_option autoImplicit true
namespace quQ0Dxa
theorem proof :qJm9rWb.c2 :=
 qnSUPza.of_children directions lifts
end quQ0Dxa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qK8v0ue
noncomputable section
open Polynomial Finset
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index block aMp)
open qYVN5fe (lK form left right yCap wCap xDeg yDeg form_map)
open qHJDQEb (IncRing Incident zeroSlot IsFree raw adjust coordX coordY
 incCoeff atInc pointX pointY pairField incidence_roots)
open private fXo from ProximityPrize.SubmissionLower.ZQfUTPd
open private cSQ form_weight cap_valid cap_pos pair_cap from ProximityPrize.SubmissionLower.ZgN8mRc
open private eval_form from ProximityPrize.SubmissionLower.Zi9hW0a
open private map_adjust eval_split from ProximityPrize.SubmissionLower.Z60GVma
private theorem form_congr_on {K:Type} [CommRing K] {d D W:ℕ}
  {u v :Index d D W→K} {j:Fin 3} (h : ∀ i,block i=j→u i=v i) :
  form u j=form v j:= by
 unfold form
 apply zUo rfl
 intro i _
 by_cases hi:block i=j <;> simp [hi,h]
def pairCoeff {d D W:ℕ} (k :Fin 3) (i:Index d D W) :pairField d D W k :=
  if h:block i≠k then
    ⟨atInc i,IntermediateField.subset_adjoin L _ ⟨i,h,rfl⟩⟩
  else 0
@[simp] theorem pairCoeff_map {d D W:ℕ} {k :Fin 3} {i:Index d D W}
    (h:block i≠k) :algebraMap (pairField d D W k) (Incident d D W) (pairCoeff k i) =
      atInc i:= by
  rw [pairCoeff,dite_eq_left h]
  rfl
private theorem kept_form {d D W:ℕ} {k j:Fin 3} (hj:j≠k) :
   (form (pairCoeff k) j).map (mapRingHom (algebraMap (pairField d D W k) (Incident d D W))) =
     form atInc j:= by
 rw [form_map]
 exact form_congr_on fun i hi=>pairCoeff_map (hi.trans_ne hj)
theorem pair_root {d D W:ℕ} {k j:Fin 3} (hj:j≠k) :
    ((form (pairCoeff (d:=d) (D:=D) (W:=W) k) j).map
      (eval₂RingHom (algebraMap (pairField d D W k) (Incident d D W)) (pointX d D W))).eval
        (pointY d D W)=0:= by
  rw [← eval₂_eq_eval_map]
  change (eval₂RingHom (eval₂RingHom (algebraMap (pairField d D W k) (Incident d D W))
    (pointX d D W)) (pointY d D W)) (form (pairCoeff k) j)=0
  rw [eval_form]
  have term (i:Index d D W) :
      (if block i=j then
        algebraMap (pairField d D W k) (Incident d D W) (pairCoeff k i) *
          pointX d D W^xDeg i*pointY d D W^yDeg i else 0) =
      if block i=j then atInc i*pointX d D W^xDeg i*pointY d D W^yDeg i else 0:= by
    by_cases hi:block i=j
    · simp [hi,pairCoeff_map (hi.trans_ne hj)]
    · simp [hi]
  simp only [term,Fintype.sum_sum_type]
  obtain ⟨h0,h1,h2⟩:=incidence_roots d D W
  fin_cases j
  · simpa [block,aMp,xDeg,yDeg] using h0
  · simpa [block,aMp,xDeg,yDeg] using h1
  · simpa [block,aMp,xDeg,yDeg] using h2
private theorem eval_origin {e D B:ℕ} (u:Slot e D B→L)
   (h:u (zeroSlot e D B)=0) :aMp u 0 0=0:= by
 rw [eval_split,h,add_zero]
 apply Finset.sum_eq_zero
 intro i hi
 have hne :=(Finset.mem_erase.mp hi).1
 by_cases hx :i.val.2.val=0
 · have hy :i.val.1.val≠0:= fun hy =>
     hne (Subtype.ext (Prod.ext (Fin.ext hy) (Fin.ext hx)))
   simp [zero_pow hy]
 · simp [zero_pow hx]
private def specializeOrigin {d D W:ℕ} (u:Index d D W→L) :IncRing d D W →ₐ[L] L :=
 MvPolynomial.aeval (Sum.elim (fun _=>0) (fun i=>u i.val))
private theorem specialize_coeff {d D W:ℕ} (u:Index d D W→L)
   (h : ∀ i,¬ IsFree i→u i=0) (i:Index d D W) :
   specializeOrigin u (incCoeff i)=u i:= by
 let φ:=specializeOrigin u
 have hr (i:Index d D W) :φ (raw i)=u i:= by
   by_cases hi:IsFree i <;> simp [φ,specializeOrigin,raw,hi,h]
 have hx :φ (coordX d D W)=0:= by simp [φ,specializeOrigin,coordX]
 have hy :φ (coordY d D W)=0:= by simp [φ,specializeOrigin,coordY]
 have ha {e B:ℕ} (emb:Slot e D B→ Index d D W)
     (he : ¬ IsFree (emb (zeroSlot e D B))) (t:Slot e D B) :
     φ (adjust (fun j=>raw (emb j)) (coordX d D W) (coordY d D W) t)=u (emb t) := by
   have hm:=map_adjust φ.toRingHom (fun j=>raw (emb j)) (coordX d D W) (coordY d D W) t
   change φ _=adjust (fun j=>φ (raw (emb j))) (φ (coordX d D W)) (φ (coordY d D W)) t at hm
   rw [hm,hx,hy,show (fun j=>φ (raw (emb j)))=u ∘ emb from funext fun j=>hr (emb j)]
   simp [adjust,eval_origin (u ∘ emb) (h _ he)]
 rcases i with i | (i | i)
 · exact ha Sum.inl (fun h=>h rfl) i
 · exact ha (fun j => .inr (.inl j)) (fun h=>h rfl) i
 · exact ha (fun j => .inr (.inr j)) (fun h=>h rfl) i
private def mkSlot {e D B:ℕ} (a b:ℕ) (ha :a≤e) (hb:b+a*D ≤B) :
   Slot e D B :=
 ⟨(⟨a,by omega⟩,⟨b,by omega⟩),hb⟩
private theorem exists_slot {d D W a b:ℕ} (j:Fin 3) (ha :a≤yCap d j)
   (hb:b+a*D ≤wCap D W j) :
   ∃ i:Index d D W,block i=j∧yDeg i=a∧xDeg i=b:= by
 fin_cases j
 · exact ⟨.inl (mkSlot a b (by simpa [yCap] using ha) (by simpa [wCap] using hb)),rfl,rfl,rfl⟩
 · exact ⟨.inr (.inl (mkSlot a b (by simpa [yCap] using ha) (by simpa [wCap] using hb))),
     rfl,rfl,rfl⟩
 · exact ⟨.inr (.inr (mkSlot a b (by simpa [yCap] using ha) (by simpa [wCap] using hb))),
     rfl,rfl,rfl⟩
private theorem free_of_exponent {d D W:ℕ} {i:Index d D W}
  (h:yDeg i≠0∨xDeg i≠0) :IsFree i:= by
 rcases i with i | (i | i) <;> intro hi <;> simp [hi,xDeg,yDeg,zeroSlot] at h
private def mark {d D W:ℕ} (i j:Index d D W) :L:=if j=i then 1 else 0
private theorem mark_zero {d D W:ℕ} {i j:Index d D W} (hi:IsFree i) (hj : ¬ IsFree j) :
  mark i j=0:= by
 have h:j≠i:= fun he=>hj (he.symm ▸ hi)
 simp [mark,h]
private theorem form_mark {d D W:ℕ} (i:Index d D W) (k :Fin 3) :
   form (mark i) k=if block i=k then monomial (yDeg i) (monomial (xDeg i) 1) else 0:= by
 unfold form
 rw [Finset.sum_eq_single i]
 · simp [mark]
 · intro j _ hj
   simp [mark,hj]
 · simp
private theorem form_add {d D W:ℕ} (u v :Index d D W→L) (k :Fin 3) :
  form (fun i=>u i+v i) k=form u k+form v k := by
 simp only [form,← Finset.sum_add_distrib]
 apply zUo rfl
 intro i _
 split_ifs <;> simp
private theorem incidence_resultant_ne {d D W:ℕ} (hD:0<D) (hd:3≤d)
   (hW:d*D ≤W) {j k :Fin 3} (hjk :j≠k) :
   (form (incCoeff (d:=d) (D:=D) (W:=W)) j).resultant (form incCoeff k)
     (yCap d j) (yCap d k)≠0:= by
 let m:=yCap d j
 let n:=yCap d k
 have hm:0< m:=cap_pos (by omega) j
 have hn:0<n:=cap_pos (by omega) k
 have hw:1≤wCap D W k := by
   have hb:n*D ≤wCap D W k :=cap_valid hW k
   exact (Nat.mul_pos hn hD).trans_le hb
 obtain ⟨a,haj,hay,hax⟩:=exists_slot (d:=d) (D:=D) (W:=W) j (a :=m) (b:=0)
   le_rfl (by simpa using cap_valid hW j)
 obtain ⟨b,hbk,hby,hbx⟩:=exists_slot (d:=d) (D:=D) (W:=W) k (a :=n) (b:=0)
   le_rfl (by simpa using cap_valid hW k)
 obtain ⟨c,hck,hcy,hcx⟩:=exists_slot (d:=d) (D:=D) (W:=W) k (a :=0) (b:=1)
   (Nat.zero_le _) (by simpa using hw)
 let u:Index d D W→L:= fun i=>(mark a i+mark b i)+mark c i
 have hu (i:Index d D W) (hi : ¬ IsFree i) :u i=0:= by
   have ha :=free_of_exponent (i:=a) (Or.inl (hay ▸ hm.ne'))
   have hb:=free_of_exponent (i:=b) (Or.inl (hby ▸ hn.ne'))
   have hc:=free_of_exponent (i:=c) (Or.inr (hcx ▸ Nat.one_ne_zero))
   simp [u,mark_zero ha hi,mark_zero hb hi,mark_zero hc hi]
 let φ:=(specializeOrigin u).toRingHom
 have hs (l:Fin 3) : (form incCoeff l).map (mapRingHom φ)=form u l:= by
   rw [form_map]
   exact form_congr_on fun i _=>specialize_coeff u hu i
 have hf :form u j=(z7y:lK L)^m:= by
   change form (fun i=>(mark a i+mark b i)+mark c i) j= _
   rw [form_add,form_add,form_mark,form_mark,form_mark]
   simp [haj,hay,hax,hbk,hck,hjk.symm,monomial_one_right_eq_X_pow]
 have hg:form u k=(z7y:lK L)^n+C (z7y:Polynomial L) := by
   change form (fun i=>(mark a i+mark b i)+mark c i) k= _
   rw [form_add,form_add,form_mark,form_mark,form_mark]
   simp [haj,hbk,hby,hbx,hck,hcy,hcx,hjk,monomial_one_right_eq_X_pow]
 intro hz
 have he :=congrArg (mapRingHom φ) hz
 rw [map_zero,← resultant_map_map,hs,hs,hf,hg] at he
 have hgdeg: ((z7y:lK L)^n+C (z7y:Polynomial L)).natDegree≤n:= by
   rw [← hg]
   exact cSQ _ _
 rw [resultant_X_pow_left _ _ _ hgdeg,coeff_add,coeff_X_pow,coeff_C_zero,
   ite_eq_right hn.ne,zero_add] at he
 exact (pow_ne_zero _ Polynomial.X_ne_zero) he
theorem proof :qHJDQEb.c1 := by
  intro d D W hD _ hd hW k
  let j:=left k
  let l:=right k
  have hj:j≠k := by fin_cases k <;> decide
  have hl:l≠k := by fin_cases k <;> decide
  have hjl:j≠l:= by fin_cases k <;> decide
  let F:=form (pairCoeff (d:=d) (D:=D) (W:=W) k) j
  let G:=form (pairCoeff (d:=d) (D:=D) (W:=W) k) l
  let m:=yCap d j
  let n:=yCap d l
  let R:=F.resultant G m n
  refine ⟨R,?_,?_,?_⟩
  · have hR: (form (atInc (d:=d) (D:=D) (W:=W)) j).resultant (form atInc l) m n≠0:= by
      let ι:=algebraMap (IncRing d D W) (Incident d D W)
      have hf (b:Fin 3) : (form incCoeff b).map (mapRingHom ι)=form atInc b :=
        form_map ι _ _
      rw [← hf j,← hf l,resultant_map_map]
      exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr
        (incidence_resultant_ne hD hd hW hjl)
    intro hz
    have he :=congrArg (mapRingHom (algebraMap (pairField d D W k) (Incident d D W))) hz
    change mapRingHom _ (F.resultant G m n)= _ at he
    rw [map_zero,← resultant_map_map,kept_form hj,kept_form hl] at he
    exact hR he
  · rw [aeval_def]
    exact map_resultant_eq_zero_of_common_root
      (eval₂RingHom (algebraMap (pairField d D W k) (Incident d D W)) (pointX d D W)) F G
      (cSQ _ _) (cSQ _ _) (Or.inl (cap_pos (by omega) j).ne') (pointY d D W)
      (pair_root hj) (pair_root hl)
  · rw [← pair_cap d D W k]
    exact fXo F G m n D _ _ (form_weight _ _ (cap_valid hW j))
      (form_weight _ _ (cap_valid hW l))
end
end qK8v0ue
end
section
namespace qVP0NNc
theorem proof :qJm9rWb.c1 :=
 qHJDQEb.of_children
  qK8v0ue.proof
  qIPidRd.proof
  q1XnGpd.proof
end qVP0NNc
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qqBEMJa
noncomputable section
open Polynomial qNu3xvc
open cu (L)
open E7 (CurveField CurvePlace)
open XX (aoG)
open P5_7_1_7_4_3_4 (adG)
open private local_data from ProximityPrize.SubmissionLower.ZRtQEca
open private constIn res_mem residue_zero fresh a1v avoid from ProximityPrize.SubmissionLower.ZYcqQEc
open private aMX from ProximityPrize.SubmissionLower.Y
open scoped WithZero
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
theorem choose_slope {ι:Type} [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L)
    (v :ι→GraphVal A false) (h : ∀ i,Over (v i) (w i) (x i)) :
    ∃ b:L,∀ a :L,∀ i,∃ t: (v i).val.valuationSubring,
      (t:EC A)=constant A a*amm A +
        (constant A b*jet A false+jU A false) ∧
      ¬ ResidueConstant (v i) (t:EC A) := by
  let R (i:ι) :=(v i).val.valuationSubring
  let π (i:ι) :=IsLocalRing.residue (R i)
  let e (i:ι) :=(π i).comp (constIn (v i))
  let y (i:ι) :R i:=⟨jU A false,(v i).ordinate_regular⟩
  let V (i:ι) :R i:=⟨jet A false,(v i).jet_regular⟩
  have hv (i:ι) :π i (V i)∉(e i).fieldRange∨π i (y i)∉(e i).fieldRange := by
    rw [show π i (V i)∈(e i).fieldRange↔ResidueConstant (v i) (jet A false)
      from res_mem (v i) (V i),
      show π i (y i)∈(e i).fieldRange↔ResidueConstant (v i) (jU A false)
      from res_mem (v i) (y i)]
    exact (h i).2.2.symm
  obtain ⟨b,-,hb⟩ :=
    avoid (fun i => {b | e i b*π i (V i)+π i (y i)∈(e i).fieldRange})
      (fun i=>a1v _ _ _ (hv i)) ∅ Set.finite_empty
  refine ⟨b,?_⟩
  intro a i
  let X₀:R i:=⟨amm A,(v i).base_regular⟩
  let t:=constIn (v i) a*X₀+(constIn (v i) b*V i+y i)
  refine ⟨t,rfl,fun ht=>hb i ?_⟩
  have hX:π i X₀∈(e i).fieldRange :=(res_mem _ _).mpr ⟨x i,(h i).2.1⟩
  have ha :e i a∈(e i).fieldRange :=(e i).mem_fieldRange_self a
  have hT:π i t∈(e i).fieldRange :=(res_mem _ _).mpr ht
  change e i b*π i (V i)+π i (y i)∈(e i).fieldRange
  have he :π i t - e i a*π i X₀=e i b*π i (V i)+π i (y i) := by
    simp only [t,map_add,map_mul,e,zQb]
    abel
  exact he ▸ (e i).fieldRange.sub_mem hT ((e i).fieldRange.mul_mem ha hX)
theorem efg (hE :CurveField L E) (v :GraphVal A false) (w:CurvePlace L E)
   (t:v.val.valuationSubring) (ht : ¬ ResidueConstant v (t:EC A))
   {n:ℕ} (hn:0<n) (hw : ∀ c,v.val (seed A c)=w.value c^n) (f :E[X]) :
   v.val (f.eval₂ (seed A) (t:EC A))=adG w.value f^n:= by
 classical
 obtain rfl | hf :=eq_or_ne f 0
 · simp [adG,hn.ne']
 let R:=w.value.valuationSubring
 let B:=v.val.valuationSubring
 obtain ⟨ρ,_,hρ,_,_⟩:=local_data hE w
 let ι:R →+* B:=((seed A).comp R.subtype).codRestrict B.toSubring (fun c=> by
   change v.val (seed A (c:E))≤1
   rw [hw]
   exact pow_le_one₀ zero_le c.property)
 let π:=IsLocalRing.residue B
 have hπ (c:R) :π (ι c)=π (constIn v (ρ c)) := by
   rw [← sub_eq_zero,← map_sub,← show ι (aoG w (ρ c))=constIn v (ρ c) from rfl,
     ← map_sub]
   let d:=c-aoG w (ρ c)
   have hd:w.value (d:E)<1 := by
     apply w.value.mem_maximalIdeal_iff.mp
     have hker :=IsLocalRing.ker_eq_maximalIdeal ρ (fun a=>⟨_,hρ a⟩)
     rw [← hker,RingHom.mem_ker]
     simp [d,hρ]
   exact (residue_zero v (ι d)).mpr (by
     change v.val (seed A (d:E))<1
     rw [hw]
     exact pow_lt_one₀ zero_le hd hn.ne')
 obtain ⟨m,hm,hmax⟩:=Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
   (fun i=>w.value (f.coeff i))
 let b:=f.coeff m
 have hb:b≠0:=mem_support_iff.mp hm
 have hbval :w.value b=adG w.value f :=hmax.symm
 let d (i:ℕ) :R:=⟨f.coeff i/b,by
   change w.value (f.coeff i/b)≤1
   rw [w.value.map_div,div_le_one₀ (w.value.pos_iff.mpr hb),hbval]
   exact aMX _ _ _⟩
 let g:R[X] := ∑ i∈f.support,monomial i (d i)
 have hg:g.coeff m=1 := by
   change (∑ i∈f.support,monomial i (d i)).coeff m= _
   simpa [finsetSum_coeff,coeff_monomial,hm] using
     (show d m=1 from Subtype.ext (div_self hb))
 let z :=g.eval₂ ι t
 let S:=g.map ρ
 have hS:S≠0:= by
   intro h
   have hc:S.coeff m=1 := by rw [show S=g.map ρ from rfl,coeff_map,hg,map_one]
   simp [h] at hc
 let zz :B:=S.eval₂ (constIn v) t
 have hz :π z=π zz := by
   change π (g.eval₂ ι t)=π ((g.map ρ).eval₂ (constIn v) t)
   rw [hom_eval₂,eval₂_map,hom_eval₂]
   exact eval₂_congr (RingHom.ext hπ) rfl rfl
 have hZ:v.val (zz :EC A)=1 := by
   change v.val (B.subtype (S.eval₂ (constIn v) t))=1
   rw [hom_eval₂]
   exact fresh v t ((not_congr (res_mem v t)).mpr ht) S hS
 have hvz :v.val (z :EC A)=1 :=
   le_antisymm z.property (le_of_not_gt fun h =>
     (not_lt_of_ge hZ.ge) ((residue_zero v zz).mp (hz ▸ (residue_zero v z).mpr h)))
 have hscale :f.eval₂ (seed A) (t:EC A)=seed A b*(z :EC A) := by
   rw [eval₂_eq_sum,sum_def]
   change _=seed A b*B.subtype (g.eval₂ ι t)
   rw [hom_eval₂]
   simp only [g,eval₂_finsetSum,eval₂_monomial,Finset.mul_sum]
   apply zUo rfl
   intro i _
   change _=seed A b*(seed A (f.coeff i/b)*(t:EC A)^i)
   rw [← mul_assoc,← map_mul,mul_div_cancel₀ _ hb]
 rw [hscale,map_mul,hvz,mul_one,hw,hbval]
end
end qqBEMJa
end
section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000
namespace qqBEMJa
noncomputable section
open Polynomial IntermediateField KaehlerDifferential TensorProduct
open qNu3xvc
open cu (L)
open P5 (p)
open aKx (b3a)
open private eval_false eval_ne from ProximityPrize.SubmissionLower.Z3IN5pc
open qTFhFCb (chart_transition)
open scoped TensorProduct nonZeroDivisors
theorem map_polynomial {E F:Type} [zrb E] [zrb F] (m:RatFunc E →+* F)
  (s :E →+* F) (h : ∀ a,m (RatFunc.C a)=s a) (f :E[X]) :
  m (algebraMap E[X] (RatFunc E) f)=f.eval₂ s (m RatFunc.X) := by
 have he :m.comp (algebraMap E[X] (RatFunc E))=eval₂RingHom s (m RatFunc.X) := by
  apply z86
  · intro a
    simpa only [zQb,RatFunc.algebraMap_C,coe_eval₂RingHom,eval₂_C] using h a
  · simp
 exact zLs he f
variable {E :Type} [zrb E]
private abbrev physHom (A:Equation E) :E[X] →+* EC A :=
 (a7W A).comp C
private theorem physicalTrans (A:Equation E) :
   letI:=(seed A).toAlgebra
   Transcendental E (amm A) := by
 letI:=(seed A).toAlgebra
 have hm: (aeval (R:=E) (amm A)).toRingHom=physHom A:= by
   apply z86
   · intro a
     rw [ziQ,RingHom.coe_coe,aeval_C]
     rfl
   · simp only [ziQ,RingHom.coe_coe,aeval_X]
     rfl
 apply transcendental_iff_injective.mpr
 change Function.Injective (aeval (R:=E) (amm A)).toRingHom
 rw [hm]
 apply (injective_iff_map_eq_zero _).mpr
 intro f hz
 by_contra hf
 exact eval_ne A (C f) (C_ne_zero.mpr hf) (by simpa using A.positive)
   ((eval_false A _).trans hz)
private def param {F:Type} [zrb F] [zZE E F] {u:F}
   (hu:Transcendental E u) :RatFunc E →+* F :=
 (algebraMap (IntermediateField.adjoin E ({u} : Set F)) F).comp
   (RatFunc.algEquivOfTranscendental u hu).toRingHom
private theorem param_C {F:Type} [zrb F] [zZE E F] {u:F}
  (hu:Transcendental E u) (c:E) :param hu (RatFunc.C c)=algebraMap E F c:= by
 simp [param,← RatFunc.algebraMap_eq_C]
private theorem param_X {F:Type} [zrb F] [zZE E F] {u:F}
  (hu:Transcendental E u) :param hu RatFunc.X=u:= by
 simp [param]
private theorem physicalFinite (A:Equation E) (hq:polar A false≠0) :
    letI:=(seed A).toAlgebra
    letI:=(param (physicalTrans A)).toAlgebra
    zAa (RatFunc E) (EC A)∧zw7 (RatFunc E) (EC A) := by
  let F:=EC A
  let J:=RatFunc E
  letI:zZE E F:=(seed A).toAlgebra
  let j:J →+* F:=param (physicalTrans A)
  letI:zZE J F:=j.toAlgebra
  let y :=jU A false
  let i:E[X] →+* J:=algebraMap _ _
  have hi (f :E[X]) :j (i f)=physHom A f := by
    have hc:j.comp i=physHom A:= by
      apply z86
      · intro a
        change j (RatFunc.C a)=seed A a
        exact param_C _ _
      · exact param_X _
    exact zLs hc f
  have he (f :E[X][X]) :aeval y (f.map i)=a7W A f := by
    rw [aeval_def,eval₂_map,show (algebraMap J F).comp i=physHom A from RingHom.ext hi]
    exact eval_false A f
  let Q:=A.f.map i
  have hQ:Irreducible Q :=
    ((A.irreducible.isPrimitive A.positive.ne').irreducible_iff_irreducible_map_fraction_map
      (K:=J)).mp A.irreducible
  have hder :aeval y Q.derivative≠0:= by
    rw [show Q.derivative=A.f.derivative.map i from derivative_map _ _,he,
      ← eval_false A]
    exact hq
  have hs :Q.Separable :=(separable_iff_derivative_ne_zero hQ).mpr
    (fun h=>hder (by rw [h,map_zero]))
  have hr :aeval y Q=0:= by
    rw [show Q=A.f.map i from rfl,he,a7W,zQb,AdjoinRoot.mk_self,map_zero]
  have hy :IsSeparable J y :=hs.of_dvd (minpoly.dvd _ _ hr)
  let G:=IntermediateField.adjoin J ({y} : Set F)
  have hm (d:AdjoinRoot A.f) :algebraMap (AdjoinRoot A.f) F d∈G:= by
    obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective d
    change a7W A f∈G
    exact (mem_adjoin_simple_iff J _).mpr ⟨f.map i,1,by rw [he,map_one,div_one]⟩
  have hgen:G = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot A.f) a
    exact G.div_mem (hm b) (hm c)
  have hF:zAa J G:=IntermediateField.adjoin.finiteDimensional hy.isIntegral
  have hS:zw7 J G :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable J F).mpr hy
  rw [hgen] at hF hS
  exact ⟨Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv,
    AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv⟩
private theorem differential {F:Type} [zrb F] [zZE E F] [zZE E[X] F]
   [zsf E E[X] F] [zk2 E[X] F] :
   ∃ e :Ω[F⁄E] ≃ₗ[F] F,e (D E F (algebraMap E[X] F z7y))=1 := by
 let e :=(tensorKaehlerEquivOfFormallyEtale E E[X] F).symm.trans
   ((AlgebraTensorModule.congr (LinearEquiv.refl F F) (polynomialEquiv E)).trans
     (AlgebraTensorModule.rid E[X] F F))
 refine ⟨e,?_⟩
 simp [e,tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
private theorem physicalData (A:Equation E) (hq:polar A false≠0) :
    letI:=(seed A).toAlgebra
    zAa (IntermediateField.adjoin E ({amm A} : Set (EC A))) (EC A) ∧
      ∃ e :Ω[EC A⁄E] ≃ₗ[EC A] EC A,e (D E (EC A) (amm A))=1 := by
  let F:=EC A
  let J:=RatFunc E
  letI:zZE E F:=(seed A).toAlgebra
  let h:=physicalTrans A
  let G:=IntermediateField.adjoin E ({amm A} : Set F)
  let b:=RatFunc.algEquivOfTranscendental (amm A) h
  let j:J →+* F:=param h
  obtain ⟨hfin,hs⟩:=physicalFinite A hq
  letI:zZE E[X] F:=(physHom A).toAlgebra
  letI:zZE J F:=j.toAlgebra
  letI:SMul E F:=zGD
  letI:SMul E[X] F:=zGD
  letI:SMul J F:=zGD
  letI:Module E F:=zXs
  letI:Module E[X] F:=zXs
  letI:Module J F:=zXs
  haveI:zsf E E[X] F:=zsL fun _=>rfl
  haveI:zsf E[X] J F:=zsL fun f=> by
    change physHom A f=j (algebraMap E[X] J f)
    rw [map_polynomial j (seed A) (param_C h),param_X h]
    have he :eval₂RingHom (seed A) (amm A)=physHom A:= by
      apply z86
      · intro a
        exact eval₂_C _ _
      · exact eval₂_X _ _
    exact (zLs he f).symm
  haveI:zk2 E[X] J:=Algebra.FormallyEtale.of_isLocalization E[X]⁰
  haveI:zk2 J F:=Algebra.FormallyEtale.of_isSeparable J F
  haveI:zk2 E[X] F:=Algebra.FormallyEtale.comp E[X] J F
  refine ⟨RingHom.Finite.of_comp_finite (f :=b.toRingHom) (g:=algebraMap G F) hfin,?_⟩
  exact differential (E :=E) (F:=F)
private theorem separating {F:Type} [zrb F] [zZE E F] (u:F)
   (e :Ω[F⁄E] ≃ₗ[F] F) (hd:e (D E F u)≠0) (hu:Transcendental E u)
   (hF:zAa (IntermediateField.adjoin E ({u} : Set F)) F) :
   letI:=(param hu).toAlgebra
   zw7 (RatFunc E) F:= by
 let J:=RatFunc E
 letI:zZE J F:=(param hu).toAlgebra
 haveI:zAa J F :=
   zfr (g:=algebraMap (IntermediateField.adjoin E ({u} : Set F)) F) hF
     (RatFunc.algEquivOfTranscendental u hu).toRingEquiv.finite
 haveI:zsf E J F:=zsL fun a=>(param_C hu a).symm
 let k :=KaehlerDifferential.map E J F F
 have hk :k (D E F u)=0:= by
   rw [show u=algebraMap J F RatFunc.X from (param_X hu).symm,map_D]
   exact (D J F).map_algebraMap _
 have hzero (z :Ω[F⁄E]) :k z=0:= by
   have he : (e z/e (D E F u))•D E F u=z :=e.injective (by
     rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hd])
   rw [← he,map_smul,hk,smul_zero]
 haveI:Algebra.FormallyUnramified J F :=
   ⟨⟨fun a b=> by
     obtain ⟨x,rfl⟩:=KaehlerDifferential.map_surjective E J F a
     obtain ⟨y,rfl⟩:=KaehlerDifferential.map_surjective E J F b
     exact (hzero x).trans (hzero y).symm⟩⟩
 exact Algebra.FormallyUnramified.isSeparable J F
private theorem choose_param {F:Type} [zrb F] [zZE E F] (s :L →+* E)
   (x H :F) (ht:Transcendental E x)
   (hfin:zAa (IntermediateField.adjoin E ({x} : Set F)) F)
   (e :Ω[F⁄E] ≃ₗ[F] F) (hx :e (D E F x)=1) :
   ∃ a :L,∃ m:RatFunc E →+* F,
     (∀ c,m (RatFunc.C c)=algebraMap E F c) ∧
     m RatFunc.X=algebraMap E F (s a)*x+H ∧
     (letI:=m.toAlgebra; zAa (RatFunc E) F) ∧
     (letI:=m.toAlgebra; zw7 (RatFunc E) F) := by
 let c:=(algebraMap E F).comp s
 let U (a :L) :F:=c a*x+H
 let T:=algebraicClosure E F
 have ha (a :L) :c a∈T:=T.algebraMap_mem (s a)
 have halg: ({a :L | IsAlgebraic E (U a)} : Set L).Subsingleton := by
   intro a h₁ b h₂
   by_contra hn
   have hne :c a - c b≠0:=sub_ne_zero.mpr (c.injective.ne hn)
   have hmul : (c a-c b)*x∈T:= by
     have he : (c a-c b)*x=U a-U b:= by dsimp only [U]; ring
     rw [he]
     exact T.sub_mem (mem_algebraicClosure_iff.mpr h₁) (mem_algebraicClosure_iff.mpr h₂)
   have hh:=T.div_mem hmul (T.sub_mem (ha a) (ha b))
   rw [mul_comm,mul_div_cancel_right₀ _ hne] at hh
   exact ht (mem_algebraicClosure_iff.mp hh)
 have hdiff (a :L) :e (D E F (U a))=c a+e (D E F H) := by
   have hc:D E F (c a)=0:=(D E F).map_algebraMap (s a)
   rw [show U a=c a*x+H from rfl,map_add,Derivation.leibniz,hc,
     smul_zero,add_zero,map_add,map_smul,hx,smul_eq_mul,mul_one]
 have hdif : ({a :L | e (D E F (U a))=0} : Set L).Subsingleton := by
   intro a h₁ b h₂
   change e (D E F (U a))=0 at h₁
   change e (D E F (U b))=0 at h₂
   rw [hdiff] at h₁ h₂
   exact c.injective (add_right_cancel (h₁.trans h₂.symm))
 obtain ⟨a,_,hab⟩:=Set.infinite_univ.exists_notMem_finite (halg.finite.union hdif.finite)
 have hu:Transcendental E (U a) := fun h=>hab (Or.inl h)
 have hdu:e (D E F (U a))≠0:= fun h=>hab (Or.inr h)
 have hFu:=b3a ht hfin hu
 refine ⟨a,param hu,param_C hu,param_X hu,?_,separating (U a) e hdu hu hFu⟩
 exact zfr (g:=algebraMap (IntermediateField.adjoin E ({U a} : Set F)) F) hFu
   (RatFunc.algEquivOfTranscendental (U a) hu).toRingEquiv.finite
theorem choose_base [zZE L E] (A:Equation E) (hd:2≤A.d) (hp:A.d<p)
   (H :EC A) :
   ∃ a :L,∃ m:RatFunc E →+* EC A,
     (∀ c,m (RatFunc.C c)=seed A c) ∧
     m RatFunc.X=constant A a*amm A+H ∧
     (letI:=m.toAlgebra; zAa (RatFunc E) (EC A)) ∧
     (letI:=m.toAlgebra; zw7 (RatFunc E) (EC A)) := by
 letI:=(seed A).toAlgebra
 obtain ⟨hfin,e,hx⟩:=physicalData A (chart_transition A hd hp).1
 exact choose_param (algebraMap L E) _ H (physicalTrans A) hfin e hx
end
end qqBEMJa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qqBEMJa
open Polynomial qNu3xvc
open qdpQ3Rb (AffinePencil numerator)
open qTFhFCb (chart_transition)
open cu (L)
open private eval_false from ProximityPrize.SubmissionLower.Z3IN5pc
private theorem b12 {E :Type} [zrb E] [zZE L E] (A:Equation E)
  (q:polar A false≠0) (a b:L) :
  KM A false (numerator A a 1 b)/polar A false =
    constant A a*amm A+(constant A b*jet A false+jU A false) := by
 have hC (c:L) :
    KM A false (C (C (algebraMap L E c)))=constant A c:=eval_false A _
 have hX :
    KM A false (C (z7y:E[X]))=amm A:=eval_false A _
 have hY:KM A false (z7y:E[X][X])=jU A false :=eval_false A _
 have hq:KM A false A.f.derivative=polar A false :=rfl
 have h₁:constant A 1=1 :=map_one ((seed A).comp (algebraMap L E))
 have hn:constant A (-b) = -constant A b:=map_neg ((seed A).comp (algebraMap L E)) b
 simp only [numerator,map_add,map_mul,hC,hX,hY,hq,h₁,one_mul,hn,jet]
 change _=constant A a*amm A +
  (constant A b*(-KM A false (physicalDerivative A.f)/polar A false) +
    jU A false)
 field_simp [q]
 ring
theorem proof :qdpQ3Rb.c1 := by
 intro E _ _ A hE hd hp ι _ w x v h
 obtain ⟨b,hb⟩:=choose_slope w x v h
 obtain ⟨a,m,hmC,hmX,hfin,hsep⟩ :=
   choose_base A hd hp (constant A b*jet A false+jU A false)
 have hq:=(chart_transition A hd hp).1
 let D:AffinePencil A :=
   { a :=a,b:=1,c:=b,polar_ne :=hq,base :=m,base_seed :=hmC
     base_X:=hmX.trans (b12 A hq a b).symm,finite :=hfin,separable :=hsep }
 refine ⟨D,fun i => ?_⟩
 obtain ⟨t,ht,hnt⟩:=hb a i
 obtain ⟨n,hn,hs⟩:=(h i).1
 refine ⟨n,hn,fun f => ?_⟩
 change (v i).val (m (algebraMap E[X] (RatFunc E) f))= _
 rw [map_polynomial m (seed A) hmC,hmX.trans ht.symm]
 exact efg hE (v i) (w i) t hnt hn hs f
end qqBEMJa
end
end
