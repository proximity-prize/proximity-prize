import ProximityPrize.SubmissionLower.Z99zqBd
set_option Elab.async false
open _root_ renaming Algebra.subset_adjoin → zkk, Finset.range → z4x, Finset.sum_div → zQ4, Finset.sum_mul → zkq, Fintype.card_sigma → zTU, Function.Injective → zq4, Int.toNat_of_nonneg → zi4, MvPolynomial.basisRestrictSupport → zzc, Nat.add_mul → zNE, Nat.le_of_lt_succ → zeh, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y, RingHom.comp_apply → zQb, Submodule.sum_mem → zo3
section
set_option backward.isDefEq.respectTransparency false
namespace qj0Yp9c
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5_7_7 (Dg)
private theorem image_sum {R M:Type} [CommRing R] [CommRing M]
  (f :R[X] →+* M) (P:R[X]) :
  f P = ∑ i∈P.support,f (z1z (P.coeff i)*z7y ^i) := by
 simpa only [Polynomial.sum,map_sum] using (congrArg f P.sum_C_mul_X_pow_eq).symm
private theorem scaled_image_mem {J:Input} (C:Chart J) {M:Type} [Field M]
  (f :M[X][X][X] →+* EC J) (scalar :M →+* C.base)
  (hconst : ∀ d,f (z1z (z1z (z1z d)))=(scalar d:EC J))
  (hx :f (z1z (z1z (z7y:M[X])))=amm J)
  (hz :f (z1z (z7y:M[X][X]))=seed J)
  (hy :f z7y=jU J false)
  {a b c:ℕ} {G:M[X][X][X]} (hG:fits J.s a b c G) :
  f G/denominator C ^a∈dO C a b c:= by
 classical
 rw [image_sum f G,zQ4]
 refine zo3 _ fun k hk => ?_
 rw [map_mul,map_pow]
 have h₂:=image_sum (f.comp z1z) (G.coeff k)
 simp only [zQb] at h₂
 rw [h₂]
 simp only [map_mul,map_pow,zkq,zQ4]
 refine zo3 _ fun j hj => ?_
 have h₃:=image_sum ((f.comp z1z).comp z1z) ((G.coeff k).coeff j)
 simp only [zQb] at h₃
 rw [h₃]
 simp only [map_mul,map_pow,zkq,zQ4]
 refine zo3 _ fun i hi => ?_
 have hk₀:=le_natDegree_of_ne_zero (mem_support_iff.mp hk)
 have hka :=hk₀.trans hG.1
 have hha : (a-k)+k=a :=zxt hka
 have hjc:=(le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans (hG.2.1 k)
 have hi₀:=le_natDegree_of_ne_zero (mem_support_iff.mp hi)
 have hw:=hG.2.2 k j (mem_support_iff.mp hj)
 have hs :a*J.s=(a-k)*J.s+k*J.s := by rw [← zNE,hha]
 have hm:=mono_mem C hha (show i≤b+(a-k)*J.s by omega) hjc
 let d:=((G.coeff k).coeff j).coeff i
 have h:=(dO C a b c).smul_mem (scalar d) hm
 change (scalar d:EC J)*mono C i j (a-k) k∈_ at h
 rw [hconst,hx,hz,hy]
 convert h using 1
 have he :denominator C ^a=denominator C ^(a-k)*denominator C ^k := by
  rw [← pow_add,hha]
 conv_lhs=>rw [he]
 simp only [mono,numeratorU,numeratorV,inv_pow,div_eq_mul_inv,mul_inv_rev]
 ring
theorem scaled_eval_mem {J:Input} (C:Chart J) {a b c:ℕ}
  {G:C.base[X][X][X]} (hG:fits J.s a b c G) :
  m8 C G/denominator C ^a∈dO C a b c:= by
 refine scaled_image_mem C (m8 C) (RingHom.id _) ?_ ?_ ?_ ?_ hG <;>
  simp [m8,coe_eval₂RingHom,eval₂_C,eval₂_X]
private theorem scaled_root_mem {J:Input} (C:Chart J) {a b c:ℕ}
  {G:Dg} (hG:fits J.s a b c G) :
  a7W J G/denominator C ^a∈dO C a b c :=
 scaled_image_mem C (a7W J) C.scalar (fun d=>(C.scalar_eq d).symm)
  rfl rfl rfl hG
def vForm (J:Input) :Dg :=
 J.F.derivative*z7y-Polynomial.C (z1z (z1z (J.l:L)))*J.F
private theorem vForm_coeff (J:Input) (k :ℕ) :
   (vForm J).coeff k=J.F.coeff k*z1z (z1z ((k :L)-(J.l:L))) := by
 unfold vForm
 rw [coeff_sub,coeff_C_mul]
 cases k with
 | zero =>
   simp only [coeff_mul_X_zero,Nat.cast_zero,zero_sub,map_neg]
   ring
 | succ k =>
   rw [coeff_mul_X,coeff_derivative]
   push_cast
   rw [map_sub,map_sub,mul_sub,mul_comm (z1z (z1z (J.l:L)))]
   simp
private theorem fits_by_coeff {J:Input} {G:Dg} {b n:ℕ}
   (hd:G.natDegree≤J.l-1)
   (hc : ∀ k,∃ d:L,G.coeff k=J.F.coeff (k+n)*z1z (z1z d))
   (hweight:J.b+J.l*J.s≤b+(J.l-1)*J.s+n*J.s) :
   fits J.s (J.l-1) b J.h G:= by
 refine ⟨hd,fun k => ?_,fun k j h => ?_⟩
 · obtain ⟨d,hd⟩:=hc k
   rw [hd]
   exact (natDegree_mul_C_le _ _).trans (J.Ca.height _)
 · obtain ⟨d,hd⟩:=hc k
   rw [hd,coeff_mul_C] at h ⊢
   have hw:=J.weight (k+n) j (left_ne_zero_of_mul h)
   have hp:=natDegree_mul_C_le ((J.F.coeff (k+n)).coeff j) d
   rw [zNE] at hw
   omega
private theorem u_form_mem {J:Input} (C:Chart J) :
   relativePolar C*numeratorU C∈dO C (J.l-1) J.b J.h:= by
 have hl:=J.Ca.two_le
 have hN :J.l-1+1=J.l:= by omega
 have hNw:=congrArg (fun n=>n*J.s) hN
 rw [zNE,one_mul] at hNw
 have hfits :fits J.s (J.l-1) J.b J.h J.F.derivative :=
   fits_by_coeff (n:=1) (by simpa [J.Ca.jU] using natDegree_derivative_le J.F)
     (fun k=>⟨((k+1 :ℕ) :L),by rw [coeff_derivative]; simp⟩)
     (by simp only [one_mul]; omega)
 have h:=scaled_root_mem C hfits
 have hpow:denominator C ^(J.l-1)=denominator C ^(J.l-2)*denominator C:= by
   rw [← pow_succ,show J.l-2+1=J.l-1 by omega]
 rw [hpow,← div_div] at h
 rw [relativePolar,polar,chartEval_false,show chartEq J false=J.F from rfl,numeratorU,
   ← div_eq_mul_inv]
 exact h
private theorem v_form_mem {J:Input} (C:Chart J) :
   relativePolar C*numeratorV C∈dO C (J.l-1) (J.b+J.s) J.h:= by
 have hl:=J.Ca.two_le
 have hN :J.l-1+1=J.l:= by omega
 have hNw:=congrArg (fun n=>n*J.s) hN
 rw [zNE,one_mul] at hNw
 have hd: (vForm J).natDegree≤J.l-1 := by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro k hk
   rw [vForm_coeff]
   rcases eq_or_lt_of_le (show J.l≤k by omega) with h | h
   · simp [← h]
   · rw [coeff_eq_zero_of_natDegree_lt (J.Ca.jU ▸ h),zero_mul]
 have hfits :fits J.s (J.l-1) (J.b+J.s) J.h (vForm J) :=
   fits_by_coeff (n:=0) hd
     (fun k=>⟨(k :L)-(J.l:L),by simpa only [Nat.add_zero] using vForm_coeff J k⟩)
     (by simp only [Nat.zero_mul,add_zero]; omega)
 have hm:=scaled_root_mem C hfits
 have hz :=(rootMap_eq_zero_iff J J.F).mpr dvd_rfl
 have he :a7W J (vForm J)=a7W J J.F.derivative*jU J false := by
   let a :Dg:=J.F.derivative*z7y
   let b:Dg:=z1z (z1z (z1z (J.l:L)))*J.F
   change a7W J (a-b)= _
   rw [map_sub (a7W J) a b]
   dsimp [a,b]
   rw [map_mul,map_mul,hz,mul_zero,sub_zero]
   rfl
 have hpow:denominator C ^(J.l-1)=denominator C ^(J.l-2)*denominator C:= by
   rw [← pow_succ,show J.l-2+1=J.l-1 by omega]
 rw [he,hpow] at hm
 rw [relativePolar,polar,chartEval_false,show chartEq J false=J.F from rfl,numeratorV,
   div_mul_div_comm]
 exact hm
theorem polar_mul_piece {J:Input} (C:Chart J) (a b c:ℕ) (ha :1≤a) :
   (dO C a b c).map (nY C)≤dO C (a+(J.l-2)) (b+(J.b+J.s)) (c+J.h) := by
 apply Submodule.map_le_iff_le_comap.mpr
 apply Submodule.span_le.mpr
 rintro _ ⟨m,rfl⟩
 let i:=m.2.1.val
 let j:=m.2.2.val
 let v :=m.1.val
 let u:=a-v
 have huv :u+v=a :=zxt (zeh m.1.isLt)
 have hi:i≤b+u*J.s :=zeh m.2.1.isLt
 have hj:j≤ c:=zeh m.2.2.isLt
 have hgrade :a-1+(J.l-1)=a+(J.l-2) := by have :=J.Ca.two_le; omega
 change relativePolar C*mono C i j u v∈dO C (a+(J.l-2)) (b+(J.b+J.s)) (c+J.h)
 by_cases hu:u=0
 · have hv :0<v := by omega
   have h:=mono_mem C (a :=a-1) (v :=v-1) (u:=u) (by omega) hi hj
   have hm:=eLg C (v_form_mem C) h
   rw [Nat.add_comm (J.l-1),hgrade,Nat.add_comm (J.b+J.s),Nat.add_comm J.h] at hm
   have he :mono C i j u v=numeratorV C*mono C i j u (v-1) := by
     have h:=pow_succ (numeratorV C) (v-1)
     rw [Nat.sub_add_cancel (show 1≤v by omega)] at h
     simp only [mono,h]
     ring
   rw [he,← mul_assoc]
   exact hm
 · have hu' : u-1+1=u:= by omega
   have hi' : i≤(b+J.s)+(u-1)*J.s := by
     rw [← hu',Nat.add_mul,one_mul] at hi
     omega
   have h:=mono_mem C (a :=a-1) (u:=u-1) (v :=v) (by omega) hi' hj
   have hm:=eLg C (u_form_mem C) h
   rw [Nat.add_comm (J.l-1),hgrade,Nat.add_comm J.h] at hm
   have he :mono C i j u v=numeratorU C*mono C i j (u-1) v := by
     have h:=pow_succ (numeratorU C) (u-1)
     rw [hu'] at h
     simp only [mono,h]
     ring
   rw [he,← mul_assoc]
   exact (show J.b+(b+J.s)=b+(J.b+J.s) by omega) ▸ hm
end
end qj0Yp9c
end
section
set_option maxHeartbeats 400000
namespace qj0Yp9c
noncomputable section
open qrKC9pb Finset
open cu (L)
open scoped WithZero BigOperators
private abbrev OrdVal (J:Input) :=Valuation (EC J) ℤᵐ⁰
private def order {J:Input} (v :OrdVal J) (f :EC J) :ℤ :=
 -WithZero.log (v f)
private theorem order_nonneg {J:Input} (v :OrdVal J) {f :EC J}
  (hf :f≠0) (h:v f≤1) :0≤order v f := by
 have h:=(WithZero.log_le_log (v.ne_zero_iff.mpr hf) one_ne_zero).mpr h
 simpa only [order,neg_nonneg,WithZero.log_one] using h
private theorem order_mul {J:Input} (v :OrdVal J) {f g:EC J}
  (hf :f≠0) (hg:g≠0) :order v (f*g)=order v f+order v g:= by
 simp only [order,map_mul,WithZero.log_mul (v.ne_zero_iff.mpr hf) (v.ne_zero_iff.mpr hg),
  neg_add]
private theorem order_pow {J:Input} (v :OrdVal J) (f :EC J) (n:ℕ) :
  order v (f^n)=(n:ℤ)*order v f := by
 simp only [order,map_pow,WithZero.log_pow,nsmul_eq_mul,mul_neg]
private theorem value_of_order {J:Input} (v :OrdVal J) {f :EC J}
  (hf :f≠0) :v f=WithZero.exp (-order v f) := by
 rw [order,neg_neg,WithZero.exp_log (v.ne_zero_iff.mpr hf)]
private structure Representative {J:Input} (C:Chart J) (v :OrdVal J) (m e :ℕ) where
 f :EC J
 mem:f∈aho C
 ne :f≠0
 n:ℕ
 ord:order v f=n
 residue : (n:ℤ) % m=e
 minimal : ∀ g∈aho C,g≠0→ order v g % m=e→(n:ℤ)≤order v g
private theorem representatives {J:Input} (C:Chart J) (v :OrdVal J)
   (hreg : ∀ f∈aho C,v f≤1) (hs :Function.Surjective v)
   {m e :ℕ} (he :e< m) :Nonempty (Representative C v m e) := by
 classical
 obtain ⟨t,ht⟩:=hs (WithZero.exp (-1 :ℤ))
 have ht₀:t≠0:=v.ne_zero_iff.mp (ht.symm ▸ WithZero.exp_ne_zero)
 obtain ⟨A,hAr,B,hBr,hB,h⟩:=chart_fraction C t ht₀
 have hA:A≠0:= fun hA=>ht₀ (by simp [h,hA])
 have hdiff :order v A - order v B=1 := by
   have hlog:=congrArg WithZero.log ht
   rw [h,map_div₀,WithZero.log_div (v.ne_zero_iff.mpr hA) (v.ne_zero_iff.mpr hB),
     WithZero.log_exp] at hlog
   unfold order
   omega
 let g:=A^e*B^((m-1)*e)
 have hg:g≠0:=mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)
 have hgr :g∈aho C:=mul_mem (pow_mem hAr _) (pow_mem hBr _)
 have hformula :order v g=e+(m:ℤ)*((e :ℤ)*order v B) := by
   have hm₁:1≤ m:= by omega
   dsimp [g]
   rw [order_mul v (pow_ne_zero _ hA) (pow_ne_zero _ hB),order_pow,order_pow]
   push_cast [Nat.cast_sub hm₁]
   rw [show order v A=order v B+1 by omega]
   ring
 have hgmod:order v g % m=e := by
   rw [hformula,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by positivity) (by exact_mod_cast he)]
 let P (n:ℕ) := ∃ f∈aho C,f≠0∧order v f=n∧(n:ℤ) % m=e
 have exists_order (f :EC J) (hf :f∈aho C) (hf₀:f≠0)
     (hfmod:order v f % m=e) :P (order v f).toNat := by
   have hn:=zi4 (order_nonneg v hf₀ (hreg f hf))
   exact ⟨f,hf,hf₀,hn.symm,hn ▸ hfmod⟩
 have hex : ∃ n,P n:=⟨_,exists_order g hgr hg hgmod⟩
 obtain ⟨f,hf,hf₀,hfn,hfmod⟩:=Nat.find_spec hex
 refine ⟨⟨f,hf,hf₀,Nat.find hex,hfn,hfmod,fun q hq hq₀ hqmod => ?_⟩⟩
 have hmin:=Nat.find_min' hex (exists_order q hq hq₀ hqmod)
 have hn:=zi4 (order_nonneg v hq₀ (hreg q hq))
 exact hn ▸ (show (Nat.find hex :ℤ)≤((order v q).toNat :ℤ) by exact_mod_cast hmin)
private theorem centre_separator {J:Input} (C:Chart J) {r s :Bool}
   (D:GraphPrime J r) (E :GraphPrime J s) {a x b y :L}
   (hD:Over J D a x) (hE :Over J E b y) (hab: (a,x)≠(b,y)) :
   ∃ f∈aho C,D.val f=1∧E.val f<1 := by
 have hq (q:EC J) (hq:q∈aho C) {u w:L}
     (huw:u≠w) (hdu:D.val (q-constant J u)<1)
     (hew:E.val (q-constant J w)<1) :
     ∃ f∈aho C,D.val f=1∧E.val f<1 := by
   have hm:constant J w∈aho C:= by
     rw [← C.scalar_eq]
     exact (aho C).algebraMap_mem (C.scalar w)
   let F:=C.base.subtype.comp C.scalar
   have hconst (c:L) :F c=constant J c:=C.scalar_eq c
   have hsub:constant J (u-w)=constant J u - constant J w:= by
     simp only [← hconst,map_sub]
   have hunit :D.val (constant J u - constant J w)=1 :=
     hsub ▸ D.constants (u-w) (sub_ne_zero.mpr huw)
   refine ⟨q-constant J w,sub_mem hq hm,?_,hew⟩
   have h:q-constant J w=(q-constant J u)+(constant J u-constant J w) := by abel
   rw [h,D.val.map_add_eq_of_lt_right (hdu.trans_eq hunit.symm),hunit]
 by_cases h:a=b
 · have hxy :x≠y := fun hxy=>hab (Prod.ext h hxy)
   exact hq (amm J) (zkk (by simp)) hxy hD.2 hE.2
 · exact hq (seed J) (zkk (by simp)) h hD.1 hE.1
private theorem separators {J:Input} (C:Chart J) {ι:Type} [Fintype ι]
   (a x :ι→L) (r :ι→Bool) (D : ∀ i,GraphPrime J (r i))
   (hi:zq4 (fun i=>(a i,x i))) (ho : ∀ i,Over J (D i) (a i) (x i))
   (hC : ∀ i,qg C (D i)) :
   ∃ w:ι→EC J,(∀ i,w i∈aho C) ∧
     (∀ i,(D i).val (w i)=1)∧(∀ i j,j≠i→(D j).val (w i)<1) := by
 classical
 have hsep (i j:ι) : ∃ f∈aho C,(D i).val f=1 ∧
     (j≠i→(D j).val f<1) := by
   by_cases hij:j=i
   · exact ⟨1,one_mem _,map_one _,fun hn=>(hn hij).elim⟩
   obtain ⟨f,hf,hu,hz⟩:=centre_separator C (D i) (D j) (ho i) (ho j)
     (fun h=>hij (hi h).symm)
   exact ⟨f,hf,hu,fun _=>hz⟩
 choose f hf fu fz using hsep
 let w (i:ι) := ∏ j∈univ.erase i,f i j
 refine ⟨w,fun i=>prod_mem (fun j _=>hf i j),fun i => ?_,fun i j hij => ?_⟩
 · simp only [w,map_prod,fu,prod_const_one]
 · dsimp only [w]
   rw [← mul_prod_erase _ _ (mem_erase.mpr ⟨hij,mem_univ j⟩),map_mul,map_prod]
   have hprod: (∏ k∈(univ.erase i).erase j,(D j).val (f i k))≤1 :=
     prod_le_one fun k _=>(hC j).regular _ (hf i k)
   exact (mul_le_of_le_one_right bot_le hprod).trans_lt (fz i j hij)
theorem polar_classes {J:Input} (C:Chart J) {ι:Type} [Fintype ι]
    (a x :ι→L) (r :ι→Bool) (D : ∀ i,GraphPrime J (r i))
    (hi:zq4 (fun i=>(a i,x i))) (ho : ∀ i,Over J (D i) (a i) (x i))
    (hC : ∀ i,qg C (D i)) :
    ∃ V:Submodule C.base (EC J),FiniteDimensional C.base V ∧
      V≤(aho C).toSubmodule ∧
      Disjoint V ((aho C).toSubmodule.map (nY C)) ∧
      (∑ i,polarOrder (D i))≤Module.finrank C.base V:= by
  classical
  let v (i:ι) :=(D i).val
  let m (i:ι) :=polarOrder (D i)
  let I:=Σ i,Fin (m i)
  have hphi (j:I) :order (v j.1) (relativePolar C)=m j.1 := by
    have h: (order (v j.1) (relativePolar C)).toNat=m j.1 := by
      simp only [order,m,polarOrder,v,(hC j.1).polar_val]
    have hm:=j.2.isLt
    omega
  let q (j:I) :Representative C (v j.1) (m j.1) j.2.val :=
    Classical.choice (representatives C (v j.1) (hC j.1).regular (D j.1).normalized j.2.isLt)
  let n (j:I) :=(q j).n
  obtain ⟨w,hw,hwi,hwj⟩:=separators C a x r D hi ho hC
  let N :=univ.sup n+1
  have hN (j:I) :n j<N :=Nat.lt_succ_of_le (le_sup (mem_univ j))
  let g (j:I) :=w j.1^N*(q j).f
  have hg (j:I) :g j∈aho C:=mul_mem (pow_mem (hw _) _) (q j).mem
  have hown (j:I) :v j.1 (g j)=WithZero.exp (-(n j:ℤ)) := by
    dsimp only [g]
    rw [map_mul,map_pow,show v j.1 (w j.1)=1 from hwi _,one_pow,one_mul,
      value_of_order _ (q j).ne,(q j).ord]
  have hother (j:I) (i:ι) (hij:i≠j.1) :
      v i (g j)≤WithZero.exp (-(N :ℤ)) := by
    have hlt:v i (w j.1)<1 :=hwj _ _ hij
    have hle :v i (w j.1)≤WithZero.exp (-1 :ℤ) := by
      by_cases hz :v i (w j.1)=0
      · rw [hz]; exact bot_le
      have h:=(WithZero.log_lt_log hz one_ne_zero).mpr hlt
      rw [WithZero.log_one] at h
      exact (WithZero.log_le_iff_le_exp hz).mp (by omega)
    dsimp only [g]
    rw [map_mul,map_pow]
    calc
      _≤(v i (w j.1))^N :=mul_le_of_le_one_right bot_le ((hC i).regular _ (q j).mem)
      _≤(WithZero.exp (-1 :ℤ))^N :=pow_le_pow_left₀ bot_le hle _
      _ = _:= by rw [← WithZero.exp_nsmul]; simp
  let W:=(aho C).toSubmodule.map (nY C)
  have hzero (c:I→C.base) (hc: (∑ j,c j•g j)∈W) : ∀ j,c j=0:= by
    intro j
    by_contra hj
    let T:=univ.filter (fun k :I=>k.1=j.1∧c k≠0)
    obtain ⟨d,hd,hmin⟩:=exists_min_image T n ⟨j,by simp [T,hj]⟩
    obtain ⟨hdj,hd₀⟩:=(mem_filter.mp hd).2
    have hterm (k :I) (hk :c k≠0) :v d.1 (c k•g k)=v d.1 (g k) := by
      change v d.1 ((c k :EC J)*g k)= _
      rw [map_mul,show v d.1 (c k :EC J)=1 from (hC d.1).base_unit (c k) hk,one_mul]
    have hsv :=(v d.1).map_sum_eq_of_lt (s :=univ) (f := fun k=>c k•g k) (j:=d)
      (mem_univ _) (fun k hk => ?_)
    rcases Submodule.mem_map.mp hc with ⟨z,hz,hzsum⟩
    change relativePolar C*z = ∑ j,c j•g j at hzsum
    have hval :v d.1 (relativePolar C*z)=WithZero.exp (-(n d:ℤ)) := by
      rw [hzsum,hsv,hterm d hd₀,hown]
    have hz₀:z≠0:= by
      intro he
      rw [he,mul_zero,map_zero] at hval
      exact WithZero.exp_ne_zero hval.symm
    have horder :=congrArg (fun t => -WithZero.log t) hval
    simp only [WithZero.log_exp,neg_neg] at horder
    change order (v d.1) (relativePolar C*z)= _ at horder
    rw [order_mul _ (relativePolar_ne C) hz₀,hphi d] at horder
    have heq :order (v d.1) z=(n d:ℤ) - m d.1 := by omega
    have hmod:order (v d.1) z % m d.1=d.2.val := by
      rw [heq,Int.sub_emod_right]
      exact (q d).residue
    have hbad:=(q d).minimal z hz hz₀ hmod
    have hm:=d.2.isLt
    change (n d:ℤ)≤order (v d.1) z at hbad
    omega
    · rw [hterm d hd₀,hown]
      by_cases hk₀:c k=0
      · simp [hk₀]
      rw [hterm k hk₀]
      by_cases hkd:k.1=d.1
      · obtain ⟨i,k⟩:=k
        obtain ⟨j',d⟩:=d
        dsimp at hkd
        subst i
        rw [hown ⟨j',k⟩,WithZero.exp_lt_exp,neg_lt_neg_iff]
        have hle :=hmin ⟨j',k⟩ (mem_filter.mpr ⟨mem_univ _,hdj,hk₀⟩)
        have hn:n ⟨j',d⟩≠n ⟨j',k⟩:= by
          intro he
          have h:=(q ⟨j',d⟩).residue.symm.trans
            (show (n ⟨j',d⟩:ℤ) % m j' = (k.val :ℤ) by rw [he]; exact (q ⟨j',k⟩).residue)
          have hdk :d=k :=Fin.ext (by exact_mod_cast h)
          exact (mem_sdiff.mp hk).2 (mem_singleton.mpr (by subst k; rfl))
        exact_mod_cast lt_of_le_of_ne hle hn
      · exact (hother k d.1 (Ne.symm hkd)).trans_lt
          (WithZero.exp_lt_exp.mpr (by have :=hN d; omega))
  let V:=Submodule.span C.base (Set.range g)
  have hlin:LinearIndependent C.base g:=Fintype.linearIndependent_iff.mpr
    (fun c hc=>hzero c (hc ▸ W.zero_mem))
  refine ⟨V,FiniteDimensional.span_of_finite _ (Set.finite_range _),
    Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hg j),?_,?_⟩
  · rw [disjoint_iff_inf_le]
    intro z hz
    obtain ⟨c,hc⟩:=(Submodule.mem_span_range_iff_exists_fun _).mp hz.1
    have hcz :=hzero c (hc ▸ hz.2)
    rw [Submodule.mem_bot,← hc]
    simp [hcz]
  · rw [finrank_span_eq_card hlin]
    simp [I,m,zTU]
end
end qj0Yp9c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBTXDtb
noncomputable section
open qj0Yp9c (PieceIndex twiceCount)
private def toIndex {s a b c:ℕ} (v :cV s a b c) :PieceIndex s a b c:= by
 have ha :=v.property.1
 have hc:=v.property.2.1
 have hb:=v.property.2.2
 have hs :a*s=(a-v.val none)*s+v.val none*s := by
  rw [← zNE,zxt ha]
 refine ⟨⟨v.val none,by omega⟩,⟨v.val.some.some (),?_⟩,⟨v.val.some none,by omega⟩⟩
 change v.val.some.some ()<b+(a-v.val none)*s+1
 omega
def gradeIndex {s a b c:ℕ} (m:PieceIndex s a b c) :cV s a b c:= by
  have ha :=zeh m.1.isLt
  have hc:=zeh m.2.2.isLt
  have hb:=zeh m.2.1.isLt
  refine ⟨exponent m.1.val m.2.2.val m.2.1.val,?_⟩
  simp only [cV,Set.mem_ofPred_eq,Finsupp.some_apply,exponent_y,exponent_z,exponent_x]
  refine ⟨ha,hc,?_⟩
  have hs :a*s=(a-m.1.val)*s+m.1.val*s := by
    rw [← zNE,zxt ha]
  omega
private theorem index_ext {s a b c:ℕ} {m n:PieceIndex s a b c}
  (hk :m.1.val=n.1.val) (hi:m.2.1.val=n.2.1.val) (hj:m.2.2.val=n.2.2.val) :
  m=n:= by
 rcases m with ⟨k,i,j⟩
 rcases n with ⟨k',i',j'⟩
 obtain rfl :k=k' := Fin.ext hk
 exact congrArg (Sigma.mk k) (Prod.ext (Fin.ext hi) (Fin.ext hj))
def gradeEquiv (s a b c:ℕ) :cV s a b c ≃ PieceIndex s a b c where
  toFun:=toIndex
  invFun:=gradeIndex
  left_inv v :=Subtype.ext (exponent_eta v.val)
  right_inv m:= by
    apply index_ext <;> simp [toIndex,gradeIndex]
instance (s a b c:ℕ) :Fintype (cV s a b c) :=
 Fintype.ofEquiv _ (gradeEquiv s a b c).symm
instance (K:Type) [Field K] (s a b c:ℕ) :FiniteDimensional K (space K s a b c) :=
 Module.Finite.of_basis (zzc K (cV s a b c))
private theorem count (s a b c:ℕ) :
   2*(Fintype.card (PieceIndex s a b c) :ℤ)=twiceCount s a b c:= by
 have hcard:Fintype.card (PieceIndex s a b c) =
     ∑ k∈z4x (a+1),(b+k*s+1)*(c+1) := by
   rw [zTU]
   simp only [Fintype.card_prod,Fintype.card_fin]
   rw [Fin.sum_univ_eq_sum_range (fun k=>(b+(a-k)*s+1)*(c+1))]
   rw [← Finset.sum_range_reflect (fun k=>(b+k*s+1)*(c+1))]
   simp
 have hs :=congrArg (fun n:ℕ=>(n:ℤ)) (Finset.sum_range_id_mul_two (a+1))
 simp only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_sum,Nat.cast_add,Nat.cast_one,
   Nat.cast_ofNat] at hs
 rw [hcard,Nat.cast_sum]
 push_cast
 simp only [twiceCount,← zkq]
 rw [show (∑ k∈z4x (a+1),((b:ℤ)+(k :ℤ)*s+1)) =
     (a+1)*((b:ℤ)+1)+(∑ k∈z4x (a+1),(k :ℤ))*s from by
   simp_rw [add_right_comm _ _ (1 :ℤ),Finset.sum_add_distrib,Finset.sum_const,
     Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,zkq,mul_add]]
 linear_combination ((c:ℤ)+1)*(s :ℤ)*hs
theorem twice_finrank (K:Type) [Field K] (s a b c:ℕ) :
  2*(Module.finrank K (space K s a b c) :ℤ)=twiceCount s a b c:= by
 rw [space,Module.finrank_eq_card_basis (zzc K (cV s a b c)),
  Fintype.card_congr (gradeEquiv s a b c)]
 exact count s a b c
end
end qBTXDtb
end
