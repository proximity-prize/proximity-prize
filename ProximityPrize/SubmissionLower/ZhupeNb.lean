import ProximityPrize.SubmissionLower.CgH03
import ProximityPrize.SubmissionLower.ZsazLcd
import ProximityPrize.SubmissionLower.ZUItRVc
import ProximityPrize.SubmissionLower.ZzzlQ7b
import ProximityPrize.SubmissionLower.ZCEtgbe
import ProximityPrize.SubmissionLower.ZlH1Cxb
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZRYXIua
import ProximityPrize.SubmissionLower.ZflC1Fd
import ProximityPrize.SubmissionLower.Z32V4rd
import ProximityPrize.SubmissionLower.ZlInw9b
import ProximityPrize.SubmissionLower.ZKUXhzd
import ProximityPrize.SubmissionLower.ZNGQJQc
import ProximityPrize.SubmissionLower.Z0aQQAb
set_option Elab.async false
open _root_ renaming Finset.exists_mem_eq_sup → zOU, Finsupp.add_apply → zSs, Fintype.card_fin → zgY, Fintype.card_sigma → zTU, Function.Injective → zq4, Module.finrank → zsE, Module.finrank_pi_fintype → z0r, MvPolynomial.monomial → ztt, Nat.add_le_add_right → zlr, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.zero_lt_succ → zA8, Polynomial.C → z1z, Polynomial.map_add → zS4, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m, Polynomial.map_sub → z3A, Submodule.zero_mem → z4M
section
set_option autoImplicit true
namespace P5_7_3_3_4_2_1_1
theorem proof :qX9S3Pd.c1 :=
  q9aDOab.rank_bound
end P5_7_3_3_4_2_1_1
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_2_1_2
theorem proof :qX9S3Pd.c2 :=
  q9aDOab.height_family
end P5_7_3_3_4_2_1_2
end
section
section
set_option autoImplicit true
namespace qStFbea
theorem proof :qZcMfNa.c1 :=qtVXGJd.proof
end qStFbea
end
section
set_option autoImplicit true
namespace qfg3dma
theorem proof :qZcMfNa.c2 :=
 qyOEyfe.proof
end qfg3dma
end
section
set_option backward.isDefEq.respectTransparency false
namespace qKzT4va
noncomputable section
open Polynomial Finset
open cu (L)
open qBd5KZd (btN bounded modulus j3)
open qZcMfNa (Padded)
open scoped Classical
open private afg bounded_div bOH fresh no_divisor Stock pack eIR Kt onRows_coeff from ProximityPrize.SubmissionLower.ZzzlQ7b
private abbrev Removed (u v n:ℕ) :=Σ i:Fin (n+1),Fin (n*u+(i:ℕ)*(v-u))
private theorem removed_card (u v n:ℕ) (huv :u≤v) :
  Fintype.card (Removed u v n)=j3 (u+v) n:= by
 rw [zTU]
 simp only [zgY]
 rw [qZCRTge.top_count,show 2*u+(v-u)=u+v by omega]
 rfl
theorem proof :qZcMfNa.c3:= by
  intro E _ _ u v e g M f A B huv hf he hM hA hBdim hSdim
  let _:=hBdim
  let _:=hSdim
  let n:=e+g
  have hM0:0<M:=Nat.zero_lt_of_lt hM
  obtain ⟨b,hb⟩:=fresh hf
  let d:E[X] :=modulus b M
  have hd:d.Monic:=(monic_X_sub_C _).pow M
  have hddeg:d.natDegree=M:= by simp [d,modulus,natDegree_pow]
  have hd1 :d≠1 := fun h=>hM0.ne' (hddeg.symm.trans (by rw [h,natDegree_one]))
  let prod:=(LinearMap.mulLeft L f).comp (pack g M B)
  let T:=(Kt n ((modByMonicHom d).restrictScalars L)).comp prod
  let Q:=(Kt n ((divByMonicHom d).restrictScalars L)).comp prod
  have hp (x :Stock g M B) : (pack g M B x).natDegree≤g :=
    zeh (ofFn_natDegree_lt (zA8 g) _)
  have hpack (x :Stock g M B) :bounded B (pack g M B x) := by
    intro i j
    rw [eIR]
    split_ifs <;> first | exact Subtype.property _ | exact z4M _
  have hprod (x :Stock g M B) :bounded (B+A) (prod x) :=afg hA (hpack x)
  have hpdeg (x :Stock g M B) : (prod x).natDegree≤n:=natDegree_mul_le_of_le he (hp x)
  have htdeg (x :Stock g M B) : (T x).natDegree≤n :=
    zeh (ofFn_natDegree_lt (zA8 n) _)
  have hqdeg (x :Stock g M B) : (Q x).natDegree≤n :=
    zeh (ofFn_natDegree_lt (zA8 n) _)
  have hrem (x :Stock g M B) (i:ℕ) :
      (T x).coeff i=if i<n+1 then (prod x).coeff i %ₘ d else 0:=onRows_coeff n _ _ i
  have hquot (x :Stock g M B) (i:ℕ) :
      (Q x).coeff i=if i<n+1 then (prod x).coeff i /ₘ d else 0:=onRows_coeff n _ _ i
  have hT (x :Stock g M B) :bounded (B+A) (T x) := by
    intro i j
    rw [hrem]
    split_ifs
    · exact (bounded_div (B+A) b M (hprod x i) j).1
    · rw [coeff_zero]; exact z4M _
  have hQ (x :Stock g M B) :bounded (B+A) (Q x) := by
    intro i j
    rw [hquot]
    split_ifs
    · exact (bounded_div (B+A) b M (hprod x i) j).2
    · rw [coeff_zero]; exact z4M _
  have hrel (x :Stock g M B) :f*pack g M B x=T x+C d*Q x := by
    apply Polynomial.ext
    intro i
    change (prod x).coeff i= _
    rw [coeff_add,coeff_C_mul,hrem,hquot]
    split_ifs with hi
    · exact (modByMonic_add_div _ _).symm
    · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le
        ((Nat.succ_le_succ (hpdeg x)).trans (Nat.le_of_not_gt hi))),mul_zero,add_zero]
  have hTin:zq4 T:= by
    apply (injective_iff_map_eq_zero T).mpr
    intro x hx
    have hz :pack g M B x=0:= by
      by_contra hh
      have hdeg: (Bivariate.swap (pack g M B x)).natDegree<M:= by
        apply Nat.lt_of_le_pred hM0
        apply natDegree_le_iff_coeff_eq_zero.mpr
        intro j hj
        apply Polynomial.ext
        intro i
        rw [bOH,coeff_zero,eIR]
        have hk : ¬ j<M:= fun h=>hj.not_ge ((Nat.lt_iff_le_pred hM0).mp h)
        by_cases hi:i<g+1 <;> simp [hi,hk]
      apply no_divisor hf hh hb hdeg
      exact ⟨Q x,by rw [hrel,hx,zero_add]⟩
    funext k
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩:=k
    apply Subtype.ext
    change (x (⟨i,hi⟩,⟨j,hj⟩) :E)=0
    have h:=congrArg (fun P:E[X][X]=>(P.coeff i).coeff j) hz
    simpa only [eIR,dite_eq_left hi,dite_eq_left hj,coeff_zero] using h
  let test :Stock g M B →ₗ[L] (Removed u v n→btN (B+A)) :=LinearMap.pi fun j =>
    ((((lcoeff E (M-1-j.2)).restrictScalars L).comp
      ((lcoeff (E[X]) j.1).restrictScalars L)).comp T).codRestrict _
        (fun x=>hT x j.1 (M-1-j.2))
  let out:=T.comp test.ker.subtype
  refine ⟨b,out.range,?_,?_⟩
  · have hI:zsE L (Stock g M B) =
        ((g+1)*M)*zsE L (btN B) := by
      rw [z0r,sum_const,card_univ,Fintype.card_prod,zgY,
        zgY,Nat.nsmul_eq_mul]
    have hJ:zsE L (Removed u v n→btN (B+A)) =
        j3 (u+v) n*zsE L (btN (B+A)) := by
      rw [z0r,sum_const,card_univ,removed_card u v n huv,Nat.nsmul_eq_mul]
    have hout:zq4 out:= fun x y h=>Subtype.ext (hTin h)
    rw [LinearMap.finrank_range_of_inj hout]
    have hr :=test.range.finrank_le
    have hk :=test.finrank_range_add_finrank_ker
    rw [hJ] at hr
    rw [hI] at hk
    rw [← hk,Nat.add_comm (zsE L test.ker)]
    exact zlr hr _
  · rintro G ⟨x,rfl⟩
    change Padded u v n M (T x.val)∧bounded (B+A) (T x.val)∧_
    refine ⟨⟨htdeg _,?_⟩,hT _,pack g M B x.val,Q x.val,hp _,hqdeg _,hpack _,hQ _,hrel _⟩
    intro i hrow
    have hin:i<n+1 :=zB1 ((le_natDegree_of_ne_zero hrow).trans (htdeg _))
    let k :=((T x.val).coeff i).natDegree
    have hk :k<M:= by
      dsimp only [k]
      rw [hrem,ite_eq_left hin]
      exact (natDegree_modByMonic_lt _ hd hd1).trans_le hddeg.le
    change k+n*u+i*(v-u)<M
    by_contra! hbig
    have htop:M-1-k<n*u+i*(v-u) := by omega
    let j:Removed u v n:=⟨⟨i,hin⟩,⟨M-1-k,htop⟩⟩
    have hzero :=congrArg (fun z :Removed u v n→btN (B+A)=>(z j:E))
      (LinearMap.mem_ker.mp x.property)
    change ((T x.val).coeff i).coeff (M-1-(M-1-k))=0 at hzero
    rw [show M-1-(M-1-k)=k by omega] at hzero
    exact (leadingCoeff_ne_zero.mpr hrow) hzero
end
end qKzT4va
end
section
set_option backward.isDefEq.respectTransparency false
namespace qD58ldc
noncomputable section
open Polynomial

open qZcMfNa (Padded weight)
open qBd5KZd (j3)
open private expand aNF weights c0Q weight_expand coefficient_finrank from ProximityPrize.SubmissionLower.ZCEtgbe
variable {E :Type} [Field E]
private theorem VB (u v n:ℕ) {f :E[X][X]} (hf :f≠0) :
   weight u v n f=(expand f).weightedTotalDegree (weights (v-u))+n*u:= by
 rw [weight_expand]
 let w (i:ℕ) :=(f.coeff i).natDegree+i*(v-u)
 change f.support.sup (fun i=>(f.coeff i).natDegree+n*u+i*(v-u))=f.support.sup w+n*u
 apply le_antisymm
 · apply Finset.sup_le
   intro i hi
   have h:=Finset.le_sup (f :=w) hi
   dsimp only [w] at h ⊢
   omega
 · obtain ⟨i,hi,he⟩:=zOU _ (support_nonempty.mpr hf) w
   rw [he]
   have h:=Finset.le_sup (f := fun i=>(f.coeff i).natDegree+n*u+i*(v-u)) hi
   dsimp only [w]
   omega
private theorem padded_lt {u v n M:ℕ} {G:E[X][X]} (hG:G≠0)
  (h:Padded u v n M G) :weight u v n G<M:= by
 obtain ⟨i,hi,he⟩:=zOU _ (support_nonempty.mpr hG)
  (fun i=>(G.coeff i).natDegree+n*u+i*(v-u))
 unfold weight
 exact he.symm ▸ h.2 i (mem_support_iff.mp hi)
private def width (u v k j i:ℕ) :=j*(u+v)-(k*u+i*(v-u))
private abbrev Slot (u v k j:ℕ) :=Σ i:Fin (k+1),Fin (width u v k j i)
private def slotExp {u v k j:ℕ} (t:Slot u v k j) :Option Unit →₀ ℕ :=
 (Finsupp.single () t.2.val).optionElim t.1.val
private theorem cp4 {u v k j:ℕ} (huv :u≤v) (hj:j≤k) :
  Fintype.card (Slot u v k j)≤j3 (u+v) j:= by
 rw [zTU]
 simp only [zgY]
 have hu:2*u+(v-u)=u+v := by omega
 simpa only [hu,width,j3] using qZCRTge.tail_count k j u (v-u) hj
private theorem quotient_slots {u v e k j W:ℕ} {f q:E[X][X]}
  (hf :f≠0) (hq:q≠0) (he :f.natDegree=e) (hW:W<weight u v e f)
  (hpad:Padded u v (e+k) (W+1+j*(u+v)) (f*q))
  {x :Option Unit →₀ ℕ} (hx :x∈(expand q).support) :
  x∈Set.range (@slotExp u v k j) := by
 have hG:=mul_ne_zero hf hq
 have htop:=padded_lt hG hpad
 rw [VB _ _ _ hf] at hW
 rw [VB _ _ _ hG,map_mul,MvPolynomial.weightedTotalDegree_mul _ _ _
  ((map_ne_zero_iff _ expand.injective).mpr hf) ((map_ne_zero_iff _ expand.injective).mpr hq),
  Nat.add_mul] at htop
 have ht:=MvPolynomial.le_weightedTotalDegree (weights (v-u)) hx
 rw [c0Q] at ht
 have hk :=hpad.1
 rw [Polynomial.natDegree_mul hf hq,he] at hk
 have hi:x none≤q.natDegree :=le_natDegree_of_ne_zero fun hz =>
  (MvPolynomial.mem_support_iff.mp hx) (by rw [aNF,hz,Polynomial.coeff_zero])
 have hs :x.some ()<width u v k j (x none) := by
  unfold width
  omega
 refine ⟨⟨⟨x none,by omega⟩,⟨x.some (),hs⟩⟩,?_⟩
 change (Finsupp.single () (x.some ())).optionElim (x none)=x
 rw [← Finsupp.unique_single x.some,Finsupp.optionElim_some]
private def outputs (u v k j:ℕ) (f :E[X][X]) :Submodule E (MvPolynomial (Option Unit) E) :=
 Submodule.span E (Set.range fun t:Slot u v k j=>expand f*ztt (slotExp t) 1)
private theorem mem_outputs {u v e k j W:ℕ} {f G:E[X][X]}
   (hf :f≠0) (he :f.natDegree=e) (hW:W<weight u v e f)
   (hpad:Padded u v (e+k) (W+1+j*(u+v)) G) (hd:f∣G) :
   expand G∈outputs u v k j f := by
 obtain ⟨q,rfl⟩:=hd
 by_cases hq:q=0
 · simp [hq]
 have hsum:expand (f*q) = ∑ x∈(expand q).support,
     expand f*ztt x ((expand q).coeff x) := by
   rw [map_mul]
   conv_lhs=>rw [(expand q).as_sum,Finset.mul_sum]
 rw [hsum]
 apply Submodule.sum_mem
 intro x hx
 obtain ⟨t,rfl⟩:=quotient_slots hf hq he hW hpad hx
 have hm:expand f*ztt (slotExp t) 1∈outputs u v k j f :=
   Submodule.subset_span ⟨t,rfl⟩
 simpa only [← mul_smul_comm,MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using
   (outputs u v k j f).smul_mem ((expand q).coeff (slotExp t)) hm
theorem proof :qZcMfNa.c4 := by
 classical
 intro E _ _ u v e k j W f A S huv hj hf he hW hA hS hd
 let U:=outputs u v k j f
 have :FiniteDimensional E U:=Module.Finite.span_of_finite _ (Set.finite_range _)
 have hU (G:S) :expand G.val∈U :=
  mem_outputs hf he hW (hS G.val G.property).1 (hd G.val G.property)
 have hdim:zsE E U≤j3 (u+v) j :=
  (finrank_range_le_card _).trans (cp4 huv hj)
 exact (coefficient_finrank A S U hU (fun G=>(hS G.val G.property).2)).trans
  (ztf _ hdim)
end
end qD58ldc
end
end
section
set_option backward.isDefEq.respectTransparency false
namespace qLe9wYc
noncomputable section
open Polynomial Finset
open cu (L)
open E7 (CurvePlace)
open XX (aoG)
open qBd5KZd (small modulus)
open qZcMfNa (Padded BA cleared_map)
open private inclusion liftBi orderIdeal from ProximityPrize.SubmissionLower.ZsazLcd
open private cleared_scale from ProximityPrize.SubmissionLower.Z5rjxle
open scoped WithZero nonZeroDivisors
private theorem dLK {S:Type} [Field S] {P Q:S[X]} {G:S[X][X]}
   {u v n M:ℕ} (huv :u≤v) (hP:P.natDegree≤v) (hQ:Q.natDegree≤u)
   (hG:Padded u v n M G) (hM:0<M) : (BA n P Q G).natDegree<M:= by
 classical
 apply Nat.lt_of_le_pred hM
 refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
 by_cases h:G.coeff j=0
 · simp [h]
 have hjn:=zeh (mem_range.mp hj)
 have hp: (P^j).natDegree≤j*v :=natDegree_pow_le.trans (zBI _ hP)
 have hq: (Q^(n-j)).natDegree≤(n-j)*u :=
   natDegree_pow_le.trans (zBI _ hQ)
 have he :n*u+j*(v-u)=j*v+(n-j)*u:= by
   rw [Nat.mul_sub_left_distrib,Nat.sub_mul]
   have :=zBI j huv
   have :=ztf u hjn
   omega
 have hj:=hG.2 j h
 rw [add_assoc,he] at hj
 calc
   _≤(G.coeff j).natDegree+j*v+(n-j)*u :=
     natDegree_mul_le_of_le (natDegree_mul_le_of_le le_rfl hp) hq
   _≤M-1 := by omega
private theorem cleared_eval {S D:Type} [CommRing S] [CommRing D]
  (a :S[X] →+* D) (x :D) (P Q:S[X]) {f :S[X][X]} {n:ℕ}
  (hf :f.natDegree≤n) (hx :x*a Q=a P) :
  a (BA n P Q f)=f.eval₂ a x*(a Q)^n:= by
 rw [eval₂_eq_sum_range' _ (zB1 hf)]
 simp only [BA,map_sum,map_mul,map_pow,sum_mul]
 refine sum_congr rfl fun j hj => ?_
 have hsplit :j+(n-j)=n:=Nat.add_sub_of_le (zeh (mem_range.mp hj))
 have hpow: (a Q)^n=(a Q)^j*(a Q)^(n-j) := by rw [← pow_add,hsplit]
 rw [hpow,← hx,mul_pow]
 ac_rfl
private theorem reduced_resultant {S:Type} [CommRing S] [Nontrivial S]
   (P Q d:S[X]) (f G H R:S[X][X]) {e g n:ℕ}
   (he :e≠0) (hf :f.natDegree≤e) (hg:G.natDegree≤g)
   (hGn:G.natDegree≤n) (hRn:R.natDegree≤n)
   (hQ:IsUnit Q.leadingCoeff) (hd:d.Monic)
   (hdeg: (BA n P Q G).natDegree<d.natDegree)
   (hroot :BA e P Q f=0) (hrel :f*H=G+Polynomial.C d*R) :
   f.resultant G e g=0:= by
 let D:=Localization.Away Q
 let a :S[X] →+* D:=algebraMap S[X] D
 have hQreg:Q∈S[X]⁰:=mem_nonZeroDivisors_of_leadingCoeff hQ.mem_nonZeroDivisors
 have ha :zq4 a :=IsLocalization.injective (M:=Submonoid.powers Q) D (by
   rintro _ ⟨j,rfl⟩
   exact pow_mem hQreg j)
 let x :D:=IsLocalization.mk' D P ⟨Q,Submonoid.mem_powers Q⟩
 have hx :x*a Q=a P:=IsLocalization.mk'_spec D P _
 let ev :=eval₂RingHom a x
 have evC (z :S[X]) :ev (z1z z)=a z :=eval₂_C _ _
 have eu (j:ℕ) :IsUnit ((a Q)^j) :=IsLocalization.Away.algebraMap_pow_isUnit Q _
 have hz {p:S[X][X]} {j:ℕ} (hp:p.natDegree≤j) (hc:BA j P Q p=0) :
     ev p=0:= by
   have h:=cleared_eval a x P Q hp hx
   rw [hc,map_zero] at h
   exact (eu j).mul_right_cancel (h.symm.trans (zero_mul _).symm)
 have hf0:=hz hf hroot
 have h:=congrArg ev hrel
 change ev (f*H)=ev (G+Polynomial.C d*R) at h
 simp only [map_mul,map_add,evC,hf0,zero_mul] at h
 have hcong:BA n P Q G+d*BA n P Q R=0:= by
   apply ha
   rw [map_add,map_mul,cleared_eval a x P Q hGn hx,cleared_eval a x P Q hRn hx,
     map_zero,← mul_assoc,← add_mul]
   change (ev G+a d*ev R)*(a Q)^n=0
   rw [← h,zero_mul]
 have hG0:BA n P Q G=0:= by
   by_contra hn
   have hv :d∣BA n P Q G:=⟨-BA n P Q R,by
     rw [mul_neg]
     exact eq_neg_of_add_eq_zero_left hcong⟩
   exact hdeg.not_ge (hd.natDegree_le_of_dvd hn hv)
 have hg0:=hz hGn hG0
 obtain ⟨U,V,_,_,hUV⟩:=exists_mul_add_mul_eq_C_resultant f G hf hg (Or.inl he)
 apply ha
 simpa only [map_add,map_mul,evC,hf0,hg0,zero_mul,add_zero,map_zero] using
   (congrArg ev hUV).symm
variable {E :Type} [Field E] [Algebra L E]
private theorem local_resultant (w:CurvePlace L E) (P Q:L[X]) (b:L)
    (f G H R:E[X][X]) {u v n m M:ℕ}
    (huv :u≤v) (hM:0<M) (hfpos :0<f.natDegree)
    (hQ0:Q≠0) (hP:P.natDegree≤v) (hQ:Q.natDegree≤u)
    (hRd:R.natDegree≤n) (hGpad:Padded u v n M G)
    (hif : ∀ i j,w.value ((f.coeff i).coeff j)≤1)
    (hiG : ∀ i j,w.value ((G.coeff i).coeff j)≤1)
    (hiH : ∀ i j,w.value ((H.coeff i).coeff j)≤1)
    (hiR : ∀ i j,w.value ((R.coeff i).coeff j)≤1)
    (hz : ∀ i,small w (-(m:ℤ))
      ((BA f.natDegree (P.map (algebraMap L E)) (Q.map (algebraMap L E)) f).coeff i))
    (heq :f*H=G+Polynomial.C (modulus b M)*R) (j:ℕ) :
    small w (-(m:ℤ)) ((f.resultant G).coeff j) := by
  let O:=w.value.valuationSubring
  let a :=inclusion w
  let c:=aoG w
  let ρ:=Ideal.Quotient.mk (orderIdeal w m)
  let P₀:=P.map c
  let Q₀:= Q.map c
  let d:O[X] :=(Polynomial.X-Polynomial.C (c b))^M
  obtain ⟨F,hF⟩:=liftBi w f hif
  obtain ⟨G₀,hG₀⟩:=liftBi w G hiG
  obtain ⟨H₀,hH₀⟩:=liftBi w H hiH
  obtain ⟨R₀,hR₀⟩:=liftBi w R hiR
  have ha :zq4 a :=w.value.valuationSubring.toSubring.subtype_injective
  have hb:zq4 (mapRingHom a) :=zTo a ha
  have hc:a.comp c=algebraMap L E :=rfl
  have hd:d.map a=modulus b M:= by
    simp only [d,modulus,z5m,z3A,map_X,map_C]
    rfl
  have hrel :F*H₀=G₀+Polynomial.C d*R₀:= by
    apply zTo (mapRingHom a) hb
    rw [zNl,zS4,zNl,map_C,hF,hG₀,hH₀,hR₀,coe_mapRingHom,hd]
    exact heq
  have hmap (N :ℕ) (B:O[X][X]) :
      (BA N P₀ Q₀ B).map a =
        BA N (P.map (algebraMap L E)) (Q.map (algebraMap L E)) (B.map (mapRingHom a)) := by
    simp only [cleared_map,P₀,Q₀,zoi,hc]
  let e :=f.natDegree
  let g:=G.natDegree
  have hFd:F.natDegree=e :=
    (natDegree_map_eq_of_injective hb F).symm.trans (congrArg natDegree hF)
  have hGd:G₀.natDegree=g :=
    (natDegree_map_eq_of_injective hb G₀).symm.trans (congrArg natDegree hG₀)
  have hR₀d:R₀.natDegree≤n:= by
    rw [← natDegree_map_eq_of_injective hb R₀,hR₀]
    exact hRd
  have hF0: (BA e P₀ Q₀ F).map ρ=0:= by
    ext i
    rw [coeff_map,coeff_zero,Ideal.Quotient.eq_zero_iff_mem]
    change small w (-(m:ℤ)) (a ((BA e P₀ Q₀ F).coeff i))
    rw [← coeff_map,hmap,hF]
    exact hz i
  have hGdeg: ((BA n P₀ Q₀ G₀).map ρ).natDegree<M:= by
    refine natDegree_map_le.trans_lt ?_
    rw [← natDegree_map_eq_of_injective ha (BA n P₀ Q₀ G₀),hmap,hG₀]
    exact dLK huv (natDegree_map_le.trans hP) (natDegree_map_le.trans hQ) hGpad hM
  have hzero : (F.resultant G₀ e g).map ρ=0:= by
    rcases subsingleton_or_nontrivial (O ⧸ orderIdeal w m) with hS | hS
    · let _:=hS
      exact Subsingleton.elim _ _
    let _:=hS
    change (mapRingHom ρ) (F.resultant G₀ e g)=0
    rw [← resultant_map_map (S:=(O ⧸ orderIdeal w m)[X]) F G₀ e g (mapRingHom ρ)]
    have hunit :IsUnit (Q₀.map ρ).leadingCoeff := by
      simp only [Q₀,zoi]
      rw [leadingCoeff_map_of_injective (ρ.comp c).injective]
      exact (leadingCoeff_ne_zero.mpr hQ0).isUnit.map _
    let red:=mapRingHom ρ
    refine reduced_resultant (P₀.map ρ) (Q₀.map ρ) (d.map ρ)
      (F.map red) (G₀.map red) (H₀.map red) (R₀.map red) (e :=e) (g:=g) (n:=n)
      hfpos.ne' (natDegree_map_le.trans hFd.le) (natDegree_map_le.trans hGd.le)
      (natDegree_map_le.trans (hGd.trans_le hGpad.1)) (natDegree_map_le.trans hR₀d)
      hunit (((monic_X_sub_C (c b)).pow M).map ρ) ?_ ?_ ?_
    · dsimp only [red]
      rw [← cleared_map,show (d.map ρ).natDegree=M by
        simp only [d,z5m,z3A,map_X,map_C,
          (monic_X_sub_C (ρ (c b))).natDegree_pow,natDegree_X_sub_C,mul_one]]
      exact hGdeg
    · dsimp only [red]
      rwa [← cleared_map]
    · change F.map red*H₀.map red=G₀.map red+Polynomial.C (red d)*R₀.map red
      rw [← map_C red,← zNl,← zNl,← zS4,hrel]
  have hj:ρ ((F.resultant G₀ e g).coeff j)=0:= by rw [← coeff_map,hzero,coeff_zero]
  have hsmall:=Ideal.Quotient.eq_zero_iff_mem.mp hj
  change small w (-(m:ℤ)) (a ((F.resultant G₀ e g).coeff j)) at hsmall
  have hres : (F.resultant G₀ e g).map a=f.resultant G:= by
    change (mapRingHom a) (F.resultant G₀ e g)= _
    rw [← resultant_map_map,hF,hG₀]
  rwa [← coeff_map,hres] at hsmall
private theorem amI (w:CurvePlace L E) {a z :E} {s t:ℤ}
  (ha :w.value a=WithZero.exp s) :
  small w t (a*z)↔small w (t-s) z := by
 have ht:WithZero.exp t=WithZero.exp s*WithZero.exp (t-s) := by
  rw [← WithZero.exp_add,add_sub_cancel]
 simp only [small,map_mul,ha,ht,mul_le_mul_iff_right₀ (WithZero.exp_pos (a :=s))]
theorem proof :qZcMfNa.c5:= by
  intro T C P Q u v k m M b f G H R A V huv hfpos hM hPQ _hHd hRd hV hf hG hH hR hz hpad heq j t
  let w:=C.Ia t
  let a₀:=A w
  have hVw:V w=0:=hV t
  have hVA: (V+A) w=a₀:= by rw [zSs,hVw,zero_add]
  obtain ⟨a,ha⟩:=w.normalized (WithZero.exp (-(a₀:ℤ)))
  have ha0:a≠0:= by
    intro h
    rw [h,map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let sc (p:C.E[X][X]) :=z1z (z1z a)*p
  have hs (p:C.E[X][X]) : (sc p).natDegree=p.natDegree :=
    natDegree_C_mul (Polynomial.C_ne_zero.mpr ha0)
  have hcoeff (p:C.E[X][X]) (i l:ℕ) : ((sc p).coeff i).coeff l=a*(p.coeff i).coeff l:= by
    simp only [sc,coeff_C_mul]
  have hint {p:C.E[X][X]} (hp : ∀ i l,small w (a₀:ℤ) ((p.coeff i).coeff l)) :
      ∀ i l,w.value (((sc p).coeff i).coeff l)≤1 := by
    intro i l
    rw [← WithZero.exp_zero (M:=ℤ),hcoeff]
    change small w 0 (a*(p.coeff i).coeff l)
    exact (amI w ha).2 (by simpa using hp i l)
  have hH₀ (i l:ℕ) :w.value ((H.coeff i).coeff l)≤1 := by
    have hh:small w (V w) ((H.coeff i).coeff l) :=hH i l w
    simpa only [small,hVw,Nat.cast_zero,WithZero.exp_zero] using hh
  have hGA (i l:ℕ) :small w a₀ ((G.coeff i).coeff l) :=hVA ▸ hG i l w
  have hRA (i l:ℕ) :small w a₀ ((R.coeff i).coeff l) :=hVA ▸ hR i l w
  have hz₀ (i:ℕ) :small w (-(m:ℤ))
      ((BA (sc f).natDegree ((P t).map (algebraMap L C.E))
        ((Q t).map (algebraMap L C.E)) (sc f)).coeff i) := by
    rw [hs]
    dsimp only [sc]
    rw [cleared_scale,coeff_C_mul,amI w ha]
    have h:=hz t i
    change small w ((a₀:ℤ)-(m:ℤ)) _ at h
    convert h using 1
    omega
  have hpad₀:Padded u v ((sc f).natDegree+k) M (sc G) := by
    rw [hs]
    refine ⟨(hs G).trans_le hpad.1,fun i hi => ?_⟩
    dsimp only [sc] at hi ⊢
    rw [coeff_C_mul] at hi ⊢
    exact (zlr (zlr (natDegree_C_mul_le _ _) _) _).trans_lt
      (hpad.2 i (fun h=>hi (by rw [h,mul_zero])))
  have heq₀:sc f*H=sc G+Polynomial.C (modulus b M)*sc R:= by
    dsimp only [sc]
    rw [mul_assoc,heq]
    ring
  obtain ⟨hQ0,hQd,hPd⟩:=hPQ t
  have h:=local_resultant w (P t) (Q t) b (sc f) (sc G) H (sc R) huv hM
    (hs f ▸ hfpos) hQ0 hPd hQd (show (sc R).natDegree≤(sc f).natDegree+k by
      rw [hs,hs]; exact hRd) hpad₀ (hint (fun i l=>hf i l w)) (hint hGA) hH₀ (hint hRA) hz₀ heq₀ j
  simp only [hs,sc,resultant_C_mul_left,resultant_C_mul_right,← mul_assoc,← map_pow] at h
  rw [← Polynomial.C_mul,← pow_add,coeff_C_mul] at h
  have hpow:w.value (a^(f.natDegree+G.natDegree)) =
      WithZero.exp (-((f.natDegree :ℤ)+(G.natDegree :ℤ))*(a₀:ℤ)) := by
    rw [map_pow,ha,← WithZero.exp_nsmul,nsmul_eq_mul,Nat.cast_add]
    congr 1
    ring
  have hout: ((f.natDegree•(V+A)+G.natDegree•A) w:ℤ) =
      ((f.natDegree :ℤ)+(G.natDegree :ℤ))*(a₀:ℤ) := by
    simp only [zSs,Finsupp.smul_apply,nsmul_eq_mul,hVA,Nat.cast_add,Nat.cast_mul]
    change (f.natDegree :ℤ)*a₀+(G.natDegree :ℤ)*a₀= _
    ring
  change small w (((f.natDegree•(V+A)+G.natDegree•A) w:ℤ)-(m:ℤ)) _
  rw [hout]
  have hh:=(amI w hpow).1 h
  convert hh using 1
  ring
end
end qLe9wYc
end
section
set_option autoImplicit true
namespace qeUU4Yd
theorem a_1 :q0mTRkc.c1 :=qaAXjzc.proof
theorem a_2 :q0mTRkc.c2 :=quA006b.proof
theorem a_3:q0mTRkc.c3:=q516YUa.proof
theorem a_4_1 :qJh2f6d.c1 :=qDcYfMc.proof
theorem a_4_2 :qJh2f6d.c2 :=qbeSBca.proof
theorem a_4_3:qJh2f6d.c3:=qQ1s08b.proof
theorem a_4_4 :qJh2f6d.c4 :=qMDQ8Za.proof
theorem a_4_5:qJh2f6d.c5:=qPq7Shb.proof
theorem a_4_6:qJh2f6d.c6:=qF6fTmd.proof
theorem a_4 :q0mTRkc.c4 :=qJh2f6d.of_children a_4_1 a_4_2 a_4_3 a_4_4 a_4_5 a_4_6
theorem a_5_1 :qJm9rWb.c1 :=qVP0NNc.proof
theorem a_5_2 :qJm9rWb.c2 :=quQ0Dxa.proof
theorem a_5:q0mTRkc.c5:=qJm9rWb.of_children a_5_1 a_5_2
theorem a_6_1 :qeBKasb.c1 :=q6kkC0d.proof
theorem a_6_2 :qeBKasb.c2 :=qrqpbQa.proof
theorem a_6_3:qeBKasb.c3:=q43OGpb.proof
theorem a_6:q0mTRkc.c6:=qeBKasb.of_children a_6_1 a_6_2 a_6_3
theorem a_7:q0mTRkc.c7:=qWsLKEa.proof
theorem proof :qNUt03b.c4 :=q0mTRkc.of_children a_1 a_2 a_3 a_4 a_5 a_6 a_7
end qeUU4Yd
end
section
set_option autoImplicit true
namespace qFw4O1a
theorem proof :qDxaYpa.c5 :=
  qZcMfNa.of_children qStFbea.proof qfg3dma.proof
    qKzT4va.proof qD58ldc.proof qLe9wYc.proof
end qFw4O1a
end
section
set_option autoImplicit true
namespace qqARUNb
theorem proof :qDxaYpa.c6 :=
  qxDtRld.of_children q7KvxZa.proof qrU3rOc.proof qYbkOtc.proof
end qqARUNb
end
section
set_option autoImplicit true
namespace qRvOhhe
theorem proof :qWEQiwd.c2 :=
  qBajpRb.of_children
    (qX9S3Pd.of_children P5_7_3_3_4_2_1_1.proof P5_7_3_3_4_2_1_2.proof)
    qMAQGbd.proof
end qRvOhhe
end
