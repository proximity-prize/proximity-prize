import ProximityPrize.SubmissionLower.Zm7WGxe
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.Z0SRqJa
import ProximityPrize.SubmissionLower.Z7Epuse
import ProximityPrize.SubmissionLower.ZjZ6ihd
import ProximityPrize.SubmissionLower.ZpYo3sb
import ProximityPrize.SubmissionLower.ZjpV9lc
set_option Elab.async false
section
open _root_ renaming Algebra.algebraMap→c9,Finset.filter_subset→nI,IsFractionRing.injective→ ov,Polynomial.Bivariate.swap→nq,Polynomial.X→lz,Polynomial.coe_evalRingHom→n5,Polynomial.isPrimitive_of_dvd→nX,Polynomial.natDegree_map_eq_of_injective→ oy,Polynomial.taylor→cy,charP_of_injective_ringHom→ oq,congrArg→lV,left_ne_zero_of_mul→ ox,map_mul→mD,map_pow→lJ,pow_ne_zero→ oj,qWdRihc.Bounded→lI,qWdRihc.specialize→aU
section
namespace q6Ra53a
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open qWdRihc (i5 nC ek)
open private bhI from ProximityPrize.SubmissionLower.CS
private abbrev aQ:=FractionRing i5
private theorem seed_degree_le {f :nC} {h:ℕ} :
   (nq f).natDegree≤h↔lI f h:= by
 unfold lI
 simp only [natDegree_le_iff_coeff_eq_zero]
 constructor
 · intro hf i j hj
   simpa only [bhI,coeff_zero] using
     lV (fun q:i5=>q.coeff i) (hf j hj)
 · intro hf j hj
   apply Polynomial.ext
   intro i
   rw [bhI,coeff_zero]
   exact hf i j hj
private theorem dde {f g:nC} (hf :f≠0) (hg:g≠0) :
   (nq (f*g)).natDegree =
     (nq f).natDegree+(nq g).natDegree := by
 have hn (a :nC) (ha :a≠0) :nq a≠0 :=
   fun h=>ha (Bivariate.swap.injective (h.trans (map_zero nq).symm))
 rw [mD,natDegree_mul (hn f hf) (hn g hg)]
private theorem specialize_ne_zero {q:nC} (hq:q.IsPrimitive) (z :L) :
  aU z q≠0:= by
 intro hz
 apply not_isUnit_X_sub_C z
 apply hq
 apply (C_dvd_iff_dvd_coeff ((lz :i5) - C z) q).mpr
 intro i
 rw [dvd_iff_isRoot,IsRoot.def]
 have he :=lV (fun f :L[X]=>f.coeff i) hz
 simpa only [aU,coe_mapRingHom,coeff_map,n5 ,coeff_zero] using he
private theorem separable_of_degree {f :aQ[X]} (hf :Irreducible f)
  (hd:f.natDegree<p) :f.Separable := by
 let:CharP L p:=oq (c9 K L).injective p
 let:CharP i5 p:=oq (C_injective (R:=L)) p
 let:CharP aQ p :=
  oq (ov i5 aQ) p
 have hpos :=natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hf)
 have hn:f.natDegree - 1+1=f.natDegree := by omega
 have hc: (f.natDegree :aQ)≠0:= by
  rw [Ne,CharP.cast_eq_zero_iff aQ p]
  exact fun h=>(not_le_of_gt hd) (Nat.le_of_dvd hpos h)
 apply (separable_iff_derivative_ne_zero hf).mpr
 intro he
 have hz :=lV (fun g:aQ[X]=>g.coeff (f.natDegree - 1)) he
 have hcast:=lV (fun n:ℕ=>(n:aQ)) hn
 rw [Nat.cast_add,Nat.cast_one] at hcast
 rw [coeff_derivative,hn,coeff_natDegree,coeff_zero] at hz
 rw [hcast] at hz
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf.ne_zero) hc hz
private theorem generic_separable (f :nC) (hp:f.IsPrimitive) (hs :Squarefree f)
    (hd:f.natDegree<p) : (ek f).Separable := by
  let g:=mapRingHom (c9 i5 aQ)
  change (g f).Separable
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero=>exact (hs.ne_zero rfl).elim
  | unit u hu =>
    exact ⟨↑(hu.map g).unit⁻¹,0,by simpa only [zero_mul,add_zero] using (hu.map g).val_inv_mul⟩
  | mul a b ha hb ih =>
    have hbprim:=nX hp (dvd_mul_right b a)
    have hirr :Irreducible (g b) :=
      (hbprim.irreducible_iff_irreducible_map_fraction_map (K:=aQ)).mp hb
    have hdeg: (b*a).natDegree=b.natDegree+a.natDegree :=natDegree_mul hb.ne_zero ha
    have hbd: (g b).natDegree<p:= by
      change (b.map (c9 i5 aQ)).natDegree<p
      rw [oy (ov i5 aQ)]
      omega
    have hcop:IsCoprime (g b) (g a) :=
      (hirr.isCoprime_or_dvd (g a)).resolve_right (fun h =>
        hb.not_isUnit (IsRelPrime.of_squarefree_mul hs dvd_rfl
          (hbprim.dvd_of_fraction_map_dvd_fraction_map h)))
    rw [mD]
    exact (separable_of_degree hirr hbd).mul
      (ih (nX hp (dvd_mul_left a b)) hs.of_mul_right (by omega)) hcop
private theorem extract (f :nC) :
    ∃ (s :i5) (q R:nC),q.IsPrimitive∧R.IsPrimitive∧Squarefree R ∧
      f=C s*q^2*R∧(R=1∨0<R.natDegree) := by
  let:StrongNormalizationMonoid i5:=UniqueFactorizationMonoid.strongNormalizationMonoid
  let:NormalizedGCDMonoid i5:=UniqueFactorizationMonoid.toNormalizedGCDMonoid i5
  obtain ⟨q,R,hf,hs⟩:=exists_sq_mul_squarefree f.primPart
  have hq:=nX f.isPrimitive_primPart
    (hf ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by decide :2≠0)) R)
  have hR:=nX f.isPrimitive_primPart (hf ▸ dvd_mul_left R (q^2))
  have he :f=C f.content*q^2*R:= by
    rw [mul_assoc (C f.content) (q^2),hf]
    exact f.eq_C_content_mul_primPart
  by_cases hd:R.natDegree=0
  · have hC:=eq_C_of_natDegree_eq_zero hd
    refine ⟨f.content*R.coeff 0,q,1,hq,isPrimitive_one,squarefree_one,?_,Or.inl rfl⟩
    calc
      f=C f.content*q^2*C (R.coeff 0) :=
        he.trans (lV (fun S:nC=>C f.content*q^2*S) hC)
      _=C (f.content*R.coeff 0)*q^2*1 := by rw [C_mul,mul_one]; ac_rfl
  · exact ⟨f.content,q,R,hq,hR,hs,he,Or.inr (Nat.pos_of_ne_zero hd)⟩
theorem proof :qWdRihc.c1 := by
 intro H Δ hΔ hB hD
 obtain ⟨s,q,R,hq,hR,hS,he,hpos⟩:=extract Δ
 have hn:C s*q^2*R≠0:=he ▸ hΔ
 have hsq:=ox hn
 have hs :s≠0:=C_ne_zero.mp (ox hsq)
 have hq0:=hq.ne_zero
 have hR0:=hR.ne_zero
 have hseed :=seed_degree_le.mpr hB
 rw [he,dde hsq hR0,dde (C_ne_zero.mpr hs) (oj _ hq0),
   lJ,natDegree_pow,Bivariate.swap_C,oy C_injective] at hseed
 refine ⟨s,q,R,hs,by omega,seed_degree_le.mp (by omega),seed_degree_le.mp (by omega),
   specialize_ne_zero hq,he,?_⟩
 rcases hpos with h | h
 · exact Or.inl h
 · have hdiv :R∣Δ:=⟨C s*q^2,he.trans (mul_comm _ _)⟩
   have hd:R.natDegree<p:=(natDegree_le_of_dvd hdiv hΔ).trans_lt hD
   exact Or.inr ⟨h,hd,generic_separable R hR hS hd⟩
end
end q6Ra53a
end
section
set_option autoImplicit true
set_option maxHeartbeats 800000
namespace qzjCOqe
noncomputable section
open Polynomial qWdRihc
open P5 (K node)
open cu (L j9)
open private zeros_le from ProximityPrize.SubmissionLower.Zm7WGxe
private theorem bound_taylor {f :nC} {H :ℕ} (hf :lI f H) (x :L) :
  lI (cy (C x) f) H := by
 intro i
 rw [taylor_coeff,hasseDeriv_apply,eval_sum,Polynomial.sum_def]
 apply natDegree_sum_le_of_forall_le
 intro j _
 simp only [eval_monomial,← C_eq_natCast,← C_pow]
 exact (natDegree_mul_C_le _ _).trans ((natDegree_C_mul_le _ _).trans (hf j))
private theorem cqu (z x :L) (f :nC) :
  aU z (cy (C x) f)=cy x (aU z f) := by
 simp only [aU,coe_mapRingHom,map_taylor,n5 ,eval_C]
private theorem bOe (z :L) (f :i5) :
 aU z (C f)=C (f.eval z) :=Polynomial.map_C _
private theorem de4 (z :L) :aU z lz=Polynomial.X :=
 Polynomial.map_X _
private theorem specialize_zero_eval (z :L) (f :nC) :
  (aU z f).eval 0=(f.coeff 0).eval z := by
 simp only [← coeff_zero_eq_eval_zero,aU,coe_mapRingHom,coeff_map,n5]
private theorem coeff_shift (f :nC) (k :ℕ) :
  (lz^k*f).coeff k=f.coeff 0:= by
 simpa only [Nat.zero_add] using coeff_X_pow_mul f k 0
private theorem normalize (a b q:nC) (ha :a≠0) :
   ∃ (k :ℕ) (A B Q:nC),a=lz^k*A∧b=lz^k*B ∧
     q=lz^k*Q∧(A.coeff 0≠0∨B.coeff 0≠0∨Q.coeff 0≠0) := by
 classical
 have hex : ∃ j,a.coeff j≠0∨b.coeff j≠0∨q.coeff j≠0 :=
   ⟨a.natDegree,Or.inl (by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr ha)⟩
 let k :=Nat.find hex
 have lower (i:ℕ) (hi:i<k) :a.coeff i=0∧b.coeff i=0∧q.coeff i=0:= by
   simpa only [not_or,not_not] using Nat.find_min hex hi
 have hdA: (lz :nC)^k∣a :=X_pow_dvd_iff.mpr fun i hi=>(lower i hi).1
 have hdB: (lz :nC)^k∣b:=X_pow_dvd_iff.mpr fun i hi=>(lower i hi).2.1
 have hdQ: (lz :nC)^k∣q:=X_pow_dvd_iff.mpr fun i hi=>(lower i hi).2.2
 obtain ⟨A,hA⟩:=hdA
 obtain ⟨B,hB⟩:=hdB
 obtain ⟨Q,hQ⟩:=hdQ
 refine ⟨k,A,B,Q,hA,hB,hQ,?_⟩
 have hk :=Nat.find_spec hex
 change a.coeff k≠0∨b.coeff k≠0∨q.coeff k≠0 at hk
 rw [hA,hB,hQ] at hk
 simpa only [coeff_shift] using hk
private theorem eE6 (J:UJ) (T:Finset K) (x :L)
    {a b q:nC} {s :i5} (ha :a≠0)
    (hr : ∀ γ∈T,
      (aU (J.z γ) a*j9 (J.scalar γ)-aU (J.z γ) b)^2 =
        C (s.eval (J.z γ))*(aU (J.z γ) q)^2) :
    ∃ k :ℕ,let A:=(cy (C x) a).coeff k
      let B:=(cy (C x) b).coeff k
      let Q:=(cy (C x) q).coeff k
      (A≠0∨B≠0∨Q≠0) ∧ ∀ γ∈T,
        (A.eval (J.z γ)*(j9 (J.scalar γ)).eval x - B.eval (J.z γ))^2 =
          s.eval (J.z γ)*(Q.eval (J.z γ))^2 := by
  obtain ⟨k,A,B,Q,hA,hB,hQ,hne⟩ :=
    normalize (cy (C x) a) (cy (C x) b) (cy (C x) q)
      (fun h=>ha ((taylor_eq_zero _ _).mp h))
  refine ⟨k,?_⟩
  dsimp only
  simp only [hA,hB,hQ,coeff_shift]
  refine ⟨hne,?_⟩
  intro γ hγ
  let z :=J.z γ
  let S:=j9 (J.scalar γ)
  have ht:=lV (taylorAlgHom x) (hr γ hγ)
  change (taylorAlgHom x) ((aU z a*S-aU z b)^2) =
    (taylorAlgHom x) (C (s.eval z)*(aU z q)^2) at ht
  simp only [lJ,mD,map_sub] at ht
  change (cy x (aU z a)*cy x S - cy x (aU z b))^2 =
    cy x (C (s.eval z))*(cy x (aU z q))^2 at ht
  rw [taylor_C,← cqu z x a,← cqu z x b,
    ← cqu z x q,hA,hB,hQ] at ht
  simp only [mD,lJ,de4] at ht
  have hc: (aU z A*cy x S-aU z B)^2 =
      C (s.eval z)*(aU z Q)^2 := by
    let w:L[X] :=lz^k
    apply mul_left_cancel₀ (oj 2 (show w≠0 from oj _ Polynomial.X_ne_zero))
    calc
      _=((w*aU z A)*cy x S - w*aU z B)^2 := by ring
      _=C (s.eval z)*(w*aU z Q)^2 :=ht
      _ = _:= by ring
  have he :=lV (evalRingHom (0:L)) hc
  simpa only [lJ,mD,map_sub,n5 ,eval_C,
    specialize_zero_eval,← coeff_zero_eq_eval_zero (cy x S),taylor_coeff_zero] using he
private theorem norm_zero {s u v :i5} (h:v=0 ∨ ¬ ∃ r :i5,r^2=s)
   (he :u^2=s*v^2) :u=0∧v=0:= by
 by_cases hv :v=0
 · exact ⟨sq_eq_zero_iff.mp (by simpa [hv] using he),hv⟩
 obtain hs :=h.resolve_left hv
 let F:=FractionRing i5
 let e :i5 →+* F:=c9 i5 F
 have hi:=ov i5 F
 have hv' : e v≠0:=(map_ne_zero_iff _ hi).mpr hv
 have he' : (e u/e v)^2=e s := by
   rw [div_pow,div_eq_iff (oj 2 hv'),← lJ,← lJ,← mD,he]
 have hint :IsIntegral i5 ((e u/e v)^2) :=he'.symm ▸ isIntegral_algebraMap
 obtain ⟨r,hr⟩:=IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide) hint
 apply (hs ⟨r,hi ?_⟩).elim
 change e (r^2)=e s
 rw [lJ,show e r= _ from hr,he']
private theorem exceptional (J:UJ) (T:Finset K) (hT:T⊆J.CF)
    {a b q:nC} {s :i5} {G H M:ℕ} (ha :a≠0)
    (haG:lI a G) (hbG:lI b G) (hqH :lI q H)
    (hG:2*G≤M) (hH :s.natDegree+2*H≤M)
    (hn:q=0 ∨ ¬ ∃ r :i5,r^2=s)
    (hr : ∀ γ∈T,
      (aU (J.z γ) a*j9 (J.scalar γ)-aU (J.z γ) b)^2 =
        C (s.eval (J.z γ))*(aU (J.z γ) q)^2) :asT J T M:= by
  intro i
  let x :=c9 K L (node i)
  let t:=c9 K L (J.word i)
  obtain ⟨k,hne,hrel⟩:=eE6 J T x ha hr
  let A:=(cy (C x) a).coeff k
  let B:=(cy (C x) b).coeff k
  let Q:=(cy (C x) q).coeff k
  let test :=(C t*A - B)^2 - s*Q^2
  have hA:=bound_taylor haG x k
  have hQ:=bound_taylor hqH x k
  have hit_iff (γ:K) :J.hit γ i↔(j9 (J.scalar γ)).eval x=t:= by
    change _↔((J.scalar γ).map (c9 K L)).eval (c9 K L (node i)) =
      c9 K L (J.word i)
    rw [eval_map_apply,(c9 K L).injective.eq_iff]
    rfl
  by_cases hz :test=0
  · have hzero :=norm_zero (s :=s) (u:=C t*A - B) (v := Q)
      (hn.imp (fun h=> by simp [Q,h]) id) (sub_eq_zero.mp hz)
    have hb:B=C t*A:=(sub_eq_zero.mp hzero.1).symm
    have ha0:A≠0:= by
      intro h
      rcases hne with h' | h' | h'
      · exact h' h
      · exact h' (show B=0 by rw [hb,h,mul_zero])
      · exact h' hzero.2
    right
    refine (zeros_le _ J.z (J.seed_injective.mono ((nI _ _).trans hT))
      ha0 ?_).trans (hA.trans (by omega))
    intro γ hγ
    obtain ⟨hγ,hm⟩:=Finset.mem_filter.mp hγ
    have he : (A.eval (J.z γ)*(j9 (J.scalar γ)).eval x - B.eval (J.z γ))^2 =
        s.eval (J.z γ)*(Q.eval (J.z γ))^2 :=hrel γ hγ
    rw [hzero.2,eval_zero,zero_pow two_ne_zero,mul_zero] at he
    have he :=sq_eq_zero_iff.mp he
    rw [hb,eval_mul,eval_C,mul_comm t (A.eval (J.z γ)),← mul_sub] at he
    exact (mul_eq_zero.mp he).resolve_right
      (sub_ne_zero.mpr fun h=>hm ((hit_iff γ).mpr h))
  · have htest :test.natDegree≤M:= by
      exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_pow_le_of_le _ ((natDegree_sub_le _ _).trans
          (max_le ((natDegree_C_mul_le _ _).trans hA) (bound_taylor hbG x k)))).trans hG)
        ((natDegree_mul_le_of_le le_rfl (natDegree_pow_le_of_le _ hQ)).trans hH))
    left
    refine (zeros_le _ J.z (J.seed_injective.mono ((nI _ _).trans hT))
      hz ?_).trans htest
    intro γ hγ
    obtain ⟨hγ,hh⟩:=Finset.mem_filter.mp hγ
    have he :=hrel γ hγ
    rw [(hit_iff γ).mp hh] at he
    simpa only [test,A,B,Q,eval_sub,eval_pow,eval_mul,eval_C,
      mul_comm t,sub_eq_zero] using he
theorem proof :qWdRihc.c3:= by
  classical
  intro J H a b q s ha haH hbH hqH _ hs hr
  by_cases hsq : ∃ r :i5,r^2=s
  · obtain ⟨r,hsq⟩:=hsq
    have hrH :r.natDegree≤H := by
      rw [← hsq,natDegree_pow] at hs
      omega
    let b' (v :i5) :=b+C v*q
    let T (v :i5) :=J.CF.filter fun γ =>
      aU (J.z γ) a*j9 (J.scalar γ)=aU (J.z γ) (b' v)
    have hex (v :i5) (hv :v.natDegree≤H) :asT J (T v) (4*H) := by
      have hb' : lI (b' v) (2*H) := by
        intro i
        change ((b+C v*q).coeff i).natDegree≤2*H
        rw [coeff_add,coeff_C_mul]
        exact (natDegree_add_le _ _).trans (max_le ((hbH i).trans (by omega))
          ((natDegree_mul_le_of_le hv (hqH i)).trans (by omega)))
      refine exceptional J (T v) (nI _ _) (s :=0) (q:=0)
        (G:=2*H) (H :=0) ha (fun i=>(haH i).trans (by omega)) hb' (by intro i; simp)
        (by omega) (by simp) (Or.inl rfl) ?_
      intro γ hγ
      have he :=(Finset.mem_filter.mp hγ).2
      rw [he,sub_self]
      simp
    refine ⟨T r,T (-r),?_,hex r hrH,hex (-r) (by simpa only [natDegree_neg] using hrH)⟩
    ext γ
    constructor
    · intro hγ
      have join (v :i5)
          (h:aU (J.z γ) a*j9 (J.scalar γ)-aU (J.z γ) b =
            C (v.eval (J.z γ))*aU (J.z γ) q) :γ∈T v := by
        refine Finset.mem_filter.mpr ⟨hγ,?_⟩
        change aU (J.z γ) a*j9 (J.scalar γ)=aU (J.z γ) (b+C v*q)
        rw [map_add,mD,bOe,add_comm (aU (J.z γ) b)]
        exact sub_eq_iff_eq_add.mp h
      have he :=hr γ hγ
      rw [← hsq,eval_pow,lJ,← mul_pow] at he
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
      · exact Finset.mem_union.mpr (Or.inl (join r h))
      · exact Finset.mem_union.mpr (Or.inr (join (-r) (by
          simpa only [eval_neg,map_neg,neg_mul] using h)))
    · intro hγ
      rcases Finset.mem_union.mp hγ with h | h
      · exact nI _ _ h
      · exact nI _ _ h
  · refine ⟨J.CF,∅,by simp,?_,by intro i; simp⟩
    exact exceptional J J.CF (fun _ h=>h) ha haH hbH hqH
      (by omega) (by omega) (Or.inr hsq) hr
end
end qzjCOqe
end
end
section
set_option autoImplicit true
namespace P6_7_4
noncomputable section
open P6 (I)
open P5_7_2 (Aux fO ChosenRow Donors NodeUnits Ls anM jX stages)
open qMNIwTb
open cu (L)
open DP (jF zG aq7 complete VY bga azS)

open private height_guard free_char from ProximityPrize.SubmissionLower.ZQmiAIb
set_option backward.isDefEq.respectTransparency false in
theorem donors (h1 :qMNIwTb.c1) (hpad:PaddedFree)
    (b:fO) (hb₀:2≤b.val) (h:ℕ) (hlo: (jX b).lo≤h) (hhi:h≤(jX b).hi)
    (D:jF h) (hD:NodeUnits D) (Crt:zG D) (word:I→L) :
    Nonempty (Donors b Crt word) := by
  classical
  have hh:=(height_guard b).1.trans_le hlo
  have hu:=hhi.trans (height_guard b).2
  have std (mode) (a :Aux) (ha :Filed b mode a) (hp : ¬ CJ b mode a) :
      0<Mq h a ∧
      (if mode then aMH h a (fullCap a.shape) else 0) <
        rankSum (Mq h a) (VY Crt word a.shape) := by
    have reduce (hw:aL4 h a) {n:ℕ}
        (hn:Module.finrank L (aq7 h word a.shape (anM h a.dI a.shape)) ≤
          n+Module.finrank L (complete Crt word a.shape (anM h a.dI a.shape)))
        (hz :bga a.shape+n<azS h a.shape+O3 h a (fullCap a.shape) mode) :
        0<Mq h a ∧
        (if mode then aMH h a (fullCap a.shape) else 0) <
          rankSum (Mq h a) (VY Crt word a.shape) := by
      refine ⟨width_room hw,?_⟩
      have hf :=physical_to_rank hu Crt word a hw hn
      have he :=ceiling_add_gain h a (fullCap a.shape) (by omega) (fun _=>le_rfl)
      cases mode <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> omega
    by_cases hb:12≤b.val
    · obtain ⟨hB,hw,hz⟩:=qs0zuzc.proof b h hlo hhi hb mode a ha
      exact reduce hw (historical_poles hh hu Crt word a.shape hB _) (by omega)
    · have hb' : b.val<12 := by omega
      obtain ⟨hw,hz⟩:=qpjPzMc.proof b h hlo hhi hb' mode a ha hp
      exact reduce hw (h1 b h hlo hhi hb' mode a ha hp D hD Crt word) hz
  have free (a :Aux) (ha :Filed b false a) :Nonempty (ChosenRow Crt word a.dI a.shape) := by
    by_cases hp:CJ b false a
    · exact hpad b hb₀ h hlo hhi a ha hp D hD Crt word
    · obtain ⟨hr,hz⟩:=std false a ha hp
      exact nonzero_raw hr (fun _=>le_rfl) (by simpa using hz)
  let pick (a :Aux) (ha :Filed b false a) :=Classical.choice (free a ha)
  have freeFiled (s :Ls) (hs :s∈stages b) :Filed b false ⟨s.dI,s.free⟩ :=
    Or.inr ⟨s,hs,rfl⟩
  have mov (s :Ls) (hs :s∈stages b) :
      ∃ Q:ChosenRow Crt word s.dI s.moving,
        qQ.aeH (pick _ (freeFiled s hs)).jet Q.jet:= by
    let a :Aux :=⟨s.dI,s.moving⟩
    have ha :Filed b true a :=Or.inr ⟨s,hs,rfl⟩
    have hp:=free_char b s hs
    have hd : ¬ CJ b true a := by
      simp only [CJ,ite_true]
      omega
    obtain ⟨hr,hz⟩:=std true a ha hd
    have hv :LayeredBank Crt word a (fullCap a.shape) (VY Crt word a.shape) :=
      ⟨hr,fun _=>le_rfl,fun _=>le_rfl,
        fun _ _ hP j i hne =>
          le_min (Nat.le_add_left j i) (DP.d3r Crt word hP j i hne).2.1,
        by simpa using hz⟩
    exact choose_layered hh hu hv (pick _ (freeFiled s hs)) hp
  exact ⟨⟨fun s hs=>⟨pick _ (freeFiled s hs),(mov s hs).choose,(mov s hs).choose_spec⟩,
    fun a ha=>pick a (Or.inl ⟨rfl,ha⟩),fun _ _ _=>rfl⟩⟩
theorem padded_free (hl:qQCEOid.c1)
    (sign : ∀ (b:fO),2≤b.val → ∀ (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
      ∀ (a :Aux),Filed b false a→CJ b false a →
        aL4 h a∧bga a.shape+2*h*qBZoH8d.paddedRank a.shape <
          azS h a.shape+O3 h a (fullCap a.shape) false) :PaddedFree := by
  intro b hb h hlo hhi a ha hpa D _ Crt word
  have hh:=(height_guard b).1.trans_le hlo
  have hu:=hhi.trans (height_guard b).2
  obtain ⟨hw,hz⟩:=sign b hb h hlo hhi a ha hpa
  have hP:=qBZoH8d.c4y (qBZoH8d.from_projective hl) hh (hu.trans_lt (by decide))
    Crt word a.shape (anM h a.dI a.shape)
  have hs :=physical_to_rank hu Crt word a hw hP
  exact nonzero_raw (width_room hw) (fun _=>le_rfl) (by omega)
end
end P6_7_4
end
section
set_option autoImplicit true
namespace P6_7_4
noncomputable section
open Polynomial
open P6 (K p jG)
open P6_7 (YQ RegularBound)
open P5_7_2 (A Aux fO Donors aKj NodeUnits Window Test jX row Lc j3 ZN
  threshold apo seedCap eqx eiO)
open qMNIwTb (Filed CJ aL4 O3 fullCap)
open qBZoH8d (paddedRank)
open cu (L Equation vm yq FX qD kr)
open DP (jF zG aKF VY bga azS)
open Qt (gY Qc)
open qWdRihc (UJ height shorten)
open private budget guards from ProximityPrize.SubmissionLower.Zqb2cFb
open private disc_degree near_guards root_count from ProximityPrize.SubmissionLower.Zm7WGxe
def c1 :Prop :=qQCEOid.c1
def c2 :Prop :=qQCEOid.c2
def c3:Prop :=
  ∀ (b:fO),2≤b.val → ∀ (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ (a :Aux),Filed b false a→CJ b false a →
      aL4 h a∧bga a.shape+2*h*paddedRank a.shape <
        azS h a.shape+O3 h a (fullCap a.shape) false
def c4 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Window b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∀ (D:jF M.iF.toNat),D.block 0=H→D.block 1=H.map (frobenius L p) →
    NodeUnits D→(∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ)) →
    ∀ (Crt:zG D),Donors b Crt (wordLift M) →
      Nonempty (bkU b M F (VY Crt (wordLift M)))
def c5:Prop :=
  ∀ (b:fO),2≤b.val→b.val<12 → ∀ (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ x :Test b,j3 h (Lc b x)<ZN h (Lc b x).shape (threshold x) (apo x)
def c6:Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Window b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∀ (i:aKj b) (f :Equation),
      Dt.Reduced f→f.natDegree=i.val+1→3≤f.natDegree →
      0<gY f→vm f (seedCap b i) →
      ∀ T⊆Γ,(∀ γ∈T,yq f (M.label γ) (F.scalar γ)=0)→T.card≤(row b).Z1
private theorem count_small (b:fO) {u del} (M:jG u del)
    {Γ} (F:P1.bje A M Γ) (hw:Window b M.iF) (i:aKj b) (f :Equation)
    (hf :Dt.Reduced f) (he :f.natDegree≤2) (hs :vm f (seedCap b i))
    (T:Finset K) (hT:T⊆Γ) (hr : ∀ γ∈T,yq f (M.label γ) (F.scalar γ)=0) :
    T.card≤(row b).Z1 := by
  have hg:=near_guards b
  have hhi:=hw.2
  have hh:M.iF.toNat≤(jX b).hi:= by omega
  let J:UJ :=
    ⟨T,fun γ=>algebraMap K L (M.label γ),F.scalar,M.word,
      fun _ _ _ _ h=>sub_left_inj.mp ((algebraMap K L).injective h),F.distinct.mono hT,
      fun γ hγ=>(P6_7.aic F (hT hγ)).trans ((Nat.add_le_add_left hh _).trans hg.1),
      fun γ hγ =>
        let mark :=F.mark γ (hT hγ)
        ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩⟩
  have hv :vm f qWdRihc.seedCap:= fun j=>(hs j).trans Nat.and_le_right
  obtain ⟨a,b',c,hn,ha,hb,hc,ham,hbm,hcm,roots⟩ :=
    shorten J M.label (fun _=>rfl) f (Polynomial.ne_zero_of_natDegree_gt hf.1) he hv hr
  exact (root_count q6Ra53a.proof qtQA4Je.proof qzjCOqe.proof J hn ha hb hc
    (disc_degree ham hbm hcm (by decide)) roots).trans
    ((show 64*height+4≤0x21ba040087f84 from by decide).trans hg.2)
private theorem ecU {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ)
    (T:Finset K) (hT:T⊆Γ) {f :Equation} (hf :0<f.natDegree) (hs :vm f 0)
    (hr : ∀ γ∈T,yq f (M.label γ) (F.scalar γ)=0) :T.card≤f.natDegree := by
  classical
  let g:=f.map (qD 0)
  have hc (z :K) (i:ℕ) :qD z (f.coeff i)=(f.coeff i).coeff 0:= by
    have h:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hs i))
    conv_lhs=>rw [h]
    simp [qD]
  have he (z :K) :f.map (qD z)=g:= by
    ext i
    simp only [g,coeff_map,hc]
  have hn:g≠0:= by
    intro hz
    have hlead:=congrArg (fun G:FX[X]=>G.coeff f.natDegree) hz
    simp only [g,coeff_map,hc,coeff_zero] at hlead
    have h:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero (hs f.natDegree))
    have hfn :f≠0:= fun h0=> by simp [h0] at hf
    exact (leadingCoeff_ne_zero.mpr hfn) (h.trans (by rw [hlead,map_zero]))
  let val := fun γ=>kr (F.scalar γ)
  have hi:Set.InjOn val (T:Set K) :=
    fun _ ha _ hb h=>F.distinct (hT ha) (hT hb) (qQ.bNe h)
  calc
    T.card=(T.image val).card:=(Finset.card_image_of_injOn hi).symm
    _≤g.natDegree :=Polynomial.card_le_degree_of_subset_roots (by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
      apply (Polynomial.mem_roots hn).mpr
      change g.eval (val γ)=0
      rw [← he (M.label γ),Polynomial.eval_map]
      exact hr γ hγ)
    _≤f.natDegree :=Polynomial.natDegree_map_le
private theorem count (hfloor :P5_7_2.c1) (hpole :qMNIwTb.c1) (hpadded:PaddedFree)
    (hprefix :c4) (hsign:c5) (hlarge :c6) (b:fO) (hb:2≤b.val) :
    RegularBound A (jX b) := by
  classical
  intro u del M Γ F hw hshift H bY
  have hwin:Window b M.iF:=hw
  have hlo:=hwin.1
  have hhi:=hwin.2
  have hl: (jX b).lo≤M.iF.toNat := by omega
  have hu:M.iF.toNat≤(jX b).hi:= by omega
  obtain ⟨glo,ghi,gchar,gdegree⟩:=guards b
  have margin (x :Test b) :
      j3 M.iF.toNat (Lc b x) <
        ZN M.iF.toNat (Lc b x).shape (threshold x) (apo x) := by
    by_cases hr :b.val<12
    · exact hsign b hb hr _ hl hu x
    · exact qMHqmcc.checked hl (hu.trans (Nat.le_of_lt ghi)) (qwtjEYd.proof b (by omega) x)
  obtain ⟨D,hfirst,hadjacent,hnode,hres⟩:=P6_7.bW4 M F H bY
  obtain ⟨Crt⟩:=atp.dRH D
  obtain ⟨R⟩:=donors hpole hpadded b hb _ hl hu D hnode Crt (wordLift M)
  obtain ⟨Q⟩:=hprefix b hb u del M Γ F hwin hshift H bY D hfirst hadjacent hnode hres Crt R
  let T:=Γ \ Q.gH
  have hT:T⊆Γ:=Finset.sdiff_subset
  have hp: (Γ \ T).card≤(row b).prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.paid_bound
    intro γ hγ
    obtain ⟨hmem,hnot⟩:=Finset.mem_sdiff.mp hγ
    by_contra hn
    exact hnot (Finset.mem_sdiff.mpr ⟨hmem,hn⟩)
  suffices hkept:T.card≤(row b).Z1 by
    exact (Finset.card_sdiff_add_card_eq_card hT ▸ Nat.add_le_add hp hkept).trans (budget b)
  have cover : ∀ γ∈T,∃ q∈Q.parents,P6_7.axy M F q γ:= fun γ hγ =>
    (Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  by_cases hm:T.Nonempty
  · obtain ⟨γ,hγ⟩:=hm
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
    obtain ⟨i,he,hs⟩:=eiO (b:=b) hf.positive (fun x hE hv =>
      (margin x).not_ge (eqx Crt (wordLift M) (glo.trans_le hl)
        (hu.trans_lt ghi) gchar Q.geometric Q.terminal_pass hf x (hfloor b _ hl hu D hnode Crt _ x) hE hv))
    have roots : ∀ η∈T,yq f (M.label η) (F.scalar η)=0:= by
      intro η hη
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz
    by_cases hzero :gY f=0
    · exact (ecU M F T hT hf.positive ((Qc f 0).mp hzero.le) roots).trans
        ((he.trans_le (Nat.succ_le_of_lt i.isLt)).trans gdegree)
    have hseed :=Nat.pos_of_ne_zero hzero
    have hred:Dt.Reduced f :=⟨hf.positive,hf.primitive,hf.separable⟩
    by_cases hsmall:f.natDegree≤2
    · exact count_small b M F hwin i f hred hsmall hs T hT roots
    · exact hlarge b hb u del M Γ F hwin hshift H bY i f hred he (by omega) hseed hs T hT roots
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) :P6_7.c4 := by
  intro r hr
  obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hr
  change i<(P5_7.nearRows.drop 2).length at hi
  have hindex :2+i<P5_7.nearRows.length:= by rw [List.length_drop] at hi; omega
  have hget: (P5_7.nearRows.drop 2)[i]=jX ⟨2+i,hindex⟩:=List.getElem_drop
  rw [hget]
  have hlocal:=qQCEOid.of_children h1 h2
  exact count (qjf96Pd.of_children (qjf96Pd.reciprocal_of_local hlocal) qqXHigb.proof)
    (qlHk46d.of_children h1 h2) (padded_free h1 h3) h4 h5 h6 ⟨2+i,hindex⟩ (by simp)
end
end P6_7_4
end
