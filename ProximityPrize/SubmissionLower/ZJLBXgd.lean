import ProximityPrize.SubmissionLower.Zn9MhWd
import ProximityPrize.SubmissionLower.ZK15T2b
set_option Elab.async false
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qQNoJ5c
noncomputable section
open Polynomial
open P5 (K p)
open P5_7 (midAgreement)

open qAxtVye (HorizontalBand graphUnit aSz)
open private ePj co9 interpolate horizontalBase_mono from ProximityPrize.SubmissionLower.ZK15T2b
open cu (aZ qD)
open gT (Ambient aQ abX)
open pI (acW by6)
open YY (xg Si U7 by9 aef a9E)
open private cag c2p c0U ddj b1I diE from ProximityPrize.SubmissionLower.G
open scoped BigOperators Classical
def aHl {maxHeight u del} {M:P1.FJ maxHeight u del} {Γ} (F:P1.bje midAgreement M Γ) (C:acW) :
    Finset K:=C.qv.biUnion fun I=>Γ.filter (I0 F I)
theorem ez0 {maxHeight u del} {M:P1.FJ maxHeight u del} {Γ} {F:P1.bje midAgreement M Γ}
    {C:acW} {γ:K} (hγ:γ∈Γ) {I:Ideal Ambient} (hI:I∈C.qv)
    (hm:I0 F I γ) :γ∈aHl F C :=
  Finset.mem_biUnion.mpr ⟨I,hI,Finset.mem_filter.mpr ⟨hγ,hm⟩⟩
private theorem cZQ {maxHeight u del} {M:P1.FJ maxHeight u del} {Γ} (F:P1.bje midAgreement M Γ)
    {I:Ideal Ambient} {C:aZ} (hC:xg I=Ideal.span {C}) :
    ∀ z∈(Γ.filter (I0 F I)).image M.label,qD z C=0:= by
  intro z hz
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
  apply c2p (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem dhW {maxHeight u del} (M:P1.FJ maxHeight u del) (T:Finset K) :
    (T.image M.label).card=T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab=>sub_left_inj.mp hab)
private theorem fTy {b maxHeight u del} {M:P1.FJ maxHeight u del} {Γ}
    (F:P1.bje midAgreement M Γ)
    (uq:aKd b M F) (gp4 :HorizontalBand b→HorizontalTariff b M F)
    {a h cap:ℚ} (rate :aSz b cap a h) {I:Ideal Ambient} (geom:by6 I)
    (hcap: (aef I:ℚ)≤ cap) (hp:aef I<p) :
    ((Γ.filter (I0 F I)).card:ℚ) ≤
      a*(aef I:ℚ)+h*(a9E I:ℚ)+aef I:= by
  let T:=Γ.filter (I0 F I)
  let D:=aef I
  let H :=a9E I
  have hD: (0:ℚ)≤D:=Nat.cast_nonneg _
  have hH : (0:ℚ)≤H :=Nat.cast_nonneg _
  obtain ⟨f,hf,he,hpos,hd⟩:=GK.proof I (co9 geom)
  have hdq: (f.totalDegree :ℚ)≤D:= by exact_mod_cast hd
  by_cases hconst:by9 (xg I)
  · obtain ⟨Q,hQ,heQ⟩:=hconst
    have hdeg:f.totalDegree= Q.totalDegree :=b1I f hf.ne_zero Q (he.symm.trans heQ)
    have hδ:0<Q.totalDegree :=hdeg ▸ hpos
    obtain ⟨g,hg,hroot,hgD⟩:=ePj I Q (co9 geom) geom.2.2.2.2 hQ heQ
    have hgcap:g≤D:=(Nat.le_mul_of_pos_left g hδ).trans hgD
    have hlen:Module.finrank aQ (abX (Si I))= Q.totalDegree*g:= by
      obtain ⟨_,Q',hQ',hQ'proj,_,hlen,_,_⟩:=hroot
      have heQ' : xg I=Ideal.span {MvPolynomial.map U7 Q'} := hQ'proj
      have hdeg' := b1I f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen,← hdeg',hdeg]
    have hmarks : ∀ γ∈T,gT.aSf (Si I) (M.label γ) (F.scalar γ) :=
      fun _ hz=>cag (Finset.mem_filter.mp hz).2
    let x :ℚ:=(Q.totalDegree :ℚ)*g
    let direct :=graphUnit/(g:ℚ)
    have hx :0≤x := by dsimp [x]; positivity
    have hxD:x≤D:= by dsimp [x]; exact_mod_cast hgD
    have hgq: (0:ℚ)≤g:=Nat.cast_nonneg _
    have hdir : (T.card:ℚ)≤direct*x := by
      have hcount:=ddj f hf.ne_zero (hd.trans_lt hp) (T.image M.label) (cZQ F he)
      rw [dhW,hdeg] at hcount
      have hcast: (T.card:ℚ)≤graphUnit*(Q.totalDegree :ℚ) := by exact_mod_cast hcount
      refine hcast.trans_eq ?_
      have hgz : (g:ℚ)≠0:= by exact_mod_cast hg.ne'
      dsimp only [direct,x]
      field_simp [hgz]
    have hpay : (T.card:ℚ)≤a*x+h*H+g:= by
      by_cases ha :a<direct
      · rcases rate.interpolation g hg ha with hr | ⟨hb,heq,hr⟩ | ⟨hb,hg2,hbranch,hbase,hr⟩
        · exact interpolate ha rate.nonneg hgq hH (by simpa only [sub_zero] using hr) hdir (by
            simpa only [zero_mul,zero_add] using
              (uq T (Finset.filter_subset _ _) (Si I) g H hg (hgcap.trans_lt hp)
                hroot (hlen ▸ hgD.trans_lt hp) hmarks))
        · have hc:=(gp4 hb T (Finset.filter_subset _ _) (Si I) g Q.totalDegree H
              hg hδ hroot hlen (hgD.trans_lt hp) hmarks).1 heq
          exact interpolate ha rate.nonneg hgq hH (by simpa only [sub_zero] using hr) hdir (by
            simpa only [zero_mul,zero_add,heq,Nat.cast_one] using hc)
        · have hc:=(gp4 hb T (Finset.filter_subset _ _) (Si I) g Q.totalDegree H
              hg hδ hroot hlen (hgD.trans_lt hp) hmarks).2 hg2 hbranch
          have hδcap: (Q.totalDegree :ℚ)≤ cap:= by rw [← hdeg]; exact hdq.trans hcap
          have hle :=horizontalBase_mono hδcap g
          apply interpolate ha hbase hgq hH hr hdir
          exact hc.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hle hx) le_rfl) le_rfl)
      · calc
          _≤direct*x :=hdir
          _≤a*x :=mul_le_mul_of_nonneg_right (le_of_not_gt ha) hx
          _≤_:= by linarith only [mul_nonneg rate.height hH,hgq]
    have hgcapq: (g:ℚ)≤D:= by exact_mod_cast hgcap
    exact hpay.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hxD rate.nonneg) le_rfl) hgcapq)
  · have hmov :=c0U p f hf (he ▸ hconst)
      (T.image M.label) (cZQ F he)
    rw [dhW] at hmov
    have hcard: (T.card:ℚ)≤(f.totalDegree :ℚ)^2 := by exact_mod_cast hmov
    calc
      _≤(f.totalDegree :ℚ)^2 :=hcard
      _≤a*D:= by
        rw [pow_two]
        exact mul_le_mul ((hdq.trans hcap).trans rate.degree) hdq (Nat.cast_nonneg _) rate.nonneg
      _≤_:= by linarith only [mul_nonneg rate.height hH,hD]
theorem fTz {b maxHeight u del} {M:P1.FJ maxHeight u del} {Γ}
    (F:P1.bje midAgreement M Γ) (uq:aKd b M F)
    (gp4 :HorizontalBand b→HorizontalTariff b M F)
    {a h cap:ℚ} (rate :aSz b cap a h) (C:acW)
    (hcap: (C.cost 0:ℚ)≤ cap) (hp:C.cost 0<p) :
    ((aHl F C).card:ℚ)≤a*(C.cost 0:ℚ)+h*(C.cost 1 :ℚ)+C.cost 0:= by
  have hsum : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hsumH : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  have hcount (I:Ideal Ambient) (hI:I∈C.qv) :
      ((Γ.filter (I0 F I)).card:ℚ) ≤
        a*(aef I:ℚ)+h*(a9E I:ℚ)+aef I:= by
    have hn:aef I≤C.cost 0:=hsum ▸ Finset.single_le_sum (fun _ _=>Nat.zero_le _) hI
    have hq: (aef I:ℚ)≤(C.cost 0:ℚ) := by exact_mod_cast hn
    exact fTy F uq gp4 rate (C.geometric I hI) (hq.trans hcap) (hn.trans_lt hp)
  calc
    _ ≤ ∑ I∈C.qv,((Γ.filter (I0 F I)).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,(a*(aef I:ℚ)+h*(a9E I:ℚ)+aef I) :=
      Finset.sum_le_sum hcount
    _ = _:= by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Nat.cast_sum,hsum,hsumH]
end
end qQNoJ5c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace qQNoJ5c
noncomputable section
open Polynomial
open P5 (K p)
open P5_7 (midAgreement Qn)
open P5_7_3 (Jr Pairs O2 anM)
open P6_7_5 (Source)
open qAxtVye (nV afa arS aU2 a5S bQX am1 aqE
  agA axS a3D Fo V8 Process passes nextIndex)
open TD (J2 bfw)
open private cDJ ddZ from ProximityPrize.SubmissionLower.ZK15T2b
open cu (Shape vP Jet rD A5 jz)
open gT (Ambient tK iJ aci aNB gk aQ)
open pI (xN dual O9 aaS oU acW
  pN weight dot bH7 b6V crE b1w mass)
open ac2
open ac3
open private cpa from ProximityPrize.SubmissionLower.U
open private d1m from ProximityPrize.SubmissionLower.ZJEYUQc
open scoped BigOperators Classical
theorem aS3 {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) {t:Dt.Bank} (ht:Jr b t)
    (hpos :0<t.shape.m*midAgreement) {P:Jet} {W:ℕ}
    (hW:W≤O2 t.shape) (hP:P∈rows t.shape W) :
    ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0 :=
  src.necessary t ht W (by unfold O2 at hW; omega) P hP
theorem eo4 {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF) {t:Dt.Bank}
    (ht:Jr b t) {r :ℕ} (guard :am1 b.jX.hi r t.shape)
    {P:Jet} (hP:P∈rows t.shape (anM M.iF.toNat r t.shape))
    (i:Fin 2) (a :ℕ) (ha :a≤ r) :
    ∀ γ∈Γ,rD (A5 i a P) (M.label γ) (F.scalar γ)=0:= by
  apply aS3 src ht guard.pos _ (src.shift t ht _ _ hP i a)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ ha) _).trans (cDJ hw guard)
def ecO {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (pairs :P5_7_3.Pairs b M.iF.toNat rows)
    (i:afa b) :bQX pairs i :=
  let pair :=arS pairs i
  ⟨Classical.choice (bRI.proof _ _ pair.free_ne
      (src.shape _ (aU2 i) _ _ pair.free_mem)),
    Classical.choice (bRI.proof _ _ pair.moving_ne
      (src.shape _ (a5S i) _ _ pair.moving_mem))⟩
theorem b3t {cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {I:Ideal Ambient} {G:tK} {γ:K} (hm:I0 F I γ) (hG:aaS G I) :
    gT.FW G (F.scalar γ)=0:= by
  simpa only [pI.d2l] using RingHom.mem_ker.mp (hm hG)
theorem eGu {cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {I:Ideal Ambient} (hI:I.IsPrime) {γ:K} (hm:I0 F I γ) :
    P6_7.axy M F (ac6.Bridge.aQF I hI) γ:= by
  intro P hP
  apply RingHom.mem_ker.mpr
  change rD P (M.label γ) (F.scalar γ)=0
  rw [← aNB]
  exact RingHom.mem_ker.mp (hm hP)
theorem cDK {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF)
    {t:Dt.Bank} (ht:Jr b t) {r :ℕ}
    (guard :am1 b.jX.hi r t.shape) (hr :r<p)
    {I:Ideal Ambient} (hactive :xN I) (hd:dual I) (hv :agA rows t.shape I)
    {P:Jet} (hP:P∈rows t.shape (anM M.iF.toNat r t.shape)) :
    O9 I P (r+1) := by
  classical
  have hn:=src.nested t ht t ht rfl rfl rfl le_rfl
  have hcut:=cDJ hw guard
  have hc:=ddZ (algebraMap cu.aZ aQ) hn
    (src.shift t ht) hv hcut hP
  rw [← aVL] at hc
  exact dLt hd (cy0.proof I hactive.prime hactive.jet_finite
    hd hactive.jet_lt _ r hr hc)
theorem b2N {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) {t:Dt.Bank} (ht:Jr b t)
    (hpos :0<t.shape.m*midAgreement) {I:Ideal Ambient} (hf : ¬ agA rows t.shape I) :
    ∃ P:Jet,oU P t.shape∧iJ P∉I ∧
      ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0:= by
  classical
  unfold agA at hf
  push Not at hf
  obtain ⟨P,hP,hprop⟩:=hf
  exact ⟨P,src.shape t ht _ P hP,hprop,aS3 src ht hpos le_rfl hP⟩
theorem d59 {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (sched:aqE b)
    (pairs :P5_7_3.Pairs b M.iF.toNat rows) (i:afa b) {I:Ideal Ambient}
    (hf : ¬ axS (arS pairs i) I) :
    ∃ P:Jet,oU P (a3D (nV b i))∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
  classical
  let s :=nV b i
  let pair :=arS pairs i
  obtain ⟨ga,gc⟩:=sched.aE7 i i.isLt
  have liftCaps {P:Jet} (h:oU P s.free.shape∨oU P s.moving.shape) :
      oU P (a3D s) :=d1m ga.ode.jb gc.ode.jb h
  by_cases hP:agA rows s.free.shape I
  · by_cases hQ:agA rows s.moving.shape I
    · have htest : ¬ aFX.aTw pair.free pair.moving I :=
        fun h=>hf ⟨hP,hQ,h⟩
      unfold aFX.aTw at htest
      push Not at htest
      obtain ⟨f,_,_,_,hdiv,hmem,g,a,hclear,hproper⟩:=htest
      have hcaps :=src.shape _ (a5S i) _ _ pair.moving_mem
      have hG:=YZ.bWO pair.moving_ne hcaps gc.ode.jpos hdiv hclear
      refine ⟨YZ.alD g,liftCaps (Or.inr hG),hproper,?_⟩
      intro γ _ hγ
      apply YZ.bWP hclear
      have hz :=RingHom.mem_ker.mp (hγ hmem)
      simpa only [aNB,rD,eval₂_C,coe_eval₂RingHom,cu.yq] using hz
    · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N src (a5S i) gc.pos hQ
      exact ⟨P,liftCaps (Or.inr hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
  · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N src (aU2 i) ga.pos hP
    exact ⟨P,liftCaps (Or.inl hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
theorem bKS {cap u del} {M:P1.FJ cap u del} {Γ} (F:P1.bje midAgreement M Γ)
    (s :Shape) {I:Ideal Ambient} {P:Jet} (hs :s.J≤ s.B) (hI:xN I)
    (hcaps :oU P s) (hprop:iJ P∉I) :
    ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (pN I)) ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0 →
        γ∈C.direct ∨ ∃ Q∈C.qv,I0 F Q γ:= by
  let Ia (Q:Ideal Ambient) :=Γ.filter (I0 F Q)
  let direct :=(a2T I P).biUnion Ia
  have hcard:direct.card≤(a2T I P).card:= by
    have hsingle (Q:Ideal Ambient) (hQ:Q∈a2T I P) :
        (Ia Q).card≤1 := by
      obtain ⟨hcomp,hconst⟩:=Finset.mem_filter.mp hQ
      let _:Q.IsPrime :=(bZk hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply jz.injective
      apply (algebraMap cu.FX (gk Q)).injective
      exact (cpa hconst (Finset.mem_filter.mp hγ).2).trans
        (cpa hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈a2T I P,(Ia Q).card:=Finset.card_biUnion_le
      _ ≤ ∑ _∈a2T I P,1 :=Finset.sum_le_sum hsingle
      _ = _:= by simp
  let C:acW :=
    ⟨direct,aOS I P,by
      intro Q hQ
      obtain ⟨hcomp,hmov⟩:=Finset.mem_filter.mp hQ
      obtain ⟨hp,hdim⟩:=bZk hI hprop hcomp
      exact ⟨hp,hdim,cy6.proof Q hp hdim hmov⟩⟩
  refine ⟨C,?_,?_⟩
  · intro bw
    fin_cases bw
    · exact ac6.Bridge.dS4 s I P hs hI hcaps hprop
    · exact ac6.Bridge.dSZ s I P hs hI hcaps hprop
    · exact hcard.trans (ac6.Bridge.dSJ s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    let e :=aci (M.label γ) (F.scalar γ)
    change I≤RingHom.ker e at hmark
    have hz :iJ P∈RingHom.ker e :=
      RingHom.mem_ker.mpr ((aNB (M.label γ) (F.scalar γ) P).trans hzero)
    have hle :I ⊔ Ideal.span {iJ P} ≤ RingHom.ker e :=
      sup_le hmark ((Ideal.span_singleton_le_iff_mem _).mpr hz)
    have : (RingHom.ker e).IsPrime :=RingHom.ker_isPrime e
    obtain ⟨Q,hmin,hQmark⟩:=Ideal.exists_minimalPrimes_le hle
    have hQ:Q∈aT1 I P:=Ideal.mem_minimalPrimesFinset.mpr hmin
    by_cases ht:aYy Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q,Finset.mem_filter.mpr ⟨hQ,ht⟩,Finset.mem_filter.mpr ⟨hγ,hQmark⟩⟩)
    · exact Or.inr ⟨Q,Finset.mem_filter.mpr ⟨hQ,ht⟩,hQmark⟩
theorem dN1 {cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    (A:Finset (Ideal Ambient)) (s :Shape) (hs :s.J≤ s.B)
    (ha : ∀ I∈A,xN I)
    (hcut : ∀ I∈A,∃ P:Jet,oU P s∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0) :
    ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (mass A)) ∧
      ∀ γ∈Γ,(∃ I∈A,I0 F I γ)→γ∈C.direct ∨ ∃ I∈C.qv,I0 F I γ:= by
  have hex (I:Ideal Ambient) (hI:I∈A) :
      ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (pN I)) ∧
        ∀ γ∈Γ,I0 F I γ→γ∈C.direct ∨ ∃ Q∈C.qv,I0 F Q γ:= by
    obtain ⟨P,hp,hprop,hzero⟩:=hcut I hI
    obtain ⟨C,hc,hmarks⟩:=bKS F s hs (ha I hI) hp hprop
    exact ⟨C,hc,fun γ hγ hm=>hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I:Ideal Ambient) :acW :=
    if hI:I∈A then Classical.choose (hex I hI) else b1w
  have hC (I:Ideal Ambient) (hI:I∈A) :
      (∀ bw,(C I).cost bw≤dot (weight s bw) (pN I)) ∧
      ∀ γ∈Γ,I0 F I γ→γ∈(C I).direct ∨ ∃ Q∈(C I).qv,I0 F Q γ:= by
    simpa only [C,dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨bH7 A C,?_,?_⟩
  · intro bw
    calc
      _ ≤ ∑ I∈A,(C I).cost bw:=b6V A C bw
      _ ≤ ∑ I∈A,dot (weight s bw) (pN I) :=
        Finset.sum_le_sum (fun I hI=>(hC I hI).1 bw)
      _ = _:=crE _ _
  · rintro γ hγ ⟨I,hI,hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q,hQ,hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I,hI,hd⟩)
    · exact Or.inr ⟨Q,Finset.mem_biUnion.mpr ⟨I,hI,hQ⟩,hmark⟩
theorem cD4 {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP}
    {pairs :Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF)
    {i:ℕ} (hi:i≤Fo b) (k :Fin 4) :J2 (R.Bp i) k≤V8 b i k := by
  induction i with
  | zero =>
    exact (Nat.cast_le (α:=ℚ)).mpr
      ((pI.a5I (R.a4R 0) k).trans (R.init_mass k))
  | succ i ih =>
    have ht:i<Fo b:=hi
    refine le_min ((bfw (R.eEO i) k).trans (ih ht.le)) ?_
    let j:=nextIndex i ht
    let s :=nV b j
    let pair :=arS pairs j
    obtain ⟨ga,gb⟩:=R.sched.aE7 j j.isLt
    have hr :=R.sched.bN7 j j.isLt
    exact aZC.proof s.free.shape s.moving.shape s.dI true pair.free pair.moving
      (R.sched.bIj i ht) hr ga.ode.small gb.ode.small ga.seed_small gb.seed_small
      ga.ode.jb gb.ode.jb pair.free_ne pair.moving_ne
      (src.shape _ (aU2 j) _ _ pair.free_mem)
      (src.shape _ (a5S j) _ _ pair.moving_mem) pair.no_moving
      (R.fixed j).free (R.fixed j).moving (R.Bp (i+1))
      (fun _ I hI=>(R.kept_clean (i+1) hI).2) (fun I hI=> by
        obtain ⟨hc,hd⟩:=R.kept_clean (i+1) hI
        have hactive :=(R.DN I (R.a4R (i+1) hI)).1
        have hp:axS pair I:= by
          have he :=(Finset.mem_filter.mp hI).2
          simpa only [passes,dite_eq_left ht] using he
        exact ⟨hactive,hp.2.2,(hc j).1,(hc j).2,
          cDK src hw (aU2 j) ga hr hactive hd hp.1 pair.free_mem,
          cDK src hw (a5S j) gb hr hactive hd hp.2.1 pair.moving_mem⟩) k
end
end qQNoJ5c
end
