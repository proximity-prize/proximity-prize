import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZIBb1mb
import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
set_option autoImplicit true
namespace qCj6p1d
noncomputable section
open Polynomial
open P6_6 (mV gZ bf pair32)
open P6_6_7 qAzl5me
open aR (ao af Shape aO shape cK extend)
open dN (GeoJets An bC separant)
open BO (Ue)
open vS (bzb cZX)
open lB (bF a3t)
open P6_6_7_3 (bW2 charter cDD local_weight)
open private d29 from ProximityPrize.SubmissionLower.ZY18Mqc
def c1 :Prop :=
  ∀ (g:af 4) (p:Shape),bF p→aO (shape g) p→0<(shape g).t →
    p.t≠1→Nonempty (dmL g p)
def c2 :Prop :=
  ∀ (g:af 4) (p:Shape),bF p→aO (shape g) p→0<(shape g).t →
    p.t=1→Nonempty (dmL g p)
def c3:Prop :=
  ∀ (g:af 4) (p:Shape),bF p→aO (shape g) p→0<(shape g).t →
    1<p.t→Nonempty (dmM g p)
def c4 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (F:Finset (Branch R G ell)) (T:Branch R G ell→Finset P6.K),
      let p:=chartBody C R cs
      SameChart F →
      (∀ b∈F,Nonempty (Member4 b.g p)∧aSG p b C.s (T b) ∧
        T b⊆C.Δ ∧ ∀ γ∈T b,b.dY (extend (C.s γ))) →
      (32 :ℤ)*(demandCost F T:ℤ)≤pair32 false p (firstSlot C R cs) (cutterBody C ell)
def c5:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (F:Finset (Branch R G ell)) (T:Branch R G ell→Finset P6.K),
      let p:=chartBody C R cs
      1<p.t→SameChart F →
      (∀ b∈F,Nonempty (Member5 b.g p)∧bMD p b C.s (T b) ∧
        T b⊆C.Δ ∧ ∀ γ∈T b,b.dY (extend (C.s γ))) →
      (32 :ℤ)*(demandCost F T:ℤ)≤pair32 true p (firstSlot C R cs) (cutterBody C ell)
def c6:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (F:Finset (Branch R G ell)),
      let p:=chartBody C R cs
      SameChart F→(∀ b∈F,Nonempty (Member4 b.g p)) →
      (additiveCost F:ℤ)≤ memberDegree p (firstSlot C R cs) (cutterBody C ell)
private theorem branch_exists {C:Context} {R G ell cs} (h:PairInput C R G ell cs)
    (A:SurfaceAssignment C R G) {γ:P6.K} (hγ:γ∈terminalMarks C R G ell cs A) :
    ∃ b:Branch R G ell,b.aI=A.aI γ∧b.dY (extend (C.s γ)) ∧
      ∃ i a,Selected C cs b.aI γ i a∧b.g=chartRow C i a := by
  classical
  obtain ⟨ha,i,a,hsel,P,hP,hmark,ht⟩:=Finset.mem_filter.mp hγ
  obtain ⟨hm,ho,hh,_⟩:=Finset.mem_filter.mp ha
  obtain ⟨hz,hsurf⟩:=A.valid γ hm ho
  obtain ⟨v,_,hv,hw⟩:=local_weight h.factor.1 h.proper hz hh
  let g:=chartRow C i a
  have hreg:An (extend (C.s γ)) (sigma g)≠0 :=
    fun hs=>hsel.regular (Ue.mp hs)
  let b:Branch R G ell :=
    ⟨A.aI γ,hz,by rw [hv]; exact_mod_cast hw,g,P,hP,fun hp=>hreg (hmark hp),
      fun hs=>ht.resolve_left (fun hn=>hn hs)⟩
  exact ⟨b,rfl,⟨hmark,Ue.mp (hsurf (hsel.canonical.2.1 a le_rfl)),hreg⟩,
    i,a,hsel,rfl⟩
theorem Branch.b1G {R G ell} {b c:Branch R G ell}
    (hs :b.aI=c.aI) (hg:b.g=c.g) (hc:b.curve=c.curve) :b=c:= by
  cases b
  cases c
  cases hs
  cases hg
  cases hc
  rfl
private theorem A9 {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    bF (chartBody C R cs) := by
  cases cs with
  | own _=>exact lB.Tn R
  | union _ =>
    refine ⟨le_max_right _ _,?_⟩
    let x :=P6_6.rawResidual P6_6.m6 C.v
    let j:=min x.j (3*x.b)
    change 3*min x.t (min x.b (j/3))≤j
    have h:=(min_le_right x.t _).trans (min_le_right x.b (j/3))
    omega
private theorem chart_pos {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    0<(chartBody C R cs).t:= by
  have he : (chartIndices C cs).Nonempty := by
    cases cs with
    | own i=>exact ⟨i,Finset.mem_singleton_self i⟩
    | union l =>
      obtain ⟨γ,hγ⟩:=C.nonempty
      obtain ⟨i,hi,_⟩:=C.marks.Eh γ hγ
      exact ⟨i,hi⟩
  obtain ⟨i,hi⟩:=he
  exact (C.marks.factors i (charter h hi)).2.1.trans_le ((bW2 h).2 i hi).2.2
private theorem selected_box {C:Context} {R G ell cs} (h:PairInput C R G ell cs)
    {z γ i a} (hs :Selected C cs z γ i a) :
    aO (shape (chartRow C i a)) (chartBody C R cs)∧0<(shape (chartRow C i a)).t:= by
  refine ⟨cDD (a3t _ _) ((bW2 h).2 i hs.index_mem),?_⟩
  by_contra! ht
  have hz :=MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero (Nat.le_zero.mp ht)
  exact hs.regular (by rw [separant,hz]; exact map_zero _)
private theorem next_zero {g:af 4} {U:ao[X]} (hg:cK g U=0)
    (hU:U.natDegree≤gZ) :
    An U (bC (ZV g))=0:= by
  have hd:U.natDegree<bf+1 :=
    (Nat.lt_succ_of_le hU).trans (Nat.lt_succ_self _)
  exact Ue.mpr (d29 g U hg _ hd)
private theorem regular_eval_apply {g:af 4} {U:ao[X]} (h:An U (sigma g)≠0)
    (D:GeoJets) :aJf g U h (qR g D)=An U D :=
  IsLocalization.Away.lift_eq _ _ _
private theorem lifted_proper_of_value {R G ell} (b:Branch R G ell) {U:ao[X]}
    (h:b.dY U) {D:vS.g9} (hd:afU b.g U h.2.2 D ≠0) :
    yu b.g D∉b.a5x := by
  have hm:b.a5x≤RingHom.ker (aJf b.g U h.2.2) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change aJf b.g U h.2.2 (qR b.g P)=0
    rw [regular_eval_apply]
    exact h.1 hP
  exact fun hp=>hd (hm hp)
private theorem map_mem_localCurve {R G ell} (b:Branch R G ell) {D:GeoJets}
    (hD:qR b.g D∈b.a5x) :D∈b.curve := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (sigma b.g))
    (ChartRing b.g)] at hD
  obtain ⟨m,⟨n,rfl⟩,hm⟩:=hD
  exact (b.member.minimal.isPrime.mem_or_mem hm).resolve_left
    (fun hp=>b.regular (b.member.minimal.isPrime.mem_of_pow_mem n hp))
private theorem slice4 {R G ell p} (b:Branch R G ell) (a :dmL b.g p)
    {C:Context} {L T:Finset P6.K} (hL:L⊆C.Δ) (hT:T⊆L)
    (hon : ∀ γ∈L,b.dY (extend (C.s γ)))
    (hd: (b.Simple∧T=L)∨bzb L C.s T) :aSG p b C.s T:= by
  classical
  rcases hd with ⟨hs,_⟩ | (hcard | ⟨x,v,⟨δ,hδ,hδv⟩,hslice⟩)
  · obtain ⟨n,heq⟩:=a.next_represents
    refine Or.inr ⟨a.next,a.next_fits,fun hn=>b.terminal hs
      (heq.symm ▸ b.curve.mul_mem_left _ hn),?_⟩
    intro γ hγ
    have h:=hon γ (hT hγ)
    have hm:=next_zero h.2.1 (Polynomial.natDegree_map_le.trans (C.messages.degree γ (hL (hT hγ))))
    rw [heq,map_mul,map_pow,mul_eq_zero] at hm
    exact hm.resolve_left (pow_ne_zero _ h.2.2)
  · exact Or.inl hcard.le
  · obtain ⟨D,hD,hev⟩:=a.values x v
    refine Or.inr ⟨D,hD,fun hd=>hδv ((hev _ (C.messages.degree δ (hL hδ))
      (hon δ hδ).2).mp ((hon δ hδ).1 hd)),?_⟩
    intro γ hγ
    have hm:γ∈L.filter (fun η=>(C.s η).eval x=v) :=hslice ▸ hγ
    exact (hev _ (C.messages.degree γ (hL (hT hγ))) (hon γ (hT hγ)).2).mpr
      (Finset.mem_filter.mp hm).2
private theorem slice5 {R G ell p} (b:Branch R G ell) (a :dmM b.g p)
    {C:Context} {L T:Finset P6.K} (hL:L⊆C.Δ) (hT:T⊆L)
    (hon : ∀ γ∈L,b.dY (extend (C.s γ)))
    (hd: (b.Simple∧T=L)∨bzb L C.s T) :bMD p b C.s T:= by
  classical
  rcases hd with ⟨hs,_⟩ | (hcard | ⟨x,v,⟨δ,hδ,hδv⟩,hslice⟩)
  · refine Or.inr ⟨a.next,a.next_fits,?_,?_⟩
    · intro hn
      exact b.terminal hs (map_mem_localCurve b (b.a5x.mem_of_dvd a.next_represents.dvd hn))
    · intro γ hγ h
      have he :=a.next_represents.map (aJf b.g _ h.2.2)
      change Associated (afU b.g (extend (C.s γ)) h.2.2 a.next) _ at he
      rw [regular_eval_apply,next_zero h.2.1
        (Polynomial.natDegree_map_le.trans (C.messages.degree γ (hL (hT hγ))))] at he
      exact (associated_zero_iff_eq_zero _).mp he
  · exact Or.inl hcard.le
  · obtain ⟨D,hD,hev⟩:=a.values x v
    have h:=hon δ hδ
    refine Or.inr ⟨D,hD,lifted_proper_of_value b h
      (fun hz=>hδv ((hev _ (C.messages.degree δ (hL hδ)) h.2.1 h.2.2).mp hz)),?_⟩
    intro γ hγ hg
    have hm:γ∈L.filter (fun η=>(C.s η).eval x=v) :=hslice ▸ hγ
    exact (hev _ (C.messages.degree γ (hL (hT hγ))) hg.2.1 hg.2.2).mpr
      (Finset.mem_filter.mp hm).2
private theorem label_bound {C:Context} {R G ell} (b:Branch R G ell)
    {L T:Finset P6.K} (hL:L⊆C.Δ)
    (h: (b.Simple→T=L) ∧
      (¬ b.Simple→dN.agC L C.s T.card)) :
    mV*L.card≤ mV*(b.demandWeight*T.card)+mV*b.extra := by
  classical
  by_cases hs :b.Simple
  · simp [Branch.demandWeight,Branch.extra,hs,h.1 hs]
  · have hi:=P6_6_5.bv5 (C.messages.mono hL) T.card
      (fun i hi=>h.2 hs (P6.node i) (C.w i) hi)
    simp only [Branch.demandWeight,Branch.extra,ite_eq_right hs,Nat.mul_one]
    have hc: (82317:ℕ)≤ mV*2 := by decide
    change mV*L.card≤_
    calc
      _≤82317*T.card+mV:=hi
      _≤(mV*2)*T.card+mV :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _
      _ = _:= by rw [Nat.mul_assoc]
private theorem charge {R G ell} (F:Finset (Branch R G ell))
    (L T:Branch R G ell→Finset P6.K)
    (h : ∀ b∈F,mV*(L b).card≤ mV*(b.demandWeight*(T b).card) +
      mV*b.extra) :
    (mV:ℤ)*(↑(∑ b∈F,b.weight*(L b).card) :ℤ) ≤
      (mV:ℤ)*(demandCost F T:ℤ)+mV*(additiveCost F:ℤ) := by
  classical
  have hn:mV*(∑ b∈F,b.weight*(L b).card) ≤
      mV*demandCost F T+mV*additiveCost F:= by
    rw [demandCost,additiveCost,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro b hb
    calc
      _=b.weight*(mV*(L b).card) := by ac_rfl
      _≤b.weight*(mV*(b.demandWeight*(T b).card)+mV*b.extra) :=
        Nat.mul_le_mul_left _ (h b hb)
      _ = _:= by simp only [Nat.mul_add]; ac_rfl
  exact_mod_cast hn
private theorem pair_thin {p r q:Shape} (ht:p.t=1) :
    pair32 true p r q=pair32 false p r q:= by
  unfold pair32
  rw [ht]
  rfl
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
    qAzl5me.c1 := by
  classical
  intro C R G ell cs h A dR
  let Ia :=terminalMarks C R G ell cs A
  let B:=Branch R G ell
  let a (γ:Ia) :B:=(branch_exists h A γ.property).choose
  have spec (γ:Ia) : (a γ).aI=A.aI γ∧(a γ).dY (extend (C.s γ)) ∧
      ∃ i n,Selected C cs (a γ).aI γ i n∧(a γ).g=chartRow C i n :=
    (branch_exists h A γ.property).choose_spec
  let F:=Ia.attach.image a
  let CF (b:B) :=Ia.filter (fun γ => ∃ h:γ∈Ia,a ⟨γ,h⟩=b)
  let p:=chartBody C R cs
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  have label_sub (b:B) :CF b⊆C.Δ:= by
    intro γ hγ
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1).1
  have on_curve (b:B) (γ) (hγ:γ∈CF b) :b.dY (extend (C.s γ)) := by
    obtain ⟨hm,he⟩:=(Finset.mem_filter.mp hγ).2
    exact he ▸ (spec ⟨γ,hm⟩).2.1
  have available (b:B) : ∃ T⊆CF b,(b.Simple→T=CF b) ∧
      (b∈F → ¬ b.Simple→dN.agC (CF b) C.s T.card∧bzb (CF b) C.s T) := by
    by_cases hs :b.Simple
    · exact ⟨CF b,Finset.Subset.rfl,fun _=>rfl,fun _ hn=>(hn hs).elim⟩
    by_cases hb:b∈F
    · obtain ⟨γ,_,hγ⟩:=Finset.mem_image.mp hb
      have hne : (CF b).Nonempty :=⟨γ.val,Finset.mem_filter.mpr ⟨γ.property,γ.property,hγ⟩⟩
      obtain ⟨T,hT,_,hsct,hd⟩:=cZX (CF b) C.s hne
      exact ⟨T,hT,fun h=>(hs h).elim,fun _ _=>⟨hsct,hd⟩⟩
    · exact ⟨∅,Finset.empty_subset _,fun h=>(hs h).elim,fun hb' _=>(hb hb').elim⟩
  choose T hT hsimple hmultiple using available
  have demanded (b:B) (hb:b∈F) : (b.Simple∧T b=CF b)∨bzb (CF b) C.s (T b) := by
    by_cases hs :b.Simple
    · exact Or.inl ⟨hs,hsimple b hs⟩
    · exact Or.inr (hmultiple b hb hs).2
  have Ig (b:B) (hb:b∈F) :
      ∃ γ i n,Selected C cs b.aI γ i n∧b.g=chartRow C i n:= by
    obtain ⟨γ,_,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨i,n,hi,he⟩:=(spec γ).2.2
    exact ⟨γ,i,n,hi,he⟩
  have hf :SameChart F:= by
    intro b hb c hc he
    obtain ⟨γ,i,n,hi,hbi⟩:=Ig b hb
    obtain ⟨δ,j,m,hj,hcj⟩:=Ig c hc
    have ⟨hij,hnm⟩:=hi.unique (he.symm ▸ hj)
    rw [hbi,hcj,hij,hnm]
  have box (b:B) (hb:b∈F) :aO (shape b.g) p∧0<(shape b.g).t:= by
    obtain ⟨_,_,_,hi,he⟩:=Ig b hb
    exact he.symm ▸ selected_box h hi
  have bY (b:B) (hb:b∈F) :Nonempty (dmL b.g p) := by
    by_cases ht:p.t=1
    · exact h2 _ _ (A9 h) (box b hb).1 (box b hb).2 ht
    · exact h1 _ _ (A9 h) (box b hb).1 (box b hb).2 ht
  have ha :=h6 C R G ell cs h F hf (fun b hb=>(bY b hb).map dmL.toMember4)
  have iy :32*(demandCost F T:ℤ)≤pair32 false p r q :=
    h4 C R G ell cs h F T hf (fun b hb=> by
      obtain ⟨ch⟩:=bY b hb
      exact ⟨⟨ch.toMember4⟩,slice4 b ch (label_sub b) (hT b) (on_curve b) (demanded b hb),
        (hT b).trans (label_sub b),fun γ hγ=>on_curve b γ (hT b hγ)⟩)
  have kK:32*(demandCost F T:ℤ)≤pair32 dR p r q:= by
    cases dR with
    | false=>exact iy
    | true =>
      by_cases ht:p.t=1
      · rw [pair_thin ht]
        exact iy
      · have htop:1<p.t:=lt_of_le_of_ne (chart_pos h) (fun he=>ht he.symm)
        exact h5 C R G ell cs h F T htop hf (fun b hb=> by
          obtain ⟨ch⟩:=h3 _ _ (A9 h) (box b hb).1 (box b hb).2 htop
          exact ⟨⟨ch.toMember5⟩,slice5 b ch (label_sub b) (hT b) (on_curve b) (demanded b hb),
            (hT b).trans (label_sub b),fun γ hγ=>on_curve b γ (hT b hγ)⟩)
  have hs : (∑ γ∈Ia,ell*genericOrder R (A.aI γ)) =
      ∑ b∈F,b.weight*(CF b).card:= by
    let w (γ:P6.K) :=ell*genericOrder R (A.aI γ)
    calc
      _ = ∑ γ∈Ia.attach,w γ:=(Finset.sum_attach Ia w).symm
      _ = ∑ b∈F,∑ γ∈Ia.attach.filter (fun γ=>a γ=b),w γ :=
        (Finset.sum_fiberwise_of_maps_to (fun γ _=>Finset.mem_image_of_mem a (Finset.mem_attach _ γ))
          (fun γ=>w γ)).symm
      _ = _:= by
        apply Finset.sum_congr rfl
        intro b _
        have hc: (Ia.attach.filter (fun γ=>a γ=b)).card=(CF b).card:= by
          rw [Finset.filter_attach']
          simp only [Finset.card_map,Finset.card_attach,CF]
        rw [← hc]
        calc
          _ = ∑ γ∈Ia.attach.filter (fun γ=>a γ=b),b.weight:= by
            apply Finset.sum_congr rfl
            intro γ hγ
            have h:=(Finset.mem_filter.mp hγ).2
            change ell*genericOrder R (A.aI γ)= _
            rw [← (spec γ).1,h]
          _ = _:= by simp [Nat.mul_comm]
  have hp:=charge F CF T fun b hb=>label_bound b (label_sub b)
    ⟨hsimple b,fun hn=>(hmultiple b hb hn).1⟩
  change aid C R G ell A Ia≤terminalCap dR p r q
  have hsc:aid C R G ell A Ia =
      (32 :ℤ)*mV*(↑(∑ b∈F,b.weight*(CF b).card) :ℤ) := by
    rw [← hs,aid,Nat.cast_sum]
    simp only [Nat.cast_mul,feeScale,Nat.cast_ofNat]
    rw [← Finset.mul_sum]
    ring
  rw [hsc,terminalCap]
  have hleft:=mul_le_mul_of_nonneg_left hp (show 0≤(32 :ℤ) by decide)
  have hmix :=mul_le_mul_of_nonneg_left kK (Int.natCast_nonneg mV)
  have hadd:=mul_le_mul_of_nonneg_left ha (show 0≤(32 :ℤ)*mV by positivity)
  linarith only [hleft,hmix,hadd]
end
end qCj6p1d
