import ProximityPrize.SubmissionLower.ZbnhR9d
import ProximityPrize.SubmissionLower.ZPoi06c
set_option Elab.async false
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q3rjQGe
noncomputable section
open Finset Polynomial
open P6 (K dw)
open P6_7_1
open cu (Jet rD)
open gT (Ambient iJ aNB)
open pI (xN acW dual mass pN)

open ac6.Bridge (aQF)
open TD (GM J2 FP)
open private bKS from ProximityPrize.SubmissionLower.ZPoi06c
open scoped Classical BigOperators
@[simp] theorem free_shape (i:Free) :aHp i.castSucc=(stage i).free := by
  simp [aHp]
@[simp] theorem terminal_shape :aHp termTrial=terminal.box := by
  simp [aHp]
@[simp] theorem free_bank {x :Input} (P:Poles x) (i:Free) :
    aV P i.castSucc=P.rows (stage i).free (cutoff (stage i).free) := by
  simp [aV]
@[simp] theorem terminal_bank {x :Input} (P:Poles x) :
    aV P termTrial=rectBank P terminal (rectCut terminal) := by
  simp [aV]
theorem dot_mass (v :GM) (S:Finset (Ideal Ambient)) :
    FP v (J2 S) = ∑ q∈S,FP v (fun k=>pN q k) := by
  simp only [FP,J2,mass,Nat.cast_sum,mul_sum]
  exact sum_comm
theorem dSz (j:Fin 3) (t:Trial) (k :Fin 4) :
    0≤SS j t k :=Nat.cast_nonneg _
theorem axisWeight_nonneg (k :Fin 4) :0≤axisWeight k :=Nat.cast_nonneg _
theorem card_union_q (A B:Finset K) : ((A∪B).card:ℚ)≤A.card+B.card:= by
  exact_mod_cast card_union_le A B
theorem card_biUnion_q {α:Type*} (A:Finset α) (B:α→Finset K) :
    ((A.biUnion B).card:ℚ) ≤ ∑ a∈A,((B a).card:ℚ) := by
  exact_mod_cast (card_biUnion_le : (A.biUnion B).card≤_)
theorem free_cut {x :Input} (P:Poles x) (i:Free) {q:Ideal Ambient}
    (ha :xN q) (hf : ¬ passes P i.castSucc q) :
    ∃ C:acW,(∀ j,(C.cost j:ℚ)≤FP (SS j i.castSucc)
      (fun k=>pN q k)) ∧
      marks x q⊆C.direct∪onCurves x C:= by
  have hj: (stage i).free.J≤(stage i).free.B:= by fin_cases i <;> decide
  have hm:0<(stage i).free.m*dw:= by fin_cases i <;> decide
  have hw:cutoff (stage i).free<(stage i).free.m*dw:= by unfold cutoff; omega
  unfold passes at hf
  rw [free_bank] at hf
  push Not at hf
  obtain ⟨g,hg,hp⟩:=hf
  let F:=P6_7.weakenFamily x.F (show P5_7.farAgreement≤dw by decide)
  obtain ⟨C,hC,hcover⟩:=bKS F (stage i).free hj ha
    (DP.d3r P.crt x.word hg) hp
  refine ⟨C,fun j => ?_,?_⟩
  · simpa only [FP,pI.dot,SS,free_shape,Nat.cast_sum,Nat.cast_mul] using
      (Nat.cast_le (α:=ℚ)).mpr (hC j)
  · intro γ hγ
    obtain ⟨hγ,hq⟩:=mem_filter.mp hγ
    rcases hcover γ hγ hq (necessary P hw hg hγ) with h | ⟨I,hI,hon⟩
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,I,hI,hon⟩)
theorem terminal_row {x :Input} (P:Poles x) {q:Ideal Ambient}
    (hf : ¬ passes P termTrial q) :
    ∃ g∈rectBank P terminal (rectCut terminal),iJ g∉q:= by
  unfold passes at hf
  rw [terminal_bank] at hf
  push Not at hf
  exact hf
theorem eGu {x :Input} {q:Ideal Ambient} (hp:q.IsPrime) {γ:K}
    (hm:onMark x q γ) :P6_7.axy x.M x.F (aQF q hp) γ:= by
  intro g hg
  apply RingHom.mem_ker.mpr
  change rD g (x.M.label γ) (x.F.scalar γ)=0
  rw [← aNB]
  exact RingHom.mem_ker.mp (hm hg)
variable {x P R} (O:OriginCover x P R) {f :Jet}
theorem stopped_zero :
    stopped O f 0=(QV O f 0).filter (fun q => ¬ dual q) :=rfl
theorem stopped_succ (t:Trial) :
    stopped O f t.succ=(QV O f t.succ).filter (fun q => ¬ passes P t q) :=rfl
theorem stopped_sub (s :bAL) :stopped O f s⊆QV O f s := by
  induction s using Fin.cases with
  | zero=>rw [stopped_zero]; exact filter_subset _ _
  | succ t=>rw [stopped_succ]; exact filter_subset _ _
private theorem earlier_disjoint {s s' : bAL} (h:s<s') :
    Disjoint (stopped O f s) (stopped O f s') := by
  have hh:s.val<s'.val :=h
  apply disjoint_left.mpr
  intro q hi hj
  obtain ⟨_,hd,ht⟩:=mem_filter.mp (stopped_sub O s' hj)
  induction s using Fin.cases with
  | zero =>
    rw [stopped_zero] at hi
    exact (mem_filter.mp hi).2 (hd (by omega))
  | succ t =>
    rw [stopped_succ] at hi
    exact (mem_filter.mp hi).2 (ht t (by simpa only [Fin.val_succ] using hh))
private theorem all_mass (k :Fin 4) :
    (∑ s :bAL,J2 (stopped O f s) k)≤J2 (O.parents f) k := by
  let A:Finset bAL:=univ
  have hd: (A:Set bAL).PairwiseDisjoint (stopped O f) := by
    intro i _ j _ hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact earlier_disjoint O h
    · exact (earlier_disjoint O h).symm
  have hu:A.biUnion (stopped O f)⊆O.parents f := by
    intro q hq
    obtain ⟨s,_,hs⟩:=mem_biUnion.mp hq
    exact (mem_filter.mp (stopped_sub O s hs)).1
  have hb:=TD.bfw hu k
  simp only [J2,mass,Nat.cast_sum,sum_biUnion hd] at hb
  simpa only [A,J2,mass,Nat.cast_sum] using hb
theorem placed {q:Ideal Ambient} (hq:q∈O.parents f) :
    (∃ s,q∈stopped O f s)∨q∈final O f := by
  by_cases hd:dual q
  · by_cases h : ∃ t:Trial,¬ passes P t q
    · have hn : ∃ n,∃ t:Trial,t.val=n ∧ ¬ passes P t q:= by
        obtain ⟨j,hj⟩:=h
        exact ⟨j.val,j,rfl,hj⟩
      obtain ⟨t,ht,hfail⟩:=Nat.find_spec hn
      left
      refine ⟨t.succ,?_⟩
      rw [stopped_succ]
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hq,fun _=>hd,?_⟩,hfail⟩
      intro j hj
      by_contra hbad
      exact Nat.find_min hn
        (by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right,ht] using hj) ⟨j,rfl,hbad⟩
    · exact Or.inr (mem_filter.mpr ⟨hq,hd,fun t=>by_contra fun ht=>h ⟨t,ht⟩⟩)
  · left
    refine ⟨0,?_⟩
    rw [stopped_zero]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hq,fun h=>(Nat.not_lt_zero _ h).elim,
      fun _ h=>(Nat.not_lt_zero _ h).elim⟩,hd⟩
def Az (G:Geometry O) :aAU where
  factors :=O.factors
  origin :=O.origin
  line :=O.line
  stops f s :=J2 (stopped O f s)
  nonneg _ _ _ _:=Nat.cast_nonneg _
  spend_order :=G.spend_order
  line_ok f hf hl:= by
    obtain ⟨ho,hj,hu,_⟩:=O.line_pos f hf hl
    exact ⟨ho,hj,hu⟩
  nested o j:=O.nested o.val (Nat.le_of_lt_succ o.isLt) j
  initial f hf k :=(all_mass O k).trans (G.initial f hf k)
  global k :=(sum_le_sum fun _ _=>all_mass O k).trans (G.global k)
  all_free o k :=(sum_le_sum fun _ _=>TD.bfw (stopped_sub O termStop) k).trans
    (G.all_free o k)
end
end q3rjQGe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q3rjQGe
noncomputable section
open Finset

open P6_7_1
open cu (Jet)
open gT (Ambient iJ)
open pI (xN acW dual pN)

open ac6.Bridge (aQF cbq)
open TD (FP J2 a3x)
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (x :Input) (P:Poles x) (R:EarlyPicks x P) (O:OriginCover x P R),Geometry O
def c2 :Prop :=
  ∀ (x :Input) (P:Poles x),(bankBook P).card≤bankFee
def c3:Prop :=
  ∀ (x :Input) (o:Origin) (q:Ideal Ambient),xN q→q.height=2 → ¬ dual q →
    (∀ k,(pN q k :ℚ)≤ memberCap o 0 k) →
    ((marks x q).card:ℚ)≤FP (rankPrice o) (fun k=>pN q k)
def c4 :Prop :=
  ∀ (x :Input) (_P:Poles x) (C:acW) (d a b:ℚ),
    FreeRateOK d a b→(C.cost 0:ℚ)≤d →
    ((onCurves x C).card:ℚ)≤(a+1)*C.cost 0+b*C.cost 1
def c5:Prop :=
  ∀ (x :Input) (P:Poles x) (q:Ideal Ambient),
    xN q→q.height=2→dual q →
    ∀ g∈rectBank P terminal (rectCut terminal),iJ g∉q →
    ∃ C:RectCover,
      (∀ a,(C.kd a :ℚ)≤FP axisWeight (fun k=>pN q k)) ∧
      (∀ j,(C.toacW.cost j:ℚ)≤FP (SS j termTrial)
        (fun k=>pN q k)) ∧
      marks x q⊆C.direct∪onCurves x C.toacW
def c6:Prop :=
  ∀ (x :Input) (_P:Poles x) (C:RectCover) (d D z a b:ℚ),
    RectRateOK d D z a b→(∀ i,(C.kd i:ℚ)≤d) →
    (C.toacW.cost 0:ℚ)≤D →
    ((onCurves x C.toacW).card:ℚ) ≤
      z*C.kd 0+(a+1)*C.kd 1+b*C.toacW.cost 1+C.toacW.cost 0
def c7:Prop :=Nonempty cL
private theorem free_card (h:c4) {x :Input} (P:Poles x) (o:Origin)
    (i:Free) {q:Ideal Ambient} (ha :xN q) (hf : ¬ passes P i.castSucc q)
    {a b:ℚ} (hr :FreeRateOK (freeDegree o i) a b)
    (hm : ∀ k,(pN q k :ℚ)≤ memberCap o i.castSucc.succ k) :
    ((marks x q).card:ℚ)≤FP (freePrice a b i) (fun k=>pN q k) := by
  obtain ⟨C,hC,hcover⟩:=free_cut P i ha hf
  have hd:=(hC 0).trans (a3x (dSz 0 i.castSucc) hm)
  have hcount:=h x P C _ a b hr hd
  obtain ⟨hn,_,ha,hb,_⟩:=hr
  have ha' : 0≤a+1 := by linarith only [hn.trans ((le_max_left _ _).trans ha)]
  let w (j:Fin 3) :=FP (SS j i.castSucc) (fun k=>pN q k)
  calc
    _≤(C.direct.card:ℚ)+(onCurves x C).card :=
      ((Nat.cast_le (α:=ℚ)).mpr (card_le_card hcover)).trans (card_union_q _ _)
    _≤(a+1)*w 0+b*w 1+w 2 := by
      have h2 : (C.direct.card:ℚ)≤w 2 :=hC 2
      linarith only [hcount,h2,mul_le_mul_of_nonneg_left (hC 0) ha',
        mul_le_mul_of_nonneg_left (hC 1) hb]
    _ = _:= by
      simp only [w,freePrice,FP,add_mul,one_mul,sum_add_distrib,mul_sum,mul_assoc]
private theorem rect_card (h5:c5) (h6:c6) {x :Input} (P:Poles x) (o:Origin)
    {q:Ideal Ambient} (ha :xN q) (hh:q.height=2) (hd:dual q)
    (hf : ¬ passes P termTrial q) {z a b:ℚ}
    (hr :RectRateOK (axisCap o) (planeCap o) z a b)
    (hm : ∀ k,(pN q k :ℚ)≤ memberCap o termStop k) :
    ((marks x q).card:ℚ)≤FP (rectPrice z a b) (fun k=>pN q k) := by
  obtain ⟨g,hg,hp⟩:=terminal_row P hf
  obtain ⟨C,haxis,hplane,hcover⟩:=h5 x P q ha hh hd g hg hp
  have haxis' i:=(haxis i).trans (a3x axisWeight_nonneg hm)
  have hplane' := (hplane 0).trans (a3x (dSz 0 termTrial) hm)
  have hcount:=h6 x P C _ _ z a b hr haxis' hplane'
  obtain ⟨_,_,_,_,ha,_,hz,hb,_⟩:=hr
  have hz' : 0≤z := by linarith only [hz]
  have ha' : 0≤a+1 := by linarith only [ha]
  let v :=FP axisWeight (fun k=>pN q k)
  let w (j:Fin 3) :=FP (SS j termTrial) (fun k=>pN q k)
  calc
    _≤(C.direct.card:ℚ)+(onCurves x C.toacW).card :=
      ((Nat.cast_le (α:=ℚ)).mpr (card_le_card hcover)).trans (card_union_q _ _)
    _≤(z+a+1)*v+b*w 1+w 0+w 2 := by
      have h2 : (C.direct.card:ℚ)≤w 2 :=hplane 2
      linarith only [hcount,h2,mul_le_mul_of_nonneg_left (haxis 0) hz',
        mul_le_mul_of_nonneg_left (haxis 1) ha',
        mul_le_mul_of_nonneg_left (hplane 1) hb,hplane 0]
    _ = _:= by
      simp only [v,w,rectPrice,FP,add_mul,one_mul,sum_add_distrib,mul_sum,mul_assoc]
private theorem stop_card (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    {x P R} {O:OriginCover x P R} (G:Geometry O) (D:cL)
    {f :Jet} (hf :f∈O.factors) (s :bAL) {q:Ideal Ambient} (hq:q∈stopped O f s) :
    ((marks x q).card:ℚ)≤FP (stopPrice D.a D.b D.z D.ar D.br (O.origin f) s)
      (fun k=>pN q k) := by
  have hl:=stopped_sub O s hq
  obtain ⟨ha,hh,_,_⟩:=O.geometric f hf q (mem_filter.mp hl).1
  have hm:=G.member f hf s q hl
  induction s using Fin.cases with
  | zero =>
    rw [stopped_zero] at hq
    exact h3 x (O.origin f) q ha hh (mem_filter.mp hq).2 hm
  | succ t =>
    have hd:=(mem_filter.mp hl).2.1 (Nat.succ_pos _)
    rw [stopped_succ] at hq
    have hn:=(mem_filter.mp hq).2
    revert hm hn
    refine Fin.lastCases ?_ (fun i => ?_) t
    · intro hm hn
      simpa only [stopPrice,Fin.cases_succ,Fin.lastCases_last] using
        rect_card h5 h6 P (O.origin f) ha hh hd hn (D.rect_ok (O.origin f)) hm
    · intro hm hn
      simpa only [stopPrice,Fin.cases_succ,Fin.lastCases_castSucc] using
        free_card h4 P (O.origin f) i ha hn (D.free_ok (O.origin f) i) hm
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    (h7:c7) :P6_7_1.c5:= by
  classical
  intro x P R O _
  let G:=h1 x P R O
  obtain ⟨D⟩:=h7
  let loss (f :Jet) (s :bAL) :=(stopped O f s).biUnion (fun q=>marks x q \ bankBook P)
  let booked (f :Jet) :=O.lineMarks f∪univ.biUnion (loss f)
  let charged:=O.factors.biUnion booked
  have hstop (f :Jet) (hf :f∈O.factors) (s :bAL) :
      ((loss f s).card:ℚ)≤FP (stopPrice D.a D.b D.z D.ar D.br (O.origin f) s)
        (J2 (stopped O f s)) := by
    rw [dot_mass]
    exact (card_biUnion_q _ _).trans (sum_le_sum fun q hq =>
      ((Nat.cast_le (α:=ℚ)).mpr (card_le_card sdiff_subset)).trans
        (stop_card h3 h4 h5 h6 G D hf s hq))
  have hcharged: (charged.card:ℚ) ≤
      ∑ f∈O.factors,(lineCharge f (O.line f) +
        ∑ s :bAL,FP (stopPrice D.a D.b D.z D.ar D.br (O.origin f) s)
          (J2 (stopped O f s))) := by
    apply (card_biUnion_q _ _).trans
    exact sum_le_sum fun f hf=>(card_union_q _ _).trans
      (add_le_add ((Nat.cast_le (α:=ℚ)).mpr (O.line_bound f hf))
        ((card_biUnion_q _ _).trans (sum_le_sum fun s _=>hstop f hf s)))
  let book :=(charged∪bankBook P)∪O.gH
  have hbook :book.card≤prefixFee := by
    have ho: (O.gH.card:ℚ)≤paidFee :=(Nat.cast_le (α:=ℚ)).mpr O.paid_bound
    have hk : ((bankBook P).card:ℚ)≤bankFee :=(Nat.cast_le (α:=ℚ)).mpr (h2 x P)
    have hsum:=D.Ya (Az O G)
    have h:=(card_union_q _ _).trans (add_le_add (card_union_q charged (bankBook P)) ho)
    change (book.card:ℚ)≤_ at h
    have hb: (book.card:ℚ)≤prefixFee := by
      simp only [Az] at hsum
      linarith only [h,hk,hcharged,hsum]
    exact_mod_cast hb
  let V:=O.factors.biUnion (final O)
  have vmem {q:Ideal Ambient} (hq:q∈V) :
      xN q∧q.height=2∧dual q∧(∀ t,passes P t q) ∧
        ∃ f∈O.factors,q∈O.parents f := by
    obtain ⟨f,hf,hq⟩:=mem_biUnion.mp hq
    obtain ⟨hp,hd,ht⟩:=mem_filter.mp hq
    obtain ⟨ha,hh,_,_⟩:=O.geometric f hf q hp
    exact ⟨ha,hh,hd,ht,f,hf,hp⟩
  let aI (q:V) :=aQF q.val (vmem q.property).1.prime
  refine ⟨⟨book,hbook,V.attach.image aI,?_,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨I,_,rfl⟩:=mem_image.mp hq
    obtain ⟨ha,hh,hd,_⟩:=vmem I.property
    exact cbq ha hh hd
  · intro q hq
    obtain ⟨I,_,rfl⟩:=mem_image.mp hq
    obtain ⟨f,hf,hI⟩:=(vmem I.property).2.2.2.2
    refine ⟨f,hf,I.val,hI,rfl,?_⟩
    intro i hi
    let j:Free :=⟨i.val-1,by have :=i.isLt; change i.val<5 at this; omega⟩
    have hj:j.succ=i:=Fin.ext (by simp [j]; omega)
    rw [← hj]
    simpa only [passes,free_bank] using (vmem I.property).2.2.2.1 j.castSucc
  · intro q hq
    obtain ⟨I,_,rfl⟩:=mem_image.mp hq
    simpa only [FullPass,aI,aQF,Ideal.mem_comap,passes,terminal_bank] using
      (vmem I.property).2.2.2.1 termTrial
  · intro γ hγ
    by_cases h:γ∈book
    · exact Or.inl h
    have hno (f :Jet) (hf :f∈O.factors) (hm:γ∈booked f) :False :=
      h (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨f,hf,hm⟩)))
    rcases O.Eh γ hγ with hp | ⟨f,hf,hl | ⟨I,hI,hm⟩⟩
    · exact (h (mem_union_right _ hp)).elim
    · exact (hno f hf (mem_union_left _ hl)).elim
    rcases placed O hI with ⟨s,hs⟩ | hv
    · exfalso
      apply hno f hf
      refine mem_union_right _ (mem_biUnion.mpr ⟨s,mem_univ _,mem_biUnion.mpr ⟨I,hs,?_⟩⟩)
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hγ,hm⟩,
        fun hb=>h (mem_union_left _ (mem_union_right _ hb))⟩
    · let J:V:=⟨I,mem_biUnion.mpr ⟨f,hf,hv⟩⟩
      exact Or.inr ⟨aI J,mem_image_of_mem _ (mem_attach _ _),
        eGu (vmem J.property).1.prime hm⟩
end
end q3rjQGe
end
