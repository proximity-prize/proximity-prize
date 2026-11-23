import ProximityPrize.SubmissionLower.ZHcXm6a
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P6_7_2_3
noncomputable section
open Finset Polynomial
open P6 (K dw)
open P6_7 (RectTail)
open P6_7_2
open cu (Jet j9 rD)
open DP (ad0 d3r)
open gT (Ambient iJ aNB)
open pI (xN dual oU)
open ac6.Bridge (aQF cbq)
open TD (FP J2 bfw cZV)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x) (pick :Picks (b:=b) x.h P.rows),
    TopPair x→Nonempty (OriginCover P pick)
def c2 :Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x) (pick :Picks (b:=b) x.h P.rows)
    (O:OriginCover P pick),Geometry O
def c3:Prop :=
  ∀ (b:RectTail) (x :Input b) (o:Origin) (Q:Ideal Ambient),
    xN Q → ¬ dual Q→MemberFits b o 0 Q →
    ((marks x Q).card:ℚ)≤FP (rankPrice b o) (sectionMass Q)
def c4 :Prop :=
  ∀ (b:RectTail) (x :Input b) (o:Origin) (i:FreeTest) (Q:Ideal Ambient),
    xN Q→Q.height=2→dual Q→MemberFits b o (freeStop i) Q →
    ∀ G:Jet,oU G (free b (freeStage i))→iJ G∉Q →
      (∀ γ∈x.Γ,onMark x Q γ→ rD G (x.M.label γ) (x.F.scalar γ)=0) →
      ∀ a h,FreeOK b o i a h →
        ((marks x Q).card:ℚ)≤FP (freePrice b i a h+freeAllowance b i) (sectionMass Q)
def c5:Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x) (Q:Ideal Ambient),
    (Bs b).paidOrder*(dw-131071+1+x.h)≤2*x.h*(Bs b).dI →
    ¬ terminalPass P Q→Nonempty (TerminalCutter x Q)
def c6:Prop :=
  ∀ (b:RectTail) (x :Input b) (o:Origin) (Q:Ideal Ambient),
    xN Q→Q.height=2→dual Q→MemberFits b o terminalStop Q →
    TerminalCutter x Q → ∀ z a h,TerminalOK b o z a h →
      ((marks x Q).card:ℚ)≤FP (terminalPrice b z a h+terminalAllowance b) (sectionMass Q)
def c7:Prop := ∀ b:RectTail,Nonempty (cL b)
private theorem freeStage_eq (i:FreeTest) :
    (⟨(freeStop i).val,by have :=i.isLt; change i.val+1<6; omega⟩:Ls)=freeStage i:=rfl
private theorem freeStop_ne (i:FreeTest) :freeStop i≠0:= by
  intro h
  have hv :=congrArg Fin.val h
  change i.val+1=0 at hv
  omega
private theorem freeStop_lt (i:FreeTest) : (freeStop i).val<6:= by
  have h:=i.isLt
  change i.val+1<6
  omega
private theorem freeStop_inv (i:FreeTest) :
    (⟨(freeStop i).val-1,by have :=i.isLt; change (i.val+1)-1<5; omega⟩:FreeTest)=i:= by
  apply Fin.ext
  exact Nat.add_sub_cancel _ _
private theorem pass_free {b:RectTail} {x :Input b} (P:Poles x) (i:FreeTest) (Q) :
    passes P (freeStop i) Q↔freePass P (freeStage i) Q:= by
  simp only [passes,ite_eq_right (freeStop_ne i),dite_eq_left (freeStop_lt i),freeStage_eq]
private theorem price_free {b:RectTail} (R:Rates b) (o:Origin) (i:FreeTest) :
    priceAt R o (freeStop i)=freePrice b i (R.freeSeed o i) (R.freeHeight o i) := by
  simp only [priceAt,ite_eq_right (freeStop_ne i),dite_eq_left (freeStop_lt i),freeStop_inv]
private theorem allowance_free (b:RectTail) (i:FreeTest) :
    bAY b (freeStop i)=freeAllowance b i:= by
  simp only [bAY,ite_eq_right (freeStop_ne i),dite_eq_left (freeStop_lt i),freeStop_inv]
private theorem height_lower {b:RectTail} (x :Input b) :b.kA.lo≤x.h:= by
  have h:=x.kA.1
  change (b.kA.lo:ℤ)≤x.M.iF at h
  change b.kA.lo≤x.M.iF.toNat
  omega
private theorem free_cutter {b:RectTail} {x :Input b} (P:Poles x) (i:Ls) (Q:Ideal Ambient)
    (hn : ¬ freePass P i Q) :
    ∃ G:Jet,oU G (free b i)∧iJ G∉Q ∧
      ∀ γ∈x.Γ,rD G (x.M.label γ) (x.F.scalar γ)=0:= by
  unfold freePass at hn
  push Not at hn
  obtain ⟨G,hG,hp⟩:=hn
  have hm:0<(free b i).m*dw:= by cases b <;> fin_cases i <;> decide
  have hw:cutoff x.h 0 (free b i)<(free b i).m*dw:= by
    simp only [cutoff,mul_zero,Nat.sub_zero]
    omega
  refine ⟨G,d3r P.crt x.word hG,hp,?_⟩
  intro γ hγ
  let M:=x.F.mark γ hγ
  have hd: (j9 (x.F.scalar γ)).natDegree≤131071+x.h:= by
    rw [j9,Polynomial.natDegree_map]
    exact P6_7.aic x.F hγ
  refine atp.dPr P.crt x.word P.nodes _ _ (P.marks γ hγ) hd M.bad.support
    M.bad.dw ?_ (free b i) _ hw G hG
  intro j hj
  rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,M.scalar_hits j hj]
variable {b:RectTail} {x :Input b} {P:Poles x} {pick :Picks (b:=b) x.h P.rows}
private theorem lost_prop {O:OriginCover P pick} {f s Q} (hQ:Q∈Hj O f s) :
    Q∈O.parents f∧(∀ t<s,passes P t Q) ∧ ¬ passes P s Q:= by
  obtain ⟨hl,hn⟩:=mem_filter.mp hQ
  obtain ⟨hp,ht⟩:=mem_filter.mp hl
  exact ⟨hp,ht,hn⟩
private theorem first_stop (O:OriginCover P pick) {f Q} (hQ:Q∈O.parents f) :
    (∃ s,Q∈Hj O f s)∨Q∈final O f := by
  by_cases h : ∀ s,passes P s Q
  · exact Or.inr (mem_filter.mpr ⟨hQ,h⟩)
  · obtain ⟨s,hs⟩:=not_forall.mp h
    have he : ∃ n:ℕ,∃ s :bAL,s.val=n ∧ ¬ passes P s Q:=⟨s.val,s,rfl,hs⟩
    obtain ⟨t,ht,hn⟩:=Nat.find_spec he
    have hp (u:bAL) (hu:u<t) :passes P u Q:= by
      by_contra hh
      exact (Nat.find_min he (show u.val<Nat.find he from ht ▸ hu)) ⟨u,rfl,hh⟩
    exact Or.inl ⟨t,mem_filter.mpr ⟨mem_filter.mpr ⟨hQ,hp⟩,hn⟩⟩
private theorem mass_losses (O:OriginCover P pick) (f :Jet) (k :Fin 4) :
    (∑ s,J2 (Hj O f s) k)≤J2 (O.parents f) k := by
  classical
  have hd:Set.PairwiseDisjoint (↑(univ :Finset bAL)) (Hj O f) := by
    intro s _ t _ hst
    change Disjoint (Hj O f s) (Hj O f t)
    rw [disjoint_left]
    intro Q hs ht
    rcases lt_or_gt_of_ne hst with h | h
    · exact (lost_prop hs).2.2 ((lost_prop ht).2.1 s h)
    · exact (lost_prop ht).2.2 ((lost_prop hs).2.1 t h)
  have hsub: (univ.biUnion (Hj O f))⊆O.parents f := fun Q hQ =>
    let ⟨_,_,hs⟩:=mem_biUnion.mp hQ
    (lost_prop hs).1
  have hm:=bfw hsub k
  simpa only [J2,pI.mass,Nat.cast_sum,sum_biUnion hd] using hm
private def toInvoice (O:OriginCover P pick) (G:Geometry O) :aAU b where
  factors :=O.factors
  origin :=O.origin
  line :=O.line
  arL f s :=J2 (Hj O f s)
  nonneg f _ s :=cZV (Hj O f s)
  spend_order :=G.spend_order
  nested:=O.nested
  line_pos :=O.line_pos
  initial f hf k :=(mass_losses O f k).trans (G.initial f hf k)
  bAW k :=(sum_le_sum fun f _=>mass_losses O f k).trans (G.bAW k)
  finalPool o k :=(sum_le_sum fun _ _ =>
    bfw (filter_subset _ _) k).trans (G.finalPool o k)
private theorem loss_bound (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    (O:OriginCover P pick) (G:Geometry O) (R:cL b) {f} (hf :f∈O.factors)
    (s :bAL) (Q:Ideal Ambient) (hQ:Q∈Hj O f s) :
    ((marks x Q).card:ℚ) ≤
      FP (priceAt R.toRates (O.origin f) s+bAY b s) (sectionMass Q) := by
  obtain ⟨hm,hs,hn⟩:=lost_prop hQ
  obtain ⟨hA,hh,_,_⟩:=O.geometric f hf Q hm
  have hfit :=G.member f hf s Q (mem_filter.mp hQ).1
  by_cases h0:s=0
  · subst s
    have hr :=h3 b x (O.origin f) Q hA (by simpa [passes] using hn) hfit
    simpa [priceAt,bAY] using hr
  have hpos :0<s := by
    have h: (0:bAL)≤ s :=Fin.zero_le _
    exact lt_of_le_of_ne h (Ne.symm h0)
  have hd:dual Q:= by simpa [passes] using hs 0 hpos
  by_cases ht:s.val<6
  · let i:FreeTest:=⟨s.val-1,by
      have hp:0<s.val :=hpos
      omega⟩
    have he :freeStop i=s := by
      apply Fin.ext
      change s.val-1+1=s.val
      have hp:0<s.val :=hpos
      omega
    have hfails : ¬ freePass P (freeStage i) Q:= fun hp =>
      hn (he ▸ (pass_free P i Q).2 hp)
    obtain ⟨F,hF,hproper,hvanish⟩:=free_cutter P (freeStage i) Q hfails
    rw [← he,price_free,allowance_free]
    exact h4 b x (O.origin f) i Q hA hh hd (he.symm ▸ hfit) F hF hproper
      (fun γ hγ _=>hvanish γ hγ) _ _ (R.freeOK _ _)
  · have he :s=terminalStop:= by
      apply Fin.ext
      have hb:=s.isLt
      change s.val=6
      omega
    subst s
    have hfail : ¬ terminalPass P Q:= by simpa [passes,terminalStop] using hn
    obtain ⟨C⟩:=h5 b x P Q (paid_guard b x.h (height_lower x)) hfail
    have htotal:=h6 b x (O.origin f) Q hA hh hd hfit C _ _ _ (R.terminalOK _)
    simpa [priceAt,bAY,terminalStop] using htotal
private theorem dot_mass (v :TD.GM) (S:Finset (Ideal Ambient)) :
    FP v (J2 S) = ∑ Q∈S,FP v (sectionMass Q) := by
  simp only [FP,J2,pI.mass,sectionMass,Nat.cast_sum,mul_sum]
  exact sum_comm
private theorem card_union_q (S T:Finset K) : ((S∪T).card:ℚ)≤S.card+T.card:= by
  exact_mod_cast card_union_le S T
private theorem card_biUnion_q {α:Type*} (S:Finset α) (T:α→Finset K) :
    ((S.biUnion T).card:ℚ) ≤ ∑ a∈S,((T a).card:ℚ) := by
  exact_mod_cast (card_biUnion_le : (S.biUnion T).card≤_)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    (h7:c7) :P6_7_2.c3:= by
  classical
  intro b x P pick top
  obtain ⟨O⟩:=h1 b x P pick top
  obtain ⟨R⟩:=h7 b
  let G:=h2 b x P pick O
  let stops (f :Jet) (s :bAL) :=(Hj O f s).biUnion (marks x)
  let booked (f :Jet) :=O.lineMarks f∪univ.biUnion (stops f)
  let book :=O.gH∪O.factors.biUnion booked
  let B:=toInvoice O G
  have hstop (f :Jet) (hf :f∈O.factors) (s :bAL) :
      ((stops f s).card:ℚ) ≤
        FP (priceAt R.toRates (B.origin f) s+bAY b s) (B.arL f s) := by
    rw [show B.arL f s=J2 (Hj O f s) from rfl,dot_mass]
    exact (card_biUnion_q _ _).trans (sum_le_sum fun Q hQ =>
      loss_bound h3 h4 h5 h6 O G R hf s Q hQ)
  have hbooked (f :Jet) (hf :f∈O.factors) :
      ((booked f).card:ℚ)≤(lineCharge b f (B.line f) :ℚ) +
        ∑ s,FP (priceAt R.toRates (B.origin f) s+bAY b s) (B.arL f s) := by
    have hl: ((O.lineMarks f).card:ℚ)≤lineCharge b f (B.line f) := by
      exact_mod_cast O.line_bound f hf
    exact (card_union_q _ _).trans (add_le_add hl
      ((card_biUnion_q _ _).trans (sum_le_sum fun s _=>hstop f hf s)))
  have hb:book.card≤prefixFee b:= by
    have hp: ((O.gH.card:ℕ) :ℚ)≤ee3 b:= by exact_mod_cast O.paid_bound
    have hq:=(card_union_q O.gH _).trans (add_le_add hp
      ((card_biUnion_q _ _).trans (sum_le_sum fun f hf=>hbooked f hf)))
    exact_mod_cast hq.trans (R.Az B)
  let V:=O.factors.biUnion (final O)
  have Z1 {Q:Ideal Ambient} (hQ:Q∈V) :
      xN Q∧Q.height=2 ∧ ∀ s,passes P s Q:= by
    obtain ⟨f,hf,hfQ⟩:=mem_biUnion.mp hQ
    obtain ⟨hparent,ht⟩:=mem_filter.mp hfQ
    obtain ⟨ha,hh,_,_⟩:=O.geometric f hf Q hparent
    exact ⟨ha,hh,ht⟩
  let aI (Q:V) :=aQF Q.val (Z1 Q.property).1.prime
  refine ⟨⟨book,hb,V.attach.image aI,?_,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨Q,_,rfl⟩:=mem_image.mp hq
    obtain ⟨ha,hh,ht⟩:=Z1 Q.property
    exact cbq ha hh (by simpa [passes] using ht 0)
  · intro q hq i hi
    obtain ⟨Q,_,rfl⟩:=mem_image.mp hq
    have hi' : i.val≠0:= fun h=>hi (Fin.ext h)
    let s :bAL:=⟨i.val,i.isLt.trans (by decide)⟩
    have hs :s≠0:= fun h=>hi' (congrArg Fin.val h)
    have hlt:s.val<6:=i.isLt
    have ht:=(Z1 Q.property).2.2 s
    rw [passes,ite_eq_right hs,dite_eq_left hlt] at ht
    have he : (⟨s.val,hlt⟩:Ls)=i:=Fin.ext rfl
    rw [he] at ht
    intro F hF
    change iJ F∈Q.val
    exact ht F hF
  · intro q hq
    obtain ⟨Q,_,rfl⟩:=mem_image.mp hq
    have hp:terminalPass P Q.val := by
      simpa [passes,terminalStop] using (Z1 Q.property).2.2 terminalStop
    exact hp
  · intro γ hγ
    rcases O.Eh γ hγ with hp | ⟨f,hf,hl | ⟨Q,hQ,hm⟩⟩
    · exact Or.inl (mem_union_left _ hp)
    · exact Or.inl (mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_union_left _ hl⟩))
    rcases first_stop O hQ with ⟨s,hs⟩ | hv
    · have hmarks :γ∈marks x Q:=mem_filter.mpr ⟨hγ,hm⟩
      have hstop:γ∈stops f s :=mem_biUnion.mpr ⟨Q,hs,hmarks⟩
      have hbook :γ∈booked f :=mem_union_right _ (mem_biUnion.mpr ⟨s,mem_univ _,hstop⟩)
      exact Or.inl (mem_union_right _ (mem_biUnion.mpr ⟨f,hf,hbook⟩))
    · let J:V:=⟨Q,mem_biUnion.mpr ⟨f,hf,hv⟩⟩
      refine Or.inr ⟨aI J,mem_image_of_mem _ (mem_attach _ _),?_⟩
      intro F hF
      apply RingHom.mem_ker.mpr
      change rD F (x.M.label γ) (x.F.scalar γ)=0
      rw [← aNB]
      exact RingHom.mem_ker.mp (hm hF)
end
end P6_7_2_3
end
section
set_option autoImplicit true
namespace qu56FMb
noncomputable section
open P6_7 (RectTail)
open P6_7_2 (Bs)
open P6_7_2_3 (sectionMass)
open cu (FX L Shape)
open gT (Ambient aQ gk Pp B4)
open ac3 (aYy)
open YY (xg aef a9E Si U7)
open TD (GM FP)
open scoped Classical BigOperators
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev s (b:RectTail) :=(Bs b).terminal
abbrev r (b:RectTail) :=(Bs b).paidOrder
abbrev den (b:RectTail) :ℚ:=(r b+1 :ℕ)
def RectCaps (s :Shape) (F:Ambient) :Prop :=
  ∀ a∈F.support,a 0≤ s.U∧a 1≤ s.U∧a 2+a 3≤ s.B∧a 3≤ s.J
def cut (Q:Ideal Ambient) (F:Ambient) :Finset (Ideal Ambient) :=
  (Q ⊔ Ideal.span {F}).minimalPrimesFinset
def qv (Q:Ideal Ambient) (F:Ambient) :Finset (Ideal Ambient) :=
  (cut Q F).filter fun I => ¬ aYy I
def points (Q:Ideal Ambient) (F:Ambient) :Finset (Ideal Ambient) :=
  (cut Q F).filter aYy
def PaidOn (F:Ambient) (r :ℕ) (I:Ideal Ambient) :Prop :=
  ∀ a :Exponent,(∑ i,a i)≤ r→Rk.KR a F∈I
def paidWeight (F:Ambient) (r :ℕ) (I:Ideal Ambient) :ℕ :=
  if PaidOn F r I then r+1 else 1
abbrev dmO (I:Ideal Ambient) (k :Fin 4) :=
  gk (I.map (MvPolynomial.map (algebraMap FX aQ)) ⊔
    Ideal.span {(![Pp 1,Pp 0,Pp 2,B4 2 3] :
      Fin 4→MvPolynomial (Fin 4) aQ) k})
def curveMass (I:Ideal Ambient) :GM:= fun k=>Module.finrank aQ (dmO I k)
def divisorMass (Q:Ideal Ambient) (F:Ambient) (r :ℕ)
    (mass :Ideal Ambient→ℚ) :ℚ :=
  ∑ I∈qv Q F,(paidWeight F r I:ℚ)*mass I
def firstWeight (s :Shape) (k :Fin 4) :GM :=
  let u:ℚ:=s.U
  let j:ℚ:=s.J
  let y :ℚ:=(s.B-s.J:ℕ)
  ![![u,y,j,0],![u,y,j,0],![0,2*u,0,j],![0,0,2*u,y+j]] k
def firstMass (s :Shape) (Q:Ideal Ambient) :GM :=
  fun k=>FP (firstWeight s k) (sectionMass Q)
def rowPrice (s :Shape) :GM := ![s.U,s.U,(s.B-s.J:ℕ),s.J]
def aHm (b:RectTail) (z a h:ℚ) :GM :=
  let v :=rowPrice (s b)
  let w:GM := ![z,a+1,h,0]
  fun k=>if r b=0 then w k/den b else max (v k) (w k/den b)
structure Descended (I:Ideal Ambient) (C:MvPolynomial (Fin 2) L) (g:ℕ) :Prop where
  irreducible :Irreducible C
  projection :xg I=Ideal.span {MvPolynomial.map U7 C}
  positive :0<g
  plane_pos :0<C.totalDegree
  root :gT.bbt (Si I) g (a9E I)
  u7:C.totalDegree*g≤aef I
  first: (C.degreeOf 0:ℚ)*g≤ curveMass I 0
  second: (C.degreeOf 1 :ℚ)*g≤ curveMass I 1
end
end qu56FMb
end
