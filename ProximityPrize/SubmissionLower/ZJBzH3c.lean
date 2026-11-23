import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.ZWpWUpd
import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.Z9vQBQe
import ProximityPrize.SubmissionLower.ZXdt6vc
set_option Elab.async false
section
set_option autoImplicit true
namespace q0T1nKc
theorem proof :qqwac6b.c1 :=
  q6CrDDe.of_children q978Lma.proof P5_7_1_5_4_2_1_2.proof
end q0T1nKc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qTplN5b
noncomputable section
open Finset Polynomial
open P6 (K p blockLength)
open P5_7 (midAgreement)
open P6_7_1 (Input Poles degree)
open q3rjQGe (NativeOK nativeRate nativeSlope gap)
open qHuUuEa (DescendedMarks)
open qK3TPae (AmplifiedCut highFee regular high_count polar_count)
open gT (abX aQ)
open YY (bnQ)
open private b1I from ProximityPrize.SubmissionLower.G
open quN7Z4a (physicalWeight)
open qb0hmCe (CurveModel)
open gT (kM)
open Cu (sQ)
open private sheet_count from ProximityPrize.SubmissionLower.ZlPdtnc
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (e H g c W M:ℕ)
    (S:quN7Z4a.Sheet Q J e H T z s),
    3≤e→e<p→Q.totalDegree*e<p→NativeOK e g c W M →
    W<physicalWeight degree S.root.equation →
    Set.InjOn z (T:Set K)→(∀ γ∈T,(s γ).natDegree≤degree) →
    ∃ C:AmplifiedCut T,C.ng.sum (fun _ n=>n)<p^C.order*(highFee e g c*H+1)
def c2 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (e H W:ℕ)
    (S:quN7Z4a.Sheet Q J e H T z s),
    Set.InjOn z (T:Set K)→0<e→Q.totalDegree*e<p →
    physicalWeight degree S.root.equation≤W →
    ∃ (C:CurveModel Q) (F:P5_7_3_5_2.Sheet C z s),
      F.d=e∧F.h≤H∧F.weight degree W∧F.marks⊆regular Q z T ∧
      ((regular Q z T) \ F.marks).card≤H
def c3:Prop :=P5_7_3_5_2.c2
def c4 :Prop :=
  ∀ {Q:sQ} {C:CurveModel Q} {z :K→K} {s :K→K[X]}
    (F:P5_7_3_5_2.Sheet C z s) (e W:ℕ),
    F.d=e→3≤e→e<p→e*degree≤W→polarDegree e W<p →
    F.weight degree W→(∀ γ∈F.marks,(s γ).natDegree≤degree) →
    P5_7_3_5_2.BranchBudget F degree (6+2*e) (poleFee e W)
private theorem sheet {x :Input} {T:Finset K} {J:Ideal kM} {Q e H}
    (A:DescendedMarks x T J Q e H) (he :0<e) :
    ∃ (C:sQ) (hC:Irreducible C),C.totalDegree= Q.totalDegree ∧
      Nonempty (@quN7Z4a.Sheet C ⟨hC⟩ J e H T x.M.label x.F.scalar) := by
  have hlen:Module.finrank aQ (abX J)= Q.totalDegree*e := by
    obtain ⟨_,C,hc,hp,_,hs,_,_⟩:=A.curve
    change J.comap gT.pZ =
      Ideal.span {MvPolynomial.map YY.U7 C} at hp
    let f :=MvPolynomial.map YY.U7 C
    have hf :f≠0:=(map_ne_zero_iff _ (MvPolynomial.map_injective _
      YY.U7.injective)).mpr hc.ne_zero
    have hdeg:=b1I f hf Q (hp.symm.trans A.projection)
    rw [← hdeg,bnQ]
    exact hs
  exact quN7Z4a.sheet he A.curve hlen A.marks
private theorem marks {x :Input} (P:Poles x) {T:Finset K} (hT:T⊆x.Γ) :
    qkgz7gb.UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,?_,?_,?_⟩
  · intro γ hγ
    exact (P6_7.aic x.F (hT hγ)).trans
      (Nat.add_le_add_left (P6_7_1.heights x).2 _)
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(by decide :midAgreement≤P6.dw).trans m.bad.dw,
      m.scalar_hits⟩
  · exact ⟨x.h,(by decide :0<P6_7_1.packetLo).trans_le (P6_7_1.heights x).1,
      P.D,fun γ hγ=>P.marks γ (hT hγ)⟩
private theorem slope {e :ℕ} (he :0<e) (d:ℕ) :
    nativeSlope d e*((e :ℚ)*d)=(d:ℚ)^2/3+(4*(e :ℚ)^2+8*e)*d:= by
  have heq : (e :ℚ)≠0:=Nat.cast_ne_zero.mpr he.ne'
  unfold nativeSlope
  field_simp
  ring
private theorem low_rate {e g c W:ℕ} (he :3≤e) (hW:e*degree≤W) :
    ((7+6*e :ℕ) :ℚ)+(2*e*blockLength+poleFee e W:ℕ)/(gap:ℚ) ≤
      nativeRate e g c W:= by
  have hp:3*e*e*degree≤(6*e-2)*W:= calc
    _=(3*e)*(e*degree) := by ring
    _≤_:=Nat.mul_le_mul (by omega) hW
  have hn:2*e*blockLength+poleFee e W ≤
      (2*e+1)*blockLength+(6*e-2)*W-3*e*e*degree := by
    rw [Nat.add_sub_assoc hp]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  exact (add_le_add_right (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn)
    (Nat.cast_nonneg gap)) _).trans (le_max_right _ _)
private theorem divide_gap {e g c W t H d:ℕ} (he :3≤e) (hW:e*degree≤W)
    (h:gap*t≤((7+6*e)*gap+2*e*blockLength+poleFee e W)*H+(4*e*gap*d)*e) :
    (t:ℚ)≤nativeRate e g c W*H+4*(e :ℚ)^2*d:= by
  have hgap: (0:ℚ)<gap:=Nat.cast_pos.mpr (by decide :0<gap)
  let n:ℕ:=2*e*blockLength+poleFee e W
  have h' : (gap:ℚ)*t≤(((7+6*e :ℕ) :ℚ)*gap+n)*H+(4*(e :ℚ)*gap*d)*e := by
    exact_mod_cast (show gap*t≤((7+6*e)*gap+n)*H+(4*e*gap*d)*e from by
      simpa only [n,add_assoc] using h)
  have h'' : (t:ℚ)≤(((7+6*e :ℕ) :ℚ)+(n:ℚ)/gap)*H+4*(e :ℚ)^2*d:= by
    apply le_of_mul_le_mul_left _ hgap
    refine h'.trans_eq ?_
    field_simp [hgap.ne']
  exact h''.trans (add_le_add_left (mul_le_mul_of_nonneg_right
    (low_rate (g:=g) (c:=c) he hW) (Nat.cast_nonneg H)) _)
private theorem low_count (prepare :c2) (local_test :c3) (poles :c4)
    {Q:sQ} [hQ:Fact (Irreducible Q)] {J:Ideal kM} {T:Finset K}
    {z s w e H g c W} (S:quN7Z4a.Sheet Q J e H T z s)
    (m:qkgz7gb.UJ degree w T z s)
    (he :3≤e) (heP:e<p) (hp:Q.totalDegree*e<p)
    (hl:physicalWeight degree S.root.equation≤W) (hW:e*degree≤W)
    (hpW:polarDegree e W<p) :
    (T.card:ℚ)≤nativeRate e g c W*H+4*(e :ℚ)^2*Q.totalDegree+(Q.totalDegree :ℚ)^2/3:= by
  have he0:0<e := by omega
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  obtain ⟨C,F,hd,hh,hw,hsub,hexc⟩:=prepare Q J T z s e H W S m.Kw he0 hp hl
  obtain ⟨R⟩:=P5_7_3_5_2.starts m
  have hbranch :=poles F e W hd he heP hW hpW hw (fun γ hγ=>m.degree γ (hU (hsub hγ)))
  have h:=sheet_count local_test m R (hsub.trans hU) hd.le heP hbranch
  change gap*F.marks.card ≤
    ((6+2*e+4*e)*gap+2*e*blockLength+poleFee e W)*F.h+(4*e*gap*Q.totalDegree)*F.d at h
  rw [hd] at h
  have hN :gap*U.card≤((7+6*e)*gap+2*e*blockLength+poleFee e W)*H+
      (4*e*gap*Q.totalDegree)*e := by
    rw [← card_sdiff_add_card_eq_card hsub,Nat.mul_add]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ hexc)
      (h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _))).trans_eq (by ring)
  have hmain:=divide_gap (g:=g) (c:=c) he hW hN
  have hbad:=polar_count qGzrWfb.proof hQ.out m.Kw S.onSeed
  have hbadQ:3*((T \ U).card:ℚ)≤(Q.totalDegree :ℚ)*(Q.totalDegree-1 :ℕ) := by
    exact_mod_cast hbad
  have hs : ((Q.totalDegree-1 :ℕ) :ℚ)≤Q.totalDegree := by exact_mod_cast Nat.sub_le Q.totalDegree 1
  have hbad' := hbadQ.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [← card_sdiff_add_card_eq_card hU,Nat.cast_add]
  nlinarith only [hbad',hmain]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qHuUuEa.c2 := by
  intro x P T J Q e H g c W M A he hok
  have he0:0<e := by omega
  obtain ⟨C,hC,hdeg,⟨S⟩⟩:=sheet A he0
  let:Fact (Irreducible C) :=⟨hC⟩
  have m:=marks P A.subset
  have hc:C.totalDegree*e<p:=hdeg ▸ A.seed_lt
  have heP:e<p:=(Nat.le_mul_of_pos_left _ (hdeg ▸ A.plane_pos)).trans_lt hc
  rw [slope he0]
  by_cases hw:physicalWeight degree S.root.equation≤W
  · obtain ⟨_,hW,_,_,_,hpW⟩:=hok
    have h:=low_count h2 h3 h4 (g:=g) (c:=c) S m he heP hc hw hW hpW
    rw [hdeg] at h
    have hrest: (0:ℚ)≤8*(e :ℚ)*Q.totalDegree+e := by positivity
    linarith only [h,hrest]
  · obtain ⟨B,hB⟩:=h1 C J T x.M.label x.F.scalar e H g c W M S
      he heP hc hok (lt_of_not_ge hw) m.Kw m.degree
    have h:=Nat.lt_of_mul_lt_mul_left ((high_count B).trans_lt hB)
    have hcard: (T.card:ℚ)≤(highFee e g c:ℕ)*H := by
      exact_mod_cast Nat.le_of_lt_succ h
    have hr : ((highFee e g c:ℕ) :ℚ)≤nativeRate e g c W:=le_max_left _ _
    have hrest: (0:ℚ)≤(Q.totalDegree :ℚ)^2/3+(4*(e :ℚ)^2+8*e)*Q.totalDegree+e := by
      positivity
    linarith only [hcard.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg H)),hrest]
end
end qTplN5b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qNRjwze
noncomputable section
open Finset
open P6 (K p blockLength dw)
open P6_7 (RectTail)
open P6_7_2 (Input Picks Poles free Bs)
open P5_7 (farAgreement)
open cu (qD)
open gT (tK FW)
open pI (NO abM)
open qQ (VN aJr)
open aF0 (power BJ YM)
open akZ (aSK)
open baX (mix)
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open scoped Classical
private abbrev D:ℕ:=133477
private abbrev a :=BJ D 115
private abbrev v :=YM D 115 25
private abbrev jX:=3*((115-25)*v+25*a)+115^2
private theorem fixed_marks {b:RectTail} (x :Input b) (G:tK) (hG:abM G 115 25) :
    (x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0).card≤jX:= by
  let T:=x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0
  let β:ℚ:=((blockLength-farAgreement:ℕ) :ℚ)/((farAgreement-D:ℕ) :ℚ)
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hv : (v :ℚ)≤a := by exact_mod_cast (min_le_left a (power D*(25-1)+D))
  have hT:T⊆x.Γ:=filter_subset _ _
  have hD:131071+(Bs b).hi≤D:= by cases b <;> decide
  have h:=cSy (x.F.distinct.mono hT) ⟨by decide,by decide,by decide,by decide⟩
    G hG (fun γ hγ=>(mem_filter.mp hγ).2) (β*a) (β*v) (by positivity)
    (mul_le_mul_of_nonneg_left hv hβ) (fun U hU f hf hp hb hj hr=> by
      have hc:=qUJtx6c.ePE (x.F.distinct.mono (hU.trans hT))
        (fun γ hγ=>((P6_7.aic x.F (hT (hU hγ))).trans
          (Nat.add_le_add_left (emE x) _)).trans hD)
        (w:=x.M.word) (fun γ hγ =>
          let m:=x.F.mark γ (hT (hU hγ))
          ⟨m.bad.support,(by decide :farAgreement≤dw).trans m.bad.dw,m.scalar_hits⟩)
        (d:=D) (by decide) (by decide) (by decide) f hf hp hb hj hr
      refine hc.trans_eq ?_
      change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
      unfold mix
      ring)
  have hβ₃:β≤3:= by
    change (82365:ℚ)/46302≤3
    apply (div_le_iff₀ (by decide : (0:ℚ)<46302)).mpr
    exact_mod_cast (show 82365≤3*46302 from by decide)
  have h' : (T.card:ℚ)≤(jX:ℚ) := calc
    _≤ mix 115 25 (β*a) (β*v)+(115^2 :ℕ) :=h
    _≤ mix 115 25 (3*a) (3*v)+(115^2 :ℕ) := by unfold mix; gcongr
    _ = _:= by unfold mix jX; push_cast; ring
  exact_mod_cast h'
theorem stripped_paid {b:RectTail} (x :Input b) {P:Poles x} (pick :Picks (b:=b) x.h P.rows)
    (A:NO (anchorRow pick) (free b 0)) (s :aSK A) :
    ∃ gH :Finset K,gH.card≤au1 b ∧
      ∀ γ∈x.Γ,qD (x.M.label γ) s.content=0∨FW A.equation (x.F.scalar γ)=0 →
        γ∈gH := by
  let T:=x.Γ.filter fun γ=>FW A.equation (x.F.scalar γ)=0
  let S:=x.Γ.filter fun γ=>qD (x.M.label γ) s.content=0
  let C:VN :=⟨s.content,s.content_ne,∅⟩
  have hU: (free b 0).U≤1139:= by cases b <;> decide
  have hseed :=aJr (T:=S) (label :=x.M.label) (fun _ _ _ _ h=>sub_left_inj.mp h)
    C ((s.content_le.trans hU).trans_lt (by decide)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  have hS:S.card≤(p+1)*1139:= by
    exact (by simpa only [C,card_empty,Nat.add_zero] using hseed :
      S.card≤(p+1)*s.content.totalDegree).trans (Nat.mul_le_mul_left _ (s.content_le.trans hU))
  have hT:T.card≤jX:=fixed_marks x _ A.equation_caps
  have hfee : (p+1)*1139+jX≤au1 b:= by cases b <;> decide
  exact ⟨S∪T,(card_union_le _ _).trans ((Nat.add_le_add hS hT).trans hfee),
    fun γ hγ h=>mem_union.mpr (h.imp (fun h=>mem_filter.mpr ⟨hγ,h⟩) (fun h=>mem_filter.mpr ⟨hγ,h⟩))⟩
end
end qNRjwze
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
namespace qigFtUb
open P6_7 (RectTail)
open P6_7_2
set_option quotPrecheck false in
local notation "AxisGrade" b:arg i:arg =>
  (∀ h,(RectTail.kA b).lo≤h→h≤(Bs b).hi →
    Subrect b (Lc i 0) ∧
    rectDebit b h (Lc i 0)<ZN b h (Lc i 0) 0 (Fin.val i+1) (seedCap i+1))
def c1 :Prop :=
  ∀ i:jJ .pruned,67≤ i.val→AxisGrade .pruned i
def c2 :Prop := ∀ i:jJ .tailOne,AxisGrade .tailOne i
def c3:Prop := ∀ i:jJ .tailTwo,AxisGrade .tailTwo i
def c4 :Prop := ∀ i:jJ .tailThree,AxisGrade .tailThree i
private theorem iy (b:RectTail) :
    check b (full b) ((Bs b).ordinateCap+1) 0=true := by
  cases b <;> rfl
private theorem tested_swap {b:RectTail} (i:jJ b) :
    Lc i 1=⟨(Lc i 0).t,(Lc i 0).z⟩:= by
  simp [Lc,show (1 :Fin 2)≠0 by decide]
private theorem pruned (hp:c1) (i:jJ .pruned) :AxisGrade .pruned i:= by
  by_cases hi:i.val<67
  · have hc:check .pruned (Lc i 0) (i.val+1) (seedCap i+1)=true := by
      rcases i with ⟨j,hj⟩
      rw [← gradeTest_eq hj]
      simpa only [Nat.zero_add] using prefix_get (prefix_add prunedFirst prunedSecond) hi
    intro h hlo hhi
    exact checked .pruned (Lc i 0) _ _ (Nat.succ_pos _) hc h hlo hhi
  · exact hp i (by omega)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_7_2.c6:= by
  intro b h hlo hhi
  obtain ⟨hs,ht⟩:=checked b (full b) _ 0 (Nat.succ_pos _) (iy b) h hlo hhi
  refine ⟨hs,ht,?_⟩
  have gw : ∀ i:jJ b,AxisGrade b i:= by
    cases b
    · exact pruned h1
    · exact h2
    · exact h3
    · exact h4
  intro i kd
  have H :=gw i h hlo hhi
  fin_cases kd
  · exact H
  · rcases hr :Lc i 0 with ⟨u,x⟩
    rw [hr] at H
    have hswap:=tested_swap i
    rw [hr] at hswap
    change Subrect b (Lc i 1) ∧
      rectDebit b h (Lc i 1)<ZN b h (Lc i 1) 1 (i.val+1) (seedCap i+1)
    rw [hswap,debit_swap,gain_swap]
    exact ⟨⟨H.1.2.1,H.1.1,H.1.2.2.2,H.1.2.2.1⟩,H.2⟩
end qigFtUb
end
