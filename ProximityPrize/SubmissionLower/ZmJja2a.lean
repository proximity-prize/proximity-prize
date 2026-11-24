import ProximityPrize.SubmissionLower.ZvIni8b
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZKtTCEc
import ProximityPrize.SubmissionLower.ZoOOLsc
import ProximityPrize.SubmissionLower.ZAZ7Tec
import ProximityPrize.SubmissionLower.Zt2VnXa
import ProximityPrize.SubmissionLower.ZuoZ7sd
import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZOb5aoe
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.Z2oJVua
import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZDw1jvc
import ProximityPrize.SubmissionLower.ZB2eCyc
import ProximityPrize.SubmissionLower.Z1xfoqa
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZAJiURc
import ProximityPrize.SubmissionLower.ZlInw9b
import ProximityPrize.SubmissionLower.ZD84Mrc
set_option Elab.async false
section
section
set_option autoImplicit true
namespace qWbWDnc
theorem proof :qJOpoVa.c2 :=
  qypA4Sc.of_children qWnROxa.proof qlcyGcd.proof
    qrrOjma.proof
end qWbWDnc
end
end
section
set_option autoImplicit true
namespace qxtWb5a
abbrev polarDegree (D e W:ℕ) :ℕ:=(2*e-1)*W-e*e*D
abbrev poleFee (D e W:ℕ) :ℕ:=(6*e-2)*W-3*e*e*D
end qxtWb5a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qxtWb5a
noncomputable section
open Finset Polynomial
open P6 (K p blockLength dw)
open P6_7 (RectTail bW4)
open P6_7_2 (Input)
open P6_7_2_3 (degree oldAgreement NativeOK nativeRate)
open q6hAhQd (DescendedMarks nativeSlope)
open qK3TPae (AmplifiedCut highFee regular high_count polar_count)
open quN7Z4a (physicalWeight)
open qb0hmCe (CurveModel)
open P5_7_3_5_2 (BranchBudget gap)
open gT (kM abX aQ)
open YY (bnQ)
open Cu (sQ)
open private b1I from ProximityPrize.SubmissionLower.G
open private input_degree from ProximityPrize.SubmissionLower.Zzatq8a
open private sheet_count from ProximityPrize.SubmissionLower.ZlPdtnc
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (D e H g c W M:ℕ)
    (S:quN7Z4a.Sheet Q J e H T z s),
    0<D→3≤e→e<p→Q.totalDegree*e<p→NativeOK D e g c W M →
    W<physicalWeight D S.root.equation →
    Set.InjOn z (T:Set K)→(∀ γ∈T,(s γ).natDegree≤D) →
    ∃ C:AmplifiedCut T,C.ng.sum (fun _ n=>n)<p^C.order*(highFee e g c*H+1)
def c2 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (D e H W:ℕ)
    (S:quN7Z4a.Sheet Q J e H T z s),
    Set.InjOn z (T:Set K)→0<e→Q.totalDegree*e<p →
    physicalWeight D S.root.equation≤W →
    ∃ (C:CurveModel Q) (F:P5_7_3_5_2.Sheet C z s),
      F.d=e∧F.h≤H∧F.weight D W∧F.marks⊆regular Q z T ∧
      ((regular Q z T) \ F.marks).card≤H
def c3:Prop :=P5_7_3_5_2.c2
def c4 :Prop :=
  ∀ {Q:sQ} {C:CurveModel Q} {z :K→K} {s :K→K[X]}
    (F:P5_7_3_5_2.Sheet C z s) (D e W:ℕ),
    0<D→D <p→F.d=e→3≤e→e<p→e*D ≤W→polarDegree D e W<p →
    F.weight D W→(∀ γ∈F.marks,(s γ).natDegree≤D) →
    BranchBudget F D (6+2*e) (poleFee D e W)
private theorem sheet {b:RectTail} {x :Input b} {T:Finset K} {J:Ideal kM} {Q e H}
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
private theorem marks {b:RectTail} {x :Input b} {T:Finset K} (hT:T⊆x.Γ) :
    qkgz7gb.UJ (degree b) x.M.word T x.M.label x.F.scalar := by
  obtain ⟨P,_,_,_,hP⟩:=bW4 x.M x.F x.H x.bY
  have hpos :0<b.kA.lo:= by cases b <;> decide
  have hlo: (b.kA.lo:ℤ)≤x.M.iF:=x.kA.1
  have h:0<x.h:= by
    change 0<x.M.iF.toNat
    omega
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
    fun γ hγ=>input_degree x (hT hγ),?_,⟨x.h,h,P,fun γ hγ=>hP γ (hT hγ)⟩⟩
  intro γ hγ
  let m:=x.F.mark γ (hT hγ)
  exact ⟨m.bad.support,(by decide :oldAgreement≤dw).trans m.bad.dw,
    m.scalar_hits⟩
private theorem slope {e :ℕ} (he :0<e) (d:ℕ) :
    nativeSlope d e*((e :ℚ)*d)=(d:ℚ)^2/3+(4*(e :ℚ)^2+8*e)*d:= by
  have heq : (e :ℚ)≠0:=Nat.cast_ne_zero.mpr he.ne'
  unfold nativeSlope
  field_simp
  ring
private theorem low_rate {D e g c W:ℕ} (he :3≤e) (hW:e*D ≤W) :
    ((7+6*e :ℕ) :ℚ)+(2*e*blockLength+poleFee D e W:ℕ)/(gap D:ℚ) ≤
      nativeRate D e g c W:= by
  have hp:3*e*e*D ≤(6*e-2)*W:= calc
    _=(3*e)*(e*D) := by ring
    _≤_:=Nat.mul_le_mul (by omega) hW
  have hn:2*e*blockLength+poleFee D e W ≤
      (2*e+1)*blockLength+(6*e-2)*W-3*e*e*D:= by
    rw [Nat.add_sub_assoc hp]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  exact (add_le_add_right (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn)
    (Nat.cast_nonneg (gap D))) _).trans (le_max_right _ _)
private theorem divide_gap {D e g c W t H d:ℕ} (hD:D <oldAgreement)
    (he :3≤e) (hW:e*D ≤W)
    (h:gap D*t≤((7+6*e)*gap D+2*e*blockLength+poleFee D e W)*H+(4*e*gap D*d)*e) :
    (t:ℚ)≤nativeRate D e g c W*H+4*(e :ℚ)^2*d:= by
  have hgap: (0:ℚ)<gap D:=Nat.cast_pos.mpr (Nat.sub_pos_of_lt hD)
  let n:ℕ:=2*e*blockLength+poleFee D e W
  have h' : (gap D:ℚ)*t≤(((7+6*e :ℕ) :ℚ)*gap D+n)*H+(4*(e :ℚ)*gap D*d)*e := by
    exact_mod_cast (show gap D*t≤((7+6*e)*gap D+n)*H+(4*e*gap D*d)*e from by
      simpa only [n,add_assoc] using h)
  have h'' : (t:ℚ)≤(((7+6*e :ℕ) :ℚ)+(n:ℚ)/gap D)*H+4*(e :ℚ)^2*d:= by
    apply le_of_mul_le_mul_left _ hgap
    refine h'.trans_eq ?_
    field_simp [hgap.ne']
  exact h''.trans (add_le_add_left (mul_le_mul_of_nonneg_right
    (low_rate (g:=g) (c:=c) he hW) (Nat.cast_nonneg H)) _)
private theorem low_count (prepare :c2) (local_test :c3) (poles :c4)
    {Q:sQ} [hQ:Fact (Irreducible Q)] {J:Ideal kM} {T:Finset K}
    {z s w D e H g c W} (S:quN7Z4a.Sheet Q J e H T z s)
    (m:qkgz7gb.UJ D w T z s) (hD0:0<D) (hD:D <oldAgreement)
    (he :3≤e) (heP:e<p) (hp:Q.totalDegree*e<p)
    (hl:physicalWeight D S.root.equation≤W) (hW:e*D ≤W)
    (hpW:polarDegree D e W<p) :
    (T.card:ℚ)≤nativeRate D e g c W*H+4*(e :ℚ)^2*Q.totalDegree+(Q.totalDegree :ℚ)^2/3:= by
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  obtain ⟨C,F,hd,hh,hw,hsub,hexc⟩:=prepare Q J T z s D e H W S m.Kw (by omega) hp hl
  obtain ⟨R⟩:=P5_7_3_5_2.starts m
  have hbranch :=poles F D e W hD0 (hD.trans (by decide :oldAgreement<p)) hd he heP hW hpW hw
    (fun γ hγ=>m.degree γ (hU (hsub hγ)))
  have h:=sheet_count local_test m R (hsub.trans hU) hd.le heP hbranch
  change gap D*F.marks.card ≤
    ((6+2*e+4*e)*gap D+2*e*blockLength+poleFee D e W)*F.h+(4*e*gap D*Q.totalDegree)*F.d at h
  rw [hd] at h
  have hN :gap D*U.card≤((7+6*e)*gap D+2*e*blockLength+poleFee D e W)*H+
      (4*e*gap D*Q.totalDegree)*e := by
    rw [← card_sdiff_add_card_eq_card hsub,Nat.mul_add]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ hexc)
      (h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _))).trans_eq (by ring)
  have hmain:=divide_gap (g:=g) (c:=c) hD he hW hN
  have hbad:=polar_count qGzrWfb.proof hQ.out m.Kw S.onSeed
  have hbadQ:3*((T \ U).card:ℚ)≤(Q.totalDegree :ℚ)*(Q.totalDegree-1 :ℕ) := by
    exact_mod_cast hbad
  have hs : ((Q.totalDegree-1 :ℕ) :ℚ)≤Q.totalDegree := by exact_mod_cast Nat.sub_le Q.totalDegree 1
  have hbad' := hbadQ.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [← card_sdiff_add_card_eq_card hU,Nat.cast_add]
  nlinarith only [hbad',hmain]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :q6hAhQd.c2 := by
  intro b x T J Q e H A he g c W M hok
  have he0:0<e := by omega
  obtain ⟨C,hC,hdeg,⟨S⟩⟩:=sheet A he0
  let:Fact (Irreducible C) :=⟨hC⟩
  have m:=marks (x :=x) A.subset
  have hc:C.totalDegree*e<p:=hdeg ▸ A.seed_lt
  have heP:e<p:=(Nat.le_mul_of_pos_left _ (hdeg ▸ A.plane_pos)).trans_lt hc
  have hD0:0<degree b:= by cases b <;> decide
  have hD:degree b<oldAgreement:= by cases b <;> decide
  rw [slope he0]
  by_cases hw:physicalWeight (degree b) S.root.equation≤W
  · obtain ⟨_,hW,_,_,_,hpW⟩:=hok
    have h:=low_count h2 h3 h4 (g:=g) (c:=c) S m hD0 hD he heP hc hw hW hpW
    rw [hdeg] at h
    have hrest: (0:ℚ)≤8*(e :ℚ)*Q.totalDegree+e := by positivity
    linarith only [h,hrest]
  · obtain ⟨B,hB⟩:=h1 C J T x.M.label x.F.scalar (degree b) e H g c W M S
      hD0 he heP hc hok (lt_of_not_ge hw) m.Kw m.degree
    have h:=Nat.lt_of_mul_lt_mul_left ((high_count B).trans_lt hB)
    have hcard: (T.card:ℚ)≤(highFee e g c:ℕ)*H := by
      exact_mod_cast Nat.le_of_lt_succ h
    have hr : ((highFee e g c:ℕ) :ℚ)≤nativeRate (degree b) e g c W:=le_max_left _ _
    have hrest: (0:ℚ)≤(Q.totalDegree :ℚ)^2/3+(4*(e :ℚ)^2+8*e)*Q.totalDegree+e := by
      positivity
    linarith only [hcard.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg H)),hrest]
end
end qxtWb5a
end
section
set_option autoImplicit true
namespace qr1Ougb
open P6 (p)
open P6_7 (RectTail)
open P6_7_2_3
open qVWQWJa
private theorem cTz (b:RectTail) : (0:ℚ)<gap b:= by cases b <;> decide
private theorem ratio_le (b:RectTail) : (262144 :ℚ)/gap b≤6:= by
  apply (div_le_iff₀ (cTz b)).2
  exact_mod_cast (show 262144≤6*gap b by cases b <;> decide)
private theorem rate_eq (b:RectTail) (e g c W:ℕ) :
    nativeRate (degree b) e g c W=(rateNum (degree b) (gap b) e g c W:ℚ)/gap b:= by
  unfold nativeRate rateNum
  rw [Nat.cast_max,← max_div_div_right (cTz b).le]
  push_cast
  rw [add_div,mul_div_cancel_right₀ _ (cTz b).ne',mul_div_cancel_right₀ _ (cTz b).ne']
private abbrev direct (e :ℕ) :ℚ:=(q:ℚ)/e
private abbrev threshold (d e :ℕ) :ℚ:=(d:ℚ)/510/(3*(e :ℚ))+4*e+8
private theorem native_blend {b:RectTail} {d a h e n:ℕ}
    (he :0<e) (h0:threshold d e≤a) (ha : (a :ℚ)<direct e)
    (hc:Cross (gap b) d a h e n) :
    (n:ℚ)/gap b*(direct e-a)/(direct e-threshold d e)≤h:= by
  have heq : (0:ℚ)<e := by exact_mod_cast he
  have hz : (e :ℚ)*direct e=(q:ℚ) := by
    dsimp only [direct]
    field_simp
  have hL:1530*(e :ℚ)*(direct e-a)=1530*(q:ℚ)-1530*a*e := by
    rw [← hz]
    ring
  have hR:1530*(e :ℚ)*(direct e-threshold d e) =
       1530*(q:ℚ)-((d:ℚ)+1530*e*(4*e+8)) := by
    rw [← hz]
    dsimp only [threshold]
    field_simp
    ring
  have hcQ:1530*(n:ℚ)*q+(h:ℚ)*gap b*((d:ℚ)+1530*(e :ℚ)*(4*e+8)) ≤
      (h:ℚ)*gap b*(1530*(q:ℚ))+1530*(n:ℚ)*a*e := by exact_mod_cast hc
  have h' : (n:ℚ)*(1530*(e :ℚ)*(direct e-a)) ≤
      (h:ℚ)*gap b*(1530*(e :ℚ)*(direct e-threshold d e)) := by
    rw [hL,hR]
    linarith only [hcQ]
  have h'' : (n:ℚ)*(direct e-a)≤(h:ℚ)*gap b*(direct e-threshold d e) := by
    apply (mul_le_mul_iff_right₀ (show 0<1530*(e :ℚ) by positivity)).1
    convert h' using 1 <;> ring
  apply (div_le_iff₀ (sub_pos.mpr (h0.trans_lt ha))).2
  rw [div_mul_eq_mul_div₀]
  exact (div_le_iff₀ (cTz b)).2 (by convert h'' using 1
                                    ring)
private theorem free_of_checks {b:RectTail} {o:Origin} {i:FreeTest} {d a h:ℕ}
    (hproj:freeProjection b o i=(d:ℚ)/510) (hda :d≤510*a) (hh:100≤h)
    (hfloor :38740117≤a) (hap:a<p) (hc:checks b d a h 52=true) :
    FreeOK b o i (a :ℚ) (h:ℚ) := by
  have hA: (38740117:ℚ)≤a := by exact_mod_cast hfloor
  have hH : (100:ℚ)≤h:= by exact_mod_cast hh
  have hdaQ: (d:ℚ)/510≤a := by
    apply (div_le_iff₀ (by norm_num)).2
    rw [mul_comm]
    exact_mod_cast hda
  have hgap:=cTz b
  unfold FreeOK
  rw [hproj]
  refine ⟨by positivity,hdaQ.trans_lt (by exact_mod_cast hap),hdaQ,Nat.cast_nonneg _,?_⟩
  intro e he ha
  change (a :ℚ)<direct e at ha
  have heQ: (0:ℚ)<e := by exact_mod_cast he
  have heN :a*e<q:= by exact_mod_cast (lt_div_iff₀ heQ).1 ha
  have he54 :e≤54 := by
    by_contra! hn
    exact (not_lt_of_ge ((show q≤38740117*55 by decide).trans (Nat.mul_le_mul hfloor hn))) heN
  unfold BlendOK
  rw [min_self]
  by_cases h1 :e=1
  · subst e
    right
    left
    refine ⟨rfl,?_⟩
    change (1-(a :ℚ)/direct 1)*(1+3*262144/gap b)≤h
    have hx :1-(a :ℚ)/direct 1≤1 :=
      sub_le_self _ (div_nonneg (by positivity) (by positivity))
    refine (mul_le_of_le_one_left (by positivity) hx).trans ?_
    rw [mul_div_assoc]
    linarith only [ratio_le b,hH]
  by_cases h2 :e=2
  · subst e
    right
    right
    left
    have MV: (16:ℚ)≤a := by linarith only [hA]
    refine ⟨rfl,MV,?_⟩
    change (13+8*262144/gap b)*(direct 2-a)/(direct 2-16)≤h
    have hx : (direct 2-a)/(direct 2-16)≤1 :=
      (div_le_one (sub_pos.mpr (MV.trans_lt ha))).2 (sub_le_sub_left MV _)
    rw [mul_div_assoc]
    refine (mul_le_of_le_one_right (by positivity) hx).trans ?_
    rw [mul_div_assoc]
    linarith only [ratio_le b,hH]
  have he3:3≤e := by omega
  let t:Fin 52 :=⟨e-3,by omega⟩
  have ht:t.val+3=e :=Nat.sub_add_cancel he3
  have hprice :=cross_of_checks t.isLt hc (by rw [ht]; exact heN)
  change Cross (gap b) d a h (t.val+3)
    (rateNum (degree b) (gap b) (t.val+3) (extra b t.val) (param t.val) (width b t.val)) at hprice
  have hw:=witness b t
  rw [ht] at hw hprice
  have h0:threshold d e≤a := by
    have he1Q: (1 :ℚ)≤e := by exact_mod_cast he
    have he54Q: (e :ℚ)≤54 := by exact_mod_cast he54
    have hx : (d:ℚ)/510/(3*(e :ℚ))≤(a :ℚ)/3 :=
      (div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by linarith only [he1Q])).trans (div_le_div_of_nonneg_right hdaQ (by norm_num))
    dsimp only [threshold]
    linarith only [hx,he54Q,hA]
  right
  right
  right
  refine ⟨he3,extra b t.val,param t.val,width b t.val,_,hw,h0,?_⟩
  change nativeRate (degree b) e (extra b t.val) (param t.val) (width b t.val) *
    (direct e-a)/(direct e-threshold d e)≤h
  rw [rate_eq]
  exact native_blend (b:=b) he h0 ha hprice
theorem proof :qVWQWJa.c1 := by
  intro b o i
  obtain ⟨hda,hh,hc⟩:=checked b o i
  refine free_of_checks (projection_eq b o i) hda hh (Nat.le_add_right _ _) ?_ hc
  unfold freeSeedN
  exact (Nat.add_lt_add_left (Nat.mod_lt _ (by decide :0<2^24)) _).trans (by decide)
end qr1Ougb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qpzrJre
private theorem t0:qJOpoVa.c1 :=qcYA6zd.proof
private theorem t1 :qJOpoVa.c2 :=qWbWDnc.proof
private theorem t2 :qhFwyvc.c1 :=P5_7_1_7Q4332.proof1
private theorem t3:qhFwyvc.c2 :=P5_7_1_7Q4332.proof
private theorem t4 :qoCymac.c2 :=qhFwyvc.of_children t2 t3
private theorem t5:qoCymac.c4 :=q6hv5Ed.proof
private theorem t6:qoCymac.c6:=qIGP9Qa.proof
private theorem t7:qJOpoVa.c3:=qG0wqGe.of_children t4 t5 t6
private theorem t8:qT2dl0a.c1 :=qMskYpa.proof
private theorem t9:qEAs6me.c1 :=qLXGHAd.proof
private theorem t10 :qEAs6me.c2 :=qDTrBfa.proof
private theorem t11 :qVAMdHe.c1 :=qxwYnxa.proof
private theorem t12 :qVAMdHe.c2 :=qirQQEe.proof
private theorem t13:qEAs6me.c3:=qVAMdHe.of_children t11 t12
private theorem t14 :q2tSkEc.c1 :=qEAs6me.of_children t9 t10 t13
private theorem t15:q7P6kQb.c1 :=qgDJA5b.proof
private theorem t16:q7P6kQb.c2 :=qloRzZa.proof
private theorem t17:q7P6kQb.c3:=qg1w8ra.proof
private theorem t18:q7P6kQb.c4 :=qxqqTXa.proof
private theorem t19:q2tSkEc.c2 :=q7P6kQb.of_children t15 t16 t17 t18
private theorem t20:qJOpoVa.c5:=q2tSkEc.of_children t14 t19
private theorem t21 :qJOpoVa.c6:=q9r9FBa.proof
theorem proof :qDxaYpa.c7:=qT2dl0a.of_children t0 t1 t7 t8 t20 t21
end qpzrJre
end
