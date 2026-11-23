import ProximityPrize.SubmissionLower.ZKfhfIb
import ProximityPrize.SubmissionLower.ZVbskte
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qpDASwe
noncomputable section
open Finset Polynomial
open P6 (K p dw blockLength)
open P5_7 (midAgreement)
open P6_7_3 (degree)
open qUrGXob (gap)
open qY7abfd (quadraticRate)
open qrsE1ie (discriminant geomSquare)
open quN7Z4a (OF sheet physicalWeight compressionWidth)
open gT (aQ abX)
open private degree_le from ProximityPrize.SubmissionLower.ZZ5hHja
open private disc_degree from ProximityPrize.SubmissionLower.ZcErkXc
open private chart_part from ProximityPrize.SubmissionLower.ZVbskte
def c1 :Prop :=qrsE1ie.c1
def c2 :Prop :=qrsE1ie.c2
theorem of_children (h1 :c1) (h2 :c2) :qY7abfd.c1 := by
  intro x _ T J Q H A
  have hrank : ∃ d:ℕ,Module.finrank aQ (abX J)=d*2 := by
    obtain ⟨_,C₀,_,_,_,h,_,_⟩:=A.curve
    exact ⟨C₀.totalDegree,h⟩
  obtain ⟨d,hd⟩:=hrank
  obtain ⟨C₀,hC₀,_,⟨S⟩⟩:=sheet (by decide :0<2) A.curve hd A.marks
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  have hz :Set.InjOn x.M.label (T:Set K) := fun _ _ _ _ h=>sub_left_inj.mp h
  have W:OF T x.F.scalar x.M.word degree := by
    refine ⟨x.F.distinct.mono A.subset,fun γ hγ=>degree_le x (A.subset hγ),?_⟩
    intro γ hγ
    let m:=x.F.mark γ (A.subset hγ)
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,
      m.scalar_hits⟩
  have hH : (0:ℚ)≤H :=Nat.cast_nonneg _
  have hρ: (0:ℚ)≤(blockLength:ℚ)/gap:= by positivity
  have hcount: (T.card:ℚ)≤(11+3*(blockLength:ℚ)/gap)*H+1 := by
    have small (hc:T.card≤11*H) : (T.card:ℚ)≤(11+3*(blockLength:ℚ)/gap)*H+1 := by
      have hc' : (T.card:ℚ)≤11*H := by exact_mod_cast hc
      rw [mul_div_assoc]
      linarith only [hc',mul_nonneg (mul_nonneg (by norm_num : (0:ℚ)≤3) hρ) hH]
    by_cases hw:compressionWidth degree 2≤physicalWeight degree S.root.equation
    · have hc:=h1 C₀ J T x.M.label x.F.scalar degree H S (by decide) hw hz W.degree
      exact small (hc.trans (Nat.mul_le_mul_right H (by decide)))
    by_cases hs :geomSquare S.root.equation
    · have hc:=qRoCwuc.dO2 S hz W (by decide) (chart_part S hs)
      have hc' : (T.card:ℚ)≤3*(blockLength:ℚ)/gap*H+1 :=hc
      linarith only [hc',hH]
    have hdeg: (discriminant S.root.equation).natDegree<p :=
      (disc_degree degree S.root.equation).trans_lt
        ((Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hw) (by decide)).trans
          (by decide :2*compressionWidth degree 2<p))
    exact small (h2 C₀ J T x.M.label x.F.scalar H S hdeg hs hz)
  have hr :11+3*(blockLength:ℚ)/gap≤quadraticRate := by
    unfold quadraticRate
    simp only [mul_div_assoc]
    linarith only [hρ]
  have hm: (0:ℚ)≤16*(2*(Q.totalDegree :ℚ)) := by positivity
  linarith only [hcount,mul_le_mul_of_nonneg_right hr hH,hm]
end
end qpDASwe
end
section
set_option autoImplicit true
namespace qvCjzac
open P6_7_3 (degree)
def polarDegree (e W:ℕ) :ℕ:=(2*e-1)*W-e*e*degree
def poleFee (e W:ℕ) :ℕ:=(6*e-2)*W-3*e*e*degree
end qvCjzac
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qvCjzac
noncomputable section
open Polynomial MvPolynomial
open P6 (K dw)
open P5_7 (midAgreement)
open P6_7_3 (Input Poles degree)
open qY7abfd (DescendedMarks)
open gT (kM abX aQ)
open Cu (sQ)
open YY (bnQ)
open private b1I from ProximityPrize.SubmissionLower.G
open private degree_le from ProximityPrize.SubmissionLower.ZZ5hHja
theorem sheet {x :Input} {T:Finset K} {J:Ideal kM} {Q e H}
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
theorem marks {x :Input} (P:Poles x) {T:Finset K} (hT:T⊆x.Γ) :
    qkgz7gb.UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
    fun γ hγ=>degree_le x (hT hγ),?_,?_⟩
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,
      m.scalar_hits⟩
  · refine ⟨x.h,?_,P.D,fun γ hγ=>P.marks γ (hT hγ)⟩
    have h:=x.kA.1
    change (2407:ℤ)≤x.M.iF at h
    change 0<x.M.iF.toNat
    omega
end
end qvCjzac
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qvCjzac
noncomputable section
open Finset Polynomial
open P6 (K p blockLength)
open P6_7_3 (degree)
open qUrGXob (NativeOK nativeRate gap)
open qY7abfd (nativeSlope)
open qK3TPae (AmplifiedCut highFee regular high_count polar_count)
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
    3≤e→e<p→NativeOK e g c W M →
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
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qY7abfd.c2 := by
  intro x P T J Q e H g c W M A he _ hok
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
      he heP hok (lt_of_not_ge hw) m.Kw m.degree
    have h:=Nat.lt_of_mul_lt_mul_left ((high_count B).trans_lt hB)
    have hcard: (T.card:ℚ)≤(highFee e g c:ℕ)*H := by
      exact_mod_cast Nat.le_of_lt_succ h
    have hr : ((highFee e g c:ℕ) :ℚ)≤nativeRate e g c W:=le_max_left _ _
    have hrest: (0:ℚ)≤(Q.totalDegree :ℚ)^2/3+(4*(e :ℚ)^2+8*e)*Q.totalDegree+e := by
      positivity
    linarith only [hcard.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg H)),hrest]
end
end qvCjzac
end
