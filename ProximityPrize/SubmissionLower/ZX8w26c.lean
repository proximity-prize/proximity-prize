import ProximityPrize.SubmissionLower.ZwO1rQb
import ProximityPrize.SubmissionLower.Z3swOYa
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qYdH9sc
noncomputable section
open Finset Polynomial
open scoped Classical BigOperators
open P5 (K p blockLength)

open q7F2qKe (Input wX weakAgreement)
open qxRSHvb (nativeSlope)
open qK3TPae (AmplifiedCut regular polar_count)
open quN7Z4a (Sheet physicalWeight)
open qkgz7gb (UJ)
open qb0hmCe (CurveModel)
open gT (kM)
open Cu (sQ)



open private sheet_count from ProximityPrize.SubmissionLower.ZlPdtnc
open private word_from_window from ProximityPrize.SubmissionLower.ZwO1rQb
open private OF.distinct OF.degree OF.lg from ProximityPrize.SubmissionLower.ZogIzOe


open private height_guard from ProximityPrize.SubmissionLower.ZQmiAIb
def c1 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (D g H extra c W M:ℕ)
    (S:Sheet Q J g H T z s),3≤g→ g<p→FilterOK D g extra c W M →
    W<physicalWeight D S.root.equation→Set.InjOn z (T:Set K) →
    (∀ γ∈T,(s γ).natDegree≤D) →
    ∃ B:AmplifiedCut T,
      B.ng.sum (fun _ n=>n)<p^B.order*((g*(c+1)+(g+extra))*H+1)
def c2 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (D g H W:ℕ)
    (S:Sheet Q J g H T z s),Set.InjOn z (T:Set K)→0<g→Q.totalDegree*g<p →
    physicalWeight D S.root.equation≤W →
    ∃ (C:CurveModel Q) (F:P5_7_3_5_2.Sheet C z s),
      F.d=g∧F.h≤H∧F.weight D W∧F.marks⊆regular Q z T ∧
      ((regular Q z T) \ F.marks).card≤H
def c3:Prop :=P5_7_3_5_2.c2
def c4 :Prop :=
  ∀ {Q:sQ} {C:CurveModel Q} {z :K→K} {s :K→K[X]}
    (F:P5_7_3_5_2.Sheet C z s) (D g W:ℕ),
    F.d=g→3≤g→ g<p→ g*D ≤W→polarDegree D g W<p→F.weight D W →
    (∀ γ∈F.marks,(s γ).natDegree≤D) →
    P5_7_3_5_2.BranchBudget F D (6+2*g) (poleFee D g W)
def c5:Prop :=q7YMR4d.c3
private theorem marks {b u del M Γ F} (x : @Input b u del M Γ F) {T:Finset K}
  (hT:T⊆Γ) :UJ (wX b) M.word T M.label F.scalar := by
 have hw:=word_from_window F x.vo hT
 refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,OF.distinct hw,OF.degree hw,OF.lg hw,
  M.iF.toNat,?_,x.D,fun γ hγ=>x.residues γ (hT hγ)⟩
 have hh:=x.vo.1
 have hp:=(height_guard b).1
 omega
private theorem slope {g:ℕ} (hg:0<g) (d:ℕ) :
  nativeSlope d g false*((g:ℚ)*d)=(d:ℚ)^2/3+(4*(g:ℚ)^2+8*g)*d:= by
 have hgq: (g:ℚ)≠0:=Nat.cast_ne_zero.mpr hg.ne'
 simp only [nativeSlope,Bool.false_eq_true,ite_false,add_zero]
 field_simp
 ring
private theorem divide_gap {D g W t H d:ℕ} {v :ℚ} (hD:D <weakAgreement)
    (hv :7+6*(g:ℚ)+((2*g+1)*blockLength+poleFee D g W:ℕ)/(weakAgreement-D:ℕ)≤v)
    (h: (weakAgreement-D)*t ≤
      ((7+6*g)*(weakAgreement-D)+2*g*blockLength+poleFee D g W)*H+
        (4*g*(weakAgreement-D)*d)*g) :
    (t:ℚ)≤v*H+4*(g:ℚ)^2*d:= by
  let G:=weakAgreement-D
  let n:=2*g*blockLength+poleFee D g W
  have hG: (0:ℚ)<G:=Nat.cast_pos.mpr (Nat.sub_pos_of_lt hD)
  have h' : (G:ℚ)*t≤(((7+6*g:ℕ) :ℚ)*G+n)*H+(4*(g:ℚ)*G*d)*g:= by
    exact_mod_cast (show G*t≤((7+6*g)*G+n)*H+(4*g*G*d)*g from by
      simpa only [G,n,add_assoc] using h)
  have h'' : (t:ℚ)≤(7+6*(g:ℚ)+(n:ℚ)/G)*H+4*(g:ℚ)^2*d:= by
    apply le_of_mul_le_mul_left _ hG
    refine h'.trans_eq ?_
    push_cast
    field_simp [hG.ne']
  have hn:n≤(2*g+1)*blockLength+poleFee D g W:= by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have hr :7+6*(g:ℚ)+(n:ℚ)/G≤v :=
    (add_le_add le_rfl (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn) hG.le)).trans hv
  exact h''.trans (add_le_add (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) le_rfl)
private theorem low_count (prep:c2) (local_test :c3) (poles :c4) (polar :c5)
   {Q:sQ} [hQ:Fact (Irreducible Q)] {J:Ideal kM} {T:Finset K}
   {z s w D g H W v} (S:Sheet Q J g H T z s) (m:UJ D w T z s)
   (hD:D <weakAgreement) (hg:3≤g) (hgP:g<p) (hp:Q.totalDegree*g<p)
   (hl:physicalWeight D S.root.equation≤W) (hW:g*D ≤W) (hpW:polarDegree D g W<p)
   (hv :7+6*(g:ℚ)+((2*g+1)*blockLength+poleFee D g W:ℕ)/(weakAgreement-D:ℕ)≤v) :
   (T.card:ℚ)≤v*H+4*(g:ℚ)^2*Q.totalDegree+(Q.totalDegree :ℚ)^2/3:= by
 let U:=regular Q z T
 have hU:U⊆T:=filter_subset _ _
 obtain ⟨C,F,hd,hh,hw,hsub,hexc⟩:=prep Q J T z s D g H W S m.Kw (by omega) hp hl
 obtain ⟨R⟩:=P5_7_3_5_2.starts m
 have hb:=poles F D g W hd hg hgP hW hpW hw (fun γ hγ=>m.degree γ (hU (hsub hγ)))
 have h:=sheet_count local_test m R (hsub.trans hU) hd.le hgP hb
 let G:=weakAgreement-D
 change G*F.marks.card≤((6+2*g+4*g)*G+2*g*blockLength+poleFee D g W)*F.h+
   (4*g*G*Q.totalDegree)*F.d at h
 rw [hd] at h
 have hn:G*U.card≤((7+6*g)*G+2*g*blockLength+poleFee D g W)*H+
     (4*g*G*Q.totalDegree)*g:= by
   rw [← card_sdiff_add_card_eq_card hsub,Nat.mul_add]
   exact (Nat.add_le_add (Nat.mul_le_mul_left _ hexc)
     (h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _))).trans_eq (by ring)
 have hmain:=divide_gap hD hv hn
 have hbad:=polar_count polar hQ.out m.Kw S.onSeed
 have hbadQ:3*((T \ U).card:ℚ)≤(Q.totalDegree :ℚ)*(Q.totalDegree-1 :ℕ) := by
   exact_mod_cast hbad
 have hs : ((Q.totalDegree-1 :ℕ) :ℚ)≤Q.totalDegree :=Nat.cast_le.mpr (Nat.sub_le _ _)
 have hbad' := hbadQ.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
 rw [← card_sdiff_add_card_eq_card hU,Nat.cast_add]
 nlinarith only [hbad',hmain]
end
end qYdH9sc
