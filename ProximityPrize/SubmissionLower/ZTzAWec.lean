import ProximityPrize.SubmissionLower.ZEXyWMe
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZLt6kU
set_option Elab.async false
open _root_ renaming Module.finrank→lV,Nat.le_of_lt_succ→mD,Nat.mul_le_mul_left→lJ,P5_7.midAgreement→aU,P5_7_3.terminal→cy,P5_7_3.threshold→c9,Polynomial.coeff_natDegree→lI,cu.Equation→lz
section
set_option autoImplicit true
namespace P5_7_3
noncomputable section
open Finset Polynomial MvPolynomial

open Dt (Bank)
open cu (Shape ku vP FX Jet slots triangle vm)
open qQ (oU)
open Qt (aH3 gY bg4)
open baY (Bp)
open private bKE from ProximityPrize.SubmissionLower.D8
open private cer cTX from ProximityPrize.SubmissionLower.D8
open private ddI from ProximityPrize.SubmissionLower.A1
open private bGH Wb from ProximityPrize.SubmissionLower.A0
structure bAN (h:ℕ) (t:Bank) (rows :vP) (f :lz) :Prop where
 ajB:bbk h t rows
 shape : ∀ W,∀ P∈rows t.shape W,oU P t.shape
 leading:qQ.aSa h rows t.shape
 divides : ∀ W<t.shape.m*aU,∀ P∈rows t.shape W,P≠0 →
  f^(ahs h t.shape W-P.natDegree)∣P.leadingCoeff
private def aT2 (h:ℕ) (s :Shape) (E v W:ℕ) :ℕ :=
 ku s fun q j =>
   if q*(131071-h)≤W+j then
     Bp s.U v ((q-j)/E) (ahs h s W - j)
   else 0
private def b4O (h:ℕ) (s :Shape) (E v W j:ℕ) :ℕ :=
 let r :=ahs h s W - j
 (aH3 (131071-h) s.B W j - r*E)*slots s.U (r*v)
private theorem cJb (h:ℕ) (s :Shape) (E v W:ℕ)
  (hk :0<131071-h) (he :0<E) :
  (∑ j∈range (s.J+1),b4O h s E v W j)=aT2 h s E v W:= by
 rw [aT2,← ddI]
 apply sum_congr rfl
 intro j _
 exact cTX _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
private theorem boi (h:ℕ) (s :Shape) (E v W:ℕ) (V:Submodule FX Jet)
    {f :lz} (hf :f≠0) (hE :E≤f.natDegree) (hv :v≤gY f)
    (hk :0<131071-h) (he :0<E)
    (hcaps : ∀ P∈V,oU P s)
    (hlead : ∀ P∈V,P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈V,P≠0→f^(ahs h s W-P.natDegree)∣P.leadingCoeff) :
    lV FX V≤aT2 h s E v W:= by
  have hrow {P:Jet} (hP:P∈V) (hn:P≠0) :
      P.leadingCoeff.natDegree+P.natDegree≤ s.B∧P.natDegree≤ s.J ∧
      vm P.leadingCoeff s.U:= by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree≠0:= by
      rw [lI,lI]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB,hJ,_⟩:=hcaps P hP _ _ ha
    refine ⟨hB,hJ,fun i => ?_⟩
    by_cases hi:P.leadingCoeff.coeff i=0
    · simp [hi]
    · rw [← lI] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cJb h s E v W hk he]
  refine bGH (F:=FX) (A:=lz) V (b4O h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r :=ahs h s W - j
    apply cer _ (g:=f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact lJ _ hE
    · rw [bg4 hf]
      exact lJ _ hv
    · rintro c ⟨⟨P,hP⟩,rfl⟩ hc
      change P.coeff j≠0 at hc
      obtain ⟨hpV,hd⟩:=Wb.mp hP
      have hn:P≠0:= by
        intro hz
        exact hc (by simp [hz])
      have hj:P.natDegree=j :=
        le_antisymm (mD ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB,_,hseed⟩:=hrow hpV hn
      have hwidth :=hlead P hpV hn
      have hdiv :=hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree<_∧vm (P.coeff j) _∧_∣P.coeff j
      rw [← hj,lI,hj]
      refine ⟨?_,hseed,hdiv⟩
      have hd:=(Nat.le_div_iff_mul_le hk).2 hwidth
      unfold aH3
      omega
  · intro P hp
    by_cases hn:P=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
private theorem bDM (h:ℕ) (s :Shape) (E v :ℕ) (hh:0<2*h) (hk :1≤131071-h) :
    (∑ W∈range (s.m*aU),aT2 h s E v W)+ZN h s E v =
      triangle s.U*ku s (fun q j=>s.m*aU +j-q*(131071-h)) := by
  have hswap (F:ℕ→ℕ→ℕ→ℕ) :
      (∑ W∈range (s.m*aU),ku s (F W)) =
        ku s (fun q j => ∑ W∈range (s.m*aU),F W q j) := by
    unfold ku
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [aT2,ZN]
  rw [hswap]
  simp only [ku,← sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq:j≤q:=(mD (mem_range.mp hj)).trans (min_le_left _ _)
  have hq:q≤q*(131071-h) := by simpa using lJ q hk
  exact bKE (s.m*aU) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
theorem eqx {b:fO} {h:ℕ} (hh:0<2*h) (hk :0<131071-h)
   (x :Test b) {rows f} (hf :f≠0) (ht:bAN h (Lc b x) rows f)
   (htop:0<(Lc b x).shape.m*aU)
   (hwidth : (Lc b x).shape.B*(131071-h)≤(Lc b x).shape.m*aU)
   (hE :c9 b x≤f.natDegree) (hv :apo b x≤gY f) :
   ZN h (Lc b x).shape (c9 b x) (apo b x)≤j3 h (Lc b x) := by
 have he :0<c9 b x := by cases x <;> exact Nat.succ_pos _
 let t:=Lc b x
 let top:=t.shape.m*aU
 have htopPos :0<top:=htop
 have hbWidth:t.shape.B*(131071-h)≤top:=hwidth
 have htopSub:top-1+1=top:= by omega
 have hraw : ∀ q≤t.shape.B,∀ j≤ min q t.shape.J,
     q*(131071-h)≤top-1+1+j:= by
   intro q hq j _
   rw [htopSub]
   exact (Nat.mul_le_mul_right _ hq).trans (hbWidth.trans (by omega :top≤top+j))
 have hmin:=ht.ajB (top-1) (show top-1<top by omega) hraw
 change triangle t.shape.U*ku t.shape (fun q j=>top-1+1+j-q*(131071-h)) ≤
   j3 h t + ∑ W∈range (top-1+1),lV FX (rows t.shape W) at hmin
 rw [htopSub] at hmin
 have hmax : (∑ W∈range top,lV FX (rows t.shape W)) ≤
     ∑ W∈range top,aT2 h t.shape (c9 b x) (apo b x) W:= by
   apply sum_le_sum
   intro W hW
   exact boi h t.shape _ _ W _ hf hE hv hk he
     (ht.shape W) (ht.leading W) (ht.divides W (mem_range.mp hW))
 have htotal:=bDM h t.shape (c9 b x) (apo b x) hh hk
 change (∑ W∈range top,aT2 h t.shape (c9 b x) (apo b x) W) +
   ZN h t.shape (c9 b x) (apo b x) =
   triangle t.shape.U*ku t.shape (fun q j=>top+j-q*(131071-h)) at htotal
 change ZN h t.shape (c9 b x) (apo b x)≤j3 h t
 omega
end
end P5_7_3
end
section
set_option autoImplicit true
namespace P5_7_3
noncomputable section
open Polynomial
open P5 (p)
open P5_7 (midAgreement Qn)
open cu (vm)

open Qt (gY Qc)
theorem awI (b:fO) :
  0<b.jX.lo∧b.jX.hi<131071 ∧
  0<(cy b).shape.m*aU∧(cy b).shape.m*aU<p ∧
  (cy b).shape.B*(131071-b.jX.lo)≤(cy b).shape.m*midAgreement:= by
 cases b <;> exact ⟨by decide,by decide,by decide,by decide,by decide⟩
theorem schedule_paid (b:fO) :
  prefixFee b+b.schedule.retainedFee≤b.jX.cap:= by
 cases b <;> decide
private theorem all_slots (b:fO) :
  b.schedule.gw.all (fun g=>decide (g.slots≤(cy b).shape.U))=true := by
 cases b <;> rfl
private theorem grade_slots (b:fO) (i:aKj b) :
  (cV b i).slots≤(cy b).shape.U :=
 of_decide_eq_true (List.all_eq_true.mp (all_slots b) _ (List.get_mem _ _))
theorem aRe {b:fO} {w:ℤ} (hw:Qn b.jX.lo b.jX.hi w) :
  b.jX.lo≤w.toNat∧w.toNat≤b.jX.hi:= by
 obtain ⟨hl,hh⟩:=hw
 omega
theorem ctc (b:fO) (x :Test b) :
   Jr b (Lc b x)∧(Lc b x).shape.m=(cy b).shape.m ∧
   (Lc b x).shape.B=(cy b).shape.B∧(Lc b x).shape.J=(cy b).shape.J ∧
   (Lc b x).shape.U≤(cy b).shape.U:= by
 cases x with
 | none=>exact ⟨Or.inl rfl,rfl,rfl,rfl,le_rfl⟩
 | some i=>exact ⟨Or.inr (Or.inr ⟨i,rfl⟩),rfl,rfl,rfl,grade_slots b i⟩
theorem eiO {b:fO} {f :lz} (hp:0<f.natDegree)
   (reject : ∀ x :Test b,c9 b x≤f.natDegree →
     apo b x≤gY f→False) :
   ∃ i:aKj b,f.natDegree=i.val+1∧vm f (cV b i).seedCap:= by
 have he :f.natDegree≤b.schedule.gw.length:= by
   by_contra! hlo
   exact reject none hlo (Nat.zero_le _)
 let i:aKj b:=⟨f.natDegree-1,by omega⟩
 have hidx :f.natDegree=i.val+1 := by dsimp [i]; omega
 refine ⟨i,hidx,(Qc _ _).mp ?_⟩
 by_contra! hlow
 exact reject (some i) hidx.ge hlow
end
end P5_7_3
end
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def r0:=p2! 499 110 0x6868d4c8 30 3 0x227d6ffec101986b3cf768
private def r1 :=p2! 501 105 0x6605202d 30 3 0x1fab3fce5fc8d0ea8b48ee
private def r2 :=p2! 503 104 0x66910d8b 30 3 0x20c8a40e7a257d6a9bed56
private def r3:=p2! 504 105 0x67fdf705 30 3 0x22dea2ceb761c8eaf285b6
private def r4 :=p2! 518 107 0x7337bf16 31 3 0xde2cb6e13fbb252d3f95f1
private def r5:=p2! 547 109 0x8b2f878c 31 3 0x1d48e97e91df0c531a16ba3
private def r6:=p2! 561 117 0x9f7e6a06 31 3 0x2ce933c6f7f408e35459bf9
private def r7:=p2! 561 127 0xa9f0ad78 31 3 0x34f1aa2f2c756a6b72595a0
private def r8:=p2! 577 119 0xb0dd09c5 31 3 0x3dbb3a274bc352f37f5d0de
private def r9:=p2! 585 122 0xbc76fd56 31 3 0x49a9689b82a2b28b9b84cdf
private def dz :=p2! 595 135 0xd73aa42f 32 3 0x19946c258012e0883d935782
private def dD:=p2! 596 137 0xdadbae42 32 3 0x1a9e036882300e6c3e0d9c6e
private def dK:=p2! 599 125 0xcf326828 31 3 0x5f478757d82e06a3c5ac57f
private def e8:=p2! 609 126 0xdbdb80dc 32 3 0x1be153f381f54fab3e04dd3e
private def gD:=p2! 617 127 0xe6abc278 32 3 0x1f86c18e87bfb74a3f6549a0
private def gx :=p2! 621 139 0xfc954e46 32 3 0x26319a5f9434030a422fb0dd
private def iu:=p2! 624 129 0xf2194452 32 3 0x236ea8ba8dd690b840d40ae0
private def kD:=p2! 635 132 0x104ae87f3 32 3 0x2a260c30977aff9a430d7c29
private def lH :=p2! 675 140 0x14bfd4f36 32 4 0x5ebfb047826457b97de1804a9e49af
private def kR:=p2! 712 162 0x1b9460150 32 4 0x4171f5076f18660ea636b8053d9f020
private def jV:=p2! 716 148 0x1a2e2d039 32 4 0x31773f06f1994b2de4f04005262c397
private def lp:=p2! 716 149 0x1a51710d6 32 4 0x32f7da06fed7eb9df6b8e80528e85fd
private def kZ:=p2! 735 168 0x1f6b4426b 33 4 0x43f234424e78d0f604987100584b8f26
private def lQ:=p2! 808 168 0x2a987d61f 33 4 0x1034eb90ba88fbd5275bb7a00641c52aa
private def nJ:=p2! 812 169 0x2b7a17d6d 33 4 0x116dd204bc25bd07a7e953f0064e445c6
private def nP:=p2! 820 170 0x2d12dd3e6 33 4 0x13cddf093f18cdd0a8db98f0066521712
private def qA:=p2! 833 171 0x2f9feec82 33 4 0x17f08b05c3c9aef8aa4ce1e0068900b95
def dataB:Array aqm := #[
 r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,dz,dD,dK,e8,gD,gx,iu,kD,lH,kR,jV,lp,kZ,lQ,
 nJ,nP,qA
]
end qpECY2d
end
