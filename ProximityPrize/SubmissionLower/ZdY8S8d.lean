import ProximityPrize.SubmissionLower.Zqby9gc
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxSynthPendingDepth 8
namespace qdY8S8d
noncomputable section
open K1 (I p)
open cu (FX L Jet Shape triangle ku)
open DP (jF zG VY d3q d3r bga)
open gT (alm)
open aBa (cNB)
open qQ (aeH)
open Finset Polynomial
open private cSB from ProximityPrize.SubmissionLower.T
open private eHt from ProximityPrize.SubmissionLower.ZhDU57c
open private c4y from ProximityPrize.SubmissionLower.Zq1cNdd
open private eligible boi bDM from ProximityPrize.SubmissionLower.D6
def gainAt (h N :ℕ) (s :Shape) (mode :ℕ) :ℕ :=
  triangle s.U*ku s (fun q j=>N+j-q*(131071-h)-mode*(2*h*j))
structure Test (h N :ℕ) (s :Shape) (e mode :ℕ) :Prop where
  jet:s.J≤ s.B
  seed :s.B≤ s.U
  char :s.B<p
  pole :P5_7_4.poleRank s≤triangle s.U*agU.arY s+e
  width :s.B*(131071-h)<N
  strict :bga s+2*h*e<gainAt h N s mode
theorem ofTests {h:ℕ} {b:qxWWUna.Bank} {mode :ℕ} (t:qxWWUna.Tests h b mode) :
    Test h (qxWWUna.count h b) b.shape b.DG mode :=
  ⟨t.jet,t.seed,t.char,t.pole,t.width,t.strict⟩
variable {h:ℕ} {D:jF h} (crt:zG D) (word:I→L)
private theorem bwO (hpos :0<h) (hhi:h≤131070) {N :ℕ} {s :Shape} {e mode :ℕ}
    (t:Test h N s e mode) :
    gainAt h N s 0≤bga s+2*h*e + ∑ W∈range N,Module.finrank FX (VY crt word s W) := by
  have hw:N-1+1=N := by have :=t.width; omega
  have ha :=atp.bT9 (hhi.trans (by decide)) s (N-1)
    (fun q hq j _=> by
      rw [hw]
      exact (Nat.mul_le_mul_right _ hq).trans (t.width.le.trans (Nat.le_add_right _ _)))
  have hc:=atp.Yw h word s (N-1)
  have ht:=agU.telescope hhi crt word s (N-1)
  have hg:=c4y (qQCEOid.of_children qcsMxUc.proof qCgnalc.proof)
    hpos (hhi.trans_lt (by decide)) crt word s t.jet t.seed t.char (N-1)
  have hp:=Nat.mul_le_mul_left (2*h) t.pole
  rw [Nat.mul_add,show 2*h*(triangle s.U*agU.arY s) =
      DP.azS h s by unfold agU.arY DP.azS; ac_rfl] at hp
  unfold DP.ceG at ha
  rw [hw] at ha ht
  unfold gainAt
  simp only [zero_mul,Nat.sub_zero]
  omega
theorem bVl (hpos :0<h) (hhi:h≤131070) {N :ℕ} {s :Shape} {e mode :ℕ}
    (t:Test h N s e mode) : ∃ Q∈VY crt word s (N-1),Q≠0:= by
  by_contra! hz
  have hf :=bwO crt word hpos hhi t
  have hs :bga s+2*h*e<gainAt h N s 0:=t.strict.trans_le (by
    unfold gainAt ku
    simp only [zero_mul,Nat.sub_zero]
    exact Nat.mul_le_mul_left _ (sum_le_sum fun _ _=>sum_le_sum fun _ _=>Nat.sub_le _ _))
  have he : (∑ W∈range N,Module.finrank FX (VY crt word s W))=0:= by
    apply sum_eq_zero
    intro W hW
    have hbot:VY crt word s W = ⊥ := by
      apply bot_unique
      intro Q hQ
      exact (Submodule.mem_bot FX).mpr
        (hz Q (d3q crt word rfl rfl rfl le_rfl
          (Nat.le_sub_one_of_lt (mem_range.mp hW)) hQ))
    rw [hbot,finrank_bot]
  omega
theorem cCz (hpos :0<h) (hhi:h≤131070) {N :ℕ} {s :Shape} {e :ℕ}
    (t:Test h N s e 1) {G Q:Jet} (hg:Irreducible G) (hv :0<G.natDegree) (hm:alm G)
    (hq:Q≠0) (hd:G∣Q) {U:ℕ} (hp:U<p)
    (hseed : ∀ j i,((Q.coeff j).coeff i).totalDegree≤U) :
    ∃ R∈VY crt word s (N-1),¬ G∣R:= by
  by_contra! hcommon
  have hsum: (∑ W∈range N,Module.finrank FX (VY crt word s W)) ≤
      triangle s.U*(∑ W∈range N,ku s (fun q j =>
        if eligible h N W q j then 1 else 0)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro W hW
    apply boi
    · exact fun Q hQ=>d3r crt word hQ
    · exact atp.eu5 hpos hhi crt word s W
    · intro R hR hn
      apply eHt h N W hpos (mem_range.mp hW) hg hv hm hq hd hp hseed hn
      intro i a ha
      exact hcommon _ (d3q crt word rfl rfl rfl le_rfl ha
        (atp.d3s crt word hR i a))
  have hk :1≤131071-h:= by omega
  have he :=congrArg (triangle s.U * ·) (bDM s h N hk)
  rw [Nat.mul_add] at he
  have hu: (∑ W∈range N,Module.finrank FX (VY crt word s W))+gainAt h N s 1 ≤
      gainAt h N s 0:= by
    unfold gainAt
    simp only [one_mul,zero_mul,Nat.sub_zero]
    exact (Nat.add_le_add_right hsum _).trans_eq he
  have hf :=bwO crt word hpos hhi t
  have hs :=t.strict
  omega
theorem pick_pair (hpos :0<h) (hhi:h≤131070) {N M:ℕ} {s r :Shape} {e f :ℕ}
    (tf :Test h N s e 0) (tm:Test h M r f 1) (hp:s.U<p) :
    ∃ Q R:Jet,Q∈VY crt word s (N-1)∧R∈VY crt word r (M-1) ∧
      Q≠0∧R≠0∧aeH Q R:= by
  obtain ⟨Q,hQ,hn⟩:=bVl crt word hpos hhi tf
  have hseed (j k :ℕ) : ((Q.coeff j).coeff k).totalDegree≤ s.U:= by
    by_cases hz : (Q.coeff j).coeff k=0
    · simp [hz]
    · exact (d3r crt word hQ j k hz).2.2
  obtain ⟨R,hR,hn',ha⟩:=cNB Q hn _ (bVl crt word hpos hhi tm)
    (fun G hg hd hv hm=>cCz crt word hpos hhi tm hg hv hm hn hd hp hseed)
  exact ⟨Q,R,hQ,hR,hn,hn',fun G hg hd hd' hv =>
    cSB G (fun hm=>ha G hg hd hv hm hd')⟩
end
end qdY8S8d
end
section
set_option autoImplicit true
namespace qxWWUna
open Finset
open P6 (dw p)
open P6_7_1 (afa Intro packetLo packetHi)
open cu (triangle ku)
open DP (bga)
open czX (a8x dei)
open qZyoMPc (aP4 bound)
open private row aJm level cck from ProximityPrize.SubmissionLower.E7
open private total asB from ProximityPrize.SubmissionLower.Z07A6ec
open private bid from ProximityPrize.SubmissionLower.CN
private theorem cA5: (dw:ℤ)=179827:=rfl
private def origin (b:Bank) (h:ℤ) :ℤ:=(b.shape.m:ℤ)*dw - 2*h*b.dI
private def worst (b:Bank) (h:ℤ) :ℤ:=origin b h-(131071-h)*b.shape.B
private def tailLen (b:Bank) (mode :ℕ) :ℕ :=
  if mode=0 then 0 else
    b.shape.B+1-((count packetLo b-(2*packetLo-1)*b.shape.J)/(131071-packetLo)+1)
private def keep (b:Bank) (q:ℕ) :ℕ :=
  min (min q b.shape.J) ((count packetLo b-q*(131071-packetLo))/(2*packetLo-1))+1
private def shortSum (f :ℕ→ℤ) :ℕ→ℤ
  | 0=>0
  | n+1=>shortSum f n+f n
private theorem shortSum_eq (f :ℕ→ℤ) (n:ℕ) :
    shortSum f n = ∑ i∈range n,f i:= by
  induction n with
  | zero=>simp [shortSum]
  | succ n ih=>rw [shortSum,ih,sum_range_succ]
private def trim (b:Bank) (mode :ℕ) (h:ℤ) :ℤ :=
  shortSum (fun i =>
    let q:=b.shape.B+1-tailLen b mode+i
    let x :=2*origin b h
    let y := -2*(131071-h)
    let z :=1-2*mode*h
    row x y z q (min q b.shape.J+1) - row x y z q (keep b q)) (tailLen b mode)
private def signedTotal (b:Bank) (mode :ℕ) (h:ℤ) :ℤ :=
  total b.shape (2*origin b h) (-2*(131071-h)) (1-2*mode*h)-6*trim b mode h
private theorem gq1 (b:Bank) (h mode q j:ℕ) (hh:h≤131071) :
    origin b h-(131071-(h:ℤ))*q+(1-2*mode*(h:ℤ))*j ≤
      ((count h b+j-q*(131071-h)-mode*(2*h*j) :ℕ) :ℤ) := by
  have cast_sub_le (a b:ℕ) : (a :ℤ)-b≤((a-b:ℕ) :ℤ) := by omega
  have hcut:=cast_sub_le (b.shape.m*dw) (2*h*b.dI)
  have hraw:=cast_sub_le (count h b+j) (q*(131071-h))
  have hloss :=cast_sub_le (count h b+j-q*(131071-h)) (mode*(2*h*j))
  change _≤(count h b:ℤ) at hcut
  push_cast [Nat.cast_sub hh] at hcut hraw hloss
  unfold origin
  rw [cA5]
  nlinarith only [hcut,hraw,hloss]
private theorem total_le (b:Bank) (mode h:ℕ) (hh:h≤131071) (hJ:b.shape.J≤b.shape.B+1) :
    (triangle b.shape.U:ℤ)*signedTotal b mode h≤12*(O3 h b mode :ℤ) := by
  let t:=tailLen b mode
  let a :=b.shape.B+1-t
  have ht:t≤b.shape.B+1 := by
    unfold t tailLen
    split
    · exact Nat.zero_le _
    · exact Nat.sub_le _ _
  have ha :a+t=b.shape.B+1 :=Nat.sub_add_cancel ht
  let R (q n:ℕ) :=row (2*origin b h) (-2*(131071-(h:ℤ))) (1-2*mode*(h:ℤ)) q n
  let W (q j:ℕ) :ℤ:=(count h b+j-q*(131071-h)-mode*(2*h*j) :ℕ)
  have hr (q n:ℕ) (hn:n≤ min q b.shape.J+1) :
      R q n≤2 * ∑ j∈range (min q b.shape.J+1),W q j:= by
    have he :R q n=2 * ∑ j∈range n,
        (origin b h-(131071-(h:ℤ))*q+(1-2*mode*(h:ℤ))*j) := by
      rw [bid]
      unfold R row
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by decide)
    exact (sum_le_sum fun j _=>gq1 b h mode q j hh).trans
      (sum_le_sum_of_subset_of_nonneg (range_mono hn) fun j _ _=>Int.natCast_nonneg _)
  let F (q:ℕ) := ∑ j∈range (min q b.shape.J+1),W q j
  have hsum: (∑ q∈range a,R q (min q b.shape.J+1)) +
      (∑ i∈range t,R (a+i) (keep b (a+i)))≤2 * ∑ q∈range (b.shape.B+1),F q:= by
    rw [← ha,sum_range_add F,mul_add,mul_sum,mul_sum]
    exact add_le_add (sum_le_sum fun q _=>hr q _ le_rfl)
      (sum_le_sum fun i _=>hr (a+i) _ (Nat.succ_le_succ (min_le_left _ _)))
  have he :signedTotal b mode h=6*((∑ q∈range a,R q (min q b.shape.J+1)) +
      ∑ i∈range t,R (a+i) (keep b (a+i))) := by
    unfold signedTotal trim
    rw [asB _ _ _ _ hJ,shortSum_eq]
    change 6*(∑ q∈range (b.shape.B+1),R q (min q b.shape.J+1)) -
      6*(∑ i∈range t,(R (a+i) (min (a+i) b.shape.J+1) - R (a+i) (keep b (a+i))))= _
    rw [← ha,sum_range_add (fun q=>R q (min q b.shape.J+1)),sum_sub_distrib]
    ring
  have hz :=mul_le_mul_of_nonneg_left hsum
    (show 0≤6*(triangle b.shape.U:ℤ) from mul_nonneg (by decide) (Int.natCast_nonneg _))
  rw [he]
  unfold O3 ku
  push_cast
  change _≤12*((triangle b.shape.U:ℤ) * ∑ q∈range (b.shape.B+1),F q)
  linarith only [hz]
private def score (b:Bank) (mode :ℕ) (h:ℤ) :ℤ :=
  (triangle b.shape.U:ℤ) *
      (signedTotal b mode h - 2*(262144*a8x (b.shape.m-2*b.shape.J) b.shape.J:ℕ)) -
    24*h*b.DG
private theorem test (b:Bank) (mode h:ℕ) (hl:packetLo≤h) (hu:h≤packetHi)
    (hJ:b.shape.J≤b.shape.B) (hU:b.shape.B≤b.shape.U) (hp:b.shape.B<K1.p)
    (hm:2*b.shape.J≤b.shape.m) (hB:b.shape.m+b.shape.J≤b.shape.B+1)
    (hd:aP4 b.shape.B b.shape.J b.shape.U≤2880*(b.DG:ℤ))
    (hw₀:0<worst b packetLo) (hw₁:0<worst b packetHi)
    (hs₀:0<score b mode packetLo) (hs₁:0<score b mode packetHi) :
    Tests h b mode := by
  have hli: (packetLo:ℤ)≤h:=Int.ofNat_le.mpr hl
  have hui: (h:ℤ)≤packetHi:=Int.ofNat_le.mpr hu
  have hh:=hu.trans (show packetHi≤131071 by decide)
  have wa (t:ℤ) :worst b t=worst b packetLo+(t-(packetLo:ℤ))*((b.shape.B:ℤ)-2*b.dI) := by
    unfold worst origin
    ring
  have ta (t:ℤ) :trim b mode t=trim b mode packetLo +
      (t-(packetLo:ℤ))*(trim b mode ((packetLo:ℤ)+1)-trim b mode packetLo) := by
    simp only [trim,shortSum_eq,← sum_sub_distrib,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    unfold row origin
    ring
  have sa (t:ℤ) :score b mode t=score b mode packetLo +
      (t-(packetLo:ℤ))*(score b mode ((packetLo:ℤ)+1)-score b mode packetLo) := by
    unfold score signedTotal
    rw [ta t]
    unfold total aJm level origin
    ring
  rw [wa] at hw₁
  rw [sa (packetHi:ℤ)] at hs₁
  have hw:=(wa h).symm ▸ cck hli hui hw₀ hw₁
  have hs :=(sa h).symm ▸ cck hli hui hs₀ hs₁
  unfold worst origin at hw
  rw [cA5] at hw
  have hn:0≤(131071-(h:ℤ))*(b.shape.B:ℤ) :=
    mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
  have hbuf :2*h*b.dI≤b.shape.m*dw:= by
    apply Int.ofNat_le.mp
    push_cast
    linarith only [hw,hn]
  have hwidth :b.shape.B*(131071-h)<count h b:= by
    apply Int.ofNat_lt.mp
    unfold count
    push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
    linarith only [hw]
  have hnode :=congrArg (fun n:ℕ=>(n:ℤ)) (dei b.shape hm hB)
  have hphys :bga b.shape=triangle b.shape.U*agU.ad1 b.shape := by
    unfold bga agU.ad1
    rw [Nat.mul_assoc]
  have hscores :=total_le b mode h hh (hJ.trans (Nat.le_succ _))
  refine ⟨hJ,hU,hp,bound _ _ hJ hU hd,hwidth,Int.ofNat_lt.mp ?_⟩
  unfold score at hs
  rw [← hnode] at hs
  unfold j3
  rw [hphys]
  push_cast at hs ⊢
  linarith only [hs,hscores]
local notation "test!" => test _ _ _ ‹packetLo≤_› ‹_≤packetHi›
  (by decide) (by decide) (by decide) (by decide) (by decide)
  (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
  (of_decide_eq_true rfl) (of_decide_eq_true rfl)
theorem free_tests {h:ℕ} (hl:packetLo≤h) (hu:h≤packetHi) (i:afa) :
    Tests h (free i) 0:= by
  fin_cases i <;> exact test!
theorem moving_tests {h:ℕ} (hl:packetLo≤h) (hu:h≤packetHi) (i:afa) :
    Tests h (moving i) 1 := by
  fin_cases i <;> exact test!
theorem aux_tests {h:ℕ} (hl:packetLo≤h) (hu:h≤packetHi) (i:Intro) :
    Tests h (aux i) 0:= by
  fin_cases i <;> exact test!
theorem ddk (i:afa) : (free i).shape.U<p:= by
  fin_cases i <;> decide
end qxWWUna
end
