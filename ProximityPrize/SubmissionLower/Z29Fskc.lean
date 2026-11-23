import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.ZQpU10d
set_option Elab.async false
set_option maxRecDepth 2048
section
set_option autoImplicit true
namespace q8kPhwd
open GI (kJ)
open aFM (avC a7s)
open aRR (DW)
open private core from ProximityPrize.SubmissionLower.ZQpU10d
def Ig (t p:ℕ) :kJ :=
  let a :=4*p-5030-t
  let b:=min 570 ((7*p-8875-3*t)/2)
  let c:=min 570 ((16*p-20280-9*t)/4)
  let m:=max b c
  if t<115 then
    if p<1299+45*t/100 then
      if t<15 then ⟨0,0,c⟩ else ⟨a,0,2*c/3⟩
    else if t<64 then ⟨0,m/3,2*m/3⟩ else ⟨0,m/2,m/2⟩
  else if t<145 then
    if p<1280+t/2 then ⟨a,0,0⟩
    else if p<1292+t/2 then ⟨a,0,2*c/3⟩ else ⟨0,m/2,m/2⟩
  else if p<1289+44*t/100 then ⟨a,0,0⟩
  else if p<1301+45*t/100 then ⟨a,b/3,0⟩
  else if p<1278+55*t/100-(221-t)/2 then ⟨a,2*b/3,0⟩
  else if t<225 || (t<320 && p<1393+35*t/100) then ⟨0,2*m/3,m/3⟩
  else if p<1393+35*t/100 then ⟨0,b,0⟩ else ⟨a,0,2*c/3⟩
def oppExpr (p o:ℕ) :ℕ :=
  let x :=1711-(o+2)/3
  let z :=3*min 571 (1711-o)
  (avC o+avC (p-x-z))-(avC (p-x)+avC (p-z))
def saving (t p:ℕ) (w:kJ) :ℕ :=
  let a :=w.value
  let b:=w.top
  let c:=w.Ej
  let spent:=a+b+3*c
  if 1710<spent || 570<b+c then 0 else
    let d:=1710-spent
    core d (1711-3*(b+c)) (p-3*b-2*c) (p+100-t-2*b-3*c)
      (min (d+1) ((1813-t-a-4*c)/4))
def entry (t p:ℕ) :ℕ :=
  let opp:=oppExpr p (p+100-t)
  let old:=0x854673d-avC p
  let lo:=if t<115 then 1285+43*t/100 else 1281+(t-100)/4
  let hi:=if t<228 then 1345+52*t/100 else 1387+42*t/100
  if p<1275 then opp else if hi<p then old else
    min opp (if p<lo then old else old - saving t p (Ig t p))
def acF (q:ℕ) :ℤ :=
  24*(158*0x854673d +
    a7s (fun i=>a7s (fun j=>entry (q-2900) (1552-(22*i+j))) 22) 16:ℕ)
    - DW 1710+DW 1552+DW (4200-(q:ℤ))
end q8kPhwd
end
section
set_option autoImplicit true
namespace q8kPhwd
open P6_6_2
open xE (Flag denominator gd oldCount AO U1 m5 BH)
open GI (a7O anX)
open aAZ (anW bwI Jc)
open aFM (avC)
open private b9F from ProximityPrize.SubmissionLower.B
open private arn from ProximityPrize.SubmissionLower.BK
open private save count_eq from ProximityPrize.SubmissionLower.ZfPVEHa
open private core_eq from ProximityPrize.SubmissionLower.ZQpU10d
def bY (p o:ℤ) :Flag:=⟨1710,p,1710,570,o⟩
theorem flag_plateau {q:ℕ} (hl:2900≤q) (hh:q<3307) (r :Offset) :
    pT q r=bY (1710-(r.val :ℤ)) (4710-(q:ℤ) - r.val) := by
  rw [qwbsesc.b3v]
  unfold iO P6_6.Dj
  rw [ite_eq_left hh,min_eq_right (by omega :1710≤q),min_eq_right (by omega :1710≤q)]
  rfl
private theorem capped_den (u:ℤ) (hu:u≤1710) :U1 1710 u 570=denominator u:= by
  rw [qwbsesc.bCi _ _ hu,anW _ _ (by decide) (by omega),
    bwI _ _ hu]
theorem bJS (p o:ℤ) (hp:p≤1710) :
    oldCount (bY p o)=denominator 1710 - denominator (p-1) := by
  unfold oldCount bY
  dsimp only
  rw [min_eq_right (by omega),capped_den _ le_rfl,capped_den _ (by omega)]
theorem old_nonneg (p:ℤ) (hp:p≤1710) :0≤denominator 1710 - denominator (p-1) := by
  have eqc (u:ℤ) (hu:u≤1710) :gd 1710 u=denominator u :=
    (anW _ _ (by decide) (by omega)).trans (bwI _ _ hu)
  rw [← eqc _ le_rfl,← eqc _ (by omega)]
  exact sub_nonneg.mpr (anX 1710 (by omega))
theorem den_nonneg (u:ℤ) (hu:u≤1710) :0≤denominator u:= by
  rw [← capped_den _ hu,qwbsesc.bCi _ _ hu,← aw7.proof]
  exact Int.natCast_nonneg _
private def shiftX (o:ℤ) :ℤ:=1711-(o+2)/3
private def shiftZ (o:ℤ) :ℤ:=3*min 571 (1711-o)
private theorem opp_le {p o:ℤ} (hp:0<p) (hp' : p≤1710)
    (ho:0<o) (ho' : o≤1710) :
    oppositeBound (bY p o) ≤
      (denominator (o-1)+denominator (p-1-shiftX o-shiftZ o)
        - (denominator (p-1-shiftX o)+denominator (p-1-shiftZ o))).toNat := by
  unfold oppositeBound
  rw [ite_eq_right (show ¬ (bY p o).order≤0 from not_le.mpr ho),
    ite_eq_right (show ¬ (bY p o).lower≤0 from not_le.mpr hp)]
  change (oldCount (bY p o)-(U1 1710 1710 570 -
    U1 1710 (min 1710 (o-1)) 570) +
    min (latticeAllowance (bY p o))
      (U1 1710 1710 570-U1 1710 (min 1710 (o-1)) 570)).toNat≤_
  rw [min_eq_right (show o-1≤1710 by omega),capped_den 1710 le_rfl,
    capped_den (o-1) (by omega),bJS p o hp']
  apply Int.toNat_le_toNat
  refine (add_le_add_right (min_le_left (latticeAllowance (bY p o)) _) _).trans ?_
  have hx :max 0 (min 1710 (1710 :ℤ)-(o+2)/3+1)=shiftX o:= by
    rw [min_self,max_eq_right (by omega)]
    unfold shiftX
    ring
  have hy :2*max 0 (min 1710 ((1710 :ℤ)/2) - max 0 ((o-1710+1)/2)+1)
      = 1712 := by
    rw [show max 0 ((o-1710+1)/2)=0 by omega]
    decide
  have hz :3*max 0 (min (min 570 (1710 :ℤ)) (1710-o)+1)=shiftZ o:= by
    rw [min_eq_left (by decide : (570:ℤ)≤1710),max_eq_right (by
      exact add_nonneg (le_min (by decide) (by omega)) (by decide))]
    unfold shiftZ
    congr 1
    omega
  unfold latticeAllowance
  simp only [bY,hx,hy,hz]
  rw [Jc (p-1-1712) (by omega),
    Jc (p-1-shiftX o-1712) (by unfold shiftX; omega),
    Jc (p-1-1712-shiftZ o) (by unfold shiftZ; omega),
    Jc (p-1-shiftX o-1712-shiftZ o) (by unfold shiftX shiftZ; omega)]
  ring_nf
  exact le_rfl
theorem tail_block {q:ℕ} (hl:2900≤q) (hh:q<3307)
    (r :Offset) (hr :510≤ r.val) (w:Fin 11→ℕ) :
    (xR q r w:ℤ)≤denominator (4709-(q:ℤ) - r.val) := by
  let p:=(1710 :ℤ) - r.val
  let o:=(4710 :ℤ)-(q:ℤ) - r.val
  have hp:p≤1200:= by dsimp [p]; omega
  have ho:o≤1300:= by dsimp [o]; omega
  have ho' : o - 1=4709-(q:ℤ) - r.val := by dsimp [o]; ring
  rw [← ho']
  have h:xR q r w≤oppositeBound (pT q r) :=min_le_right _ _
  rw [flag_plateau hl hh r] at h
  change xR q r w≤oppositeBound (bY p o) at h
  by_cases hz :o≤0
  · simp only [oppositeBound,bY,hz,ite_true] at h
    rw [Jc _ (by omega)]
    exact Int.ofNat_le.mpr h
  have ha :oppositeBound (bY p o)≤(denominator (o-1)).toNat := by
    by_cases hn:p≤0
    · rw [oppositeBound]
      simp only [bY,hz,ite_false,hn,ite_true,min_eq_right (show o-1≤1710 by omega),
        capped_den _ (show o-1≤1710 by omega)]
      exact le_rfl
    · refine (opp_le (by omega) (by omega) (by omega) (by omega)).trans ?_
      have hx :p-1-shiftX o<0:= by unfold shiftX; omega
      have hz' : p-1-shiftZ o<0:= by unfold shiftZ; omega
      have hboth:p-1-shiftX o-shiftZ o<0:= by unfold shiftX shiftZ; omega
      rw [Jc _ hx,Jc _ hz',Jc _ hboth]
      simp
  calc
    _≤((denominator (o-1)).toNat :ℤ) :=Int.ofNat_le.mpr (h.trans ha)
    _ = _:=Int.toNat_of_nonneg (den_nonneg (o-1) (by omega))
private theorem natDen_cast (u:ℤ) : (avC (u+1).toNat :ℤ)=denominator u :=
  (b9F u).trans (arn u)
private theorem oppExpr_correct {p o:ℕ} (hp:0<p) (hp' : p≤1710)
    (ho:0<o) (ho' : o≤1710) :
    oppositeBound (bY p o)≤oppExpr p o:= by
  refine (opp_le (by exact_mod_cast hp) (by exact_mod_cast hp') (by exact_mod_cast ho)
    (by exact_mod_cast ho')).trans ?_
  unfold oppExpr
  have hx : ((1711-(o+2)/3:ℕ) :ℤ)=shiftX o:= by
    unfold shiftX
    rw [Nat.cast_sub (by omega),Int.natCast_ediv,Nat.cast_add]
    rfl
  have hz : ((3*min 571 (1711-o) :ℕ) :ℤ)=shiftZ o:= by
    unfold shiftZ
    rw [Nat.cast_mul,Nat.cast_min,Nat.cast_sub (by omega)]
    rfl
  generalize 1711-(o+2)/3=x at hx ⊢
  generalize 3*min 571 (1711-o)=z at hz ⊢
  rw [← hx,← hz]
  dsimp only
  have h (a b:ℕ) : (avC (p-a-b) :ℤ)=denominator ((p:ℤ)-1-a-b) := by
    have he :p-a-b=((p:ℤ)-1-a-b+1).toNat := by omega
    rw [he,natDen_cast]
  have h₀: (avC o:ℤ)=denominator ((o:ℤ)-1) := by
    simpa only [sub_add_cancel,Int.toNat_natCast] using natDen_cast ((o:ℤ)-1)
  have h₁:=h x 0
  have h₂:=h z 0
  have h₃:=h x z
  simp only [Nat.sub_zero,Nat.cast_zero,sub_zero] at h₁ h₂
  omega
private theorem oldNat_correct (p o:ℕ) (hp:p≤1710) :
    0x854673d-avC p=(oldCount (bY p o)).toNat := by
  rw [bJS p o (by exact_mod_cast hp)]
  have hn: (avC p:ℤ)=denominator ((p:ℤ)-1) := by
    simpa only [sub_add_cancel,Int.toNat_natCast] using natDen_cast ((p:ℤ)-1)
  have hD:denominator 1710=(0x854673d:ℤ) :=rfl
  omega
private theorem save_eq (F:Flag) (hu:F.upper=3*F.cap) :
    save F=(m5 F).toNat := by
  unfold save m5
  split <;> rename_i hv
  · rfl
  dsimp only
  have hc : ¬ F.cap<0:= by
    intro h
    simp [h] at hv
  have hb (u:ℤ) (hle :u≤F.upper) :U1 F.degree u F.cap=gd F.degree u:= by
    simp only [U1,hc,ite_false,gd,
      show u-3*(F.cap+1)<0 by omega,decide_true,Bool.or_true,ite_true,sub_zero]
  unfold oldCount AO
  rw [hb _ le_rfl,hb _ (min_le_left _ _)]
  by_cases hz :F.order - 1-F.lower+F.degree<0
  · simp only [hz,ite_true,sub_zero,← count_eq]
    omega
  simp only [hz,ite_false]
  split <;> rename_i hl
  · simp only [min_eq_right hl,← count_eq]
    omega
  · simp only [min_eq_left (le_of_not_ge hl),← count_eq]
    omega
set_option maxHeartbeats 800000 in
private theorem saving_correct {t p:ℕ} (ho:t≤p+100) (w:GI.kJ) :
    saving t p w =
      (m5 (BH (bY p (p+100-t:ℕ)) w.expand)).toNat := by
  let F:=BH (bY p (p+100-t:ℕ)) w.expand
  have hf :F=⟨1710-((w.value :ℤ)+w.top+3*w.Ej),
    (p:ℤ)-(3*(w.top:ℤ)+2*w.Ej),1710-(3*(w.top:ℤ)+3*w.Ej),
    570-((w.top:ℤ)+w.Ej),↑(p+100-t:ℕ)-(2*(w.top:ℤ)+3*w.Ej)⟩ :=
    a7O _ _
  have hu:F.upper=3*F.cap:= by rw [hf]; dsimp only; ring
  rw [← save_eq F hu]
  by_cases hd:1710<w.value+w.top+3*w.Ej
  · have h:F.degree<0:= by rw [hf]; dsimp only; omega
    simp [saving,hd,save,h]
  by_cases hc:570<w.top+w.Ej
  · have h:F.cap<0:= by rw [hf]; dsimp only; omega
    simp [saving,hc,save,h]
  have hdd:0≤F.degree := by rw [hf]; dsimp only; omega
  have hcc:0≤F.cap:= by rw [hf]; dsimp only; omega
  rw [core_eq F hdd (by omega) hcc]
  simp only [saving,hd,hc,decide_false,Bool.false_or,Bool.false_eq_true,ite_false]
  congr 1 <;> rw [hf] <;> dsimp only <;> omega
theorem middle_block {q:ℕ} (hl:2900≤q) (hh:q<3307) (r :Offset)
    (hr :158≤ r.val) (hr' : r.val<510) :
    xR q r (Ig (q-2900) (1710-r.val)).expand≤entry (q-2900) (1710-r.val) := by
  let p:=1710-r.val
  let t:=q-2900
  let o:=p+100-t
  let w:=Ig t p
  change xR q r w.expand≤entry t p
  have ho:0<o∧o≤1710 := by dsimp [o,p,t]; omega
  have hF:pT q r=bY p o:= by
    rw [flag_plateau hl hh r]
    congr 1 <;> dsimp [p,o,t] <;> omega
  have ha :xR q r w.expand≤oppExpr p o:= by
    have h:xR q r w.expand≤oppositeBound (pT q r) :=min_le_right _ _
    rw [hF] at h
    exact h.trans (oppExpr_correct (p:=p) (o:=o)
      (by dsimp [p]; omega) (by dsimp [p]; omega) ho.1 ho.2)
  have hb:=qwbsesc.block_le_old q r w.expand
  rw [hF] at hb
  have he :=oldNat_correct p o (by dsimp [p]; omega)
  have hc:xR q r w.expand≤0x854673d-avC p:= by rwa [he]
  let lo:=if t<115 then 1285+43*t/100 else 1281+(t-100)/4
  let hi:=if t<228 then 1345+52*t/100 else 1387+42*t/100
  let old:=0x854673d-avC p
  change _≤(if p<1275 then oppExpr p o else if hi<p then old else
    min (oppExpr p o) (if p<lo then old else old - saving t p w))
  by_cases hs :p<1275
  · rw [ite_eq_left hs]
    exact ha
  rw [ite_eq_right hs]
  by_cases ht:hi<p
  · rw [ite_eq_left ht]
    exact hc
  rw [ite_eq_right ht]
  apply le_min ha
  by_cases hv :p<lo
  · rw [ite_eq_left hv]
    exact hc
  rw [ite_eq_right hv]
  have h:=qwbsesc.block_le_residual q r w.expand
  rw [hF] at h
  have e :=saving_correct (t:=t) (p:=p) (by dsimp [p,t]; omega) w
  rw [show p+100-t=o from rfl] at e
  rw [show old=0x854673d-avC p from rfl,he,e]
  omega
end q8kPhwd
end
section
set_option autoImplicit true
namespace q8kPhwd
open P6_6_2
open qwbsesc (aak block_le_old)
open xE (denominator)
open aRR (DW afw)
open aFM (a7s)
open private c6y from ProximityPrize.SubmissionLower.B
open private sum_den from ProximityPrize.SubmissionLower.ZJCauJe
open Finset
open scoped BigOperators
private def term (q r :ℕ) :ℤ :=
  if r<158 then denominator 1710 - denominator (1709-(r :ℤ))
  else if r<510 then entry (q-2900) (1710-r)
  else denominator (4709-(q:ℤ) - r)
private theorem term_le {q:ℕ} (hl:2900≤q) (hh:q<3307) (r :Offset) :
    (xR q r (Ig (q-2900) (1710-r.val)).expand:ℤ)≤term q r.val := by
  unfold term
  split
  · have h:=block_le_old q r (Ig (q-2900) (1710-r.val)).expand
    rw [flag_plateau hl hh,bJS _ _ (by omega),
      show (1710 :ℤ)-r.val-1=1709-r.val by ring] at h
    have he :=Int.toNat_of_nonneg (old_nonneg (1710-r.val) (by omega))
    rw [show (1710 :ℤ)-r.val-1=1709-r.val by ring] at he
    calc
      _≤(((denominator 1710 - denominator (1709-(r.val :ℤ))).toNat :ℕ) :ℤ) :=
        Int.ofNat_le.mpr h
      _ = _:=he
  · split
    · exact Int.ofNat_le.mpr (middle_block hl hh r (by omega) (by assumption))
    · exact tail_block hl hh r (by omega) _
private theorem sum_den_zero (a :ℤ) (n:ℕ) :
    24*(∑ j∈range n,denominator (a - 1-(j:ℤ))) =
      DW a - DW (a-n) := by
  simpa only [Nat.zero_add,Nat.cast_zero,sub_zero] using sum_den a 0 n
private theorem group_sum (f :ℕ→ℕ) (w n:ℕ) :
    a7s (fun i=>a7s (fun j=>f (w*i+j)) w) n=a7s f (w*n) := by
  simp only [c6y]
  induction n with
  | zero=>simp
  | succ n ih=>rw [sum_range_succ,ih,Nat.mul_succ,sum_range_add]
private theorem cfO (q:ℕ) :24*(∑ j∈range 4710,term q j)=acF q:= by
  rw [show 4710=510+4200 by decide,sum_range_add,show 510=158+352 by decide,
    sum_range_add,mul_add,mul_add]
  have ha : (∑ j∈range 158,term q j) =
      158*denominator 1710 - ∑ j∈range 158,denominator (1709-(j:ℤ)) := by
    calc
      _ = ∑ j∈range 158,(denominator 1710 - denominator (1709-(j:ℤ))) :=
        sum_congr rfl fun j hj=>ite_eq_left (mem_range.mp hj)
      _ = _:= by
        rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
        norm_num only [Nat.cast_ofNat]
  have hb: (∑ j∈range 352,term q (158+j)) =
      (a7s (fun k=>entry (q-2900) (1552-k)) 352 :ℤ) := by
    rw [c6y,Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    have h:=mem_range.mp hj
    simp only [term,show ¬158+j<158 by omega,show 158+j<510 by omega,
      ite_false,ite_true,show 1710-(158+j)=1552-j by omega]
  have hc: (∑ j∈range 4200,term q (158+352+j)) =
      ∑ j∈range 4200,denominator (4200-(q:ℤ) - 1 - j) := by
    apply sum_congr rfl
    intro j _
    simp only [term,show ¬158+352+j<158 by omega,show ¬158+352+j<510 by omega,
      ite_false,Nat.cast_add,Nat.cast_ofNat]
    rw [show (4709:ℤ)-q-(158+352+(j:ℤ))=4200-q-1-j by ring]
  rw [ha,hb,hc,mul_sub]
  have hd:=sum_den_zero 1710 158
  change 24*(∑ j∈range 158,denominator (1709-(j:ℤ))) =
    DW 1710 - DW 1552 at hd
  have ht:=sum_den_zero (4200-(q:ℤ)) 4200
  norm_num only [Nat.cast_ofNat] at ht
  rw [hd,ht,afw (4200-(q:ℤ)-4200) (by omega),sub_zero,
    acF,group_sum (fun k=>entry (q-2900) (1552-k)) 22 16,
    show 22*16=352 by decide,Nat.cast_add,Nat.cast_mul,show denominator 1710=(0x854673d:ℤ) from rfl]
  ring
private theorem grade_scaled {q:ℕ} (hl:2900≤q) (hh:q<3307) :
    24*(al2 q (fun r=>(Ig (q-2900) (1710-r.val)).expand) :ℤ)≤acF q:= by
  rw [← cfO q]
  apply mul_le_mul_of_nonneg_left _ (by decide)
  rw [al2,Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun j=>term q j) 4710]
  exact sum_le_sum fun r _=>term_le hl hh r
def bvj (lo:ℕ) :ℕ→ℤ
  | 0=>0
  | n+1=>bvj lo n+acF (lo+n)
theorem fZi (lo n:ℕ) :bvj lo n = ∑ j∈range n,acF (lo+j) := by
  induction n with
  | zero=>simp [bvj]
  | succ n ih=>rw [bvj,sum_range_succ,ih]
private theorem rowTotal_append (lo m n:ℕ) :
    bvj lo (m+n)=bvj lo m+bvj (lo+m) n:= by
  rw [fZi,sum_range_add,fZi,fZi]
  simp only [Nat.add_assoc]
theorem checked {lo m mid n a b c:ℕ}
    (h:bvj lo m=(a :ℤ)) (hm:lo+m=mid)
    (k :bvj mid n=(b:ℤ)) (hs :a+b=c) :
    bvj lo (m+n)=(c:ℤ) := by
  rw [rowTotal_append,hm,h,k,← Nat.cast_add,hs]
theorem of_total {lo hi cap:ℕ} (hl:2900≤lo) (hh:hi≤3307)
    (h:bvj lo (hi-lo)≤24*(cap:ℤ)) :aak lo hi cap:= by
  refine ⟨fun q r=>(Ig (q-2900) (1710-r.val)).expand,?_⟩
  have he : (24 :ℤ)*rankBand (fun q r=>(Ig (q-2900) (1710-r.val)).expand) lo hi ≤
      bvj lo (hi-lo) := by
    rw [fZi,← sum_Ico_eq_sum_range,rankBand,Nat.cast_sum,mul_sum]
    exact sum_le_sum fun j hj=>grade_scaled (hl.trans (mem_Ico.mp hj).1)
      ((mem_Ico.mp hj).2.trans_le hh)
  omega
end q8kPhwd
end
section
set_option autoImplicit true
namespace q8kPhwd
open aFM (a7s)
open aRR (DW)
private def inside (q:ℕ) :ℕ :=
  a7s (fun i=>a7s (fun j=>entry (q-2900) (1552-(22*i+j))) 22) 16
private def zJ (q:ℕ) :ℤ :=
  24*((158*0x854673d:ℕ) :ℤ) - DW 1710+DW 1552+DW (4200-(q:ℤ))
def insideTotal (lo:ℕ) :ℕ→ℕ
  | 0=>0
  | n+1=>insideTotal lo n+inside (lo+n)
def outsideTotal (lo:ℕ) :ℕ→ℤ
  | 0=>0
  | n+1=>outsideTotal lo n+zJ (lo+n)
private theorem parts (lo n:ℕ) :
    bvj lo n=24*(insideTotal lo n:ℤ)+outsideTotal lo n:= by
  induction n with
  | zero=>simp [bvj,insideTotal,outsideTotal]
  | succ n ih =>
    rw [bvj,ih,insideTotal,outsideTotal,acF]
    unfold inside zJ
    simp only [Nat.cast_add]
    ring
theorem numeric (lo n a c:ℕ) (h:insideTotal lo n=a)
    (k :24*(a :ℤ)+outsideTotal lo n=(c:ℤ)) :bvj lo n=(c:ℤ) := by
  rw [parts,h,k]
end q8kPhwd
end
