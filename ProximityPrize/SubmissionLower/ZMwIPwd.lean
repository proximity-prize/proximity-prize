import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.ZQpU10d
import ProximityPrize.SubmissionLower.ZLMe53d
import ProximityPrize.SubmissionLower.ZQGI7be
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 8192
namespace qs7wmAa
open Finset P6_6_2
open qwbsesc (aak b3v pairPowers residual_pair block_le_old)
open xE (Flag Jd U1 gd denominator oldCount AO m5 BH)
open aRR (DW b0n afw)
open aAZ (Jc anW aej bwI)
open aFM (a7s)
open private c6y from ProximityPrize.SubmissionLower.B
open private xY arn from ProximityPrize.SubmissionLower.CM
open private count_eq save from ProximityPrize.SubmissionLower.ZfPVEHa
open private countN count_eq_countN core core_eq from ProximityPrize.SubmissionLower.ZQpU10d
open private fWE from ProximityPrize.SubmissionLower.DY
def valPow (d q r :ℕ) :ℕ:=3000+d - q-4*r
def topPow (d q r :ℕ) :ℕ :=
  min (min 570 ((4*(4710 - q)-3422 - 9*r)/2)) (d - valPow d q r)
def aji (d q r :ℕ) :Fin 11→ℕ :=
  pairPowers 0 3 (valPow d q r) (topPow d q r)
def saving (d q r :ℕ) :ℕ :=
  let a :=valPow d q r
  let b:=topPow d q r
  let dd:=d-a - b
  core dd (1711 - 3*b) (1710 - r-3*b) (4710 - q - r - 2*b)
    (min (dd+1) ((3003+d - q-a)/4))
def oldSum (d:ℕ) :ℕ :=
  a7s (fun r=>countN d 1711 - countN d (1710 - r)) 310
def rowSave (d q:ℕ) :ℕ :=
  a7s (fun i=>a7s (fun j=>saving d q (40+18*i+j)) 18) 15
def saveSum (d lo:ℕ) :ℕ→ℕ
  | 0=>0
  | n+1=>saveSum d lo n+rowSave d (lo+n)
def bhM (lo:ℕ) :ℕ→ℤ
  | 0=>0
  | n+1=>bhM lo n+DW (↑(4400-(lo+n) :ℕ) :ℤ)
private theorem dEV (d u t:ℤ) (ht:0≤t) (hu:u≤3*t) :
    U1 d u t=gd d u:= by
  have h:u-3*(t+1)<0:= by omega
  simp [U1,not_lt.mpr ht,gd,h]
private theorem save_eq_lower (F:Flag) (hu:F.upper≤3*F.cap) :
    save F=(m5 F).toNat := by
  unfold save m5
  split <;> rename_i hv
  · rfl
  dsimp only
  have hc:0≤F.cap:= by
    have : ¬ F.cap<0:= fun h=> by simp [h] at hv
    omega
  unfold oldCount AO
  rw [dEV _ _ _ hc hu,dEV _ _ _ hc ((min_le_left _ _).trans hu)]
  by_cases hz :F.order - 1-F.lower+F.degree<0
  · simp only [hz,ite_true,sub_zero,← count_eq]; omega
  simp only [hz,ite_false]
  split <;> rename_i hl
  · simp only [min_eq_right hl,← count_eq]; omega
  · simp only [min_eq_left (le_of_not_ge hl),← count_eq]; omega
private theorem countN_cast (d:ℕ) (u:ℤ) :
    (countN d (u+1).toNat :ℤ)=gd d u:= by
  rw [← count_eq,count_eq_countN]
  simp only [not_lt.mpr (Int.natCast_nonneg d),ite_false,Int.toNat_natCast]
private theorem bJS {d q:ℕ} (he :iO q=d) (r :Offset) :
    oldCount (pT q r)=((countN d 1711 - countN d (1710 - r.val) :ℕ) :ℤ) := by
  have h1 :=countN_cast d 1710
  have h2 :=countN_cast d (1709-(r.val :ℤ))
  change (countN d 1711 :ℤ)=gd d 1710 at h1
  rw [show ((1709:ℤ) - r.val+1).toNat=1710 - r.val by omega] at h2
  have hn:0≤oldCount (pT q r) := by
    rw [← bjv.proof aw7.proof]; exact Int.natCast_nonneg _
  have ho:oldCount (pT q r)=gd d 1710 - gd d (1709-(r.val :ℤ)) := by
    rw [b3v,he]; unfold oldCount; dsimp only
    rw [min_eq_right (by omega : (1710 :ℤ) - r.val - 1≤1710),
      show (1710 :ℤ) - r.val - 1=1709 - r.val by ring,
      dEV _ _ _ (by decide) (by decide),dEV _ _ _ (by decide) (by omega)]
  rw [ho,← h1,← h2] at hn ⊢; omega
private theorem saving_eq {d q:ℕ} (hd' : d≤1710) (hq:3307≤q) (he :iO q=d)
    (r :Offset) :
    (m5 (BH (pT q r) (aji d q r.val))).toNat=saving d q r.val := by
  let a :=valPow d q r.val; let b:=topPow d q r.val
  have ha :a≤d:= by dsimp [a,valPow]; omega
  have hb:b≤570:=(min_le_left _ _).trans (min_le_left _ _)
  have hab:a+b≤d:= by have :b≤d-a :=min_le_right _ _; omega
  let R:=BH (pT q r) (aji d q r.val)
  have hR:R=⟨(d:ℤ)-a - b,1710-(r.val :ℤ)-3*b,1710-3*(b:ℤ),
      570-(b:ℤ),4710-(q:ℤ) - r.val - 2*b⟩:= by
    rw [show R=BH (pT q r) (pairPowers 0 3 a b) from rfl,
      b3v,he,residual_pair,show Jd 0=⟨1,0,0,0,0⟩ from rfl,
      show Jd 3=⟨1,3,3,1,2⟩ from rfl]
    dsimp only; congr 1 <;> ring
  have hu:R.upper≤3*R.cap:= by rw [hR]; dsimp only; omega
  rw [← save_eq_lower R hu,core_eq R (by rw [hR]; dsimp only; omega)
    (by rw [hR]; dsimp only; omega) (by rw [hR]; dsimp only; omega)]
  have hD:R.degree.toNat=d-a - b:= by rw [hR]; dsimp only; omega
  have hD' : (R.degree+1).toNat=d-a - b+1 := by rw [hR]; dsimp only; omega
  have hU: (R.upper+1).toNat=1711 - 3*b:= by rw [hR]; dsimp only; omega
  have hL:R.lower.toNat=1710 - r.val-3*b:= by rw [hR]; dsimp only; omega
  have hO:R.order.toNat=4710 - q - r.val - 2*b:= by rw [hR]; dsimp only; omega
  have hB: (R.order+3 - R.lower+R.degree).toNat=3003+d - q-a := by rw [hR]; dsimp only; omega
  rw [hD,hD',hU,hL,hO,hB]; rfl
private theorem dzo {d q:ℕ} (hd' : d≤1710) (hq:3307≤q) (he :iO q=d)
    (r :Offset) :
    (xR q r (aji d q r.val) :ℤ) ≤
      ((countN d 1711 - countN d (1710 - r.val) :ℕ) :ℤ) -
        if 40≤ r.val then (saving d q r.val :ℤ) else 0:= by
  let F:=pT q r; let p:=aji d q r.val; let R:=BH F p
  have ho:=bJS he r
  have hn0:0≤oldCount F:= by rw [← bjv.proof aw7.proof]; exact Int.natCast_nonneg _
  split_ifs with h40
  · have hnR:0≤oldCount F - m5 R:=fWE F p
    have hle :xR q r p≤(oldCount F - max 0 (m5 R)).toNat := by
      refine (min_le_left _ _).trans ?_
      unfold prescribedBound; dsimp only; split
      · exact Nat.zero_le _
      · exact Int.toNat_le_toNat ((min_le_right _ _).trans (sub_le_sub_left (max_le_max_left _ (le_max_right _ _)) _))
    have hnn:0≤oldCount F - max 0 (m5 R) := by omega
    have hmx :max 0 (m5 R)=(saving d q r.val :ℤ) := by
      rw [← saving_eq hd' hq he r]
      change max 0 (m5 R)=((m5 R).toNat :ℤ)
      omega
    have h1 :=Int.ofNat_le.mpr hle
    rw [Int.toNat_of_nonneg hnn,ho,hmx] at h1; exact h1
  · rw [sub_zero]
    have h1 :=Int.ofNat_le.mpr (block_le_old q r p)
    rw [Int.toNat_of_nonneg hn0,ho] at h1; exact h1
private theorem den_nonneg (u:ℤ) :0≤xY u:= by
  unfold xY; split
  · rfl
  · rename_i h; have :0≤u:= by omega
    exact Int.ediv_nonneg (by positivity) (by decide)
private theorem dzq {d q:ℕ} (hd:1400≤d) (hd' : d≤1710) (hq:3307≤q)
    (hqd:4710 - q≤d) (he :iO q=d) (r :Offset)
    (hr :r.val<4710 - q) (h310 :310≤ r.val) (p:Fin 11→ℕ) :
    (xR q r p:ℤ)≤denominator (4709-(q:ℤ) - r.val) := by
  let l:ℤ:=1710 - r.val; let o:ℤ:=4710 - q - r.val; let u:=l - 1
  let x :=(d:ℤ)-(o+2)/3+1; let z :=3*(min (570:ℤ) (1710 - o)+1)
  have hx :933≤x := by dsimp [x,o]; omega
  have hz :924≤z := by have : (307:ℤ)≤ min 570 (1710 - o) :=le_min (by decide) (by dsimp [o]; omega); dsimp [z]; omega
  have hall:latticeAllowance ⟨d,l,1710,570,o⟩=denominator u - denominator (u - x) - denominator (u - z) := by
    have hZ:0≤ min (570:ℤ) (1710 - o)+1 := by have : (0:ℤ)≤ min 570 (1710 - o) :=le_min (by decide) (by dsimp [o]; omega); omega
    simp only [latticeAllowance,min_eq_left (show (d:ℤ)≤1710 by omega),
      min_eq_left (show (570:ℤ)≤d by omega),show (1710 :ℤ)/2=855 by decide,
      min_eq_right (show (855:ℤ)≤d by omega),max_eq_left (show (o - d+1)/2≤0 by dsimp [o]; omega),
      sub_zero,max_eq_right (by decide : (0:ℤ)≤855+1),max_eq_right hZ,
      show (2 :ℤ)*(855+1)=1712 by decide]
    change denominator u - denominator (u - max 0 x) - denominator (u - 1712) - denominator (u - z) +
      denominator (u - max 0 x - 1712)+denominator (u - max 0 x - z)+denominator (u - 1712 - z) -
      denominator (u - max 0 x - 1712 - z)= _
    have hu:u≤1709:= by dsimp [u,l]; omega
    simp (disch:=omega) only [max_eq_right (show 0≤x by omega),Jc,sub_zero,add_zero]
  have hopp:oppositeBound ⟨d,l,1710,570,o⟩≤(denominator (o - 1)).toNat := by
    unfold oppositeBound; dsimp only
    rw [ite_eq_right (show ¬ o≤0 by dsimp [o]; omega),ite_eq_right (show ¬ l≤0 by dsimp [l]; omega),
      min_eq_right (show o - 1≤1710 by dsimp [o]; omega),oldCount]
    dsimp only
    rw [min_eq_right (show l - 1≤1710 by dsimp [l]; omega),
      dEV d 1710 570 (by decide) (by decide),dEV d (o - 1) 570 (by decide) (by dsimp [o]; omega),
      dEV d (l - 1) 570 (by decide) (by dsimp [l]; omega),hall]
    apply Int.toNat_le_toNat
    have h1 :=min_le_left (denominator u - denominator (u - x) - denominator (u - z))
      (gd d 1710 - gd d (o - 1))
    have h2 :=anW d (o - 1) (by omega) (by dsimp [o]; omega)
    have h3:=bwI d (o - 1) (by dsimp [o]; omega)
    have h4 :=anW d (l - 1) (by omega) (by dsimp [l]; omega)
    have h5 (i:ℤ) (hi:1≤ i) :denominator (u - d - i)=0:=Jc _ (by dsimp [u,l]; omega)
    have h6:0≤denominator (u - x) := by rw [← arn]; exact den_nonneg _
    have h7:0≤denominator (u - z) := by rw [← arn]; exact den_nonneg _
    have h8:gd d (l - 1)=denominator u:= by
      rw [h4]; unfold aej; change denominator u - denominator (u - d - 1) - denominator (u - d - 2) - denominator (u - d-3)=denominator u
      rw [h5 1 (by decide),h5 2 (by decide),h5 3 (by decide)]; ring
    have h9:gd d (o - 1)=denominator (o - 1) :=h2.trans h3
    linarith
  have hb:xR q r p≤(denominator (4709-(q:ℤ) - r.val)).toNat := by
    refine (min_le_right _ _).trans ?_
    rw [b3v,he]
    simpa only [l,o,show (4710 :ℤ) - q - r.val - 1=4709 - q - r.val by ring] using hopp
  have hn:0≤denominator (4709-(q:ℤ) - r.val) := by rw [← arn]; exact den_nonneg _
  exact (Int.ofNat_le.mpr hb).trans_eq (Int.toNat_of_nonneg hn)
private theorem bmn (q:ℕ) (r :Offset) (hr :4710 - q≤ r.val) (p:Fin 11→ℕ) :
    xR q r p=0:= by
  refine Nat.eq_zero_of_le_zero ((min_le_right _ _).trans ?_)
  rw [b3v]; change (if (4710 :ℤ) - q - r.val≤0 then 0 else _)≤0
  exact le_of_eq (ite_eq_left (by omega))
private theorem rowSave_eq (d q:ℕ) :
    rowSave d q = ∑ j∈range 270,saving d q (40+j) := by
  have h2 (m:ℕ) :a7s (fun i=>a7s (fun j=>saving d q (40+18*i+j)) 18) m =
      ∑ k∈range (18*m),saving d q (40+k) := by
    induction m with
    | zero=>simp [a7s]
    | succ m ih =>
      rw [a7s,ih,c6y,show 18*(m+1)=18*m+18 by ring,sum_range_add]
      exact congrArg (_ + ·) (sum_congr rfl fun j _=>congrArg (saving d q) (by omega))
  exact h2 15
private theorem saveSum_add (d lo m n:ℕ) :
    saveSum d lo (m+n)=saveSum d lo m+saveSum d (lo+m) n:= by
  induction n with
  | zero=>simp [saveSum]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,saveSum,saveSum,ih,Nat.add_assoc,
      show lo+(m+n)=lo+m+n by omega]
theorem saveSum_append {d lo m n a b c:ℕ} (h1 :saveSum d lo m=a)
    (h2 :saveSum d (lo+m) n=b) (hc:a+b=c) :saveSum d lo (m+n)=c:= by
  rw [saveSum_add,h1,h2,hc]
private theorem saveSum_eq (d lo n:ℕ) :
    saveSum d lo n = ∑ i∈range n,rowSave d (lo+i) := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [saveSum,sum_range_succ,ih]
private theorem dgC (lo n:ℕ) :
    bhM lo n = ∑ i∈range n,DW (↑(4400-(lo+i) :ℕ) :ℤ) := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [bhM,sum_range_succ,ih]
private theorem euy (q:ℕ) (hq:q≤4400) :
    24*(∑ r∈Ico 310 (4710 - q),denominator (4709-(q:ℤ) - r)) =
      DW (↑(4400 - q:ℕ) :ℤ) := by
  let n:=4400 - q
  rw [sum_Ico_eq_sum_range,show 4710 - q-310=n by dsimp [n]; omega]
  have hs : (∑ r∈range n,denominator (4709-(q:ℤ)-((310+r :ℕ) :ℤ))) =
      ∑ r∈range n,denominator (0+(r :ℤ)) := by
    conv_rhs=>rw [← sum_range_reflect (fun r :ℕ=>denominator (0+(r :ℤ))) n]
    refine sum_congr rfl fun r hr => ?_
    have h:=mem_range.mp hr; congr 1; dsimp [n] at h ⊢; omega
  rw [hs,b0n,zero_add,afw 0 le_rfl,sub_zero]
theorem plateau_band {d lo hi os sv cap:ℕ} {tl:ℤ}
    (hd:1400≤d) (hd' : d≤1710) (hlo:3307≤lo) (hhi:hi≤3678)
    (hle :lo≤hi) (hld:4710-lo≤d)
    (he : ∀ q∈Ico lo hi,iO q=d)
    (hos :oldSum d=os) (hsv :saveSum d lo (hi-lo)=sv)
    (htl:bhM lo (hi-lo)=tl)
    (hcap:24*(((hi-lo:ℕ) :ℤ)*os - sv)+tl≤24*(cap:ℤ)) :
    aak lo hi cap:= by
  refine ⟨fun q r=>aji d q r.val,?_⟩
  have hrow (q:ℕ) (hq:q∈Ico lo hi) :
      24*(al2 q (fun r=>aji d q r.val) :ℤ) ≤
        24*((os :ℤ) - rowSave d q)+DW (↑(4400 - q:ℕ) :ℤ) := by
    obtain ⟨h1,h2⟩:=mem_Ico.mp hq
    let term (r :ℕ) :ℤ:=if hr :r<4710 then ↑(xR q ⟨r,hr⟩ (aji d q r)) else 0
    have hre (r :Offset) :term r.val=xR q r (aji d q r.val) :=dite_eq_left r.isLt
    have hsum: (al2 q (fun r=>aji d q r.val) :ℤ) = ∑ r∈range (4710 - q),term r := by
      rw [al2,Nat.cast_sum]
      calc _ = ∑ r :Fin 4710,term r.val :=sum_congr rfl fun r _=>(hre r).symm
        _ = ∑ r∈range 4710,term r :=Fin.sum_univ_eq_sum_range term 4710
        _ = _:= by
          symm; refine sum_subset (range_mono (Nat.sub_le _ _)) fun r hr hr' => ?_
          let i:Offset :=⟨r,mem_range.mp hr⟩
          change term i.val=0
          rw [hre i,bmn q i (by simpa only [i,mem_range,not_lt] using hr'),Nat.cast_zero]
    have hsplit : (∑ r∈range (4710 - q),term r) =
        (∑ r∈range 310,term r) + ∑ r∈Ico 310 (4710 - q),term r := by
      simpa only [Nat.Ico_zero_eq_range] using (sum_Ico_consecutive term (Nat.zero_le 310) (by omega :310≤4710 - q)).symm
    have hearly : (∑ r∈range 310,term r)≤(os :ℤ) - rowSave d q:= by
      have hle' : (∑ r∈range 310,term r) ≤
          ∑ r∈range 310,(((countN d 1711 - countN d (1710 - r) :ℕ) :ℤ) -
            if 40≤ r then (saving d q r :ℤ) else 0) :=
        sum_le_sum fun r hr=> by
          let i:Offset :=⟨r,show r<4710 by have :=mem_range.mp hr; omega⟩
          change term i.val≤_; rw [hre i]
          exact dzo hd' (by omega) (he q hq) i
      rw [sum_sub_distrib] at hle'
      have ho' : (∑ r∈range 310,((countN d 1711 - countN d (1710 - r) :ℕ) :ℤ))=os := by
        rw [← Nat.cast_sum,← c6y,← oldSum,hos]
      have hs' : (∑ r∈range 310,if 40≤ r then (saving d q r :ℤ) else 0)=rowSave d q:= by
        rw [show (310 :ℕ)=40+270 by decide,sum_range_add]
        have hz : (∑ r∈range 40,if 40≤ r then (saving d q r :ℤ) else 0)=0 :=
          sum_eq_zero fun r hr=>ite_eq_right (by have :=mem_range.mp hr; omega)
        rw [hz,zero_add,rowSave_eq,Nat.cast_sum]
        exact sum_congr rfl fun j _=>ite_eq_left (by omega)
      linarith
    have hlate : (∑ r∈Ico 310 (4710 - q),term r) ≤ ∑ r∈Ico 310 (4710 - q),denominator (4709-(q:ℤ) - r) :=
      sum_le_sum fun r hr=> by
        obtain ⟨ha,hb⟩:=mem_Ico.mp hr
        let i:Offset :=⟨r,show r<4710 by omega⟩
        change term i.val≤_; rw [hre i]
        exact dzq hd hd' (by omega) (by omega) (he q hq) i hb ha _
    rw [hsum,hsplit,mul_add,← euy q (by omega)]
    exact add_le_add (mul_le_mul_of_nonneg_left hearly (by decide)) (mul_le_mul_of_nonneg_left hlate (by decide))
  have htot:24*(rankBand (fun q r=>aji d q r.val) lo hi:ℤ) ≤
      24*(((hi-lo:ℕ) :ℤ)*os - sv)+tl:= by
    rw [rankBand,Nat.cast_sum,mul_sum]
    calc _ ≤ ∑ q∈Ico lo hi,(24*((os :ℤ) - rowSave d q)+DW (↑(4400 - q:ℕ) :ℤ)) :=sum_le_sum hrow
      _ = ∑ i∈range (hi-lo),(24*((os :ℤ) - rowSave d (lo+i))+DW (↑(4400-(lo+i) :ℕ) :ℤ)) :=
        sum_Ico_eq_sum_range ..
      _=24*(∑ _i∈range (hi-lo),(os :ℤ) - ∑ i∈range (hi-lo),(rowSave d (lo+i) :ℤ)) +
          ∑ i∈range (hi-lo),DW (↑(4400-(lo+i) :ℕ) :ℤ) := by
        rw [sum_add_distrib,← mul_sum,sum_sub_distrib]
      _ = _:= by
        rw [sum_const,card_range,nsmul_eq_mul,← Nat.cast_sum,← saveSum_eq,hsv,← dgC,htl]
  have hb:=htot.trans hcap; omega
theorem plateau_degree {lo hi d q:ℕ}
    (h: (lo=3307∧hi=3335∧d = 1700)∨(lo=3335∧hi=3407∧d = 1650) ∨
      (lo=3407∧hi=3470∧d = 1600)∨(lo=3470∧hi=3537∧d = 1550) ∨
      (lo=3537∧hi=3585∧d = 1500)∨(lo=3585∧hi=3630∧d = 1450) ∨
      (lo=3630∧hi=3678∧d = 1400)) (hq:q∈Ico lo hi) :iO q=d:= by
  obtain ⟨hl,hh⟩:=mem_Ico.mp hq
  rcases h with h | h | h | h | h | h | h <;> rcases h with ⟨rfl,rfl,rfl⟩
  all_goals simp (disch:=omega) only [iO,P6_6.Dj,ite_eq_left,ite_eq_right,min_eq_right]
end qs7wmAa
end
section
set_option autoImplicit true
namespace qXzfTzc
noncomputable section
open aR (ao Shape)
open aFN (Slot)
open MvPolynomial Finset
open scoped BigOperators Pointwise
abbrev Poly :=MvPolynomial (Fin 2) ao
local notation "X₀" => (MvPolynomial.X (0:Fin 2) :Poly)
local notation "X₁" => (MvPolynomial.X (1 :Fin 2) :Poly)
def ex (b c:ℕ) :Fin 2 →₀ ℕ:=Finsupp.single 0 b+Finsupp.single 1 c
@[simp] theorem ex_zero (b c:ℕ) :ex b c 0=b:= by simp [ex]
@[simp] theorem ex_one (b c:ℕ) :ex b c 1=c:= by simp [ex]
theorem ex_unique (e :Fin 2 →₀ ℕ) :ex (e 0) (e 1)=e := by
  ext k
  fin_cases k <;> simp
theorem mon (b c:ℕ) :monomial (ex b c) (1 :ao)=X₀^b*X₁^c:= by
  simp [monomial_fin_two]
def subst:Poly →ₐ[ao] Poly :=MvPolynomial.aeval ![1+X₀,X₀+X₁]
@[simp] theorem subst_zero :subst X₀=1+X₀:= by simp [subst]
@[simp] theorem subst_one :subst X₁=X₀+X₁:= by simp [subst]
private theorem coeff_term (b c j k :ℕ) :
    (X₀^k*(X₀+X₁)^c).coeff (ex b j) =
      if j≤ c∧k+(c-j)=b then (c.choose j:ao) else 0:= by
  rw [MvPolynomial.X_pow_eq_monomial,coeff_monomial_mul']
  have hl:Finsupp.single (0:Fin 2) k≤ex b j↔k≤b:= by
    simp [Finsupp.single_le_iff]
  simp only [hl]
  by_cases hk :k≤b
  · rw [ite_eq_left hk,one_mul,coeff_add_pow]
    simp only [Finset.HasAntidiagonal.mem_antidiagonal,Finsupp.tsub_apply,ex_zero,ex_one,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 :Fin 2)≠0 by decide),Nat.sub_zero]
    by_cases he :b - k+j=c
    · have he' : j≤ c∧k+(c-j)=b:= by omega
      have h' : b-k=c-j:= by omega
      rw [ite_eq_left he,ite_eq_left he',h',Nat.choose_symm he'.1]
    · rw [ite_eq_right he,ite_eq_right (by omega),Nat.cast_zero]
  · rw [ite_eq_right hk,ite_eq_right (by omega)]
theorem coeff_model (b c u v :ℕ) :
    (((1+X₀)^b)*(X₀+X₁)^c).coeff (ex u v) =
      if v≤ c∧c-v≤u then
        (c.choose v :ao)*(b.choose (u-(c-v)) :ao) else 0:= by
  rw [add_comm (1 :Poly) X₀,add_pow,Finset.sum_mul,coeff_sum]
  simp only [one_pow,mul_one]
  have he (k :ℕ) :
      ((X₀^k*(b.choose k :Poly))*(X₀+X₁)^c).coeff (ex u v) =
        (b.choose k :ao)*(if v≤ c∧k+(c-v)=u then (c.choose v :ao) else 0) := by
    rw [← C_eq_coe_nat,mul_comm (X₀^k),mul_assoc,coeff_C_mul,coeff_term]
  simp_rw [he]
  by_cases hv :v≤ c∧c-v≤u
  · rw [ite_eq_left hv,Finset.sum_eq_single (u-(c-v))]
    · rw [ite_eq_left ⟨hv.1,by omega⟩,mul_comm]
    · intro k _ hne
      rw [ite_eq_right (by omega),mul_zero]
    · intro hk
      have hb:b< u-(c-v) := by simp only [Finset.mem_range] at hk; omega
      simp [Nat.choose_eq_zero_of_lt hb]
  · rw [ite_eq_right hv]
    exact Finset.sum_eq_zero fun k _=> by rw [ite_eq_right (by omega),mul_zero]
def project (a :Shape) (q h:ℕ) :Poly →ₗ[ao] (Slot a q→ao) :=
  LinearMap.pi fun r=>if qzLARrc.derivativeIndex r<h then
    (lcoeff ao (ex r.2.val r.1.val)).comp subst.toLinearMap else 0
theorem project_apply (a :Shape) (q h:ℕ) (p:Poly) (r :Slot a q) :
    project a q h p r =
      if qzLARrc.derivativeIndex r<h then
        (subst p).coeff (ex r.2.val r.1.val) else 0:= by
  unfold project
  rw [LinearMap.pi_apply]
  split <;> rfl
theorem project_col {a :Shape} {q d h:ℕ} (s :Slot a q)
    (hs :d≤ s.1.val+s.2.val) :
    project a q h (monomial (ex s.2.val s.1.val) 1) =
      (qmb8rCe.cutMatrix a q d h).col s := by
  funext r
  rw [project_apply,mon]
  simp only [map_mul,map_pow,subst_zero,subst_one,coeff_model,
    Matrix.col_apply,qmb8rCe.cutMatrix,hs,true_and]
  split <;> simp_all
end
end qXzfTzc
end
section
set_option autoImplicit true
namespace qXzfTzc
noncomputable section

open MvPolynomial Finset
open scoped Pointwise
local notation "X₀" => (MvPolynomial.X (0:Fin 2) :Poly)
local notation "X₁" => (MvPolynomial.X (1 :Fin 2) :Poly)
def weight (e :Fin 2 →₀ ℕ) :=e 0+2*e 1
def Bounds (lo hi j c:ℕ) (p:Poly) :Prop :=
  ∀ e∈p.support,lo≤e 0+e 1∧e 0+e 1≤hi∧weight e≤j∧e 1≤ c
theorem Bounds.mono {lo hi j c lo' hi' j' c' : ℕ} {p:Poly}
    (hp:Bounds lo hi j c p) (hl:lo' ≤ lo) (hh:hi≤hi') (hj:j≤j') (hc:c≤ c') :
    Bounds lo' hi' j' c' p:= fun e he =>
  ⟨hl.trans (hp e he).1,(hp e he).2.1.trans hh,(hp e he).2.2.1.trans hj,(hp e he).2.2.2.trans hc⟩
theorem Bounds.add {lo hi j c:ℕ} {p q:Poly}
    (hp:Bounds lo hi j c p) (hq:Bounds lo hi j c q) :Bounds lo hi j c (p+q) := by
  intro e he
  exact (Finset.mem_union.mp (support_add he)).elim (hp e) (hq e)
theorem Bounds.neg {lo hi j c:ℕ} {p:Poly}
    (hp:Bounds lo hi j c p) :Bounds lo hi j c (-p) := fun e he=>hp e (by simpa using he)
private theorem Bounds.mul {l h j c l' h' j' c' : ℕ} {p q:Poly}
    (hp:Bounds l h j c p) (hq:Bounds l' h' j' c' q) :
    Bounds (l+l') (h+h') (j+j') (c+c') (p*q) := by
  intro e he
  obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul _ _ he)
  have ea :=hp a ha
  have eb:=hq b hb
  simp only [weight,Finsupp.add_apply] at *
  omega
theorem bounds_mon (b c:ℕ) :Bounds (b+c) (b+c) (b+2*c) c (monomial (ex b c) 1) := by
  intro e he
  have :ex b c=e := by simpa [support_monomial] using he
  subst e
  simp [weight]
private theorem b1 :Bounds 0 0 0 0 1 := by
  intro e he
  simp only [support_one,Finset.mem_singleton] at he
  subst e
  simp [weight]
private theorem bx :Bounds 1 1 1 0 X₀:= by
  intro e he
  simp only [support_X,Finset.mem_singleton] at he
  subst e
  simp [weight]
private theorem by' : Bounds 1 1 2 1 X₁:= by
  intro e he
  simp only [support_X,Finset.mem_singleton] at he
  subst e
  simp [weight,Finsupp.single_eq_of_ne (show (0:Fin 2)≠1 by decide)]
private theorem Bounds.pow {l h j c:ℕ} {p:Poly} (hp:Bounds l h j c p) (n:ℕ) :
    Bounds (l*n) (h*n) (j*n) (c*n) (p^n) := by
  induction n with
  | zero=>simpa using b1
  | succ n ih=>simpa only [Nat.mul_succ,pow_succ] using ih.mul hp
def orderGe (k :ℕ) (p:Poly) :Prop := ∀ e∈p.support,k≤weight e
theorem orderGe.coeff_eq_zero {k :ℕ} {p:Poly} (hp:orderGe k p) {e :Fin 2 →₀ ℕ}
    (he :weight e<k) :p.coeff e=0 :=
  notMem_support_iff.mp fun hm=>(Nat.not_le_of_lt he) (hp e hm)
private theorem orderGe.mono {k l:ℕ} {p:Poly}
    (hp:orderGe k p) (hl:l≤k) :orderGe l p:= fun e he=>hl.trans (hp e he)
private theorem orderGe.add {k :ℕ} {p q:Poly} (hp:orderGe k p)
    (hq:orderGe k q) :orderGe k (p+q) := fun e he =>
  (Finset.mem_union.mp (support_add he)).elim (hp e) (hq e)
theorem orderGe.neg {k :ℕ} {p:Poly}
    (hp:orderGe k p) :orderGe k (-p) := fun e he=>hp e (by simpa using he)
private theorem orderGe.mul {k l:ℕ} {p q:Poly}
    (hp:orderGe k p) (hq:orderGe l q) :orderGe (k+l) (p*q) := by
  intro e he
  obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul _ _ he)
  have ea :=hp a ha
  have eb:=hq b hb
  simp only [weight,Finsupp.add_apply] at *
  omega
private theorem orderGe.pow {k :ℕ} {p:Poly} (hp:orderGe k p) (n:ℕ) :
    orderGe (k*n) (p^n) := by
  induction n with
  | zero=>simp [orderGe]
  | succ n ih=>simpa only [Nat.mul_succ,pow_succ] using ih.mul hp
private theorem wm (b c:ℕ) :orderGe (b+2*c) (monomial (ex b c) 1) := by
  intro e he
  have :ex b c=e := by simpa [support_monomial] using he
  subst e
  simp [weight]
private def Lead (b c:ℕ) (p:Poly) :=orderGe (b+2*c+1) (p - monomial (ex b c) 1)
private theorem Lead.ord {b c:ℕ} {p:Poly} (hp:Lead b c p) :orderGe (b+2*c) p:= by
  have hp' : orderGe (b+2*c+1) (p - monomial (ex b c) 1) :=hp
  simpa using (hp'.mono (Nat.le_succ _)).add (wm b c)
private theorem Lead.mul {b c d e :ℕ} {p q:Poly} (hp:Lead b c p) (hq:Lead d e q) :
    Lead (b+d) (c+e) (p*q) := by
  have hp' : orderGe (b+2*c+1) (p - monomial (ex b c) 1) :=hp
  have hq' : orderGe (d+2*e+1) (q - monomial (ex d e) 1) :=hq
  have hh:=(hp'.mul hq.ord).add
    ((wm b c).mul hq' |>.mono (show (b+2*c+1)+(d+2*e)≤(b+2*c)+(d+2*e+1) by omega))
  have he : (b+d)+2*(c+e)+1=(b+2*c+1)+(d+2*e) := by omega
  unfold Lead
  rw [he,mon,pow_add,pow_add]
  simp only [mon] at hh
  convert hh using 1
  ring
private theorem Lead.pow {b c:ℕ} {p:Poly} (hp:Lead b c p) (n:ℕ) :
    Lead (b*n) (c*n) (p^n) := by
  induction n with
  | zero=>simp [Lead,mon,orderGe]
  | succ n ih=>simpa only [Nat.mul_succ,pow_succ] using ih.mul hp
private theorem leadMon (b c:ℕ) :Lead b c (monomial (ex b c) 1) := by
  simp [Lead,orderGe]
private abbrev G:Poly :=1-X₀
private abbrev F₁:Poly :=G+X₁
private abbrev F₂:Poly :=X₀*G+X₁
def relation (b c m r s t:ℕ) :Poly :=
  X₀^(b-t)*G^(m-r)*X₁^c*F₁^s*F₂^t
theorem relation_bounds (b c m r s t:ℕ) :
    Bounds (b-t+c+t) (b-t+(m-r)+c+s+2*t)
      (b-t+(m-r)+2*c+2*s+2*t) (c+s+t) (relation b c m r s t) := by
  have hg:Bounds 0 1 1 0 G:= by
    change Bounds 0 1 1 0 (1-X₀)
    rw [sub_eq_add_neg]
    exact Bounds.add (b1.mono (by decide) (by decide) (by decide) (by decide))
      (bx.neg.mono (by decide) (by decide) (by decide) (by decide))
  have h₁:Bounds 0 1 2 1 F₁:=Bounds.add
    (hg.mono (by decide) (by decide) (by decide) (by decide))
    (by'.mono (by decide) (by decide) (by decide) (by decide))
  have h₂:Bounds 1 2 2 1 F₂:=Bounds.add
    ((bx.mul hg).mono (by decide) (by decide) (by decide) (by decide))
    (by'.mono (by decide) (by decide) (by decide) (by decide))
  have h:=((((bx.pow (b-t)).mul (hg.pow (m-r))).mul (by'.pow c)).mul (h₁.pow s)).mul (h₂.pow t)
  simpa [relation,Nat.add_assoc] using h
theorem relation_lead (b c m r s t:ℕ) (ht:t≤b) :
    orderGe (b+2*c+1) (relation b c m r s t - monomial (ex b c) 1) := by
  have hx :Lead 1 0 X₀:= by simpa [mon] using leadMon 1 0
  have hy :Lead 0 1 X₁:= by simpa [mon] using leadMon 0 1
  have h₁:orderGe 1 X₀:= by simpa using hx.ord
  have h₂:orderGe 2 X₁:= by simpa using hy.ord
  have hg:Lead 0 0 G:= by
    simp only [Lead,mon,pow_zero,mul_one,Nat.zero_add,Nat.mul_zero]
    have he :G - 1 = -X₀:= by ring
    rw [he]
    exact h₁.neg
  have hf₁:Lead 0 0 F₁:= by
    have he :F₁-1 = -X₀+X₁:= by ring
    simpa [Lead,mon,he] using h₁.neg.add (h₂.mono (by decide))
  have hf₂:Lead 1 0 F₂:= by
    have he :F₂-X₀ = -(X₀^2)+X₁:= by ring
    simpa [Lead,mon,he] using (h₁.pow 2).neg.add h₂
  have hh:=((((hx.pow (b-t)).mul (hg.pow (m-r))).mul (hy.pow c)).mul (hf₁.pow s)).mul (hf₂.pow t)
  simpa [Lead,relation,Nat.sub_add_cancel ht] using hh
theorem relation_zero (b c m r s t:ℕ) :
    orderGe (m-r+c+2*s+2*t) (subst (relation b c m r s t)) := by
  have hx :orderGe 1 X₀:= by simpa [mon] using (wm 1 0)
  have hy :orderGe 2 X₁:= by simpa [mon] using (wm 0 1)
  have hg:orderGe 1 (subst G) := by simpa using hx.neg
  have h₁:orderGe 2 (subst F₁) := by
    have he :subst F₁=X₁:= by simp [map_sub,map_add]
    rwa [he]
  have h₂:orderGe 2 (subst F₂) := by
    have he :subst F₂ = -(X₀^2)+X₁:= by simp [map_sub,map_add]; ring
    rw [he]
    exact (hx.pow 2).neg.add hy
  have hw:orderGe 1 (subst X₁) := by simpa using hx.add (hy.mono (by decide))
  have hv :orderGe 0 (subst X₀) := fun _ _=>Nat.zero_le _
  have hh:=((((hv.pow (b-t)).mul (hg.pow (m-r))).mul (hw.pow c)).mul (h₁.pow s)).mul (h₂.pow t)
  simpa [relation] using hh
end
end qXzfTzc
end
section
set_option autoImplicit true
namespace q6nKpZc
noncomputable section
open Finset
open scoped BigOperators Classical
open q7F2qKe (cL stops origins partMass originCutter stopPrice globalCap originFreeCap originBudget afterFree lossTail fibreShape lineFee dotResources factorUnit sumPrefix factorRunning factorBill)
open TD (GM J2 FP dYl a3x cZV)
open akZ (yE caQ)
open private swap_tail crE dot_add matrix_dot from ProximityPrize.SubmissionLower.ZHSmgre
private theorem absorb_factor {b u del M Γ F x} {C : @aAT u del M Γ F b x}
    (R:Timeline C) (D:cL b) {o f} (ho:o∈origins b) (hf :f∈C.factors o) :
    (∑ j∈stops b,FP (D.residual o) (J2 (R.stopped o f j)))+(C.line o f).card ≤
      dotResources (factorUnit (D.residual o) (originCutter b o)) (yE f) := by
  have hb:=R.aNI o ho f hf
  rw [crE]
  have he :=
    (a3x (D.fWE o) hb).trans_eq
      (matrix_dot (D.residual o) (fibreShape b o (C.rescue o f)) (yE f))
  have hc:=C.line_price o ho f hf
  cases h:C.rescue o f with
  | false =>
    simp only [h,Bool.false_eq_true,ite_false] at hc
    rw [Nat.eq_zero_of_le_zero hc,Nat.cast_zero,add_zero]
    simpa only [fibreShape,h,Bool.false_eq_true,ite_false] using he
  | true =>
    have ⟨hl,hp⟩:=C.rescue_last o ho f hf h
    have hbox (k :Fin 3) :yE f k≤originBudget b o k := by
      refine (single_le_sum (fun d _=>Nat.zero_le (yE d k)) hf).trans ?_
      refine (single_le_sum (fun i _=>Nat.zero_le (∑ d∈C.factors i,yE d k))
        (mem_filter.mpr ⟨ho,le_rfl⟩)).trans (C.tail o ho k)
    simp only [h,ite_true] at hc
    have hd:=D.absorb o ho hl (yE f) (fun k=>⟨hp k,hbox k⟩)
      (caQ (C.firstFactor o ho f hf).1.ne_zero)
    have hc' : ((C.line o f).card:ℚ)≤lineFee b (yE f) := by exact_mod_cast hc
    have hpay :=add_le_add he (hc'.trans hd)
    simp only [fibreShape,h,ite_true] at hpay
    simpa only [dotResources,sub_mul,sum_sub_distrib,add_sub_cancel] using hpay
private theorem factor_bill_bound {b u del M Γ F x} (C : @aAT u del M Γ F b x)
    (w:ℕ→GM) :
    (∑ o∈origins b,∑ f∈C.factors o,
      dotResources (factorUnit (w o) (originCutter b o)) (yE f))≤factorBill b w:= by
  let g:=factorRunning b w
  let d:= fun i k=>g (i+1) k-g i k
  let a := fun i k=>(∑ f∈C.factors i,(yE f k :ℚ))
  have nonneg (i k) :0≤d i k :=sub_nonneg.mpr (le_max_left _ _)
  have telescope (j k) : (∑ i∈range (j+1),d i k)=g (j+1) k := by
    induction j with
    | zero=>simp [d,g,factorRunning]
    | succ j ih =>
      rw [sum_range_succ,ih]
      dsimp only [d]
      ring
  have hl (o:ℕ) : ∑ f∈C.factors o,dotResources (factorUnit (w o) (originCutter b o)) (yE f) =
      ∑ k,factorUnit (w o) (originCutter b o) k*a o k := by
    simp only [dotResources,a,mul_sum]
    exact sum_comm
  simp only [hl]
  simp only [factorBill,dotResources]
  rw [sum_comm (s :=origins b),sum_comm (s :=origins b)]
  apply sum_le_sum
  intro k _
  calc
    _ ≤ ∑ o∈origins b,(∑ i∈range (o+1),d i k)*a o k := by
      apply sum_le_sum
      intro o _
      rw [telescope]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sum_nonneg fun _ _=>Nat.cast_nonneg _)
    _ = ∑ i∈origins b,d i k * ∑ o∈(origins b).filter (i ≤ ·),a o k :=
      swap_tail _ _ _
    _≤_:= by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (nonneg i k)
      dsimp only [a]
      exact_mod_cast C.tail i hi k
private theorem global_bill_bound {b u del M Γ F x} {C : @aAT u del M Γ F b x}
    (R:Timeline C) (D:cL b) :
    (∑ o∈origins b,∑ j∈stops b,FP (sumPrefix D.global j) (partMass C.factors R.stopped o j)) ≤
      ∑ i∈stops b,FP (D.global i) (globalCap b i) := by
  have h (j) : (∑ o∈origins b,FP (sumPrefix D.global j) (partMass C.factors R.stopped o j)) =
      ∑ k,sumPrefix D.global j k * ∑ o∈origins b,partMass C.factors R.stopped o j k := by
    rw [crE]
    rfl
  rw [sum_comm (s :=origins b) (t:=stops b)]
  simp only [h]
  unfold FP
  rw [sum_comm (s :=stops b) (t:=univ),sum_comm (s :=stops b) (t:=univ)]
  apply sum_le_sum
  intro k _
  unfold sumPrefix stops
  rw [swap_tail]
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (D.global_nonneg i k)
  simpa only [lossTail,stops,sum_comm (s :=origins b)] using R.global_bound i hi k
private theorem free_bill_bound {b u del M Γ F x} {C : @aAT u del M Γ F b x}
    (R:Timeline C) (D:cL b) :
    (∑ o∈origins b,∑ j∈stops b,
      FP (fun k=>if afterFree b≤j then D.free o k else 0) (partMass C.factors R.stopped o j)) ≤
      ∑ o∈origins b,FP (D.free o) (originFreeCap b o) := by
  apply sum_le_sum
  intro o ho
  have eq (j:ℕ) :
      FP (fun k=>if afterFree b≤j then D.free o k else 0) (partMass C.factors R.stopped o j) =
        if afterFree b≤j then FP (D.free o) (partMass C.factors R.stopped o j) else 0:= by
    split <;> simp [FP, *]
  simp only [eq,← sum_filter,crE]
  exact a3x (D.free_nonneg o) (R.free_bound o ho)
theorem weak_dual {b u del M Γ F x} {C : @aAT u del M Γ F b x}
    (R:Timeline C) (D:cL b) :
    (∑ o∈origins b,∑ f∈C.factors o,
      ((∑ j∈stops b,FP (stopPrice b D.a D.h o j) (J2 (R.stopped o f j)))+(C.line o f).card)) ≤
      (∑ i∈stops b,FP (D.global i) (globalCap b i)) +
      (∑ o∈origins b,FP (D.free o) (originFreeCap b o))+factorBill b D.residual:= by
  let g:= fun (_:ℕ) j=>sumPrefix D.global j
  let e := fun o j k=>if afterFree b≤j then D.free o k else 0
  let w:= fun o (_:ℕ)=>D.residual o
  let cost:= fun (v :ℕ→ℕ→GM) o f j=>FP (v o j) (J2 (R.stopped o f j))
  have mix (o) (v :ℕ→ℕ→GM) :
      (∑ f∈C.factors o,∑ j∈stops b,cost v o f j) =
        ∑ j∈stops b,FP (v o j) (partMass C.factors R.stopped o j) := by
    rw [sum_comm]
    simp only [cost,crE]
    rfl
  calc
    _ ≤ ∑ o∈origins b,∑ f∈C.factors o,
        ((∑ j∈stops b,(cost g o f j+cost e o f j+cost w o f j))+(C.line o f).card) := by
      apply sum_le_sum
      intro o ho
      apply sum_le_sum
      intro f _
      apply add_le_add _ le_rfl
      apply sum_le_sum
      intro j hj
      dsimp only [cost]
      rw [← dot_add]
      exact dYl (cZV _) (D.dominate o ho j hj)
    _=(∑ o∈origins b,∑ j∈stops b,FP (g o j) (partMass C.factors R.stopped o j)) +
        (∑ o∈origins b,∑ j∈stops b,FP (e o j) (partMass C.factors R.stopped o j)) +
        ∑ o∈origins b,∑ f∈C.factors o,
          ((∑ j∈stops b,cost w o f j)+(C.line o f).card) := by
      simp only [sum_add_distrib,← mix]
      ring
    _≤_ :=
      add_le_add (add_le_add (global_bill_bound R D) (free_bill_bound R D)) <|
        (sum_le_sum fun o ho=>sum_le_sum fun f hf=>absorb_factor R D ho hf).trans
          (factor_bill_bound C D.residual)
end
end q6nKpZc
end
section
set_option autoImplicit true
namespace qkrKkqa
noncomputable section
open Finset
open scoped Classical
open q6nKpZc
open q7F2qKe (SS)
open cu (Jet)
open gT (Ambient)
open pI (acW pN)
open TD (FP)
variable {b u del M Γ F} {x : @Input b u del M Γ F}
def QV (C:aAT F b x) (o:ℕ) (f :Jet) (j:ℕ) :Finset (Ideal Ambient) :=
  (C.parents o f).filter fun I => ∀ i<j,Pass x i I
def stopped (C:aAT F b x) (o:ℕ) (f :Jet) (j:ℕ) :Finset (Ideal Ambient) :=
  (QV C o f j).filter fun I => ¬ Pass x j I
theorem live_mem {C:aAT F b x} {o f j I} (h:I∈QV C o f j) :
    I∈C.parents o f ∧ ∀ i<j,Pass x i I:=mem_filter.mp h
theorem stopped_mem {C:aAT F b x} {o f j I} (h:I∈stopped C o f j) :
    I∈C.parents o f ∧ ¬ Pass x j I ∧ ∀ i<j,Pass x i I :=
  let ⟨hl,hn⟩:=mem_filter.mp h
  ⟨(live_mem hl).1,hn,(live_mem hl).2⟩
theorem live_anti {C:aAT F b x} {o f i j} (h:i≤j) :
    QV C o f j⊆QV C o f i:= fun _ hm =>
  mem_filter.mpr ⟨(live_mem hm).1,fun t ht=>(live_mem hm).2 t (ht.trans_le h)⟩
structure CutOK (j:ℕ) (I:Ideal Ambient) (Q:acW) :Prop where
  cost : ∀ i,(Q.cost i:ℚ)≤FP (SS b j i) fun k=>pN I k
  Eh : ∀ γ∈Γ,I0 F I γ →
    γ∈Q.direct ∨ ∃ J∈Q.qv,I0 F J γ
end
end qkrKkqa
end
section
set_option autoImplicit true
namespace q4V2ihd
noncomputable section
open P6 (K p jG)
open P5_7_2 (A)
open cu (L)
open gT (kM bbt aSf pZ)
open YY (U7)
structure DescendedMarks {u del} {M:jG u del} {Γ}
    (F:P1.bje A M Γ) (T:Finset K) (J:Ideal kM)
    (Q:MvPolynomial (Fin 2) L) (g H :ℕ) :Prop where
  subset :T⊆Γ
  curve :bbt J g H
  irreducible :Irreducible Q
  projection :J.comap pZ=Ideal.span {MvPolynomial.map U7 Q}
  plane_pos :0<Q.totalDegree
  seed_lt:Q.totalDegree*g<p
  marks : ∀ γ∈T,aSf J (M.label γ) (F.scalar γ)
end
end q4V2ihd
end
