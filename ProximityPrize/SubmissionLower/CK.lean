import ProximityPrize.SubmissionLower.P
set_option Elab.async false
open _root_ renaming Bool.false_eq_true→mD,Bool.false_or→lJ,Int.ofNat_sub→cy,Int.toNat_of_nonneg→n5,Nat.cast_add→nI,Nat.cast_ofNat→nX,decide_false→nq,ite_eq_right→lI,ite_false→c9,min_eq_right→lz,xE.denominator→aU
set_option autoImplicit true
section
namespace abF
open xE GI
def CY (u:ℕ) :ℕ :=
  if u == 0 then 0 else
    let q:=(u - 1)/6
    let r :=(u - 1) % 6
    (q*(q*(12*q+21+6*r)+11+r*(7+r))+2+r*(r+1))/2
def JY (d u:ℕ) :ℕ :=
  if u≤d+1 then CY u else
    let u:=min u (3*d+1)
    (CY u+CY (u-(2*d+3))+CY (u-(2*d+4))+CY (u-(2*d+5))) -
      (CY (u-(d+1))+CY (u-(d+2))+CY (u-(d+3)))
def RL (d u r :ℕ) :ℕ :=
 if d< r then 0 else JY (d-r) u
def Yp (d l u o r :ℕ) :ℕ :=
 (JY d u+RL d (o-3*r) r)-(JY d o+RL d l r)
def aD6 (s j:ℕ) :ℕ :=
  let o:=4650-(s+j)
  let r :=(4649-s)/4+1
  (125576826+RL 1650 (o-3*r) r) -
    (CY o+RL 1650 (1650-j) r)
def afm (s j:ℕ) (p:kJ) :ℕ :=
 let a :=p.value
 let b:=p.top
 let c:=p.Ej
 if 1650<a+b+3*c || 550<b+c || j+1<c || 4649<s+a+4*c then 0 else
 let d:=1650-(a+b+3*c)
 let l:=1650-(j+3*b+2*c)
 let u:=1651-3*(b+c)
 let o:=4650-(s+j+2*b+3*c)
 let r :=min d ((4649-(s+a+4*c))/4)+1
 min 30000000 (Yp d l u o r)-aD6 s j
private theorem XK (n:ℤ) :2*(n*(n - 1)/2)=n*(n - 1) := by
 have h: (2 :ℤ)∣n*(n - 1) := by
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  · exact dvd_mul_of_dvd_left (by omega : (2 :ℤ)∣n) _
  · exact dvd_mul_of_dvd_right (by omega : (2 :ℤ)∣n - 1) _
 rw [mul_comm,Int.ediv_mul_cancel h]
private theorem aT9 (n:ℕ) :
    (CY n:ℤ)=aU ((n:ℤ) - 1) := by
  cases n with
  | zero=>decide
  | succ n =>
    rw [CY,lI (by simp),Nat.succ_sub_one]
    push_cast
    rw [show (n:ℤ)+1 - 1=n by omega,aU,lI (by omega)]
    let q:=(n:ℤ)/6
    let r :=(n:ℤ) % 6
    change (q*(q*(12*q+21+6*r)+11+r*(7+r))+2+r*(r+1))/2 =
      1+r*(r+1)/2+q*(22+7*r+r*(r-1)/2) +
        (57+6*r)*(q*(q-1)/2)+6*q*(q-1)*(q-2)
    have h:=XK (r+1)
    rw [show (r+1)*(r+1-1)=r*(r+1) by ring] at h
    have heq :q*(q*(12*q+21+6*r)+11+r*(7+r))+2+r*(r+1) =
        2*(1+r*(r+1)/2+q*(22+7*r+r*(r-1)/2) +
          (57+6*r)*(q*(q-1)/2)+6*q*(q-1)*(q-2)) := by
      linear_combination -h - q*XK r-(57+6*r)*XK q
    rw [heq]
    omega
private theorem dV6 (n k :ℕ) :
   (CY (n - k) :ℤ)=aU ((n:ℤ) - 1 - k) := by
 rw [aT9]
 by_cases h:k≤n
 · rw [cy h]
   congr 1
   omega
 · have hz :n - k=0:= by omega
   simp [hz,aU ,show (n:ℤ) - 1 - k<0 by omega]
private theorem bZg (d:ℕ) (u:ℤ) :0≤gd (d:ℤ) u:= by
 by_cases h:u<0
 · simp [gd,h]
 · have hm:=anX d (show (-1 :ℤ)≤u by omega)
   simpa [gd] using hm
private theorem aTW (d u:ℕ) :
    (JY d u:ℤ)=gd (d:ℤ) ((u:ℤ) - 1) := by
  by_cases h0:u=0
  · subst u
    simp [JY,CY,gd]
  let n:=min u (3*d+1)
  have hv :min ((u:ℤ) - 1) (3*d)=(n:ℤ) - 1 := by
    simp only [n,min_def]
    split <;> split <;> omega
  have hd0 : ¬ (d:ℤ)<0:= by omega
  have hu0 : ¬ (u:ℤ) - 1<0:= by omega
  rw [JY]
  by_cases h:u≤d+1
  · rw [ite_eq_left h,aT9]
    have hn:n=u:=min_eq_left (by omega)
    have hz (z :ℤ) (hz :z<0) :aU z=0:= by simp [aU,hz]
    simp (disch:=omega) only [gd,hd0,hu0,nq,lJ,
      mD,c9,hv,hn,hz,sub_zero,add_zero]
  · rw [lI h]
    let pos :=CY n+CY (n-(2*d+3))+CY (n-(2*d+4))+CY (n-(2*d+5))
    let neg:=CY (n-(d+1))+CY (n-(d+2))+CY (n-(d+3))
    change ((pos - neg:ℕ) :ℤ)= _
    have hn:n≤3*d+1 :=min_le_right _ _
    have hlast :aU ((n:ℤ) - 1 - 3*d-6)=0:= by
      simp [aU,show (n:ℤ) - 1 - 3*d-6<0 by omega]
    have he : (pos :ℤ) - neg=gd d ((u:ℤ) - 1) := by
      simp only [pos,neg,nI,dV6,Nat.cast_mul,nX]
      rw [aT9]
      simp only [gd,hd0,hu0,nq,lJ,mD,
        c9,hv,hlast,sub_zero]
      ring_nf
    have hpos :0≤(pos :ℤ) - neg:=he ▸ bZg d _
    rwa [← Int.toNat_sub,n5 hpos]
private theorem bDz (d:ℕ) (u:ℤ) :
   (JY d u.toNat :ℤ)=gd d (u - 1) := by
 rw [aTW]
 by_cases h:0≤u
 · rw [n5 h]
 · simp [Int.toNat_of_nonpos (by omega :u≤0),gd,show u - 1<0 by omega]
private theorem bof (d r :ℕ) (u:ℤ) :
   (RL d u.toNat r :ℤ)=gd ((d:ℤ) - r) (u - 1) := by
 unfold RL
 by_cases h:d< r
 · simp [h,gd,show (d:ℤ) - r<0 by omega]
 · rw [lI h,bDz,cy (by omega :r≤d)]
private def balance (F:Flag) :ℤ:=F.order - 1-F.lower+F.degree
private theorem bCi (d u f :ℤ) (hf :0≤f) (hu:u≤3*f) :
  U1 d u f=gd d u:= by
 simp [U1,not_lt.mpr hf,gd,show u-3*(f+1)<0 by omega]
private theorem b64 (F:Flag) (hd:0≤F.degree) (hu:0≤F.upper)
    (hc:0≤F.cap) (hcap:F.upper≤3*F.cap) (hl:F.lower - 1≤F.upper)
    (hb:0≤balance F) :
    let r :=min F.degree (balance F/4)+1
    m5 F =
      gd F.degree F.upper+gd (F.degree - r) (F.order - 1 - 3*r) -
        (gd F.degree (F.order - 1)+gd (F.degree - r) (F.lower - 1)) := by
  unfold m5 oldCount AO
  simp only [not_lt.mpr hd,not_lt.mpr hu,not_lt.mpr hc,nq,lJ,mD,c9,lz hl]
  have hb' : ¬ F.order - 1-F.lower+F.degree<0:=not_lt.mpr hb
  simp only [hb',c9]
  rw [bCi _ _ _ hc hcap,bCi _ _ _ hc (hl.trans hcap)]
  simp only [balance]
  ring
private theorem beR (F:Flag) (d u r :ℕ) (hd:F.degree=d)
  (hu:F.upper=(u:ℤ) - 1) (hu0:0≤F.upper) (hc:0≤F.cap)
  (hcap:F.upper≤3*F.cap) (hl:F.lower - 1≤F.upper) (hb:0≤balance F)
  (hr : (r :ℤ)=min F.degree (balance F/4)+1) :
  Yp d F.lower.toNat u F.order.toNat r=(m5 F).toNat := by
 rw [b64 F (by omega) hu0 hc hcap hl hb,← hr,hd,hu]
 unfold Yp
 rw [← Int.toNat_sub]
 push_cast
 rw [aTW,bDz,bof]
 have ht:F.order.toNat - 3*r=(F.order-3*(r :ℤ)).toNat := by omega
 rw [ht,bof]
 rw [show F.order-3*(r :ℤ) - 1=F.order - 1 - 3*r by ring]
end abF
end
