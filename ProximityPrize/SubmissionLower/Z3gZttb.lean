import ProximityPrize.SubmissionLower.ZLcmX9d
set_option Elab.async false
section
set_option autoImplicit true
namespace qeUg7Fa
open P6_6_2 qwbsesc
open xE (Flag oldCount AO m5 BH Jd gd U1 denominator)
open aAZ (anW bwI Jc)
open private bGw from ProximityPrize.SubmissionLower.BK
open aFM (aUK)
def pivot (k :ℕ) :ℕ :=
  min (min 1320 (1590-k)) (max 31 ((2724-k-(((k :ℤ)-240)^2).toNat/7000)/2))
def first (k n:ℕ) :ℕ :=
  let x :ℤ:=(n:ℤ) - pivot k
  let b:=max 0 (min 112 ((250-(k :ℤ))*3/5+3*x-20))
  (138+37*(k :ℤ)/100+(if x<0 then 32 else 36)*x/10 - b/4).toNat
def second (k n:ℕ) :ℕ :=
  let x :ℤ:=(n:ℤ) - pivot k
  (max 0 (min 112 ((250-(k :ℤ))*3/5+3*x-20))).toNat
def powers :kJ:= fun q r =>
  pairPowers 10 3 (first (3000-q) (1709-r.val)) (second (3000-q) (1709-r.val))
def full (n:ℤ) :ℤ:=denominator 1710 - denominator n
def xArg (k n:ℤ) :ℤ:=n+(k+n)/3-1710
def zArg (k n:ℤ) :ℤ:=4*n+3*k-5130
def zo (k n:ℤ) :ℤ :=
  denominator (k+n) - denominator (xArg k n) - denominator (zArg k n)
def base (k n:ℕ) :ℤ:=if n<pivot k then zo k n else full n
private def bY (k n:ℤ) :Flag:=⟨1710,n+1,1710,570,k+n+1⟩
private def residual (k n a b:ℤ) :Flag :=
  ⟨1710-3*a-b,n+1-2*a-3*b,1710-3*a-3*b,570-a-b,k+n+1-3*a-2*b⟩
private theorem dEV (d u c:ℤ) (hu:u≤3*c) :
    U1 d u c=if c<0 then 0 else gd d u:= by
  have hz :gd (d-c-1) (u-3*(c+1))=0:= by
    simp [gd,show u-3*(c+1)<0 by omega]
  simp only [U1,hz,sub_zero]
def j3 (k n:ℕ) :ℤ :=
  let F:=residual k n (first k n) (second k n)
  let lo:=F.lower-1
  let o:=F.order-1
  let balance :=o-F.lower+F.degree
  let jO:=min F.degree (balance/4)+1
  if F.degree<0 || F.upper<0 || F.cap<0 then 0 else
    aUK F.degree F.upper-aUK F.degree (min F.upper lo) -
      (if balance<0 then 0 else aUK F.degree o -
        aUK (F.degree-jO) (o-3*jO) -
        aUK F.degree lo+aUK (F.degree-jO) lo)
private theorem Fi (k n:ℕ) :
    j3 k n=m5 (residual k n (first k n) (second k n)) := by
  let F:=residual k n (first k n) (second k n)
  have h:F.upper=3*F.cap:= by dsimp [F,residual]; ring
  have h₁:F.upper≤3*F.cap:=le_of_eq h
  have h₂:min F.upper (F.lower-1)≤3*F.cap:=(min_le_left _ _).trans h₁
  unfold j3 m5
  change (if F.degree<0 || F.upper<0 || F.cap<0 then _ else _) =
    (if F.degree<0 || F.upper<0 || F.cap<0 then _ else _)
  split
  · rfl
  · rename_i hn
    have hc : ¬ F.cap<0:= by
      intro hh
      simp [hh] at hn
    unfold oldCount AO
    rw [dEV _ _ _ h₁,dEV _ _ _ h₂]
    simp only [ite_eq_right hc,bGw]
    rfl
def iL (k n:ℕ) :ℤ:=base k n - min (base k n) (max 0 (full n - j3 k n))
private theorem degree_eq {q:ℕ} (hq:2550≤q) (hq' : q<2900) :
    iO q=1710 := by
  unfold iO P6_6.Dj
  rw [ite_eq_left (by omega),min_eq_right (by omega),min_eq_right (by omega)]
private theorem den_eq (u:ℤ) (hu:u≤1710) :gd 1710 u=denominator u :=
  (anW _ _ (by decide) (by omega)).trans (bwI _ _ hu)
private theorem den_mono {u v :ℤ} (h:u≤v) (hv :v≤1710) :denominator u≤denominator v := by
  rw [← den_eq u (h.trans hv),← den_eq v hv]
  exact GI.anX 1710 h
private theorem den_nonneg {u:ℤ} (hu:u≤1710) :0≤denominator u:= by
  by_cases h:u<0
  · rw [Jc _ h]
  · simpa only [Jc (-1) (by decide)] using (den_mono (u := -1) (by omega) hu)
theorem pivot_le (k :ℕ) :pivot k≤1320:=(min_le_left _ _).trans (min_le_left _ _)
theorem pivot_add_le (k :ℕ) (hk :k≤450) :k+pivot k≤1590:= by
  have h:pivot k≤1590-k :=(min_le_left _ _).trans (min_le_right _ _)
  omega
private theorem early_nonneg (k n:ℕ) (hk :k≤450) (hn:n<pivot k) :0≤zo k n:= by
  have h₁:=pivot_le k
  have h₂:=pivot_add_le k hk
  unfold zo
  by_cases hx :xArg k n<0
  · rw [Jc _ hx,sub_zero]
    exact sub_nonneg.mpr (den_mono (by unfold zArg; omega) (by omega))
  · have ha :xArg k n≤140:= by unfold xArg; omega
    have hb:zArg k n≤960:= by unfold zArg; omega
    have hc: (1180:ℤ)≤(k :ℤ)+n:= by unfold xArg at hx; omega
    have he :denominator 140+denominator 960≤denominator 1180:= by
      rw [show denominator 140=82068 from rfl,show denominator 960=24845681 from rfl,
        show denominator 1180=46046977 from rfl]
      exact Int.ofNat_le.mpr (by decide :82068+24845681≤46046977)
    have h:=(add_le_add (den_mono ha (by decide)) (den_mono hb (by decide))).trans
      (he.trans (den_mono hc (by omega)))
    omega
private theorem bJS (k n:ℤ) (hn:n≤1710) :oldCount (bY k n)=full n:= by
  simp only [oldCount,bY,add_sub_cancel_right,min_eq_right hn,
    bCi _ _ (le_refl _),bCi _ _ hn,den_eq _ (le_refl _),den_eq _ hn,full]
private theorem allowance_eq (k n:ℕ) (hk :k≤450) (hn:n<pivot k) :
    latticeAllowance (bY k n)=denominator n - denominator (xArg k n) - denominator (zArg k n) := by
  have h₁:=pivot_le k
  have h₂:=pivot_add_le k hk
  let x :ℤ:=1710-((k :ℤ)+n)/3
  let z :ℤ:=3*(min 570 (1709-((k :ℤ)+n))+1)
  have hx :max 0 (min (1710 :ℤ) 1710-((k :ℤ)+n+1+2)/3+1)=x := by
    rw [min_self,max_eq_right (by omega)]
    dsimp [x]
    omega
  have hy :2*max 0 (min (1710 :ℤ) (1710/2) -
      max 0 (((k :ℤ)+n+1-1710+1)/2)+1)=1712 := by
    rw [show max 0 (((k :ℤ)+n+1-1710+1)/2)=0 from max_eq_left (by omega)]
    rfl
  have hg: (120:ℤ)≤ min 570 (1709-((k :ℤ)+n)) :=le_min (by decide) (by omega)
  have hz :3*max 0 (min (min (570:ℤ) 1710) (1710-((k :ℤ)+n+1))+1)=z := by
    rw [show min (570:ℤ) 1710=570 from rfl,
      show (1710 :ℤ)-((k :ℤ)+n+1)=1709-((k :ℤ)+n) by ring,max_eq_right (by omega)]
  have hxy : (n:ℤ)-x=xArg k n:= by simp [x,xArg]; ring
  have hzy :denominator ((n:ℤ)-z)=denominator (zArg k n) := by
    by_cases ht: (570:ℤ)≤1709-((k :ℤ)+n)
    · dsimp [z]
      rw [min_eq_left ht,Jc _ (by omega),Jc (zArg k n) (by unfold zArg; omega)]
    · unfold z
      rw [min_eq_right (by omega)]
      apply congrArg denominator
      unfold zArg
      ring
  unfold latticeAllowance
  simp only [bY,add_sub_cancel_right,hx,hy,hz]
  rw [Jc ((n:ℤ)-1712) (by omega),
    Jc ((n:ℤ)-x-1712) (by dsimp [x]; omega),
    Jc ((n:ℤ)-x-z) (by dsimp [x,z]; omega),
    Jc ((n:ℤ)-1712-z) (by dsimp [z]; omega),
    Jc ((n:ℤ)-x-1712-z) (by dsimp [x,z]; omega),
    hxy,hzy]
  ring
private theorem opposite_le (k n:ℕ) (hk :k≤450) (hn:n<pivot k) :
    (oppositeBound (bY k n) :ℤ)≤zo k n:= by
  have h:=pivot_add_le k hk
  unfold oppositeBound
  simp only [bY,ite_eq_right (show ¬ ((k :ℤ)+n+1≤0) by omega),
    ite_eq_right (show ¬ ((n:ℤ)+1≤0) by omega),add_sub_cancel_right,
    min_eq_right (show (k :ℤ)+n≤1710 by omega),
    bCi _ _ (by omega : (k :ℤ)+n≤1710),bCi _ _ (le_refl (1710 :ℤ)),
    den_eq _ (by omega : (k :ℤ)+n≤1710),den_eq _ (le_refl (1710 :ℤ))]
  rw [← show bY k n=(⟨1710,(n:ℤ)+1,1710,570,(k :ℤ)+n+1⟩:Flag) from rfl,
    bJS _ _ (by have :=pivot_le k; omega),allowance_eq _ _ hk hn]
  have hm:=min_le_left (denominator n - denominator (xArg k n) - denominator (zArg k n))
    (denominator 1710 - denominator ((k :ℤ)+n))
  have hn' := early_nonneg k n hk hn
  unfold full zo at *
  omega
private theorem au9 {q:ℕ} (h₁:2550≤q) (h₂:q<2900) (r :Offset)
    (hr :r.val<1710) :pT q r=bY ((3000-q:ℕ) :ℤ) ((1709-r.val :ℕ) :ℤ) := by
  rw [b3v,degree_eq h₁ h₂]
  unfold bY
  congr 1 <;> omega
private theorem bu2 (k n a b:ℕ) :
    BH (bY k n) (pairPowers 10 3 a b)=residual k n a b:= by
  rw [residual_pair,show Jd 10=⟨3,2,3,1,3⟩ from rfl,
    show Jd 3=⟨1,3,3,1,2⟩ from rfl]
  unfold bY residual
  congr 1 <;> ring
def windowStart (k :ℕ) :ℕ:=pivot k-26
abbrev creditWidth:ℕ:=61
def negative (k n:ℕ) :ℤ :=
  if windowStart k≤n∧n<windowStart k+creditWidth then base k n-iL k n else base k n
theorem negative_le {q:ℕ} (h₁:2550≤q) (h₂:q<2900) (r :Offset)
    (hr :r.val<1710) :
    (xR q r (powers q r) :ℤ)≤negative (3000-q) (1709-r.val) := by
  let k :=3000-q
  let n:=1709-r.val
  change _≤negative k n
  have he :=au9 h₁ h₂ r hr
  have hn: (n:ℤ)≤1710 := by dsimp [n]; omega
  have hk :k≤450:= by dsimp [k]; omega
  have hb: (xR q r (powers q r) :ℤ)≤base k n:= by
    unfold base
    split
    · rename_i ht
      exact (Int.ofNat_le.mpr (min_le_right _ _)).trans
        (he ▸ opposite_le k n hk ht)
    · have hl:=Int.ofNat_le.mpr (block_le_old q r (powers q r))
      have hf :0≤full n:=sub_nonneg.mpr (den_mono hn le_rfl)
      rw [he,bJS _ _ hn,Int.toNat_of_nonneg hf] at hl
      exact hl
  have hp: (xR q r (powers q r) :ℤ)≤ max 0 (full n - j3 k n) := by
    have hl:=Int.ofNat_le.mpr (block_le_residual q r (powers q r))
    change _≤((oldCount (pT q r) -
      m5 (BH (pT q r) (pairPowers 10 3 (first k n) (second k n)))).toNat :ℤ) at hl
    rw [he,bJS _ _ hn,bu2,← Fi] at hl
    change _≤((full n - j3 k n).toNat :ℤ) at hl
    omega
  unfold negative iL
  split
  · have hm:=le_min hb hp
    simpa only [sub_sub_cancel] using hm
  · exact hb
theorem positive_le {q:ℕ} (h₁:2550≤q) (h₂:q<2900) (r :Offset)
    (hr :1710≤ r.val) (p:Fin 11→ℕ) :
    (xR q r p:ℤ)≤denominator (((3000-q:ℕ) :ℤ)-1-(r.val-1710 :ℕ)) := by
  let u:ℤ:=((3000-q:ℕ) :ℤ)-1-(r.val-1710 :ℕ)
  have hu:u≤1710 := by dsimp [u]; omega
  have he :pT q r=⟨1710,1710-(r.val :ℤ),1710,570,u+1⟩:= by
    rw [b3v,degree_eq h₁ h₂]
    congr 1
    dsimp [u]
    omega
  change _≤denominator u
  refine (Int.ofNat_le.mpr (min_le_right _ _)).trans ?_
  rw [he]
  unfold oppositeBound
  dsimp only
  by_cases ho:u<0
  · rw [ite_eq_left (by omega),Jc _ ho]
    rfl
  · rw [ite_eq_right (by omega),add_sub_cancel_right,ite_eq_left (by omega),min_eq_right hu,bCi _ _ hu,
      den_eq _ hu,Int.toNat_of_nonneg (den_nonneg hu)]
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qeUg7Fa
open Finset
open xE (denominator)
open aRR (DW b0n afw)
open aAZ (Jc)
open aFM (xY)
open private arn from ProximityPrize.SubmissionLower.BK
open private aAD bPo from ProximityPrize.SubmissionLower.BH
private def primitive (a r n:ℤ) :ℤ :=
  let A:=21+6*r
  let B:=11+7*r+r^2
  24*n*aAD a r - 24*n*(n-1)*(36*a^2+2*A*a+B) +
    16*n*(n-1)*(2*n-1)*(36*a+A) - 576*n^2*(n-1)^2
private theorem sum_poly (a r :ℤ) (n:ℕ) :
    24*(∑ i∈range n,aAD (a-2*(i:ℤ)) r)=primitive a r n:= by
  induction n with
  | zero=>simp [primitive]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
    unfold primitive aAD
    ring
private def Fy (u:ℤ) (n:ℕ) :ℤ :=
  let v :=u+12*((n:ℤ)-1)
  let m:=min n (v/12+1).toNat
  primitive (v/6) (v%6) (m:ℤ)
private theorem gu0 (u:ℤ) (n:ℕ) :
    48*(∑ i∈range n,denominator (u+12*(i:ℤ)))=Fy u n:= by
  let v :=u+12*((n:ℤ)-1)
  let m:=min n (v/12+1).toNat
  have hrev : (∑ i∈range n,denominator (u+12*(i:ℤ))) =
      ∑ i∈range n,denominator (v-12*(i:ℤ)) := by
    conv_lhs=>rw [← sum_range_reflect (fun i:ℕ=>denominator (u+12*(i:ℤ))) n]
    apply sum_congr rfl
    intro i hi
    have :=mem_range.mp hi
    rw [show ((n-1-i:ℕ) :ℤ)=(n:ℤ)-1-i by omega]
    apply congrArg denominator
    dsimp [v]
    ring
  have hm:m≤n:=min_le_left _ _
  have htrim: (∑ i∈range m,denominator (v-12*(i:ℤ))) =
      ∑ i∈range n,denominator (v-12*(i:ℤ)) := by
    apply sum_subset (range_mono hm)
    intro i hi hj
    have hh:=mem_range.mp hi
    have h' : m≤ i:= by simpa only [mem_range,not_lt] using hj
    exact Jc _ (by dsimp [m] at h'; omega)
  have hrow: (∑ i∈range m,2*denominator (v-12*(i:ℤ))) =
      ∑ i∈range m,aAD (v/6-2*(i:ℤ)) (v%6) := by
    apply sum_congr rfl
    intro i hi
    have hh:=(mem_range.mp hi).trans_le (min_le_right n (v/12+1).toNat)
    rw [bPo _ (by omega)]
    congr 1 <;> omega
  rw [hrev,← htrim,show (48:ℤ)=24*2 from rfl,mul_assoc,mul_sum,hrow,sum_poly]
  rfl
private theorem sum_mul (p n:ℕ) (f :ℕ→ℤ) :
    (∑ i∈range (p*n),f i) = ∑ r :Fin p,∑ i∈range n,f (p*i+r.val) := by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [Nat.mul_succ,sum_range_add,ih,← Fin.sum_univ_eq_sum_range]
    simp only [sum_range_succ,sum_add_distrib]
private theorem sum_residue (p n:ℕ) (hp:0<p) (f :ℕ→ℤ) :
    (∑ i∈range n,f i) =
      ∑ r :Fin p,∑ i∈range (n/p+if r.val<n%p then 1 else 0),f (p*i+r.val) := by
  have hm:=(Nat.mod_lt n hp).le
  let g (r :ℕ) :=f (p*(n/p)+r)
  have hcut: (∑ r∈range (n%p),g r) =
      ∑ r :Fin p,if r.val<n%p then g r.val else 0:= by
    rw [Fin.sum_univ_eq_sum_range (fun r :ℕ=>if r<n%p then g r else 0)]
    calc
      _ = ∑ r∈range (n%p),if r<n%p then g r else 0 :=
        sum_congr rfl fun r hr=>(ite_eq_left (mem_range.mp hr)).symm
      _ = _:=sum_subset (range_mono hm) fun r _ hr =>
        ite_eq_right (fun h=>hr (mem_range.mpr h))
  calc
    _=(∑ i∈range (p*(n/p)),f i) + ∑ r∈range (n%p),g r := by
      dsimp [g]
      rw [← sum_range_add,Nat.div_add_mod]
    _ = _:= by
      rw [sum_mul,hcut,← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      by_cases hr :r.val<n%p
      · simp only [ite_eq_left hr,sum_range_succ,g]
      · simp only [ite_eq_right hr,add_zero]
private def width (p t r :ℕ) :ℕ:=t/p+if r<t%p then 1 else 0
private def partX (k t r :ℕ) :ℤ :=
  Fy ((r :ℤ)+((k :ℤ)+r)/3-1710) (width 9 t r)
private def partZ (k t r :ℕ) :ℤ :=
  Fy (4*(r :ℤ)+3*k-5130) (width 3 t r)
private def atG (f :ℕ→ℤ) :ℕ→ℤ
  | 0=>0
  | n+1=>atG f n+f n
private theorem fbS (f :ℕ→ℤ) (n:ℕ) :atG f n = ∑ i∈range n,f i:= by
  induction n with
  | zero=>simp [atG]
  | succ n ih=>rw [atG,ih,sum_range_succ]
private theorem sum_x (k t:ℕ) :
    48*(∑ i∈range t,denominator (xArg k i))=atG (partX k t) 9:= by
  rw [sum_residue 9 t (by decide),mul_sum,fbS,← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro r _
  unfold partX width
  rw [← gu0]
  congr 1
  apply sum_congr rfl
  intro i _
  push_cast
  rw [xArg]
  apply congrArg denominator
  omega
private theorem sum_z (k t:ℕ) :
    48*(∑ i∈range t,denominator (zArg k i))=atG (partZ k t) 3:= by
  rw [sum_residue 3 t (by decide),mul_sum,fbS,← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro r _
  unfold partZ width
  rw [← gu0]
  congr 1
  apply sum_congr rfl
  intro i _
  push_cast
  unfold zArg
  apply congrArg denominator
  ring
private theorem old_sum (t:ℕ) (ht:t≤1710) :
    48*(∑ i∈range (1710-t),full ((t:ℤ)+i)) =
      48*((1710-t:ℕ) :ℤ)*denominator 1710 - 2*(DW 1710-DW t) := by
  have h:=b0n t (1710-t)
  rw [show (t:ℤ)+((1710-t:ℕ) :ℤ)=1710 by omega] at h
  simp only [full,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
  linear_combination -2*h
private theorem early_sum (k t:ℕ) :
    48*(∑ i∈range t,zo k i) =
      2*(DW ((k :ℤ)+t)-DW k)-atG (partX k t) 9-atG (partZ k t) 3:= by
  simp_rw [zo,sum_sub_distrib,mul_sub,sum_x,sum_z]
  linear_combination 2*b0n k t
private theorem base_sum (k :ℕ) : (∑ n∈range 1710,base k n) =
    (∑ i∈range (pivot k),zo k i) +
    ∑ i∈range (1710-pivot k),full ((pivot k :ℤ)+i) := by
  have h:=Nat.add_sub_of_le ((pivot_le k).trans (by decide :1320≤1710))
  conv_lhs=>rw [← h,sum_range_add]
  congr 1
  · exact sum_congr rfl fun i hi=>ite_eq_left (mem_range.mp hi)
  · refine sum_congr rfl fun i _ => ?_
    simp [base,not_lt.mpr (Nat.le_add_right _ _),Nat.cast_add]
private theorem negative_sum (k :ℕ) : (∑ n∈range 1710,negative k n) =
    (∑ n∈range 1710,base k n)-atG (fun i=>iL k (windowStart k+i)) creditWidth:= by
  let s :=windowStart k
  have hs :s+creditWidth≤1710 := by have :=pivot_le k; dsimp [s,windowStart,creditWidth]; omega
  have h (n:ℕ) :negative k n=base k n-(if s≤n∧n<s+creditWidth then iL k n else 0) := by
    unfold negative s
    split <;> simp
  simp_rw [h,sum_sub_distrib]
  rw [← sum_filter]
  have hfilter : (range 1710).filter (fun n=>s≤n∧n<s+creditWidth)=Ico s (s+creditWidth) := by
    ext n
    rw [mem_filter,mem_range,mem_Ico]
    omega
  rw [hfilter,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left,fbS]
private theorem positive_sum (k :ℕ) (hk :k≤450) :
    24*(∑ g∈range 3000,denominator ((k :ℤ)-1-g))=DW k := by
  have h: (∑ g∈range 3000,denominator ((k :ℤ)-1-g)) =
      ∑ g∈range k,denominator ((k :ℤ)-1-g) := by
    symm
    apply sum_subset (range_mono (by omega))
    intro g _ hg
    have hh:k≤g:= by simpa only [mem_range,not_lt] using hg
    exact Jc _ (by omega)
  rw [h]
  have hr : (∑ g∈range k,denominator ((k :ℤ)-1-g)) = ∑ g∈range k,denominator (g:ℤ) := by
    rw [← sum_range_reflect (fun g:ℕ=>denominator (g:ℤ)) k]
    refine sum_congr rfl fun g hg => ?_
    have :=mem_range.mp hg
    rw [show ((k-1-g:ℕ) :ℤ)=(k :ℤ)-1-g by omega]
  rw [hr]
  simpa only [Int.zero_add,afw 0 le_rfl,sub_zero] using b0n 0 k
private def offsetTerm (k r :ℕ) :ℤ :=
  if r<1710 then negative k (1709-r) else denominator ((k :ℤ)-1-(r-1710 :ℕ))
private theorem offsets_sum (k :ℕ) : (∑ r∈range 4710,offsetTerm k r) =
    (∑ r∈range 1710,negative k r) + ∑ g∈range 3000,denominator ((k :ℤ)-1-g) := by
  change (∑ r∈range (1710+3000),offsetTerm k r)= _
  rw [sum_range_add]
  apply congrArg₂ (· + ·)
  · rw [← sum_range_reflect (negative k) 1710]
    exact sum_congr rfl fun r hr=>ite_eq_left (mem_range.mp hr)
  · refine sum_congr rfl fun g _ => ?_
    simp [offsetTerm,not_lt.mpr (Nat.le_add_right _ _)]
def bvj (k :ℕ) :ℤ :=
  let t:=pivot k
  48*((1710-t:ℕ) :ℤ)*xY 1710 +
    2*(DW ((k :ℤ)+t)-DW 1710+DW t) -
    atG (partX k t) 9-atG (partZ k t) 3 -
    48*atG (fun i=>iL k (windowStart k+i)) creditWidth
theorem aH4 {q:ℕ} (h₁:2550≤q) (h₂:q<2900) :
    48*(P6_6_2.al2 q (powers q) :ℤ)≤bvj (3000-q) := by
  let k :=3000-q
  have hk :k≤450:= by dsimp [k]; omega
  have ht:pivot k≤1710 :=(pivot_le k).trans (by decide)
  have h: (P6_6_2.al2 q (powers q) :ℤ) ≤ ∑ r :P6_6_2.Offset,offsetTerm k r.val := by
    rw [P6_6_2.al2,Nat.cast_sum]
    apply sum_le_sum
    intro r _
    unfold offsetTerm
    split
    · exact negative_le h₁ h₂ r ‹_›
    · exact positive_le h₁ h₂ r (by omega) _
  change _ ≤ ∑ r :Fin 4710,offsetTerm k r.val at h
  rw [Fin.sum_univ_eq_sum_range,offsets_sum,negative_sum k,base_sum] at h
  have hp:=positive_sum k hk
  have he :=early_sum k (pivot k)
  have ho:=old_sum (pivot k) ht
  change _≤bvj k
  unfold bvj
  rw [arn]
  linarith only [h,hp,he,ho]
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qeUg7Fa
open Finset
def total (q:ℕ) :ℕ→ℤ
  | 0=>0
  | n+1=>bvj (3000-q)+total (q+1) n
private theorem asB (q n:ℕ) :
    total q n = ∑ i∈range n,bvj (3000-(q+i)) := by
  induction n generalizing q with
  | zero=>simp [total]
  | succ n ih =>
    rw [total,ih,sum_range_succ',add_comm,Nat.add_zero]
    apply congrArg (· + bvj (3000-q))
    refine sum_congr rfl fun i _ => ?_
    rw [show q+1+i=q+(i+1) by omega]
theorem asA {q n:ℕ} {v w:ℤ}
    (hv :bvj (3000-q)=v) (hw:total (q+1) n=w) :total q (n+1)=v+w:= by
  rw [total,hv,hw]
private theorem bh5 (q m n:ℕ) :total q (m+n)=total q m+total (q+m) n:= by
  induction m generalizing q with
  | zero=>simp [total]
  | succ m ih =>
    rw [show m+1+n=(m+n)+1 by omega]
    simp only [total,ih,add_assoc]
    rw [Nat.add_comm 1 m]
theorem total_append {q m n:ℕ} {v w:ℤ}
    (hv :total q m=v) (hw:total (q+m) n=w) :total q (m+n)=v+w:= by
  rw [bh5,hv,hw]
theorem dyl {q n:ℕ} (h₁:2550≤q) (h₂:q+n≤2900) :
    48*(P6_6_2.rankBand powers q (q+n) :ℤ)≤total q n:= by
  rw [P6_6_2.rankBand,Nat.cast_sum,mul_sum,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left,asB]
  exact sum_le_sum fun i hi=>aH4 (by omega) (by have :=mem_range.mp hi; omega)
end qeUg7Fa
end
