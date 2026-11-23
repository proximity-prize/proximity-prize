import ProximityPrize.SubmissionLower.DY
import ProximityPrize.SubmissionLower.ZLcmX9d
set_option Elab.async false
section
set_option autoImplicit true
namespace q5wVSFc
open P6_6_2
open qwbsesc (b3v pairPowers residual_pair bCi block_le_residual)
open xE (Flag Jd gd denominator oldCount m5 AO BH)
open aAZ (aej amM anW)
open ba2 (triple)
open private bDB bZd fWE from ProximityPrize.SubmissionLower.DY
open Finset
open scoped BigOperators
def En (d q:ℕ) :ℕ:=(d+3003 - q)/4
def aji (q:ℕ) (r :Offset) :Fin 11→ℕ :=
  pairPowers 0 0 (iO q+3000 - q-4*r.val) 0
private def bY (d b j:ℤ) :Flag:=⟨d,1710-j,1710,570,b-j⟩
private theorem initial_chart {q d:ℕ} (h:iO q=d) (r :Offset) :
    pT q r=bY d (4710-(q:ℤ)) r.val := by rw [b3v,h]; rfl
private theorem bJR (d b j:ℤ) (hj:0≤j) :
    oldCount (bY d b j)=gd d 1710 - gd d (1709-j) := by
  simp only [oldCount,bY,show (1710 :ℤ)-j-1=1709-j by ring,
    min_eq_right (by omega :1709-j≤1710),bCi d 1710 le_rfl,
    bCi d (1709-j) (by omega)]
private theorem kernel_chart (d b j:ℤ) (hd:0≤d) :
    m5 (bY d b j)=oldCount (bY d b j) - AO (bY d b j) := by
  simp [m5,bY,not_lt.mpr hd]
private theorem gAJ {b j:ℤ} (hb:b≤1032) (hj:0≤j) :
    let e :=1710-b+4*j
    AO (bY e b j) =
      gd e (b-1-j) - gd (e-j) (b-1-4*j) -
        gd e (1709-j)+gd (e-j) (1709-j) := by
  dsimp only
  have hbal:b-j-1-(1710-j)+(1710-b+4*j)=4*j-1 := by ring
  by_cases hz :j=0
  · subst j
    simp [AO,bY]
  have hq: (4*j-1)/4+1=j:= by omega
  have hm: (4*j-1)/4≤1710-b+4*j:= by omega
  simp only [AO,bY,hbal,show ¬4*j-1<0 by omega,ite_false,
    min_eq_right hm,hq]
  rw [show b-j-1=b-1-j by ring,show b-1-j-3*j=b-1-4*j by ring,
    show 1710-j-1=1709-j by ring]
def Ig (d b j:ℤ) :ℤ :=
  -triple (1710-d)+denominator (b-1-j) - denominator (b-4*j-4)+triple (1709-j-d) -
    triple (2*b-1711-5*j)+triple (2*b-1711-7*j) -
    triple (2*b-1712-8*j)+triple (2*b-1713-7*j)
private theorem gpp {d b j:ℤ} (hd:1050≤d) (hb:b≤1032) (hj:0≤j) :
    oldCount (bY d b j) - m5 (bY (1710-b+4*j) b j)=Ig d b j:= by
  let e :=1710-b+4*j
  have he :2≤e∧2≤e-j:= by dsimp [e]; omega
  rw [kernel_chart e b j (by omega),bJR _ _ _ hj,bJR _ _ _ hj,
    gAJ hb hj]
  change gd d 1710 - gd d (1709-j) -
    (gd e 1710 - gd e (1709-j) -
      (gd e (b-1-j) - gd (e-j) (b-1-4*j) -
        gd e (1709-j)+gd (e-j) (1709-j)))= _
  have hu: (1710 :ℤ)≤3*e∧1709-j≤3*(e-j)∧b-1-j≤2*e+2 ∧
      b-1-4*j≤2*(e-j)+2 := by dsimp [e]; omega
  rw [bDB (by omega :2≤d) (by omega : (1710 :ℤ)≤2*d+2),
    bDB (by omega :2≤d) (by omega :1709-j≤2*d+2),
    bZd he.1 hu.1,bDB he.1 hu.2.2.1,bDB he.2 hu.2.2.2,
    bZd he.2 hu.2.1]
  rw [show 1710-e=b-4*j by dsimp [e]; ring,
    show 1710-2*e-2=2*b-1712-8*j by dsimp [e]; ring,
    show b-1-j-e=2*b-1711-5*j by dsimp [e]; ring,
    show b-1-4*j-(e-j)=2*b-1711-7*j by dsimp [e]; ring,
    show 1709-j-(e-j)=b-1-4*j by dsimp [e]; ring,
    show 1709-j-2*(e-j)-2=2*b-1713-7*j by dsimp [e]; ring]
  have ht:triple (b-4*j) - triple (b-1-4*j) =
      denominator (b-1-4*j) - denominator (b-4*j-4) := by
    unfold triple
    ring_nf
  unfold Ig
  linear_combination ht
private theorem value_flag:Jd 0=⟨1,0,0,0,0⟩:=rfl
theorem bpg {q d:ℕ} (hl:3678≤q) (hd:1050≤d) (he :iO q=d)
    (r :Offset) (hr :r.val<En d q) :
    (xR q r (aji q r) :ℤ)≤Ig d (4710-(q:ℤ)) r.val := by
  let b:ℤ:=4710-(q:ℤ)
  let j:ℤ:=r.val
  have hp: (↑(d+3000 - q-4*r.val :ℕ) :ℤ)=d+3000 - q-4*j:= by
    unfold En at hr
    omega
  have hres :BH (pT q r) (aji q r)=bY (1710-b+4*j) b j:= by
    rw [aji,he,residual_pair,value_flag,initial_chart he r,hp]
    dsimp [bY,b,j]
    congr 1 <;> ring
  have h:=block_le_residual q r (aji q r)
  have hn:=fWE (pT q r) (aji q r)
  have hs :=Int.ofNat_le.mpr h
  rw [Int.toNat_of_nonneg hn,hres,initial_chart he r,
    gpp (by omega : (1050:ℤ)≤d) (by omega : (4710 :ℤ) - q≤1032) (Int.natCast_nonneg _)] at hs
  exact hs
def Xl (d q j:ℕ) :ℤ :=
  let k :ℤ:=En d q
  let b:ℤ:=4709-(q:ℤ)
  aej d (b-j)-aej ((d:ℤ)-k) (b-3*k-j) -
    aej d (1709-j)+aej ((d:ℤ)-k) (1709-j)
def KW (d q j:ℕ) :ℤ :=
  let k :ℤ:=En d q
  let b:ℤ:=4710-(q:ℤ)
  amM d (b-j)-amM ((d:ℤ)-k) (b-3*k-j) -
    amM d (1710-j)+amM ((d:ℤ)-k) (1710-j)
private theorem target_late {q d:ℕ} (hl:3678≤q) (hu:q<4020)
    (hd:1050≤d) (he :iO q=d) (r :Offset) :
    AO (pT q r)=Xl d q r.val := by
  let k :=En d q
  have hk : (k :ℤ)=((2999:ℤ)-(q:ℤ)+d)/4+1 := by
    unfold k En
    omega
  have he' : 2≤(d:ℤ)-k∧1709≤2*((d:ℤ)-k)+2 := by omega
  rw [initial_chart he r,AO]
  dsimp only [bY]
  have hb: (4710 :ℤ)-q-r.val-1-(1710-r.val)+d = 2999-q+d:= by ring
  simp only [hb,show ¬(2999:ℤ)-q+d<0 by omega,ite_false,
    min_eq_right (show (2999-(q:ℤ)+d)/4≤d by omega),← hk]
  rw [anW _ _ (by omega : (2 :ℤ)≤d) (by omega),
    anW _ _ he'.1 (by omega),
    anW _ _ (by omega : (2 :ℤ)≤d) (by omega),
    anW _ _ he'.1 (by omega)]
  dsimp only [ Xl,k]
  congr 2 <;> ring
theorem late_le {q d:ℕ} (hl:3678≤q) (hu:q<4020)
    (hd:1050≤d) (he :iO q=d) (r :Offset) :
    (xR q r (aji q r) :ℤ)≤Xl d q r.val := by
  let F:=pT q r
  have ht:0≤AO F:= by
    rw [← aYY.proof aw7.proof F]
    exact Int.natCast_nonneg _
  have hk :m5 F=oldCount F - AO F:= by
    rw [show F=pT q r from rfl,initial_chart he r]
    exact kernel_chart _ _ _ (by omega)
  rw [← target_late hl hu hd he]
  refine (Int.ofNat_le.mpr (min_le_left _ _)).trans ?_
  unfold prescribedBound
  change (↑(if F.order≤0 then (0:ℕ) else _) :ℤ)≤AO F
  split
  · simpa only [Nat.cast_zero] using ht
  · have hle :m5 F≤ max 0 (max (m5 F)
        (m5 (BH F (aji q r)))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hm:=min_le_right (oldCount (alp q r))
      (oldCount F - max 0 (max (m5 F) (m5 (BH F (aji q r)))))
    change ((min (oldCount (alp q r))
      (oldCount F - max 0 (max (m5 F) (m5 (BH F (aji q r)))))).toNat :ℤ)
      ≤ AO F
    omega
theorem zero_block {q:ℕ} (hq:q<4710) (r :Offset) (hr :4710-q≤ r.val) :
    xR q r (aji q r)=0:= by
  apply Nat.eq_zero_of_le_zero
  refine (min_le_left _ _).trans ?_
  unfold prescribedBound
  rw [ite_eq_left (show (pT q r).order≤0 by rw [b3v]; dsimp; omega)]
end q5wVSFc
end
section
set_option autoImplicit true
namespace q5wVSFc
open P6_6_2

open aAZ (aQt)
open ba2 (triple)
open private lower upper one c2u HD bPh cui gEr aJD from ProximityPrize.SubmissionLower.DY
open Finset
open scoped BigOperators
private theorem eux (d q j:ℕ) :
    KW d q j - KW d q (j+1)=24*Xl d q j:= by
  simp only [KW,Xl,Nat.cast_add,Nat.cast_one]
  linear_combination (norm:=ring_nf) aQt (d:ℤ) (4710-(q:ℤ)) j -
    aQt ((d:ℤ)-En d q) (4710-(q:ℤ)-3*En d q) j -
    aQt (d:ℤ) 1710 j +
    aQt ((d:ℤ)-En d q) 1710 j
private theorem euy (d q j n:ℕ) :
    24*(∑ k∈range n,Xl d q (j+k))=KW d q j - KW d q (j+n) := by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,← eux,← Nat.add_assoc]
    ring
private def bNN (d b:ℤ) (r :ℕ) :ℤ :=
  -(432*(r :ℤ)*triple (1710-d))+one (b-1) r-lower (b-4) 4 r +
    cui (1709-d) r - HD lower (2*b-1711) 5 r+HD upper (2*b-1711) 7 r -
    HD lower (2*b-1712) 8 r+HD upper (2*b-1713) 7 r
private theorem gpr (d b:ℤ) (r :ℕ) :
    432*(∑ j∈range r,Ig d b j)≤bNN d b r := by
  have h₀:=(aJD (b-4) (m:=4) (by decide) r).1
  have h₁:=(bPh (2*b-1711) (m:=5) (by decide) r).1
  have h₂:=(bPh (2*b-1711) (m:=7) (by decide) r).2
  have h₃:=(bPh (2*b-1712) (m:=8) (by decide) r).1
  have h₄:=(bPh (2*b-1713) (m:=7) (by decide) r).2
  simp only [Ig,sum_add_distrib,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,
    mul_sub,mul_add,c2u,gEr,
    show ∀ j:ℤ,b-4*j-4=b-4-4*j from fun j=> by ring,
    show ∀ j:ℤ,1709-j-d = 1709-d-j from fun j=> by ring]
  unfold bNN
  norm_num only [Nat.cast_ofNat] at h₀ h₁ h₂ h₃ h₄
  rw [show (432 :ℤ)*((r :ℤ) * -triple (1710-d)) = -(432*(r :ℤ)*triple (1710-d)) by ring]
  omega
def apg (d q:ℕ) :ℤ :=
  let r :=En d q
  bNN d (4710-(q:ℤ)) r+18*(KW d q r - KW d q (4710-q))
theorem cfP {q d:ℕ} (hl:3678≤q) (hu:q<4020)
    (hd:1050≤d) (hd' : d≤1350) (he :iO q=d) :
    432*(al2 q (aji q) :ℤ)≤apg d q:= by
  let r :=En d q
  let b:=4710-q
  have hr :r≤b:= by unfold r b En; omega
  have hb:b≤4710 := by unfold b; omega
  let f (k :ℕ) :ℤ:=if h:k<4710 then xR q ⟨k,h⟩ (aji q ⟨k,h⟩) else 0
  have hf : (al2 q (aji q) :ℤ) = ∑ k∈range b,f k := by
    rw [al2,Nat.cast_sum]
    have hh (k :Offset) : (xR q k (aji q k) :ℤ)=f k.val := by
      simp only [f]
      rw [dite_eq_left (show k.val<4710 from k.isLt)]
    simp_rw [hh]
    rw [Fin.sum_univ_eq_sum_range f]
    change (∑ k∈range 4710,f k)= _
    symm
    refine sum_subset (range_mono hb) fun k hk hk' => ?_
    have hkn:=mem_range.mp hk
    have hk'' := not_lt.mp (mt mem_range.mpr hk')
    simp only [f]
    rw [dite_eq_left hkn,zero_block (by omega :q<4710) ⟨k,hkn⟩ hk'',Nat.cast_zero]
  have hs : (∑ k∈range b,f k)=(∑ k∈range r,f k) +
      ∑ k∈range (b-r),f (r+k) := by
    conv_lhs=>rw [← Nat.add_sub_of_le hr,sum_range_add]
  have hE : (∑ k∈range r,f k) ≤ ∑ k∈range r,Ig d (4710-(q:ℤ)) k := by
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.mp hk
    have hkn:k<4710 := by omega
    simp only [f]
    rw [dite_eq_left hkn]
    exact bpg hl hd he ⟨k,hkn⟩ hk'
  have hL: (∑ k∈range (b-r),f (r+k)) ≤ ∑ k∈range (b-r),Xl d q (r+k) := by
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.mp hk
    have hkn:r+k<4710 := by omega
    simp only [f]
    rw [dite_eq_left hkn]
    exact late_le hl hu hd he ⟨r+k,hkn⟩
  rw [hf,hs,mul_add]
  have he' := (mul_le_mul_of_nonneg_left hE (by decide : (0:ℤ)≤432)).trans
    (gpr d (4710-(q:ℤ)) r)
  have hl' := mul_le_mul_of_nonneg_left hL (by decide : (0:ℤ)≤24)
  rw [euy,Nat.add_sub_of_le hr] at hl'
  change _≤bNN d (4710-(q:ℤ)) r+18*(KW d q r - KW d q b)
  omega
end q5wVSFc
end
section
set_option autoImplicit true
namespace q5wVSFc
open P6_6_2
open qwbsesc (aak aGH)
open Finset
open scoped BigOperators
private def ay (d:ℕ) :ℕ→List ℕ→Prop
  | _,[]=>True
  | q,a :: xs=>apg d q=(a :ℤ)∧ay d (q+1) xs
private theorem checked_cons {d q a :ℕ} {xs :List ℕ}
    (h:apg d q=(a :ℤ)) (hx :ay d (q+1) xs) :ay d q (a::xs) :=
  ⟨h,hx⟩
private theorem checked_sum {d q:ℕ} {xs :List ℕ} (h:ay d q xs) :
    (∑ k∈range xs.length,apg d (q+k))=(xs.sum:ℤ) := by
  induction xs generalizing q with
  | nil=>simp
  | cons a xs ih =>
    obtain ⟨ha,hx⟩:=h
    rw [List.length_cons,sum_range_succ',List.sum_cons,Nat.cast_add,Nat.add_zero,ha]
    have hshift: (∑ k∈range xs.length,apg d (q+(k+1))) =
        ∑ k∈range xs.length,apg d ((q+1)+k) :=
      sum_congr rfl fun k _=>congrArg (apg d) (by omega)
    rw [hshift,ih hx,add_comm]
private def asu (q:ℕ) :ℕ :=
  if q<3733 then 1350 else if q<3781 then 1300 else if q<3830 then 1250 else
  if q<3878 then 1200 else if q<3927 then 1150 else if q<3975 then 1100 else 1050
private theorem taper_anti:Antitone asu:= by
  intro a b hab
  unfold asu
  split_ifs <;> omega
private theorem degree {q:ℕ} (hq:3678≤q) (hh:q<4020) :
    iO q=asu q:= by
  unfold asu
  unfold iO P6_6.Dj
  simp only [show ¬q<3307 by omega,show ¬q<3335 by omega,show ¬q<3407 by omega,
    show ¬q<3470 by omega,show ¬q<3537 by omega,show ¬q<3585 by omega,
    show ¬q<3630 by omega,show ¬q<3678 by omega,hh,ite_true,ite_false]
  split_ifs <;> omega
private theorem from_rows {d lo hi cap total:ℕ} {xs :List ℕ}
    (hl:3678≤lo) (hu:hi≤4020) (hd:1050≤d) (hd' : d≤1350)
    (hlen:lo + xs.length=hi) (htotal:xs.sum=total) (hc:total≤432*cap)
    (hleft:asu lo=d) (hright:asu (hi-1)=d)
    (h:ay d lo xs) :aak lo hi cap:= by
  refine ⟨aji,?_⟩
  have hs : (∑ q∈Ico lo hi,apg d q)=(total:ℤ) := by
    rw [sum_Ico_eq_sum_range,← hlen,Nat.add_sub_cancel_left,checked_sum h,htotal]
  have hr :432*(rankBand aji lo hi:ℤ)≤total:= by
    rw [← hs,rankBand,Nat.cast_sum,mul_sum]
    apply sum_le_sum
    intro q hq
    obtain ⟨l,u⟩:=mem_Ico.mp hq
    have hqlo:=hl.trans l
    have hqhi:=u.trans_le hu
    have hupper :=taper_anti l
    have hlower :=taper_anti (show q≤hi-1 by omega)
    rw [hleft] at hupper
    rw [hright] at hlower
    exact cfP hqlo hqhi hd hd' ((degree hqlo hqhi).trans (le_antisymm hupper hlower))
  omega
private def r1 :List ℕ:=[
  0x20d475d875e,0x20b15f8c10e,0x208e5f5d3be,0x206b7548bb4,0x2048a14b554,0x2025f0cf174,
  0x20035651224,0x1fe0d1ce5ba,0x1fbe6343b0a,0x1f9c181a7bc,0x1f79e2d06da,0x1f57c362066,
  0x1f35b9cc1ea,0x1f13d3783a2,0x1ef202e3780,0x1ed0480ae92,0x1eaea2eaccc,0x1e8d20ec96e,
  0x1e6bb48dd00,0x1e4a5dcadce,0x1e291ca059c,0x1e07fe775da,0x1de6f5cd7d6,0x1dc6029f1d0,
  0x1da524e84c8,0x1d846a12db0,0x1d63c49bafc,0x1d43347f226,0x1d22b9b9998,0x1d0261b43e2,
  0x1ce21eec608,0x1cc1f15de58,0x1ca1d9054c8,0x1c81e34bdf8,0x1c6202ae4ae,0x1c423728fde,
  0x1c2280b8064,0x1c02ecc492a,0x1be36dcb754,0x1bc403c8b9a,0x1ba4aeb8dd4,0x1b857c04696,
  0x1b665e28514,0x1b475520e26,0x1b2860e9cc6,0x1b098eec282,0x1aead1a49ea,0x1acc290f4dc,
  0x1aad95280e6,0x1a8f235782e,0x1a70c61aca0,0x1a527d6d684,0x1a34494b41c,0x1a16371d474,
  0x19f8395feb6]
private theorem t1 :ay 1350 3678 r1 := by
  repeat (apply checked_cons; rfl)
  trivial
private def r2 :List ℕ:=[
  0x181c40686c8,0x17ff334c492,0x17e2398c988,0x17c55325cc2,0x17a89179fda,0x178be30a612,
  0x176f47d3a84,0x1752bfd21d2,0x17365c68300,0x171a0c1689e,0x16fdceda2a6,0x16e1a4aee8e,
  0x16c59ef7696,0x16a9ac345ae,0x168dcc62192,0x1671ff7d20e,0x165656e7898,0x163ac121e6a,
  0x161f3e28d4e,0x1603cdf8524,0x15e881f2e5e,0x15cd4898990,0x15b221e60e4,0x15970dd785a,
  0x157c1dced36,0x1561404c756,0x1546754cc40,0x152bbccbeaa,0x1511282bcbc,0x14f6a5ec6ec,
  0x14dc360abcc,0x14c1d8822cc,0x14a79eb4ac8,0x148d7722acc,0x147361c84f8,0x14595ea183c,
  0x143f7f0fda4,0x1425b193b52,0x140bf62950a,0x13f24ccc0f8,0x13d8c6de1fa,0x13bf52df508,
  0x13a5f0cbd20,0x138ca09f428,0x137373bb44c,0x135a58a0114,0x13414f494a2,0x132857b2c18]
private theorem t2 :ay 1300 3733 r2 := by
  repeat (apply checked_cons; rfl)
  trivial
private def r3:List ℕ:=[
  0x1134a2bfeda,0x111ccb1c83a,0x110519e6f86,0x10ed791f624,0x10d5e8c1e4c,0x10be68ca7f0,
  0x10a70f19842,0x108fc5af5f4,0x10788c87a98,0x1061639e830,0x104a60d465e,0x10336e290a6,
  0x101c8b98994,0x1005b91ecd6,0xfef0c9c0c4,0xfd87010376,0xfc1e376e60,0xfab66cc63c,
  0xf950ff07cc,0xf7ec8e302c,0xf68919ff66,0xf526a22f72,0xf3c684c2e2,0xf26761b102,
  0xf10938baa2,0xefac0999ae,0xee513247f4,0xecf752c842,0xeb9e6ad08e,0xea467a19fe,
  0xe8f0dea3ca,0xe79c38665e,0xe648871e40,0xe4f5ca7d6a,0xe3a56084a0,0xe255e92e5e,
  0xe107642cec,0xdfb9d13aea,0xde6e8e5202,0xdd243b6afa,0xdbdad83a78,0xda926474e0,
  0xd94c3e1ad8,0xd807051ad0,0xd6c2b92b7e,0xd57f5a0566,0xd43e459c50,0xd2fe1be7a6,
  0xd1bedc997a]
private theorem t3:ay 1250 3781 r3:= by
  repeat (apply checked_cons; rfl)
  trivial
private def r4 :List ℕ:=[
  0xb30219bf86,0xb1d8627e8e,0xb0af8000dc,0xaf89205ca4,0xae63934998,0xad3ed88d7a,
  0xac1aefe5fc,0xaaf9875e90,0xa9d8eeb668,0xa8b925abc6,0xa79a2bfd22,0xa67dafb792,
  0xa562008fd4,0xa4471e4fac,0xa32d08ac68,0xa2156db0a8,0xa0fe9d1694,0x9fe8969f3e,
  0x9ed35a04d4,0x9dc0954aca,0x9cae982e84,0x9b9d627174,0x9a8cf3c38a,0x997efa3290,
  0x9871c57320,0x97655544f6,0x9659a95dc0,0x95506fc50c,0x9447f83160,0x9340425abc,
  0x92394df620,0x9134c90e32,0x9031035ae0,0x8f2dfc93e2,0x8e2bb46fa0,0x8d2bd8fa28,
  0x8c2cb9eb20,0x8b2e56fba8,0x8a30afe390,0x893572ae9e,0x883aef15e0,0x874124d3de,
  0x864813a020,0x85516987d4,0x845b764570,0x8366399334,0x8271b32a10,0x817f91189a]
private theorem t4 :ay 1200 3830 r4 := by
  repeat (apply checked_cons; rfl)
  trivial
private def r5:List ℕ:=[
  0x658d17e1e0,0x64b4844d18,0x63dc8d4550,0x6305329008,0x622e73f2f0,0x615a57dcbe,
  0x6086d59490,0x5fb3ece14e,0x5ee19d8a10,0x5e11edfd44,0x5d42d58370,0x5c7453e4e4,
  0x5ba668e870,0x5adb1afdea,0x5a10616f40,0x59463c047a,0x587caa85d0,0x57b5b36480,
  0x56ef4dea30,0x562979e050,0x5564371080,0x54a18bebb6,0x53df6fbd00,0x531de24f36,
  0x525ce36bb0,0x519e7984cc,0x50e09be700,0x50234a5cdc,0x4f6684b120,0x4eac515792,
  0x4df2a79c60,0x4d39874b82,0x4c80f03120,0x4bcae8c0b8,0x4b156847e0,0x4a606e93f8,
  0x49abfb70e0,0x48fa15537e,0x4848b38ad0,0x4797d5e3ee,0x46e77c2c20,0x4639acd9b4,
  0x458c5f3b60,0x44df931fa4,0x4433485530,0x438985520a,0x42e0416650,0x42377c61ea,
  0x418f361340]
private theorem t5:ay 1150 3878 r5:= by
  repeat (apply checked_cons; rfl)
  trivial
private def r6:List ℕ:=[
  0x2b59ff48a8,0x2acf453120,0x2a4757785e,0x29bfccbd80,0x2938a4dd5e,0x28b1dfb170,
  0x282de44f34,0x27aa495730,0x27270ea5f4,0x26a4341660,0x262420bf5a,0x25a46b4120,
  0x25251379aa,0x24a6194540,0x2429e3ba80,0x23ae097b10,0x23328a6650,0x22b7665840,
  0x223f0468e6,0x21c6fb3b50,0x214f4aae96,0x20d7f2a020,0x20635a295c,0x1fef17ed10,
  0x1f7b2bcbbc,0x1f0795a430,0x1e96bc8f92,0x1e26373210,0x1db6056d92,0x1d462720a0,
  0x1cd90365c8,0x1c6c30e2a0,0x1bffaf78c8,0x1b937f0830,0x1b2a06acce,0x1ac0dd0bf0,
  0x1a5802089e,0x19ef758430,0x19899e9a54,0x192413f1c0,0x18bed56ee4,0x1859e2f2d0,
  0x17f7a39a9a,0x1795ae0e60,0x173402324a,0x16d29fe8d0,0x1673ee5070,0x1615841100]
private theorem t6:ay 1100 3927 r6:= by
  repeat (apply checked_cons; rfl)
  trivial
private def r7:List ℕ:=[
  0x8cde2d74e,0x891e56bc0,0x85613ce0e,0x81a6dec50,0x7e1c3bfe4,0x7a94303f0,
  0x770eba944,0x738bd9f60,0x70388df5a,0x6ce7b25c0,0x6999464ca,0x664d48bb0,
  0x6330b94f0,0x601673e80,0x5cfe77a50,0x59e8c3900,0x570257676,0x541e0f060,
  0x513be9a16,0x4e5be65a0,0x4bab04e9c,0x48fc21420,0x464f3aaec,0x43a4504c0,
  0x412861ea2,0x3eae4b910,0x3c360c882,0x39bfa4020,0x377811e58,0x353232360,
  0x32ee04518,0x30ab87810,0x2e97bba6e,0x2c857cdd0,0x2a74ca97e,0x2865a41c0,
  0x268509624,0x24a5d69b0,0x22c80b364,0x20eba68f0,0x1f3da8b4a,0x1d90edd30,
  0x1be57570a,0x1a3b3eff0,0x18bf4a890]
private theorem t7:ay 1050 3975 r7:= by
  repeat (apply checked_cons; rfl)
  trivial
private theorem b1 :aak 3678 3733 0x3bbeefe685 :=
  from_rows (total:=0x64c0c4f240b8) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t1
private theorem b2 :aak 3733 3781 0x265fd93e44 :=
  from_rows (total:=0x40b68634ad16) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t2
private theorem b3:aak 3781 3830 0x1b6a7002df :=
  from_rows (total:=0x2e3bf57f04f8) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t3
private theorem b4 :aak 3830 3878 0x110e65724e :=
  from_rows (total:=0x1cc3ea5c0ff6) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t4
private theorem b5:aak 3878 3927 0x96467d3fd :=
  from_rows (total:=0xfd82f6a5a18) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t5
private theorem b6:aak 3927 3975 0x38ffde46d :=
  from_rows (total:=0x602be144000) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t6
private theorem b7:aak 3975 4020 0x7c6d9af6 :=
  from_rows (total:=0xd1f6cbc608) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) (by decide) t7
theorem proof :qwbsesc.c7:= by
  have c2 :=aGH (by decide) (by decide) b1 b2
  have c3:=aGH (by decide) (by decide) c2 b3
  have c4 :=aGH (by decide) (by decide) c3 b4
  have c5:=aGH (by decide) (by decide) c4 b5
  have c6:=aGH (by decide) (by decide) c5 b6
  exact aGH (by decide) (by decide) c6 b7
end q5wVSFc
end
