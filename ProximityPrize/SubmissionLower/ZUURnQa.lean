import ProximityPrize.SubmissionLower.ZNc0LBb
set_option Elab.async false
section
section
set_option autoImplicit true
namespace P5_7_6
open Finset cu P5_7
open Y2 (aOy Tb bg5 aJq aYm)
open aZD (Core aT)
open private bfq co2 biQ from ProximityPrize.SubmissionLower.D9
open private bid from ProximityPrize.SubmissionLower.CN
abbrev stop (s :Shape) (E v :ℕ) :=s.J+Tb s E v
def column (s :Shape) (pin E v l r :ℕ) :ℕ :=
 let n:=stop s E v
 if l<n then aOy (2*pin*((l+min r n-1)/2)) (131071-pin) (s.m*farAgreement) (s.B+1)
 else 0
private theorem column_le (s :Shape) (pin E v l r :ℕ) :column s pin E v l r≤ s.B+1 := by
 simp only [column,aOy]
 split_ifs <;> omega
def cap (s :Shape) (pin E v t:ℕ) :ℕ :=
 if t<256 then column s pin E v 0 256 else
 if t<512 then column s pin E v 256 512 else column s pin E v 512 768
def masked (s :Shape) (pin E v h q j t:ℕ) :ℤ :=
 if q<cap s pin E v t then width s h q j t else 0
private def core (s :Shape) (h E v d k :ℕ) :Core :=
 let D:ℤ:=131071-(h:ℤ)
 let p:ℤ:=(E-1 :ℕ)
 let w:ℤ:=(E*d:ℕ)
 ⟨k,E*d,E-1,bg5 s v d (Tb s E v),aJq s v d,
   ⟨(k :ℤ)-w,-p⟩,⟨2*(s.m*farAgreement:ℕ)-D*(w+k-1),-2-D*p⟩,
   2-4*(h:ℤ)-D⟩
private theorem core_term (s :Shape) (h E v d k t a :ℕ)
   (he :0<E) (hat :a≤t) (hk :t-a+E*(a+d)≤k) :
   (core s h E v d k).term a t =
     2*(∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t) := by
 let l:=t-a+E*(a+d)
 let D:ℤ:=131071-(h:ℤ)
 have hk' : l≤k :=hk
 have hl: (l:ℤ)=(t:ℤ)+(E*d:ℕ)+((E-1 :ℕ) :ℤ)*a := by
   rw [show l=aYm E d t+(E-1)*a from biQ E d t a he hat]
   push_cast [aYm]
   ring
 change _=2*(∑ q∈Ico l k,width s h q (t-a) t)
 rw [sum_Ico_eq_sum_range]
 have hw (i:ℕ) :width s h (l+i) (t-a) t=width s h l (t-a) t+(-D)*(i:ℤ) := by
   simp only [width,D,Nat.cast_add]
   ring
 simp_rw [hw]
 rw [bid]
 simp only [core,Core.term,aT.at,width,D,Nat.cast_sub hat,Nat.cast_sub hk']
 rw [hl]
 ring
private theorem order_pos (s :Shape) (E v :ℕ) :0<Tb s E v := by
 unfold Tb
 split
 · exact Nat.succ_pos _
 · exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
private def diag (s :Shape) (h E v d t k :ℕ) :ℤ :=
 ∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
   (slots s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t
private theorem diag_eq (s :Shape) (h E v d k t:ℕ) (he :0<E) :
    let C:=core s h E v d k
    (∑ a∈range C.cap,
      if a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column
      then C.seed.eval a*C.term a t else 0)=4*diag s h E v d t k := by
  dsimp only
  let C:=core s h E v d k
  let S:=(range C.cap).filter (fun a=>a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column)
  let T:=Ico (t-s.J) (min t (Tb s E v-1)+1)
  have hn:=order_pos s E v
  have hm (a :ℕ) :a∈S↔a∈T∧(a+d)*v≤ s.U∧t-a+E*(a+d)<k := by
    simp only [S,T,C,core,mem_filter,mem_range,mem_Ico,bfq,Nat.lt_succ_iff,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hv⟩,ht,hj,hk⟩
      rw [biQ E d t a he ht]
      exact ⟨⟨by omega,ht,by omega⟩,hv,by simpa [aYm,Nat.add_assoc] using hk⟩
    · rintro ⟨⟨hj,ht,ha⟩,hv,hk⟩
      rw [biQ E d t a he ht] at hk
      exact ⟨⟨by omega,hv⟩,ht,by omega,by simpa [aYm,Nat.add_assoc] using hk⟩
  rw [← sum_filter,diag,mul_sum]
  change (∑ a∈S,C.seed.eval a*C.term a t)= _
  calc
    _ = ∑ a∈S,4*((slots s.U ((a+d)*v) :ℤ) *
          ∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t) := by
      apply sum_congr rfl
      intro a ha
      obtain ⟨ht,hv,hk⟩:=(hm a).mp ha
      have hat :a≤t:=(le_min_iff.mp (Nat.le_of_lt_succ (mem_Ico.mp ht).2)).1
      change (aJq s v d).eval a*(core s h E v d k).term a t= _
      rw [co2 _ _ _ _ hv,core_term s h E v d k t a he hat hk.le]
      ring
    _ = _:= by
      apply sum_subset (fun a ha=>((hm a).mp ha).1)
      intro a ha hn
      by_cases hv : (a+d)*v≤ s.U
      · have hz :k≤t-a+E*(a+d) :=
          Nat.le_of_not_gt (fun hk=>hn ((hm a).mpr ⟨ha,hv,hk⟩))
        simp [Ico_eq_empty_of_le hz]
      · simp [slots,hv]
private def group (s :Shape) (h E v d l r k :ℕ) :ℤ :=
 let C:=core s h E v d k
 (C.vo r 0 - C.vo r (s.J+1))-(C.vo l 0 - C.vo l (s.J+1))
private theorem group_eq (s :Shape) (h E v d l r k :ℕ) (he :0<E) (hl:l≤ r) :
  group s h E v d l r k=1440*(∑ t∈Ico l r,diag s h E v d t k) := by
 rw [group,Core.azU,Core.azU,← mul_sub,← sum_Ico_eq_sub _ hl]
 simp_rw [diag_eq s h E v d k _ he]
 rw [← mul_sum]
 ring
def total (s :Shape) (pin h E v d:ℕ) :ℤ :=
 group s h E v d 0 256 (column s pin E v 0 256) +
 group s h E v d 256 512 (column s pin E v 256 512) +
 group s h E v d 512 768 (column s pin E v 512 768)
theorem asB (s :Shape) (pin h E v d:ℕ) (he :0<E) (hn:stop s E v≤768) :
    total s pin h E v d = 1440*phase s E v d (masked s pin E v h) := by
  let f := fun t=>diag s h E v d t (cap s pin E v t)
  have hs :phase s E v d (masked s pin E v h) = ∑ t∈range 768,f t:= by
    unfold phase
    trans ∑ t∈range (stop s E v),f t
    · apply sum_congr rfl
      intro t _
      unfold f diag
      apply sum_congr rfl
      intro a _
      congr 1
      simp only [masked]
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_Ico,mem_filter]
      have hc:cap s pin E v t≤ s.B+1 := by
        unfold cap
        split_ifs <;> apply column_le
      omega
    · apply sum_subset (range_mono hn)
      intro t _ ht
      have ht' : stop s E v≤t:= by simpa only [mem_range,not_lt] using ht
      unfold f diag
      have hp:=order_pos s E v
      rw [Ico_eq_empty_of_le (by change s.J+Tb s E v≤t at ht'; omega),sum_empty]
  rw [total,group_eq s h E v d 0 256 _ he (by decide),
    group_eq s h E v d 256 512 _ he (by decide),
    group_eq s h E v d 512 768 _ he (by decide),← mul_add,← mul_add,hs]
  have hp (l r k :ℕ) (hc : ∀ t∈Ico l r,cap s pin E v t=k) :
      (∑ t∈Ico l r,diag s h E v d t k) = ∑ t∈Ico l r,f t :=
    sum_congr rfl (fun t ht=> by
      change _=diag s h E v d t (cap s pin E v t)
      rw [hc t ht])
  rw [hp 0 256 _ (by intro t ht; simp [cap,(mem_Ico.mp ht).2]),
    hp 256 512 _ (by
      intro t ht
      obtain ⟨hl,hr⟩:=mem_Ico.mp ht
      simp [cap,not_lt_of_ge hl,hr]),
    hp 512 768 _ (by
      intro t ht
      have hl:=(mem_Ico.mp ht).1
      simp [cap,not_lt_of_ge hl,show ¬t<256 by omega]),
    Nat.Ico_zero_eq_range,sum_range_add_sum_Ico f (by decide :256≤512),
    sum_range_add_sum_Ico f (by decide :512≤768)]
end P5_7_6
end
section
set_option autoImplicit true
namespace P5_7_6
open cu P5_7
open private c8O from ProximityPrize.SubmissionLower.D9
private def x5 (b:Bank) (pin E v h:ℕ) :ℤ :=
 O3 b.shape E v (masked b.shape pin E v h)-(j3 h b:ℤ)
private def nY (b:Bank) (pin E v h:ℕ) :ℤ :=
 total b.shape pin h E v 0 - total b.shape pin h E v 1 - 1440*(j3 h b:ℤ)
private theorem scaled_eq (b:Bank) (pin E v h:ℕ)
  (he :0<E) (hn:stop b.shape E v≤768) :
  nY b pin E v h=1440*x5 b pin E v h:= by
 rw [nY,x5,gain_phases _ _ _ _ he,
  asB _ _ _ _ _ _ he hn,asB _ _ _ _ _ _ he hn]
 ring
private theorem masked_step (s :Shape) (pin E v n q j t:ℕ) :
   masked s pin E v (n+1) q j t+masked s pin E v (n+1) q j t =
    masked s pin E v n q j t+masked s pin E v (n+2) q j t:= by
 by_cases ht:q<cap s pin E v t
 · have hw (h:ℕ) :masked s pin E v h q j t=width s h q j t:=ite_eq_left ht
   rw [hw (n+1),hw n,hw (n+2)]
   simp only [width,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
   ring
 · have hz (h:ℕ) :masked s pin E v h q j t=0:=ite_eq_right ht
   rw [hz (n+1),hz n,hz (n+2)]
private theorem surplus_step (b:Bank) (pin E v n:ℕ) :
    x5 b pin E v (n+1) + x5 b pin E v (n+1) =
      x5 b pin E v n + x5 b pin E v (n+2) := by
  have hg :
      O3 b.shape E v (masked b.shape pin E v (n+1)) +
        O3 b.shape E v (masked b.shape pin E v (n+1)) =
      O3 b.shape E v (masked b.shape pin E v n) +
        O3 b.shape E v (masked b.shape pin E v (n+2)) := by
    rw [← gain_add b.shape E v _ (masked b.shape pin E v (n+1)),
      ← gain_add b.shape E v _ (masked b.shape pin E v (n+2))]
    exact congrArg (O3 b.shape E v) (funext fun q=>funext fun j=>funext fun t =>
      masked_step b.shape pin E v n q j t)
  have hd: (j3 (n+1) b:ℤ)+(j3 (n+1) b:ℤ) =
      (j3 n b:ℤ)+(j3 (n+2) b:ℤ) := by
    simp only [j3,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  unfold x5
  omega
private theorem strict {b:Bank} {pin E v h:ℕ} (hl:pin≤h) (hh:h≤131071)
   (he :0<E) (hs :stop b.shape E v≤768)
   (hp:0<nY b pin E v pin) (hd:nY b pin E v pin≤nY b pin E v (pin+1)) :
   j3 h b<ZN h b.shape E v := by
 rw [scaled_eq _ _ _ _ _ he hs] at hp
 rw [scaled_eq _ _ _ _ _ he hs,scaled_eq _ _ _ _ _ he hs] at hd
 have hr :=c8O (f :=x5 b pin E v)
   (fun n _=>(surplus_step b pin E v n).le) hl (by omega)
 have hpos :0<x5 b pin E v h:= by omega
 have hg:=gain_le b.shape E v (f :=masked b.shape pin E v h)
   (g:= fun q j t=>max 0 (width b.shape h q j t)) (by
     intro q j t
     unfold masked
     split
     · exact le_max_right _ _
     · exact le_max_left _ _)
 rw [← gain_eq b.shape h E v hh] at hg
 unfold x5 at hpos
 omega
def ay (b:FarBand) (x :Test b) :Prop :=
  ∀ h,b.row.lo≤h→h≤131071 →
    j3 h (Lc b x)<ZN h (Lc b x).shape (threshold b x) (apo b x)
theorem checked {b:FarBand} {x :Test b} (z w:ℤ)
  (hs :decide (stop (Lc b x).shape (threshold b x) (apo b x)≤768)=true)
  (hz : (nY (Lc b x) b.row.lo (threshold b x) (apo b x) b.row.lo == z)=true)
  (hw: (nY (Lc b x) b.row.lo (threshold b x) (apo b x) (b.row.lo+1) == w)=true)
  (hp:decide (0<z)=true) (hd:decide (z≤w)=true) :ay b x := by
 intro h hl hh
 have he :0<threshold b x := by cases x <;> exact Nat.succ_pos _
 have hz' := beq_iff_eq.mp hz
 have hw' := beq_iff_eq.mp hw
 exact strict hl hh he (of_decide_eq_true hs)
  (by simpa only [hz'] using of_decide_eq_true hp)
  (by simpa only [hz',hw'] using of_decide_eq_true hd)
def test (b:FarBand) :ℕ→Test b
 | 0=>none
 | i+1=>if hi:i<b.row.gw.length then some ⟨i,hi⟩ else none
theorem checked_tests (b:FarBand) (ho:ay b none)
   (hg : ∀ j<b.row.gw.length,ay b (test b (j+1))) (x :Test b) :ay b x := by
 cases x with
 | none=>exact ho
 | some i =>
   rcases i with ⟨j,hj⟩
   simpa only [test,hj,dite_true] using hg j hj
end P5_7_6
end
section
set_option autoImplicit true
set_option maxRecDepth 9000
set_option maxHeartbeats 12000000
namespace P5_7_6
open P5_7
local notation "az" z:arg "," w:arg=>checked z w rfl rfl rfl rfl rfl
private theorem dbl : ∀ x,ay .dbl x := by
 refine checked_tests .dbl (az 0x32386ae8f7d38a02f80,0x329ca3a8284bf760640) ?_
 intro j hj
 change j<12 at hj
 interval_cases j
 · exact az 0xa4bf4656ddc4b4e300,0xa83c9015d7824d58c0
 · exact az 0xa3d603bcc66de3ad00,0xa76c7a602ec58c7200
 · exact az 0xae28083b526bb449c0,0xb1e8dfeef72a03a580
 · exact az 0xcae69410dbbb92e800,0xceef52681581376580
 · exact az 0xd9702cddf3a4afcfc0,0xddcf42df14b0215180
 · exact az 0xf4946d4a8e72395700,0xf9a15cb0b30740c500
 · exact az 0x139954762bbe53ce7c0,0x13fb589b30275908bc0
 · exact az 0x13835488438f0872300,0x13e557eb90f46666800
 · exact az 0x11cf77fba1f9500cc20,0x12315ca1cfb8e6d18c0
 · exact az 0x11407e9c22edb251520,0x11a25b6ea81444842a0
 · exact az 0x115dd8a91fa706996c0,0x11bfb9362e3494bc040
 · exact az 0x11d136cc9bd86a4e380,0x123321aa39cd2562d80
private theorem lZ : ∀ x,ay .lZ x := by
 refine checked_tests .lZ (az 0x19f3d61a87338edd80,0x1a2185d46decd70ec0) ?_
 intro j hj
 change j<9 at hj
 interval_cases j
 · exact az 0xda258f27cf7bee00,0xea13267188bc4300
 · exact az 0x4ca4ad3cad6f4400,0x5cd817e439874dc0
 · exact az 0x31b91931e536900,0x13ffff4c93c676c0
 · exact az 0x34ef41a79cf05d80,0x475fb8630d136440
 · exact az 0x10f2eb3673c09700,0x26110b01cf5b7a80
 · exact az 0xee1cd4e3bc94b3a0,0x115bd1cc16dee9160
 · exact az 0x20d66724ef3c64380,0x2398439b1f1b6d180
 · exact az 0x1b43732d3b085b080,0x1e052f0f55d58a160
 · exact az 0x294597765d667400,0x554ab024131a4780
private theorem om : ∀ x,ay .om x := by
 refine checked_tests .om (az 0x3695d3a6e4f457c40,0x36d6f1bddabc1b540) ?_
 intro j hj
 change j<8 at hj
 interval_cases j
 · exact az 0x2fd8622e1715a7c0,0x3203c1c6bfb48980
 · exact az 0x385aca005f430780,0x3aa9812427d5fc40
 · exact az 0x6a6fc12c0a540e80,0x6d083ac99a172b40
 · exact az 0x78c627b9cd6a50c0,0x7bd5e03bf00dfd00
 · exact az 0x8f5f50bd91cfac40,0x934a435a7e786780
 · exact az 0x6f6d746c5aa28c40,0x7356b2e238b8fa00
 · exact az 0x14e4748fb1aafc40,0x18c8deea43223740
 · exact az 0x53e2fe82f148dc40,0x57cac4f2857bcdc0
private theorem wS : ∀ x,ay .wS x := by
 refine checked_tests .wS (az 0x75d5a9e4b4c380,0x7627d2f94d1ec0) ?_
 intro j hj
 change j<7 at hj
 interval_cases j
 · exact az 0x2baf536f613940,0x2bf817c6980b00
 · exact az 0x1bb1446b698a80,0x1bfd2dd2900b00
 · exact az 0x22198481c98380,0x2268e90bc69ec0
 · exact az 0x12b2912a198b80,0x1301735ff4aec0
 · exact az 0x14593eb00bb600,0x14a82ede7b63c0
 · exact az 0x78939ee4bfb00,0x7d7bdb224adc0
 · exact az 0x121f0b260f82c0,0x126de87b9d4d40
private theorem vX : ∀ x,ay .vX x := by
 refine checked_tests .vX (az 0xc7ac956877a840,0xc7febe7d100380) ?_
 intro j hj
 change j<7 at hj
 interval_cases j
 · exact az 0x1db6738ffdd00,0x218156befcf00
 · exact az 0x287a6e0f70ee80,0x28c33d4365b140
 · exact az 0x3169d0b7ce2840,0x31b72adca26580
 · exact az 0x2728af69aea840,0x2775b58d720f80
 · exact az 0x1f7f879fc4840,0x243cdf40e0800
 · exact az 0x5ec38281dc840,0x6382e06870600
 · exact az 0x1eaa68c4fd0840,0x1ef72955154700
private theorem vg : ∀ x,ay .vg x := by
 refine checked_tests .vg (az 0x9d9a1e27af00,0x9dcfc0b4c980) ?_
 intro j hj
 change j<5 at hj
 interval_cases j
 · exact az 0x136e6f5eec00,0x13910df81540
 · exact az 0x478e54b2f500,0x47b9c0559940
 · exact az 0x6514bc854400,0x65495f9cc1c0
 · exact az 0x43ac8652af00,0x43e0926c8980
 · exact az 0x2acc49064100,0x2affe4b16c00
private theorem wI : ∀ x,ay .wI x := by
 refine checked_tests .wI (az 0x2e67cba3a000,0x2e711956c6c0) ?_
 intro j hj
 change j<4 at hj
 interval_cases j
 · exact az 0x15c564ee11c0,0x15cb2aba9b80
 · exact az 0x2b4b80ad4480,0x2b53186372c0
 · exact az 0x114bd893a000,0x1154cd54c6c0
 · exact az 0x9706fb48000,0x9794c73a2c0
private theorem vW : ∀ x,ay .vW x := by
 refine checked_tests .vW (az 0x8b265d8dea00,0x8b2fab4110c0) ?_
 intro j hj
 change j<4 at hj
 interval_cases j
 · exact az 0x1a034a364400,0x1a0833662240
 · exact az 0x324f99755100,0x325631506a40
 · exact az 0x2262ece1ca00,0x226b1c81fd40
 · exact az 0x2ca348d1ca00,0x2cab94703d40
private theorem wO : ∀ x,ay .wO x := by
 refine checked_tests .wO (az 0x1276b7abccb00,0x12774c86ff1c0) ?_
 intro j hj
 change j<4 at hj
 interval_cases j
 · exact az 0x2a46455cc3c0,0x2a4a6feeb400
 · exact az 0x4abe70668540,0x4ac4321615c0
 · exact az 0x5299eb77a100,0x52a14c549440
 · exact az 0x355d62b60900,0x35647fde9a40
private theorem wQ : ∀ x,ay .wQ x := by
 refine checked_tests .wQ (az 0x4adf8db100,0x4ae579e480) ?_
 intro j hj
 change j<4 at hj
 interval_cases j
 · exact az 0x1d72e3bcc0,0x1d76e3e200
 · exact az 0x3de290b80,0x3e21e8300
 · exact az 0x211a16f180,0x211faeae80
 · exact az 0x1b8151a80,0x1bd6d6280
theorem proof :P5_7.c6:= by
 intro b h hl hh x
 have hu:b.row.hi≤131071 := by cases b <;> decide
 have hs :ay b x := by
  cases b with
  | dbl=>exact dbl x
  | lZ=>exact lZ x
  | om=>exact om x
  | wS=>exact wS x
  | vX=>exact vX x
  | vg=>exact vg x
  | wI=>exact wI x
  | vW=>exact vW x
  | wO=>exact wO x
  | wQ=>exact wQ x
 exact hs h hl (hh.trans hu)
end P5_7_6
end
end
section
set_option autoImplicit true
namespace P5_7_2
noncomputable section
open Polynomial
open P5 (I K jG)
open P5_7 (nearRows midAgreement HeightPrice Bank YQ Qn)
open cu (FX L Shape vP Equation vm ku triangle slots yq)
open DP (jF zG)
open qQ (zI N5)
open scoped BigOperators
abbrev fO:=Fin nearRows.length
abbrev jX (b:fO) :HeightPrice :=nearRows.get b
abbrev Window (b:fO) (w:ℤ) := Qn (jX b).lo (jX b).hi w
abbrev A:=midAgreement
structure Ls where
 dI:ℕ
 free :Shape
 moving:Shape
structure Aux where
 dI:ℕ
 shape :Shape
structure af where
 declaredHi:ℕ
 prefixFee :ℕ
 Z1 :ℕ
 shape :Shape
 ad1 :ℕ
 bDZ:ℕ
 Kw:ℕ
 xF:ℕ
def row (b:fO) :af := match b.val with
  | 0=>⟨2533,0x386fa82c10cf4fa,0xbc74110447297,⟨2100,2927,619,190000⟩,0xf8eab0e80000,77,
    0x460b011917f1e42472a83073653c041a4724c851d56f5c060e65b6a66ef73677b7be7ff83e87c8b78f092895d9919c29f2a20a4ca77a9fac6aecb10b33b54b75b95bb3bd1beec09c24c3ec57c6fc86c9dcb4ccacdfcf4d09d1dd31d44d57d6ad7dd8fda1db3dc4dd6de7df8e08e19e29e39e49,
    0x11a80c2204d3c196307bc8241b0a3c82d880c634352c0e2e43c250fd70422b1145047af129a04cd913cac512a14ddc557815d78596e16bd85ccc179cc602b186b06347192cc6623⟩
  | 1=>⟨2534,0x39333a4702e58db,0xbcab0a6ad19bc,⟨2100,2927,619,185000⟩,0xf8eab0e80000,78,
    0x2808f0f515a1bc21d27c2da33538f3e843e4934e55365865d361e6686b06f673a77c7bd7fb8388738ab8e291794b97c9ac9d9a05a30a58a7faa5ac9aebb0db2db4db6bb89ba6bc2bddbf8c12c2bc43c5ac71c87c9dcb3cc8cdccf0d04d17d2ad3dd50d62d74d85d97da8db9dcaddadebdfbe0be1b,
    0xc9c095e03c081436064401dae0873425c30a4ec2c750be5432bf0d68438390ebb83d600fe8841b710f6445f01202449cb12eb84d5413c2850d11487c53c815508568f⟩
  | 2=>⟨2535,0x381165cd201faad,0x18e2f5bdc46608,⟨2100,2927,619,140000⟩,0xf8eab0e80000,103,
    0xc05b0a90f614218d1d72212692b02f633b37f3c24044454854c450253f57b5b65ef6286606966cc7007347667977c77f682485187d8a88d18fa92194896d9919b59d79f8a18a38a56a73a90aabac6ae0afab13b2bb43b5ab70b87b9cbb2bc7bdbbefc03c17c2ac3dc50c63c75c87c99caacbbccccddceecffd0fd1fd2fd3fd4fd5ed6ed7dd8cd9bdaadb8dc7dd5de4df2e00e0ee1ce29e37e45,
    0x0⟩
  | 3=>⟨2536,0x36f43bec35fba39,0x1c8ba4cbfb64ac,⟨2100,2927,619,134115⟩,0xf8eab0e80000,107,
    0x4b0960e01291721b91ff24528a2cd3103523933d341245048e4ca50553f5795b15e961f65568a6bd6f07217527827b17de80b83786188b8b48dc90292894d9719949b69d79f7a16a34a51a6ea8aaa5abfad8af1b09b21b38b4eb65b7ab8fba4bb9bcdbe1bf4c07c1ac2dc3fc51c63c75c86c97ca8cb9cc9cdaceacfad09d19d29d38d47d56d65d74d82d91d9fdaedbcdcadd8de5df3e01e0ee1be29e36e43e50,
    0x0⟩
  | 4=>⟨2537,0x37cc2d67869e598,0x1dd91e7173be55,⟨2600,3624,767,145000⟩,0x1d87d62000000,114,
    0x210630a40e51241631a11df21c2582932cd3073403783af3e641c4514854b94eb51d54e57f5ae5dd60b6386646906bb6e570e73675d7847aa7cf7f381783985b87c89c8bb8da8f891593194c96798199a9b39cb9e29f9a0fa24a3aa4ea62a76a89a9caafac1ad3ae5af6b08b18b29b39b4ab5ab69b79b88b97ba6bb5bc4bd2be1befbfdc0bc18c26c34c41c4ec5bc68c75c82c8fc9bca8cb4cc0ccccd8ce4cf0cfcd08d13d1fd2ad36d41,
    0x0⟩
  | 5=>⟨2538,0x36dfa2a3d7fcaf9,0x234037652c70c2,⟨2600,3624,767,140000⟩,0x1d87d62000000,120,
    0x110510900ce10c1491851c11fc2372702a92e13193503863bc3f042445848a4bc4ed51e54e57d5ab5d860563165d6876b16da70372a75177779c7c17e580882a84c86d88d8ac8cb8e990692393e95997498d9a69bf9d69eda04a1aa2fa44a59a6da80a94aa6ab9acbaddaeeb00b11b22b32b42b52b62b72b81b90b9fbaebbdbccbdabe8bf6c04c12c1fc2dc3ac48c55c62c6fc7bc88c94ca1cadcbacc6cd2cdeceacf5d01d0dd18d24d2fd3ad45d51d5cd67d72,
    0x0⟩
  | 6=>⟨2541,0x37af2996d014c0a,0xe48a13fe55f40,⟨2600,3624,767,163000⟩,0x1d87d62000000,92,
    0x480920da1211681ad1f12342772b82f83373753b23ed42846249a4d250853d5715a45d66076376656936bf6ea71473d76578c7b17d67f981b83d85d87c89a8b68d28ee90892193a95196997f9959ab9c09d49e99fca10a23a35a47a59a6ba7da8ea9faafac0ad0ae0af0b00b0fb1eb2db3cb4bb59b68b76b84b92ba0baebbbbc9bd6be3bf0bfdc0ac17,
    0x0⟩
  | 7=>⟨2544,0x3565d9c177c91ec,0x21baaec0245ef0,⟨2600,3624,767,135000⟩,0x1d87d62000000,120,
    0x2d06a0a70e311e1591931cc20523d2742aa2e031634a37e3b23e44164474784a84d750553356058d5b85e360d6376606886af6d66fc72174676978d7af7d17f181283185086e88b8a88c48df8fa91492d94595d97598b9a19b79cc9e19f5a08a1ca2ea41a53a65a76a87a98aa9ab9ac9ad9ae9af8b07b16b25b34b42b51b5fb6db7bb88b96ba3bb1bbebcbbd8be4bf1bfdc0ac16c22c2ec3ac46c52c5ec69c75c80c8cc97ca2cadcb8cc3ccecd9ce4ceecf9d04,
    0x0⟩
  | 8=>⟨2554,0x376d9ffcb18b33a,0x1adc9e7b6c7b61,⟨2600,3624,767,135000⟩,0x1d87d62000000,114,
    0x3206f0ac0e812315d1971d02082402772ad2e231734b37f3b13e34144454754a44d24ff52c5585845ae5d860162a65167869e6c36e870c72f7517737947b47d37f180f82c84986487f8998b38cb8e38fb91292893d95296797b98e9a29b49c79d99ea9fca0da1da2ea3ea4ea5ea6da7ca8ba9aaa9ab7ac5ad4ae2aefafdb0ab18b25b32b3fb4cb58b65b71b7eb8ab96ba2baebbabc5bd1bdcbe8bf3bfec09c14c1fc2ac35c40c4bc55c60,
    0x0⟩
  | 9=>⟨2564,0x363b9bc58404cba,0x1129f8ea816497,⟨2600,3624,767,208000⟩,0x1d87d62000000,62,
    0x1b0790d512f1871dd2312842d432236e3b840044648a4cc50b5495845bd5f462965c68c6bb6e771173a7607847a77c87e780481f83985186887e8938a88bb8cf8e18f39059169279389489589679779869949a39b19bf9cd9db9e89f6,
    0x948150e08e882f220e4f441e2125ec505e1588c5c16182d065a81a8206de01c6ec75291e0e47b6b1f930815120e7086242237c8aed234fc8f622453093242549496b3⟩
  | 10=>⟨2574,0x2b0a6a79f4ec78d,0x163a99c4af11df,⟨2600,3624,767,155000⟩,0x1d87d62000000,72,
    0x440890cd1101521921d120f24c2872c12fa33136739c3d04024334624904bd4e851253b5625885ac5cf5f161263164f66b6876a16ba6d26e970071572a73e75276577878a79c7ad7bf7cf7e07f07ff80f81e82d83c84a85986787588289089d8ab8b88c48d18de8ea8f6903,
    0x0⟩
  | 11=>⟨2580,0x26ea98b2b325cce,0x17621d585b03ef,⟨2600,3624,767,135000⟩,0x1d87d62000000,77,
    0x180560920cd1071401781af1e521924d2802b22e231234036e39a3c53ef41844046748c4b14d44f65175375565745915ac5c75e05f961062763c65166567968b69e6af6c06d16e26f270171172072e73d74b75976677478178e79b7a87b47c07cd7d97e47f07fc80781281e82983483e849854,
    0x0⟩
  | 12=>⟨2703,0x25cd9045b43293c,0x6d53c7fd324fb,⟨2600,3624,767,208000⟩,0x1d87d62000000,50,
    0x580b410e1651ba20c25c2aa2f533d3833c74084464814ba4f15245565845b05d95fe61d63865166867e6926a66b96cb6dc6ed6fd70c71c72b73974875676377177e78b7977a47b07bc7c8,
    0xbb4c4f631974c75e920a6c8cb5257109cff28db8a94e2bb20b3762dfe4bc732ff48c34031b2cc97333118cf4734604d3fb358e0d8b436a08dc91379fce041⟩
  | _=>⟨2703,0x25613ce2b893847,0x6a120bd97145c,⟨2600,3624,767,208000⟩,0x1d87d62000000,50,
    0x360930ee14619c1ef24028e2da32336a3ae3ef42e46b4a44db51054157059d5c75ec60c62764065766d6816956a86b96cb6db6ec6fb70b71a72873674475275f76c77978679279e7aa7b6,
    0xb4b04ef419a607754211948eb825fc89f4429708ac482c4d8b6742e9b8bedf30910c5b6324f8cc6333cc0d1af35190d6d636424db0337500df56384e4e2ec⟩
private def unpackShape (n:ℕ) :Shape :=
 ⟨n &&& 0xfff,(n >>> 12) &&& 0xfff,(n >>> 24) &&& 0x3ff,n >>> 34⟩
private def unpackStage (n:ℕ) :Ls :=
 ⟨n &&& 0x3f,unpackShape ((n >>> 6) &&& 0x3fffffffffffff),unpackShape (n >>> 60)⟩
private def unpackAux (n:ℕ) :Aux :=
 ⟨n &&& 0x3f,unpackShape (n >>> 6)⟩
def stages (b:fO) :List Ls :=
 (match b.val with
 | 0=>[0x40d90ee46f32c003d40641cc14c0,0x48b85024ce3700053b0641cc14c1,0x4e5e92055d3d6003c90982a01e42,
     0x5cb154e638473006c208024c1a84,0x6ca89766f54fe047870782201886,0x8c115ca88661d054600982ac1eca,
     0xadf1e78bc9874033ab0c83942950,0x13853aa3ca090800dd91586004558]
 | 1=>[0x41868eb46b32c003d10641cc14c0,0x49444ff4ca370005360641cc14c1,0x4f7dd1c5583d6003c80982a01e42,
     0x5da054a634473006bb08024c1a84,0x6c381797185170449d0782201886,0x8af8dcd8a9636051520982ac1eca,
     0xafa5a73bc9874032d90c83942950,0x1454ea97c758ef00dd01586004558]
 | 2=>[0x409e8eb46b32c003cf0641cc14c0,0x483a0ff4ca370005300641cc14c1,0x4e65d1c5583d6003c60982a01e42,
     0x5c5414a634473006b508024c1a84,0x6ab5579718517041ee0782201886,0x88f25cd8a963604e7c0982ac1eca,
     0xad47e73bc98740320e0c83942950,0x13dbda97c758ef00dc71586004558]
 | 3=>[0x3fbcceb46b32c003cc0641cc14c0,0x47378ff4ca3700052b0641cc14c1,0x4d5591c5583d6003c40982a01e42,
     0x5b1114a634473006af08024c1a84,0x693d57971851703f740782201886,0x86fb5cd8a963604bd70982ac1eca,
     0xaafaa73bc9874031490c83942950,0x13685a97c758ef00dbf1586004558]
 | 4=>[0x3ee18eb46b32c003c90641cc14c0,0x463c4ff4ca370005260641cc14c1,0x4c4c91c5583d6003c20982a01e42,
     0x59d714a634473006a808024c1a84,0x67d017971851703d270782201886,0x85129cd8a96360495e0982ac1eca,
     0xa8bd273bc98740308a0c83942950,0x12fa1297c758ef00db61586004558]
 | 5=>[0x3e0c4eb46b32c003c60641cc14c0,0x4547cff4ca370005210641cc14c1,0x4b4b11c5583d6003c00982a01e42,
     0x58a594a634473006a208024c1a84,0x666c97971851703b040782201886,0x83381cd8a96360470e0982ac1eca,
     0xa68ee73bc987402fd10c83942950,0x1290a697c758ef00dae1586004558]
 | 6=>[0x3d3c8eb46b32c003c30641cc14c0,0x445a4ff4ca3700051c0641cc14c1,0x4a5051c5583d6003bf0982a01e42,
     0x577c54a6344730069c08024c1a84,0x6512d79718517039060782201886,0x816adcd8a9636044e20982ac1eca,
     0xa46f273bc987402f1e0c83942950,0x122bc297c758ef00da51586004558]
 | 7=>[0x3bc18e645431b003bb0641cc14c0,0x41b70ff4ca3700036e08825c1b41,0x4ae99094fa392003b90982a01e42,
     0x542ed4a6344730046e0ac2f82244,0x613b579718517013b607c23c19c6,0x7c4d9cd8a96360196909c2cc204a,
     0xa072e67b9084b02d230c83942950,0x1115a297c758ef00abc1b07585518]
 | 8=>[0x3a630e143c30a0031a07c22418c0,0x401e0fa4b335f0036908825c1b41,0x47e29094fa392003b40982a01e42,
     0x532213e5fa44a004670ac2f82244,0x61b1d626a54c50131507c23c19c6,0x77965cd8a96360189f09c2cc204a,
     0x9cb765bb5782202b510c83942950,0x101f5a97c758ef00aaf1b07585518]
 | 9=>[0x35390d740c2e8003980641cc14c0,0x3b2b0eb46b32c004cf0641cc14c1,0x4033d044e2381003bf09027c1cc2,
     0x4b79d325c1421006a808023c19c4,0x5f5953e5fa44a0114207c23c19c6,0x7d099857525400165309c2cc204a,
     0xbcae9d88e265f017bb0d03bc2b10,0xd95f297c738ef0121c12c5683e58]
 | 10=>[0x324a4c43ae2a4003800641cc14c0,0x36294e143c30a004a40641cc14c1,0x3b86cf549b34e003ad09027c1cc2,
     0x45e51215703e70066a08023c19c4,0x533453e5fa44a00fc207c23c19c6,0x6c3f5857525400146e09c2cc204a,
     0xa53cdcd8a9636022330c83942950,0xbbef697c738ef00fd31385884018]
 | 11=>[0x63bf88c2a31e5003690641cc14c0,0xbf6bc922c01fa0047c0641cc14c1,0x505c0ba37f28200a2205c1ac1342,
     0x214588b53672710063108023c19c4,0x51951215703e700e8107c23c19c6,0x6ad91626a54c500cce0a42f8224a,
     0x93e29c186f60d00ae20f44543210,0xc986244ae47d0019bd1144f03918]
 | 12=>[0x5261c8c2a31e5003750641cc14c0,0x89cdc922c01fa004800641cc14c1,0x47854ba37f282009c305c1ac1342,
     0x11df48b53672710063108023c19c4,0x4bc39215703e700dfa07c23c19c6,0x62bc1626a54c500c9b0a42f8224a,
     0x87badc186f60d00af40f44543210,0xb829e44ae47d0019371144f03918]
 | _=>[0x500b48c2a31e5004550581941240,0x83a78922c01fa0047c0641cc14c1,0x46350ba37f282009b005c1ac1342,
     0x109828b53672710062c08023c19c4,0x4ad45215703e700de007c23c19c6,0x61725626a54c500c8c0a42f8224a,
     0x85d3dc186f60d00aed0f44543210,0xb578a44ae47d0019161144f03918]).map unpackStage
def introduction (b:fO) :List Aux :=
 (match b.val with
 | 0=>[0x70608c27c1cc5,0x15e207c23c19c6,0x10380a42f8224a,0x6f70b834825c8,0x87a0f4454320d,0x12ad0c0368278d,
     0xc500f44543210,0x16e00fc47c33d4,0xb4f1445884014,0x53b0641cc14c1,0x6c208024c1a84,0x19011245183ad8]
 | 1=>[0x70008c27c1cc5,0x159e07c23c19c6,0x101d0a42f8224a,0x6f20b834825c8,0x8750f4454320d,0x128f0c0368278d,
     0xc460f44543210,0x16c00fc47c33d4,0xb491445884014,0x5360641cc14c1,0x6bb08024c1a84,0x1a3011c51c3ad8,
     0x1c641185103a58]
 | 2=>[0x6f908c27c1cc5,0x155c07c23c19c6,0x10030a42f8224a,0x6ee0b834825c8,0x8700f4454320d,0x12710c0368278d,
     0xc3c0f44543210,0x16a00fc47c33d4,0xb421445884014,0x5300641cc14c1,0x6b508024c1a84,0x1a0c11c51c3ad8,
     0x1c391185103a58]
 | 3=>[0x6f308c27c1cc5,0x151b07c23c19c6,0xfe90a42f8224a,0x6e90b834825c8,0x86c0f4454320d,0x12540c0368278d,
     0xc320f44543210,0x16810fc47c33d4,0xb3c1445884014,0x52b0641cc14c1,0x6af08024c1a84,0x19e811c51c3ad8,
     0x1c0e1185103a58]
 | 4=>[0x6ed08c27c1cc5,0x14dc07c23c19c6,0xfd00a42f8224a,0x6e50b834825c8,0x8670f4454320d,0x12380c0368278d,
     0xc280f44543210,0x16610fc47c33d4,0xb351445884014,0x5260641cc14c1,0x6a808024c1a84,0x19c411c51c3ad8,
     0x1be41185103a58]
 | 5=>[0x6e708c27c1cc5,0x149e07c23c19c6,0xfb60a42f8224a,0x6e10b834825c8,0x8620f4454320d,0x121b0c0368278d,
     0xc1f0f44543210,0x16430fc47c33d4,0xb2f1445884014,0x5210641cc14c1,0x6a208024c1a84,0x19a111c51c3ad8,
     0x1bba1185103a58]
 | 6=>[0x6e108c27c1cc5,0x146207c23c19c6,0xf9e0a42f8224a,0x6dc0b834825c8,0x85d0f4454320d,0x11ff0c0368278d,
     0xc150f44543210,0x16240fc47c33d4,0xb291445884014,0x51c0641cc14c1,0x69c08024c1a84,0x197e11c51c3ad8,
     0x1b911185103a58]
 | 7=>[0x45306c1ec1641,0x6cf08c27c1cc5,0x5280902941dc4,0xf6b0802481a46,0xf550a42f8224a,0x6cf0b834825c8,
     0x84f0f4454320d,0x11ae0c0368278d,0x9cb10c4cc3750,0x1c2d0f44543214,0xa3c1506044554,0x1d841204f03918]
 | 8=>[0x4fe0641cc14c1,0x6bd08c27c1cc5,0x6eb08023c19c4,0x131507c23c19c6,0xf0f0a42f8224a,0x6c30b834825c8,
     0x8420f4454320d,0x115f0c0368278d,0xbdd0f44543210,0x15740fc47c33d4,0xb031445884014,0x1ec71144f03918]
 | 9=>[0x4cf0641cc14c1,0x68508c27c1cc5,0x6a808023c19c4,0x114207c23c19c6,0xe380a42f8224a,0x69a0b834825c8,
     0x8150f4454320d,0x106c0c0368278d,0xb840f44543210,0x14670fc47c33d4,0xac81445884014,0x1ce11144f03918]
 | 10=>[0x4a40641cc14c1,0x65008c27c1cc5,0x66a08023c19c4,0xfc207c23c19c6,0xd790a42f8224a,0x6730b834825c8,
     0x7eb0f4454320d,0xf940c0368278d,0xb300f44543210,0x13750fc47c33d4,0xa8f1445884014,0x1b371144f03918]
 | 11=>[0x47c0641cc14c1,0x62008c27c1cc5,0x63108023c19c4,0xe8107c23c19c6,0xcce0a42f8224a,0x64e0b834825c8,
     0x7c30f4454320d,0xed20c0368278d,0xae20f44543210,0x129a0fc47c33d4,0xa591445884014,0x19bd1144f03918]
 | 12=>[0x4800641cc14c1,0x62808c27c1cc5,0x63108023c19c4,0xdfa07c23c19c6,0xc9b0a42f8224a,0x6680b834825c8,
     0x7ea0f4454320d,0xe980c0368278d,0xaf40f44543210,0x12610fc47c33d4,0xa8a1445884014,0x19371144f03918]
 | _=>[0x47c0641cc14c1,0x62c08023c19c4,0x62308c27c1cc5,0xde007c23c19c6,0x6650b834825c8,0xc8c0a42f8224a,
     0xe870c0368278d,0x7e70f4454320d,0xaed0f44543210,0x124e0fc47c33d4,0xa841445884014,0x19161144f03918]).map unpackAux
def movingOrder (b:fO) :List ℕ:= match b.val with
 | 0=>[2,4,5,6]
 | 1=>[2,4,5,6]
 | 2=>[2,4,5,6]
 | 3=>[2,4,5,6]
 | 4=>[2,4,5,6]
 | 5=>[2,4,5,6]
 | 6=>[2,4,5,6]
 | 7=>[2,4,5]
 | 8=>[2,4,5,6]
 | 9=>[2,4,5,6,7]
 | 10=>[2,4,5,6,7]
 | 11=>[2,4,5,6,7]
 | 12=>[2,4,5,6,7]
 | _=>[2,4,5,6,7]
def rankBlend (b:fO) :Option ℚ :=
 if b.val<5 then some (1/ 10) else none
structure TopRow where
 shape :Shape
 YM:ℕ
 avF:ℕ
 poleRank :ℕ
def topDonors (b:fO) :TopRow×TopRow :=
  if b.val<7 then
    (⟨⟨64,87,27,640⟩,12,292256,15643160⟩,
      ⟨⟨120,164,50,3037⟩,19,3137221,0x13094c39⟩)
  else
    (⟨⟨64,87,27,681⟩,12,292256,15643160⟩,
      ⟨⟨128,174,52,3267⟩,22,4005848,0x196ce109⟩)
def O2 (s :Shape) :=s.m*A-1
def anM (h dI:ℕ) (s :Shape) :=O2 s-2*h*dI
abbrev aKj (b:fO) :=Fin (row b).bDZ
abbrev Test (b:fO) :=Option (aKj b)
def seedCap (b:fO) (i:aKj b) :ℕ :=
 ((row b).Kw >>> (12*i.val)) &&& 0xfff
def slotsAt (b:fO) (i:aKj b) :ℕ :=
 (row b).shape.U-(((row b).xF >>> (18*i.val)) &&& 0x3ffff)
def poleRowsAt (b:fO) (U:ℕ) :ℕ :=
 if 12≤b.val then (U+1)*0x43b72bf6462
 else if b.val<4 then 0x1cccacb1996*(U+1)-0x47c4a7d1ca8f0
 else 0x43ae6a1ea00*(U+1)-0xd0d1138a56500
def terminal (b:fO) :Bank :=
 ⟨(row b).shape,(row b).ad1,poleRowsAt b (row b).shape.U⟩
def Lc (b:fO) :Test b→Bank
  | none=>terminal b
  | some i =>
    ⟨{ (terminal b).shape with U:=slotsAt b i },(terminal b).ad1,
      poleRowsAt b (slotsAt b i)⟩
def threshold {b:fO} : Test b→ℕ
 | none=>(row b).bDZ+1
 | some i=>i.val+1
def apo {b:fO} : Test b→ℕ
 | none=>0
 | some i=>seedCap b i+1
def j3 (h:ℕ) (t:Bank) :=
 triangle t.shape.U*t.ad1+2*h*t.arY
def ZN (h:ℕ) (s :Shape) (E v :ℕ) :ℕ :=
  ku s fun q j =>
    let g:=(q-j)/E
    let x :=s.m*A+j-q*(131071-h)
    let c:= fun a=>slots s.U (a*v)
    (∑ a∈Finset.range g,(c a-c (a+1))*(x-2*h*(j+a))) +
      c g*(x-2*h*(j+g))
def TerminalFloor (h:ℕ) (t:Bank) (rows :vP) :Prop :=
  triangle t.shape.U*ku t.shape (fun q j=>t.shape.m*A+j-q*(131071-h)) ≤
    j3 h t + ∑ W∈Finset.range (t.shape.m*A),Module.finrank FX (rows t.shape W)
def NodeUnits {h:ℕ} (D:jF h) :Prop :=
 ∀ i k,(D.block i).eval (DP.ad0 k)≠0
structure ChosenRow {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L)
  (r :ℕ) (s :Shape) where
 raw:DP.Source
 mem:raw∈DP.complete Crt word s (anM h r s)
 nonzero :DP.U4 raw≠0
 cfw:2*h*r<s.m*A
abbrev ChosenRow.jet {h D Crt word r s} (R : @ChosenRow h D Crt word r s) :=
 DP.U4 R.raw
structure akE {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L) (s :Ls) where
 free :ChosenRow Crt word s.dI s.free
 moving:ChosenRow Crt word s.dI s.moving
 no_moving:qQ.aeH free.jet moving.jet
structure Donors (b:fO) {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L) where
 staged : ∀ s∈stages b,akE Crt word s
 initial : ∀ s∈introduction b,ChosenRow Crt word s.dI s.shape
 shared : ∀ s (hs :s∈stages b) (ha : (⟨s.dI,s.free⟩:Aux)∈introduction b),
  (initial _ ha).raw=(staged s hs).free.raw
def wordLift {u del} (M:jG u del) :I→L:= fun i=>algebraMap K L (M.word i)
structure bkU (b:fO) {u del} (M:jG u del) {Γ}
  (F:P1.bje A M Γ) (rows :vP) where
 gH :Finset K
 paid_bound:gH.card≤(row b).prefixFee
 parents :Finset zI
 geometric : ∀ q∈parents,N5 q
 terminal_pass : ∀ q∈parents,∀ P∈rows (terminal b).shape (O2 (terminal b).shape),
  P∈q.asIdeal
 Eh : ∀ γ∈Γ,γ∈gH ∨ ∃ q∈parents,P5_7.axy M F q γ
def W0 (degreeRange :ℕ→Prop) :Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Window b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∀ (i:aKj b) (f :Equation),
      Dt.Reduced f→f.natDegree=i.val+1→degreeRange f.natDegree →
      0<Qt.gY f→vm f (seedCap b i) →
      ∀ T⊆Γ,(∀ γ∈T,yq f (M.label γ) (F.scalar γ)=0) →
      T.card≤(row b).Z1
end
end P5_7_2
end
