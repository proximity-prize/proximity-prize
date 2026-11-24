import ProximityPrize.SubmissionLower.ZJb37yc
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace P5_7_3_3Q5
open P5 (p blockLength)
open P5_7 (midAgreement)
open P5_7_3 (fO prefixFee)
open qAxtVye
open TD (GM FP running XM alN a3x)
def alpha (b:fO) :ℚ:=1+2*((blockLength:ℚ)/midAgreement)*wX b
def mu (b:fO) :ℚ:=((blockLength - wX b:ℕ) :ℚ)/gap b
def drop (a :ℚ) :=a/graphUnit
def aoV (b:fO) (a :ℚ) :=2*alpha b*drop a
def slope (b:fO) (a :ℚ) :=2*alpha b-(mu b-alpha b)*drop a
def disc (a :ℚ) (g:ℕ) :ℚ:=1-a*g/graphUnit
def raw (b:fO) (a :ℚ) (g:ℕ) :ℚ:=disc a g*alO b g
theorem bgA (b:fO) (a :ℚ) (g:ℕ) :
  raw b a g = -(aoV b a)*(g:ℚ)^2+slope b a*g+(mu b-alpha b) := by
 unfold raw disc alO aoV slope drop mu alpha
 ring
theorem fT3 (b:fO) (a :ℚ) (g m start:ℕ) (hg:start≤g)
   (hq:0≤aoV b a)
   (hl:m=start∨aoV b a*(2*(m:ℚ) - 1)≤ slope b a)
   (hr :slope b a≤aoV b a*(2*(m:ℚ)+1)) :
   raw b a g≤ raw b a m:= by
 rw [bgA,bgA]
 rcases lt_trichotomy g m with h | rfl | h
 · have he :0≤(m:ℚ) - g:=sub_nonneg.mpr (by exact_mod_cast h.le)
   have hgm: (g:ℚ)+m≤2*(m:ℚ) - 1 := by
     have hh: (g:ℚ)+1≤ m:= by exact_mod_cast h
     linarith only [hh]
   have hb:aoV b a*((g:ℚ)+m)≤ slope b a := by
     rcases hl with hm | hm
     · omega
     · exact (mul_le_mul_of_nonneg_left hgm hq).trans hm
   nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
 · exact le_rfl
 · have he :0≤(g:ℚ) - m:=sub_nonneg.mpr (by exact_mod_cast h.le)
   have hgm:2*(m:ℚ)+1≤(g:ℚ)+m:= by
     have hh: (m:ℚ)+1≤g:= by exact_mod_cast h
     linarith only [hh]
   have hb:=hr.trans (mul_le_mul_of_nonneg_left hgm hq)
   nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
def start:fO→ℕ
 | .h2704 | .h2708=>16
 | _=>1
def aoF (b:fO) (a :ℚ) :ℕ :=
 max (start b) ((slope b a/(2*aoV b a)+1/2 :ℚ).floor.toNat)
def extra (b:fO) (cap a h:ℚ) (g:ℕ) :Bool :=
 decide (raw b a g≤h) ||
  (decide (g=1) && decide (disc a g*lineUnit b≤h)) ||
  (decide (2≤g) && decide (branchDegree b g<p) &&
    decide (horizontalBase cap g≤a) &&
    decide (disc a g*horizontalUnit b g≤disc (horizontalBase cap g) g*h))
def cey (b:fO) (cap a h:ℚ) (m:ℕ) :Bool :=
  decide (cap≤a) && decide (0≤a) && decide (0≤h) && decide (0≤aoV b a) &&
    (decide (m=start b) || decide (aoV b a*(2*(m:ℚ) - 1)≤ slope b a)) &&
    decide (slope b a≤aoV b a*(2*(m:ℚ)+1)) && decide (raw b a m≤h) &&
    (List.range' 1 (start b - 1)).all (extra b cap a h)
theorem fTx {b:fO} {c cap a h:ℚ} {m:ℕ}
    (hc:c≤ cap) (ck :cey b cap a h m=true) :aSz b c a h:= by
  simp only [cey,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
  rcases ck with ⟨⟨⟨⟨⟨⟨⟨hd,ha⟩,hh⟩,hq⟩,hl⟩,hr⟩,hp⟩,he⟩
  refine ⟨hc.trans hd,ha,hh,fun g hg _ => ?_⟩
  have hG:0<graphUnit :=Nat.cast_pos.mpr (Nat.succ_pos _)
  have hgr : (0:ℚ)<g:=Nat.cast_pos.mpr hg
  let D:=graphUnit/(g:ℚ)
  have hD:0<D:=div_pos hG hgr
  have form (x :ℚ) :D - x=D *disc x g:= by
    dsimp [D,disc]
    field_simp
  have jX (v t:ℚ) (hv :disc a g*v≤t) : (D-a)*v≤D*t:= by
    rw [form a,mul_assoc]
    exact mul_le_mul_of_nonneg_left hv hD.le
  change (D-a)*alO b g≤D*h∨_
  by_cases hs :start b≤g
  · exact Or.inl (jX _ _ ((fT3 b a g m (start b) hs hq hl hr).trans hp))
  · have hb:HorizontalBand b:= by
      cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (hs hg).elim
    have hm:g∈List.range' 1 (start b - 1) := by
      rw [List.mem_range'_1]
      exact ⟨hg,by omega⟩
    have hx :=List.all_eq_true.mp he g hm
    simp only [extra,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hx
    rcases hx with (hs | ⟨h1,hline⟩) | ⟨⟨⟨h2,hbnd⟩,hbase⟩,hhor⟩
    · exact Or.inl (jX _ _ hs)
    · exact Or.inr (Or.inl ⟨hb,h1,jX _ _ hline⟩)
    · have hcb:horizontalBase c g≤horizontalBase cap g:= by
        unfold horizontalBase
        linarith only [hc]
      refine Or.inr (Or.inr ⟨hb,h2,hbnd,hcb.trans hbase,?_⟩)
      calc
        (D-a)*horizontalUnit b g≤D*(disc (horizontalBase cap g) g*h) :=jX _ _ hhor
        _=(D-horizontalBase cap g)*h:= by rw [form (horizontalBase cap g),mul_assoc]
        _≤(D-horizontalBase c g)*h:=mul_le_mul_of_nonneg_right (sub_le_sub_left hcb _) hh
open private edp from ProximityPrize.SubmissionLower.ZnaG81a
abbrev cL:=List ℕ
def decode (mode :ℕ) :ℕ→ℕ→ℕ→cL
  | 0,_,_=>[]
  | n+1,z,prev =>
    let t:=z%16+((z>>>4)%8)*2^6+((z>>>7)%32)*2^12+((z>>>12)%32)*2^18
    let c:=(z>>>17)%4
    let z :=z>>>19
    let r :=if c=1 then prev else if c=2 then mode else z%2^53
    (t+r*2^24)::decode mode n (if c=0 then z>>>53 else z) r
def bits (xs :cL) (i s w:ℕ) :=
 (xs[i]?.getD 0 >>> s) % 2^w
def degree (xs :cL) (i:ℕ) :ℚ:=bits xs i 24 29
def height (xs :cL) (i:ℕ) :ℚ:=bits xs i 53 24
def t (xs :cL) (i k :ℕ) :=bits xs i (6*k) 6
def corner (b:fO) (i r :ℕ) (k :Fin 4) :ℚ :=
 let s :=nV b i
 alN s.free.shape s.moving.shape r (s.dI+1) true k
lemma paired_le (b:fO) (i r :ℕ) (k :Fin 4)
  (hp:0< r) (hr :r≤(nV b i).dI+1) :
  TD.bf7 (nV b i).free.shape (nV b i).moving.shape (nV b i).dI true k ≤
    corner b i r k := by
 obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hp.ne'
 change ((List.range ((nV b i).dI+1)).foldl
  (fun a j=>min a (corner b i (j+1) k)) (corner b i 1 k))≤ corner b i (j+1) k
 exact edp _ _ _ (List.mem_range.mpr (by omega))
def cap (b:fO) (xs :cL) :ℕ→GM
  | 0=> fun k=>BC b k
  | i+1=> fun k =>
    let r :=min (t xs (i+1) k.val) ((nV b (i+1)).dI+1)
    if r=0 then cap b xs i k else corner b (i+1) r k
theorem bHK (b:fO) (xs :cL) (i:ℕ) (k :Fin 4) :
    V8 b i k≤ cap b xs i k := by
  induction i with
  | zero=>exact le_rfl
  | succ i ih =>
    let r :=min (t xs (i+1) k.val) ((nV b (i+1)).dI+1)
    change min (V8 b i k) _≤ if r=0 then cap b xs i k else corner b (i+1) r k
    split
    · exact (min_le_left _ _).trans ih
    · next h=>exact (min_le_right _ _).trans (paired_le b _ _ k
        (Nat.pos_of_ne_zero h) (min_le_right _ _))
def delta (v :ℕ→GM) (i:ℕ) :GM :=
 fun k=>running v (i+1) k - running v i k
def Z2 (x :ℚ) :ℕ := ⌈x⌉.toNat
theorem rounded_le (x :ℚ) :x≤(Z2 x :ℚ) :=
 (Int.le_ceil x).trans (by
   exact_mod_cast Int.self_le_toNat ⌈x⌉)
def charge (b:fO) (xs :cL) (v :ℕ→GM) (i:ℕ) :=
 Z2 (FP (delta v i) (cap b xs i))
def total (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | i+1=>total f i+f i
theorem blT (b:fO) (xs :cL) (n:ℕ)
    (v :ℕ→GM) :
    XM n v (V8 b)≤(total (charge b xs v) n:ℚ) := by
  induction n with
  | zero=>simp [ XM,total]
  | succ n ih =>
    rw [ XM,Finset.sum_range_succ,← XM,total,Nat.cast_add]
    exact add_le_add ih
      ((a3x (fun _=>sub_nonneg.mpr (le_max_left _ _))
        (bHK b xs n)).trans (rounded_le _))
def seedUpper (b:fO) (xs :cL) :=total (charge b xs (SS b 0)) (Fo b+1)
def bound (b:fO) (xs :cL) (s i:ℕ) :ℚ :=
 min s (FP (SS b 0 i) (cap b xs i))
def lossUpper (b:fO) (xs :cL) (s :ℕ) :=
 total (charge b xs (a5z b (degree xs) (height xs))) (Fo b+1)+s
def payment (b:fO) (xs :cL) (s :ℕ) :=
 Z2 (cb1 b)+lossUpper b xs s+exitFee b
def row (b:fO) (xs :cL) (s i:ℕ) :Bool :=
 cey b (bound b xs s i) (degree xs i) (height xs i) (aoF b (degree xs i))
theorem checked {b xs s} (rows : ∀ i:Fin (Fo b+1),row b xs s i=true)
   (seed :seedUpper b xs≤ s) (small:s<p)
   (gH :payment b xs s≤prefixFee b) :Cv b:= by
 have hs :ash b≤(s :ℚ) :=
   (blT b xs _ _).trans (Nat.cast_le.mpr seed)
 refine ⟨hs.trans_lt (by exact_mod_cast small),degree xs,height xs,
   Z2 (cb1 b),lossUpper b xs s,?_,rounded_le _,?_,gH⟩
 · intro i hi
   let j:Fin (Fo b+1) :=⟨i,Nat.lt_succ_of_le hi⟩
   apply fTx _ (rows j)
   exact min_le_min hs (a3x (fun k=>Nat.cast_nonneg _)
     (bHK b xs i))
 · rw [lossUpper,Nat.cast_add]
   exact add_le_add (blT b xs _ _) hs
set_option quotPrecheck false in
local notation "L!" n:arg m:arg z:arg seed:arg =>
 checked (xs:=decode m n z 0) (s:=seed)
  (by intro i; fin_cases i <;> decide +kernel)
  (Nat.le_of_ble_eq_true (by decide +kernel))
  (by decide +kernel)
  (Nat.le_of_ble_eq_true (by decide +kernel))
theorem l2704:Cv .h2704:=L! 9 0xf387082a5f8 0x32959a28960283a110439af202045f4298803d1aa21009740210883bbc59fc0000410c8842f32a0379488108881bfbaa80d55bc0888808ccab601baa008488038eb43bd16440000c0000 0x1f932000
theorem l2708:Cv .h2708:=L! 9 0x1115500a4ebc 0x2bb258f117da21d0803ac6c0e9c7ec20000921088a41539c38e39010c884593e9fc00004108881f9d1270300180888809d6e347fc9d00848803e96c14938180000c0000 0x1dc80000
theorem l2715:Cv .daC:=L! 8 0x2bba40f18ea70 0x1458a52292906c00011a9fca1ae48ac82108994f1c9c38e39010c8935a9da44924941088946176a28606c808888d661eb2ccccd008488a107a41ace47c0000c0000 0x1c9b4000
theorem l2725:Cv .daF:=L! 8 0x2f0e0ee4080fe 0x1538a221558ce800011dbdf518381c1021089e3fae97d850c418c89655ee9fc000041088935b8aa449249408888e947f2efbe83008488aa5f53e212c380000c0000 0x1b104000
theorem l2750:Cv .rQ:=L! 8 0x364ea2c894477 0x231e7914a5d758000124dcb413bbad4821089f4699171745d418c89951881c38e39010889657001fc00004088890f6a4a8d5105008488c540036e08db80000c0000 0x15744000
theorem l2775:Cv .daL:=L! 11 0x40f640aad54cb 0x6afebd975ef6c46740e18a54cbfd2202dac0e41388c9b68220000cb0594d016a3e8000094528ec8f9b3961084518c89f4817971745d410889658111fc00004108895c24aa094d3c408488ec266ae88ead8000040000 0x1f362000
theorem l2800:Cv .sY:=L! 11 0x655e5870e38e4 0x3254f0d7d2d38234a131ac0fbf338b79d0100000e0001310a708efcd1742148a83fcf1224924c18c89f4e13171745d41088c211131b7a039857460109121937c52a6e708000020cbb354aaaab00000 0x1c25d000
theorem l2900:Cv .s4:=L! 18 0xa105164892493 0x140f88a3051540067040ae06764931c7c2ac807c09112ca1476d8b09000685d5e1c38e390000437c9f33393a5d884a0921c4f1451eb8800024052090a452108b42eaf0e1c71c818c8a319144222884450808c109140d49a2ca63a9800013fc7ec2d5323200000 0x14236000
theorem l2919:Cv .h2919:=L! 17 0xd0c5803871c72 0x65b456708dbd001ae0c638c03b5880c015c0e2cd8434129e900e811928b42a3611f12b6100010fa869cb8ba2ea0000e85ef6049b333c00e8a488f645147ae200a452108a319144222884450088c10115086b224492498109148ba5e2809a7f80001450a812a0f14d80000 0xf248000
theorem l2946:Cv .h2946:=L! 17 0xd0c7183871c72 0x1b002b9a986a5806b840ae07947581863ad9807c09224f71451eb8895b080008a10e9e48924930000680e8a4893dc5147ae200a452108a319144222884451088c101150874f2449249810915001e4248542e800014c4eb726300d800000 0xda9d000
theorem l2950:Cv .s5:=L! 17 0xd0d3103871c72 0xd9e280d31f34a035c205703d51c38c10184403e0295b080008a117da48924930000680e8a48b55c5147ae200a452108a319144222884451088c1011508bed244924981091511119240d264000014d75d225ad14380000 0xd842000
theorem l2980:Cv .tI:=L! 17 0xd0db083871c72 0x38e15f32a0fd880df0416c101f0248cbb05147ae2256c1000240003407452465d828a3d71005229084518c8a211144222884450808c109158ccfa21047c78000155413a225d3b580000 0xc983000
theorem l3000:Cv .s6:=L! 17 0xd0eefa3871c72 0x452c152a02d4b00df0816c11978142a3285700f80a80010002484a0400052481c228a3d71085228c64518c8a211144222884450008c10915d948f1f6388e810915b931e2013b7900000 0xb022000
theorem l3050:Cv .tT:=L! 17 0x1249dac28a3d71 0x2554271389245006f83440ba8e1c71c805b0407c06881751c38e390a000509e6224492498000490940d102ea3871c720000494a4618c8b440ba8e1c71c818c8a211144222884450088c10916be5081b5ca61010916989131bf1b2c80000 0x9e3c000
theorem l3100:Cv .s7:=L! 17 0x124d58228a3d71 0x13d407493999ac039c1a2559870e38e402d8204202a0006895661c38e390000492940d12acc3871c720084494a4618c8b44ab30e1c71c818c8a201144222884450088c109179b48018598f601091770bfb18dfee580000 0x90a3000
theorem l3200:Cv .sJ:=L! 11 0x125452c28a3d71 0xe5523233b11f200011d8d2c61966667010ab240013a11345ea38e1c71c829492321144322884450848c009199c1661364a3e00000 0x6949000
theorem l3400:Cv .tv:=L! 12 0x1259bb628a3d71 0x4096068dc2f1c38e39005b08e840d1b85e3871c720000514c89a370bc70e38e41084500c8a211144222840450848c0000 0x2d36000
theorem l3555:Cv .uH:=L! 12 0x126942828a3d71 0x8258102d82740080005daeedc19666670a6449084500c8a201144222840450848c0000 0x23ba000
theorem proof:qAxtVye.c5
 | .h2704=>l2704
 | .h2708=>l2708
 | .daC=>l2715
 | .daF=>l2725
 | .rQ=>l2750
 | .daL=>l2775
 | .sY=>l2800
 | .s4=>l2900
 | .h2919=>l2919
 | .h2946=>l2946
 | .s5=>l2950
 | .tI=>l2980
 | .s6=>l3000
 | .tT=>l3050
 | .s7=>l3100
 | .sJ=>l3200
 | .tv=>l3400
 | .uH=>l3555
end P5_7_3_3Q5
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace qDqjiRb
noncomputable section


open qAxtVye (nV RU aqE azi aIe arC auN)
open akZ (aB5 aRJ yE ajz cN5 aHP weightedDegree cs5 c2L cfi collect bt8 caQ bKa bLw)
open cu gT pI YX XY Polynomial
open qQ (aeH)
open scoped BigOperators Classical
open private b6z dg6 from ProximityPrize.SubmissionLower.D7


private theorem eo1 {b:P5_7_3.fO} (sched:aqE b)
    {P Q:Jet} (hQ:Q≠0) (hnc:aeH P Q)
    (hQc:oU Q (nV b 0).moving.shape) (T8:ℕ→Jet)
    (rows : ∀ i∈RU b,T8 i≠0∧oU (T8 i) (nV b i).free.shape) :
    ∀ (is :List ℕ),(∀ i∈is,i∈RU b) →
    ∀ (D:Finset Jet) (cap:Fin 3→ℕ),aRJ P D→(∀ j,ajz D j≤ cap j) →
    ∃ S:Finset (Ideal Ambient),aB5 S ∧
      (∀ k old,mass S k≤azi b k is cap old+weightedDegree old D) ∧
      ∀ z R,(∀ i∈is,∀ j a,a≤(nV b i).dI →
        rD (A5 j a (T8 i)) z R=0) →
        rD Q z R=0→(∃ f∈D,rD f z R=0) → ∃ I∈S,IZ I z R:= by
  classical
  intro is
  induction is with
  | nil =>
    intro _ D cap hD hcap
    let t:=(nV b 0).moving.shape
    have gt:=(sched.aE7 0 sched.aXU).2
    obtain ⟨S,hG,hS,hC⟩:=collect D
      (fun f k=>aHP t k f+af1 (yE f 2) (yE f 0) k)
      (fun f z R=>rD f z R=0∧rD Q z R=0)
      (dg6 hD hnc hQc gt.ode.jb gt.ode.small hQ)
    refine ⟨S,hG,?_,?_⟩
    · intro k old
      have hord: (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2] :Fin 4→ℕ) k=af1 (cap 2) (cap 0) k := by
        fin_cases k <;> try rfl
        change 2*cap 0*cap 2=2*cap 2*cap 0
        ring
      have hstep:=cs5 (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty,weightedDegree,ajz,Finset.sum_empty,
        mul_zero,Finset.sum_const_zero,Nat.add_zero] at hstep
      have hsum:=Nat.add_le_add hstep (c2L D cap hcap k)
      calc
        _ ≤ ∑ f∈D,(aHP t k f+af1 (yE f 2) (yE f 0) k) :=hS k
        _≤(weightedDegree old D + aIe cap old t k)+af1 (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _:= by
          simp only [azi,hord]
          ac_rfl
    · intro z R _ hq ⟨f,hf,hz⟩
      exact hC f hf z R ⟨hz,hq⟩
  | cons i is ih =>
    intro his D cap hD hcap
    have hi:=his i (List.mem_cons_self ..)
    have hrest : ∀ l∈is,l∈RU b:= fun l hl=>his l (List.mem_cons_of_mem _ hl)
    let s :=(nV b i).free.shape
    let r :=(nV b i).dI
    let T:=D.filter fun f => ∀ j a,a≤ r→f∣A5 j a (T8 i)
    have hT:T⊆D:=Finset.filter_subset _ _
    have gt:=(sched.aE7 i (sched.brd i hi).2).1
    obtain ⟨hrow,hc⟩:=rows i hi
    have hTcap (j:Fin 3) :
        ajz T j≤ min (cap j) (auN s j/(r+1)) :=
      le_min ((cN5 hT j).trans (hcap j))
        (bLw (hD.mono hT) hrow hc gt.seed_small r
          (fun f hf=>(Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover,hLaterGeom,hLaterCap,hLater⟩ :=
      ih hrest T _ (hD.mono hT) hTcap
    obtain ⟨discard,hDiscardGeom,hDiscardCap,hDiscard⟩ :=
      collect (D \ T) (fun f k=>aHP s k f)
        (fun f z R=>rD f z R=0 ∧
          ∀ j a,a≤ r→ rD (A5 j a (T8 i)) z R=0) (by
        intro f hf
        obtain ⟨hfD,hfT⟩:=Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a,a≤ r→f∣A5 j a (T8 i) :=
          fun hall=>hfT (Finset.mem_filter.mpr ⟨hfD,hall⟩)
        push Not at hn
        obtain ⟨j,a,ha,hd⟩:=hn
        have hirr :=(hD.factors f hfD).1
        obtain ⟨S,hG,hF,hC⟩:=bt8 (b6z hirr hd)
          (caQ hirr.ne_zero) gt.ode.jb (bKa f) (czY.proof s (T8 i) hc j a)
        exact ⟨S,hG,fun k=>(hF k).trans_eq (cfi f s gt.ode.jb k),
          fun z R hr=>hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard∪laterCover,?_,?_,?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w:= fun j=>max (old j) (arC s k j)
      let newCap:= fun j=>min (cap j) (auN s j/(r+1))
      have hstep:=cs5 hT cap old s k hcap
      calc
        _≤ mass discard k+mass laterCover k :=bOC (fun I=>pN I k) _ _
        _≤(∑ f∈D \ T,aHP s k f)+(azi b k is newCap w+weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _=azi b k is newCap w+((∑ f∈D \ T,aHP s k f)+weightedDegree w T) := by ac_rfl
        _≤azi b k is newCap w+(weightedDegree old D + aIe cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _:= by
          change _=(aIe cap old s k+azi b k is newCap w)+weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f,hf,hz⟩
      by_cases h:f∈T
      · obtain ⟨I,hI,hMark⟩:=hLater z R
          (fun l hl=>hder l (List.mem_cons_of_mem _ hl)) hq ⟨f,h,hz⟩
        exact ⟨I,Finset.mem_union_right _ hI,hMark⟩
      · obtain ⟨I,hI,hMark⟩:=hDiscard f (Finset.mem_sdiff.mpr ⟨hf,h⟩) z R
          ⟨hz,hder i (List.mem_cons_self ..)⟩
        exact ⟨I,Finset.mem_union_left _ hI,hMark⟩
end
end qDqjiRb
end
