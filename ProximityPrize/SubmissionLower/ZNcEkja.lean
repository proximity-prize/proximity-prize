import ProximityPrize.SubmissionLower.Z6s7ala
set_option Elab.async false
open _root_ renaming Fin.sum_univ_succ → zCS, Nat.cast_add → z6H, Nat.cast_mul → z2R, Nat.cast_ofNat → zWE, Nat.le_of_ble_eq_true → zjC, Nat.le_of_lt_succ → zeh, Nat.mul_pos → zah, Nat.sub_add_cancel → zxt, Nat.succ_pos → ztH
set_option maxHeartbeats 5000000
section
set_option autoImplicit true
namespace qhqUbdb
open P6_7_3 (IntroIndex)
open qUrGXob
open qtqUEwc (baseCap base_le historyAt late_caps d dN dD)
open TD (FP a3x)
open pI (weight)
private theorem first_le {o:IntroIndex} {t:Trial} {v :Fin 4→ℕ}
    (hv :MemberFits o t v) {c:ℕ}
    (hc:historyAt t.val 0<((c+1 :ℕ) :ℚ)) :v 0≤ c:= by
  have h: (v 0:ℚ)≤historyAt t.val 0:= by
    rw [historyAt,dite_eq_left t.isLt]
    exact (hv.1 0).trans (min_le_right _ _)
  exact zeh (Nat.cast_lt.mp (h.trans_lt hc))
private def firstCap (o:IntroIndex) (t:Trial) :ℕ :=
  if t.val=9 then min (baseCap o t 0) 1927
  else if t.val=10 then min (baseCap o t 0) 1202
  else if t.val=11 then min (baseCap o t 0) 910
  else baseCap o t 0
private theorem firstCap_le {o:IntroIndex} {t:Trial} {v :Fin 4→ℕ}
    (hv :MemberFits o t v) :v 0≤firstCap o t:= by
  have hb:=base_le hv 0
  unfold firstCap
  split
  · next h =>
    exact le_min hb (first_le hv (by
      rw [h]
      exact late_caps.1.trans_lt (by norm_num)))
  · split
    · next h =>
      exact le_min hb (first_le hv (by
        rw [h]
        exact late_caps.2.1.trans_lt (by norm_num)))
    · split
      · next h =>
        exact le_min hb (first_le hv (by
          rw [h]
          exact late_caps.2.2.2.trans_lt (by norm_num)))
      · exact hb
private def cap (o:IntroIndex) (t:Trial) (k :Fin 4) :ℕ :=
  if k=0 then firstCap o t else baseCap o t k
private theorem cap_le {o:IntroIndex} {t:Trial} {v :Fin 4→ℕ}
    (hv :MemberFits o t v) (k :Fin 4) :v k≤ cap o t k := by
  unfold cap
  split
  · next h=>subst k; exact firstCap_le hv
  · exact base_le hv k
private def jX (o:IntroIndex) (t:Trial) :ℕ :=
  let w:=weight (aHp t) 0
  w 0*cap o t 0+w 1*cap o t 1+w 2*cap o t 2+w 3*cap o t 3
private theorem price_cast (o:IntroIndex) (t:Trial) :
    (jX o t:ℚ)=FP (SS 0 t) (fun k=>(cap o t k :ℚ)) := by
  simp only [jX,FP,SS,Fin.sum_univ_four,z6H,z2R]
private def toTrial (i:Fin 4) :Trial:=⟨i.val+8,by omega⟩
private theorem price_check (o:IntroIndex) (i:Fin 4) :
    jX o (toTrial i)*(dD o (toTrial i)+1)≤dN o (toTrial i) := by
  fin_cases o <;> fin_cases i <;> exact zjC (by with_unfolding_all rfl)
theorem proof :qtqUEwc.c1 := by
  intro o t v ht _ hv
  have hi:t.val-8<4 := by have :=t.isLt; omega
  let i:Fin 4 :=⟨t.val-8,hi⟩
  have he :toTrial i=t:= by
    apply Fin.ext
    exact zxt ht
  have hp:=price_check o i
  rw [he] at hp
  apply (min_le_right _ _).trans
  calc
    _≤FP (SS 0 t) (fun k=>(cap o t k :ℚ)) :=
      a3x (fun _=>Nat.cast_nonneg _) (fun k=>Nat.cast_le.mpr (cap_le hv k))
    _=(jX o t:ℚ) :=(price_cast o t).symm
    _≤d o t:=(le_div_iff₀ (Nat.cast_pos.mpr (ztH _))).mpr (by exact_mod_cast hp)
end qhqUbdb
end
section
set_option autoImplicit true
namespace qaIVK8c
open P6 (p blockLength)
open P6_7_3 (IntroIndex degree)
open qUrGXob (Trial graphRate gap NativeOK nativeRate aSz)
open qtqUEwc (dN dD bN bD)
private abbrev q:ℕ:=p+1
private def table :List (ℕ×ℕ×ℕ×ℕ) :=[
  (10,45,476659,7007592),
  (16,55,631015,11258771),
  (22,65,782505,16480344),
  (33,74,931783,22642959),
  (41,84,1079178,29719960),
  (49,94,1225470,37713333),
  (56,104,1371141,46628288),
  (71,113,1516062,56446165),
  (80,123,1659957,67135800),
  (86,133,1803823,78748515),
  (105,142,1946894,91225572),
  (111,152,2089610,0x63be5c5),
  (129,161,2232154,0x71578f8),
  (135,171,2374234,0x7fc402d),
  (156,180,2516071,0x8f07118),
  (160,190,2657691,0x9f20567),
  (182,199,2798914,0xb009f18),
  (185,209,2940279,0xc1d1ab3),
  (206,218,3080988,0xd45ffac),
  (229,227,3221812,0xe7ca769),
  (231,237,3362416,0xfc06808),
  (254,246,3502683,0x1110f12b),
  (276,255,3643057,0x126f2bd0),
  (277,265,3783253,0x13da740b),
  (301,274,3923076,0x15524378),
  (326,283,4062990,0x16d7acbd),
  (344,292,4202909,0x186a7c78),
  (348,302,4342398,0x1a09848d),
  (374,311,4481872,0x1bb5d8fb),
  (398,320,4621414,0x1d6f9e75),
  (416,329,4760899,0x1f3691e8),
  (420,339,4899981,0x2109965b),
  (446,348,5039109,0x22e9fc48),
  (473,357,5178252,0x24d7ad01),
  (494,366,5317377,0x26d28d38),
  (491,376,5456288,0x28d9eea1),
  (518,385,5595048,0x2aedfb48),
  (546,394,5733816,0x2d0f3c61),
  (574,403,5872600,0x2f3dba1c),
  (595,412,6011357,0x31794b9b),
  (589,422,6149984,0x33c187f8),
  (616,431,6288441,0x36163d1f),
  (645,440,6426861,0x3877ea58),
  (673,449,6565299,0x3ae6c7e7),
  (703,458,6703718,0x3d62ae98),
  (725,467,6842116,0x3feb9ad9),
  (747,476,6980460,0x4281658c),
  (742,486,7118612,0x45236a41),
  (771,495,7256725,0x47d25128),
  (800,504,7394830,0x4a8e3d0d),
  (830,513,7532914,0x4d571d54),
  (860,522,7670985,0x502cfa93)]
private def entry (i:ℕ) :ℕ×ℕ×ℕ×ℕ:=(table[i]?).getD (0,0,0,0)
private abbrev num (i:ℕ) :ℕ:=(entry i).2.2.2
private theorem cTz : (0:ℚ)<gap:= by decide
private theorem rate_num (u v w:ℕ) :
    max (u:ℚ) ((v :ℚ)+(w:ℚ)/gap) =
      ((max (u*gap) (v*gap+w) :ℕ) :ℚ)/gap:= by
  rw [Nat.cast_max,← max_div_div_right cTz.le]
  push_cast
  rw [add_div,mul_div_cancel_right₀ _ cTz.ne',mul_div_cancel_right₀ _ cTz.ne']
private theorem witness (i:Fin 52) :
    ∃ g c W M,NativeOK (i.val+3) g c W M ∧
      nativeRate (i.val+3) g c W=(num i.val :ℚ)/gap:= by
  let g:=(entry i.val).1
  let c:=(entry i.val).2.1
  let W:=(entry i.val).2.2.1
  let e :=i.val+3
  refine ⟨g,c,W,W+1+((g+1)*c/(c+1))*degree,?_,?_⟩
  · unfold NativeOK
    fin_cases i <;> decide
  · unfold nativeRate
    rw [rate_num]
    congr 2
    fin_cases i <;> decide
private abbrev aNum (u v :ℕ) :ℕ:=max (55*u) (q*v)
private abbrev priceOK (u v x y e n:ℕ) :Prop :=
  3*n*y*(55*q*v)+55*x*gap*(u+(12*e*e+24*e)*v) ≤
    55*x*gap*(3*q*v)+3*n*y*(aNum u v*e)
private def checks (u v x y :ℕ) :ℕ→Bool
  | 0=>true
  | i+1 =>
    Nat.ble (3*num i*y*(55*q*v)+55*x*gap*(u+(12*(i+3)*(i+3)+24*(i+3))*v))
      (55*x*gap*(3*q*v)+3*num i*y*(aNum u v*(i+3))) && checks u v x y i
private theorem price_of_check {u v x y k i:ℕ} (hi:i<k) (h:checks u v x y k=true) :
    priceOK u v x y (i+3) (num i) := by
  induction k with
  | zero=>omega
  | succ k ih =>
    simp only [checks,Bool.and_eq_true] at h
    rcases eq_or_lt_of_le (zeh hi) with rfl | hk
    · exact zjC h.1
    · exact ih hk h.2
private theorem aNum_cast (u v :ℕ) (hv :0<v) :
    (aNum u v :ℚ)=55*(v :ℚ)*max ((u:ℚ)/v) (graphRate 55) := by
  have hvq: (0:ℚ)<v :=Nat.cast_pos.mpr hv
  rw [mul_max_of_nonneg _ _ (by positivity),aNum,Nat.cast_max]
  congr 1
  · rw [z2R]
    field_simp
    ring
  · rw [z2R]
    change (q:ℚ)*v=55*(v :ℚ)*((q:ℚ)/55)
    ring
private theorem native_price {u v x y e n:ℕ} {A:ℚ}
    (hc:priceOK u v x y e n) (he :0<e) (hv :0<v) (hy :0<y)
    (hA: (aNum u v :ℚ)=55*(v :ℚ)*A)
    (h0: (u:ℚ)/v/(3*e)+4*e+8≤A) (ha :A<graphRate e) :
    (n:ℚ)/gap*(graphRate e-A)/(graphRate e-((u:ℚ)/v/(3*e)+4*e+8)) ≤
      (x :ℚ)/y := by
  have heq : (0:ℚ)<e :=Nat.cast_pos.mpr he
  have hvq: (0:ℚ)<v :=Nat.cast_pos.mpr hv
  have hyq: (0:ℚ)<y :=Nat.cast_pos.mpr hy
  have hz : (e :ℚ)*graphRate e=(q:ℚ) := by
    unfold graphRate
    field_simp
  have hL:55*(q:ℚ)*v-(aNum u v :ℚ)*e=55*v*e*(graphRate e-A) := by
    rw [hA]
    linear_combination (-55*(v :ℚ))*hz
  have hR:3*(q:ℚ)*v-u-(12*(e :ℚ)*e+24*e)*v =
      3*v*e*(graphRate e-((u:ℚ)/v/(3*e)+4*e+8)) := by
    rw [← hz]
    field_simp
    ring
  have hcQ:=(Nat.cast_le (α:=ℚ)).mpr hc
  simp only [z6H,z2R,zWE] at hcQ
  have hcross :3*(n:ℚ)*y*(55*(q:ℚ)*v-(aNum u v :ℚ)*e) ≤
      55*(x :ℚ)*gap*(3*(q:ℚ)*v-u-(12*(e :ℚ)*e+24*e)*v) := by
    linear_combination hcQ
  rw [hL,hR] at hcross
  apply (div_le_iff₀ (sub_pos.mpr (h0.trans_lt ha))).2
  rw [div_mul_eq_mul_div₀,div_mul_eq_mul_div₀]
  apply (div_le_div_iff₀ cTz hyq).2
  apply (mul_le_mul_iff_right₀ (show 0<165*(v :ℚ)*(e :ℚ) by positivity)).1
  convert hcross using 1 <;> ring
private theorem small_cap (u v :ℕ) (h:u*gap+v*blockLength≤100*gap) :
    (u:ℚ)+(v :ℚ)*blockLength/gap≤100:= by
  calc
    _=((u:ℚ)*gap+(v :ℚ)*blockLength)/gap:= by
      rw [add_div,mul_div_cancel_right₀ _ cTz.ne']
    _≤_:=(div_le_iff₀ cTz).2 (by exact_mod_cast h)
private theorem fTx {u v x y :ℕ} (hv :0<v) (hy :0<y)
    (hd:u<p*v) (hm:100*y≤x) (hc:checks u v x y 52=true) :
    aSz ((u:ℚ)/v) (max ((u:ℚ)/v) (graphRate 55)) ((x :ℚ)/y) := by
  let D:ℚ:=(u:ℚ)/v
  let A:=max D (graphRate 55)
  have hvq: (0:ℚ)<v :=Nat.cast_pos.mpr hv
  have hyq: (0:ℚ)<y :=Nat.cast_pos.mpr hy
  have hd0:0≤D:= by positivity
  have hq: (1000:ℚ)≤graphRate 55:= by
    apply (le_div_iff₀ (by norm_num)).2
    exact_mod_cast (show 1000*55≤q by decide)
  have hfloor : (1000:ℚ)≤A:=hq.trans (le_max_right _ _)
  have hdA:D ≤A:=le_max_left _ _
  have h100: (100:ℚ)≤(x :ℚ)/y :=
    (le_div_iff₀ hyq).2 (by exact_mod_cast hm)
  refine ⟨hd0,(div_lt_iff₀ hvq).2 (by exact_mod_cast hd),le_rfl,by positivity,?_⟩
  intro e he ha
  have he54 :e≤54 := by
    by_contra! hn
    have hx :graphRate e≤graphRate 55 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast hn)
    exact (not_lt_of_ge (hx.trans (le_max_right _ _))) ha
  by_cases h1 :e=1
  · subst e
    right
    left
    refine ⟨rfl,?_⟩
    have hx :1-A/graphRate 1≤1 :=
      sub_le_self _ (div_nonneg (by linarith only [hfloor]) (by positivity))
    exact (mul_le_of_le_one_left (by positivity) hx).trans
      ((small_cap 1 3 (by decide)).trans h100)
  by_cases h2 :e=2
  · subst e
    right
    right
    left
    have MV: (16:ℚ)≤A:= by linarith only [hfloor]
    refine ⟨rfl,MV,?_⟩
    have hx : (graphRate 2-A)/(graphRate 2-16)≤1 :=
      (div_le_one (sub_pos.mpr (MV.trans_lt ha))).2 (sub_le_sub_left MV _)
    rw [mul_div_assoc]
    exact (mul_le_of_le_one_right (by positivity) hx).trans
      ((small_cap 13 8 (by decide)).trans h100)
  have he3:3≤e := by omega
  let i:Fin 52 :=⟨e-3,by omega⟩
  have hie :i.val+3=e :=zxt he3
  have hprice :=price_of_check i.isLt hc
  obtain ⟨g,c,W,M,hw,hr⟩:=witness i
  rw [hie] at hw hr hprice
  have he1q: (1 :ℚ)≤e := by exact_mod_cast he
  have he54q: (e :ℚ)≤54 := by exact_mod_cast he54
  have hx :D/(3*e)≤D/3 :=
    div_le_div_of_nonneg_left hd0 (by norm_num) (by linarith only [he1q])
  have h0:D/(3*e)+4*e+8≤A:= by
    linarith only [hfloor,hdA,he54q,hx]
  right
  right
  right
  refine ⟨he3,g,c,W,M,hw,h0,?_⟩
  rw [hr]
  exact native_price hprice he hv hy (aNum_cast u v hv) h0 ha
set_option exponentiation.threshold 320 in
private theorem checked (o:IntroIndex) (t:Trial) :
    (Nat.ble (dN o t+1) (p*(dD o t+1)) &&
      Nat.ble (100*(bD o t+1)) (bN o t) &&
      checks (dN o t) (dD o t+1) (bN o t) (bD o t+1) 52)=true := by
  fin_cases o <;> fin_cases t <;> decide
theorem proof :qtqUEwc.c2 := by
  intro o t
  have h:=checked o t
  simp only [Bool.and_eq_true] at h
  exact fTx (ztH _) (ztH _)
    (zjC h.1.1) (zjC h.1.2) h.2
end qaIVK8c
end
section
set_option autoImplicit true
namespace qOMTp8b
open Finset qUrGXob qtqUEwc
open P6_7_3 (IntroIndex afa introCap bgK)
open TD (GM FP)
open scoped BigOperators
private theorem fraction_le (n d u:ℕ) (hd:0<d) (h:n*256≤u*d) :
    (n:ℚ)/d≤(u:ℚ)/(256:ℕ) :=
  (div_le_div_iff₀ (Nat.cast_pos.mpr hd) (by decide)).mpr (by exact_mod_cast h)
private theorem charge (n d c e u:ℕ) {x :ℚ} (hd:0<d) (he :0<e)
    (hx :x≤(c:ℚ)/e) (h:n*c*256≤u*(d*e)) :
    (n:ℚ)/d*x≤(u:ℚ)/(256:ℕ) := by
  refine (mul_le_mul_of_nonneg_left hx (by positivity)).trans ?_
  rw [div_mul_div_comm,← z2R,← z2R]
  exact fraction_le _ _ _ (zah hd he) h
private theorem dotVec (a b c:ℚ) (v :GM) :
    FP ![a,b,c,0] v=a*v 0+b*v 1+c*v 2 := by
  simp only [FP,zCS,Fin.sum_univ_zero]
  change a*v 0+(b*v 1+(c*v 2+(0*v 3+0)))= _
  simp only [zero_mul,add_zero,add_assoc]
private theorem stage_le :
    stageBook≤((0x69a009093e70fc1f :ℕ) :ℚ)/(256:ℕ) +
      ((0x45847cf721d0deda :ℕ) :ℚ)/(256:ℕ) := by
  have hstage :stageBook = ∑ s∈({10,11} : Finset bAL),FP (stageDual s) (bAW s) := by
    symm
    apply sum_subset (subset_univ _)
    intro s _ hs
    have h:s≠10 := fun he=>hs (by simp [he])
    have h' : s≠11 := fun he=>hs (by simp [he])
    simp [stageDual,h,h',FP]
  rw [hstage,sum_pair (show (10 :bAL)≠11 by decide)]
  have Kr :stageDual 10 = ![((0x6d9abd44445f3:ℕ) :ℚ)/(125:ℕ),0,0,0] := by
    simp only [stageDual,ite_true,zWE]
  have h11 :stageDual 11 = ![((0x5c7620ab2b933:ℕ) :ℚ)/(100:ℕ),0,0,0] := by
    simp only [stageDual,ite_eq_right (show (11 :bAL)≠10 by decide),ite_true,zWE]
  rw [Kr,h11,dotVec,dotVec]
  simp only [zero_mul,add_zero]
  exact add_le_add
    (charge _ 125 94442 49 _ (by decide) (by decide) late_caps.1 (by decide))
    (charge _ 100 145559 121 _ (by decide) (by decide) late_caps.2.1 (by decide))
private theorem foldStart {α:Type*} (f :α→ℚ) (xs :List α) (a :ℚ) :
    xs.foldl (fun z i=>min z (f i)) a≤a := by
  induction xs generalizing a with
  | nil=>exact le_rfl
  | cons i xs ih=>exact (ih _).trans (min_le_left _ _)
private theorem foldEntry {α:Type*} (f :α→ℚ) (xs :List α) (a :ℚ) {i:α}
    (hi:i∈xs) :xs.foldl (fun z j=>min z (f j)) a≤f i:= by
  induction xs generalizing a with
  | nil=>simp at hi
  | cons j xs ih =>
    rcases List.mem_cons.mp hi with rfl | hm
    · exact (foldStart f xs _).trans (min_le_right _ _)
    · exact ih _ hm
private theorem pre_le (i:afa) (k :Fin 4)
    (hi:i∈([1,2,3,4,5,6,7] :List (Fin 8))) (n d:ℕ)
    (hn:mixedNat (bgK (stage i).free) (refShape 0) k=n)
    (hd: (stage i).dI+1=d) :
    preMoving 0 k≤(n:ℚ)/d:= by
  rw [preMoving,ite_eq_right (show (0:IntroIndex)≠lastOrigin by decide)]
  refine (foldEntry _ _ _ hi).trans_eq ?_
  rw [freeBound,← mixedNat_cast,hn,← Nat.cast_succ]
  exact congrArg (fun x :ℕ=>(n:ℚ)/(x :ℚ)) hd
private theorem free_le :
    freeBook≤((0x2794ba9bb8d792ee :ℕ) :ℚ)/(256:ℕ) +
      ((0x120c878c510d2265:ℕ) :ℚ)/(256:ℕ) +
      ((0xe1367bfc7e04f77:ℕ) :ℚ)/(256:ℕ) := by
  have h0:=pre_le (6:Fin 8) 0 (by decide) 14215 17 (by rfl) (by decide)
  have h1 :=pre_le (7:Fin 8) 1 (by decide) 270373 25 (by rfl) (by decide)
  have h2 :=pre_le (7:Fin 8) 2 (by decide) 1216245 25 (by rfl) (by decide)
  have h:freeDual 0 = ![((0xbd57b98b8bff5:ℕ) :ℚ)/(250:ℕ),
      ((0xaae506b9f98:ℕ) :ℚ)/(25:ℕ),((0xed04b4a9275:ℕ) :ℚ)/(200:ℕ),0] := by
    simp only [freeDual,ite_true,zWE]
  rw [freeBook,sum_eq_single (0:IntroIndex),h,dotVec]
  · exact add_le_add (add_le_add
      (charge _ 250 _ _ _ (by decide) (by decide) h0 (by decide))
      (charge _ 25 _ _ _ (by decide) (by decide) h1 (by decide)))
      (charge _ 200 _ _ _ (by decide) (by decide) h2 (by decide))
  · intro i _ hi
    simp [freeDual,hi,FP]
  · simp
private def costs (i:IntroIndex) :ℕ :=
  ([0x6e7eace4ff3a77cc,0xff82cd833de6b2e0,0xf22db9144b36c04,0,0xdf365368304b499,
    0x10a5fb940b98d1e9,0x2684e218118033e,0x5051bcf653601a05,0x6967d5acc33bed1,0,0,
    0x25699e1f0013d754,0,0] :List ℕ).get i
private theorem row_charge (x y z d e f u:ℕ) (hd:0<d) (he :0<e) (hf :0<f)
    (h: (x*e*f+y*d*f+z*d*e)*256≤u*(d*e*f)) :
    (x :ℚ)/d+(y :ℚ)/e+(z :ℚ)/f≤(u:ℚ)/(256:ℕ) := by
  refine le_of_eq_of_le ?_ (fraction_le _ _ _ (zah (zah hd he) hf) h)
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hd.ne',Nat.cast_ne_zero.mpr he.ne',Nat.cast_ne_zero.mpr hf.ne']
private theorem factor_row (i:IntroIndex) :
    (∑ j,factorJump i j*(introCap i.val j:ℚ))≤(costs i:ℚ)/(256:ℕ) := by
  simp only [Fin.sum_univ_three,factorJump,div_mul_eq_mul_div,← z2R]
  refine row_charge _ _ _ _ _ _ _ (ztH _) (ztH _) (ztH _) ?_
  fin_cases i <;> exact zjC (by with_unfolding_all rfl)
private theorem cost_total: (∑ i:IntroIndex,costs i)=0x21a77dd55b131d09a := by
  simp only [zCS]
  rfl
private theorem aC9 :
    factorBook≤((0x21a77dd55b131d09a :ℕ) :ℚ)/(256:ℕ) := by
  calc
    factorBook ≤ ∑ i:IntroIndex,(costs i:ℚ)/(256:ℕ) :=
      sum_le_sum fun i _=>factor_row i
    _ = _:= by rw [← sum_div,← Nat.cast_sum,cost_total]
theorem proof :qtqUEwc.c4 := by
  unfold qtqUEwc.c4
  refine (add_le_add (add_le_add stage_le free_le) aC9).trans ?_
  simp only [← add_div,← z6H]
  apply (div_le_iff₀ (show (0:ℚ)<((256:ℕ) :ℚ) by decide)).mpr
  rw [← z2R,Nat.cast_le]
  decide
end qOMTp8b
end
