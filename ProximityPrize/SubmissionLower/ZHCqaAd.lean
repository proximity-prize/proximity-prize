import ProximityPrize.SubmissionLower.ZOrwy2c
import ProximityPrize.SubmissionLower.ZGAUtmc
set_option Elab.async false
open _root_ renaming Finset.Ico → zUb, Finset.range_mono → znF, Finset.sum_congr → zUo, Finset.sum_le_sum_of_subset → zZL, Nat.add_le_add → z9f, Nat.add_zero → zXY, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.mul_left_comm → zZ0, Nat.sub_eq_zero_of_le → zT5, Nat.sub_le_sub_right → zIu, Nat.zero_add → zbc
section
set_option autoImplicit true
namespace q2w4Sxc
open aR (Shape aO)
open P6_6 P6_6_8
def c1 :Prop :=fO 0
def c2 :Prop :=fO 3
def c3:Prop :=fO 4
def c4 :Prop :=fO 5
def c5:Prop :=fO 6
def c6:Prop :=fO 7
private theorem cDD {a b c:Shape} (h:aO a b) (g:aO b c) :aO a c :=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.trans g.2.2⟩
private theorem refine_mem {lo r hi:Shape} (hr :JetShape r)
    (hl:aO lo r) (hh:aO r hi) :
    aO (refineBox lo hi).1 r∧aO r (refineBox lo hi).2 := by
  obtain ⟨_,h3,h2⟩:=hr
  obtain ⟨hlb,hlj,hlt⟩:=hl
  obtain ⟨hhb,hhj,hht⟩:=hh
  have htb:r.t≤ r.b:= by omega
  have ht:r.t≤ min hi.t (min hi.b (hi.j/3)) :=
    le_min hht (le_min (htb.trans hhb) (by omega))
  have hb: (lo.j+1 - min hi.t (min hi.b (hi.j/3)))/2≤ r.b:= by omega
  exact ⟨⟨max_le hlb (max_le (hlt.trans htb) hb),max_le hlj (by omega),hlt⟩,
    ⟨hhb,le_min hhj (by omega),ht⟩⟩
private theorem trim_mem {lo r hi:Shape} (hr :JetShape r)
    (hl:aO lo r) (hh:aO r hi) :
    aO (trimBox lo hi).1 r∧aO r (trimBox lo hi).2 := by
  obtain ⟨a,b⟩:=refine_mem hr hl hh
  obtain ⟨c,d⟩:=refine_mem hr a b
  exact refine_mem hr c d
private theorem order_fits {v :Shape} (hv :W0 v) {k :ℕ} (hk :k≤132) :
    aO (v.scale k) Wk := by
  obtain ⟨b,j,t,_⟩:=c8J hv
  exact ⟨(Nat.mul_le_mul hk b).trans (by decide :132*24≤4025),
    (Nat.mul_le_mul hk j).trans (by decide :132*7≤1710),
    (Nat.mul_le_mul hk t).trans (by decide :132*2≤570)⟩
private theorem move_order {v lo r :Shape} (h:aO lo r) {k :ℕ}
    (hk :CompanionTest v lo k∨k=1) :CompanionTest v r k∨k=1 := by
  rcases hk with hk | rfl
  · exact .inl (by
      by_contra hc
      exact not_companion_down h hc hk)
  · exact .inr rfl
private theorem priced {v lo r :Shape} (hv :W0 v) (h:aO lo r)
    {k :ℕ} {dR:Bool} (hk :Usable v lo k) (hf :selfFee v r k dR≤dot (Lw v) r) :
    ∃ k dR,0<k∧aO (v.scale k) Wk∧(CompanionTest v r k∨k=1) ∧
      selfFee v r k dR≤dot (Lw v) r :=
  ⟨k,dR,hk.1,order_fits hv hk.2.1,move_order h hk.2.2,hf⟩
private theorem dot_mono (c:Shape) {lo r :Shape} (h:aO lo r) :dot c lo≤dot c r :=
  z9f (z9f (zBI _ h.1) (zBI _ h.2.1))
    (zBI _ h.2.2)
private theorem same_top {lo r hi:Shape} (hl:aO lo r) (hh:aO r hi) (hp:0< r.t)
    (ht:hi.t=1∨2≤lo.t) :r.t=1↔hi.t=1 := by
  have hl' := hl.2.2
  have hh' := hh.2.2
  rcases ht with h | h <;> omega
theorem iK {v lo hi r :Shape} (hv :W0 v) (h:Certificate v lo hi)
    (hr :JetShape r) (ht:0< r.t) (hn : ¬ CompanionTest v r (sharedOrder v))
    (hl:aO lo r) (hh:aO r hi) :
    ∃ k dR,0<k∧aO (v.scale k) Wk∧(CompanionTest v r k∨k=1) ∧
      selfFee v r k dR≤dot (Lw v) r := by
  induction h with
  | empty he=>exact (he (cDD hl hh)).elim
  | prune hp=>exact (not_companion_down hl hn hp).elim
  | trim _ ih =>
    obtain ⟨a,b⟩:=trim_mem hr hl hh
    exact ih a b
  | regular hk hs htop hf =>
    exact priced hv hl hk ((fee_mono hr.2.1 hh (same_top hl hh ht hs) htop).trans (hf.trans (dot_mono _ hl)))
  | splitB m _ _ ihl ihr =>
    by_cases h:r.b≤ m
    · exact ihl hl ⟨h,hh.2⟩
    · exact ihr ⟨by change m+1≤ r.b; omega,hl.2⟩ hh
  | rK m _ _ ihl ihr =>
    by_cases h:r.j≤ m
    · exact ihl hl ⟨hh.1,h,hh.2.2⟩
    · exact ihr ⟨hl.1,by change m+1≤ r.j; omega,hl.2.2⟩ hh
  | splitT m _ _ ihl ihr =>
    by_cases h:r.t≤ m
    · exact ihl hl ⟨hh.1,hh.2.1,h⟩
    · exact ihr ⟨hl.1,hl.2.1,by change m+1≤ r.t; omega⟩ hh
private theorem cV {v :Shape} (hv :W0 v) :v.j=0∨3≤v.j∧v.j≤7:= by
  rcases hv with h | h
  · subst v
    exact .inl rfl
  · have ht:=h.1.1
    have hj:=h.1.2.1
    have h7:=(c8J (.inr h)).2.1
    exact .inr ⟨by omega,h7⟩
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
    P6_6_8.c4 := by
  intro v hv r hr hfirst hsmall ht hlast
  have hcert:Certificate v ⟨1,3,1⟩ (cap v) := by
    rcases cV hv with h0 | ⟨h3',h7⟩
    · exact h1 v hv h0
    · interval_cases hj:v.j
      · exact h2 v hv hj
      · exact h3 v hv hj
      · exact h4 v hv hj
      · exact h5 v hv hj
      · exact h6 v hv hj
  apply iK hv hcert hr ht hsmall
  · exact ⟨hr.1,by have h:=hr.2.1; change 3≤ r.j; omega,ht⟩
  · exact ⟨le_min hlast.1 hfirst.1,le_min hlast.2.1 hfirst.2.1,le_min hlast.2.2 hfirst.2.2⟩
end q2w4Sxc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qpPqCOe
open aR (Shape)
open P6_6 (Gq V7)
open P6_6_8 (pS aUJ)
open wV (HY aWp)
open private bgn eO4 ow from ProximityPrize.SubmissionLower.Zqd3kta
open private bSj.aTY bSj.ay9 total eL3 clip eNO from ProximityPrize.SubmissionLower.E6
open private eiI from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
private def cum (d j:ℕ) :ℕ :=
  if d=0 then 0 else FI.a3U (d - 1) j
private theorem cum_eq (d j t:ℕ) (h:j/3≤t) :
    cum d j=HY d j t:= by
  by_cases hd:d=0
  · simp [cum,HY,hd]
  simp only [cum,HY,hd,ite_false,AJ.bmI]
  rw [ite_eq_right (by omega),Nat.sub_zero]
private theorem boa {a b j:ℕ} (h:a≤b) :cum a j≤ cum b j:= by
  rw [cum_eq a j (j/3) le_rfl,cum_eq b j (j/3) le_rfl,bSj.aTY,bSj.aTY]
  exact zZL (znF h)
private theorem saturation {r j t c:ℕ} (hc:j≤ c) :
    V7 (min r c) j t=V7 r j t:= by
  simp only [bSj.ay9,total]
  refine zUo rfl fun z hz=>zUo rfl fun y hy =>
    zUo rfl fun x hx => ?_
  simp only [Finset.mem_range] at hz hy hx
  simp only [le_min_iff,show z+y + x≤ c by omega,and_true]
private def loss (u j:ℕ) :ℕ×ℕ×ℕ→ℕ
  | (lo,hi,c) =>
    let a :=max (lo - u) (c+1)
    let b:=hi - u
    if j≤ c∨b≤a then 0
    else cum b j - cum a j-(b-a)*(cum (c+1) j - cum c j)
private theorem band_loss (u j lo hi c:ℕ) (hhi:hi≤4026) (hlh:lo≤hi) :
    aWp u 4026 j (j/3) (lo,hi,c)+loss u j (lo,hi,c) =
      cum (hi-u) j - cum (lo-u) j:= by
  let a :=lo-u
  let b:=hi-u
  have hab:a≤b:=zIu hlh u
  by_cases hj:j≤ c
  · simp only [loss,hj,true_or,ite_true,zXY]
    rw [eL3 _ _ _ _ _ _ _ hlh]
    simp only [clip,min_eq_right hhi,min_eq_right (hlh.trans hhi)]
    change (∑ r∈zUb a b,V7 (min r c) j (j/3))= _
    simp_rw [saturation hj,cum_eq _ _ _ le_rfl,bSj.aTY]
    exact (eNO _ hab).symm
  by_cases h:b≤ c+1
  · have he :hi-u≤ max (lo-u) (c+1) :=h.trans (le_max_right _ _)
    simp only [loss,hj,false_or,he,ite_true,zXY]
    simp only [aWp,min_eq_right hhi,show min b (c+1)=b from min_eq_left h,
      show min a b=a from min_eq_left hab,
      show b - max a (c+1)=0 from zT5 he,zero_mul,zXY,
      cum_eq _ _ _ le_rfl,a,b]
  have hba : ¬ b≤ max a (c+1)∨b=a := by omega
  by_cases heq :b=a
  · have he :hi-u≤ max (lo-u) (c+1) :=heq.le.trans (le_max_left _ _)
    simp only [loss,hj,false_or,he,ite_true,zXY]
    rw [eL3 _ _ _ _ _ _ _ hlh]
    simp only [clip,min_eq_right hhi,min_eq_right (hlh.trans hhi)]
    change (∑ r∈zUb a b,V7 (min r c) j (j/3))= _
    change (∑ r∈zUb a b,V7 (min r c) j (j/3))=cum b j - cum a j
    rw [heq,Finset.Ico_self,Finset.sum_empty,Nat.sub_self]
  have hb:max a (c+1)≤b:=max_le hab (by omega)
  have hlt : ¬ hi-u≤ max (lo-u) (c+1) :=hba.resolve_right heq
  let d:=c+1
  let e :=max a d
  have hupper : (b-e)*(cum d j - cum c j)≤ cum b j - cum e j:= by
    rw [cum_eq b j _ le_rfl,cum_eq e j _ le_rfl,cum_eq d j _ le_rfl,cum_eq c j _ le_rfl,
      bSj.aTY,bSj.aTY,bSj.aTY,bSj.aTY]
    rw [show d=c+1 from rfl,Finset.sum_range_succ,Nat.add_sub_cancel_left,
      eNO _ hb]
    calc
      _ = ∑ _∈zUb e b,V7 c j (j/3) := by
        simp only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.card_Ico]
      _≤_:=Finset.sum_le_sum fun r hr =>
        (eiI (by have :=(Finset.mem_Ico.mp hr).1; omega) le_rfl le_rfl)
  have hsplit :cum (min a d) j=cum a j+cum d j - cum e j:= by
    rcases le_total a d with h | h
    · simp [e,min_eq_left h,max_eq_right h]
    · simp [e,min_eq_right h,max_eq_left h]
  have ha' : cum a j≤ cum e j:=boa (le_max_left _ _)
  have hd' : cum d j≤ cum e j:=boa (le_max_right _ _)
  have hb' : cum e j≤ cum b j:=boa hb
  have hm' : cum (min a d) j≤ cum d j:=boa (min_le_right _ _)
  have hs' : cum e j≤ cum a j+cum d j:= by
    rcases le_total a d with hh | hh
    · simp [e,max_eq_right hh]
    · simp [e,max_eq_left hh]
  simp only [loss,hj,false_or,hlt,ite_false,aWp,min_eq_right hhi,
    show min (hi-u) (c+1)=c+1 from min_eq_right (by change c+1≤b; omega),
    ← cum_eq _ _ _ le_rfl]
  change cum d j - cum (min a d) j+(b-e)*(cum d j - cum c j) +
    (cum b j - cum e j-(b-e)*(cum d j - cum c j))=cum b j - cum a j
  omega
private theorem arL (u j stop start:ℕ) (bs :List (ℕ×ℕ×ℕ))
    (h:ow start stop bs) (htop:stop≤4026) :
    start≤ stop ∧
    (bs.map (aWp u 4026 j (j/3))).sum+(bs.map (loss u j)).sum =
      cum (stop-u) j - cum (start-u) j:= by
  induction bs generalizing start with
  | nil =>
    change start=stop at h
    subst start
    exact ⟨le_rfl,(Nat.sub_self _).symm⟩
  | cons hd tl ih =>
    obtain ⟨lo,hi,c⟩:=hd
    obtain ⟨heq,hlh,_,hc⟩:=h
    subst start
    obtain ⟨hst,he⟩:=ih hi hc
    have h₁:cum (lo-u) j≤ cum (hi-u) j:=boa (zIu hlh u)
    have h₂:cum (hi-u) j≤ cum (stop-u) j:=boa (zIu hst u)
    have h₃:=band_loss u j lo hi c (hst.trans htop) hlh
    refine ⟨hlh.trans hst,?_⟩
    simp only [List.map_cons,List.sum_cons]
    omega
def stockPlain (x :Shape) :ℕ :=
  if x.b≤4025∧x.j≤1710∧x.t≤570 then
    let j:=1710 - x.j
    cum (4026 - x.b) j-(bgn.map (loss x.b j)).sum
  else 0
theorem stockPlain_eq (x :Shape) (h:3*x.t≤x.j) :stockPlain x=Gq x := by
  rw [← aUJ]
  unfold stockPlain pS
  split
  · rename_i hx
    have ht: (1710-x.j)/3≤570-x.t:= by omega
    have he :aWp x.b 4026 (1710-x.j) (570-x.t) =
        aWp x.b 4026 (1710-x.j) ((1710-x.j)/3) := by
      funext kA
      obtain ⟨a,b,c⟩:=kA
      simp only [aWp,← cum_eq _ _ _ ht,← cum_eq _ _ _ le_rfl]
    rw [he]
    have hl:=(arL x.b (1710-x.j) 4026 0 bgn eO4 le_rfl).2
    rw [Nat.zero_sub,show cum 0 (1710-x.j)=0 from rfl,Nat.sub_zero] at hl
    dsimp only
    omega
  · rfl
end qpPqCOe
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qpPqCOe
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
open private WC bP5 aEH byM from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
private def xF (n s :ℕ) :List ℕ :=
  let ws :=List.replicate (n/s) s
  if n % s=0 then ws else ws ++ [n % s]
private theorem widths_sum (n s :ℕ) : (xF n s).sum=n:= by
  have h:=Nat.mod_add_div n s
  by_cases hm:n % s=0
  · simpa [xF,hm,nsmul_eq_mul,Nat.mul_comm] using h
  · simpa [xF,hm,nsmul_eq_mul,Nat.mul_comm,Nat.add_comm] using h
abbrev count (n s :ℕ) :ℕ:=(n+8*s - 1)/(8*s)
private abbrev value (z :ℕ) :ℕ:=z % 0x800000*0x400000
def total:ℕ→ℕ→ℕ
  | 0,_=>0
  | f+1,z=>value z+total f (z >>> 23)
def Blocks (g:ℕ→ℕ) (s :ℕ) :ℕ→ℕ→ℕ→ℕ→Prop
  | 0,_,n,_=>n=0
  | f+1,start,n,z =>
    let q:=min n (8*s)
    Nat.ble (aEH g start (xF q s)) (value z)=true ∧
      Blocks g s f (start+q) (n-q) (z >>> 23)
private theorem bVF {g:ℕ→ℕ} (hg:Antitone g) (s f start n z :ℕ)
    (h:Blocks g s f start n z) :
    WC g start n≤total f z := by
  induction f generalizing start n z with
  | zero =>
    change n=0 at h
    simp [h,WC,total]
  | succ f ih =>
    let q:=min n (8*s)
    have hsum:=byM hg (xF q s) start
    rw [widths_sum] at hsum
    have hblock :aEH g start (xF q s)≤value z := by simpa only [Nat.ble_eq] using h.1
    have htail:=ih (start+q) (n-q) (z >>> 23) h.2
    conv_lhs=>rw [← Nat.add_sub_of_le (show q≤n from min_le_left ..),bP5]
    exact z9f (hsum.trans hblock) htail
def retainedLayer (v :Shape) (d:ℕ) :ℕ:=stockPlain (v.scale (d+1))
private def S6 (v r :Shape) (k d:ℕ) :ℕ:=stockPlain (used v r k d)
private theorem layer_eq {v r :Shape} {k :ℕ} (hv :3*v.t≤v.j) (hr :3*r.t≤ r.j) :
    S6 v r k=layerMass v r k := by
  funext d
  unfold S6 layerMass
  rw [aUJ,stockPlain_eq]
  change 3*((d+1)*v.t+(d+2-k)*r.t)≤(d+1)*v.j+(d+2-k)*r.j
  rw [Nat.mul_add,zZ0 3,zZ0 3]
  exact z9f (zBI _ hv) (zBI _ hr)
private theorem retained_eq {v r :Shape} {k d:ℕ} (hd:d+2≤k) :
    S6 v r k d=retainedLayer v d:= by
  simp only [S6,used,retainedLayer,zT5 hd,Shape.scale,Shape.plus,
    Nat.zero_mul,zXY]
abbrev jM (v :Shape) (z :ℕ) :Prop :=
  Blocks (retainedLayer v) 1 (count (sharedOrder v - 1) 1) 0 (sharedOrder v - 1) z
abbrev earlyValue (v :Shape) (z :ℕ) :ℕ:=total (count (sharedOrder v - 1) 1) z
def MassChecks (v r :Shape) (k start n s prev z :ℕ) :Prop :=
  S6 v r k n=0∧Nat.blt (prev+total (count (n-start) s) z) gG=true ∧
    Blocks (S6 v r k) s (count (n-start) s) start (n-start) z
theorem mass_sound {v r :Shape} {k start n s prev z :ℕ}
    (hv :3*v.t≤v.j) (hr :3*r.t≤ r.j) (h:MassChecks v r k start n s prev z)
    (he :WC (S6 v r k) 0 start≤prev) :CompanionTest v r k := by
  have hl:=layer_eq (k :=k) hv hr
  have hb:=bVF (hl ▸ layer_anti v r k) s (count (n-start) s) start (n-start) z h.2.2
  have hadd:=z9f he hb
  have ha :=bP5 (S6 v r k) 0 start (n-start)
  rw [zbc] at ha
  rw [← ha,hl] at hadd
  have hlt:prev+total (count (n-start) s) z<gG:= by simpa only [Nat.blt_eq] using h.2.1
  have hle :=zZL (f :=layerMass v r k)
    (znF (show n≤ start+(n-start) by omega))
  apply companion_of_mass (n:=n)
  · exact hl ▸ h.1
  · rw [mass,AJ.bOw]
    exact hle.trans_lt (by simpa only [WC,zbc] using hadd.trans_lt hlt)
theorem no_early (v r :Shape) (k :ℕ) :WC (S6 v r k) 0 0≤0:= by
  simp [WC]
theorem early_bound {v r :Shape} {z :ℕ}
    (hv :3*v.t≤v.j) (h:jM v z) :
    WC (S6 v r (sharedOrder v)) 0 (sharedOrder v - 1)≤earlyValue v z := by
  let k :=sharedOrder v
  have hleft:WC (S6 v r k) 0 (k-1)=WC (retainedLayer v) 0 (k-1) := by
    unfold WC
    refine zUo rfl fun d hd => ?_
    have hd:=Finset.mem_range.mp hd
    rw [zbc,retained_eq (by omega)]
  have hrm:Antitone (retainedLayer v) := by
    have stockEq (d:ℕ) :retainedLayer v d=Gq (v.scale (d+1)) := by
      apply stockPlain_eq
      change 3*((d+1)*v.t)≤(d+1)*v.j
      rw [zZ0]
      exact zBI _ hv
    intro d e hde
    rw [stockEq,stockEq]
    have he :=Nat.add_le_add_right hde 1
    exact dNb ⟨ztf _ he,ztf _ he,
      ztf _ he⟩
  rw [hleft]
  exact bVF hrm _ _ _ _ _ h
end qpPqCOe
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qpPqCOe
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
private def offerCheck (v a lo hi:Shape) (k :ℕ) :Bool :=
  decide (0<k∧k≤132∧(hi.t=1∨2≤lo.t)∧3*hi.t≤hi.j) &&
    Nat.ble (selfFee v hi k false) (dot a lo)
inductive Tree where
  | cut (kd point :ℕ) (left right:Tree)
  | leaf (k n s z :ℕ)
def read (zo:ℕ) :ℕ→ℕ→Tree×ℕ
  | 0,z=>(.leaf 0 0 0 0,z)
  | fuel+1,z =>
    let op:=z % 512
    let next:=z/512
    if op<399 then
      let (a,rest) :=read zo fuel next
      let (b,rest) :=read zo fuel rest
      (.cut (op/ 133) (op % 133) a b,rest)
    else if op=400 then (.leaf 1 0 0 0,next)
    else
      let k :=op-399
      let n:=next % 512
      let s :=next/512 % 256
      let rest:=next >>> 17
      let bits :=23*count (n-(if k=0 then zo else 0)) s
      (.leaf k n s (rest % (2^bits)),rest >>> bits)
private def cut (kd m:ℕ) (lo hi:Shape) : (Shape×Shape)×(Shape×Shape) :=
  if kd=0 then ((lo,{hi with b:=m}),({lo with b:=m+1},hi))
  else if kd = 1 then ((lo,{hi with j:=m}),({lo with j:=m+1},hi))
  else ((lo,{hi with t:=m}),({lo with t:=m+1},hi))
private theorem cut_sound {v :Shape} (kd m:ℕ) (lo hi:Shape)
    (h:Certificate v (cut kd m lo hi).1.1 (cut kd m lo hi).1.2)
    (g:Certificate v (cut kd m lo hi).2.1 (cut kd m lo hi).2.2) :
    Certificate v lo hi:= by
  by_cases hb:kd=0
  · exact .splitB m (by simpa [cut,hb] using h) (by simpa [cut,hb] using g)
  by_cases hj:kd = 1
  · exact .rK m (by simpa [cut,hb,hj] using h) (by simpa [cut,hb,hj] using g)
  · exact .splitT m (by simpa [cut,hb,hj] using h) (by simpa [cut,hb,hj] using g)
def jf (v a :Shape) (pre :ℕ) (tree :Tree) (lo hi:Shape) :Prop :=
  let (lo,hi) :=trimBox lo hi
  match tree with
  | .cut kd m l r =>
    let (left,right) :=cut kd m lo hi
    jf v a pre l left.1 left.2∧jf v a pre r right.1 right.2
  | .leaf k n s z =>
    if k=0 then MassChecks v lo (sharedOrder v) (sharedOrder v - 1) n s pre z
    else if k=1 then offerCheck v a lo hi k=true
    else offerCheck v a lo hi k=true∧MassChecks v lo k 0 n s 0 z
private theorem c2a {v lo hi:Shape} {k :ℕ}
    (h:offerCheck v (Lw v) lo hi k=true)
    (hk :CompanionTest v lo k∨k=1) :
    Certificate v lo hi:= by
  simp only [offerCheck,Bool.and_eq_true,decide_eq_true_eq,Nat.ble_eq] at h
  exact .regular ⟨h.1.1,h.1.2.1,hk⟩ h.1.2.2.1 h.1.2.2.2 h.2
private theorem checks_sound (v :Shape) (hv :3*v.t≤v.j) (zo:ℕ)
    (hp:jM v zo) (tree :Tree) (lo hi:Shape)
    (h:jf v (Lw v) (earlyValue v zo) tree lo hi) :Certificate v lo hi:= by
  induction tree generalizing lo hi with
  | cut kd m l r ihl ihr =>
    apply Certificate.trim
    exact cut_sound kd m _ _ (ihl _ _ h.1) (ihr _ _ h.2)
  | leaf k n s z =>
    apply Certificate.trim
    have hr :3*(trimBox lo hi).1.t≤(trimBox lo hi).1.j:=le_max_right _ _
    unfold jf at h
    dsimp only at h
    split at h
    · exact .prune (mass_sound hv hr h (early_bound hv hp))
    · split at h
      · exact c2a h (.inr (by assumption))
      · exact c2a h.1 (.inl (mass_sound hv hr h.2 (no_early ..)))
theorem replay (v a :Shape) (code preCode :ℕ) (hv :3*v.t≤v.j) (ha :Lw v=a)
    (hp:jM v preCode)
    (h:jf v a (earlyValue v preCode) (read (sharedOrder v - 1) 20 code).1 ⟨1,3,1⟩ (cap v)) :
    Certificate v ⟨1,3,1⟩ (cap v) :=
  checks_sound v hv preCode hp _ _ _ (ha ▸ h)
end qpPqCOe
end
