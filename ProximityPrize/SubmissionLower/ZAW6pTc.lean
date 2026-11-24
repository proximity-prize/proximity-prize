import ProximityPrize.SubmissionLower.AJ
import ProximityPrize.SubmissionLower.ZITfVad
import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZqXQOta
import ProximityPrize.SubmissionLower.ZNc08Oa
import ProximityPrize.SubmissionLower.ZIBb1mb
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset.filter_subset → zT0, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_le_sum → zQk, Finset.sum_range_add → zGH, Fintype.card → zhP, Fintype.card_le_of_injective → zWJ, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
namespace qaTCFjd
open qK9H6va
open UO (bAQ cAy cqd aFb)
open baV (above)
open fP (Ew cF xH oG
  qI aAs Qg)
open scoped BigOperators
open private order ao5 from ProximityPrize.SubmissionLower.CG
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
def KC (q r cap:ℕ) :Prop :=
  (Gy q (offset r)).rank≤ cap
def DV (q r :ℕ) :ℕ:=155-(q+r)
theorem aq6 (q r :ℕ) :
    (Vm q (offset r)).toNat=DV q r := by
  unfold Vm offset DV
  omega
def ajZ (q r :ℕ) (U:ℕ→ℕ→Prop) (e :ait q (offset r)) :Prop :=
  56+e.val 0+3*(e.val 3 - 16)≤ iO q+order e.val+r ∧
    U (order e.val) (e.val 3)
def ajY (q r :ℕ) (U:ℕ→ℕ→Prop) (m:XN q (offset r)) :Prop :=
  order m.val<DV q r ∧ ¬ U (order m.val) (m.val 3)
theorem aEb (q r :ℕ) (U:ℕ→ℕ→Prop) (hU:bAQ U) (e :ait q (offset r))
    (m:XN q (offset r)) (hn:Gy q (offset r) e m≠0) :
    ajZ q r U e∨ajY q r U m:= by
  have hle (i:Fin 4) (hi:i=1∨i=2∨i=3) :m.val i≤e.val i:= by
    by_contra! hg
    have hz :=Nat.choose_eq_zero_of_lt hg
    rcases hi with rfl | rfl | rfl <;> exact hn (by simp [Gy,prefixMatrix,hz])
  have h₁:=hle 1 (by simp)
  have h₂:=hle 2 (by simp)
  have h₃:=hle 3 (by simp)
  have hmc:=m.property
  simp only [Ew,xH,cF] at hmc
  obtain ⟨_,hlo,_,hcap⟩:=hmc
  unfold offset at hlo
  obtain ⟨hd,hw⟩:=e.property
  rw [cF] at hd
  rw [oG] at hw
  have hw' := hw.trans_le (aq6 q r).le
  classical
  by_cases ha :U (order m.val) (m.val 3)
  · left
    refine ⟨?_,?_⟩
    · unfold order
      omega
    · exact hU (by unfold order; omega) (by unfold order; omega) h₃ ha
  · right
    refine ⟨?_,ha⟩
    unfold order
    omega
def aEG (d h r z c:ℕ) :ℕ :=
  min (d+c+1 - z) (min ((h+2 - z)/3) (d+z+r+1-(56+3*(c - 16))))
def a2K (d z :ℕ) :ℕ:=d+z - 56
def aHb (d r z c:ℕ) :ℕ :=
  if c≤16 then min (d+c+1 - z) (d+z+r+1 - 56)-a2K d z else 0
private def a3V (d h r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)] (z c:ℕ) (row:Bool) :ℕ :=
  if row then (if U z c then aEG d h r z c else 0)
  else (if U z c then 0 else aHb d r z c)
private abbrev ax0 (d h r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)] (row:Bool) :=
  Σ z :Fin h,Σ c:Fin (z.val/2+1),Fin (a3V d h r U z c row)
private theorem cIc (d:ℕ) {e m:Fin 4 →₀ ℕ}
    (he :e.degree=d) (hm:m.degree=d)
    (h₀:e 0=m 0) (hc:e 3=m 3) (hz :order e=order m) :e=m:= by
  rw [cF] at he hm
  unfold order at hz
  ext i
  have h₂:e 2=m 2 := by omega
  have h₁:e 1=m 1 := by omega
  fin_cases i <;> assumption
private theorem c9a (q r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)]
    [DecidablePred (ajZ q r U)] :
    zhP {e // ajZ q r U e} ≤
      zhP (ax0 (iO q) (DV q r) r U true) := by
  let encode (e : {e // ajZ q r U e}) :
      ax0 (iO q) (DV q r) r U true :=
    ⟨⟨order e.val.val,by
        have hw:=e.val.property.2
        rw [oG] at hw
        have hw' := hw.trans_le (aq6 q r).le
        unfold order
        omega⟩,
      ⟨e.val.val 3,by
        change e.val.val 3<order e.val.val/2+1
        unfold order
        omega⟩,
      ⟨e.val.val 0,by
        obtain ⟨hd,hw⟩:=e.val.property
        rw [cF] at hd
        rw [oG] at hw
        have hw' := hw.trans_le (aq6 q r).le
        obtain ⟨hreach,habove⟩:=e.property
        change e.val.val 0<a3V _ _ _ _ (order e.val.val) (e.val.val 3) true
        simp only [a3V,ite_true,ite_eq_left habove,aEG,lt_min_iff]
        unfold order at *
        omega⟩⟩
  refine zWJ encode (fun e m h => ?_)
  have hz :=congrArg (fun p:ax0 _ _ _ _ true=>p.1.val) h
  have hc:=congrArg (fun p:ax0 _ _ _ _ true=>p.2.1.val) h
  have ha :=congrArg (fun p:ax0 _ _ _ _ true=>p.2.2.val) h
  exact Subtype.ext (Subtype.ext (cIc _ e.val.property.1 m.val.property.1 ha hc hz))
private theorem cGO (q r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)]
    [DecidablePred (ajY q r U)] :
    zhP {m // ajY q r U m} ≤
      zhP (ax0 (iO q) (DV q r) r U false) := by
  have low (m:XN q (offset r)) :
      a2K (iO q) (order m.val)≤ m.val 0:= by
    obtain ⟨hd,_,hi,_⟩:=m.property
    rw [cF] at hd
    rw [xH] at hi
    unfold a2K order
    omega
  let encode (m : {m // ajY q r U m}) :
      ax0 (iO q) (DV q r) r U false :=
    ⟨⟨order m.val.val,m.property.1⟩,
      ⟨m.val.val 3,by
        change m.val.val 3<order m.val.val/2+1
        unfold order
        omega⟩,
      ⟨m.val.val 0-a2K (iO q) (order m.val.val),by
        obtain ⟨hd,hlo,_,hcap⟩:=m.val.property
        rw [cF] at hd
        rw [xH] at hlo
        unfold offset at hlo
        have habove :=m.property.2
        have hlow:=low m.val
        change _<a3V _ _ _ _ (order m.val.val) (m.val.val 3) false
        simp only [a3V,Bool.false_eq_true,ite_false,ite_eq_right habove,aHb,
          ite_eq_left hcap]
        unfold a2K order at *
        omega⟩⟩
  refine zWJ encode (fun e m h => ?_)
  have hz :order e.val.val=order m.val.val :=
    congrArg (fun p:ax0 _ _ _ _ false=>p.1.val) h
  have hc:=congrArg (fun p:ax0 _ _ _ _ false=>p.2.1.val) h
  have ha :e.val.val 0-a2K (iO q) (order e.val.val) =
      m.val.val 0-a2K (iO q) (order m.val.val) :=
    congrArg (fun p:ax0 _ _ _ _ false=>p.2.2.val) h
  rw [hz] at ha
  have he :=low e.val
  have hm:=low m.val
  rw [hz] at he
  exact Subtype.ext (Subtype.ext
    (cIc _ e.val.property.1 m.val.property.1 (by omega) hc hz))
def aht (d h r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)] :ℕ :=
  qI h fun z=>qI (z/2+1) fun c =>
    if U z c then aEG d h r z c else aHb d r z c
theorem aHj (q r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)]
    [DecidablePred (ajZ q r U)] [DecidablePred (ajY q r U)] :
    zhP {e // ajZ q r U e} +
      zhP {m // ajY q r U m} ≤
        aht (iO q) (DV q r) r U:= by
  refine (Nat.add_le_add (c9a q r U) (cGO q r U)).trans_eq ?_
  simp only [ax0,Fintype.card_sigma,Fintype.card_fin,aht,Qg]
  rw [← zfW]
  refine zUo rfl fun z _ => ?_
  rw [← zfW]
  exact zUo rfl fun c _=> by
    by_cases h:U z c <;> simp [a3V,h]
theorem rank_eq_zero (q r :ℕ) (hr :155≤q+r) :
    (Gy q (offset r)).rank=0:= by
  have he : ∀ e :ait q (offset r),False := by
    intro e
    have hc:DV q r=0:=Nat.sub_eq_zero_of_le hr
    exact Nat.not_lt_zero _ (e.property.2.trans_le ((aq6 q r).trans hc).le)
  have hz :Gy q (offset r)=0:= by
    ext e
    exact (he e).elim
  rw [hz,Matrix.rank_zero]
theorem ces (q r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)]
    (hU:bAQ U) :
    (Gy q (offset r)).rank≤aht (iO q) (DV q r) r U:= by
  classical
  exact (ao5 _ _ _ (aEb q r U hU)).trans (aHj q r U)
theorem fTl (q r :ℕ) (hq:q≤99+iO q)
    (hr :q+r≤155) :
    KC q r (cqd (99+iO q - q) (DV q r)) := by
  refine (ces q r _ (cAy 0 0 0 0)).trans ?_
  have ht (z :ℕ) :iO q+z+r+1 - 56 =
      99+iO q - q+z+1 - DV q r := by
    unfold DV
    omega
  simp only [aht,above,Nat.zero_le,true_or,and_self,ite_true,
    cqd,Qg]
  refine zQk fun z _ => ?_
  calc
    _ ≤ ∑ _c:Fin (z.val/2+1),
        min ((DV q r+2 - z.val)/3)
          (99+iO q - q+z.val+1 - DV q r) := by
      refine zQk fun c _ => ?_
      unfold aEG
      apply (min_le_right _ _).trans
      apply min_le_min_left
      rw [← ht]
      exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _
    _ = _:= by simp
private theorem tail_add (b h k n m:ℕ) :
    aFb b h k (n+m)=aFb b h k n+aFb b h (k+n) m:= by
  simp only [aFb,aAs,zGH,Nat.add_assoc]
theorem eiN (q d s₀ s₁ s₂:ℕ) (zo:List ℕ)
    (hd:iO q=d) (hq:q≤99+d) (hlen:zo.length+20≤155 - q)
    (h₀:aFb (99+d - q) (155 - q) zo.length 10=s₀)
    (h₁:aFb (99+d - q) (155 - q) (zo.length+10) 10=s₁)
    (h₂:aFb (99+d - q) (155 - q) (zo.length+20)
      (155 - q-(zo.length+20))=s₂)
    (hbudget:zo.sum+(s₀+s₁+s₂)≤Ni q)
    (hearly : ∀ r,r<zo.length→KC q r zo[r]!) :
    Oi q≤Ni q:= by
  let h:=155 - q
  let b:=99+d - q
  let k :=zo.length
  let f (r :ℕ) :=(Gy q (offset r)).rank
  have hsplit :k+(h - k)=h:= by dsimp [h,k]; omega
  have htail:aFb b h k (h - k)=s₀+s₁+s₂:= by
    have hlen' : h - k=10+10+(h-(k+20)) := by dsimp [h,k]; omega
    rw [hlen',tail_add b h k (10+10),tail_add b h k 10]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) h₀ h₁) h₂
  have hfirst: (∑ r∈z4x k,f r)≤zo.sum:= by
    calc
      _ ≤ ∑ r∈z4x k,zo[r]! :=
        zQk fun r hr=>hearly r (Finset.mem_range.mp hr)
      _=zo.sum:= by
        rw [← zdx (fun r :ℕ=>zo[r]!),← Fin.sum_univ_getElem zo]
        exact zUo rfl fun r _=> by rw [getElem!_pos]
  have hlast : (∑ i∈z4x (h - k),f (k+i))≤aFb b h k (h - k) := by
    unfold aFb
    rw [aAs]
    refine zQk fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hrank :=fTl q (k+i) (hd.symm ▸ hq) (by dsimp [h] at hi'; omega)
    simpa only [KC,f,b,hd,h,DV,Nat.sub_sub] using hrank
  calc
    Oi q = ∑ r∈z4x h,f r := by
      unfold Oi
      rw [zdx (fun r=>f r)]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _)) ?_
      intro r _ hr
      have hr' : ¬ r<155 - q:= fun hlt=>hr (Finset.mem_range.mpr hlt)
      exact rank_eq_zero q r (by omega)
    _=(∑ r∈z4x k,f r) + ∑ i∈z4x (h - k),f (k+i) := by
      rw [← zGH,hsplit]
    _≤zo.sum+aFb b h k (h - k) :=Nat.add_le_add hfirst hlast
    _≤Ni q:=htail.symm ▸ hbudget
end qaTCFjd
end
section
set_option autoImplicit true
namespace qnDrZ2b
noncomputable section
open Polynomial P6_6 P6_6_7 q90NBie Finset

open P6_6_7_3 (GW cDD)
open aR (af Shape shape aO cK extend Dd)
open dN (bC Ch An separant)
open BO (Ue)
open aKp (bDo)
open wH (qg)
open lB (bF yy Tn a3t abr)
open private prod_shape literal_fits from ProximityPrize.SubmissionLower.ZIBb1mb
open private bYX bYY cFk from ProximityPrize.SubmissionLower.B5
open scoped BigOperators
private theorem allowed {C:Context} {R ell cs} (h:CaseGuard C R ell cs) :
    chartIndices C cs⊆C.S:= by
  cases cs with
  | union l=>exact Subset.rfl
  | own i =>
    intro k hk
    exact (mem_singleton.mp hk).symm ▸ h.1
private theorem product_box {C:Context} {R ell cs} (h:CaseGuard C R ell cs) :
    aO (shape (GW C cs)) (chartBody C R cs) := by
  cases cs with
  | union l =>
    change aO (shape (factorProd C.f C.S)) (remainingChart C.v)
    apply literal_fits
    rw [prod_shape C.f C.S (fun i hi=>(C.marks.factors i hi).1.ne_zero)]
    obtain ⟨hb,hj,ht⟩:=C.fits
    exact ⟨Nat.le_sub_of_add_le' hb,Nat.le_sub_of_add_le' hj,Nat.le_sub_of_add_le' ht⟩
  | own i =>
    change aO (shape (∏ k∈({i} : Finset _),C.f k)) (shape R).iU
    rw [Finset.prod_singleton]
    have hn:R≠0:= fun hz =>
      (C.marks.factors i h.1).1.ne_zero (zero_dvd_iff.mp (hz ▸ h.2.1.dvd))
    exact cDD (anm.bNR hn h.2.1.dvd') (akM.a1n R)
private theorem body_chamber (C:Context) (R:af 4) (cs :ChartCase C.n) :
    bF (chartBody C R cs) := by
  cases cs with
  | own i=>exact Tn R
  | union l =>
    let j:=min (m6.j - C.v.j) (3*(m6.b - C.v.b))
    change j≤ max (m6.b - C.v.b) j ∧
      3*min (m6.t - C.v.t) (min (m6.b - C.v.b) (j/3))≤j
    exact ⟨le_max_right _ _,(zBI 3
      ((min_le_right _ _).trans (min_le_right _ _))).trans (Nat.mul_div_le _ _)⟩
private theorem weighted_simplex (p:Shape) (m:ℕ) (hm:4≤ m) :
    aO ⟨1,3,1⟩ (weightedChart m p) := by
  rw [weightedChart]
  split
  · let j:=3+(m-4)*(p.j - 2)
    have hj:3≤j:=Nat.le_add_right _ _
    change 1≤ max (1+(m-4)*(p.b - 1)) j∧3≤j∧1≤ min (m-3) (j/3)
    exact ⟨(by omega :1≤j).trans (le_max_right _ _),hj,le_min (by omega) (by omega)⟩
  · exact cFk m p
private theorem sum_budget {n a b u v :ℕ}
    (hs :n≤a+b) (ha :46402*a≤82317*(u/6)+46402)
    (hb:6*b≤v) (hv :6≤v) :
    6*46402*n≤82317*u+2*46402*v := by
  have :=Nat.div_mul_le_self u 6
  omega
theorem proof :q90NBie.c2 := by
  classical
  intro C R ell cs h D hc L hL hmarks
  intro p
  by_cases hne :L.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,card_empty,mul_zero]
    exact Nat.zero_le _
  let P:=GW C cs
  have hP:aO (shape P) p:=product_box h
  have hf (i) (hi:i∈chartIndices C cs) :=C.marks.factors i (allowed h hi)
  have hrow (i) (hi:i∈chartIndices C cs) :aO (shape (C.f i)) p :=
    cDD (anm.bNR
      (Finset.prod_ne_zero_iff.mpr (fun j hj=>(hf j hj).1.ne_zero))
      (Finset.dvd_prod_of_mem C.f hi)) hP
  obtain ⟨γ,hγ⟩:=hne
  have hindex : (chartIndices C cs).Nonempty := by
    cases cs with
    | union l =>
      obtain ⟨i,hi,_⟩:=C.marks.Eh γ (hL hγ)
      exact ⟨i,hi⟩
    | own i=>exact ⟨i,mem_singleton_self i⟩
  have ht:0<p.t:= by
    obtain ⟨i,hi⟩:=hindex
    exact (hf i hi).2.1.trans_le (hrow i hi).2.2
  have hp:bF p:=body_chamber C R cs
  have hunit :aO ⟨1,3,1⟩ p:= by
    have hj:3≤p.j:=(zBI 3 ht).trans hp.2
    exact ⟨(by omega :1≤p.j).trans hp.1,hj,ht⟩
  by_cases hmem:bC P∈D
  swap
  · have hcount:=bYX hc hunit (abr hP) hmem C.messages.distinct hL
        (fun η hη=>⟨hmarks η hη,?_⟩)
    · calc
        _=mV*(6*L.card) := by ac_rfl
        _≤ mV*sectionCost p D:=zBI _ hcount
        _≤_:= by
          rw [show 2*mV*sectionCost p D =
            mV*sectionCost p D + mV*sectionCost p D by ring]
          omega
    · suffices bC P∈Ch (extend (C.s η)) from this
      cases cs with
      | union l =>
        obtain ⟨i,hi,hz⟩:=C.marks.Eh η (hL hη)
        apply Ue.mpr
        change (MvPolynomial.eval _) (factorProd C.f C.S)=0
        rw [factorProd,map_prod]
        exact Finset.prod_eq_zero hi hz
      | own i =>
        change bC (∏ k∈({i} : Finset _),C.f k)∈_
        rw [Finset.prod_singleton]
        exact (hmarks η hη) (D.mem_of_dvd (map_dvd (MvPolynomial.map dN.j8) h.2.1.dvd) hc.contains)
  have hprod : ∏ i∈chartIndices C cs,bC (C.f i)∈D:= by
    simpa only [P,GW,factorProd,bC,map_prod] using hmem
  let:D.IsPrime :=hc.prime
  obtain ⟨i,hi,hfi⟩:=Ideal.IsPrime.prod_mem_iff.mp hprod
  let f :=C.f i
  have hsmall:=hf i hi
  have htop: (shape f).t<K1.p:=hsmall.2.2.1.2.2.trans_lt (by decide :16<K1.p)
  have hon :Dd f (extend (C.s γ)) :=
    ⟨Ue.mp (hmarks γ hγ hfi),C.marks.leading γ (hL hγ) i (allowed h hi)⟩
  obtain ⟨r,hr,_⟩:=bAm.bmF htop hon hfi (hmarks γ hγ)
  let g:=(separant^[r]) f
  have hfit :aO (shape g) p:=cDD (a3t f r) (hrow i hi)
  have hsep:bC (separant g)∉D:=hr.2.2
  have hgt:0<(shape g).t:= by
    by_contra! hz
    apply hsep
    rw [show separant g=0 from MvPolynomial.pderiv_eq_zero_of_notMem_vars (by
      exact fun hv=>(MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv) (by
        change g.degreeOf 3≤0 at hz
        omega))]
    simpa only [bC,map_zero] using D.zero_mem
  have hsfit :yy (bC (separant g)) p:= by
    apply abr
    rw [← Function.iterate_succ_apply' separant r f]
    exact cDD (a3t f (r+1)) (hrow i hi)
  let A:=L.filter fun η=>qg g (extend (C.s η))
  let B:=L.filter fun η => ¬ qg g (extend (C.s η))
  have hA:A⊆C.Δ:=(zT0 _ _).trans hL
  have hsplit :L.card≤A.card+B.card:= by
    rw [Finset.card_filter_add_card_filter_not]
  have hb:=bYX (L:=B) hc hunit hsfit hsep C.messages.distinct ((zT0 _ _).trans hL)
      (fun η hη=>⟨hmarks η (Finset.mem_filter.mp hη).1,
        Ue.mpr (not_ne_iff.mp (Finset.mem_filter.mp hη).2)⟩)
  have hv :6≤ sectionCost p D:= by
    obtain ⟨x,Q,hx,hQ,hproper,hvan⟩:=bDo hc.prime hc.dim
    have hfitQ:yy Q p :=
      ⟨hQ.1.trans hunit.1,hQ.2.1.trans hunit.2.1,hQ.2.2.trans hunit.2.2⟩
    simpa using bYY D p hc.prime hc.dim hunit Q hfitQ hproper {x}
      (by intro y hy; rw [Finset.mem_singleton.mp hy]; exact ⟨hx,hvan⟩)
  have htaylor :bf≤K1.p:= by decide
  have hsimplex :=weighted_simplex p bf (by decide)
  let u:=sectionCost (weightedChart bf p) D
  have ha :=P6_6_5.bv5 (C.messages.mono hA) (u/6) (by
    intro j hmiss
    obtain ⟨Q,hQ,he⟩:=d40 (by decide) htaylor hfit hp ht hgt (P6.node j) (C.w j)
    have on {η} (hη:η∈A) :
        An (extend (C.s η)) Q=0↔(C.s η).eval (P6.node j)=C.w j:= by
      obtain ⟨hηL,hreg⟩:=Finset.mem_filter.mp hη
      have hg:cK g (extend (C.s η))=0 :=
        Ue.mp (hmarks η hηL (hr.2.1 r le_rfl))
      exact he _ (Nat.lt_succ_of_le (C.messages.degree η (hL hηL))) hg hreg
    obtain ⟨η,hη,hw⟩:=hmiss
    have hproper :Q∉D :=
      fun hm=>hw ((on hη).mp (hmarks η ((zT0 _ _) hη) hm))
    apply (Nat.le_div_iff_mul_le (by decide :0<6)).mpr
    rw [Nat.mul_comm]
    exact bYX hc hsimplex hQ hproper C.messages.distinct
      ((zT0 _ _).trans hA) fun ξ hξ=> by
        obtain ⟨hξA,hval⟩:=Finset.mem_filter.mp hξ
        exact ⟨hmarks ξ ((zT0 _ _) hξA),(on hξA).mpr hval⟩)
  exact sum_budget hsplit ha (show 6*B.card≤ sectionCost p D from hb) hv
end
end qnDrZ2b
end
