import ProximityPrize.SubmissionLower.ZrIiE0d
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZdZNCPb
import ProximityPrize.SubmissionLower.A
import ProximityPrize.SubmissionLower.ZedfuCc
import ProximityPrize.SubmissionLower.BA
import ProximityPrize.SubmissionLower.ZV6zyia
set_option Elab.async false
section
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace czW
noncomputable section
open Polynomial Matrix
open cu (Shape)
open Ge anc aeL
open agU (Bb Xq)
open scoped BigOperators Matrix Polynomial
open private bXV from ProximityPrize.SubmissionLower.Z
private abbrev aRN (s :Shape) (t:Offset s) (q:jJ s) :=
 Fin (Bb s.B s.J t.val q.val)
private theorem crG {A D M:Type} [Fintype A] [Fintype D] [AddCommMonoid M]
  (e :A ↪ D) (f :D→M) (h : ∀ d,(∀ a,e a≠d)→f d=0) :
  ∑ d,f d = ∑ a,f (e a) := by
 classical
 rw [← Finset.sum_map Finset.univ e]
 symm
 apply Finset.sum_subset (Finset.subset_univ _)
 intro d _ hd
 exact h d fun a ha=>hd (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,ha⟩)
private theorem cGY (s :Shape) (t:Offset s) (q:jJ s) (j:ℕ)
  (hj:j≤ min q.val s.J) (hfirst:Gv s t≤j)
  (hx :t.val+j - s.J<s.B+s.J) :
  j-Gv s t<Bb s.B s.J t.val q.val := by
 have ht:=t.isLt
 have hhigh:j≤ s.B+2*s.J - 1 - t.val := by omega
 have hmin:=le_min (hj.trans (min_le_left _ _))
  (le_min (hj.trans (min_le_right _ _)) hhigh)
 change j-Gv s t< min q.val (min s.J (s.B+2*s.J - 1 - t.val))+1 -
  Gv s t
 omega
private theorem dND (s :Shape) (t:Offset s) {q q' : jJ s}
  (h:q.val≤q'.val) :
  Bb s.B s.J t.val q.val≤Bb s.B s.J t.val q'.val := by
 unfold Bb
 exact Nat.sub_le_sub_right (Nat.add_le_add_right (min_le_min_right _ h) 1) _
private def cT0 (s :Shape) (q:jJ s) :Shift s q ↪ jJ s where
 toFun p:=⟨q.val+p.val,by
  have hq:=q.isLt
  have hp:=p.isLt
  omega⟩
 inj' _ _ h:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def deF (s :Shape) (t:Offset s) (q:jJ s) :
  aRN s t q ↪ NQ s q.val where
 toFun a :=⟨Gv s t+a.val,
  Nat.lt_succ_of_le (beO s t q a.val a.isLt).1⟩
 inj' _ _ h:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def a9g {F:Type} [Field F] {s :Shape}
   (α:F) (z :kq F) (P:Gm F) (q:jJ s) (j x :ℕ) :kq F :=
 ∑ p:Shift s q,
   (((q.val - j+p.val).choose (q.val - j) :kq F)*z^p.val) *
     algebraMap (i5 F) (kq F) (b6l α j (q.val - j+p.val) x P)
private theorem exF {F:Type} [Field F] (s :Shape)
  (α:F) (z :kq F) (P:Gm F) (q:jJ s) (j:NQ s q.val)
  (x :ℕ) :
  (aVG s α z P q j).coeff x=a9g α z P q j.val x := by
 simp only [aVG,finsetSum_coeff,coeff_C_mul,coeff_map,bHT,
  a9g,efk]
private theorem eLu {F:Type} [Field F] (s :Shape) (t:Offset s)
    (α:F) (z :kq F) (P:Gm F) (q:jJ s)
    (i:Fin (Xq s.B s.J t.val q.val)) :
    (Pa s t z *ᵥ
        (fun u=>algebraMap (i5 F) (kq F) (input α u P))) ⟨q,i⟩ =
      ∑ a :aRN s t q,((Gv s t+a.val).choose i.val :kq F) *
        a9g α z P q (Gv s t+a.val)
          (t.val+(Gv s t+a.val) - s.J) := by
  classical
  rw [Matrix.mulVec,dotProduct,Fintype.sum_sigma]
  let f (q' : jJ s) (a :aRN s t q') :=
    Pa s t z ⟨q,i⟩ ⟨q',a⟩ *
      algebraMap (i5 F) (kq F) (input α ⟨q',a⟩ P)
  change (∑ q',∑ a,f q' a)= _
  rw [crG (cT0 s q) (fun q' => ∑ a,f q' a)]
  · simp only [a9g,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    let q' := cT0 s q p
    have hqq:q.val≤q'.val :=Nat.le_add_right _ _
    let e :aRN s t q ↪ aRN s t q' :=
      Fin.castLEEmb (dND s t hqq)
    change (∑ a,f q' a)= _
    rw [crG e (f q')]
    · apply Finset.sum_congr rfl
      intro a _
      let j:=Gv s t+a.val
      have hj:j≤q.val :=(beO s t q a.val a.isLt).1.trans (min_le_left _ _)
      have hp:q'.val - q.val=p.val := by
        change q.val+p.val - q.val=p.val
        omega
      have hOrd:q'.val - j=q.val - j+p.val := by
        change q.val+p.val - j=q.val - j+p.val
        omega
      change (if q.val≤q'.val∧j≤q.val then
        ((j.choose i.val :kq F)*((q'.val - j).choose (q.val - j) :kq F)) *
          z^(q'.val - q.val) else 0) *
          algebraMap (i5 F) (kq F)
            (b6l α j (q'.val - j) (t.val+j - s.J) P)= _
      rw [ite_eq_left ⟨hqq,hj⟩,hp,hOrd]
      simp only [j,mul_assoc]
    · intro a ha
      have hj : ¬ Gv s t+a.val≤q.val := by
        intro hj
        have hb:=beO s t q' a.val a.isLt
        have hi:=cGY s t q (Gv s t+a.val)
          (le_min hj (hb.1.trans (min_le_right _ _))) (Nat.le_add_right _ _) hb.2
        have ha' : a.val<Bb s.B s.J t.val q.val := by omega
        exact ha ⟨a.val,ha'⟩ (Fin.ext rfl)
      simp [f,Pa,a2N,hj]
  · intro q' h
    have hl : ¬ q.val≤q'.val := by
      intro hqq
      have hq' := q'.isLt
      let p:Shift s q:=⟨q'.val - q.val,by omega⟩
      exact h p (Fin.ext (by change q.val+(q'.val - q.val)=q'.val; omega))
    apply Finset.sum_eq_zero
    intro a _
    have hz :Pa s t z ⟨q,i⟩ ⟨q',a⟩=0:= by
      unfold Pa
      exact ite_eq_right (fun h=>hl h.1)
    simp only [f,hz,zero_mul]
private theorem dMw {F:Type} [Field F] (s :Shape) (t:Offset s)
    (α:F) (z :kq F) (P:Gm F) (q:jJ s)
    (k :NQ s q.val) (l:ℕ) (hl:l<s.B+s.J)
    (ht:t.val+q.val+k.val=l+s.J) :
    (aRi s q.val (aVG s α z P q) k).coeff l =
      ∑ a :aRN s t q,((Gv s t+a.val).choose k.val :kq F) *
        a9g α z P q (Gv s t+a.val)
          (t.val+(Gv s t+a.val) - s.J) := by
  classical
  rw [bXV,crG (deF s t q)]
  · apply Finset.sum_congr rfl
    intro a _
    let j:=Gv s t+a.val
    have hj:=(beO s t q a.val a.isLt).1.trans (min_le_left _ _)
    have hshift:q.val - j+k.val≤l:= by
      have hfirst:s.J≤t.val+j:= by
        dsimp [j,Gv]
        omega
      omega
    have hx :l-(q.val - j+k.val)=t.val+j - s.J:= by omega
    change (if k.val≤j∧q.val - j+k.val≤l then
      (j.choose k.val :kq F)*(aVG s α z P q (deF s t q a)).coeff
        (l-(q.val - j+k.val)) else 0)= _
    by_cases hk :k.val≤j
    · rw [ite_eq_left ⟨hk,hshift⟩,hx,exF]
      rfl
    · change _=(j.choose k.val :kq F) *
        a9g α z P q j (t.val+j - s.J)
      rw [ite_eq_right (fun h=>hk h.1),Nat.choose_eq_zero_of_lt (lt_of_not_ge hk),
        Nat.cast_zero,zero_mul]
  · intro j hj
    split_ifs with h
    · exfalso
      have hjmin:j.val≤ min q.val s.J:=Nat.lt_succ_iff.mp j.isLt
      have hjq:=hjmin.trans (min_le_left _ _)
      have hshift:=h.2
      have hfirst:Gv s t≤j.val := by unfold Gv; omega
      have hx :t.val+j.val - s.J<s.B+s.J:= by omega
      let a :aRN s t q:=⟨j.val-Gv s t,cGY s t q j.val hjmin hfirst hx⟩
      apply hj a
      apply Fin.ext
      change Gv s t+(j.val-Gv s t)=j.val
      omega
    · rfl
private theorem eKN {E :Type} [Field E] {a n h:ℕ}
  (hs :bTl E a n h) (v :Fin n→E)
  (hv : ∀ r,(∑ j,btx a n h r j*v j)=0) (k :ℕ) (hk :k<h) :
  (∑ j:Fin n,((a+j.val).choose k :E)*v j)=0:= by
 obtain ⟨w,hw⟩:=hs k hk
 simp only [hw,Finset.sum_mul,mul_assoc]
 rw [Finset.sum_comm]
 simp only [← Finset.mul_sum,hv,mul_zero,Finset.sum_const_zero]
theorem proof :aeL.c1 := by
 intro F _ s α z hs P _ hm q k
 apply Polynomial.X_pow_dvd_iff.mpr
 intro l hl
 by_cases ht:q.val+k.val≤l+s.J
 · let t:Offset s :=⟨l+s.J-(q.val+k.val),by omega⟩
   have ht' : t.val+q.val+k.val=l+s.J:= by dsimp [t]; omega
   have hk :k.val<aIN s t q:= by unfold aIN; omega
   rw [dMw s t α z P q k l hl ht']
   let v (j:aRN s t q) :=
    a9g α z P q (Gv s t+j.val) (t.val+(Gv s t+j.val) - s.J)
   apply eKN (hs t q) v _ k.val hk
   intro r
   have hr :=congrFun (hm t) (⟨q,r⟩:Pivot s t)
   rw [eLu] at hr
   exact hr
 · rw [bXV]
   apply Finset.sum_eq_zero
   intro j _
   have hj:j.val≤ min q.val s.J:=Nat.lt_succ_iff.mp j.isLt
   have hjq:=hj.trans (min_le_left _ _)
   have hjJ:=hj.trans (min_le_right _ _)
   have hn : ¬ q.val - j.val+k.val≤l:= by omega
   simp [hn]
end
end czW
end
section
namespace aSk
open scoped BigOperators
theorem proof :aeL.c2 := by
 intro F ι κ _ _ _ _ M D hM
 obtain ⟨Q,T,L,d,hQT,hL,hdeg,hlead⟩ :=
  d4I M (d4U M hM.1)
 obtain ⟨e,he,hd⟩:=d4s Q d hdeg hlead
 exact ⟨Q,L,d,hL,hdeg,hd.trans (aVV M D Q T L hQT hL hM e he)⟩
end aSk
end
end
section
set_option autoImplicit true
namespace qN0s3Ta
noncomputable section
open aR (ao)
open fP (lP qI aAs)
open P6_6_1 (Exponent FF space asu gAu)
open PolynomialDifferential (differentialWeight)
open scoped BigOperators
private def exponent (x v a b c:ℕ) :Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v,a,b,c]).optionElim x
@[simp] private theorem exponent_none (x v a b c:ℕ) :exponent x v a b c none=x := by
  simp [exponent]
@[simp] private theorem cNN (x v a b c:ℕ) (i:Fin 4) :
    exponent x v a b c (some i) = ![v,a,b,c] i:= by simp [exponent]
private theorem b6S (m:Fin 4 →₀ ℕ) (w:Fin 4→ℕ) :
    m.weight w=m 0*w 0+m 1*w 1+m 2*w 2+m 3*w 3:= by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul,add_assoc]
private def aMH (r :ℕ) :ℕ :=
  if r≤33 then 133 else if r≤35 then 131 else
  if r≤38 then 129 else 111+2*((56 - r)/2)
private theorem ceiling_bounds (r :ℕ) (hr :r≤56) :
    aMH r≤133∧r≤asu (aMH r) := by
  simp only [aMH,asu]
  split_ifs <;> omega
private def gw (r :ℕ) :ℕ:=aMH r+1 - r
private def topCount (r :ℕ) :ℕ:=min (min 16 r) ((56 - r)/2)+1
private def secondCount (r c:ℕ) :ℕ:=min (r - c) (56 - r - 2*c)+1
private def base (r :ℕ) :ℕ:=99*179827 - 133425*aMH r
private def width (r j:ℕ) :ℕ:=base r+133425*j
private abbrev Slot:=Σ r :Fin 57,Σ c:Fin (topCount r),Σ _:Fin (secondCount r c),
  Σ j:Fin (gw r),Fin (width r j)
private abbrev Symbol := {u:Exponent // FF u}
private theorem derivative_bounds (r c b:ℕ) (hr :r<57)
    (hc:c<topCount r) (hb:b<secondCount r c) :
    c≤16∧b+c≤ r∧r+b+2*c≤56:= by
  unfold topCount at hc
  unfold secondCount at hb
  omega
private theorem jet_coordinates (x v a b c:ℕ) :
    (exponent x v a b c).some.degree=v+a+b+c ∧
    (exponent x v a b c).some.weight lP=a+2*b+3*c:= by
  rw [Finsupp.degree_eq_weight_one,b6S,b6S]
  simp [lP,Finsupp.some_apply,Nat.mul_comm]
private theorem gEz (x v a b c:ℕ) :
    (exponent x v a b c).weight (differentialWeight P6_6.gZ) ≤
      x+133425*(v+a+b+c) := by
  have hw:differentialWeight (d:=3) P6_6.gZ=fun i =>
      i.elim 1 (fun k=>133425 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw,exponent,Finsupp.weight_optionElim,b6S]
  simp
  omega
private def aei (q:Slot) :Symbol:= by
  rcases q with ⟨r,c,b,j,x⟩
  let a :=r.val-(b.val+c.val)
  let v :=aMH r - j.val - r.val
  refine ⟨exponent x v a b c,?_⟩
  obtain ⟨hc,hbc,hi⟩:=derivative_bounds r c b r.isLt c.isLt b.isLt
  obtain ⟨hceil,hcap⟩:=ceiling_bounds r (Nat.le_of_lt_succ r.isLt)
  have hj:=j.isLt
  have hx :=x.isLt
  have hr :a+b.val+c.val=r.val := by dsimp [a]; omega
  unfold gw at hj
  have hg:v+a+b.val+c.val=aMH r - j.val := by
    dsimp [v]
    omega
  obtain ⟨hd,hind⟩:=jet_coordinates x v a b c
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hd,hg]
    exact (Nat.sub_le _ _).trans hceil
  · rw [hind]
    change _≤56
    omega
  · simpa [cNN] using hc
  · rw [hd,hg]
    simp only [cNN]
    change a+b.val+c.val≤asu (aMH r - j.val)
    rw [hr]
    exact hcap.trans (gAu (Nat.sub_le _ _))
  · apply (gEz x v a b c).trans
    rw [hg]
    change _≤99*179827 - 1
    unfold width base at hx
    omega
private theorem deG:Function.Injective aei:= by
  rintro ⟨⟨r,hr⟩,⟨c,hc⟩,⟨b,hb⟩,⟨j,hj⟩,⟨x,hx⟩⟩
    ⟨⟨r',hr'⟩,⟨c',hc'⟩,⟨b',hb'⟩,⟨j',hj'⟩,⟨x',hx'⟩⟩ h
  have hbc:=(derivative_bounds r c b hr hc hb).2.1
  have hbc' := (derivative_bounds r' c' b' hr' hc' hb').2.1
  have ec:c=c' := by simpa [aei] using congrArg (fun u:Symbol=>u.val (some 3)) h
  have eb:b=b' := by simpa [aei] using congrArg (fun u:Symbol=>u.val (some 2)) h
  have ea :r-(b+c)=r' - (b' + c') := by
    simpa [aei] using congrArg (fun u:Symbol=>u.val (some 1)) h
  have er :r=r' := by omega
  have ex :x=x' := by simpa [aei] using congrArg (fun u:Symbol=>u.val none) h
  subst r'; subst b'; subst c'; subst x'
  have ev :aMH r - j - r=aMH r - j' - r := by
    simpa [aei] using congrArg (fun u:Symbol=>u.val (some 0)) h
  change j<gw r at hj
  change j' < gw r at hj'
  unfold gw at hj hj'
  have ej:j=j' := by omega
  subst j'
  rfl
private def aH3 (r :ℕ) :ℕ :=
  let n:=gw r
  n*base r+133425*(n*(n - 1)/2)
private theorem sum_width (r :ℕ) : (∑ j:Fin (gw r),width r j)=aH3 r := by
  rw [Fin.sum_univ_eq_sum_range (width r)]
  simp [width,aH3,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_range_id]
private theorem Qg (n:ℕ) (f :ℕ→ℕ) :qI n f = ∑ i:Fin n,f i:= by
  rw [Fin.sum_univ_eq_sum_range f,aAs]
private def count (r :ℕ) :ℕ:=qI (topCount r) (secondCount r)*aH3 r
private theorem cp4 :Fintype.card Slot = ∑ r :Fin 57,count r := by
  simp only [Slot,Fintype.card_sigma,Fintype.card_fin,sum_width,count,Qg]
  simp [Finset.sum_mul]
private def r0:List ℕ:=[
  0x475332b7,0xd2caa4ba,0x19f4399c4,0x2a9a78cb6,0x3eeec2f97,
  0x56c136b94,0x71e2b6100,0x9024e6754,0xb15a30d2f,0xd555c1856,
  0xfbeb885b4,0x124f03895a,0x1503948e7f,0x17d9cf3780,0x1acf235de0]
private def r1 :List ℕ:=[
  0x1de10d1248,0x210d149c87,0x241a7074dc,0x270988700a,0x29dac462d4,
  0x2c8e8c21fd,0x2e8d254354,0x2fad327d28,0x2ff9aba4a7,0x2f7d57b267,
  0x2e42ccc266,0x2c82c209ac,0x2a17648667,0x27375c6a35,0x23e9fe8af0]
private def r2 :List ℕ:=[
  0x20e2485430,0x1df345b416,0x1b45f15b1f,0x18af089408,0x1653d00350,
  0x140f1dfa58,0x11fed5b1fb,0x1006ccbc24,0xe45213628,0xc8c74c35c,
  0xb0e61a264,0x99675f9f0,0x856b2cb80,0x71b3049d0,0x6148d09b8]
private def r3:List ℕ:=[
  0x511039cec,0x43e68b548,0x36e4fdd34,0x2cabe266c,0x22974f498,
  0x1b005b560,0x138d2cd08,0xe4b7ba60,0x92c95074,0x5f4c8da8,
  0x2db868cc,0x163c8774]
private def totals :List ℕ:=r0 ++ r1 ++ r2 ++ r3
private theorem count_eq (r :Fin 57) :count r=totals[r.val]! := by fin_cases r <;> decide
private theorem eWA:r0.sum=0xa103c4b9dc:= by decide
private theorem fgW:r1.sum=0x26e2b1477ae := by decide
private theorem fpX:r2.sum=0x1042ff61814 := by decide
private theorem fvo:r3.sum=0x16b58a5590:= by decide
private theorem dhG: (∑ r :Fin 57,count r)=0x42a14599f2e := by
  have hlen:totals.length=57:=rfl
  calc
    _ = ∑ r :Fin 57,totals[r.val]! := Finset.sum_congr rfl fun r _=>count_eq r
    _ = ∑ r :Fin totals.length,totals[r.val]! := by rw [hlen]
    _ = ∑ r :Fin totals.length,totals[r.val] :=
      Finset.sum_congr rfl fun r _=> by rw [getElem!_pos]
    _=totals.sum:=Fin.sum_univ_getElem totals
    _ = _:= by simp only [totals,List.sum_append,eWA,fgW,fpX,fvo]
theorem proof :P6_6_1.c2 := by
  let:Module.Finite ao (MvPolynomial.restrictSupport ao {u:Exponent | FF u}) :=
    inferInstanceAs (Module.Finite ao space)
  let b:=MvPolynomial.basisRestrictSupport ao {u:Exponent | FF u}
  have h:=(b.linearIndependent.comp aei deG).fintype_card_le_finrank
  rw [cp4,dhG] at h
  exact (by decide :0x42a14040000<0x42a14599f2e).trans_le h
end
end qN0s3Ta
end
section
set_option autoImplicit true
namespace qnODzma
noncomputable section
open aR (af shape)
open dN (bC j8 oA kC)
open agL (BV EY bft afc aD7)
open Dr (aIc aIT aQG ccl)
open rW (n8 Yg)
open WI (ctQ agr)
open P6_6_7 (Context PairInput firstSlot cutterBody)
open MvPolynomial
open private cGC from ProximityPrize.SubmissionLower.BA
theorem dlP {R G:af 4} {P:n8} {i ell:ℕ}
    (hR:bC R≠0) (hrel :IsRelPrime (bC R) (bC G))
    (hp: (kC R G).IsMinimalPrime P)
    (hi : ∀ a,EY a< i→bC (BV a R)∈P)
    (hell : ∀ a,EY a<ell→bC (BV a G)∈P) :
    ell*i≤Yg (kC R G) P:= by
  let _:=hp.isPrime
  have hheight:=aD7 hR hrel hp
  have vanish (F:af 4) (d:ℕ)
      (h : ∀ a,EY a<d→bC (BV a F)∈P) :
      afc P (bC F) d:= by
    apply bRn.proof _ P d hheight
    intro a ha
    change BV a (MvPolynomial.map j8 F)∈P
    rw [← bft]
    exact h a ha
  have hle :=OO.bsc hheight (vanish R i hi) (vanish G ell hell)
  have hw: (Yg (kC R G) P:ℕ∞) =
      oA (kC R G) P hp.isPrime := by
    simp only [Yg,dite_eq_left hp.isPrime]
    exact ENat.natCast_toNat (ccl hp).2
  rw [← hw,Nat.mul_comm i ell] at hle
  exact ENat.natCast_le_natCast.mp hle
theorem cycle_budget {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    ∑ P∈(kC R G).minimalPrimesFinset,
      (Yg (kC R G) P:ℚ)*affineDegree P ≤
      ((firstSlot C R cs).b:ℚ)*(cutterBody C ell).b:= by
  classical
  let J:=kC R G
  let F:=Ideal.span {bC R}
  have hR:=agr h.factor.1.ne_zero
  have hrel :=lB.amo R G h.factor.1 h.proper
  have hb:0<(shape R).b:=h.factor.2.1.1
  have hF:F ≠ ⊤ := by
    intro he
    have hdeg:=(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp
      (Ideal.span_singleton_eq_top.mp he)).2
    rw [ctQ] at hdeg
    exact (Nat.ne_of_gt hb) hdeg
  have hdimF:=natDegree_affineHilbertPolynomial_span_singleton_add_one hR hF
  rw [Nat.card_fin] at hdimF
  have hthree : (affineHilbertPolynomial (Ideal.span {bC R})).natDegree=3:= by omega
  have hcoeff :6*(affineHilbertPolynomial F).leadingCoeff=(shape R).b:= by
    have hd:=affineDegree_span_singleton hR
    rw [affineDegree,hthree,ctQ] at hd
    norm_num at hd
    exact hd
  have hc:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (aIT R G hrel) (ctQ G).le
  rw [← aIc,hthree] at hc
  norm_num at hc
  obtain ⟨_,hbudget⟩:=cGC J hc.1
  have hfirst: (shape R).b≤(firstSlot C R cs).b:= by
    cases cs with
    | union _=>exact le_rfl
    | own _=>exact le_max_left _ _
  calc
    _=2 * ∑ P∈J.minimalPrimesFinset,
        (Yg J P:ℚ)*(affineHilbertPolynomial P).coeff 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hd:=aQG hR hrel (Ideal.mem_minimalPrimesFinset.mp hP)
      simp only [affineDegree,Polynomial.leadingCoeff,hd]
      norm_num
      ring
    _≤2*(affineHilbertPolynomial J).coeff 2 :=
      mul_le_mul_of_nonneg_left hbudget (by norm_num)
    _≤((shape R).b:ℚ)*(shape G).b:= by
      change 2*(affineHilbertPolynomial (kC R G)).coeff 2 ≤
        (R.totalDegree :ℚ)*G.totalDegree
      change 6*(affineHilbertPolynomial F).leadingCoeff=(R.totalDegree :ℚ) at hcoeff
      nlinarith only [hc.2,congrArg (fun x :ℚ=>x*G.totalDegree) hcoeff]
    _≤_:=mul_le_mul
      (by exact_mod_cast hfirst) (by exact_mod_cast h.H6.1) (by positivity) (by positivity)
end
end qnODzma
end
