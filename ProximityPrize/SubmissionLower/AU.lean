import ProximityPrize.SubmissionLower.AP
set_option Elab.async false
open _root_ renaming Nat.add_le_add → z9f, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu
set_option autoImplicit true
section
namespace I5
open aR (Shape aO qP iH)
open vS (tC)
open yi (bF tD)
open nZ (On Jg zK Xr Q5
 Xz DC A9 KZ AA adM F4
 ZT)
open Py (LI)
open bJ (bf Rb Ix sL W5 asQ H6)
open bj0 (slope bN4)
open private shift shift_add acJ aET from ProximityPrize.SubmissionLower.CI
private abbrev u:=bf+1
private abbrev v :=bf+2
private theorem cUw {p:Shape} (ht:3≤p.t) (hj:3*p.t+3≤p.j) :
  (3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
    3*(2+(u - 5)*p.t)≤(qP u p).j ∧
    3*(2+(v - 5)*p.t)≤(qP v p).j ∧
    2*u≤(qP u p).t∧2*v≤(qP v p).t) ∧
    2≤(tC p).t:= by
 change (_∧_∧3*(2+133456*p.t)≤4+133456*(p.j - 2) ∧
  3*(2+133457*p.t)≤4+133457*(p.j - 2) ∧
  266922≤ min (2+133456*p.t) ((4+133456*(p.j - 2))/3) ∧
  266924≤ min (2+133457*p.t) ((4+133457*(p.j - 2))/3)) ∧
  2≤ min (p.t+1) ((p.j+1)/3)
 simp only [le_min_iff]
 omega
private theorem a8Y {p p' q q' : Shape} (hp:aO p p') (hq:aO q q')
    (hp' : bF p') (hc:bF q) (hc' : bF q')
    (ht:3≤p.t) (hj:3*p.t+3≤p.j)
    (hj' : 3*p'.t+3≤p'.j) :
    Rb p q≤Rb p' q' := by
  let base (x y :Shape) :=
    iH x y (qP u x) (qP v x) +
      u*iH x y (tC x) (qP v x) +
      v*iH x y (tC x) (qP u x)
  let mR (x y :Shape) :=
    ((base x y :ℤ) -
      ((u:ℤ)*bJ.wP x y slope (qP v x) +
        (v :ℤ)*bJ.wP x y slope (qP u x) +
        (u:ℤ)*(v :ℤ) *
          (bJ.wP x y slope (tC x) - bJ.wP x y slope slope))).toNat
  have corr (x y :Shape) (hy :bF y) (hg:2≤(tC x).t)
      (hb:2*v≤(qP v x).t) :
      mR x y=iH x y (qP u x) (qP v x) +
        u*iH x y (shift 1 (tC x)) (shift v (qP v x)) +
        v*iH x y (shift 1 (tC x)) (qP u x) := by
    have hg' := shift_add (k :=1) (F4 x) (by simpa only [Nat.mul_one] using hg)
    exact bN4 x y _ _ _ _ _ u v
      (by simpa only [Shape.scale,Nat.one_mul] using hg')
      (shift_add (AA _ _) hb) hy (F4 _) (AA _ _)
      (AA _ _) (acJ (F4 _) hg) (acJ (AA _ _) hb)
  obtain ⟨htest,hgt⟩:=cUw ht hj
  obtain ⟨htest',hgt'⟩:=cUw (ht.trans hp.2.2) hj'
  have hbt:=htest.2.2.2.2.2
  have hbt' := htest'.2.2.2.2.2
  have nmono {r r' s s' : Shape} (hr :aO r r') (hs :aO s s')
      (hrc :bF r) (hrc' : bF r') (hsc:bF s) :
      iH p q r s≤ iH p' q' r' s' :=
    tD hp hq hr hs hp' hc' hrc' hc hrc hsc
  have hbase :=nmono (KZ u hp) (KZ v hp)
    (AA _ _) (AA _ _) (AA _ _)
  have hgraph (k :ℕ) :=nmono (adM hp) (KZ k hp)
    (F4 _) (F4 _) (AA _ _)
  have hgm:=aET 1 (adM hp)
  have hgc:=acJ (k :=1) (F4 p) hgt
  have hgc' := acJ (k :=1) (F4 p') hgt'
  unfold Rb
  dsimp only
  rw [ite_eq_left htest,ite_eq_left htest']
  change min _ (min (base p q) (mR p q))≤ min _ (min (base p' q') (mR p' q'))
  rw [corr p q hc hgt hbt,corr p' q' hc' hgt' hbt']
  exact min_le_min (nmono (DC u hp) (DC v hp)
    (A9 _ _) (A9 _ _) (A9 _ _))
    (min_le_min (z9f (z9f hbase (zBI u (hgraph v)))
      (zBI v (hgraph u)))
      (z9f (z9f hbase (zBI u
        (nmono hgm (aET v (KZ v hp)) hgc hgc'
          (acJ (AA _ _) hbt))))
        (zBI v (nmono hgm (KZ u hp) hgc hgc' (AA _ _)))))
theorem RR {x y q z :Shape} (hx :aO x y) (hq:aO q z)
    (hc:bF q) (hz :bF z) (ht:3≤x.t) (hj:3*x.t+3≤x.j)
    (hjy :3*y.t+3≤y.j) (mode :asQ) :
    Ix x q≤Ix y z∧W5 mode x q≤W5 mode y z := by
  let p:=x.iU
  let p' := y.iU
  let L:=bf
  have hp:=On hx
  have hp'c:=Jg y (Nat.le_trans (Nat.le_add_right _ _) hjy)
  have hpc:=Jg x (Nat.le_trans (Nat.le_add_right _ _) hj)
  have hh:=DC L hp
  have hh₀:=A9 L p
  have hh₁:=A9 L p'
  have ha :=zK hq (Q5 hp 4)
  have ha₀:=Xr hc (Xz hpc 4)
  have ha₁:=Xr hz (Xz hp'c 4)
  have hmx :=tD hp hq ha hh hp'c hz ha₁ hc ha₀ hh₀
  have hmp:=tD hp hq ha hp hp'c hz ha₁ hc ha₀ hpc
  have hmx' := tD hp hp hp hh hp'c hp'c hp'c hpc hpc hh₀
  have hmp' := tD hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have hjx :=tD hp hq hp hh hp'c hz hp'c hc hpc hh₀
  have hjp:=tD hp hq hp hp hp'c hz hp'c hc hpc hpc
  have hadd:=zBI 2 hx.2.2
  have hcurve :=z9f hmx (zcp hadd hmx')
  have hpoint :=z9f hmp (zcp hadd hmp')
  constructor
  · unfold Ix
    apply z9f
    · exact LI (a8Y hp hq hp'c hc hz ht hj hjy) _
    · exact LI (zcp
        (zcp (zBI _ hx.1) hq.1) (DC u hp).1) _
  · have haux :sL x q≤ sL y z :=
      z9f (zcp (zBI _ hx.1) hq.1)
        (LI (z9f (zBI _ hcurve)
          (zBI _ hpoint)) _)
    cases mode with
    | iy=>exact haux
    | product =>
      exact z9f haux (LI (z9f
        (zBI _ hjx) (zBI _ hjp)) _)
theorem aM8 (b:bJ.Bank) (x :Shape) (a r :ℕ) :
 bF (H6 b x a r) :=⟨le_max_right _ _,ZT _ _⟩
theorem bZz {x y :Shape} (h:aO x y) (b:bJ.Bank)
  {a a' r :ℕ} (haa :a≤a') :aO (H6 b y a' r) (H6 b x a r) := by
 obtain ⟨hb,hj,ht⟩:=h
 refine ⟨?_,?_,?_⟩ <;> dsimp [H6] <;> gcongr
theorem dTh (b:bJ.Bank) (x y :Shape) {a a' : ℕ} (haa :a≤a') :
  aO (H6 b y a' a') (H6 b x a a) := by
 refine ⟨?_,?_,?_⟩ <;> dsimp [H6] <;> simp only [Nat.sub_self,Nat.zero_mul,Nat.zero_add] <;>
  gcongr
end I5
end
section
namespace I5
open aR (Shape aO)
open bJ (gV asQ H6 Xd Ix W5 YK EW)
open cS (kW bpY)
abbrev lower (t:ℕ) :Shape :=⟨109,48,t⟩
abbrev upper (t:ℕ) :Shape :=⟨125, 51,t⟩
abbrev bx3 (t:ℕ) :ℕ:=gV - kW t
def alR (a :ℕ) :ℕ:=if a<25 then 54 else 59
def fO (t first stop:ℕ) :Prop :=
  ∀ x,aO (lower t) x→aO x (upper t) →
    ∀ a,first≤a→a<stop→EW .ag x (bx3 t) a≤alR a
private theorem aMD:Monotone alR:= by
 intro a b hab
 unfold alR
 split_ifs <;> omega
private theorem DH {t:ℕ} {x q z :Shape}
  (hx :aO (lower t) x) (hy :aO x (upper t)) (h₁:10≤t) (h₂:t≤13)
  (hq:aO q z) (hc:yi.bF q) (hz :yi.bF z)
  (c:asQ) :
  Ix x q≤Ix (upper t) z ∧
    W5 c x q≤W5 c (upper t) z := by
 have ht:x.t=t:=Nat.le_antisymm hy.2.2 hx.2.2
 have hj:48≤x.j:=hx.2.1
 exact RR hy hq hc hz (by omega) (by omega) (by change 3*t+3≤51; omega) c
private theorem bt9 {b:bJ.Bank} {x :Shape} {v a r l D m h:ℕ}
  (hr :r≤a) (hl:1≤l)
  (hm:Ix x (H6 b x a r)≤ m)
  (hh:W5 (Xd a r) x (H6 b x a r)≤h)
  (hv :h<v) (hml:m≤(v - h)*l)
  (hd:YK a r x.t l - 1≤D) :
  EW b x v a≤D :=
 bpY hr hl (hh.trans_lt hv)
  (hm.trans (hml.trans (ztf _ (Nat.sub_le_sub_left hh _)))) hd
theorem iy {t first stop l m h:ℕ}
   (h₁:10≤t) (h₂:t≤13) (hl:1≤l)
   (hm:Ix (upper t) (H6 .ag (lower t) first first)=m)
   (hh:W5 .iy (upper t) (H6 .ag (lower t) first first)=h)
   (hv :h<bx3 t) (hml:m≤(bx3 t - h)*l)
   (hd:stop - 1+l - 1≤alR first) :fO t first stop:= by
 intro x hx hy a ha hb
 obtain ⟨hm',hh'⟩:=DH hx hy h₁ h₂ (dTh .ag (lower t) x ha)
   (aM8 _ _ _ _) (aM8 _ _ _ _) .iy
 refine bt9 (r :=a) le_rfl hl (hm'.trans_eq hm) ?_ hv hml ?_
 · rw [ Xd,ite_eq_left (rfl :a=a)]
   exact hh'.trans_eq hh
 · rw [YK,ite_eq_left (rfl :a=a)]
   exact (show a+l - 1≤ stop - 1+l - 1 by omega).trans (hd.trans (aMD ha))
private theorem eOV {a k r t l:ℕ} (ha :a≤k) (hr :r<a) :
   YK a r t l≤YK k r t l:= by
 have hr' := hr.trans_le ha
 simp only [YK,ite_eq_right hr.ne,ite_eq_right hr'.ne]
 apply max_le_max le_rfl
 apply Finset.sup_le
 intro s hs
 apply Finset.le_sup_of_le hs
 split
 · exact zIu (Nat.add_le_add_right (ztf s ha) _) _
 · exact le_rfl
theorem product {t first stop r l m h:ℕ}
   (h₁:10≤t) (h₂:t≤13) (hr :r<first) (hl:1≤l)
   (hm:Ix (upper t) (H6 .ag (lower t) first r)=m)
   (hh:W5 .product (upper t) (H6 .ag (lower t) first r)=h)
   (hv :h<bx3 t) (hml:m≤(bx3 t - h)*l)
   (hd:YK (stop - 1) r t l - 1≤alR first) :fO t first stop:= by
 intro x hx hy a ha hb
 have hra :=hr.trans_le ha
 have ht:x.t=t:=Nat.le_antisymm hy.2.2 hx.2.2
 obtain ⟨hm',hh'⟩:=DH hx hy h₁ h₂ (bZz hx .ag ha (r :=r))
   (aM8 _ _ _ _) (aM8 _ _ _ _) .product
 refine bt9 hra.le hl (hm'.trans_eq hm) ?_ hv hml ?_
 · simpa only [ Xd,ite_eq_right hra.ne] using hh'.trans_eq hh
 · rw [ht]
   exact (zIu (eOV (by omega) hra) _).trans (hd.trans (aMD ha))
end I5
end
section
namespace kX
open aR (Shape)

open cS (order ye)
def bw (s x :Shape) :ℕ:=ye (order .ag s) x
end kX
end
