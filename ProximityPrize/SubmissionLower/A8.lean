import ProximityPrize.SubmissionLower.ZL1G0Rc
import ProximityPrize.SubmissionLower.ZSJzjxb
import ProximityPrize.SubmissionLower.Zeuox8a
set_option Elab.async false
open _root_ renaming Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf
set_option maxRecDepth 256
set_option maxHeartbeats 80000
set_option autoImplicit true
section
namespace fk
open aR (Shape aO ceilDiv bY iH)

open yi (bF tD)
open bJ (Bank bf dJ sL lY)
open cS (order yF ye)
open wV (pS zN C8)
open nZ (j0 On Jg zK Xr Q5 Xz DC A9 ZT)
open scoped BigOperators
theorem fE (b:Bank) {x y :Shape} (ht:0<x.t) (hxy :aO x y) :
  order b x≤order b y := by
 change yF pS b x≤yF pS b y
 unfold yF ceilDiv
 apply Nat.div_le_div_right
 apply Nat.sub_le_sub_right
 apply zlr
 apply Nat.sub_le_sub_left
 apply zBI
 unfold zN
 exact (Finset.sum_le_sum fun i _=>WO.aaQ b (Q5 hxy (i+1))).trans
  (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.div_le_div_left hxy.2.2 ht)))
private theorem aO0 (l bw x :ℕ) :C8 l bw x≤x := by
 unfold C8
 split
 · exact min_le_right _ _
 · exact le_rfl
theorem NC (l:ℕ) (x :Shape) :ye l x≤lY x :=
 (aO0 _ _ _).trans (aO0 _ _ _)
theorem awa {s x :Shape} {l:ℕ} (hl:0<l) (ho:l≤order .dB x) :
   ye (order .ag s) x≤dJ x Bank.dB.box l:= by
 let o:=order .dB x
 have hf :C8 o (dJ x Bank.dB.box o) (lY x) ≤
     dJ x Bank.dB.box o:= by
   rw [C8,ite_eq_left (show 0<o from hl.trans_le ho)]
   exact min_le_left _ _
 exact ((aO0 _ _ _).trans hf).trans
   (z3b (FI.aqT _ hl ho) _)
private theorem ceil_mono {a b:ℕ} (h:a≤b) (l:ℕ) :ceilDiv a l≤ ceilDiv b l :=
 Py.LI h l
private abbrev u:=bf+1
private abbrev v :=bf+2
private def iy (p q:Shape) :ℕ:=iH p q (bY u p) (bY v p)
def Di (x q:Shape) (l:ℕ) :ℕ :=
  min (lC.mg x q l)
    (sL x q+ceilDiv (ceilDiv (iy x.iU q) 32 +
      ceilDiv ((P4.t+2*bJ.mV)*x.b*q.b*(bY u x.iU).b)
        bJ.mV) l)
theorem aa7 (x q:Shape) (l:ℕ) :dJ x q l≤Di x q l:= by
 apply le_min (lC.x9 _ _ _)
 apply z3b
 apply ceil_mono
 apply zlr
 apply ceil_mono
 unfold bJ.Rb
 dsimp only
 split <;> exact min_le_left _ _
theorem afr {x y q:Shape} (h:aO x y)
    (hx :3*x.t≤x.j) (hy :3*y.t≤y.j) (hq:bF q)
    (l:ℕ) :Di x q l≤Di y q l:= by
  apply min_le_min (lC.zO h (j0 _) hx hy hq hq l)
  have hp:=On h
  have hp' := Jg y hy
  have hm:=tD hp (j0 q) (DC u hp) (DC v hp)
    hp' hq (A9 _ _) hq (A9 _ _) (A9 _ _)
  let p:=x.iU
  let p' := y.iU
  let L:=bf
  let Q:=q.plus (p.scale 4)
  let R:=q.plus (p'.scale 4)
  have hpc:=Jg x hx
  have hQ:aO Q R:=zK (j0 q) (Q5 hp 4)
  have hQc:bF Q:=Xr hq (Xz hpc 4)
  have hRc:bF R:=Xr hq (Xz hp' 4)
  have h₁:=tD hp (j0 q) hQ (DC L hp) hp' hq hRc hq hQc (A9 L p)
  have h₂:=tD hp (j0 q) hQ hp hp' hq hRc hq hQc hpc
  have h₃:=tD hp hp hp (DC L hp) hp' hp' hp' hpc hpc (A9 L p)
  have h₄:=tD hp hp hp hp hp' hp' hp' hpc hpc hpc
  have htop:=zBI 2 h.2.2
  have hc:=z9f h₁ (zcp htop h₃)
  have hn:=z9f h₂ (zcp htop h₄)
  have ha :sL x q≤ sL y q :=
    z9f (ztf q.b (zBI (2*bJ.gZ) h.1))
      (ceil_mono (z9f (zBI P4.t hc)
        (zBI (2*bJ.mV) hn)) _)
  have hb:=zcp
    (ztf q.b (zBI (P4.t+2*bJ.mV) h.1))
    (DC u hp).1
  exact z9f ha
    (ceil_mono (z9f (ceil_mono hm 32) (ceil_mono hb bJ.mV)) l)
private abbrev aMw:Shape :=⟨bJ.aPr,bJ.aWz,0⟩
private abbrev common :Shape :=
 ⟨bJ.aHc+aMw.b/bJ.tau,bJ.aM1+aMw.j/bJ.tau,0⟩
private def rH (x :Shape) :Shape :=
 if x.t=1 then bJ.ajN x.iU else bY (bf+4) x.iU
private theorem aNL {x y :Shape} (h:aO x y) (ht:x.t=y.t) :
   aO (rH x) (rH y) := by
 have hp:=On h
 unfold rH
 by_cases h₁:x.t=1
 · have h₂:y.t=1 :=ht ▸ h₁
   rw [ite_eq_left h₁,ite_eq_left h₂]
   obtain ⟨hb,hj,_⟩:=hp
   refine ⟨?_,?_,?_⟩ <;> dsimp [bJ.ajN] <;> gcongr
 · have h₂ : ¬ y.t=1 := fun h₂=>h₁ (ht.trans h₂)
   rw [ite_eq_right h₁,ite_eq_right h₂]
   exact DC _ hp
private theorem aro (x :Shape) :bF (rH x) := by
 unfold rH
 split
 · exact ⟨le_max_right _ _,ZT _ _⟩
 · exact A9 _ _
private def V0 (h:Shape) :Shape :=
 ⟨max (max h.b common.b) (max h.j (common.j+1)),
   max h.j (common.j+1),max 1 h.t⟩
private theorem arp {h:Shape} (hh:bF h) :bF (V0 h) := by
 refine ⟨le_max_right _ _,?_⟩
 change 3*max 1 h.t≤ max h.j (common.j+1)
 rcases le_total 1 h.t with h₁ | h₁
 · rw [max_eq_right h₁]
   exact hh.2.trans (le_max_left _ _)
 · rw [max_eq_left h₁]
   exact (show 3≤ common.j+1 by decide).trans (le_max_right _ _)
private theorem aNM {a b:Shape} (h:aO a b) :aO (V0 a) (V0 b) := by
 obtain ⟨hb,hj,ht⟩:=h
 refine ⟨?_,?_,?_⟩ <;> dsimp [V0] <;> gcongr
theorem RQ {x y :Shape} (h:aO x y) (ht:x.t=y.t)
    (hx :3*x.t≤x.j) (hy :3*y.t≤y.j) :lY x≤lY y := by
  let p:=x.iU
  let p' := y.iU
  let a :=rH x
  let a' := rH y
  let c:=V0 a
  let c' := V0 a'
  have hp:=On h
  have hpc:=Jg x hx
  have hp'c:=Jg y hy
  have ha :=aNL h ht
  have hac:=aro x
  have ha'c:=aro y
  have hc:=aNM ha
  have hcc:=arp hac
  have hc'c:=arp ha'c
  have hcommon :bF common := by unfold bF; decide
  have hbroad:bF aMw:= by unfold bF; decide
  have hm1 :=tD hp (j0 common) hc ha hp'c hcommon hc'c hcommon hcc hac
  have hm2 :=tD hp (j0 common) hc hp hp'c hcommon hc'c hcommon hcc hpc
  have hm3:=tD hp hp ha ha hp'c hp'c ha'c hpc hac hac
  have hm4 :=tD hp (j0 aMw) (j0 aMw) ha hp'c hbroad hbroad hbroad hbroad hac
  have hm5:=tD hp (j0 aMw) (j0 aMw) hp hp'c hbroad hbroad hbroad hbroad hpc
  have hb:=h.1
  have hpb:p.b≤p'.b:=hp.1
  have hab:a.b≤a'.b:=ha.1
  have hs : (if 1<x.t then ceilDiv (4*x.t*iH p p a a) 32 + x.t*x.b^2+1 else 0) ≤
      (if 1<y.t then ceilDiv (4*y.t*iH p' p' a' a') 32+y.t*y.b^2+1 else 0) := by
    rw [ht]
    split
    · gcongr
      exact ceil_mono (zBI _ hm3) _
    · exact le_rfl
  have hd :
      ceilDiv (P4.t*iH p common c a) (32*bJ.mV) +
        ceilDiv (iH p common c p) 32+20*p.b*a.b^2 +
        5*bJ.gZ*p.b*a.b+1 ≤
      ceilDiv (P4.t*iH p' common c' a') (32*bJ.mV) +
        ceilDiv (iH p' common c' p') 32+20*p'.b*a'.b^2 +
        5*bJ.gZ*p'.b*a'.b+1 := by
    gcongr
    · exact ceil_mono (zBI _ hm1) _
    · exact ceil_mono hm2 _
  refine zlr (z9f (z9f hd hs) ?_) _
  exact ceil_mono
    (z9f (zBI _ hm4) (zBI _ hm5)) _
end fk
end
section
namespace fk
open aR (Shape)

open bJ (Bank dJ)

open CQ (box)
def kn (a z :Shape) (b:Bank) (l:ℕ) :ℕ :=
 if 3≤a.t∧3*a.t+3≤a.j then dJ z b.box l
 else Di z b.box l
end fk
end
section
namespace fk
open aR (Shape aO)
open yi (bF)

open bJ (Bank Valid dJ)

open CQ (box)
private theorem Yw {x a z :Shape} (hxa :aO a x) (hxz :aO x z)
   (hv :Valid x) (ht:x.t=z.t) (hat :a.t=x.t) (b:Bank) (l:ℕ) :
   dJ x b.box l≤kn a z b l:= by
 have hq:bF b.box := by cases b <;> exact ⟨by decide,by decide⟩
 have hxb:=hv.2.1
 have hzb:3*z.t≤z.j:=ht ▸ hxb.trans hxz.2.1
 unfold kn
 split
 · rename_i h
   have hj:=h.2.trans hxa.2.1
   have hj' := hj.trans hxz.2.1
   have hf :=I5.RR hxz (nZ.j0 b.box) hq hq
     (hat ▸ h.1) (hat ▸ hj) (hat.trans ht ▸ hj') .iy
   exact z9f hf.2 (Py.LI hf.1 l)
 · exact (aa7 x _ _).trans (afr hxz hxb hzb hq l)
end fk
end
