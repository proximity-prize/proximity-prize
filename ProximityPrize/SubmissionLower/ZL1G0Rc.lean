import ProximityPrize.SubmissionLower.Zeuox8a
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.C3
set_option Elab.async false
open _root_ renaming Nat.add_le_add → z9f, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf
set_option autoImplicit true
section
open private aGh.ceil_mono aGh.u aGh.v from ProximityPrize.SubmissionLower.Zeuox8a
namespace By
open aR (Shape aO ceilDiv iH bY qP)
open vS (tC)
open yi (bF tD)
open bJ (Bank bf mV gZ dJ)



open nZ (j0 On Jg zK Xr Q5 Xz DC A9 KZ AA adM F4)
open scoped BigOperators
private def bCL (p q:Shape) :ℕ :=
 let u:=bf+1
 let v :=bf+2
 let a :=qP u p
 let b:=qP v p
 let g:=tC p
 min (iH p q (bY u p) (bY v p))
  (iH p q a b+u*iH p q g b+v*iH p q g a)
private theorem a8Y {p p' q:Shape} (hp:aO p p') (hp' : bF p') (hq:bF q) :
   bCL p q≤bCL p' q:= by
 let L:=bf
 have hchart:iH p q (bY (L+1) p) (bY (L+2) p) ≤
     iH p' q (bY (L+1) p') (bY (L+2) p') :=
   tD hp (j0 q) (DC _ hp) (DC _ hp) hp' hq
     (A9 _ _) hq (A9 _ _) (A9 _ _)
 have hlift:iH p q (qP (L+1) p) (qP (L+2) p) ≤
     iH p' q (qP (L+1) p') (qP (L+2) p') :=
   tD hp (j0 q) (KZ _ hp) (KZ _ hp) hp' hq
     (AA _ _) hq (AA _ _) (AA _ _)
 have hgraph (M:ℕ) :
     iH p q (tC p) (qP M p)≤ iH p' q (tC p') (qP M p') :=
   tD hp (j0 q) (adM hp) (KZ _ hp) hp' hq
     (F4 _) hq (F4 _) (AA _ _)
 exact min_le_min hchart (z9f (z9f hlift (zBI _ (hgraph _)))
   (zBI _ (hgraph _)))
private theorem ceil_mono {a b:ℕ} (h:a≤b) (l:ℕ) :ceilDiv a l≤ ceilDiv b l :=
 Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
private theorem dgq {p q:Shape} (ht:p.t≤2) :
   bJ.Rb p q=bCL p q:= by
 have hsmall : ¬ 2*(bf+1)≤(qP (bf+1) p).t:= by
   intro h
   have hh:=h.trans (min_le_left (2+(bf+1 - 5)*p.t) _)
   change 266922≤2+133456*p.t at hh
   omega
 unfold bJ.Rb bCL
 dsimp only
 split
 · rename_i h
   exact (hsmall h.2.2.2.2.1).elim
 · rfl
theorem aa8 (aV:Bank) {x y :Shape} (h:aO x y)
   (hx :3*x.t≤x.j) (hy :3*y.t≤y.j) (ht:y.t≤2) (l:ℕ) :
   dJ x aV.box l≤dJ y aV.box l:= by
 let p:=x.iU
 let p' := y.iU
 let q:=aV.box
 let L:=bf
 let A:=q.plus (p.scale 4)
 let A' := q.plus (p'.scale 4)
 have hp:=On h
 have hpc:bF p:=Jg x hx
 have hp'c:bF p' := Jg y hy
 have hqc:bF q:= by
   cases aV <;> exact ⟨by decide,by decide⟩
 have ha :aO A A' := zK (j0 q) (Q5 hp 4)
 have hac:bF A:=Xr hqc (Xz hpc 4)
 have ha'c:bF A' := Xr hqc (Xz hp'c 4)
 have hcurve :=tD hp (j0 q) ha (DC L hp) hp'c hqc ha'c hqc hac (A9 L p)
 have hpoint :=tD hp (j0 q) ha hp hp'c hqc ha'c hqc hac hpc
 have hcurve' := tD hp hp hp (DC L hp) hp'c hp'c hp'c hpc hpc (A9 L p)
 have hpoint' := tD hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
 have htc:=zBI 2 h.2.2
 have hc:=z9f hcurve (zcp htc hcurve')
 have hn:=z9f hpoint (zcp htc hpoint')
 have hgeom:=z9f (zBI P4.t hc) (zBI (2*mV) hn)
 have hraw:=ztf q.b (zBI (2*gZ) h.1)
 have hmain: (P4.t+2*mV)*x.b*q.b*(bY (L+1) p).b ≤
     (P4.t+2*mV)*y.b*q.b*(bY (L+1) p').b :=
   zcp (ztf _ (zBI _ h.1)) (DC _ hp).1
 unfold dJ bJ.aHo bJ.W5 bJ.Ix
 dsimp only
 rw [dgq (p:=x.iU) (q:=aV.box) (h.2.2.trans ht),
   dgq (p:=y.iU) (q:=aV.box) ht]
 exact z9f (z9f hraw (ceil_mono hgeom _))
   (ceil_mono (z9f (ceil_mono (a8Y hp hp'c hqc) _) (ceil_mono hmain _)) _)
end By
end
section
open private aGh.aO1 aGh.ccN aGh.fE aGh.j4 aGh.u aGh.v from ProximityPrize.SubmissionLower.Zeuox8a
namespace a0F


open bJ (Bank bf)





open aGh (j4 ccN aO1)
open aGh (fE)
private abbrev u:=bf+1
private abbrev v :=bf+2
private abbrev q:=Bank.ag.box



end a0F
end
