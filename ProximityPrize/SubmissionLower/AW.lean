import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.D7
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.AY
import ProximityPrize.SubmissionLower.BA
import ProximityPrize.SubmissionLower.E3
set_option Elab.async false
open _root_ renaming MvPolynomial.aeval → zIe, MvPolynomial.restrictCappedDegree → zVE, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
section
namespace cz7
noncomputable section
open Polynomial Finset
open P2 (K I node)
open aR (af extend embed)
open oR (qg)
open ana
theorem a8m {w:I→K} {T:Finset K} {s :K→K[X]} {a v :ℕ}
   (hdistinct :Set.InjOn s (T:Set K)) (f :af 2) (hf :Irreducible f) (hfpos :0<f.degreeOf 1)
   (hreg : ∀ γ∈T,qg 1 f (extend (s γ))) (ha :0<a) (hv :0<v)
   (i:I) (hmiss : ∃ γ∈T,(s γ).eval (node i)≠w i)
   (cut:MvPolynomial (Fin 2) Tv)
   (hcut:cut∈zVE (Fin 2) Tv 1 a v)
   (heval : ∀ γ∈T,zIe (Ia (extend (s γ))) cut=0 ↔
     (s γ).eval (node i)=w i) :
   (T.filter fun γ=>(s γ).eval (node i)=w i).card ≤
     MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
 classical
 let x (γ:K) :=Ia (extend (s γ))
 have hx :Set.InjOn x (T:Set K) := fun _ ha _ hb heq =>
   hdistinct ha hb (Polynomial.map_injective _ embed.injective (b8P heq))
 have hroot (γ:K) (hγ:γ∈T) :zIe (x γ) (u7 f)=0:= by
   dsimp only [x]
   rw [bT0,(hreg γ hγ).1,map_zero]
 have hproper :cut∉Ideal.span {u7 f} := by
   obtain ⟨η,hη,hbad⟩:=hmiss
   intro hmem
   obtain ⟨q,hq⟩:=Ideal.mem_span_singleton.mp hmem
   exact hbad ((heval η hη).mp (by rw [hq,map_mul,hroot η hη,zero_mul]))
 let lg:=T.filter fun γ=>(s γ).eval (node i)=w i
 have hplane :u7 f∈zVE (Fin 2) Tv 1
     f.totalDegree (f.degreeOf 1) := by
   intro m hm
   have hm' := MvPolynomial.support_map_subset asx f hm
   exact ⟨MvPolynomial.le_totalDegree hm',MvPolynomial.monomial_le_degreeOf 1 hm'⟩
 have hc:=bWs ha hv (cbT hf.ne_zero) (cbW hf hfpos)
   hplane hcut hproper (lg.image x) (by
     intro z hz
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
     obtain ⟨hγT,hγi⟩:=Finset.mem_filter.mp hγ
     exact ⟨hroot γ hγT,(heval γ hγT).mpr hγi⟩)
 rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc
end
end cz7
end
end
section
set_option autoImplicit true
section
namespace lC
open aR (Shape aO ceilDiv bY qP iH)
open vS (tC)
open yi (bF tD)
open bJ (dJ Ix sL bf mV gZ)
open nZ (On Jg zK Xr
 Q5 Xz DC A9 KZ AA adM F4)
private abbrev L:=bf
private def dR (p q:Shape) :ℕ :=
 let a :=qP (L+1) p
 let b:=qP (L+2) p
 iH p q a b+(L+1)*iH p q (tC p) b+(L+2)*iH p q (tC p) a
def mg (x q:Shape) (l:ℕ) :ℕ :=
  sL x q+ceilDiv (ceilDiv (dR x.iU q) 32 +
    ceilDiv ((P4.t+2*mV)*x.b*q.b*(bY (L+1) x.iU).b)
     mV) l
private theorem ceil_mono {a b:ℕ} (h:a≤b) (l:ℕ) :ceilDiv a l≤ ceilDiv b l :=
 Nat.div_le_div_right (Nat.sub_le_sub_right (zlr h l) 1)
theorem x9 (x q:Shape) (l:ℕ) :dJ x q l≤ mg x q l:= by
 change sL x q+ceilDiv (Ix x q) l≤ mg x q l
 unfold Ix mg
 apply z3b
 apply ceil_mono
 apply zlr
 apply ceil_mono
 unfold bJ.Rb
 dsimp only
 split
 · exact (min_le_right _ _).trans (min_le_left _ _)
 · exact min_le_right _ _
theorem zO {x y q r :Shape} (h:aO x y) (hq:aO q r)
   (hx :3*x.t≤x.j) (hy :3*y.t≤y.j) (hc:bF q) (hr :bF r)
   (l:ℕ) :mg x q l≤ mg y r l:= by
 let p:=x.iU
 let p' := y.iU
 let Q:=q.plus (p.scale 4)
 let R:=r.plus (p'.scale 4)
 have hp:aO p p' := On h
 have hx' := Jg x hx
 have hy' := Jg y hy
 have hQ:aO Q R:=zK hq (Q5 hp 4)
 have hQx :bF Q:=Xr hc (Xz hx' 4)
 have hQy :bF R:=Xr hr (Xz hy' 4)
 have hl:dR p q≤dR p' r := by
   have h₁:=tD hp hq (KZ (L+1) hp) (KZ (L+2) hp)
     hy' hr (AA _ _) hc (AA _ _) (AA _ _)
   have h₂ (m:ℕ) :=tD hp hq (adM hp) (KZ m hp)
     hy' hr (F4 _) hc (F4 _) (AA _ _)
   exact z9f (z9f h₁ (zBI _ (h₂ (L+2))))
     (zBI _ (h₂ (L+1)))
 have hraw (k :ℕ) :k*x.b*q.b≤k*y.b*r.b :=
   zcp (zBI _ h.1) hq.1
 have hm:=zcp (hraw (P4.t+2*mV)) (DC (L+1) hp).1
 have h₁:=tD hp hq hQ (DC L hp) hy' hr hQy hc hQx (A9 L p)
 have h₂:=tD hp hq hQ hp hy' hr hQy hc hQx hx'
 have h₃:=tD hp hp hp (DC L hp) hy' hy' hy' hx' hx' (A9 L p)
 have h₄:=tD hp hp hp hp hy' hy' hy' hx' hx' hx'
 have htop:=zBI 2 h.2.2
 have hcurve :=z9f h₁ (zcp htop h₃)
 have hpoint :=z9f h₂ (zcp htop h₄)
 have hgeom:=z9f (zBI P4.t hcurve)
   (zBI (2*mV) hpoint)
 exact z9f (z9f (hraw (2*gZ)) (ceil_mono hgeom _))
   (ceil_mono (z9f (ceil_mono hl _) (ceil_mono hm _)) l)
theorem ug {x :Shape} {l m:ℕ} (hm:0< m) (h:m≤l) :
  cS.ye l x≤dJ x gW.Bank.ag.box m:= by
 unfold cS.ye wV.C8
 dsimp only
 rw [ite_eq_left (hm.trans_le h)]
 exact (min_le_left _ _).trans (z3b (FI.aqT _ hm h) _)
end lC
end
end
