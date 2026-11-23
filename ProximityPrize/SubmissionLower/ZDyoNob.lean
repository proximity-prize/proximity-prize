import ProximityPrize.SubmissionLower.ZJEYUQc
import ProximityPrize.SubmissionLower.ZNc08Oa
set_option Elab.async false
open _root_ renaming Ideal→cy,Nat.add_le_add_left→ oj,Nat.mul_le_mul_left→n5,Nat.sub_add_cancel→ ox,Or.inl→lV,Or.inr→lJ,P5_7.FarBand→c9,P5_7.Pairs→nq,gT.Ambient→aU,le_max_left→mD,le_max_right→nX
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace P5_7_5
noncomputable section
open Polynomial

open P5_7 (Ls Jr InFar O2 anM aRe)
open cu (Shape vP Jet)
open gT (iJ)
open pI (NO oU)
open ac2
open ac3
open private dfc ddV from ProximityPrize.SubmissionLower.U


open scoped BigOperators Classical
abbrev afa (b:c9) :=Fin b.row.stages.length
def arS {b h rows} (pairs :nq b h rows) (i:afa b) :
    P5_7.akE h rows (nV b i) :=
  pairs _ (cqz i.isLt)
theorem aU2 {b:c9} (i:afa b) :Jr b (nV b i).free :=
 lJ (lV ⟨_,cqz i.isLt,lV rfl⟩)
theorem a5S {b:c9} (i:afa b) :Jr b (nV b i).moving :=
 lJ (lV ⟨_,cqz i.isLt,lJ rfl⟩)
private theorem cDJ {b w} (hw:InFar b w) {r :ℕ} {s :Shape}
  (guard :am1 b.row.hi r s) :
  anM w.toNat r s+2*w.toNat*r≤O2 s := by
 have h:=Nat.mul_le_mul_right r (n5 2 (aRe hw).2)
 have h' := h.trans guard.buffer
 unfold anM
 omega
structure bQX {b h rows} (pairs :nq b h rows) (i:afa b) where
 free :NO (arS pairs i).free (nV b i).free.shape
 moving:NO (arS pairs i).moving (nV b i).moving.shape
theorem gxI {h rows s} {pair :P5_7.akE h rows s}
   {I:cy aU} (hI:I.IsPrime) (hp:axS pair I) :
   P5_7.axS pair (ac6.Bridge.aQF I hI) :=
 ⟨hp.1,hp.2.1,hp.2.2⟩
private theorem ddZ {A:Type*} [CommRing A] (a :cu.aZ →+* A)
  {rows :vP} {s :Shape} {I:cy aU} {h W r :ℕ} {P:Jet}
  (hn : ∀ W W',W≤W' → rows s W≤ rows s W')
  (hs :qQ.bk4 h rows s) (hv :agA rows s I)
  (hcut:W+2*h*r≤O2 s) (hP:P∈rows s W) :
  bp3 (I.map (Ih a)) (Ih a (iJ P)) r := by
 intro t ht
 rw [← dfc]
 apply Ideal.mem_map_of_mem
 exact hv _ (hn _ _ ((oj (n5 _ ht) _).trans hcut)
  (ddV hs hP t))
private theorem d1m {s :Ls} {P:Jet}
   (hb:s.free.shape.J≤ s.free.shape.B) (hc:s.moving.shape.J≤ s.moving.shape.B)
   (hP:oU P s.free.shape∨oU P s.moving.shape) :oU P (a3D s) := by
 have ha :s.free.shape.B≤(a3D s).B :=
   (ox hb).symm.trans_le
     (Nat.add_le_add (mD _ _) (mD _ _))
 have hd:s.moving.shape.B≤(a3D s).B :=
   (ox hc).symm.trans_le
     (Nat.add_le_add (nX _ _) (nX _ _))
 intro j i h
 rcases hP with hp | hp
 · obtain ⟨hg,hj,hu⟩:=hp j i h
   exact ⟨hg.trans ha,hj.trans (mD _ _),hu.trans (mD _ _)⟩
 · obtain ⟨hg,hj,hu⟩:=hp j i h
   exact ⟨hg.trans hd,hj.trans (nX _ _),hu.trans (nX _ _)⟩
end
end P5_7_5
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
namespace qeA2Kad
open P5 (p)

open P5_7_5
open TD (aa3)
private def SY (x :ℚ) :ℕ:=x.floor.toNat
private theorem b3F (n:ℕ) :SY (n:ℚ)=n:= by
 change ⌊(n:ℚ)⌋.toNat=n
 rw [Int.floor_natCast,Int.toNat_natCast]
def beC:c9→Fin 4→ℕ
 | .dbl => ![2828,17085,83044, 240507]
 | .lZ => ![1961,11195, 54528,139683]
 | .om => ![828,8764,43207,184233]
 | .wS => ![132,1612,9316,51496]
 | .vX => ![132,1313,7565, 33875]
 | .vg => ![18,133,1205,4042]
 | .wI => ![18,57,519,756]
 | .vW => ![18,51,465,608]
 | .wO => ![18,43, 392,432]
 | .wQ => ![11,38,216,325]
theorem au9 (b:c9) (k :Fin 4) :BC b k=beC b k := by
 cases b <;> fin_cases k <;> with_unfolding_all rfl
theorem cVa (b:c9) :
    al6 b=if b.row.RU.isEmpty then
        (nV b 0).free.shape.U*(nV b 0).moving.shape.U +
          (aa3 (nV b 0).free.shape (nV b 0).moving.shape)^2
      else beC b 3:= by
  rw [al6,au9]
theorem bq6 (b:c9) (k :Fin 4) :BC b k<p:= by
 rw [au9]
 cases b <;> fin_cases k <;> decide
theorem bq5 (b:c9) :BC b 3≤al6 b:= by
 rw [au9,cVa]
 cases b <;> exact Nat.le_of_ble_eq_true rfl
private theorem c6E (b:c9) (hb:Wx b=0) :
  aEt b=beC b 2∧aEv b=beC b 1 := by
 change SY (ar3 b 2)= _∧SY (ar3 b 1)= _
 constructor <;> simp only [ar3,hb,ite_true,V8,b3F,au9]
def c6C:c9→ℕ×ℕ
 | .lZ=>(54528,11195)
 | .om=>(27918,5703)
 | b=>(beC b 2,beC b 1)
theorem rank_eq (b:c9) :aEt b=(c6C b).1∧aEv b=(c6C b).2 := by
  cases b <;>
    try exact c6E _ rfl
  · change (min (min (BC .lZ 2 :ℚ) (aE6 .lZ 1 false 2))
      (aE6 .lZ 2 false 2)).floor.toNat=54528 ∧
      (min (min (BC .lZ 1 :ℚ) (aE6 .lZ 1 false 1))
        (aE6 .lZ 2 false 1)).floor.toNat=11195
    simp only [au9]
    exact ⟨by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · change (min (BC .om 2 :ℚ) (aE6 .om 1 false 2)).floor.toNat=27918 ∧
      (min (BC .om 1 :ℚ) (aE6 .om 1 false 1)).floor.toNat=5703
    simp only [au9]
    exact ⟨by with_unfolding_all rfl,by with_unfolding_all rfl⟩
theorem bK5 (b:c9) :aBh (aEt b) (aEv b) := by
 rw [(rank_eq b).1,(rank_eq b).2]
 cases b <;> exact ⟨by decide,by decide,by decide,by decide⟩
end qeA2Kad
end
