import ProximityPrize.SubmissionLower.ZO2xefe
import ProximityPrize.SubmissionLower.BU
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AJ
set_option Elab.async false
set_option autoImplicit true
section
namespace jN
open aR (Shape aO)
open bJ (Bank Valid dJ lY)
open cS (order)
open kX (bw)
open nF (eG)
open fk (fE NC awa)
open private Yw from ProximityPrize.SubmissionLower.A8
abbrev F6 (x :ℕ) (w:Window) :=eG x (w .indexX).lo (w .degreeX).lo
abbrev Oy (x :ℕ) (w:Window) :=eG x (w .indexX).hi (w .degreeX).hi
abbrev QW (y :ℕ) (w:Window) :=eG y (w .indexY).lo (w .degreeY).lo
abbrev Oz (y :ℕ) (w:Window) :=eG y (w .indexY).hi (w .degreeY).hi
def BB (w:Window) :ℕ :=
 max (w .indexSum).lo ((w .indexX).lo+(w .indexY).lo)
abbrev QX (x y :ℕ) (w:Window) :=
 eG (x+y) (BB w) ((w .degreeX).lo+(w .degreeY).lo)
def uq (a z :Shape) (b:Bank) (l:ℕ) :ℕ :=
 if a.j=z.j∨z.t≤2 then dJ z b.box l
 else fk.kn a z b l
private theorem dgX {a e z :Shape} (he :Valid e) (ha :aO a e)
   (hz :aO e z) (hat :a.t=e.t) (hzt:e.t=z.t) (b:Bank) (l:ℕ) :
   dJ e b.box l≤uq a z b l:= by
 unfold uq
 split
 · rename_i h
   rcases h with h | h
   · have hj:e.j=z.j:=le_antisymm hz.2.1 (h ▸ ha.2.1)
     exact nF.Tf hz.1 hj hzt he.2.1 b l
   · exact By.aa8 b hz he.2.1 (hzt ▸ he.2.1.trans hz.2.1) h l
 · exact Yw ha hz he hzt hat b l
inductive rj (a z s :Shape) :ℕ→Prop
 | wM {v} : lY z=v→ rj a z s v
 | ag {l v} : 0<l→l≤order .ag s→uq a z .ag l≤v→ rj a z s v
 | dB {l v} : 0<l→l≤order .dB a→uq a z .dB l≤v→ rj a z s v
private theorem FN {s p a e z :Shape} {v :ℕ} (h:rj a z p v)
   (he :Valid e) (ha :aO a e) (hz :aO e z)
   (hat :a.t=e.t) (hzt:e.t=z.t) (hp:aO p s) (ht:0<p.t) :
   bw s e≤v := by
 cases h with
 | wM hf =>
   exact (NC _ _).trans ((fk.RQ hz hzt he.2.1
     (hzt ▸ he.2.1.trans hz.2.1)).trans_eq hf)
 | ag hl ho hf =>
   exact (lC.ug hl (ho.trans (fE .ag ht hp))).trans
     ((dgX he ha hz hat hzt .ag _).trans hf)
 | dB hl ho hf =>
   exact (awa hl (ho.trans (fE .dB (hat ▸ he.1) ha))).trans
     ((dgX he ha hz hat hzt .dB _).trans hf)
private theorem aku (t j:ℕ) (ht:6≤t) (ht' : t≤8) (hj:j<24) :
  units t j≤units t (j+1) := by
 interval_cases t <;> interval_cases j <;> decide
private theorem units_mono {t i j:ℕ} (h₁:6≤t) (h₂:t≤8) (h:i≤j)
   (hj:j≤24) :units t i≤units t j:= by
 induction j,h using Nat.le_induction with
 | base=>exact le_rfl
 | succ j _ ih=>exact (ih (by omega)).trans (aku t j h₁ h₂ (by omega))
theorem gH {x y u v iL:ℕ} {win:Window}
   (ht:6≤x+y) (ht' : x+y≤8)
   (hx :rj (F6 x win) (Oy x win) (F6 x win) u)
   (hy :rj (QW y win) (Oz y win) (QX x y win) v)
   (hc:units (x+y) (BB win)=iL) (hp:u+v≤unit*iL) :
   ay x y win:= by
 intro z h hxv hyv _ hs _
 have hX:aO (F6 x win) (first x z) :=
   ⟨Nat.add_le_add_left (h .degreeX).1 _,Nat.add_le_add_left (h .indexX).1 _,le_rfl⟩
 have hX' : aO (first x z) (Oy x win) :=
   ⟨Nat.add_le_add_left (h .degreeX).2 _,Nat.add_le_add_left (h .indexX).2 _,le_rfl⟩
 have hY:aO (QW y win) (second y z) :=
   ⟨Nat.add_le_add_left (h .degreeY).1 _,Nat.add_le_add_left (h .indexY).1 _,le_rfl⟩
 have hY' : aO (second y z) (Oz y win) :=
   ⟨Nat.add_le_add_left (h .degreeY).2 _,Nat.add_le_add_left (h .indexY).2 _,le_rfl⟩
 have hd: (win .degreeX).lo+(win .degreeY).lo≤z.a+z.b :=
   Nat.add_le_add (h .degreeX).1 (h .degreeY).1
 have hi:BB win≤z.q+z.r :=max_le (h .indexSum).1
   (Nat.add_le_add (h .indexX).1 (h .indexY).1)
 have hpre :aO (QX x y win) ((first x z).plus (second y z)) := by
   refine ⟨?_,?_,le_rfl⟩
   · change x+y+((win .degreeX).lo+(win .degreeY).lo)≤x+z.a+(y+z.b)
     omega
   · change 3*(x+y)+BB win≤3*x+z.q+(3*y+z.r)
     omega
 have fx :=FN hx hxv hX hX' rfl rfl hX hxv.1
 have fy :=FN hy hyv hY hY' rfl rfl hpre (hxv.1.trans (Nat.le_add_right _ _))
 rw [← hc] at hp
 exact (Nat.add_le_add fx fy).trans (hp.trans
   (Nat.mul_le_mul_left unit (units_mono ht ht' hi hs)))
end jN
end
