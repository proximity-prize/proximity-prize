import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.C3
set_option Elab.async false
set_option autoImplicit true
section
namespace aGh
open aR (Shape aO ceilDiv iH qP)
open vS (tC)
open yi (bF tD)
open nZ (j0 KZ AA adM F4)
open bJ (bf)


open wV (C8)
private theorem ceil_mono {a b:ℕ} (h:a≤b) (l:ℕ) :ceilDiv a l≤ ceilDiv b l :=
 Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
private abbrev u:=bf+1
private abbrev v :=bf+2
private def j4 (p q:Shape) :ℕ :=
 let a :=qP u p
 let b:=qP v p
 let g:=tC p
 iH p q a b+u*iH p q g b+v*iH p q g a
private theorem ccN {p p' q:Shape} (hp:aO p p') (hp' : bF p')
  (hq:bF q) :j4 p q≤j4 p' q:= by
 have hlift :=
  tD hp (j0 q) (KZ u hp) (KZ v hp) hp' hq
    (AA _ _) hq (AA _ _) (AA _ _)
 have hgraph (M:ℕ) :=
  tD hp (j0 q) (adM hp) (KZ M hp) hp' hq
    (F4 _) hq (F4 _) (AA _ _)
 exact Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
  (Nat.mul_le_mul_left _ (hgraph _))
private theorem aO1 (l v f :ℕ) :C8 l v f≤f := by
 unfold C8
 split
 · exact min_le_right _ _
 · exact le_rfl
end aGh
end
section
namespace By
open aR (Shape aO)
open Jt (fQ)
open bJ (Valid gV m6)

open Ry (ahK bw)
structure Path (p x y :Shape) :Prop where
 vp:Valid p
 vx :Valid x
 vy :Valid y
 fits :aO ((p.plus x).plus y) m6
 tp:p.t=2
 tx :x.t=1
 ty :y.t=1
structure Cell where
 p:fQ
 x :fQ
 y :fQ
def Cell.dY (r :Cell) (p x y :Shape) :Prop :=
 r.p.dY p∧r.x.dY x∧r.y.dY y
def ay (r :Cell) :Prop :=
 ∀ p x y,Path p x y→ r.dY p x y→ahK (bw p p) p x y≤gV
def be3 (r :fQ) :ℕ:=max r.lowerB ((r.lowerJ+2)/3)
def clip (r u v :fQ) :fQ :=
 let b:=min r.upperB (125-(be3 u+be3 v))
 ⟨be3 r,b,r.lowerJ,min r.upperJ (min (51-(u.lowerJ+v.lowerJ)) (3*b))⟩
def XH (r :Cell) :Cell :=
 ⟨clip r.p r.x r.y,clip r.x r.p r.y,clip r.y r.p r.x⟩
inductive Position where
 | first | middle | last
def half (r :fQ) (index right:Bool) (k :ℕ) :fQ :=
  if index then
    if right then { r with lowerJ:=k+1 } else { r with upperJ:=k }
  else
    if right then { r with lowerB:=k+1 } else { r with upperB:=k }
def branch (r :Cell) (i:Position) (index right:Bool) (k :ℕ) :Cell :=
 match i with
 | .first => { r with p:=half r.p index right k }
 | .middle => { r with x :=half r.x index right k }
 | .last => { r with y :=half r.y index right k }
end By
end
section
namespace aGh
open aR (Shape aO ceilDiv)


open cS (yF order)

open wV (zN)
open nZ (Q5)



open scoped BigOperators
private theorem fE {x y :Shape} (ht:0<x.t) (hxy :aO x y) :
  order .ag x≤order .ag y := by
 unfold order yF ceilDiv
 apply Nat.div_le_div_right
 apply Nat.sub_le_sub_right
 apply Nat.add_le_add_right
 apply Nat.sub_le_sub_left
 apply Nat.mul_le_mul_left
 unfold zN
 apply FI.gw6 (Nat.div_le_div_left hxy.2.2 ht)
 intro i _
 exact WO.aaQ .ag (Q5 hxy (i+1))
end aGh
end
