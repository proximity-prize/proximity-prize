import ProximityPrize.SubmissionLower.CE
import ProximityPrize.SubmissionLower.Z0omYcd
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
open _root_ renaming Nat.add_le_add → z9f, Nat.mul_le_mul_left → zBI, Nat.mul_left_comm → zZ0, Nat.sub_le_sub_right → zIu
set_option autoImplicit true
section
namespace nZ
open aR (Shape aO bY qP iH gI Dn)
open vS (tC)
open yi (bF)
open Ds (wP oL)

open private bwp from ProximityPrize.SubmissionLower.T
theorem j0 (x :Shape) :aO x x :=⟨le_rfl,le_rfl,le_rfl⟩
theorem On {x y :Shape} (h:aO x y) :
 aO x.iU y.iU:=⟨max_le_max h.1 h.2.1,h.2.1,h.2.2⟩
theorem Jg (x :Shape) (h:3*x.t≤x.j) :
 bF x.iU:=⟨le_max_right _ _,h⟩
theorem zK {x y u v :Shape} (h:aO x y) (h' : aO u v) :
   aO (x.plus u) (y.plus v) :=
 ⟨z9f h.1 h'.1,z9f h.2.1 h'.2.1,z9f h.2.2 h'.2.2⟩
theorem Xr {x y :Shape} (hx :bF x) (hy :bF y) :
  bF (x.plus y) := by
 exact ⟨z9f hx.1 hy.1,by simp only [Shape.plus,Nat.mul_add]; exact z9f hx.2 hy.2⟩
theorem Q5 {x y :Shape} (h:aO x y) (k :ℕ) :
   aO (x.scale k) (y.scale k) :=
 ⟨zBI k h.1,zBI k h.2.1,zBI k h.2.2⟩
theorem Xz {x :Shape} (hx :bF x) (k :ℕ) :
   bF (x.scale k) :=
 ⟨zBI k hx.1,by simpa [Shape.scale,zZ0 3 k] using zBI k hx.2⟩
theorem ZT (a i:ℕ) :3*min a (i/3)≤ i:= by
 have h:=min_le_right a (i/3)
 omega
theorem A9 (L:ℕ) (x :Shape) :bF (bY L x) :=
 ⟨le_max_right _ _,ZT _ _⟩
theorem AA (L:ℕ) (x :Shape) :bF (qP L x) :=
 ⟨le_max_right _ _,ZT _ _⟩
theorem DC (L:ℕ) {x y :Shape} (h:aO x y) :
  aO (bY L x) (bY L y) := by
 obtain ⟨hb,hj,ht⟩:=h
 refine ⟨?_,?_,?_⟩ <;> dsimp [bY] <;> gcongr
theorem KZ (L:ℕ) {x y :Shape} (h:aO x y) :
  aO (qP L x) (qP L y) := by
 obtain ⟨hb,hj,ht⟩:=h
 refine ⟨?_,?_,?_⟩ <;> dsimp [qP] <;> gcongr
theorem F4 (x :Shape) :bF (tC x) :=
 ⟨le_max_right _ _,ZT _ _⟩
theorem adM {x y :Shape} (h:aO x y) :
  aO (tC x) (tC y) := by
 obtain ⟨hb,hj,ht⟩:=h
 refine ⟨?_,?_,?_⟩ <;> dsimp [tC] <;> gcongr
private def slope :Shape :=⟨1,4, 2⟩
private def shift (k h:ℕ) (x :Shape) :Shape :=
 ⟨k*x.b - h,k*x.j-4*h,k*x.t - 2*h⟩
private theorem acJ {x :Shape} {k h:ℕ}
  (hx :bF x) (hk :0<k) (ht:2*h≤x.t) :bF (shift k h x) := by
 have hfit :=(zBI k hx.2)
 rw [← zZ0 3 k] at hfit
 have hb:=zBI k hx.1
 have ht' := ht.trans (Nat.le_mul_of_pos_left x.t hk)
 change k*x.j-4*h≤k*x.b - h ∧
  3*(k*x.t - 2*h)≤k*x.j-4*h
 omega
private theorem aET {x y :Shape} (h:aO x y) (k t:ℕ) :
   aO (shift k t x) (shift k t y) :=
 ⟨zIu (zBI k h.1) _,
   zIu (zBI k h.2.1) _,
   zIu (zBI k h.2.2) _⟩
private theorem bNV (k :ℕ) (p q r s :Shape) :
  wP (p.scale k) q r s=(k :ℤ)*wP p q r s := by
 simp only [wP,gI,Dn,Shape.plus,Shape.scale,oL,
  FI.oL,Nat.cast_add,Nat.cast_mul,Nat.cast_zero]
 ring
private theorem bhj (p q r s :Shape) (hq:bF q) (hr :bF r)
  (hs :bF s) : (iH p q r s :ℤ)=wP p q r s :=
 Int.toNat_of_nonneg (show 0≤wP p q r s from bwp p q r s hq hr hs)
end nZ
end
