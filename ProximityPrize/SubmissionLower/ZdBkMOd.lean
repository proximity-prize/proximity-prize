import ProximityPrize.SubmissionLower.Zytxfqb
import ProximityPrize.SubmissionLower.Z07A6ec
import ProximityPrize.SubmissionLower.Zq1cNdd
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d := 0xd6f38800038140001600022dfd0f00091d5000398001a1312f4006d546002b6000d23bdd100374ccc016180057c92ef8017315b009560020d51f57008b7ad40389800b6b8ef40030c8de013f6003c5ce8fb0103700006b180132fa1534053031e02296005eadf1c5019c9ef80ad9801c810986c07d321803536
local notation "q!" k:arg n:arg => block 327 71 (384+8*k) n = unpack (d >>> (90*k))
private theorem tE {x y:qKlO94b.Totals} (h:(x.r.beq y.r&&x.m.beq y.m&&x.e.beq y.e)=true) :x=y:= by
 simp only [Bool.and_eq_true] at h
 cases x; cases y; simp only [qKlO94b.Totals.mk.injEq]
 exact ⟨Nat.eq_of_beq_eq_true h.1.1,Nat.eq_of_beq_eq_true h.1.2,Nat.eq_of_beq_eq_true h.2⟩
set_option quotPrecheck false in
local notation "qk!"=>tE (by decide +kernel)
private theorem b0 : q! 0 8 :=qk!
private theorem b1 : q! 1 8 :=qk!
private theorem b2 : q! 2 8 :=qk!
private theorem b3 : q! 3 8 :=qk!
private theorem b4 : q! 4 8 :=qk!
private theorem b5 : q! 5 8 :=qk!
private theorem b6 : q! 6 8 :=qk!
private theorem b7 : q! 7 8 :=qk!
private theorem b8 : q! 8 8 :=qk!
private theorem b9 : q! 9 8 :=qk!
private theorem b10 : q! 10 5 :=qk!
theorem p4_5 : block 327 71 384 85 = sumPacked d 11 := join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (b10))))))))))
end qKlO94b
end
section
section
set_option autoImplicit true
namespace qjf96Pd
open P5_7_2 (fO Test jX row Lc A)
open agU (ad1 ajD)
open czX (a8x dei)
open jQ (cUo eE)
open aF8 (bi6 CH)
theorem bank_guards (b:fO) :
  0<(jX b).lo∧(jX b).hi≤131070 ∧
  (row b).shape.J≤(row b).shape.B∧(row b).shape.B<K1.p ∧
  0<(row b).shape.m*A ∧
  (row b).shape.B*(131071-(jX b).lo)≤(row b).shape.m*A:= by
 fin_cases b <;> decide
private theorem node_data (b:fO) :
  let s :=(row b).shape
  2*s.J≤ s.m∧s.m+s.J≤ s.B+1 ∧
    262144*a8x (s.m-2*s.J) s.J=6*(row b).ad1 := by
 fin_cases b <;> decide
theorem node_rank (b:fO) (u:ℕ) :
  ad1 { (row b).shape with U:=u } = (row b).ad1 := by
 obtain ⟨hm,hB,hn⟩:=node_data b
 have he :=dei { (row b).shape with U:=u } hm hB
 exact Nat.eq_of_mul_eq_mul_left (by decide :0<6) (he.trans hn)
private def widthOK :ℕ→ℕ→Bool
 | 0,n=>n == 0
 | k+1,n=>decide ((n &&& 0x3ffff)≤0xffff) && widthOK k (n >>> 18)
private theorem width_digit {k n:ℕ} (h:widthOK k n=true) (i:ℕ) :
   ((n >>> (18*i)) &&& 0x3ffff)≤0xffff := by
 induction k generalizing n i with
 | zero =>
   have hn:n=0:=beq_iff_eq.mp h
   simp [hn]
 | succ k ih =>
   obtain ⟨hfirst,hrest⟩:=Bool.and_eq_true_iff.mp h
   cases i with
   | zero =>
     simpa only [Nat.mul_zero,Nat.shiftRight_zero] using of_decide_eq_true hfirst
   | succ i =>
     rw [Nat.mul_succ,Nat.add_comm (18*i) 18,Nat.shiftRight_add]
     exact ih hrest i
private theorem width_check (b:fO) :widthOK 80 (row b).xF=true := by
 fin_cases b <;> rfl
private theorem width_room (b:fO) :
  (row b).shape.B+0xffff≤(row b).shape.U:= by
 fin_cases b <;> decide
theorem tested_width (b:fO) (x :Test b) :
   (row b).shape.B≤(Lc b x).shape.U:= by
 have hr :=width_room b
 cases x with
 | none =>
   change (row b).shape.B≤(row b).shape.U
   omega
 | some i =>
   have hd:=width_digit (width_check b) i.val
   change (row b).shape.B≤(row b).shape.U -
     (((row b).xF >>> (18*i.val)) &&& 0x3ffff)
   omega
theorem historical_degrees (b:fO) (hb:12≤b.val) :
  (row b).shape.B=3624∧(row b).shape.J=767:= by
 fin_cases b <;> first | decide | contradiction
private theorem append_checked {B J start:ℕ} {xs ys :List (ℕ×ℕ)}
   (hx :bi6 B J start xs)
   (hy :bi6 B J (start+(xs.map Prod.fst).sum) ys) :
   bi6 B J start (xs ++ ys) := by
 induction xs generalizing start with
 | nil=>exact hy
 | cons x xs ih =>
   obtain ⟨len,value⟩:=x
   refine ⟨hx.1,ih hx.2 ?_⟩
   simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using hy
set_option quotPrecheck false in
local notation "blocksOK!" =>
 (by
   repeat' apply And.intro
   all_goals first | exact True.intro | decide +kernel)
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
private def d0:List (ℕ×ℕ) :=
 [(128,0x4b3f6420),(128,0x1f7997420),(128,0x520c38420),
  (128,0x996bd9420),(128,0xf2987a420),(128,0x15a921b420),
  (128,0x1caaace000)]
private theorem r0:bi6 3624 767 767 d0:=blocksOK!
private def d1 :List (ℕ×ℕ) :=
 [(128,0x23284ce000),(128,0x28e5ece000),(128,0x2de38ce000),
  (128,0x32212ce000),(128,0x359ecce000),(128,0x385c6ce000),
  (128,0x3a5a0ce000)]
private theorem r1 :bi6 3624 767 1663 d1 :=blocksOK!
private def d2 :List (ℕ×ℕ) :=
 [(128,0x3b97ace000),(128,0x3c154ce000),(128,0x3bd2ece000),
  (128,0x3ad08ce000),(128,0x390e2ce000),(128,0x368bcce000),
  (128,0x33496ce000)]
private theorem r2 :bi6 3624 767 2559 d2 :=blocksOK!
private def d3:List (ℕ×ℕ) :=
 [(128,0x2f470ce000),(128,0x2a8bf38854),(128,0x256eb6abcb),
  (128,0x203c5ac72b),(128,0x1b162e432d),(128,0x161ad31f02),
  (128,0x1166eb5a4d)]
private theorem r3:bi6 3624 767 3455 d3:=blocksOK!
private def d4 :List (ℕ×ℕ) :=
 [(128,0xd11af43ea),(128,0x9333f1020),(128,0x5ee31d020),
  (128,0x3527b9020),(128,0x16f1c5020),(128,0x53141020),
  (39,0x1304f52)]
private theorem r4 :bi6 3624 767 4351 d4 :=blocksOK!
private theorem historical_moment:eE 3624 767=0x43b72bf6462 :=
 @CH 3624 767 0x43b72bf6462 (d0 ++ (d1 ++ (d2 ++ (d3 ++ d4))))
   (append_checked r0 (append_checked r1 (append_checked r2 (append_checked r3 r4)))) rfl rfl
theorem grouped_moment:ajD 3624 767≤0x43b72bf6462 :=
 (cUo 3624 767).trans historical_moment.le
end qjf96Pd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qjf96Pd
open P5 (I)
open P5_7 (Bank)
open P5_7_2 (fO Test jX row Lc poleRowsAt O2 j3 TerminalFloor A)
open cu (FX L ku triangle)
open DP (jF zG VY c69 ceG bga azS
 aq7 complete)
open agU (ad1 arY ajD telescope)
open P5_7_4 (LocalPole poleRank)
def c1 :Prop :=
  ∀ (b:fO),b.val<12 →
    ∀ (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ (D:jF h) (Crt:zG D) (word:I→L) (x :Test b),
      let s :=(Lc b x).shape
      let W:=O2 s
      Module.finrank L (aq7 h word s W) ≤
        2*h*poleRank s+Module.finrank L (complete Crt word s W)
def c2 :Prop :=
  ∀ (b:fO),b.val<12 → ∀ u:ℕ,(row b).shape.B≤u →
    let s := { (row b).shape with U:=u }
    poleRank s≤triangle u*arY s+poleRowsAt b u
private theorem tested_eq (b:fO) (x :Test b) :
  Lc b x=⟨{ (row b).shape with U:=(Lc b x).shape.U },(row b).ad1,
   poleRowsAt b (Lc b x).shape.U⟩:= by
 cases x <;> rfl
section
open private c4y from ProximityPrize.SubmissionLower.Zq1cNdd
theorem reciprocal_of_local (hlocal:LocalPole) :c1 := by
 intro b _ h hl hh D Crt word x
 let s :=(Lc b x).shape
 let W:=O2 s
 have hs :s = { (row b).shape with U:=s.U } := congrArg Bank.shape (tested_eq b x)
 obtain ⟨hlo,hhi,hJ,hB,_,_⟩:=bank_guards b
 have hpos :0<h:=hlo.trans_le hl
 have hchar :h<K1.p:=hh.trans_lt (hhi.trans_lt (by decide))
 have hJB:s.J≤ s.B:= by rw [hs]; exact hJ
 have hUB:s.B≤ s.U:= by rw [hs]; exact tested_width b x
 have hBp:s.B<K1.p:= by rw [hs]; exact hB
 exact c4y hlocal hpos hchar Crt word s hJB hUB hBp W
end
private theorem floor_of_poles {h:ℕ} {D:jF h} (Crt:zG D)
    (word:I→L) (t:Bank) (hh:h≤131070) (hm:0<t.shape.m*A)
    (hw:t.shape.B*(131071-h)≤t.shape.m*A) (hn:ad1 t.shape=t.ad1)
    (hp:Module.finrank L (aq7 h word t.shape (O2 t.shape)) ≤
      azS h t.shape+2*h*t.arY +
        Module.finrank L (complete Crt word t.shape (O2 t.shape))) :
    TerminalFloor h t (VY Crt word) := by
  let s :=t.shape
  let W:=O2 s
  have hW:W+1=s.m*A:=Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have hwidth :c69 h s W:= by
    intro q hq j _
    rw [hW]
    exact (Nat.mul_le_mul_right _ hq).trans (hw.trans (Nat.le_add_right _ _))
  have hamb:=atp.bT9 (hh.trans (by decide)) s W hwidth
  have hcon :=atp.Yw h word s W
  have hsum:=telescope hh Crt word s W
  have hphys :bga s=triangle s.U*t.ad1 := by
    rw [← hn]
    unfold bga ad1
    rw [Nat.mul_assoc]
  rw [hphys] at hcon
  change Module.finrank L (aq7 h word s W)≤azS h s+2*h*t.arY +
    Module.finrank L (complete Crt word s W) at hp
  unfold TerminalFloor j3
  change triangle s.U*ku s (fun q j=>s.m*A+j-q*(131071-h)) ≤
    triangle s.U*t.ad1+2*h*t.arY +
      ∑ w∈Finset.range (s.m*A),Module.finrank FX (VY Crt word s w)
  rw [← hW]
  change ceG h s W≤_
  omega
open private c4y from ProximityPrize.SubmissionLower.ZdZNCPb
theorem of_children (h1 :c1) (h2 :c2) :P5_7_2.c1 := by
 intro b h hl hh D _ Crt word x
 let u:=(Lc b x).shape.U
 let s := { (row b).shape with U:=u }
 let t:Bank :=⟨s,(row b).ad1,poleRowsAt b u⟩
 rw [show Lc b x=t from tested_eq b x]
 obtain ⟨hlo,hhi,_,hB,hm,hwidth⟩:=bank_guards b
 have hpos :0<h:=hlo.trans_le hl
 have hraw:h≤131070:=hh.trans hhi
 have hchar :h<K1.p:=hraw.trans_lt (by decide)
 have hU:s.B≤u:=tested_width b x
 have hw:s.B*(131071-h)≤ s.m*A :=
   (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
 apply floor_of_poles Crt word t hraw hm hw (node_rank b u)
 let W:=O2 s
 change Module.finrank L (aq7 h word s W)≤azS h s+2*h*poleRowsAt b u +
   Module.finrank L (complete Crt word s W)
 by_cases hb:b.val<12
 · have hp:=h1 b hb h hl hh D Crt word x
   dsimp only at hp
   rw [show Lc b x=t from tested_eq b x] at hp
   change Module.finrank L (aq7 h word s W) ≤
     2*h*poleRank s+Module.finrank L (complete Crt word s W) at hp
   have hcap:poleRank s≤triangle u*arY s+poleRowsAt b u:=h2 b hb u hU
   have hc:=Nat.mul_le_mul_left (2*h) hcap
   have hcredit :2*h*(triangle u*arY s)=azS h s := by
     unfold arY azS
     change 2*h*(triangle s.U*_)= _
     ac_rfl
   rw [Nat.mul_add,hcredit] at hc
   omega
 · have hg:12≤b.val :=Nat.le_of_not_lt hb
   obtain ⟨hgrade,hderiv⟩:=historical_degrees b hg
   have hlocal:agU.c1 :=
     aeL.of_children czW.proof aSk.proof
   have hp:=c4y hlocal hpos hchar Crt word s hB W
   have hbound:ajD s.B s.J≤0x43b72bf6462 := by
     change ajD (row b).shape.B (row b).shape.J≤_
     rw [hgrade,hderiv]
     exact grouped_moment
   have he : (u+1)*0x43b72bf6462=poleRowsAt b u:= by
     simp only [poleRowsAt,ite_eq_left hg]
   have hcap: (s.U+1)*ajD s.B s.J≤poleRowsAt b u:= by
     rw [← he]
     exact Nat.mul_le_mul_left _ hbound
   have hc' := Nat.mul_le_mul_left (2*h) hcap
   rw [← Nat.mul_assoc] at hc'
   omega
end qjf96Pd
end
end
