import ProximityPrize.SubmissionLower.ZMoN2Pa
import ProximityPrize.SubmissionLower.Z9vlvqb
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
namespace qOhGD4a
open aR (Shape aO ceilDiv)
open oR (amU Wc)
open P6_6 (LN lowerTaylor bf mV)

open private cEr from ProximityPrize.SubmissionLower.E6
open private enough_round from ProximityPrize.SubmissionLower.ZMoN2Pa
private abbrev M:=bf
private abbrev g:=mV
private abbrev m:=P6.t
def linear (s a :Shape) :ℕ:=s.b*a.b+s.j*a.j
theorem linear_add (s q a :Shape) :linear (s.plus q) a=linear s a+linear q a := by
  simp only [linear,aR.Shape.plus]
  ring
theorem linear_scale (s a :Shape) (k :ℕ) :linear (s.scale k) a=k*linear s a := by
  simp only [linear,aR.Shape.scale]
  ring
def body (r :Shape) :Shape :=⟨max r.b (r.j+3),r.j,r.j/2⟩
theorem body_mono {r R:Shape} (h:aO r R) :aO (body r) (body R) :=
  ⟨max_le_max h.1 (Nat.add_le_add_right h.2.1 _),h.2.1,Nat.div_le_div_right h.2.1⟩
def graph (a :Shape) :Shape :=⟨a.b,a.j+1,min (a.t+1) ((a.j+1)/2)⟩
theorem adM {a A:Shape} (h:aO a A) :aO (graph a) (graph A) := by
  obtain ⟨hb,hj,ht⟩:=h
  refine ⟨hb,?_,?_⟩ <;> dsimp [graph] <;> gcongr
theorem lift_mono (L:ℕ) {a A:Shape} (h:aO a A) :
    aO (LN L a) (LN L A) := by
  obtain ⟨hb,hj,ht⟩:=h
  refine ⟨?_,?_,?_⟩ <;> dsimp [Ds.LN] <;> gcongr
theorem taylor_mono {a A:Shape} (h:aO a A) :
    aO (lowerTaylor a) (lowerTaylor A) := by
  obtain ⟨hb,hj,ht⟩:=h
  refine ⟨?_,?_,?_⟩ <;> dsimp [lowerTaylor] <;> gcongr
def mixedSlope (q s :Shape) :Shape :=
  ⟨q.t*s.j+s.t*q.j,q.t*s.b+s.t*q.b+q.j*s.b+s.j*q.b,0⟩
private theorem term_le {a q s A Q S:Shape} (ha :aO a A) (hq:aO q Q)
    (hs :aO s S) :amU a q s≤2*(A.t*Q.j*S.b) := by
  calc
    _≤A.t*Q.j*(2*S.b) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha.2.2 ((Nat.sub_le _ _).trans hq.2.1))
        ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hs.1))
    _ = _:= by ring
theorem mixed_le {a q s Q S:Shape} (ha :a.t≤a.j) (hq:aO q Q)
    (hs :aO s S) :Wc a q s≤linear (mixedSlope Q S) a := by
  let a' : Shape :=⟨a.b,a.j,a.j⟩
  have h:aO a a' := ⟨le_rfl,le_rfl,ha⟩
  unfold Wc
  apply Nat.div_le_of_le_mul
  refine (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (term_le h hq hs)
      (term_le h hs hq)) (term_le hq h hs)) (term_le hq hs h)) (term_le hs h hq))
    (term_le hs hq h)).trans ?_
  apply le_of_eq
  dsimp [a',linear,mixedSlope]
  ring
def width (b:ℕ) :ℕ:=1+(2*M - 5)*(b - 1)
theorem width_mono {a b:ℕ} (h:a≤b) :width a≤width b :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h _)) _
theorem weighted_le {b j c a d:ℕ} (hb:b≤ c) (hj:j≤ c) (hd:d≤a) :
    b*d+j*(a - d)≤ c*a := by
  calc
    _≤ c*d+c*(a - d) :=Nat.add_le_add (Nat.mul_le_mul_right _ hb) (Nat.mul_le_mul_right _ hj)
    _ = _:= by rw [← Nat.mul_add,Nat.add_comm d,Nat.sub_add_cancel hd]
theorem round_le {n c b:ℕ} (h:n≤ c*b) :ceilDiv n g≤ ceilDiv c g*b:= by
  apply cEr
  rw [← Nat.mul_assoc]
  exact h.trans (Nat.mul_le_mul_right _ (enough_round c g (by decide)))
theorem taylor_round (n:ℕ) :ceilDiv (m*n) g≤2*n:= by
  apply cEr
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (by decide)
end qOhGD4a
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace qcZ3orc
open P6_6 P6_6_8 q2w4Sxc
local notation "p!" l "," w "," h =>
  Certificate.prune (order (r :=l) (k :=43) (ws :=w) h rfl (by decide))
private theorem r1 :C ⟨12,39,1⟩ ⟨133,56,16⟩ :=
  p! ⟨12,39,1⟩,[([43,3],0x129c29ff48de),([3,3],0x18cc8b3b5df),([3,4],0x110c1f1984b),([4,5],0x9de4c49cb3),([6,11],0x38fd7f7296)],⟨rfl,rfl,rfl,rfl,rfl,trivial⟩
theorem D:C ⟨1,39,1⟩ ⟨133,56,16⟩ :=
  Certificate.trim (r1)
end qcZ3orc
end
