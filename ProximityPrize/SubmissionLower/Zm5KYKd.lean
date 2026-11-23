import ProximityPrize.SubmissionLower.D6
import ProximityPrize.SubmissionLower.ZTzAWec
import ProximityPrize.SubmissionLower.Zx0Npsd
import ProximityPrize.SubmissionLower.ZEXyWMe
import ProximityPrize.SubmissionLower.ZTOdMMe
set_option Elab.async false
section
set_option autoImplicit true
namespace P5_7_3
noncomputable section
open P5 (p)


open cu (Shape vP Jet FX triangle ku A5)
open gT (alm)

open Polynomial Finset


open private eligible boi bDM from ProximityPrize.SubmissionLower.D6
private theorem ee7 (h r :ℕ) (s :Shape) :
  O3 h r s 1≤O3 h r s 0:= by
 unfold O3 ku
 simp only [zero_mul,Nat.sub_zero]
 exact Nat.mul_le_mul_left _ (sum_le_sum fun _ _=>sum_le_sum fun _ _=>Nat.sub_le _ _)
private theorem eHt (h N W:ℕ) (hh:0<h) (hW:W<N)
   {G P R:Jet} (hi:Irreducible G) (hv :0<G.natDegree)
   (hm:alm G) (hP:P≠0) (hdiv :G∣P) {U:ℕ} (hp:U<p)
   (hseed : ∀ j i,((P.coeff j).coeff i).totalDegree≤U) (hnR:R≠0)
   (commonShift : ∀ (i:Fin 2) a,W+2*h*a≤N-1→G∣A5 i a R) :
   N≤W+2*h*R.natDegree := by
 let e :=1+(N - 1-W)/(2*h)
 have hpower :G^e∣R :=
   bjF.proof G P R U e hi hv hm hP hdiv hp hseed (by
     intro i a ha
     have hle :a≤(N - 1-W)/(2*h) := by dsimp [e] at ha; omega
     have ht:=(Nat.le_div_iff_mul_le (by omega :0<2*h)).mp hle
     rw [Nat.mul_comm a] at ht
     exact commonShift i a (by omega))
 have hdegree :=Polynomial.natDegree_le_of_dvd hpower hnR
 rw [Polynomial.natDegree_pow] at hdegree
 have he :e≤R.natDegree :=(Nat.le_mul_of_pos_right e hv).trans hdegree
 have hdiv' : (N - 1-W)/(2*h)<R.natDegree := by dsimp [e] at he; omega
 have ht:=(Nat.div_lt_iff_lt_mul (by omega :0<2*h)).mp hdiv'
 rw [Nat.mul_comm R.natDegree] at ht
 omega
private theorem eD6 (rows :vP) (s :Shape) (h r :ℕ)
    (hk :1≤131071-h)
    (hcaps : ∀ W,∀ P∈rows s W,qQ.oU P s)
    (hlead:qQ.aSa h rows s)
    (horder : ∀ W<Mq h r s,∀ P∈rows s W,P≠0 →
      Mq h r s≤W+2*h*P.natDegree) :
    (∑ W∈range (Mq h r s),Module.finrank FX (rows s W))+O3 h r s 1 ≤
      O3 h r s 0:= by
  let N :=Mq h r s
  have hsum: (∑ W∈range N,Module.finrank FX (rows s W)) ≤
      triangle s.U*(∑ W∈range N,ku s (fun q j =>
        if eligible h N W q j then 1 else 0)) := by
    rw [mul_sum]
    exact sum_le_sum (fun W hW =>
      boi s h N W _ (hcaps W) (hlead W) (horder W (mem_range.mp hW)))
  have heq :=congrArg (triangle s.U * ·) (bDM s h N hk)
  rw [Nat.mul_add] at heq
  unfold O3 amv
  simp only [one_mul,zero_mul,Nat.sub_zero]
  exact (Nat.add_le_add_right hsum _).trans_eq heq
end
end P5_7_3
end
section
set_option autoImplicit true
namespace P5_7_3
noncomputable section
open Polynomial
open P5 (p)

open Dt (Bank)
open agU (ad1 ajD)


def c1 :Prop :=
  ∀ (b:fO) (t:Bank),Jr b t →
    ad1 t.shape=t.ad1 ∧
    ajD t.shape.B t.shape.J≤t.poleMoment∧t.shape.B<p
def c2 :Prop :=
  ∀ (b:fO) h,b.jX.lo≤h→h≤b.jX.hi → ∀ s∈stages b,
    aL4 h s.dI s.free.shape ∧
    j3 h s.free<O3 h s.dI s.free.shape 0∧s.free.shape.U<p ∧
    aL4 h s.dI s.moving.shape ∧
    j3 h s.moving<O3 h s.dI s.moving.shape 1
def c4 :Prop :=
  ∀ (b:fO) h,b.jX.lo≤h→h≤b.jX.hi → ∀ x :Test b,
    j3 h (Lc b x)<ZN h (Lc b x).shape (threshold b x) (apo b x)
end
end P5_7_3
end
section
set_option autoImplicit true
namespace qqf9uAa
open Finset
open cu (Shape)
open Dt (Bank jJ)
open P5_7_3 (j3)
open bjU (af scan)
open private dcl coM from ProximityPrize.SubmissionLower.B4
theorem GradeSigns.get {t:Bank} {h e :ℕ} {gs :List jJ}
   (hc:GradeSigns t h e gs) (i:Fin gs.length) :
   Signs {t with shape := {t.shape with U:=(gs.get i).slots}} h (i.val+e) ((gs.get i).seedCap+1) := by
 induction gs generalizing e with
 | nil=>exact Fin.elim0 i
 | cons g gs ih =>
   rcases i with ⟨_ | j,hj⟩
   · change Signs {t with shape := {t.shape with U:=g.slots}} h (0+e) (g.seedCap+1)
     simpa only [Nat.zero_add] using hc.1
   · have hz :=ih hc.2 ⟨j,by simpa using hj⟩
     simpa only [List.get_cons_succ,Nat.succ_add,Nat.add_succ] using hz
theorem GradeSigns.append {t:Bank} {h e :ℕ} {xs ys :List jJ}
   (hx :GradeSigns t h e xs) (hy :GradeSigns t h (e+xs.length) ys) :
   GradeSigns t h e (xs++ys) := by
 induction xs generalizing e with
 | nil=>exact hy
 | cons g gs ih =>
   refine ⟨hx.1,ih hx.2 ?_⟩
   have he :e+1+gs.length=e+(g :: gs).length:= by
     simp only [List.length_cons]
     omega
   rw [he]
   exact hy
private def run (s :Shape) (h E v i:ℕ) :af :=
 ⟨true,IK s h h E v i,IK s h ((h:ℤ)+1) E v i⟩
private def signed (x :ℕ) :ℤ:=if x % 2=0 then (x/2 :ℕ) else -((x/2+1 :ℕ) :ℤ)
private def lower (bits x :ℕ) :ℤ:=signed (x % 2^bits)
private def step (b d x :ℕ) :ℤ:=lower d (x >>> b)
private def len (last remaining:ℕ) :ℕ:=if remaining=0 then last else 12
private def chunk (f :ℕ→af) (k l b d n a x :ℕ) :Bool :=
 let z :=scan f a n
 decide ((2^k :ℤ)*lower b x≤z.base) && decide ((2^l:ℤ)*step b d x≤z.slope - z.base)
private def valid (f :ℕ→af) (k l b d last :ℕ) :ℕ→ℕ→ℕ→Prop
 | _,0,_=>True
 | a,n+1,x=>chunk f k l b d (len last n) a x=true ∧
     valid f k l b d last (a+len last n) n (x >>> (b+d))
private def Ca (b d last :ℕ) :ℕ→ℕ→ℕ×ℤ×ℤ
 | 0,_=>(0,0,0)
 | n+1,x =>
   let (count,lo,slope) :=Ca b d last n (x >>> (b+d))
   (len last n+count,lower b x+lo,step b d x+slope)
private theorem bounds_valid (f :ℕ→af) (k l b d last a n x :ℕ)
   (ok :valid f k l b d last a n x) :
   let (c,y,z) :=Ca b d last n x
   (2^k :ℤ)*y≤(scan f a c).base∧(2^l:ℤ)*z≤(scan f a c).slope-(scan f a c).base := by
 induction n generalizing a x with
 | zero=>simp [Ca,scan]
 | succ n ih =>
   obtain ⟨ha,hn⟩:=ok
   simp only [chunk,Bool.and_eq_true,decide_eq_true_eq] at ha
   have h:=ih (a+len last n) (x >>> (b+d)) hn
   rcases hj:Ca b d last n (x >>> (b+d)) with ⟨c,y,z⟩
   simp only [hj] at h
   simp only [Ca,hj,dcl,af.add,mul_add]
   omega
theorem book (t:Bank) (h E v k l b d last n x :ℕ)
   (ok :valid (run t.shape h E v) k l b d last 0 n x)
   (he :decide (0<E)=true)
   (hc:decide ((Ca b d last n x).1≤t.shape.B+1)=true)
   (hb:boundary t.shape h (stop t.shape E v) (Ca b d last n x).1=stop t.shape E v)
   (hp:decide (1440*(j3 h t:ℤ)<(2^k :ℤ)*(Ca b d last n x).2.1)=true)
   (hs :decide (2880*((t.shape.U:ℤ)+1)*t.poleMoment≤(2^l:ℤ)*(Ca b d last n x).2.2)=true) :
   Signs t h E v := by
 rcases hj:Ca b d last n x with ⟨c,y,z⟩
 have hv :=bounds_valid _ _ _ _ _ _ _ _ _ ok
 simp only [hj] at hc hb hp hs hv
 have ha :=coM (run t.shape h E v) 0 c false
 have hd:=coM (run t.shape h E v) 0 c true
 simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add,run] at ha hd
 rw [dbW _ _ _ _ _ _ (of_decide_eq_true he) (of_decide_eq_true hc) hb] at ha hd
 rw [ha,hd] at hv
 have hp' := of_decide_eq_true hp
 have hs' := of_decide_eq_true hs
 unfold Signs
 dsimp only
 constructor
 · omega
 · have hen:2880*((t.shape.U:ℤ)+1)*t.poleMoment =
         1440*(2*((t.shape.U:ℤ)+1)*t.poleMoment) := by ring
   rw [hen] at hs'
   omega
set_option quotPrecheck false in
scoped notation "pack!" t:arg h:arg E:arg v:arg k:arg l:arg b:arg d:arg last:arg n:arg x:arg =>
 book t h E v k l b d last n x (by
  repeat' apply And.intro
  all_goals first | exact True.intro | rfl) rfl rfl rfl rfl rfl
end qqf9uAa
end
