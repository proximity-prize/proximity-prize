import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.Z6Xnfpd
set_option Elab.async false
private theorem bothR {p q:Bool} {C:Prop} (h:(p && q)=true) (f:p=true → q=true → C) :C:= by
 simp only [Bool.and_eq_true] at h; exact f h.1 h.2
section
set_option autoImplicit true
namespace P1_7_6_7
open Finset Y2
structure aT where
 offset :ℤ
 slope :ℤ
def aT.eval (p:aT) (a :ℕ) :ℤ:=p.offset+p.slope*a
def aT.add (p q:aT) :aT:=⟨p.offset+q.offset,p.slope+q.slope⟩
def aT.sub (p q:aT) :aT:=⟨p.offset-q.offset,p.slope-q.slope⟩
def aT.scale (k :ℤ) (p:aT) :aT:=⟨k*p.offset,k*p.slope⟩
def aT.shift (p:aT) (k :ℤ) :aT:=⟨p.offset+k,p.slope⟩
def aT.prod (p q:aT) :PG:=PG.bfR p.offset p.slope q.offset q.slope
private theorem aT.eval_add (p q:aT) (i:ℕ) : (p.add q).eval i=p.eval i+q.eval i:= by
 simp only [aT.add,aT.eval]
 ring
private theorem aT.eval_sub (p q:aT) (i:ℕ) : (p.sub q).eval i=p.eval i - q.eval i:= by
 simp only [aT.sub,aT.eval]
 ring
private theorem aT.aNz (k :ℤ) (p:aT) (i:ℕ) : (p.scale k).eval i=k*p.eval i:= by
 simp only [aT.scale,aT.eval]
 ring
private theorem aT.cNb (p:aT) (k :ℤ) (i:ℕ) : (p.shift k).eval i=p.eval i+k := by
 simp only [aT.shift,aT.eval]
 ring
private theorem aT.eval_prod (p q:aT) (i:ℕ) : (p.prod q).eval i=p.eval i*q.eval i:= by
 simp only [aT.prod,PG.b13,aT.eval]
private def fifthPrefix (p q:PG) (l:aT) (n:ℕ) :ℤ :=
 let x :ℤ:=n
 let t:=x*(x-1)
 let u:=t*(2*x-1)
 l.offset*bgk p q n+l.slope *
  (30*t*(p.constant*q.constant) +
   10*u*(p.constant*q.linear+p.linear*q.constant) +
   15*t*t*(p.constant*q.square+p.linear*q.linear+p.square*q.constant) +
   2*u*(3*t-1)*(p.linear*q.square+p.square*q.linear) +
   5*t*t*(2*t-1)*(p.square*q.square))
private theorem fifthPrefix_eq (p q:PG) (l:aT) (n:ℕ) :
   60*(∑ a∈range n,p.eval a*q.eval a*l.eval a)=fifthPrefix p q l n:= by
 induction n with
 | zero=>simp [fifthPrefix,bgk]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   simp only [fifthPrefix,bgk,PG.eval,aT.eval,Nat.cast_succ]
   ring
private def fifthInterval (p q:PG) (l:aT) (a b:ℕ) :ℤ :=
 fifthPrefix p q l b - fifthPrefix p q l a
private theorem fifthInterval_eq (p q:PG) (l:aT) {a b:ℕ} (hab:a≤b) :
  60*(∑ i∈Ico a b,p.eval i*q.eval i*l.eval i)=fifthInterval p q l a b:= by
 rw [fifthInterval,sum_Ico_eq_sub _ hab,mul_sub,fifthPrefix_eq,fifthPrefix_eq]
private theorem sum_affine_product (x y z w:ℤ) (n:ℕ) :
   6*(∑ i∈range n,(x+y*i)*(z+w*i)) =
     (n:ℤ)*(6*x*z+3*((n:ℤ)-1)*(x*w+y*z)+((n:ℤ)-1)*(2*(n:ℤ)-1)*y*w) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih]
   simp only [Nat.cast_succ]
   ring
private theorem sum_affine_interval (x y z w:ℤ) {l r :ℕ} (hlr :l≤ r) :
   6*(∑ t∈Ico l r,(x+y*t)*(z+w*t)) =
     let n:ℤ:=(r :ℤ)-l
     let x' := x+y*l
     let z' := z+w*l
     n*(6*x'*z'+3*(n-1)*(x'*w+y*z')+(n-1)*(2*n-1)*y*w) := by
 rw [sum_Ico_eq_sum_range]
 have shift (i:ℕ) : (x+y*(↑(l+i) :ℤ))*(z+w*(↑(l+i) :ℤ)) =
     (x+y*l+y*i)*(z+w*l+w*i) := by
   push_cast
   ring
 simp_rw [shift]
 rw [sum_affine_product,Nat.cast_sub hlr]
def stripe (p:PG) (x z :aT) (y w:ℤ) (lo hi:aT) (a b:ℕ) :ℤ :=
  let n:=hi.sub lo
  let x' := x.add (lo.scale y)
  let z' := z.add (lo.scale w)
  let nm:=n.shift (-1)
  6*fifthInterval p (x'.prod z') n a b +
    3*fifthInterval p (nm.prod ((x'.scale w).add (z'.scale y))) n a b +
    y*w*fifthInterval p (nm.prod ((n.scale 2).shift (-1))) n a b
theorem stripe_eq (p:PG) (x z :aT) (y w:ℤ) (lo hi:aT) {a b:ℕ}
    (hab:a≤b) (hlo : ∀ i∈Ico a b,0≤lo.eval i)
    (hhi : ∀ i∈Ico a b,lo.eval i≤hi.eval i) :
    stripe p x z y w lo hi a b =
      360*(∑ i∈Ico a b,p.eval i *
        ∑ t∈Ico (lo.eval i).toNat (hi.eval i).toNat,
          (x.eval i+y*t)*(z.eval i+w*t)) := by
  unfold stripe
  conv_lhs=>simp only [← fifthInterval_eq _ _ _ hab,mul_sum,← sum_add_distrib]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi'
  have hl:=hlo i hi'
  have hr :=hl.trans (hhi i hi')
  have h₀:360*(p.eval i * ∑ t∈Ico (lo.eval i).toNat (hi.eval i).toNat,
      (x.eval i+y*t)*(z.eval i+w*t)) =
      60*p.eval i*(6*∑ t∈Ico (lo.eval i).toNat (hi.eval i).toNat,
        (x.eval i+y*t)*(z.eval i+w*t)) := by ring
  rw [h₀,sum_affine_interval _ _ _ _ (Int.toNat_le_toNat (hhi i hi'))]
  simp only [Int.toNat_of_nonneg hl,Int.toNat_of_nonneg hr,aT.eval_prod,
    aT.eval_add,aT.eval_sub,aT.aNz,aT.cNb]
  ring
end P1_7_6_7
end
section
set_option autoImplicit true
namespace qPTjEYd
open Finset
open cu (Shape slots)
open Y2 (aJq)
open P1_7_6_7 (aT stripe stripe_eq)
open P5 (dw)
open P5_7_1 (j3)
open private sum_arithmetic from ProximityPrize.SubmissionLower.ZnaMqIa
open private co2 from ProximityPrize.SubmissionLower.D9


private def column (s :Shape) (E d:ℕ) :aT :=
 ⟨(s.B:ℤ)+1-(E :ℤ)*d,-(E :ℤ)⟩
private def twiceWidth (s :Shape) (h:ℤ) (E d:ℕ) :aT :=
 ⟨2*(s.m*dw:ℕ)-(131071-h)*((s.B:ℤ)+(E :ℤ)*d),
   -(131071-h)*E-4*h⟩
private def rate (h:ℤ) :ℤ:=2-4*h-(131071-h)
private theorem sum_columns (s :Shape) (h:ℤ) (E d a j:ℕ)
    (hj:j< min (s.J+1) (s.B+1-E*(a+d))) :
    2*(∑ q∈Ico (j+E*(a+d)) (s.B+1),width s h q j a) =
      ((column s E d).eval a+(-1 :ℤ)*j) *
        ((twiceWidth s h E d).eval a+rate h*j) := by
  have hj' := (lt_min_iff.mp hj).2
  have hl:j+E*(a+d)≤ s.B+1 := by omega
  rw [sum_Ico_eq_sum_range,mul_sum]
  have shift (i:ℕ) :
      2*width s h (j+E*(a+d)+i) j a =
        2*width s h (j+E*(a+d)) j a - 2*(131071-h)*(i:ℤ) := by
    simp only [width,Nat.cast_add]
    ring
  simp_rw [shift]
  rw [sum_arithmetic,Nat.cast_sub hl]
  simp only [column,twiceWidth,rate,width,aT.eval,Nat.cast_add,Nat.cast_mul,
    Nat.cast_one]
  ring
private def splitAt (s :Shape) (E v d:ℕ) :ℕ :=
 min (powerCount s E v d) ((s.B-s.J)/E+1-d)
private def a3T (s :Shape) (h:ℤ) (E v d:ℕ) :ℤ :=
 let p:=aJq s v d
 let x :=column s E d
 let z :=twiceWidth s h E d
 let k :=splitAt s E v d
 stripe p x z (-1) (rate h) ⟨0,0⟩ ⟨(s.J:ℤ)+1,0⟩ 0 k +
  stripe p x z (-1) (rate h) ⟨0,0⟩ x k (powerCount s E v d)
private theorem cRJ (s :Shape) (h:ℤ) (E v d:ℕ)
    (he :0<E) (hJ:s.J≤ s.B) :a3T s h E v d = 1440*phase s h E v d:= by
  let n:=powerCount s E v d
  let k :=splitAt s E v d
  have hk :k≤n:=min_le_left _ _
  have budget (a :ℕ) (ha :a<n) :E*(a+d)≤ s.B:= by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le he).1 ((lt_powerCount s E v d a).1 ha).1
  have hcut (a :ℕ) (ha :a<n) :a<k↔s.J+1≤ s.B+1-E*(a+d) := by
    have hb:=budget a ha
    have hd:a+d≤(s.B-s.J)/E↔E*(a+d)≤ s.B-s.J:= by
      rw [Nat.le_div_iff_mul_le he,Nat.mul_comm (a+d) E]
    change a< min n ((s.B-s.J)/E+1-d)↔_
    rw [lt_min_iff,and_iff_right ha]
    omega
  let F:= fun a=>(slots s.U ((a+d)*v) :ℤ) *
    ∑ j∈range (min (s.J+1) (s.B+1-E*(a+d))),
      ∑ q∈Ico (j+E*(a+d)) (s.B+1),width s h q j a
  have book (win:aT) {l r :ℕ} (hlr :l≤ r) (hr :r≤n)
      (hw : ∀ a∈Ico l r,win.eval a = ↑(min (s.J+1) (s.B+1-E*(a+d)) :ℕ)) :
      stripe (aJq s v d) (column s E d) (twiceWidth s h E d) (-1)
        (rate h) ⟨0,0⟩ win l r=1440*(∑ a∈Ico l r,F a) := by
    rw [stripe_eq _ _ _ _ _ _ _ hlr (by simp [aT.eval])
      (fun a ha=> by
        rw [hw a ha]
        simpa only [aT.eval,zero_mul,add_zero] using Int.natCast_nonneg
          (min (s.J+1) (s.B+1-E*(a+d))))]
    rw [mul_sum,mul_sum]
    apply sum_congr rfl
    intro a ha
    have han:=(mem_Ico.mp ha).2.trans_le hr
    rw [hw a ha,Int.toNat_natCast,co2 _ _ _ _ ((lt_powerCount s E v d a).1 han).2]
    have hz : ((⟨0,0⟩:aT).eval a).toNat=0:= by simp [aT.eval]
    rw [hz,Nat.Ico_zero_eq_range]
    let M:=min (s.J+1) (s.B+1-E*(a+d))
    have hs : (∑ j∈range M,((column s E d).eval a+(-1 :ℤ)*j) *
        ((twiceWidth s h E d).eval a+rate h*j)) =
        2*(∑ j∈range M,∑ q∈Ico (j+E*(a+d)) (s.B+1),width s h q j a) := by
      rw [mul_sum]
      exact sum_congr rfl fun j hj=>(sum_columns s h E d a j (mem_range.mp hj)).symm
    rw [hs]
    unfold F
    ring
  have left (a :ℕ) (ha :a∈Ico 0 k) :
      aT.eval ⟨(s.J:ℤ)+1,0⟩ a = ↑(min (s.J+1) (s.B+1-E*(a+d)) :ℕ) := by
    have ha' := (mem_Ico.mp ha).2
    simp [aT.eval,min_eq_left ((hcut a (ha'.trans_le hk)).1 ha')]
  have right (a :ℕ) (ha :a∈Ico k n) :
      (column s E d).eval a = ↑(min (s.J+1) (s.B+1-E*(a+d)) :ℕ) := by
    obtain ⟨ha₁,ha₂⟩:=mem_Ico.mp ha
    have hmin:=le_of_not_ge (mt (hcut a ha₂).2 (Nat.not_lt_of_ge ha₁))
    rw [min_eq_right hmin,Nat.cast_sub (by have :=budget a ha₂; omega)]
    simp only [column,aT.eval,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    ring
  change stripe _ _ _ _ _ _ _ 0 k+stripe _ _ _ _ _ _ _ k n= _
  rw [book _ (Nat.zero_le _) hk left,book _ hk le_rfl right,
    Nat.Ico_zero_eq_range,← mul_add,sum_range_add_sum_Ico _ hk]
  rfl
private def margin (s :Shape) (h E v :ℕ) :ℤ :=
 a3T s h E v 0-a3T s h E v 1 - 1440*(j3 h s :ℤ)
private theorem margin_eq (s :Shape) (h E v :ℕ) (he :0<E) (hJ:s.J≤ s.B) :
  margin s h E v=1440*(phase s h E v 0 - phase s h E v 1-(j3 h s :ℤ)) := by
 unfold margin
 rw [cRJ s _ E v 0 he hJ,cRJ s _ E v 1 he hJ]
 ring
private theorem debit_line (s :Shape) (x y :ℕ) :
    (j3 x s :ℤ)=(j3 y s :ℤ)+((x :ℤ)-y)*((j3 1 s :ℤ)-(j3 0 s :ℤ)) := by
  have sW (b c:ℕ) :
      (↑(b+2*x*c) :ℤ) =
        ↑(b+2*y*c)+((x :ℤ)-y)*((↑(b+2*1*c) :ℤ)-↑(b+2*0*c)) := by
    push_cast
    ring
  exact sW _ _
private theorem phase_line (s :Shape) (x y :ℤ) (E v d:ℕ) :
  phase s x E v d=phase s y E v d+(x-y)*(phase s 1 E v d - phase s 0 E v d) := by
 have hx :=phase_affine s x E v d
 have hy :=phase_affine s y E v d
 linarith only [hx,hy]
private def marginSlope (s :Shape) (E v :ℕ) :ℤ :=
 1440*((phase s 1 E v 0 - phase s 0 E v 0) -
  (phase s 1 E v 1 - phase s 0 E v 1)-((j3 1 s :ℤ)-(j3 0 s :ℤ)))
private theorem margin_line (s :Shape) (x y E v :ℕ) (he :0<E) (hJ:s.J≤ s.B) :
  margin s x E v=margin s y E v+((x :ℤ)-y)*marginSlope s E v := by
 rw [margin_eq s x E v he hJ,margin_eq s y E v he hJ,marginSlope,
  phase_line s (x :ℤ) (y :ℤ) E v 0,phase_line s (x :ℤ) (y :ℤ) E v 1,debit_line s x y]
 ring
end qPTjEYd
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt appendGrades)
private theorem vQa0 :GG b2 64 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa1 :GG b2 65 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa2 :GG b2 66 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa3 :GG b2 67 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa4 :GG b2 68 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa5 :GG b2 69 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa6 :GG b2 70 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa7 :GG b2 71 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem r1 :GG b2 64 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQa0 vQa1) vQa2) vQa3) vQa4) vQa5) vQa6) vQa7
private theorem vQa8 :GG b2 72 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa9 :GG b2 73 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa10 :GG b2 74 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa11 :GG b2 75 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa12 :GG b2 76 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa13 :GG b2 77 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa14 :GG b2 78 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQa15 :GG b2 79 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem r2 :GG b2 72 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQa8 vQa9) vQa10) vQa11) vQa12) vQa13) vQa14) vQa15
theorem p2_4 :GG b2 64 16:=appendGrades r1 r2
end qd4jtSc
end
