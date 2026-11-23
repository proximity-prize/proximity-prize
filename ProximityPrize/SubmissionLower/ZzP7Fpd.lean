import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.Zm5KYKd
set_option Elab.async false
section
set_option autoImplicit true
namespace q4WM8sb
open Finset
open P5 (p)
open P5_7 (midAgreement)
open P5_7_3
open Dt (Bank Ls)
open cu (Shape ku triangle)
open private bid from ProximityPrize.SubmissionLower.CN
open private row aJm level df7 df3 bhM dgC cck from ProximityPrize.SubmissionLower.E7
private theorem cA5: (midAgreement:ℤ)=179740:=rfl
private def cut (s :Shape) (r lo mode :ℕ) :ℕ :=
 min (s.B+1) ((Mq lo r s - 1-(2*mode*lo-1)*s.J)/(131071-lo)+1)
private def csU (s :Shape) (r lo mode q:ℕ) :ℕ :=
 min (min q s.J+1) ((amv lo r s q 0 - 1)/(2*mode*lo-1)+1)
private def support (s :Shape) (r lo mode q:ℕ) :ℕ :=
 if q<cut s r lo mode then min q s.J+1 else csU s r lo mode q
private def total (s :Shape) (r lo mode :ℕ) (x y z :ℤ) :ℤ :=
 let k :=cut s r lo mode
 aJm x y z s.J+level x y z s.J (k-s.J) +
  6*bhM (fun q=>row x y z q (csU s r lo mode q)) k (s.B+1-k)
private theorem asB (s :Shape) (r lo mode :ℕ) (x y z :ℤ)
   (hj:s.J≤ cut s r lo mode) :
   total s r lo mode x y z=6*(∑ q∈range (s.B+1),row x y z q (support s r lo mode q)) := by
 let k :=cut s r lo mode
 let f := fun q=>row x y z q (support s r lo mode q)
 have hk :k≤ s.B+1 :=min_le_left _ _
 have hsplit :=sum_range_add f k (s.B+1-k)
 have hprefix :=sum_range_add f s.J (k-s.J)
 rw [Nat.add_sub_of_le hk] at hsplit
 rw [Nat.add_sub_of_le hj] at hprefix
 change _=6*(∑ q∈range (s.B+1),f q)
 rw [hsplit,hprefix,mul_add,mul_add]
 have hfirst: (∑ q∈range s.J,f q) = ∑ q∈range s.J,row x y z q (q+1) := by
   apply sum_congr rfl
   intro q hq
   have hq' := mem_range.mp hq
   simp only [f,support,ite_eq_left (hq'.trans_le hj),min_eq_left hq'.le]
 have hmiddle : (∑ i∈range (k-s.J),f (s.J+i)) =
     ∑ i∈range (k-s.J),row x y z (s.J+i) (s.J+1) := by
   apply sum_congr rfl
   intro i hi
   have hi' := mem_range.mp hi
   have hlt:s.J+i<cut s r lo mode := by change s.J+i<k; omega
   simp only [f,support,ite_eq_left hlt,min_eq_right (Nat.le_add_right _ _)]
 have hlast : (∑ i∈range (s.B+1-k),f (k+i)) =
     ∑ i∈range (s.B+1-k),row x y z (k+i) (csU s r lo mode (k+i)) := by
   apply sum_congr rfl
   intro i _
   have hge :cut s r lo mode≤k+i:=Nat.le_add_right k i
   simp only [f,support,ite_eq_right (not_lt_of_ge hge)]
 rw [hfirst,hmiddle,hlast,df7,df3]
 dsimp only [total]
 rw [dgC]
private def origin (s :Shape) (r :ℕ) (h:ℤ) :ℤ:=(s.m:ℤ)*midAgreement - 2*h*r
private def aso (s :Shape) (r :ℕ) (h:ℤ) (mode q j:ℕ) :ℤ :=
 origin s r h-(131071-h)*q+(1-2*mode*h)*j
private def b7r (s :Shape) (r lo mode :ℕ) :ℤ :=
 total s r lo mode (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo)
private def cpY (s :Shape) (r lo mode :ℕ) :ℤ :=
 total s r lo mode (-4*(r :ℤ)) 2 (-2*(mode :ℤ))
private theorem gq1 (s :Shape) (r h mode q j:ℕ) (hh:h≤131071) :
  aso s r h mode q j≤((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) := by
 have cast_sub_le (a b:ℕ) : (a :ℤ)-b≤((a-b:ℕ) :ℤ) := by omega
 have hcut:=cast_sub_le (s.m*midAgreement) (2*h*r)
 have hraw:=cast_sub_le (Mq h r s+j) (q*(131071-h))
 have hloss :=cast_sub_le (amv h r s q j) (mode*(2*h*j))
 change _≤(Mq h r s :ℤ) at hcut
 change _≤(amv h r s q j:ℤ) at hraw
 push_cast [Nat.cast_sub hh] at hcut hraw hloss
 unfold aso origin
 rw [cA5]
 nlinarith only [hcut,hraw,hloss]
private theorem fZn (s :Shape) (r lo h mode q n:ℕ) :
   row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q n +
     ((h:ℤ)-lo)*row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q n =
   2*(∑ j∈range n,aso s r h mode q j) := by
 change _=2*(∑ j∈range n,(origin s r h-(131071-(h:ℤ))*q+(1-2*(mode :ℤ)*h)*j))
 rw [bid]
 unfold row origin
 ring
private theorem gxx (s :Shape) (r lo h mode :ℕ) (hh:h≤131071)
    (hj:s.J≤ cut s r lo mode) :
    b7r s r lo mode+((h:ℤ)-lo)*cpY s r lo mode ≤
      12*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
  let f := fun q=>row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q
    (support s r lo mode q)
  let g:= fun q=>row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q (support s r lo mode q)
  have hsum: (∑ q∈range (s.B+1),f q)+((h:ℤ)-lo)*(∑ q∈range (s.B+1),g q) ≤
      2*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
    unfold ku
    push_cast [Nat.cast_sum]
    rw [mul_sum,← sum_add_distrib,mul_sum]
    apply sum_le_sum
    intro q _
    rw [show f q+((h:ℤ)-lo)*g q= _ from fZn s r lo h mode q (support s r lo mode q)]
    have hsub:range (support s r lo mode q)⊆range (min q s.J+1) := by
      apply range_mono
      unfold support
      split
      · rfl
      · exact min_le_left _ _
    apply mul_le_mul_of_nonneg_left _ (by decide : (0:ℤ)≤2)
    calc
      _ ≤ ∑ j∈range (support s r lo mode q),((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) :=
        sum_le_sum fun j _=>gq1 s r h mode q j hh
      _≤_:=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Int.natCast_nonneg _)
  unfold b7r cpY
  rw [asB _ _ _ _ _ _ _ hj,asB _ _ _ _ _ _ _ hj]
  have hz :=mul_le_mul_of_nonneg_left hsum (by decide : (0:ℤ)≤6)
  dsimp only [f,g] at hz
  nlinarith only [hz]
private def biN (s :Shape) (r :ℕ) (h:ℤ) :ℤ :=
 origin s r h-(131071-h)*s.B
private theorem gMy (s :Shape) (r h:ℕ) (hh:h≤131071)
  (hw:0<biN s r h) :aL4 h r s := by
 have hn:0≤(131071-(h:ℤ))*(s.B:ℤ) := by
  exact mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
 unfold biN origin at hw
 have hbuf :2*h*r≤ s.m*midAgreement:= by
  have hz :2*(h:ℤ)*r≤(s.m:ℤ)*midAgreement:= by nlinarith only [hn,hw]
  exact_mod_cast hz
 unfold aL4 Mq
 apply Int.ofNat_lt.mp
 push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
 rw [cA5] at hw
 nlinarith only [hw]
private def cXb (t:Bank) (r lo mode :ℕ) :ℤ :=
 (triangle t.shape.U:ℤ)*b7r t.shape r lo mode - 12*(j3 lo t:ℤ)
private def deC (t:Bank) (r lo mode :ℕ) :ℤ :=
 (triangle t.shape.U:ℤ)*cpY t.shape r lo mode - 24*((t.shape.U:ℤ)+1)*t.poleMoment
private def check (lo hi:ℕ) (t:Bank) (r mode :ℕ) :Bool :=
 let w:=biN t.shape r lo
 let d:=(hi:ℤ)-lo
 let z :=cXb t r lo mode
 decide (hi≤131071) && decide (t.shape.J≤ cut t.shape r lo mode) &&
  decide (0<w) && decide (0<w+d*((t.shape.B:ℤ)-2*r)) &&
  decide (0<z) && decide (0<z+d*deC t r lo mode)
private theorem test {lo hi h:ℕ} {t:Bank} {r mode :ℕ} (hl:lo≤h) (hu:h≤hi)
  (hc:check lo hi t r mode=true) :
  aL4 h r t.shape∧j3 h t<O3 h r t.shape mode := by
 simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
 obtain ⟨⟨⟨⟨⟨hk,hj⟩,hw₀⟩,hw₁⟩,hz₀⟩,hz₁⟩:=hc
 have hl' : (lo:ℤ)≤h:=Int.ofNat_le.mpr hl
 have hu' : (h:ℤ)≤hi:=Int.ofNat_le.mpr hu
 have hh:=hu.trans hk
 have hw:=cck hl' hu' hw₀ hw₁
 have he :biN t.shape r h =
    biN t.shape r lo+((h:ℤ)-lo)*((t.shape.B:ℤ)-2*r) := by
  unfold biN origin
  ring
 refine ⟨gMy _ _ _ hh (he.symm ▸ hw),?_⟩
 have hz :=cck hl' hu' hz₀ hz₁
 have hs :=mul_le_mul_of_nonneg_left (gxx _ _ _ _ _ hh hj)
  (Int.natCast_nonneg (triangle t.shape.U))
 unfold cXb deC j3 at hz
 unfold O3 j3
 apply Int.ofNat_lt.mp
 push_cast at hz ⊢
 nlinarith only [hz,hs]
private def jf (lo hi:ℕ) (ss :List Ls) :Prop :=
 ∀ s∈ss,check lo hi s.free s.dI 0=true ∧
   check lo hi s.moving s.dI 1=true∧s.free.shape.U<p
private theorem dLg {lo hi:ℕ} {s :Ls} {ss :List Ls}
  (hf :check lo hi s.free s.dI 0=true)
  (hm:check lo hi s.moving s.dI 1=true)
  (hp:s.free.shape.U<p) (ht:jf lo hi ss) :jf lo hi (s :: ss) :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm,hp⟩,ht⟩
private theorem dLh {lo hi:ℕ} : jf lo hi [] := by simp [jf]
set_option maxHeartbeats 5000000 in
private theorem dsU (b:fO) :jf b.jX.lo b.jX.hi (stages b) := by
 cases b <;> simp only [stages,fO.schedule]
 all_goals repeat' first
  | exact dLh
  | refine dLg rfl rfl (by decide) ?_
theorem proof :P5_7_3.c2 := by
 intro b h hl hu s hs
 obtain ⟨hf,hm,hc⟩:=dsU b s hs
 obtain ⟨hw,hd⟩:=test hl hu hf
 obtain ⟨hw',hd'⟩:=test hl hu hm
 exact ⟨hw,hd,hc,hw',hd'⟩
end q4WM8sb
end
section
set_option autoImplicit true
namespace qkgz7gb
noncomputable section
open P5 (K I p node blockLength)
open P5_7 (midAgreement)
open cu (L Equation vm triangle)
open DP (jF aKF)
open Y3 (Dg embed constant)
open Polynomial
inductive Stock where
 | symmetric (v :ℕ)
 | asymmetric (vz vt:ℕ)
 deriving DecidableEq
structure Witness where
 g:ℕ
 modulus :ℕ
 weight:ℕ
 stock :Stock
def Stock.size :Stock→ℕ
 | .symmetric v=>triangle v
 | .asymmetric vz vt=>(vz+1)*(vt+1)
def Stock.cUr (s :Stock) (u:ℕ) :Stock :=
 match s with
 | .symmetric v => .symmetric (v+u)
 | .asymmetric vz vt => .asymmetric (vz+u) (vt+u)
def Stock.fits (s :Stock) (G:Equation) :Prop :=
 match s with
 | .symmetric v=>vm G v
 | .asymmetric vz vt => ∀ i,(G.coeff i).degreeOf 0≤vz∧(G.coeff i).degreeOf 1≤vt
def ceilDiv (a b:ℕ) :ℕ:=(a+b-1)/b
def physicalStock (a D:ℕ) :ℕ :=
 let j:=ceilDiv a D
 j*a - D*(j*(j-1)/2)
def Stock.resultantShift (s :Stock) (e E u:ℕ) :Stock :=
 match s with
 | .symmetric v => .symmetric (e*v+E*u)
 | .asymmetric vz vt => .asymmetric (e*vz+E*u) (e*vt+E*u)
def Stock.first:Stock→ℕ
 | .symmetric v=>v
 | .asymmetric vz _=>vz
def Stock.b5A:Stock→ℕ
 | .symmetric v=>(p+1)*v
 | .asymmetric vz vt=>vz+p*vt
def highStock (e u:ℕ) (w:Witness) :Stock :=
 (w.stock.cUr u).resultantShift e (e+w.g) u
def FilterOK (D e u:ℕ) (w:Witness) :Prop :=
  let E :=e+w.g
  0<D ∧0<e∧e*D ≤w.weight∧E*D <w.modulus ∧
  (D*(E*(E+1)/2)+physicalStock (w.modulus-w.weight-1) D)*(w.stock.cUr u).size <
    (w.g+1)*w.modulus*w.stock.size ∧
  (highStock e u w).first<p
def branchDegree (D e W:ℕ) :Stock→ℕ
 | .symmetric _=>2*e*W-e*e*D
 | .asymmetric _ _=>(2*e-2)*W-e*(e-1)*D
def CurveOK (D e W:ℕ) (s :Stock) :Prop :=
 0<D ∧D < midAgreement∧0<e∧e<p∧e*D ≤W ∧
 match s with
 | .symmetric _=>branchDegree D e W s<p
 | .asymmetric _ _=>branchDegree D e W s+2*W<p
def smoothRate (D e u W:ℕ) (s :Stock) :ℕ :=
  let g:=midAgreement-D
  let m:=branchDegree D e W s
  let (base,poles) := match s with
    | .symmetric _=>(1, 2*e*(2*m-1))
    | .asymmetric _ _=>(7,(2*e-2)*(2*m-1)+4*W)
  (base+6*e)*u+ceilDiv (u*(2*e*blockLength+poles)) g+4*e*e
def planeFee (B:ℕ) :ℕ :=
 let d:=2*B-1
 B*d+(d-1)*(d-2)/2
def Weighted (D W:ℕ) (f :Equation) :Prop :=
  ∃ (Q:Dg) (a :cu.FX),a≠0∧embed Q=constant a*f ∧
    ∀ j m,(Q.coeff j).coeff m≠0→((Q.coeff j).coeff m).natDegree+j*D ≤W
def LowWeight (D W:ℕ) (f :Equation) :Prop :=
 ∀ q:Equation,Irreducible q→q∣f→Weighted D W q
structure UJ (D:ℕ) (word:I→K) (T:Finset K) (z :K→K) (S:K→K[X]) :Prop where
 Kw:Set.InjOn z (T:Set K)
 sections :Set.InjOn S (T:Set K)
 degree : ∀ γ∈T,(S γ).natDegree≤D
 dw : ∀ γ∈T,∃ V:Finset I,midAgreement≤V.card ∧ ∀ i∈V,(S γ).eval (node i)=word i
 poles : ∃ h:ℕ,0<h ∧ ∃ P:jF h,∀ γ∈T,aKF P (z γ) (S γ)
abbrev PlaneCurve :=MvPolynomial (Fin 2) L
def rV (z :K→K) (γ:K) :Fin 2→L :=
 let a :=algebraMap K L (z γ)
 ![a,a^p]
def SmoothAt (q:PlaneCurve) (x :Fin 2→L) :Prop :=
 q.eval x=0 ∧ ∃ i:Fin 2,(MvPolynomial.pderiv i q).eval x≠0
open scoped Classical in
def SmoothCount (T:Finset K) (z :K→K) (B:ℕ) :Prop :=
  ∀ q:PlaneCurve,Irreducible q →
    (T.filter fun γ=>SmoothAt q (rV z γ)).card≤B*q.totalDegree
end
end qkgz7gb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨3000,4189,858,u⟩,0x2c49ea7940000,0x75c8c30a950⟩:Dt.Bank) 3555 e v k l b d z n x
theorem ordinary3555:Signs (terminal .uH) 3555 13 0 :=
 r! 50872 13 0 61 70 31 4 4 3 0x19ae5c0548116382
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .uH) 3555 e ((((P5_7_3.fO.uH).schedule.gw).drop a).take 1)
theorem yQj0:gZ! 1 0:=⟨r! 41861 1 110 70 69 21 5 7 3 0x114200711a217aaec,trivial⟩
theorem yQj1:gZ! 2 1:=⟨r! 42560 2 107 71 69 20 5 8 3 0x285801c6f50c4076,trivial⟩
theorem yQj2:gZ! 3 2:=⟨r! 43612 3 104 72 69 19 5 9 3 0x5e6007456867110,trivial⟩
theorem yQj3:gZ! 4 3:=⟨r! 44531 4 100 70 69 21 5 11 3 0x1a3e0075e321ae894,trivial⟩
theorem yQj4:gZ! 5 4:=⟨r! 46347 5 96 71 69 20 5 1 4 0x3be001f3f92e9716,trivial⟩
theorem yQj5:gZ! 6 5:=⟨r! 49464 6 91 71 69 21 5 4 4 0x800116a004696a909f76,trivial⟩
theorem grades3555A:GradeSigns (terminal .uH) 3555 1 (((P5_7_3.fO.uH).schedule.gw).take 6) :=⟨yQj0.1,yQj1.1,yQj2.1,yQj3.1,yQj4.1,yQj5.1,trivial⟩
end qqf9uAa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨3000,4189,858,u⟩,0x2c49ea7940000,0x75c8c30a950⟩:Dt.Bank) 3555 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .uH) 3555 e ((((P5_7_3.fO.uH).schedule.gw).drop a).take 1)
theorem yQj6:gZ! 7 6:=⟨r! 50872 7 84 70 70 22 4 7 4 0x1d04008fdfaa34724,trivial⟩
theorem yQj7:gZ! 8 7:=⟨r! 50872 8 76 72 70 20 4 3 4 0x48a008762a8dd06,trivial⟩
theorem yQj8:gZ! 9 8:=⟨r! 50872 9 65 72 70 20 4 12 3 0x276008052a8e626,trivial⟩
theorem yQj9:gZ! 10 9:=⟨r! 50872 10 52 72 70 20 4 9 3 0x104007980a8ee68,trivial⟩
theorem yQj10:gZ! 11 10:=⟨r! 50872 11 37 72 70 20 4 7 3 0x3e0072d2a8f5dc,trivial⟩
theorem yQj11:gZ! 12 11:=⟨r! 50872 12 20 72 70 20 4 5 3 0x2006c58a8fc92,trivial⟩
theorem grades3555B:GradeSigns (terminal .uH) 3555 7 (((P5_7_3.fO.uH).schedule.gw).drop 6) :=⟨yQj6.1,yQj7.1,yQj8.1,yQj9.1,yQj10.1,yQj11.1,trivial⟩
end qqf9uAa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (Signs GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2704 e v k l b d z n x
theorem ordinary2704 :Signs (terminal .h2704) 2704 29 0 :=
 r! 184320 29 0 75 73 19 4 1 3 0x8faf0461e70
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2704) 2704 e ((((P5_7_3.fO.h2704).schedule.gw).drop a).take 1)
theorem yQj12:gZ! 1 0:=⟨r! 92258 1 869 69 71 23 4 12 2 0x8fe245461d706,trivial⟩
theorem yQj13:gZ! 2 1:=⟨r! 92692 2 861 69 71 23 4 12 2 0x9004bd562cad4,trivial⟩
theorem yQj14:gZ! 3 2:=⟨r! 93190 3 853 69 71 23 4 12 2 0x902d19563e2c8,trivial⟩
theorem yQj15:gZ! 4 3:=⟨r! 93592 4 844 67 71 25 4 12 2 0x904cbcd5932026,trivial⟩
theorem yQj16:gZ! 5 4:=⟨r! 94238 5 836 68 71 24 4 1 3 0x22420b58acc6938,trivial⟩
theorem grades2704A:GradeSigns (terminal .h2704) 2704 1 (((P5_7_3.fO.h2704).schedule.gw).take 5) :=⟨yQj12.1,yQj13.1,yQj14.1,yQj15.1,yQj16.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2704 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2704) 2704 e ((((P5_7_3.fO.h2704).schedule.gw).drop a).take 1)
theorem yQj17:gZ! 6 5:=⟨r! 94804 6 827 68 71 24 4 1 3 0x12242c6e8aceef5a,trivial⟩
theorem yQj18:gZ! 7 6:=⟨r! 95472 7 818 68 71 24 4 1 3 0x38243a8e2ad1ebae,trivial⟩
theorem yQj19:gZ! 8 7:=⟨r! 96077 8 808 65 71 27 4 1 3 0xee8911d08c56a5394e,trivial⟩
theorem yQj20:gZ! 9 8:=⟨r! 97002 9 799 69 71 23 4 1 3 0x1b8916e1b56c691a,trivial⟩
theorem yQj21:gZ! 10 9:=⟨r! 97907 10 789 69 71 23 4 1 3 0x2c891bdd556e78a4,trivial⟩
theorem yQj22:gZ! 11 10:=⟨r! 98811 11 778 68 71 24 4 1 3 0x20e24837f8ae119a8,trivial⟩
theorem grades2704B:GradeSigns (terminal .h2704) 2704 6 ((((P5_7_3.fO.h2704).schedule.gw).drop 5).take 6) :=⟨yQj17.1,yQj18.1,yQj19.1,yQj20.1,yQj21.1,yQj22.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2704 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2704) 2704 e ((((P5_7_3.fO.h2704).schedule.gw).drop a).take 1)
theorem yQj23:gZ! 12 11:=⟨r! 99951 12 767 68 71 24 4 1 3 0x2da249d60aae6606a,trivial⟩
theorem yQj24:gZ! 13 12:=⟨r! 101188 13 755 66 71 26 4 1 3 0xef424b9e30abb0a868,trivial⟩
theorem yQj25:gZ! 14 13:=⟨r! 102822 14 743 68 71 24 4 2 3 0x4b624e08e0cf3e3fa,trivial⟩
theorem yQj26:gZ! 15 14:=⟨r! 104782 15 730 68 71 24 4 2 3 0x5a62510116cfd4d74,trivial⟩
theorem yQj27:gZ! 16 15:=⟨r! 107315 16 716 69 71 24 4 2 3 0x33a22a7a92c84d964,trivial⟩
theorem yQj28:gZ! 17 16:=⟨r! 110654 17 700 69 72 24 3 2 3 0xde01696d668d397a,trivial⟩
theorem grades2704C:GradeSigns (terminal .h2704) 2704 12 ((((P5_7_3.fO.h2704).schedule.gw).drop 11).take 6) :=⟨yQj23.1,yQj24.1,yQj25.1,yQj26.1,yQj27.1,yQj28.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2704 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2704) 2704 e ((((P5_7_3.fO.h2704).schedule.gw).drop a).take 1)
theorem yQj29:gZ! 18 17:=⟨r! 116014 18 682 69 72 24 3 3 3 0xe5018dd8c69b2932,trivial⟩
theorem yQj30:gZ! 19 18:=⟨r! 125542 19 659 67 72 26 4 3 3 0xe9623a6ecea2d5eeac,trivial⟩
theorem yQj31:gZ! 20 19:=⟨r! 147250 20 629 70 72 23 4 3 3 0x808943ef257c8594,trivial⟩
theorem yQj32:gZ! 21 20:=⟨r! 184320 21 579 70 73 24 4 3 3 0x1de23ffcca8c28a54,trivial⟩
theorem yQj33:gZ! 22 21:=⟨r! 184320 22 517 68 73 26 4 2 3 0x20023fd150a30adca0,trivial⟩
theorem yQj34:gZ! 23 22:=⟨r! 184320 23 451 67 73 27 4 2 3 0x1288fe9c8f46170e58,trivial⟩
theorem grades2704D:GradeSigns (terminal .h2704) 2704 18 ((((P5_7_3.fO.h2704).schedule.gw).drop 17).take 6) :=⟨yQj29.1,yQj30.1,yQj31.1,yQj32.1,yQj33.1,yQj34.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2704 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2704) 2704 e ((((P5_7_3.fO.h2704).schedule.gw).drop a).take 1)
theorem yQj35:gZ! 24 23:=⟨r! 184320 24 381 69 73 25 4 2 3 0x8fdfab5186149a,trivial⟩
theorem yQj36:gZ! 25 24:=⟨r! 184320 25 307 70 73 24 4 1 3 0x23f583e8c330c0,trivial⟩
theorem yQj37:gZ! 26 25:=⟨r! 184320 26 228 69 73 25 4 1 3 0x8fcd2ad186a8a4,trivial⟩
theorem yQj38:gZ! 27 26:=⟨r! 184320 27 145 69 73 25 4 1 3 0x8fc4b91186ec30,trivial⟩
theorem yQj39:gZ! 28 27:=⟨r! 184320 28 58 69 73 25 4 1 3 0x8fbcb591872c4a,trivial⟩
theorem grades2704E:GradeSigns (terminal .h2704) 2704 24 (((P5_7_3.fO.h2704).schedule.gw).drop 23) :=⟨yQj35.1,yQj36.1,yQj37.1,yQj38.1,yQj39.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (Signs GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
theorem ordinary2708:Signs (terminal .h2708) 2708 31 0 :=
 r! 153600 31 0 76 73 18 3 12 2 0x154f5a23c4
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQj40:gZ! 1 0:=⟨r! 91209 1 850 68 71 24 4 12 2 0x3d93b68bfc7c6,trivial⟩
theorem yQj41:gZ! 2 1:=⟨r! 91630 2 842 67 71 25 4 12 2 0x8f857e51833aaa,trivial⟩
theorem yQj42:gZ! 3 2:=⟨r! 92113 3 834 67 71 25 4 12 2 0x8faba2d18770ac,trivial⟩
theorem yQj43:gZ! 4 3:=⟨r! 92669 4 826 68 71 24 4 1 3 0x23f61acac625d0,trivial⟩
theorem yQj44:gZ! 5 4:=⟨r! 93135 5 817 64 71 28 4 1 3 0x4623ff4bceac83565e,trivial⟩
theorem grades2708A:GradeSigns (terminal .h2708) 2708 1 (((P5_7_3.fO.h2708).schedule.gw).take 5) :=⟨yQj40.1,yQj41.1,yQj42.1,yQj43.1,yQj44.1,trivial⟩
end qWKyASa
end
