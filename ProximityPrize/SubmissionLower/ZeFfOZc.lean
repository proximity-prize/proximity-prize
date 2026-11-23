import ProximityPrize.SubmissionLower.A
set_option Elab.async false
set_option autoImplicit true
section
namespace agU
open cu (Shape ku)
open scoped BigOperators
def arY (s :Shape) :ℕ :=
 ku s (fun q _=>s.B+s.J - q)
def ad1 (s :Shape) :ℕ :=
 262144*ku s (fun q j=>s.m+min q s.J-(q+2*j))
def Bb (B J t q:ℕ) :ℕ :=
 let low:=J - t
 let high:=min J (B+2*J - 1 - t)
 min q high+1-low
def Xq (B J t q:ℕ) :ℕ :=
 min (Bb B J t q) (B+2*J-(t+q))
def aVz (B J t R:ℕ) :ℕ :=
  (Finset.range (B+1)).inf' Finset.nonempty_range_add_one fun k =>
    R*k + ∑ q∈Finset.range (B+1),(q-k)*Bb B J t q
def aDY (B J t:ℕ) :ℕ :=
 let R := ∑ q∈Finset.range (B+1),Xq B J t q
 aVz B J t R - ∑ q∈Finset.range (B+1),q*Xq B J t q
def ajD (B J:ℕ) :ℕ :=
 ∑ t∈Finset.range (B+2*J),aDY B J t
end agU
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace agU
noncomputable section
open K1 (I)
open cu (L FX Shape)
open DP Polynomial
open scoped Polynomial BigOperators
open private cW6 from ProximityPrize.SubmissionLower.Z
open private aMr bVO cqC cWB from ProximityPrize.SubmissionLower.Z
private theorem gNq {h} (hhi:h≤131070) {D:jF h}
   (Crt:zG D) (s :Shape) (P:Source) (hp:P∈btN Crt s)
   (hs : ∀ j i a e,Fg P j i a e≠0 →
     a+(i+j)*(131071+h)<(s.B+s.J)*(2*h)+j) :P=0:= by
 by_contra hP
 let j:=P.natDegree
 let i:=P.leadingCoeff.natDegree
 let g:=P.leadingCoeff.leadingCoeff
 have hg:g≠0:=leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
 obtain ⟨e,he⟩ : ∃ e,g.leadingCoeff.coeff e≠0:= by
   by_contra! hh
   exact (leadingCoeff_ne_zero.mpr hg) (MvPolynomial.eq_zero_iff.mpr hh)
 have hcoeff :Fg P j i g.natDegree e≠0:= by
   simpa [Fg,j,i,g,coeff_natDegree] using he
 have hlt:=hs j i g.natDegree e hcoeff
 let H :=IE D
 have hm:H.Monic:=((D.monic 0).mul (D.monic 1)).map _
 have hd:H.natDegree=2*h:=bjE.bgu D
 have hinj:Function.Injective (algebraMap qC aQ) :=
   IsFractionRing.injective qC aQ
 have hg' : au5 g≠0:=Polynomial.map_ne_zero_iff hinj |>.2 hg
 have hdeg: (au5 g).natDegree=g.natDegree :=Polynomial.natDegree_map_eq_of_injective hinj g
 obtain ⟨Q,hQ⟩:=hp
 have hdvd:H^(s.B+s.J)∣au5 g*H^(i+j) := by
   refine ⟨(Q.coeff j).coeff i,?_⟩
   have hc:=congrArg (fun R:US=>(R.coeff j).coeff i) hQ
   change ((forward Crt P).coeff j).coeff i= _ at hc
   have hlead:=cW6 Crt P
   dsimp only at hlead
   rw [show j=P.natDegree from rfl,show i=P.leadingCoeff.natDegree from rfl,hlead] at hc
   simpa only [pW,RingHom.comp_apply,coeff_C_mul,H,i,j,g] using hc
 have hlo:=natDegree_le_of_dvd hdvd (mul_ne_zero hg' (pow_ne_zero _ hm.ne_zero))
 rw [natDegree_mul hg' (pow_ne_zero _ hm.ne_zero),hdeg,natDegree_pow,natDegree_pow,hd] at hlo
 have hweights : (i+j)*(131071+h)=(i+j)*(2*h)+(i+j)*(131071-h) := by
   rw [← Nat.mul_add]
   congr 1
   omega
 have hj:j≤(i+j)*(131071-h) :=(Nat.le_add_left j i).trans
   (by simpa using Nat.mul_le_mul_left (i+j) (show 1≤131071-h by omega))
 rw [hweights] at hlt
 omega
private theorem ker_zero {h} (hhi:h≤131070) {D:jF h} (Crt:zG D)
  (word:I→L) (s :Shape) : (aMr Crt word s 0).ker = ⊥ := by
 apply bot_unique
 intro P hP
 rw [Submodule.mem_bot]
 apply Subtype.ext
 apply gNq hhi Crt s P P.property.2
 intro j i a e hn
 simpa only [zero_add] using cqC ⟨P,hP⟩ hn
theorem telescope {h:ℕ} (hraw:h≤131070) {D:jF h}
   (Crt:zG D) (word:I→L) (s :Shape) (W:ℕ) :
   Module.finrank L (complete Crt word s W) ≤
     ∑ t∈Finset.range (W+1),Module.finrank FX (VY Crt word s t) := by
 induction W with
 | zero =>
   have hr :=(aMr Crt word s 0).finrank_range_add_finrank_ker
   rw [ker_zero hraw Crt word s,finrank_bot,add_zero] at hr
   simpa [← hr] using bVO Crt word s 0
 | succ W ih =>
   rw [Finset.sum_range_succ]
   have hr :=(aMr Crt word s (W+1)).finrank_range_add_finrank_ker
   have ha :=bVO Crt word s (W+1)
   have hb:=cWB Crt word s W
   omega
end
end agU
end
section
namespace jQ
def Fu (a q:ℕ) :ℕ:=q+1-a
def low (J t:ℕ) :ℕ:=J - t
def high (B J t:ℕ) :ℕ:=min J (B+2*J - 1 - t)
def width (B J t:ℕ) :ℕ:=high B J t+1-low J t
def edge (B J t:ℕ) :ℕ:=B+2*J - t
def aoF (B J t:ℕ) :ℕ :=
 min (width B J t) ((edge B J t - low J t+1)/2)
def a6U (n a b:ℕ) :ℕ :=
 6*n*a*b+3*(a+b)*n*(n-1)+n*(n-1)*(2*(n-1)+1)
def buF (N a :ℕ) :ℕ :=
 let n:=N-a
 3*n*(n+1)
def bK1 (N a :ℕ) :ℕ:=a6U (N-a) a 1
def cem (N k a :ℕ) :ℕ :=
 let s :=max (k+1) a
 a6U (N-s) (s-k) (s+1-a)
def bKt (B J t:ℕ) (stat :ℕ→ℕ) :ℕ :=
 let a :=low J t
 let e :=edge B J t
 let h:=aoF B J t
 stat a+stat (e+1)-(stat (a+h)+stat (e+1-h))
def bC6 (B J t:ℕ) (stat :ℕ→ℕ) :ℕ :=
 let a :=low J t
 stat a - stat (a+width B J t)
def btD (B J t:ℕ) :ℕ:=bKt B J t (buF (B+1))
def cbP (B J t:ℕ) :ℕ:=bKt B J t (bK1 (B+1))
def b2e (B J t k :ℕ) :ℕ:=bC6 B J t (cem (B+1) k)
def cud (omitted:ℕ) :ℕ→ℕ→ℕ→ℕ
  | 0,lo,_=>lo
  | fuel+1,lo,hi =>
    if lo+1<hi then
      let mid :=(lo+hi)/2
      if mid*(mid+1)≤2*omitted then cud omitted fuel mid hi
      else cud omitted fuel lo mid
    else lo
def threshold (B J t:ℕ) :ℕ :=
  let R:=btD B J t/6
  let w:=width B J t
  let h:=high B J t
  if R≤w*(B+1-h) then B-(R-1)/w else
    let omitted:=bC6 B J t (buF (B+1))/6 - R
    min B (low J t+cud omitted 16 0 (w+1))
def c2b (B J t:ℕ) :ℕ :=
 let k :=threshold B J t
 (btD B J t*k+b2e B J t k - cbP B J t)/6
def m8 (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>m8 f n+f n
def lT (B J start length:ℕ) :ℕ :=
 m8 (fun i=>c2b B J (start+i)) length
def eE (B J:ℕ) :ℕ:=lT B J J (B+J)
end jQ
end
section
namespace czX
open Finset
open cu (Shape ku)
open agU (ad1)
open scoped BigOperators
open private ddK from ProximityPrize.SubmissionLower.H
private def anH (m J q j:ℕ) :ℕ:=m+min q J-(q+2*j)
private def aQY (k i:ℕ) :ℕ :=
 k*(k+1)+(6*k+2)*i+8*i*i
def a8x (k J:ℕ) :ℕ :=
 3*(J+1)*k*(k+1)+3*(3*k+1)*J*(J+1)+4*J*(J+1)*(2*J+1)
private theorem gEK (d:ℕ) :
   2*(∑ i∈range d,(d-i))=d*(d+1) := by
 induction d with
 | zero=>simp
 | succ d ih =>
   rw [sum_range_succ']
   simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,mul_add,ih]
   ring
private theorem gBp (k J:ℕ) :
   3*(∑ i∈range (J+1),aQY k i)=a8x k J:= by
 induction J with
 | zero=>simp [aQY,a8x,mul_assoc]
 | succ J ih =>
   rw [sum_range_succ,mul_add,ih]
   unfold aQY a8x
   ring
private theorem gEJ {m B J j:ℕ} (hm:2*J≤ m)
    (hB:m+J≤B+1) (hj:j≤J) :
    2*(∑ q∈Ico j (B+1),anH m J q j)=aQY (m-2*J) (J-j) := by
  let d:=m - 2*j
  have hhead: (∑ q∈Ico j J,anH m J q j)=(J-j)*d:= by
    calc
      _ = ∑ _q∈Ico j J,d:= by
        apply sum_congr rfl
        intro q hq
        unfold anH
        rw [min_eq_left (mem_Ico.mp hq).2.le]
        dsimp [d]
        omega
      _ = _:= by simp [Nat.card_Ico]
  have htail: (∑ q∈Ico J (B+1),anH m J q j) =
      ∑ i∈range d,(d-i) := by
    rw [sum_Ico_eq_sum_range]
    calc
      _ = ∑ i∈range (B+1-J),(d-i) := by
        apply sum_congr rfl
        intro i _
        unfold anH
        rw [min_eq_right (by omega :J≤J+i)]
        dsimp [d]
        omega
      _ = _:= by
        symm
        apply sum_subset (range_mono (show d≤B+1-J by dsimp [d]; omega))
        intro i _ hi
        have hdi:d≤ i:= by simpa only [mem_range,not_lt] using hi
        exact Nat.sub_eq_zero_of_le hdi
  rw [← sum_Ico_consecutive (anH m J · j) hj (show J≤B+1 by omega),
    hhead,htail,mul_add,gEK]
  have hd:d=(m-2*J)+2*(J-j) := by dsimp [d]; omega
  rw [hd]
  unfold aQY
  ring
theorem dei (s :Shape) (hm:2*s.J≤ s.m) (hB:s.m+s.J≤ s.B+1) :
    6*ad1 s=262144*a8x (s.m-2*s.J) s.J:= by
  change 6*(262144*ku s (fun q j=>anH s.m s.J q j))= _
  unfold ku
  rw [ddK]
  let f (j:ℕ) := ∑ q∈Ico j (s.B+1),anH s.m s.J q j
  let k :=s.m-2*s.J
  change 6*(262144*(∑ j∈range (s.J+1),f j))=262144*a8x k s.J
  calc
    _=262144*(3*(2 * ∑ j∈range (s.J+1),f j)) := by ring
    _=262144*(3 * ∑ j∈range (s.J+1),aQY k (s.J-j)) := by
      rw [mul_sum]
      refine congrArg (fun n:ℕ=>262144*(3*n)) (sum_congr rfl fun j hj => ?_)
      exact gEJ hm hB (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = _:= by
      have hreflect : (∑ j∈range (s.J+1),aQY k (s.J-j)) =
          ∑ j∈range (s.J+1),aQY k j:= by
        simpa only [Nat.add_sub_cancel] using sum_range_reflect (aQY k) (s.J+1)
      rw [hreflect,gBp]
end czX
end
