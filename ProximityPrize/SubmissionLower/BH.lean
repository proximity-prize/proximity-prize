import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.R
import ProximityPrize.SubmissionLower.CO
set_option Elab.async false
open _root_ renaming Finset.range→cy,Finset.sum_range_add→lJ,Int.ediv_mul_cancel→nI,Int.emod_two_eq_zero_or_one→ oD,dvd_mul_of_dvd_left→ oq,dvd_mul_of_dvd_right→ ox,gT.Ambient→c9,ite_eq_left→lz,ite_eq_right→nq,ite_false→mD,min_eq_left→ oy,sub_zero→n5,xE.denominator→aU
set_option autoImplicit true
section
namespace aRR
open xE
private def coH (q r :ℤ) :ℤ :=
 2+r*(r+1)+q*(44+14*r+r*(r - 1)) +
   (57+6*r)*(q*(q - 1))+12*q*(q - 1)*(q - 2)
private theorem XK (x :ℤ) :2*(x*(x - 1)/2)=x*(x - 1) := by
 have h: (2 :ℤ)∣x*(x - 1) := by
  rcases oD x with hx | hx
  · exact oq (by omega : (2 :ℤ)∣x) _
  · exact ox (by omega : (2 :ℤ)∣x - 1) _
 rw [mul_comm,nI h]
private theorem coI (u:ℤ) (hu:0≤u) :
  2*aU u=coH (u/6) (u % 6) := by
 let q:=u/6
 let r :=u % 6
 simp only [aU,not_lt.mpr hu,mD,coH]
 change 2*(1+r*(r+1)/2+q*(22+7*r+r*(r - 1)/2) +
  (57+6*r)*(q*(q - 1)/2)+6*q*(q - 1)*(q - 2))= _
 have h:=XK (r+1)
 rw [show (r+1)*(r+1 - 1)=r*(r+1) by ring] at h
 change _=2+r*(r+1)+q*(44+14*r+r*(r - 1)) +
  (57+6*r)*(q*(q - 1))+12*q*(q - 1)*(q - 2)
 linear_combination h+q*XK r+(57+6*r)*XK q
private def c5h (q r :ℤ) :ℤ :=
 984*q+3084*q*(q - 1)+1728*q*(q - 1)*(q - 2) +
  216*q*(q - 1)*(q - 2)*(q-3) +
  24*r+4*r*(r - 1)*(r+1) +
  q*(528*r+84*r*(r - 1)+4*r*(r - 1)*(r - 2)) +
  (684*r+36*r*(r - 1))*q*(q - 1)+144*r*q*(q - 1)*(q - 2)
def DW (u:ℤ) :ℤ :=
 if u<0 then 0 else c5h (u/6) (u % 6)
theorem afw (u:ℤ) (hu:u≤0) :DW u=0:= by
 rcases lt_or_eq_of_le hu with h | rfl
 · simp [DW,h]
 · decide
private theorem b0m (u:ℤ) :
   DW (u+1) - DW u=24*aU u:= by
 by_cases h:u<0
 · rw [afw _ (by omega),afw _ (by omega)]
   simp [aU ,h]
 have hd:=coI u (by omega)
 have hq: (u+1)/6=u/6+(u % 6+1)/6:= by omega
 have hr : (u+1) % 6=(u % 6+1) % 6:= by omega
 simp only [DW,h,show ¬ u+1<0 by omega,mD,hq,hr]
 have hlo:0≤u % 6:= by omega
 have hhi:u % 6<6:= by omega
 generalize u % 6=r at hd hlo hhi ⊢
 interval_cases r <;> norm_num [c5h,coH] at hd ⊢ <;>
   linear_combination -12*hd
theorem b0n (a :ℤ) (n:ℕ) :
   24*(∑ j∈cy n,aU (a+(j:ℤ))) =
    DW (a+n) - DW a := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [Finset.sum_range_succ,mul_add,ih,Nat.cast_succ,← add_assoc,← b0m]
   ring
end aRR
end
section
namespace aRR
open xE GI
private def cfM (s cut:ℕ) :ℤ :=
 24*(((4650 - s - cut:ℕ) :ℤ)*gd (s :ℤ) 1650 -
  ∑ x∈cy (1650 - cut),gd (s :ℤ) ((cut + x :ℕ) :ℤ)) +
  DW ((cut:ℤ)-(3000 - s))
private def bqF (s :ℕ) :ℕ :=
 if s<1549 then 1650 else if s<1603 then 1649 else if s<1641 then 1648 else 1647
private def cV (s :ℕ) :ℤ:=cfM s (bqF s)
private def total (start:ℕ) :ℕ→ℤ
 | 0=>0
 | n+1=>total start n+cV (start+n)
private theorem asB (start n:ℕ) :
   total start n = ∑ j∈cy n,cV (start+j) := by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,Finset.sum_range_succ,ih]
private theorem esi (s m n:ℕ) :
  total s (m+n)=total s m+total (s+m) n:= by
 simp only [asB,lJ,Nat.add_assoc]
private theorem add {s a b:Nat} {x y :Int}
  (ha :total s a=x) (hb:total (s+a) b=y) :total s (a+b)=x+y := by
 rw [esi,ha,hb]
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end
end aRR
end
section
namespace aAZ
open xE
open aRR (DW b0n)
private def aAD (q r :ℤ) :ℤ :=
 12*q^3+(21+6*r)*q^2+(11+7*r+r^2)*q+2+r+r^2
private theorem XK (x :ℤ) :2*(x*(x - 1)/2)=x*(x - 1) := by
 have h: (2 :ℤ)∣x*(x - 1) := by
  rcases oD x with hx | hx
  · exact oq (by omega : (2 :ℤ)∣x) _
  · exact ox (by omega : (2 :ℤ)∣x - 1) _
 rw [mul_comm,nI h]
private theorem bPo (u:ℤ) (hu:0≤u) :
  2*aU u=aAD (u/6) (u % 6) := by
 let q:=u/6
 let r :=u % 6
 simp only [aU,nq (not_lt.mpr hu)]
 change 2*(1+r*(r+1)/2+q*(22+7*r+r*(r - 1)/2) +
  (57+6*r)*(q*(q - 1)/2)+6*q*(q - 1)*(q - 2))=aAD q r
 have h:=XK (r+1)
 rw [show (r+1)*(r+1 - 1)=r*(r+1) by ring] at h
 unfold aAD
 linear_combination h+q*XK r+(57+6*r)*XK q
theorem azV (a j:ℤ) :
  DW (a - j) - DW (a-(j+1))=24*aU (a - 1 - j) := by
 have h:=(b0n (a - 1 - j) 1).symm
 simp only [Finset.sum_range_one,Nat.cast_zero,add_zero,Nat.cast_one] at h
 convert h using 1
 ring_nf
theorem Jc (u:ℤ) (hu:u<0) :aU u=0:= by
 simp only [aU,lz hu]
def aej (d u:ℤ) :ℤ :=
  aU u - aU (u - d - 1) - aU (u - d - 2) -
    aU (u - d-3)
theorem anW (d u:ℤ) (hd:2≤d) (hu:u≤2*d+2) :
   gd d u=aej d u:= by
 by_cases hn:u<0
 · simp only [gd,hn,decide_true,Bool.or_true,ite_true,aej,
    Jc u hn,Jc (u - d - 1) (by omega),
    Jc (u - d - 2) (by omega),Jc (u - d-3) (by omega),
    n5]
 simp only [gd,aej,show ¬ d<0 by omega,hn,
   decide_false,Bool.false_or,Bool.false_eq_true,mD ,oy  (by omega :u≤3*d),
   show aU  (u - 2*d-3)=0 by simp [aU ,show u - 2*d-3<0 by omega],
   show aU  (u - 2*d-4)=0 by simp [aU ,show u - 2*d-4<0 by omega],
   show aU  (u - 2*d - 5)=0 by simp [aU ,show u - 2*d - 5<0 by omega],
   show aU  (u-3*d-6)=0 by simp [aU ,show u-3*d-6<0 by omega],
   add_zero,n5 ]
theorem bwI (d u:ℤ) (h:u≤d) :aej d u=aU u:= by
 simp only [aej,Jc (u - d - 1) (by omega),
  Jc (u - d - 2) (by omega),Jc (u - d-3) (by omega),n5 ]
def amM (d t:ℤ) :ℤ :=
 DW t - DW (t - (d+1)) - DW (t - (d+2)) - DW (t - (d+3))
theorem aQt (d a j:ℤ) :
   amM d (a - j)-amM d (a-(j+1))=24*aej d (a - 1 - j) := by
 unfold amM aej
 have h (k :ℤ) :
     DW (a - j - k) - DW (a-(j+1) - k)=24*aU (a - 1 - j - k) := by
   convert azV (a - k) j using 1 <;> ring_nf
 rw [show a - 1 - j - d - 1=a - 1 - j-(d+1) by ring,
   show a - 1 - j - d - 2=a - 1 - j-(d+2) by ring,
   show a - 1 - j - d-3=a - 1 - j-(d+3) by ring]
 linear_combination (norm:=ring_nf) azV a j - h (d+1) - h (d+2) - h (d+3)
theorem bD6 (u v :ℤ) (h:u≤v) (hv :v≤1650) :
  aU u≤aU v := by
 have he (x :ℤ) (hx :x≤1650) :gd 1650 x=aU x :=
  (anW _ _ (by decide) (by omega)).trans (bwI _ _ hx)
 rw [← he u (h.trans hv),← he v hv]
 exact GI.anX 1650 h
end aAZ
end
section
namespace aFM
open xE GI
def xY (u:ℤ) :ℤ :=
 if u<0 then 0 else u*(u*(2*u+21)+66)/72+1
def aUK (d u:ℤ) :ℤ :=
  if d<0 || u<0 then 0 else
    let v :=min u (3*d)
    if v≤d then xY v else
      let a :=v - d
      let first:=xY v - xY (a - 1) - xY (a - 2) -
        xY (a-3)
      if v≤2*d+2 then first else
        let b:=v - 2*d
        first + xY (b-3) + xY (b-4) + xY (b - 5)
def a7s (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>a7s f n+f n
end aFM
end
section
namespace ac3
noncomputable section
open cu gT pI
open scoped Classical
def aT1 (I:Ideal c9) (P:Jet) :Finset (Ideal c9) :=
 (I ⊔ Ideal.span {iJ P}).minimalPrimesFinset
def aYy (Q:Ideal c9) :Prop :=
  ∀ i:Fin 2,IsAlgebraic FX
    (Ideal.Quotient.mk Q (MvPolynomial.X (Fin.castLE (by decide :2≤4) i)))
def aOS (I:Ideal c9) (P:Jet) :Finset (Ideal c9) :=
 (aT1 I P).filter fun Q => ¬ aYy Q
def a2T (I:Ideal c9) (P:Jet) :Finset (Ideal c9) :=
 (aT1 I P).filter aYy
end
end ac3
end
