import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.DdZENrqsd
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.DdAE
import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.DdZgdIx1d
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.DdZZ0RELd
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
namespace P1_6_4_1

open scoped BigOperators
end P1_6_4_1
end
section
open _root_ renaming Finset.sum_congr→cy,Nat.cast_sum→lJ,P5_8.bo8→lI
section
set_option autoImplicit true
namespace P5_8
noncomputable section
open i4 PolynomialDifferential Finset
open scoped Polynomial
def c1 :Prop :=
 aWw small 84≤232369∧Moments small 12850 610160 205216
def c2 :Prop :=
  aWw bo8 6252≤0x62703852f02 ∧
    Moments bo8 0x12e20e912 0x1098bf757c00 0x5e143ee4d6c
end
end P5_8
end
section
set_option autoImplicit true
namespace P5_8_2
open i4 Finset
def bbW (c:ℕ) :=range (1959 - 2*c+1)
def len (b c:ℕ) :=6251-(b+c)+1
theorem cast_len {b c:ℕ} (hc:c∈range 980) (hb:b∈bbW c) :
  (len b c:ℤ)=6252 - b - c:= by
 have hc' := mem_range.mp hc
 have hb' := mem_range.mp hb
 change b<1959 - 2*c+1 at hb'
 unfold len
 omega
private def boxSum (f :ℤ→ℤ→ℤ) :ℤ :=
 ∑ c∈range 980,∑ b∈bbW c,f b c
private theorem card_box : (P5_8.bo8.E.card:ℤ)=boxSum (fun b c=>6252-b-c) := by
 simp only [lI,aH1,card_sigma,card_range,lJ,boxSum]
 exact cy rfl fun c hc=>cy rfl fun b hb=>cast_len hc hb
private theorem twice_grade {b c:ℕ} (hc:c∈range 980) (hb:b∈bbW c) :
  2*(∑ a∈range (len b c),(a+b+c))=len b c*(6251+b+c) := by
 have hc' := mem_range.mp hc
 have hb' : b<1959 - 2*c+1 :=mem_range.mp hb
 have hl:len b c - 1+(b+c)=6251 := by
  unfold len
  omega
 calc
  _=(∑ a∈range (len b c),a)*2+len b c*(2*(b+c)) := by
    simp only [add_assoc,sum_add_distrib,sum_const,card_range,smul_eq_mul]
    ring
  _=len b c*(len b c - 1+(b+c))+len b c*(b+c) := by
    rw [sum_range_id_mul_two]
    ring
  _ = _:= by rw [hl]; ring
private theorem grade_box :
  (2 :ℤ) * ↑(∑ j∈P5_8.bo8.E,j.q)=boxSum (fun b c=>(6252-b-c)*(6251+b+c)) := by
 simp only [lI,aH1,sum_sigma,Jet.q,Jet.a,Jet.b,Jet.c,lJ,boxSum]
 rw [mul_sum]
 refine cy rfl fun c hc => ?_
 rw [mul_sum]
 refine cy rfl fun b hb => ?_
 have h:=congrArg (fun n:ℕ=>(n:ℤ)) (twice_grade hc hb)
 push_cast at h
 rw [cast_len hc hb] at h
 simpa only [Nat.cast_add,len] using h
private theorem index_box :
  (↑(∑ j∈P5_8.bo8.E,j.v) :ℤ)=boxSum (fun b c=>(6252-b-c)*(b+2*c)) := by
 simp only [lI,aH1,sum_sigma,Jet.v,Jet.b,Jet.c,sum_const,card_range,
  smul_eq_mul,lJ,Nat.cast_mul,boxSum]
 refine cy rfl fun c hc=>cy rfl fun b hb => ?_
 rw [show (↑(6251-(b+c)+1) :ℤ)=6252-b-c from cast_len hc hb]
 push_cast
 rfl
def poly (a b c d x :ℤ) :=a+b*x+c*x^2+d*x^3
def sumFormula (a b c d n:ℤ) :=
 12*a*n+6*b*n*(n-1)+2*c*n*(n-1)*(2*n-1)+3*d*n^2*(n-1)^2
theorem gvl (a b c d:ℤ) (n:ℕ) :
   12*(∑ i∈range n,poly a b c d i)=sumFormula a b c d n:= by
 induction n with
 | zero=>simp [sumFormula]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
   unfold poly sumFormula
   ring
private theorem box_value (f :ℤ→ℤ→ℤ) (a b c:ℤ→ℤ)
   (r s t u value :ℤ)
   (hcoeff : ∀ x y,f x y=poly (a y) (b y) (c y) 0 x)
   (hrow : ∀ y,sumFormula (a y) (b y) (c y) 0 (1960-2*y)=poly r s t u y)
   (hend:sumFormula r s t u 980=144*value) :boxSum f=value := by
 have hs :12*boxSum f = ∑ y∈range 980,poly r s t u y := by
   unfold boxSum
   rw [mul_sum]
   refine cy rfl fun y hy => ?_
   have hn: (↑(1959-2*y+1) :ℤ)=1960-2*y := by
     have :=mem_range.mp hy
     omega
   simp only [bbW,hcoeff]
   rw [gvl,hn]
   exact hrow _
 have h:=gvl r s t u 980
 change 12*(∑ y∈range 980,poly r s t u y)=sumFormula r s t u 980 at h
 rw [← hs,hend] at h
 omega
private theorem card_value :boxSum (fun b c=>6252-b-c)=0x12e20e912 := by
 apply box_value _ (fun y=>6252-y) (fun _ => -1) (fun _=>0)
   0x7643af0 (-126540) 0 0
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
private theorem grade_value :
   boxSum (fun b c=>(6252-b-c)*(6251+b+c))=0x21317eeaf800:= by
 apply box_value _ (fun y=>6252*6251+y-y^2) (fun y=>1-2*y) (fun _ => -1)
   0xcf039f1140 (-0x35294810) (-23520) 8
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
private theorem index_value :
   boxSum (fun b c=>(6252-b-c)*(b+2*c))=0x5e143ee4d6c:= by
 apply box_value _ (fun y=>(6252-y)*2*y) (fun y=>6252-3*y) (fun _ => -1)
   0x1a8733eef0 23112868 (-150060) 8
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
theorem bsK:P5_8.Moments lI 0x12e20e912 0x1098bf757c00 0x5e143ee4d6c:= by
 have ht:=card_box.trans card_value
 have hs :=grade_box.trans grade_value
 have hv :=index_box.trans index_value
 exact ⟨by omega,by omega,by omega⟩
end P5_8_2
end
section
set_option autoImplicit true
namespace qxVnKgd
open P5_8_2 Finset
def T (n:ℤ) :ℤ:=(tri n.toNat :ℤ)
def H (w:ℤ) :ℤ:=T ((w+1)/2)+T (w/2)
def P (u:ℕ) :ℤ:=1959-(u:ℤ)
def O (q u:ℕ) :ℤ:=6559-(q:ℤ)-u
def A (p o:ℤ) :ℤ:=max 0 (2*p+o-3919)
def low (q d o:ℤ) :ℤ:=T (d+1)-(max 0 (q-979))^2 - H o
def high (p o a c:ℤ) :ℤ :=
 let n:=980-a-c
 n*(n+1) - H (p-2*a-c) - H (o-a-2*c)
def line (e :ℕ) :Multiplicities := ![0,0,0,0,e,0]
def pair (a c:ℕ) :Multiplicities := ![a,0,0,a,0,c]
def pick (q u:ℕ) :Multiplicities :=
 if q<1959 then line (O q u - q).toNat
 else pair (A (P u) (O q u)).toNat (A (O q u) (P u)).toNat
abbrev Cell:=Σ _:ℤ,ℤ
def region (i:Fin 7) :Finset Cell :=
 match i.val with
 | 0=>(Icc 0 1958).sigma fun q=>Icc 1 q
 | 1=>(Icc 0 1958).sigma fun q=>Icc (max 0 (2*q-1959)) (q-1)
 | 2=>(Icc 1 1959).sigma fun o=>Icc (o-2641) 0
 | 3=>(Icc 1 1856).sigma fun p=>Icc (max 1 (p-1651)) (min (3919-2*p) ((3919-p)/2))
 | 4=>(Icc 1307 1959).sigma fun p=>Icc (max (3920-2*p) (p-1651)) ((3919-p)/2)
 | 5=>(Icc 1307 1959).sigma fun p=>Icc (3920-2*p) ((3919-p)/2)
 | _=>(Icc 2614 2939).sigma fun s=>Icc (3920-s) (2*s-3920)
def score (i:Fin 7) (x :Cell) :ℤ :=
 let p:=x.1
 let o:=x.2
 match i.val with
 | 0=>low p p o
 | 1=>low p o o
 | 2=>961380 - H p
 | 3=>high p o 0 0
 | 4 | 5=>high p o (2*p+o-3919) 0
 | _=>(2939-p)*(2940-p)
end qxVnKgd
end
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open P5_8 (Jn Equation caps bo8 smallCaps donorCaps Gq tariffShape properDegree componentCap)
open scoped Polynomial BigOperators
































structure FactorCharts (L R:BL 2) where
  count:ℕ
  factor :Fin count→Equation
  bKQ: (∏ i,apQ.initial (factor i))∣L
  charts : ∀ i,P5_8.ProperCharts (apQ.initial (factor i)) R





end
end P6_8
end
