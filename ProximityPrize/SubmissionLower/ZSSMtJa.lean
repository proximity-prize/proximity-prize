import Mathlib.RingTheory.LaurentSeries
import ProximityPrize.SubmissionLower.ZzQsYjc
import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
section
namespace qb0hmCe
noncomputable section
open Finset Polynomial qQ9yWTb
open P5 (K)
open P5_7_1 (Input)
open P5_7_7 (phys)
open cu (L FX)
open E7 (CurveField CurvePlace poleOrder Gb)
open scoped BigOperators Classical WithZero
structure CurveModel (q:Curve) where
 E :Type
 [field :Field E]
 [algebra :Algebra L E]
 seed :Fin 2→E
 curve :CurveField L E
 equation :RingHom.ker (MvPolynomial.eval₂Hom (algebraMap L E) seed)=Ideal.span {q}
 generates :IntermediateField.adjoin L (Set.range seed) = ⊤
 co6 : ∀ i,(∑ᶠ v :CurvePlace L E,poleOrder v.value (seed i))≤q.totalDegree
attribute [instance] CurveModel.field CurveModel.algebra
def coeffHeight {E :Type} [Field E] [Algebra L E] (f :E[X][X]) :ℕ :=
  Gb L E (fun ij:Fin (f.natDegree+1) ×
      Fin ((f.support.sup fun i=>(f.coeff i).natDegree)+1) =>
    (f.coeff ij.1).coeff ij.2)
def cLN {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] LaurentSeries L)
    (j:ℤ) (f :E[X][X]) :L[X][X] :=
  f.sum fun i g=>monomial i (g.sum fun k c=>monomial k ((a c).coeff j))
def specialize (f :L[X][X]) (P Q:L[X]) :FX:=f.eval₂ phys (phys P/phys Q)
def zD {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] LaurentSeries L)
    (f :E[X][X]) (P Q:L[X]) :FX :=
  -(specialize (cLN a 1 f) P Q/specialize (cLN a 0 f).derivative P Q) *
    phys Q^2
structure Sheet {x :Input} {U:Finset K} (J:WordChart x U) {q:Curve}
   (C:CurveModel q) where
 f :C.E[X][X]
 irreducible :Irreducible f
 positive :0<f.natDegree
 normalized: (f.coeff f.natDegree).leadingCoeff=1
 marks :Finset K
 Bp:marks⊆U
 atPlace : ∀ γ∈marks,C.E →ₐ[L] LaurentSeries L
 place :K→CurvePlace L C.E
 distinct :Set.InjOn place (marks :Set K)
 value : ∀ γ (hγ:γ∈marks) c,
   (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
 arc : ∀ γ (hγ:γ∈marks),∃ a :Fin 2→PowerSeries L,
   (∀ i,atPlace γ hγ (C.seed i)=(a i:LaurentSeries L)) ∧
   (∀ i,PowerSeries.constantCoeff (a i)=site x γ i) ∧
   (∃ i,PowerSeries.coeff 1 (a i)≠0)
 integral : ∀ γ (_:γ∈marks) i j,
   (place γ).value ((f.coeff i).coeff j)≤1
 root : ∀ γ (hγ:γ∈marks),specialize (cLN (atPlace γ hγ) 0 f) (J.P γ) (J.Q γ)=0
 separable : ∀ γ (hγ:γ∈marks),
   ((cLN (atPlace γ hγ) 0 f).map phys).Separable
 simple : ∀ γ (hγ:γ∈marks),
   specialize (cLN (atPlace γ hγ) 0 f).derivative (J.P γ) (J.Q γ)≠0
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈marks,den γ≠0
 reduced : ∀ γ∈marks,IsCoprime (num γ) (den γ)
 formula : ∀ γ (hγ:γ∈marks),
   phys (num γ)/phys (den γ)=zD (atPlace γ hγ) f (J.P γ) (J.Q γ)
abbrev Sheet.d {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
 (S:Sheet J C) :=S.f.natDegree
abbrev Sheet.h {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
 (S:Sheet J C) :=coeffHeight S.f
def poleOrderAt {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve}
    {C:CurveModel q} (S:Sheet J C) (γ:K) :ℕ :=
  max (S.den γ).natDegree ((S.num γ).natDegree-P5_7_7.relativeDegree J γ)
structure SiteTarget where
 center :L
 coord:Fin 2
 a :L
 b:L
 c:L
 d:L
def SiteTarget.det (R:SiteTarget) :L:=R.a*R.d-R.b*R.c
def SiteTarget.height (R:SiteTarget) (q:Curve) :ℕ :=
 if R.b=0∧R.d=0 then 0 else q.totalDegree
def Sheet.direction {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) (γ:K) (i:Fin 2) :L :=
  if h:γ∈S.marks then (S.atPlace γ h (C.seed i)).coeff 1 else 0
end
end qb0hmCe
end
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def r0:=p! 1622 338 0x2b13d5db82 36 8 0x2557bac81fa3d94305a439bb3893d5cca80a91afca8094002ca8054fb4df920f1429240
private def r1 :=p! 1672 344 0x30260d2131 36 8 0x5948ed102c5398e116d35df48aa61e0d100b74ccd1009d5b8d10058e1546460f9b0f840
private def d2_0:=s! 1724 358 358 36 8 0xc3147fe03df20d9bf8531cccf4bcf13f080c9a6af080a97c1f0805d64eebd910275b440
private def d2_1 :=s! 1724 358 2406 23 1 0x6111cf
private def r2 :=j! 1724 358 0x36cfb8a9fb [d2_0,d2_1]
private def d3_0:=s! 1769 376 376 36 8 0x15acb47a05159339a79dbe7740ad42b03980dc8b33980b5cb63980618300f1a10a0c4340
private def d3_1 :=s! 1769 376 2424 28 1 0x82edda5
private def r3:=j! 1769 376 0x3ddecad1d0 [d3_0,d3_1]
private def d4_0:=s! 1826 380 380 36 8 0x2222f155c674c4853db7924060be9e799d00ece199d00c03b99d0065c81d93d113a8d640
private def d4_1 :=s! 1826 380 2428 30 1 0x2352380c
private def r4 :=j! 1826 380 0x4513e15f2d [d4_0,d4_1]
private def d5_0:=s! 1830 379 379 36 8 0x22daefb996881edbfbb8e420806eacf16700ed73f6700c098d6700660649b85114558240
private def d5_1 :=s! 1830 379 2427 30 1 0x25684622
private def r5:=j! 1830 379 0x456bf07881 [d5_0,d5_1]
private def d6_0:=s! 2040 424 424 37 8 0x3c1732fadb77342125e610a9ca01507a8e5009da7e72803c41439400ed7707fd4137bec840
private def d6_1 :=s! 2040 424 2472 34 2 0xa47f2ac272047780
private def r6:=j! 2040 424 0x6b739dc24c [d6_0,d6_1]
private def d7_0:=s! 2198 455 455 37 8 0x6c75d8692d2ec5d55af273b8d401a29706a00bc4823500456261a801058b1a174152635240
private def d7_1 :=s! 2198 455 2503 35 3 0x24207ed0d51bc37068eeaa3bf
private def r7:=j! 2198 455 0x904fa277dd [d7_0,d7_1]
private def d8_0:=s! 2234 472 472 37 8 0x7c15fec0b5b4aa6c583655881401bd10e0a00c62ac0500481e8828010b12b9fbc158755e40
private def d8_1 :=s! 2234 472 2520 36 3 0x22869e4b2792bf86080e00ec9f
private def r8:=j! 2234 472 0x9c78f462de [d8_0,d8_1]
def dataE :Array aqm := #[
 r0,r1,r2,r3,r4,r5,r6,r7,r8
]
end qpECY2d
end
