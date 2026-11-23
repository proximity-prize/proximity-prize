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
import ProximityPrize.SubmissionLower.AC
set_option Elab.async false
set_option autoImplicit true
section
namespace B7
noncomputable section
open aR MvPolynomial
open scoped BigOperators Polynomial
abbrev rS:=Fin bf
abbrev jo:=MvPolynomial rS ao
abbrev dF:=FractionRing ao[X]
abbrev mK:=MvPolynomial rS dF
abbrev nW:=MvPolynomial (Fin 3) dF
def Gp (P:ao[X]) :rS→ao:= fun a=>P.coeff a.val
def KT {F:Type*} [Field F] (x :F) (j:ℕ) :MvPolynomial rS F :=
 ∑ a :rS,C ((a.val.choose j:F)*x^(a.val - j))*MvPolynomial.X a
def PV:dF:=algebraMap ao[X] dF Polynomial.X
def GZ (f :af 3) :nW :=
 MvPolynomial.map (algebraMap ao[X] dF) f
def oV (P:Ideal jo) :Ideal mK :=
 P.map (MvPolynomial.map (algebraMap ao dF))
def tO:nW →ₐ[dF] mK :=
 MvPolynomial.aeval fun j=>KT PV j.val
structure XP (P:Ideal jo) (g d:nW) :Prop where
 prime :P.IsPrime
 equation_ne :g≠0
 image : (oV P).comap tO=Ideal.span {g}
 regular_open:d∉Ideal.span {g}
 recover : ∀ a :rS,∃ (v :nW) (m:ℕ),
  tO d^m*MvPolynomial.X a - tO v∈oV P
end
end B7
end
section
namespace YY
noncomputable section
open K1 cu gT Polynomial
def Si (I:Ideal Ambient) :Ideal kM:=I.comap oi
def xg (I:Ideal Ambient) :Ideal aZ:=(Si I).comap pZ
def U7:L →+* FX :=
 (algebraMap L[X] FX).comp (Polynomial.C:L →+* L[X])
def by9 (P:Ideal aZ) :Prop :=
  ∃ C:MvPolynomial (Fin 2) L,Irreducible C ∧
    P=Ideal.span {MvPolynomial.map U7 C}
def bAG (I:Ideal Ambient) :Prop :=
 I.IsPrime∧ringKrullDim (gk I)=1 ∧
 Module.Finite aQ (rM I) ∧
 0<Module.finrank aQ (rM I)
def aef (I:Ideal Ambient) :ℕ:=Module.finrank aQ (rM I)
def a9E (I:Ideal Ambient) :ℕ:=Module.finrank aQ (as2 I)
end
end YY
end
