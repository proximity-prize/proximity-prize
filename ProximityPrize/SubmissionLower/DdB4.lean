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
import ProximityPrize.SubmissionLower.DdP6Defs
import ProximityPrize.SubmissionLower.DdA2
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit true
section
namespace aZw
noncomputable section
open Polynomial

open scoped BigOperators
end
end aZw
end
section
namespace aZw
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark

theorem azg (errors m x gap cap:ℕ)
    (hm:0< m) (hg:0<gap) (hx :gap≤x) (he :0<errors)
    (hsecond: (m*x)^2≤(x+errors)*(m*(x+(m-1)*(x-gap))))
    (hfirst:m*x≤(x+errors)*cap) :
    gap*m≤errors*cap+gap:= by
  have hcancel:m*x^2≤(x+errors)*(x+(m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _=(m*x)^2 := by ring
      _≤_:=hsecond
      _ = _:= by ring
  have hM: ((m - 1 :ℕ) :ℤ)=(m:ℤ)-1 :=Int.ofNat_sub (by omega)
  have hX: ((x - gap:ℕ) :ℤ)=(x :ℤ)-gap:=Int.ofNat_sub hx
  have hcancelZ:=Int.ofNat_le.mpr hcancel
  push_cast [hM,hX] at hcancelZ
  have hfirstZ:=Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ: ((m:ℤ)*errors-((m:ℤ)-1)*gap)*x ≥
      ((m:ℤ)-1)*errors*gap:= by
    nlinarith only [hcancelZ]
  have firstZ: ((m:ℤ)-(cap:ℤ))*x≤(cap:ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ: (errors :ℤ)*cap+gap<(gap:ℤ)*m:= by exact_mod_cast h
  have hbad: (cap:ℤ)*errors<((m:ℤ)-1)*gap:= by nlinarith only [hbadZ]
  have hxpos :0<(x :ℤ) := by omega
  have cmp: (m:ℤ)*errors-((m:ℤ)-1)*gap<((m:ℤ)-(cap:ℤ))*errors := by
    linarith only [hbad]
  have left:=mul_lt_mul_of_pos_right cmp hxpos
  have right:=mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible :=secondZ.trans_lt (left.trans_le (show
      ((m:ℤ)-(cap:ℤ))*errors*x≤(cap:ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger :=mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible,bigger]
end
end aZw
end
section
set_option backward.isDefEq.respectTransparency false
namespace atp
noncomputable section

open Polynomial
open scoped Polynomial
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open DdK1 (I)
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open DdK1 (I)
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace dnG
noncomputable section
open cu Polynomial
open scoped BigOperators Polynomial
end
end dnG
end
section
namespace bjU

open Finset
open scoped BigOperators
end bjU
end
section
namespace bjU

open Finset
open scoped BigOperators
end bjU
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace dnk
noncomputable section
open cu
end
end dnk
end
