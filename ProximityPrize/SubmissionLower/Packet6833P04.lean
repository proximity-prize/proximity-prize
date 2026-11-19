import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Int.Associated
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Real.Embedding
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.GameAdd
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.NormalClosure
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.ZMod
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.GroupTheory.CosetCover
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import ProximityPrize.SubmissionLower.Packet6833P03
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart3
namespace AKN
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD AIO
open MovingFiberThreeSources6811 (direction weight)
open LF WC _Q7
open OT
variable {K E:Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta:GenericField K→+*E)
local notation "Omega" =>E
local notation "OmegaT" =>GenericField E
local notation "phi" =>RingHom.comp (RCN135.coefficientEmbedding E) (codeMap eta)
local notation "lift" =>MvPolynomial.map (RCN135.coefficientEmbedding E)
local instance:Algebra (RatFunc E) OmegaT:=CPM E
local instance:IsScalarTower E (RatFunc E) OmegaT:=target_tower E
end
end AKN
end MergedPart3
section MergedPart4
namespace APJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN084 RCN095 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN341 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD LF
open MovingFiberThreeSources6811 (direction weight)
open _Q7 OT
open AGD AKN
open ARR YE AVZ
variable {K E:Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta:GenericField K→+*E)
local notation "Poly" =>MvPolynomial (Fin 3) E
theorem DHH (N H G:Poly):filteredCut 0 (fun _=>N) H G=N:=by
  simp [filteredCut,Fin.sum_univ_one]
theorem GOM (N Q A:Poly):
    ZN 0 (fun _=>N) Q A=MvPolynomial.map (RCN135.coefficientEmbedding E) N:=by
  simp [ZN,RCN207.eliminatedCut,filteredCut,Fin.sum_univ_one]
theorem EFP
    (F:MvPolynomial (Fin 4) K) (SZ:MovingFiberThreeSources6811.Source F)
    (G N:Poly) (hG:G≠0) (hGF:G∣BXI eta F)
    (hR:frozenH eta F∈Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set Poly))
    (q:FlagDegree) (hN:RCN095.PolynomialInFlag q N)
    (B:SliceBudgets G N (frozenH eta F) q)
    (active:Finset (ANR G N (frozenH eta F)))
    (hlead: ∀a∈active,SZ.leading (codeMap eta)∉a.2.1)
    (scale z u v:ℕ)
    (hbound: ∀Q A:Poly,(2:Poly)*A≠0→
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q→RCN095.PolynomialInFlag unitYZFlag A→
      AGN eta F SZ Q A scale z u v):
    ∃moving: ∀a:active,RD a.val.2.1 (frozenH eta F) (frozenG eta F),
      (∀a:active,(moving a).zCost=(B.unit a.val.1).zCost a.val.2∧
        (moving a).yzCost=(B.unit a.val.1).yzCost a.val.2∧
        (moving a).allCost=(B.unit a.val.1).allCost a.val.2)∧
      scale*(∑ a:active,(moving a).movingCost)≤q.zOnly*z+q.yz*u+q.all*v:=by
  let P (a:active):=a.val.2.1
  let base (a:active):=B.base a.val.1 a.val.2
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩:=BJG P base (frozenH eta F) (frozenG eta F)
  let moving (a:active):RD (P a) (frozenH eta F) (frozenG eta F):={
    zCost:=(B.unit a.val.1).zCost a.val.2
    yzCost:=(B.unit a.val.1).yzCost a.val.2
    allCost:=(B.unit a.val.1).allCost a.val.2
    movingCost:=RCN344.SeparableCoordinate.degree E (RCN002.CoordinateField E (P a)) (projection a)
    zPole:=(B.unit a.val.1).zPole a.val.2
    yzPole:=(B.unit a.val.1).yzPole a.val.2
    allPole:=(B.unit a.val.1).allPole a.val.2
    movingPole:=by
      intro W
      calc
        _=∑ nu∈W,RCN346.poleOrder_p19 E (RCN002.CoordinateField E (P a)) nu
            (RCN344.SeparableCoordinate.value E (RCN002.CoordinateField E (P a)) (projection a)):=by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj a).2.2 nu).symm
        _≤_:=RCN344.SeparableCoordinate.AMH E (RCN002.CoordinateField E (P a)) (projection a) W}
  refine ⟨moving,fun _=>⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hactive:Nonempty active
  · let a0:active:=Classical.choice hactive
    have hAne:A≠0:=by intro hz;exact (hproj a0).1 (hz ▸ (P a0).zero_mem)
    have h2:(2:Poly)≠0:=(CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
    let factor (a:active):Poly:=a.val.1.val
    let old (a:active):CWU eta F (factor a) 0 (fun _=>N):=
      ⟨P a,by simpa only [DHH] using a.val.2.property⟩
    have hinj:Function.Injective (fun a:active=>(old a).1):=by
      intro a b hab
      apply Subtype.ext
      exact FBW G N (frozenH eta F) hG hR hab
    have hcut:RCN095.PolynomialInFlag q (ZN 0 (fun _=>N) Q A):=by
      rw [GOM]
      exact inFlag_map _ hN
    have hh:=CRH eta F SZ factor
      (fun a=>(RCN084.activeFactors_spec G N a.val.1).2.1.trans hGF)
      Q A scale z u v (hbound Q A (mul_ne_zero h2 hAne) hQ hA)
      0 (fun _=>N) q hcut old hinj (fun a=>hlead a.val a.property)
      (fun a=>(hproj a).1) projection (fun a=>(hproj a).2.1)
    exact hh
  · letI:IsEmpty active:=⟨fun a=>hactive ⟨a⟩⟩
    simp
end
end APJ
end MergedPart4
section MergedPart7
namespace RL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 35000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open FA JN IB
open PR BD HK HFreeDir6813
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
open _Q7
local notation "w" =>RCN326.w
def price (W:FlagDegree) (z u v:ℕ):ℕ:=W.zOnly*z+W.yz*u+W.all*v
theorem GEV (W:FlagDegree) (z u v:ℕ):
    (∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*price (MovingFiberThreeSources6811.direction j) z u v)=price W z u v:=by
  simp [Fin.sum_univ_three,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,price,unitZFlag,unitYZFlag,unitAllFlag]
end
end RL
end MergedPart7
section MergedPart8
namespace TW
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN336 RCN338 RCN339 RCN341
open FA IB JN
open BD HK
open MovingFiberThreeSources6811 (direction weight)
open HFreeDir6813 RL CB
open _Q7
open NL
local notation "w" =>RCN326.w
def stageScale {K:Type} [Field K] {F:MvPolynomial (Fin 4) K} (SZ:MovingFiberThreeSources6811.Source F) (delta:ℕ):ℕ:=SZ.d*delta
end
end TW
end MergedPart8
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart2
namespace GF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN084 RCN095
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
def CumulativeLe (p q:FlagDegree):Prop:=
  p.all≤q.all∧p.yz+p.all≤q.yz+q.all∧p.zOnly+p.yz+p.all≤q.zOnly+q.yz+q.all
theorem ELU (p p' q r:FlagDegree) (h:CumulativeLe p p'):
    flagMixed p q r≤flagMixed p' q r:=by
  have hh:=RCN084.sum_flagMixed_le_of_cumulative (fun _:Fin 1=>p) p' q r
    (by simpa using h.1) (by simpa using h.2.1) (by simpa using h.2.2)
  simpa using hh
theorem FDM (p q r:FlagDegree):flagMixed p q r=flagMixed q p r:=by
  simp only [flagMixed]
  ring
theorem CAB (p q p' q' r:FlagDegree)
    (hp:CumulativeLe p p') (hq:CumulativeLe q q'):
    flagMixed p q r≤flagMixed p' q' r:=by
  apply (ELU p p' q r hp).trans
  rw [FDM p' q r,FDM p' q' r]
  exact ELU q q' p' r hq
end
end GF
end MergedPart2
section MergedPart4
namespace BLG
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044
open RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370 RCN351 RCN037 RCN038
variable {Omega J:Type} [Field Omega] [IsAlgClosed Omega] [Fintype J]
local notation "Poly" =>MvPolynomial (Fin 3) Omega
theorem EFI
    (G T H:J→Poly)
    (base: ∀i,∀C:RCN264.RegularComponent Omega (G i) (T i) (H i),RCN341.SeparableLiteralCoordinate C.1)
    (hactive: ∀i,∀C:RCN264.RegularComponent Omega (G i) (T i) (H i),
      D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
        D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
    (hSderiv: ∀i,MvPolynomial.pderiv (1:Fin 3) (G i)≠0)
    (S:Set Omega) (hS:S.Infinite):
    ∃lam mu:Omega,lam∈S∧mu∈S∧
      ∃data: ∀i,JO (base i) (hactive i) (hSderiv i),
        ∀i,(data i).lam=lam∧(data i).mu=mu:=by
 let Family:=(i:J) × RCN264.RegularComponent Omega (G i) (T i) (H i)
 classical
 let E:Family→Type:=
   fun C=>RCN002.CoordinateField Omega C.2.1
 let rY:∀C,E C:=fun C=>coordinate Omega C.2.1 0
 let z:∀C,E C:=fun C=>coordinate Omega C.2.1 2
 let W:∀C,Finset (Place_p19 Omega (E C)):=
   fun C=>OW (base C.1 C.2)
 let baseC:∀C,RCN344.SeparableCoordinate Omega (E C):=
   fun C=>RCN042.literalToSeparableCoordinate (base C.1 C.2)
 obtain ⟨lam,hlamS,hlam0,hlam⟩:=
   RQ E rY z W
     S hS baseC (fun C=>hactive C.1 C.2)
 let U:∀C:Family,
     RCN002.CoordinateField Omega C.2.1:=fun C=>affineU Omega C.2.1 lam
 have hUgate:∀C:Family,
     ∀htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.2.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.2.1))∧
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.2.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.2.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀C:Family,
     Coordinate Omega (RCN002.CoordinateField Omega C.2.1):=
   fun C=>RCN042.coordinateOfGate (U C) (hUgate C)
 have huValue:∀C:Family,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.2.1) (uProjection C)=U C:=
   fun C=>RCN042.coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀(C:Family)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.2.1 2)):=by
   intro C v
   by_cases hv:v∈OW (base C.1 C.2)
   · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=DW
         (base C.1 C.2) v hv 0
     have h2:=DW
         (base C.1 C.2) v hv 2
     have h0le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.2.1 2)=
         v.val (coordinate Omega C.2.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C)≤1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346._Q11 Omega
         (RCN002.CoordinateField Omega C.2.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀C:Family,
     D Omega (RCN002.CoordinateField Omega C.2.1) (coordinate Omega C.2.1 1)≠0∨
       D Omega (RCN002.CoordinateField Omega C.2.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (RCN042.differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀C,E C:=fun C=>coordinate Omega C.2.1 1
 let bad (i:J):Set Omega:={mu | MvPolynomial.pderiv (0:Fin 3) (G i)-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) (G i)=0}
 have hbad:(⋃ i,bad i).Finite:=by
   apply Set.finite_iUnion
   intro i
   have hs:(bad i).Subsingleton:=by
     intro a ha b hb
     exact RCN096.directional_bad_coefficient_subsingleton (G i) (hSderiv i) ha hb
   exact hs.finite
 obtain ⟨mu,hmuS,hmu0,hmu⟩:=
   RQ
     E rS U W (S \ ⋃ i,bad i) (hS.sdiff hbad) baseC hactiveV
 have hmudir (i:J):MvPolynomial.pderiv (0:Fin 3) (G i)-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) (G i)≠0:=by
   intro hh
   exact hmuS.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)
 let V:∀C:Family,
     RCN002.CoordinateField Omega C.2.1:=
   fun C=>coordinate Omega C.2.1 1+mu • U C
 let hV:∀C:Family,
     Transcendental Omega (V C):=fun C=>(hmu C).choose
 let vProjection:∀C:Family,
     Coordinate Omega (RCN002.CoordinateField Omega C.2.1):=fun C=>Sum.inr {
   embedding:=RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.2.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀C:Family,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.2.1) (vProjection C)=V C:=by
   intro C
   exact RCN022.elementEmbedding_variable Omega (RCN002.CoordinateField Omega C.2.1) (V C) (hV C)
 have hvPole:∀(C:Family)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈OW (base C.1 C.2)
   · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=DW
         (base C.1 C.2) v hv 1
     have hY:=DW
         (base C.1 C.2) v hv 0
     have hZ:=DW
         (base C.1 C.2) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C)≤1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346._Q11 Omega
         (RCN002.CoordinateField Omega C.2.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀C:Family,
     Transcendental Omega (affineV Omega C.2.1 mu (mu*lam)):=fun C=>by
   rw [show affineV Omega C.2.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:Family):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.2.1)
         (affineV Omega C.2.1 mu (mu*lam)) (hVAff C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.2.1) (V C) (hV C):=
   RCN116.elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])

 let data (i:J):JO (base i) (hactive i) (hSderiv i):={
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=fun C=>uProjection ⟨i,C⟩
   NV:=fun C=>vProjection ⟨i,C⟩
   uGate:=fun C=>hUgate ⟨i,C⟩
   ZG:=fun C=>(hlam ⟨i,C⟩).choose
   GN:=fun C=>hVAff ⟨i,C⟩
   allFinite:=by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.1
   allSeparable:=by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.2.1
   uValue:=fun C=>huValue ⟨i,C⟩
   allValue:=by
     intro C
     rw [hvValue ⟨i,C⟩]
     simp only [V,U,affineU,affineV,smul_add,smul_smul,add_assoc]
   ACE:=by
     intro C
     rw [hvValue ⟨i,C⟩]
     exact hV ⟨i,C⟩
   uPole:=by
     intro C nu
     rw [huValue ⟨i,C⟩]
     exact huPole ⟨i,C⟩ nu
   allPole:=by
     intro C nu
     rw [hvValue ⟨i,C⟩,hvPole ⟨i,C⟩ nu,huPole ⟨i,C⟩ nu]
   directional:=hmudir i}
 exact ⟨lam,mu,hlamS,hmuS.1,data,fun _=>⟨rfl,rfl⟩⟩
end
end BLG
end MergedPart4
section MergedPart5
namespace BLL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical
open RCN030 RCN086 RCN095 RCN135 RCN136 RCN159 RCN198 RCN243 RCN263 RCN264 RCN275 RCN327 RCN332 RCN341
open RCN095 renaming PolynomialInFlag → BI
open RCN334 RCN089
open BLG
variable {K I J:Type} [Field K] [Fintype J]
variable {p errorCap a b s:ℕ} [CharP (GenericField K) p]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
theorem DYG
    (Gamma:J→Finset K) (x:I→K) (flag:J→FlagDegree)
    (stage: ∀j,FH (RCN135.polynomialEmbedding K) (Gamma j) x p errorCap (flag j) w (support a b s))
    (hproper: ∀j,¬(stage j).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (stage j).F (w+1))
    (hflag: ∀j,(flag j).yz+(flag j).all<p∧(flag j).all<p∧
      (flag j).zOnly+(flag j).yz+(flag j).all<p)
    (hmixed: ∀j,flagMixed (flag j) (RCN263.reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag<p):
    ∃lam mu:GenericField K,
      lam∈Set.range (RCN135.polynomialEmbedding K)∧mu∈Set.range (RCN135.polynomialEmbedding K)∧
      ∃geometry: ∀j,ABN (stage j),
        ∀j,(geometry j).data.lam=lam∧(geometry j).data.mu=mu:=by
  classical
  choose base hactive hZ hdata using fun j=>
    AGZ.UI
      (stage j) (hproper j) (hflag j) (hmixed j)
  obtain ⟨lam,mu,hlam,hmu,data,heq⟩:=EFI
    (fun j=>(stage j).G)
    (fun j=>RCN089.reducedGlobalTailCut (RCN135.polynomialEmbedding K) (support a b s) (stage j).F (w+1))
    (fun j=>CR (RCN135.polynomialEmbedding K) (stage j).F)
    base hactive (fun j=>RCN315.EH (stage j))
    (Set.range (RCN135.polynomialEmbedding K))
    (Set.infinite_range_of_injective (RCN135.polynomialEmbedding_injective K))
  let geometry (j:J):ABN (stage j):={
    base:=base j
    hactive:=hactive j
    hZ:=hZ j
    data:=data j
    lam_poly:=by rw [(heq j).1];exact hlam
    mu_poly:=by rw [(heq j).2];exact hmu}
  exact ⟨lam,mu,hlam,hmu,geometry,heq⟩
end
end BLL
end MergedPart5
section MergedPart9
namespace CLO
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
open RCN074 RCN086 RCN095 RCN135 RCN136 RCN244 RCN313
open RCN095 renaming PolynomialInFlag → BI
open WW
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p errorCap:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {stageSupport:RCN275.ResidualSupportParameters}
theorem DNN
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hF:Irreducible S.F) (n:ℕ):
    S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F n ↔ S.F∣numerator K S.F n:=by
  rw [RCN086.globalTailCut_dvd_iff (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K)]
  constructor
  · intro hG
    by_contra hnot
    have hrel:=EGB S.F (numerator K S.F n) hF.ne_zero
      (hF.isRelPrime_iff_not_dvd.mpr hnot)
    exact S.MW.not_isUnit (hrel S.RR hG)
  · intro hdiv
    exact S.RR.trans (map_dvd (surfaceMap (RCN135.polynomialEmbedding K)) hdiv)
end
end CLO
end MergedPart9
end SubmissionLower
end ProximityPrize
end
section
section MergedPart0
namespace ProximityPrize
namespace SubmissionLower
namespace BQX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN095 renaming PolynomialInFlag → BI
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open BEN OP
open ActualFirstCutPole6807 renaming pole_le_of_value_le → BIH
open GenericSlicePoints6807 renaming filteredCut_zero → DHH
open AHX HFreeDir6813
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {p errorCap:ℕ} [CharP (GenericField K) p]
  {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "w" =>RCN326.w
local notation "phiE" =>RingHom.comp (algebraMap Ω E) (RCN135.polynomialEmbedding K)
theorem DPE
    (Gamma:T→Finset K) (flag:T→FlagDegree)
    (S: ∀i,Stage_p19 K I (Gamma i) x p (flag i) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF: ∀i,(S i).F=F)
    (hproper: ∀i,¬(S i).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S i).F (w+1))
    (old: ∀i,CM (S i))
    (emb: ∀i,RCN002.CoordinateField Ω (old i).1→ₐ[Ω] E)
    (hinj:Function.Injective (fun i=>RCN134.embeddingPoint (old i).1 (emb i)))
    (D:Ideal PE) [D.IsPrime] (sep:RCN341.SeparableLiteralCoordinate D)
    (hpoint: ∀i,D≤RingHom.ker (MvPolynomial.aeval (RCN134.embeddingPoint (old i).1 (emb i)):PE→ₐ[E] E).toRingHom)
    (hcarrier: ∀i,RCN208.scalarPolynomialMap Ω E (S i).G∈D)
    (hisolated:RCN208.scalarPolynomialMap Ω E (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1))∉D)
    (e d cost:ℕ)
    (hpole:surfaceMap phiE F∈D→surfaceMap phiE (polyH K F)∉D→
      ∀W:Finset (Place_p19 E (RCN002.CoordinateField E D)),
        (d:ℤ)*(∑ nu∈W,RCN187.poleOrder nu.val
          (SecondJetComponentRoots.coefficientMap phiE D (RCN055.baseNumerator F (w-1))/
            SecondJetComponentRoots.coefficientMap phiE D (polyH K F)^e))≤cost):
    d*(∑ i,FO (S i) (DN (S i) (hproper i)) (old i))≤cost:=by
  classical
  let A:=RCN002.CoordinateRing E D
  let Lf:=RCN002.CoordinateField E D
  letI:=RCN006.quotientPolynomialAlgebra E D sep.index
  letI:=RCN006.polynomialBaseAlgebra E D sep.index
  letI:=RCN005.rationalBaseAlgebra E D sep.index sep.transcendental
  letI:=RCN006.quotientBaseScalarTower E D sep.index
  letI:=RCN006.quotientFractionScalarTower E D sep.index
  letI:=RCN006.polynomialRationalScalarTower E D sep.index sep.transcendental
  letI:=RCN005.rationalBaseScalarTower E D sep.index sep.transcendental
  letI:FiniteDimensional (RatFunc E) Lf:=sep.finite
  letI:Algebra.IsSeparable (RatFunc E) Lf:=sep.separable
  let i0:T:=Classical.choice inferInstance
  let ev:=SecondJetComponentRoots.coefficientMap phiE D
  let evalPoint:=fun i=>pointHom E D (slicePoint (S i) (old i) (emb i) D (hpoint i))
  let mu:=fun i=>FO (S i) (DN (S i) (hproper i)) (old i)
  let a:A:=AKZ (S i0) D
  let H:A:=YA (K:=K) D (polyH K F)
  let c:A:=ZA (K:=K) D
  let b:A:=c*H^(e+3)
  let iota:A→+*Lf:=algebraMap A Lf
  have haEq (i:T):a=AKZ (S i) D:=by
    simp only [a,AKZ,hF]
  have hpi:Function.Injective evalPoint:=by
    intro i j hh
    exact hinj (congrArg Subtype.val (RCN007.pointHom_injective E D hh))
  have hmu: ∀i,1≤mu i:=fun i=>YW (S i) (hproper i) (old i)
  have ha: ∀i,a∈(RingHom.ker (evalPoint i).toRingHom)^(mu i):=by
    intro i
    rw [haEq i]
    exact BKK (S i) (hproper i) (old i) (emb i) D (hpoint i) (hcarrier i)
  have hHpt: ∀i,evalPoint i H≠0:=by
    intro i
    have hh:=CXZ (S i) (old i) (emb i) D (hpoint i)
    simpa only [hF] using hh
  have hcpt: ∀i,evalPoint i c≠0:=fun i=>BWP D _
  have hb: ∀i,evalPoint i b≠0:=by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota:Function.Injective iota:=IsFractionRing.injective A Lf
  have hHi:iota H≠0:=by
    intro hz
    have hh:H=0:=hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hh,map_zero])
  have hci:iota c≠0:=by
    intro hz
    have hh:c=0:=hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hh,map_zero])
  have hai:iota a≠0:=by
    intro hz
    apply DAU (S i0) D (by simpa only [hF] using hisolated)
    exact hiota (by simpa only [map_zero] using hz)
  have hbi:iota b≠0:=by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx:iota a/iota b≠0:=div_ne_zero hai hbi
  have hrepr:iota a/iota b=ev (RCN055.baseNumerator F (w-1))/ev (polyH K F)^e:=by
    have hn:a=c*H^3*YA (K:=K) D (RCN055.baseNumerator F (w-1)):=by
      simpa only [hF] using CAZ (S i0) D
    have hh:=BRC iota a
      (YA (K:=K) D (RCN055.baseNumerator F (w-1))) H c e hn hHi hci
    exact hh.trans (by rw [AKL,AKL];rfl)
  have hFd:surfaceMap phiE F∈D:=by
    rw [←hF i0,←BWR]
    exact D.mem_of_dvd (map_dvd (RCN208.scalarPolynomialMap Ω E) (S i0).RR) (hcarrier i0)
  have hHd:surfaceMap phiE (polyH K F)∉D:=by
    intro hm
    have hz:=RingHom.mem_ker.mp (hpoint i0 hm)
    change MvPolynomial.eval (RCN134.embeddingPoint (old i0).1 (emb i0))
      (surfaceMap phiE (polyH K F))=0 at hz
    apply GenericSlicePoints6807.scalar_eval_ne_zero (old i0).1 (emb i0)
      (surfaceMap (RCN135.polynomialEmbedding K) (polyH K (S i0).F))
      (RCN312.JX (S i0) (old i0))
    simpa only [BWR,hF,MvPolynomial.aeval_eq_eval] using hz
  apply CVS.BUY E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d:ℤ)*(∑ nu∈W,RCN187.poleOrder nu.val (iota a/iota b))≤(cost:ℤ)
  rw [hrepr]
  exact hpole hFd hHd W
end
end BQX
end SubmissionLower
end ProximityPrize
end MergedPart0
section MergedPart1
namespace ProximityPrize
namespace SubmissionLower
namespace BQW
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN026 (Place_p19)
open RCN204 (flagPole)
open RCN002 RCN007 RCN055 RCN074 RCN076 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN156 RCN159 RCN199 RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open OP YE AVZ
open GenericSlicePoints6807 renaming filteredCut_zero → DHH
open BD HFreeDir6813 LF
open MovingFiberThreeSources6811 (direction weight)
open OT _Q7
open AHX APJ BQX
variable {K I E T:Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433] [Fintype T]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {errorCap:ℕ} {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "w" =>RCN326.w
local notation "eta" =>(algebraMap Ω E)
local notation "phiE" =>RingHom.comp (algebraMap Ω E) (RCN135.polynomialEmbedding K)
theorem EGZ
    (Gamma:T→Finset K) (flag:T→FlagDegree)
    (S: ∀i,Stage_p19 K I (Gamma i) x 2130706433 (flag i) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (hSF: ∀i,(S i).F=F)
    (parent:FlagDegree) (hparent:RCN095.PolynomialInFlag parent (BXI eta F))
    (hproper: ∀i,¬(S i).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S i).F (w+1))
    (old: ∀i,CM (S i))
    (emb: ∀i,RCN002.CoordinateField Ω (old i).1→ₐ[Ω] E)
    (hinj:Function.Injective (fun i=>RCN134.embeddingPoint (old i).1 (emb i)))
    (N:PE) (q:FlagDegree) (hNq:RCN095.PolynomialInFlag q N)
    (hNpoint: ∀i,MvPolynomial.eval (RCN134.embeddingPoint (old i).1 (emb i)) N=0)
    (hisolated: ∀i,RCN084.IsolatedPoint (RCN208.scalarPolynomialMap Ω E (S i).G) N
      (RCN208.scalarPolynomialMap Ω E (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S i).F (w+1)))
      (RCN134.embeddingPoint (old i).1 (emb i)))
    (hdeg:parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix:2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ:MovingFiberThreeSources6811.Source F) (hleading: ∀i,SZ.leading (RCN135.polynomialEmbedding K)∉(old i).1)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree)
    (hbudget: ∀(D:Ideal PE) [D.IsPrime],RCN341.SeparableLiteralCoordinate D→
      surfaceMap phiE F∈D→N∈D→surfaceMap phiE (polyH K F)∉D→
      APH phiE F D C0 (HFree6812.infCap d))
    (scale zCap uCap vCap:ℕ)
    (hbound: ∀Q A:PE,(2:PE)*A≠0→
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q→RCN095.PolynomialInFlag unitYZFlag A→
      AGN eta F SZ Q A scale zCap uCap vCap):
    3*scale*(∑ i,FO (S i) (DN (S i) (hproper i)) (old i))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap):=by
  classical
  let carrier:=BXI eta F
  let A:=RCN208.scalarPolynomialMap Ω E (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1))
  let R:=frozenH eta F
  let point:=fun i=>RCN134.embeddingPoint (old i).1 (emb i)
  let mu:=fun i=>FO (S i) (DN (S i) (hproper i)) (old i)
  let first:=hfreeFlagDir d r v z C0
  have freeze (P:MvPolynomial (Fin 4) K):
      RCN208.scalarPolynomialMap Ω E (surfaceMap (RCN135.polynomialEmbedding K) P)=surfaceMap (codeMap eta) P:=by
    simp only [RCN208.scalarPolynomialMap,surfaceMap,codeMap,RingHom.comp_apply,MvPolynomial.map_map]
  have hReq:R=RCN208.scalarPolynomialMap Ω E (CR (RCN135.polynomialEmbedding K) F):=
    (freeze (polyH K F)).symm
  have hRderiv:R=MvPolynomial.pderiv (1:Fin 3) carrier:=
    (RCN267.surfaceMap_pderiv_R (codeMap eta) F).symm
  have hcar:carrier≠0:=by
    intro hz
    exact hF (RCN136.surfaceMap_injective (codeMap eta) (DTI eta)
      (by simpa only [carrier,BXI,map_zero] using hz))
  have hdiv (i:T):RCN208.scalarPolynomialMap Ω E (S i).G∣carrier:=by
    have hh:=map_dvd (RCN208.scalarPolynomialMap Ω E) (S i).RR
    rw [hSF i,freeze] at hh
    exact hh
  have hGpoint (i:T):MvPolynomial.eval (point i) (RCN208.scalarPolynomialMap Ω E (S i).G)=0:=by
    rw [GenericSlicePoints6807.scalar_eval_embedding]
    have hc:=EN Ω (S i).G _ _ (old i)
    have hz:RCN002.coordinateEvaluation Ω (old i).1 (S i).G=0:=by
      apply (RingHom.mem_ker (f:=(RCN002.coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [RCN002.coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hFpoint (i:T):MvPolynomial.eval (point i) carrier=0:=by
    have hh:=map_dvd (MvPolynomial.eval (point i)) (hdiv i)
    rw [hGpoint i,zero_dvd_iff] at hh
    exact hh
  have hApoint (i:T):MvPolynomial.eval (point i) A=0:=by
    rw [GenericSlicePoints6807.scalar_eval_embedding]
    have hc:=GV Ω (S i).G _ _ (old i)
    have hz:RCN002.coordinateEvaluation Ω (old i).1 (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1))=0:=by
      apply (RingHom.mem_ker (f:=(RCN002.coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [RCN002.coordinateEvaluation_ker,←hSF i]
      exact hc
    rw [hz,map_zero]
  have hRpoint (i:T):MvPolynomial.eval (point i) R≠0:=by
    rw [hReq,←hSF i]
    exact GenericSlicePoints6807.scalar_eval_ne_zero (old i).1 (emb i) _
      (_Q6 Ω (S i).G _ _ (old i))
  have hDpoint (i:T):MvPolynomial.eval (point i) (MvPolynomial.pderiv (1:Fin 3) carrier)≠0:=by
    rw [←hRderiv]
    exact hRpoint i
  have hiso (i:T):RCN084.IsolatedPoint carrier N A (point i):=by
    exact AIW.DAZ carrier
      (RCN208.scalarPolynomialMap Ω E (S i).G) N A (hdiv i) (point i) (hGpoint i) (hDpoint i)
      (by simpa only [hSF] using hisolated i)
  have hcover (i:T): ∃g: ↥(RCN084.activeFactors carrier N),MvPolynomial.eval (point i) g.1=0:=
    AAU carrier N A R hcar (point i)
      (hFpoint i) (hApoint i) (hRpoint i) (hDpoint i) (hiso i)
  obtain ⟨assign,hassigned⟩:=DIX carrier N R point hcover hNpoint hRpoint
  have hRspan:R∈Ideal.span ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set PE):=by
    rw [hRderiv]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let budgets:=Classical.choice (EFX carrier N R parent q hcar hparent hNq
    2130706433 hdeg hmix)
  let active:Finset (ANR carrier N R):=Finset.univ.image assign
  have hLpoint (i:T):MvPolynomial.eval (point i) (SZ.leading (codeMap eta))≠0:=by
    have he:SZ.leading (codeMap eta)=RCN208.scalarPolynomialMap Ω E (SZ.leading (RCN135.polynomialEmbedding K)):=(freeze _).symm
    rw [he]
    exact GenericSlicePoints6807.scalar_eval_ne_zero (old i).1 (emb i) _ (hleading i)
  have hlead: ∀a∈active,SZ.leading (codeMap eta)∉a.2.1:=by
    intro a ha hmem
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp ha
    exact hLpoint i (hassigned i (hi ▸ hmem))
  obtain ⟨moving,_,hMoving⟩:=EFP eta F SZ carrier N hcar dvd_rfl hRspan
    q hNq budgets active hlead scale zCap uCap vCap hbound
  let CX (a:ANR carrier N R):=(budgets.unit a.1).toFE.weightedCost first a.2
  have hlocal (a:active):3*(∑ i with assign i=a.val,mu i)≤CX a.val+4*(w+1)*(moving a).movingCost:=by
    let T0:={i:T//assign i=a.val}
    have hne:Nonempty T0:=by
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp a.property
      exact ⟨⟨i,hi⟩⟩
    letI:Nonempty T0:=hne
    let old0:=fun i:T0=>old i.1
    let emb0:=fun i:T0=>emb i.1
    have hi0:Function.Injective (fun i:T0=>RCN134.embeddingPoint (old0 i).1 (emb0 i)):=by
      intro i j hh
      exact Subtype.ext (hinj hh)
    have hpt (i:T0):a.val.2.1≤RingHom.ker
        (MvPolynomial.aeval (RCN134.embeddingPoint (old0 i).1 (emb0 i)):PE→ₐ[E] E).toRingHom:=by
      have hh:=hassigned i.1
      rw [i.2] at hh
      exact hh
    have hcarD:carrier∈a.val.2.1:=a.val.2.1.mem_of_dvd
      (RCN084.activeFactors_spec carrier N a.val.1).2.1 (EN E a.val.1.val N R a.val.2)
    have hstageD (i:T0):RCN208.scalarPolynomialMap Ω E (S i.1).G∈a.val.2.1:=by
      obtain ⟨Q,hQ,hQne⟩:=AIW.BIG
        carrier (RCN208.scalarPolynomialMap Ω E (S i.1).G) (hdiv i.1) (point i.1) (hGpoint i.1) (hDpoint i.1)
      have hQnot:Q∉a.val.2.1:=fun hmem=>hQne (hpt i hmem)
      have hprod:RCN208.scalarPolynomialMap Ω E (S i.1).G*Q∈a.val.2.1:=
        (congrArg (fun P:PE=>P∈a.val.2.1) hQ).mp hcarD
      exact (inferInstance:a.val.2.1.IsPrime).mem_or_mem hprod |>.resolve_right hQnot
    let i0:T0:=Classical.choice hne
    have hAz:A∉a.val.2.1:=by
      have hh:=CLZ carrier N A R point assign hassigned hiso i0.1
      rwa [i0.2] at hh
    have hb:=DPE (fun i:T0=>Gamma i.1) (fun i:T0=>flag i.1)
      (fun i:T0=>S i.1) F (fun i=>hSF i.1) (fun i=>hproper i.1)
      old0 emb0 hi0 a.val.2.1 (budgets.base a.val.1 a.val.2) hpt hstageD hAz (2*w-1) 3
      (CX a.val+4*(w+1)*(moving a).movingCost) (by
        intro hFd hHd W
        have hh:=DJW phiE F a.val.2.1
          (budgets.base a.val.1 a.val.2) hHd d r v z hr hv hR hYR hAll C0
          (hbudget _ (budgets.base a.val.1 a.val.2) hFd
            (GV E a.val.1.val N R a.val.2) hHd)
          1 (CX a.val) (moving a).movingCost
          (AKA.CUE (budgets.unit a.val.1) a.val.2 first)
          (fun U=>by simpa only [Nat.cast_one,one_mul,frozenH,frozenG,codeMap] using (moving a).movingPole U) W
        simpa only [Nat.mul_one,Nat.cast_one,one_mul,Nat.cast_add,Nat.cast_mul] using hh)
    have hsum:(∑ i with assign i=a.val,mu i)=∑ i:T0,mu i.1:=by
      simpa only [T0,Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s:=(Finset.univ:Finset T)) mu (p:=fun i=>assign i=a.val)).symm
    rw [hsum]
    exact hb
  have hCX:(∑ a:active,CX a.val)≤flagMixed parent q first:=by
    rw [Finset.sum_coe_sort]
    calc
      _≤∑ a:ANR carrier N R,CX a:=Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _=∑ g: ↥(RCN084.activeFactors carrier N),∑ C:RCN264.RegularComponent E g.1 N R,
          (budgets.unit g).toFE.weightedCost first C:=Fintype.sum_sigma _
      _≤_:=sum_cost_le carrier N R parent q first hcar hparent budgets
  let assign0 (i:T):active:=⟨assign i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hpartition:(∑ a:active,∑ i with assign i=a.val,mu i)=∑ i,mu i:=by
    have hh:=DKM assign0 mu
    simpa only [assign0,Subtype.ext_iff] using hh
  have hsum:=Finset.sum_le_sum (fun a (_:a∈(Finset.univ:Finset active))=>hlocal a)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  rw [hpartition] at hsum
  calc
    _=scale*(3*∑ i,mu i):=by ring
    _≤scale*((∑ a:active,CX a.val)+4*(w+1)*(∑ a:active,(moving a).movingCost)):=
      Nat.mul_le_mul_left scale hsum
    _=scale*(∑ a:active,CX a.val)+4*(w+1)*(scale*∑ a:active,(moving a).movingCost):=by ring
    _≤_:=Nat.add_le_add (Nat.mul_le_mul_left scale hCX) (Nat.mul_le_mul_left (4*(w+1)) hMoving)
end
end BQW
end SubmissionLower
end ProximityPrize
end MergedPart1
section MergedPart2
namespace ProximityPrize
namespace SubmissionLower
namespace CAS
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open OP HFreeDir6813 BD
open GenericSlicePoints6807 renaming filteredCut_zero → DHH
open MovingFiberThreeSources6811 (direction weight)
open LF OT
open _Q7 BQW
variable {K I E A:Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433]
  [Algebra (RatFunc (GenericField K)) E] [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] [Fintype A]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {errorCap:ℕ} {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "w" =>RCN326.w
local notation "eta" =>(algebraMap Ω E)
theorem DMM
    (Gamma:A→Finset K) (flag:A→FlagDegree)
    (S: ∀a,Stage_p19 K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (hSF: ∀a,(S a).F=F)
    (parent:FlagDegree) (hparent:RCN095.PolynomialInFlag parent (BXI eta F))
    (hproper: ∀a,¬(S a).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S a).F (w+1))
    (old: ∀a,CM (S a)) (hold:Function.Injective (fun a=>(old a).1))
    (ell:MvPolynomial (Fin 3) Ω) (q:FlagDegree) (hell:RCN095.PolynomialInFlag q ell)
    (projection: ∀a,RCN344.SeparableCoordinate Ω (RCN002.CoordinateField Ω (old a).1))
    (hvalue: ∀a,RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old a).1) (projection a)=
      RCN002.coordinateEvaluation Ω (old a).1 ell)
    (hdeg:parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix:2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ:MovingFiberThreeSources6811.Source F) (hleading: ∀a,SZ.leading (RCN135.polynomialEmbedding K)∉(old a).1)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hfree:CTP (E:=E) F ell C0 d)
    (scale zCap uCap vCap:ℕ)
    (hbound: ∀Q U:PE,(2:PE)*U≠0→
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q→RCN095.PolynomialInFlag unitYZFlag U→
      AGN eta F SZ Q U scale zCap uCap vCap):
    3*scale*(∑ a,FO (S a) (DN (S a) (hproper a)) (old a)*
      RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap):=by
  classical
  let oldPrime:=fun a=>(old a).1
  letI: ∀a:A,Algebra (RatFunc Ω) (RCN002.CoordinateField Ω (oldPrime a)):=
    fun a=>(projection a).embedding.toRingHom.toAlgebra
  letI: ∀a:A,IsScalarTower Ω (RatFunc Ω) (RCN002.CoordinateField Ω (oldPrime a)):=
    fun a=>IsScalarTower.of_algebraMap_eq fun c=>((projection a).embedding.commutes c).symm
  letI: ∀a:A,FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (oldPrime a)):=fun a=>(projection a).finite
  letI: ∀a:A,Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (oldPrime a)):=fun a=>(projection a).separable
  let T:=(a:A) × (RCN002.CoordinateField Ω (oldPrime a)→ₐ[RatFunc Ω] E)
  let oldT:=fun i:T=>old i.1
  let embT:=fun i:T=>i.2.restrictScalars Ω
  let N:=GenericSlicePoints6807.sliceEquation (E:=E) ell
  have hpoints:Function.Injective (fun i:T=>RCN134.embeddingPoint (oldT i).1 (embT i)):=
    RCN134.commonBaseEmbeddingPoint_injective oldPrime hold
  have hcert (i:T):=OP.VX (S i.1).G
    (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S i.1).F (w+1))
    (RCN243.CR (RCN135.polynomialEmbedding K) (S i.1).F) ell (old i.1) (hvalue i.1) i.2
  have hNq:RCN095.PolynomialInFlag q N:=RCN207.inFlag_sub_poly (inFlag_const q _) (inFlag_map _ hell)
  have hmass:=EGZ (fun i:T=>Gamma i.1) (fun i:T=>flag i.1)
    (fun i:T=>S i.1) F hF (fun i=>hSF i.1) parent hparent (fun i=>hproper i.1)
    oldT embT hpoints N q hNq (fun i=>(hcert i).2.1) (fun i=>(hcert i).2.2.2.2)
    hdeg hmix SZ (fun i=>hleading i.1) d r v z hr hv hR hYR hAll C0
    (fun D _ sep hFD hND hHD=>hfree D sep hFD hND hHD) scale zCap uCap vCap hbound
  have hsum:=GenericSlicePoints6807.weighted_embedding_sum (E:=E) oldPrime
    (fun a=>FO (S a) (DN (S a) (hproper a)) (old a))
  simpa only [oldT,embT,T,RCN344.SeparableCoordinate.degree,oldPrime,hsum] using hmass
theorem CXM
    (Gamma:A→Finset K) (flag:A→FlagDegree)
    (S: ∀a,Stage_p19 K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (hSF: ∀a,(S a).F=F)
    (parent:FlagDegree) (hparent:RCN095.PolynomialInFlag parent (BXI eta F))
    (hproper: ∀a,¬(S a).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S a).F (w+1))
    (old: ∀a,CM (S a)) (hold:Function.Injective (fun a=>(old a).1))
    (ell:MvPolynomial (Fin 3) Ω) (q:FlagDegree) (hell:RCN095.PolynomialInFlag q ell)
    (projection: ∀a,Coordinate Ω (RCN002.CoordinateField Ω (old a).1))
    (hvalue: ∀a,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω (old a).1) (projection a)=
      RCN002.coordinateEvaluation Ω (old a).1 ell)
    (hdeg:parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix:2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ:MovingFiberThreeSources6811.Source F) (hleading: ∀a,SZ.leading (RCN135.polynomialEmbedding K)∉(old a).1)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hfree:CTP (E:=E) F ell C0 d)
    (scale zCap uCap vCap:ℕ)
    (hbound: ∀Q U:PE,(2:PE)*U≠0→
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q→RCN095.PolynomialInFlag unitYZFlag U→
      AGN eta F SZ Q U scale zCap uCap vCap):
    3*scale*(∑ a,FO (S a) (DN (S a) (hproper a)) (old a)*
      RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap):=by
  classical
  let Alive:Set A:={a | ∃c,projection a=Sum.inr c}
  let sep:=fun a:Alive=>Classical.choose a.2
  have hsep (a:Alive):projection a.1=Sum.inr (sep a):=Classical.choose_spec a.2
  let old0:=fun a:Alive=>old a.1
  have hi0:Function.Injective (fun a:Alive=>(old0 a).1):=by
    intro a b hh
    exact Subtype.ext (hold hh)
  have hv0 (a:Alive):RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old0 a).1) (sep a)=
      RCN002.coordinateEvaluation Ω (old0 a).1 ell:=by
    have hh:=hvalue a.1
    rw [hsep a] at hh
    exact hh
  let weight:=fun a=>FO (S a) (DN (S a) (hproper a)) (old a)
  have hsum:(∑ a,weight a*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))=
      ∑ a:Alive,weight a.1*RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old0 a).1) (sep a):=by
    apply Finset.sum_congr_set Alive
      (fun a=>weight a*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))
      (fun a=>weight a.1*RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old0 a).1) (sep a))
    · intro a ha
      simp only [hsep ⟨a,ha⟩,RCN344.coordinateDegree,Sum.elim_inr,old0]
    · intro a ha
      cases hpj:projection a with
      | inl c=>simp only [hpj,RCN344.coordinateDegree,Sum.elim_inl,Nat.mul_zero]
      | inr c=>exact (ha ⟨c,hpj⟩).elim
  have hb:=DMM (E:=E)
    (fun a:Alive=>Gamma a.1) (fun a:Alive=>flag a.1) (fun a:Alive=>S a.1)
    F hF (fun a=>hSF a.1) parent hparent (fun a=>hproper a.1) old0 hi0 ell q hell
    sep hv0 hdeg hmix SZ (fun a=>hleading a.1) d r v z hr hv hR hYR hAll C0 hfree
    scale zCap uCap vCap hbound
  change 3*scale*(∑ a,weight a*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))≤_
  rw [hsum]
  exact hb
end
end CAS
end SubmissionLower
end ProximityPrize
end MergedPart2
section MergedPart3
namespace ProximityPrize
namespace SubmissionLower
namespace AYR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 30000
open scoped Classical
open RCN030 RCN066 RCN086 RCN095 RCN135 RCN136 RCN159 RCN198 RCN199 RCN207 RCN237 RCN243 RCN244 RCN263 RCN264 RCN275
open RCN095 renaming PolynomialInFlag → BI
open RCN327 RCN332 RCN334 RCN336 RCN338 RCN340 RCN341 RCN344
open RCN002 RCN037 RCN038 RCN042 RCN074 RCN134 RCN156 RCN248
open JN PR
open CommonLinearChannels6807 (linearA linearU linearZ)
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p errorCap a b s:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p]
local notation "Ω" =>GenericField K
variable (S:FH (RCN135.polynomialEmbedding K) Gamma x p errorCap flag w (support a b s))
variable (hp: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1)) (geometry:ABN S)
def EGI:=
  NJ geometry.base geometry.hactive geometry.hZ
    (RCN315.EH S) geometry.data
    S.MW (AHF S hp)
    ((RCN095.support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((RCN095.support_subset_flagSupport_iff
      (RCN263.reducedResidualAgreementFlag (support a b s) (w+1)) (VQ S)).2 (AFM S))
def suppliedBase (C:CM S):RCN341.SeparableLiteralCoordinate C.1:=by
  let C' :RCN264.RegularComponent Ω S.G (VQ S)
      (CR (RCN135.polynomialEmbedding K) S.F):=
    ⟨C.1,by
      rw [←VB (EW S)]
      exact C.2⟩
  exact geometry.base C'
def suppliedUnit:=YV (EW S)
  (EGI S hp geometry) (suppliedBase S geometry)
def DKL:AND (suppliedUnit S hp geometry):=
  EZN (EW S) (EGI S hp geometry)
    (suppliedBase S geometry)
    (EYJ geometry.base geometry.hactive geometry.hZ
      (RCN315.EH S) geometry.data
      S.MW (AHF S hp)
      ((RCN095.support_subset_flagSupport_iff flag S.G).2 S.flag_support)
      ((RCN095.support_subset_flagSupport_iff
        (RCN263.reducedResidualAgreementFlag (support a b s) (w+1)) (VQ S)).2 (AFM S)))
theorem DNI:(DKL S hp geometry).lam=geometry.data.lam:=rfl
theorem FRR:(DKL S hp geometry).mu=geometry.data.mu:=rfl
def BLJ:=(suppliedUnit S hp geometry).toFE
theorem EKM (C:CM S):
    1≤(BLJ S hp geometry).yzCost C:=by
  let C' :RCN264.RegularComponent Ω S.G (VQ S)
      (CR (RCN135.polynomialEmbedding K) S.F):=
    ⟨C.1,by
      rw [←VB (EW S)]
      exact C.2⟩
  change 1≤RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)
  apply RCN042.one_le_coordinateDegree_of_transcendental_value
  rw [ETQ (suppliedUnit S hp geometry) (DKL S hp geometry) C,
    DNI,CommonLinearChannels6807.eval_linearU]
  exact geometry.data.ZG C'
theorem FDD (C:CM S):
    UJ (suppliedBase S geometry C) (flagSupport unitYZFlag)
      ((BLJ S hp geometry).yzCost C):=by
  exact (suppliedUnit S hp geometry).toQZ.yzPole C
theorem GDG (lam:Ω) (hlam:geometry.data.lam=lam) (C:CM S):
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)=
      RCN002.coordinateEvaluation Ω C.1 (CommonLinearChannels6807.linearU lam):=by
  have hh:=ETQ (suppliedUnit S hp geometry) (DKL S hp geometry) C
  simpa only [DNI,hlam] using hh
theorem GAA (lam mu:Ω) (hlam:geometry.data.lam=lam) (hmu:geometry.data.mu=mu)
    (C:CM S):
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) ((suppliedUnit S hp geometry).NV C)=
      RCN002.coordinateEvaluation Ω C.1 (CommonLinearChannels6807.linearA mu lam):=by
  have hh:=FKF (suppliedUnit S hp geometry) (DKL S hp geometry) C
  simpa only [DNI,FRR,hlam,hmu] using hh
end
end AYR
end SubmissionLower
end ProximityPrize
end MergedPart3
section MergedPart4
namespace ProximityPrize
namespace SubmissionLower
namespace BBT
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open HFree6812 HFreeDir6813 PR BD
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
open LF OT
open _Q7 WC
open CAS CB
variable {K E:Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local notation "Ω" =>GenericField K
local notation "w" =>RCN326.w
def DSG (lam mu:Ω):Fin 3→MvPolynomial (Fin 3) Ω:=
  ![CommonLinearChannels6807.linearZ,CommonLinearChannels6807.linearU lam,CommonLinearChannels6807.linearA mu lam]
theorem cast_ne {n:ℕ} (h0:0<n) (hn:n<2130706433):(n:K)≠0:=by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)
theorem slice_budget
    (F:MvPolynomial (Fin 4) K) (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9:N≤9678) (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:RCN341.SeparableLiteralCoordinate D) (hFD:surfaceMap (HFree6812.phiE K E) F∈D)
    (hHD:surfaceMap (HFree6812.phiE K E) (polyH K F)∉D) (d:Fin 3)
    (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hqd:DirShape d q) (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue Ω E)-RCN208.scalarPolynomialMap Ω E
      (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m)∈D):
    APH (HFree6812.phiE K E) F D unitAllFlag (infCap d):=by
  have hNK: ∀n:ℕ,0<n→n≤N→(n:K)≠0:=fun n h0 hn=>cast_ne h0 (by omega)
  exact ⟨DOC d F D sep hFD hHD c i hci q hqd hq hslice
    (by exact_mod_cast cast_ne (K:=K) (n:=2) (by decide) (by decide))
    (hchar_gap_p19 F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap_p19 F D hHD c i hci q hq hq1 hslice N hN hNK)⟩
theorem FGQ
    (F:MvPolynomial (Fin 4) K) (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9:N≤9678) (lam mu:Ω)
    (hlam:lam∈Set.range (RCN135.polynomialEmbedding K)) (hmu:mu∈Set.range (RCN135.polynomialEmbedding K))
    (j:Fin 3):CTP (E:=E) F (DSG lam mu j) unitAllFlag j:=by
  intro D _ sep hFD hsl hHD
  obtain ⟨ql,hql⟩:=hlam
  obtain ⟨qm,hqm⟩:=hmu
  have go:=slice_budget (E:=E) F N hN hN9 D sep hFD hHD j
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (by simp [DirShape])
      (fun m=>by fin_cases m<;>simp) (Or.inr rfl) ?_
    have he:(∑ m,MvPolynomial.C ((![0,0,1]:Fin 3→Ω) m)*MvPolynomial.X m:
        MvPolynomial (Fin 3) Ω)=CommonLinearChannels6807.linearZ:=by simp [CommonLinearChannels6807.linearZ,Fin.sum_univ_three]
    rw [he];exact hsl
  · refine go ![1,0,lam] 0 rfl ![1,0,ql] (by simp [DirShape])
      (fun m=>by fin_cases m<;>simp [hql]) (Or.inr rfl) ?_
    have he:(∑ m,MvPolynomial.C ((![1,0,lam]:Fin 3→Ω) m)*MvPolynomial.X m:
        MvPolynomial (Fin 3) Ω)=CommonLinearChannels6807.linearU lam:=by simp [CommonLinearChannels6807.linearU,Fin.sum_univ_three]
    rw [he];exact hsl
  · refine go ![mu,1,mu*lam] 1 rfl ![qm,1,qm*ql] trivial
      (fun m=>by fin_cases m<;>simp [hql,hqm]) (Or.inl rfl) ?_
    have he:(∑ m,MvPolynomial.C ((![mu,1,mu*lam]:Fin 3→Ω) m)*MvPolynomial.X m:
        MvPolynomial (Fin 3) Ω)=CommonLinearChannels6807.linearA mu lam:=by simp [CommonLinearChannels6807.linearA,Fin.sum_univ_three];ring
    rw [he];exact hsl
variable {I A:Type} [Fintype A] [CharP E 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {errorCap:ℕ} {stageSupport:RCN275.ResidualSupportParameters}
include E in
theorem DXA
    (Gamma:A→Finset K) (flag:A→FlagDegree)
    (S: ∀a,Stage_p19 K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (hSF: ∀a,(S a).F=F)
    (parent:FlagDegree)
    (hp: ∀(L:Type) [Field L] (phi:Polynomial K→+*L),RCN095.PolynomialInFlag parent (surfaceMap phi F))
    (hproper: ∀a,¬(S a).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S a).F (w+1))
    (old: ∀a,CM (S a)) (hold:Function.Injective (fun a=>(old a).1))
    (lam mu:Ω) (hlam:lam∈Set.range (RCN135.polynomialEmbedding K)) (hmu:mu∈Set.range (RCN135.polynomialEmbedding K))
    (j:Fin 3) (projection: ∀a,Coordinate Ω (RCN002.CoordinateField Ω (old a).1))
    (hvalue: ∀a,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω (old a).1) (projection a)=
      RCN002.coordinateEvaluation Ω (old a).1 (DSG lam mu j))
    (hlinear:2*(parent.zOnly+parent.yz+parent.all)<2130706433)
    (SZ SP SQ:MovingFiberThreeSources6811.Source F) (hleading: ∀a,SZ.leading (RCN135.polynomialEmbedding K)∉(old a).1)
    (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:MvPolynomial.weightedTotalDegree RCN156.residualTotalWeights F≤r+v+z) (hsmall:r+v+z≤9678)
    (hpos:0<F.degreeOf 2) (hcharF:F.degreeOf 2<2130706433)
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta)
    (hP:delta≤SP.d) (hQ:delta≤SQ.d) (hchar:delta≤2130706433) (hZchar:SZ.k<2130706433)
    (hz:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433):
    3*(SZ.d*delta)*(∑ a,FO (S a) (DN (S a) (hproper a)) (old a)*
      RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))≤
      (SZ.d*delta)*flagMixed parent (MovingFiberThreeSources6811.direction j) (hfreeFlagDir j r v z unitAllFlag)+
        4*(w+1)*((MovingFiberThreeSources6811.direction j).zOnly*(delta*flagMixed parent unitZFlag SZ.flag)+
          (MovingFiberThreeSources6811.direction j).yz*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)+
          (MovingFiberThreeSources6811.direction j).all*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)):=by
  have hell:RCN095.PolynomialInFlag (MovingFiberThreeSources6811.direction j) (DSG lam mu j):=by
    fin_cases j
    · exact FFR
    · exact FDG lam
    · exact FFE mu lam
  have hq:(MovingFiberThreeSources6811.direction j).zOnly+(MovingFiberThreeSources6811.direction j).yz+(MovingFiberThreeSources6811.direction j).all=1:=by fin_cases j<;>rfl
  have hAll' :WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ):=Or.inr (by exact_mod_cast hAll)
  exact CXM (E:=E) Gamma flag S F hF hSF parent (hp _ _)
    hproper old hold (DSG lam mu j) (MovingFiberThreeSources6811.direction j) hell projection hvalue (by omega)
    (by rw [hq,mul_one];exact hlinear) SZ hleading j r v z hr hv hR hYR hAll' unitAllFlag
    (FGQ F (r+v+z) hAll hsmall lam mu hlam hmu j) _ _ _ _
    (fun Q U hden hQf hUf=>BSF (algebraMap Ω E) F hF hpos hcharF
      SP SQ hcop delta hd hP hQ hchar SZ hZchar parent (hp _ _) hlinear Q U hden hQf hUf hz hu)
end
end BBT
end SubmissionLower
end ProximityPrize
end MergedPart4
section MergedPart5
namespace ProximityPrize
namespace SubmissionLower
namespace BIO
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN074 RCN086 RCN095 RCN135 RCN136 RCN198 RCN199 RCN200 RCN207 RCN208 RCN209 RCN264 RCN313 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open BD AFA
open MovingFiberThreeSources6811 (direction weight)
open LF OT
open _Q7 AKN AGD
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local notation "Ω" =>GenericField K
local notation "Poly" =>MvPolynomial (Fin 3) Ω
theorem DUK
    (F:MvPolynomial (Fin 4) K) (SZ:MovingFiberThreeSources6811.Source F)
    (G:I→Poly) (hGF: ∀i,G i∣baseCarrier F)
    (a b s w:ℕ) (hw:1≤w) (hR:F.degreeOf 2≤s+2)
    (hYR:RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll:RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (Q A:Poly) (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (scale z u v:ℕ) (hbound:AGN (RingHom.id Ω) F SZ Q A scale z u v)
    (old: ∀i,RCN264.RegularComponent Ω (G i) (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1)) (baseH F))
    (hold:Function.Injective (fun i=>(old i).1)) (hlead: ∀i,SZ.leading (RCN135.polynomialEmbedding K)∉(old i).1)
    (hAnonzero: ∀i,A∉(old i).1)
    (projection: ∀i,RCN344.SeparableCoordinate Ω (RCN002.CoordinateField Ω (old i).1))
    (hvalue: ∀i,RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A):
    let W:=RCN198.center a b s+w • (⟨a,b+1,s+2⟩:FlagDegree)
    scale*(∑ i,RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v:=by
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩:=RCN086.exists_filtered_certificate (RCN135.polynomialEmbedding K)
    a b s F hR hYR hAll (w+1) (by omega) (tailSelector (w+1)) 0 0 0
  have heq' :RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1)=filteredCut w coeff (baseH F) (baseG F):=heq
  let old' : ∀i,CWU (RingHom.id Ω) F (G i) w coeff:=fun i=>
    ⟨(old i).1,by
      change (old i).1∈RCN264.regularComponents Ω (G i) (filteredCut w coeff (baseH F) (baseG F)) (baseH F)
      rw [←heq']
      exact (old i).2⟩
  obtain ⟨hHflag,hGflag⟩:=RCN201.DGW (RCN135.polynomialEmbedding K) a b s F hR hYR hAll
  have hcut:=FGH F a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel Q A hQ hA
  exact CRH (RingHom.id Ω) F SZ G hGF Q A scale z u v hbound
    w coeff _ hcut old' hold hlead hAnonzero projection hvalue
theorem CTF
    (F:MvPolynomial (Fin 4) K) (SZ:MovingFiberThreeSources6811.Source F)
    (G:I→Poly) (hGF: ∀i,G i∣baseCarrier F)
    (a b s w:ℕ) (hw:1≤w) (hR:F.degreeOf 2≤s+2)
    (hYR:RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll:RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (base: ∀i,∀C:RCN264.RegularComponent Ω (G i) (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1)) (baseH F),
      RCN341.SeparableLiteralCoordinate C.1)
    (p:I→FlagDegree) (tailFlag:FlagDegree) (unit: ∀i,EE (base i) (p i) tailFlag)
    (old: ∀i,RCN264.RegularComponent Ω (G i) (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1)) (baseH F))
    (hold:Function.Injective (fun i=>(old i).1))
    (active:Finset I) (hlead: ∀i∈active,SZ.leading (RCN135.polynomialEmbedding K)∉(old i).1)
    (scale z u v:ℕ)
    (hbound: ∀Q A:Poly,(2:Poly)*A≠0→
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q→RCN095.PolynomialInFlag unitYZFlag A→
      AGN (RingHom.id Ω) F SZ Q A scale z u v):
    let W:=RCN198.center a b s+w • (⟨a,b+1,s+2⟩:FlagDegree)
    ∃budget: ∀i,RD (old i).1 (baseH F) (baseG F),
      (∀i,(budget i).zCost=(unit i).toFE.zCost (old i)∧
        (budget i).yzCost=(unit i).toFE.yzCost (old i)∧
        (budget i).allCost=(unit i).toFE.allCost (old i))∧
      scale*(∑ i∈active,(budget i).movingCost)≤W.zOnly*z+W.yz*u+W.all*v:=by
  classical
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩:=BJG
    (fun i=>(old i).1) (fun i=>base i (old i)) (baseH F) (baseG F)
  let budget (i:I):RD (old i).1 (baseH F) (baseG F):={
    zCost:=(unit i).toFE.zCost (old i)
    yzCost:=(unit i).toFE.yzCost (old i)
    allCost:=(unit i).toFE.allCost (old i)
    movingCost:=RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old i).1) (projection i)
    zPole:=(unit i).toQZ.zPole (old i)
    yzPole:=(unit i).toQZ.yzPole (old i)
    allPole:=(unit i).toQZ.allPole (old i)
    movingPole:=by
      intro U
      calc
        _=∑ nu∈U,RCN187.poleOrder nu.val
            (RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old i).1) (projection i)):=by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj i).2.2 nu).symm
        _≤_:=RCN344.SeparableCoordinate.AMH Ω (RCN002.CoordinateField Ω (old i).1) (projection i) U}
  refine ⟨budget,fun _=>⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hempty:active=∅
  · simp [hempty]
  obtain ⟨i0,hi0⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
  have hAne:A≠0:=by intro hz;exact (hproj i0).1 (hz ▸ (old i0).1.zero_mem)
  have htwo:(2:Poly)≠0:=(CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
  have hb:=DUK F SZ (fun i:active=>G i.val) (fun i=>hGF i.val)
    a b s w hw hR hYR hAll Q A hQ hA scale z u v (hbound Q A (mul_ne_zero htwo hAne) hQ hA)
    (fun i=>old i.val) (fun i j hh=>Subtype.ext (hold hh))
    (fun i=>hlead i.val i.property) (fun i=>(hproj i.val).1)
    (fun i=>projection i.val) (fun i=>(hproj i.val).2.1)
  change scale*(∑ i∈active,RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))≤_
  rwa [Finset.sum_coe_sort active (fun i=>RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))] at hb
end
end BIO
end SubmissionLower
end ProximityPrize
end MergedPart5
section MergedPart6
namespace ProximityPrize
namespace SubmissionLower
namespace BAP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 30000
open scoped Classical
open RCN002 RCN074 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136 RCN137 RCN156 RCN159 RCN243 RCN244 RCN264 RCN267 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open YE ARR
variable {K I J:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {p errorCap:ℕ} [CharP (GenericField K) p]
  {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "Poly" =>MvPolynomial (Fin 3) Ω
local notation "w" =>RCN326.w
theorem DYR
    (Gamma:J→Finset K) (flag:J→FlagDegree)
    (S: ∀j,Stage_p19 K I (Gamma j) x p (flag j) errorCap stageSupport)
    (F:MvPolynomial (Fin 4) K) (hF:F≠0) (hSF: ∀j,(S j).F=F)
    (hG: ∀j,(S j).G∈RCN137.normalizedFactorSet (surfaceMap (RCN135.polynomialEmbedding K) F))
    (hGinj:Function.Injective (fun j=>(S j).G))
    (hproper: ∀j,¬(S j).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (S j).F (w+1)):
    Function.Injective (fun a:(j:J) × CM (S j)=>a.2.1):=by
  let carrier:=surfaceMap (RCN135.polynomialEmbedding K) F
  have hcar:carrier≠0:=by
    intro hz
    exact hF (RCN136.surfaceMap_injective (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K)
      (by simpa only [carrier,map_zero] using hz))
  rintro ⟨i,Ci⟩ ⟨j,Cj⟩ he
  have hg:(S i).G=(S j).G:=by
    by_contra hne
    have hsubset:({(S i).G,(S j).G}:Finset Poly)⊆RCN137.normalizedFactorSet carrier:=by
      intro P hP
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact hG i
      · exact hG j
    have hprod:(S i).G*(S j).G∣carrier:=by
      have hh:=(Finset.prod_dvd_prod_of_subset {(S i).G,(S j).G} (RCN137.normalizedFactorSet carrier) id hsubset).trans
        (RCN137.normalizedFactorSet_product_dvd carrier hcar)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have hiG:(S i).G∈Ci.1:=EN Ω (S i).G _ _ Ci
    have hjG:(S j).G∈Ci.1:=by
      have hh:=EN Ω (S j).G _ _ Cj
      exact (congrArg (fun P:Ideal Poly=>(S j).G∈P) he).mpr hh
    have hd:=BSI carrier (S i).G (S j).G Ci.1 hprod hiG hjG
    apply _Q6 Ω (S i).G _ _ Ci
    change surfaceMap (RCN135.polynomialEmbedding K) (MvPolynomial.pderiv (2:Fin 4) (S i).F)∈Ci.1
    have hr:surfaceMap (RCN135.polynomialEmbedding K) (MvPolynomial.pderiv (2:Fin 4) (S i).F)=
        MvPolynomial.pderiv (1:Fin 3) carrier:=by
      rw [hSF i]
      exact (RCN267.surfaceMap_pderiv_R (RCN135.polynomialEmbedding K) F).symm
    exact (congrArg (fun P:Poly=>P∈Ci.1) hr).mpr hd
  have hi:i=j:=hGinj hg
  cases hi
  exact congrArg (fun C:CM (S i)=>(⟨i,C⟩:(j:J) × CM (S j)))
    (Subtype.ext he)
end
end BAP
end SubmissionLower
end ProximityPrize
end MergedPart6
section MergedPart8
namespace ProximityPrize
namespace SubmissionLower
namespace DU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN137 RCN156 RCN159 RCN174 RCN198
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN319 RCN327 RCN334
open RCN222 renaming GeometricFactor → EX
open RCN319 renaming specialization → BM
open FA CLO BAP
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
structure Packet (x:I→K) (t y r:ℕ) where
  rlow:5≤r
  rhigh:r≤14
  ylow:r+2≤y
  yhigh:y≤71
  yt:y≤t
  thigh:t≤7200
  D:ℕ
  Dlow:131072≤D
  Dchar:D<2130706433
  F:MvPolynomial (Fin 4) K
  irreducible:Irreducible F
  rdegree:0<F.degreeOf 2
  box:F∈RCN174.globalCoefficientBox K D w t r
  support:RCN275.ResidualSupportData (LocatorHybridCells.cellSupport t y r) F
  selected:K→Polynomial K
  seeds:Finset K
  nodes:Finset I
  u0:I→K
  u1:I→K
  injective:Set.InjOn x nodes
  nodeCount:nodes.card=262144
  degree: ∀gamma∈seeds,(selected gamma).natDegree≤w
  agreement: ∀gamma∈seeds,181059≤
    (nodes.filter (fun i=>(selected gamma).eval (x i)=u0 i+gamma*u1 i)).card
  solution: ∀gamma∈seeds,RCN319.specialization K (selected gamma) gamma F=0
  regular: ∀gamma∈seeds,RCN319.specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0
  noPencil:BL selected seeds w 81085
namespace Packet
variable {x:I→K} {t y r:ℕ} (P:Packet x t y r)
include P in
theorem support_caps:(LocatorHybridCells.cellSupport t y r).s=r∧(LocatorHybridCells.cellSupport t y r).ys=y∧
    (LocatorHybridCells.cellSupport t y r).total=t:=by
  have:=P.rlow
  have:=P.ylow
  have:=P.yt
  dsimp [LocatorHybridCells.cellSupport,RCN198.support,LocatorHybridCells.cellA,LocatorHybridCells.cellB,LocatorHybridCells.cellS]
  omega
theorem r_weight:wt RCN156.residualSWeights P.F≤r:=by
  simpa only [P.support_caps.1] using P.support.s_weight
theorem y_weight:wt RCN156.residualYSWeights P.F≤y:=by
  simpa only [P.support_caps.2.1] using P.support.ys_weight
theorem total_weight:wt RCN156.residualTotalWeights P.F≤t:=by
  simpa only [P.support_caps.2.2] using P.support.total_weight
theorem IZ:P.F.degreeOf 1≤y∧P.F.degreeOf 2≤r∧P.F.degreeOf 3≤t:=by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using P.support.IZ
def restrict (Delta:Finset K) (hsub:Delta⊆P.seeds):Packet x t y r:=
  {P with
          seeds:=Delta
          degree:=fun gamma hg=>P.degree gamma (hsub hg)
          agreement:=fun gamma hg=>P.agreement gamma (hsub hg)
          solution:=fun gamma hg=>P.solution gamma (hsub hg)
          regular:=fun gamma hg=>P.regular gamma (hsub hg)
          noPencil:=KX P.selected P.seeds Delta w 81085 hsub P.noPencil}
def stage (g:RCN222.GeometricFactor K P.F):
    FH (RCN135.polynomialEmbedding K) (KK K P.F P.selected P.seeds g) x
      2130706433 81085 (CO K g) w (LocatorHybridCells.cellSupport t y r):=
  BJP
    (AIT K (LocatorHybridCells.cellSupport t y r) P.F P.irreducible P.rdegree
      (P.IZ.2.1.trans_lt (by have:=P.rhigh;omega:r<2130706433)) P.support
      P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.degree P.solution P.regular P.noPencil (by decide) g)
    (AES g.val)
theorem stage_F (g:RCN222.GeometricFactor K P.F):(P.stage g).F=P.F:=rfl
theorem stage_flag (g:RCN222.GeometricFactor K P.F):
    (CO K g).all≤r∧
      (CO K g).yz+(CO K g).all≤y∧
      (CO K g).zOnly+(CO K g).yz+
        (CO K g).all≤t:=by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using
    AER P.F P.irreducible.ne_zero P.support g
theorem CVV (g:RCN222.GeometricFactor K P.F):
    ∀gamma∈KK K P.F P.selected P.seeds g,181059≤((P.stage g).AJW gamma).card:=
  fun gamma hg=>P.agreement gamma (WK K P.F P.selected P.seeds g hg)
theorem parent_flag (L:Type) [Field L] (phi:Polynomial K→+*L):
    RCN095.PolynomialInFlag ⟨t-y,y-r,r⟩ (surfaceMap phi P.F):=
  NL.CUS phi P.F r y t (by have:=P.ylow;omega) P.yt
    P.r_weight P.y_weight P.total_weight
theorem stage_proper (hproper: ¬P.F∣numerator K P.F (w+1)) (g:RCN222.GeometricFactor K P.F):
    ¬(P.stage g).G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage g).F (w+1):=by
  intro hg
  exact hproper ((DNN (P.stage g) P.irreducible (w+1)).mp hg)
theorem FDF (hproper: ¬P.F∣numerator K P.F (w+1)):
    Function.Injective (fun a:(g:RCN222.GeometricFactor K P.F) × CM (P.stage g)=>a.2.1):=by
  apply DYR (KK K P.F P.selected P.seeds)
    (CO K) P.stage P.F P.irreducible.ne_zero P.stage_F
  · intro g
    exact g.property
  · intro g h he
    exact Subtype.ext he
  · exact P.stage_proper hproper
theorem seeds_cover:P.seeds.card≤∑ g:RCN222.GeometricFactor K P.F,
    (KK K P.F P.selected P.seeds g).card:=
  AAD K P.F P.irreducible.ne_zero P.selected P.seeds P.solution
end Packet
end
end DU
end SubmissionLower
end ProximityPrize
end MergedPart8
section MergedPart9
namespace ProximityPrize
namespace SubmissionLower
namespace CVL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical
open MvPolynomial RCN081 RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN275 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open FA DU
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
def factorPacket {H:MvPolynomial (Fin 4) K} (F:RCN266.RegularIndex H)
    (D L s t y r:ℕ) (hDlow:131072≤D) (hDchar:D<2130706433)
    (hbox:F.val∈RCN174.globalCoefficientBox K D 131071 L s)
    (hrlo:5≤r) (hrhi:r≤14) (hylo:r+2≤y) (hyhi:y≤71) (hyt:y≤t) (hthi:t≤7200)
    (hR:wt RCN156.residualSWeights F.val≤r) (hY:wt RCN156.residualYSWeights F.val≤y)
    (hT:wt RCN156.residualTotalWeights F.val≤t)
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181059≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 81085):Packet (nodes:I→K) t y r where
  rlow:=hrlo
  rhigh:=hrhi
  ylow:=hylo
  yhigh:=hyhi
  yt:=hyt
  thigh:=hthi
  D:=D
  Dlow:=hDlow
  Dchar:=hDchar
  F:=F.val
  irreducible:=(RCN167.positiveRFactors_spec H F.val F.property).1
  rdegree:=(RCN167.positiveRFactors_spec H F.val F.property).2.2
  box:=by
    intro e he
    have ht:=(MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights he).trans hT
    have hr:=(MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights he).trans hR
    rw [RCN081.weight_fin4] at ht hr
    simp [RCN156.residualTotalWeights,RCN156.residualSWeights] at ht hr
    exact ⟨by omega,by omega,(hbox he).2.2⟩
  support:=by
    constructor<;>dsimp [LocatorHybridCells.cellSupport,RCN198.support,LocatorHybridCells.cellA,LocatorHybridCells.cellB,LocatorHybridCells.cellS]<;>omega
  selected:=selected
  seeds:=RCN140.regularSeeds H selected Gamma F
  nodes:=Finset.univ
  u0:=u0
  u1:=u1
  injective:=nodes.injective.injOn
  nodeCount:=by simpa only [Finset.card_univ] using hI
  degree:=fun gamma hg=>hdegree gamma (RCN140.ACS H selected Gamma F hg)
  agreement:=fun gamma hg=>hagreement gamma (RCN140.ACS H selected Gamma F hg)
  solution:=fun _ hg=>(Finset.mem_filter.mp hg).2.1
  regular:=fun _ hg=>(Finset.mem_filter.mp hg).2.2
  noPencil:=KX selected Gamma _ 131071 81085
    (RCN140.ACS H selected Gamma F) hno
end
end CVL
end SubmissionLower
end ProximityPrize
end MergedPart9
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace CLC
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open XB ARW
open SecondJetGlobalSupport (localize)
variable {K N I:Type*} [Field K] [Fintype N] [Fintype I]
theorem FCI (J P:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (q:ℕ)
    (hnot: ¬J^q∣P):
    ∃e<q,∃Q:SecondJetSupport.Poly (K:=K),P=J^e*Q∧Q≠0∧IsRelPrime J Q:=by
  have hP:P≠0:=by intro hz;exact hnot (by rw [hz];exact dvd_zero _)
  obtain ⟨e,Q,hnd,hEq⟩:=WfDvdMonoid.max_power_factor hP hJ
  have hQ:Q≠0:=by intro hz;apply hP;rw [hEq,hz,mul_zero]
  have he:e<q:=by
    by_contra h
    exact hnot ((pow_dvd_pow J (by omega:q≤e)).trans ⟨Q,hEq⟩)
  exact ⟨e,he,Q,hEq,hQ,hJ.isRelPrime_iff_not_dvd.mpr hnd⟩
end
end CLC
end MergedPart1
section MergedPart2
namespace DHM
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetRelaxedGlobalIndex (Index budget exponent)
open SecondJetRelaxedGlobalIndex renaming exponent_injective → ACD
open SecondJetRelaxedGlobalCounts renaming coefficientCount → AW
open SecondJetCoefficients (liftExponent)
open SecondJetGlobalSupport (localize)
open RCN234 RCN156
open SecondJetClearedHelper (cleared helper)
open SecondJetHelperWeights renaming cleared_weight → BUF
variable {K N E:Type} [Field K] [Fintype N] [Field E]
theorem FIO
    (phi:SecondJetSupport.Poly (K:=K)→+*Polynomial E) (z:E)
    (J P Q:SecondJetSupport.Poly (K:=K)) (e m d:ℕ) (hEq:P=J^e*Q)
    (hJ:phi J≠0) (hm:(phi J).rootMultiplicity z=m)
    (hp:(Polynomial.X-Polynomial.C z)^d∣phi P):
    (Polynomial.X-Polynomial.C z)^(d-e*m)∣phi Q:=by
  by_cases hQ:phi Q=0
  · rw [hQ];exact dvd_zero _
  rw [hEq,map_mul,map_pow] at hp
  have hn:=mul_ne_zero (pow_ne_zero e hJ) hQ
  have horder:=(Polynomial.le_rootMultiplicity_iff hn).mpr hp
  rw [Polynomial.rootMultiplicity_mul hn,
    AID.DOQ (phi J) z e hJ,hm] at horder
  exact (Polynomial.le_rootMultiplicity_iff hQ).mp (by omega)
theorem FLJ (d m e:ℕ) (hm:0<m)
    (he:e<(d+m-1)/m):0<d-e*m:=by
  have hh:(e+1)*m≤d+m-1:=(Nat.le_div_iff_mul_le hm).mp (by omega)
  have hp:e*m+m≤d+m-1:=by simpa only [Nat.add_mul,one_mul] using hh
  omega
theorem FCK
    (phi:SecondJetSupport.Poly (K:=K)→+*Polynomial E) (z:E)
    (J P:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (d m:ℕ) (hmpos:0<m)
    (hnot: ¬J^((d+m-1)/m)∣P) (hne:phi J≠0)
    (hm:(phi J).rootMultiplicity z=m)
    (hpow:(Polynomial.X-Polynomial.C z)^d∣phi P):
    ∃e<(d+m-1)/m,∃Q:SecondJetSupport.Poly (K:=K),P=J^e*Q∧Q≠0∧IsRelPrime J Q∧
      0<min m (d-e*m)∧(Polynomial.X-Polynomial.C z)^(d-e*m)∣phi Q:=by
  obtain ⟨e,he,Q,hEq,hQ,hcop⟩:=
    CLC.FCI J P hJ ((d+m-1)/m) hnot
  exact ⟨e,he,Q,hEq,hQ,hcop,lt_min hmpos (FLJ d m e hmpos he),
    FIO phi z J P Q e m d hEq hne hm hpow⟩
end
end DHM
end MergedPart2
section MergedPart3
namespace FF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open SecondJetHelperWeights renaming cleared_weight → BUF
open SecondJetGlobalSupport (localize)
open SecondJetSpecialize (specialize)
open SecondJetRelaxedGlobalIndex (Index budget exponent)
open SecondJetRelaxedGlobalIndex renaming exponent_injective → ACD
open RCN234 RCN156 BD
open MovingFiberThreeSources6811 (direction weight)
structure Parameters where
  m:ℕ
  L:ℕ
  B:ℕ
  s:ℕ
  U:ℕ
  k:ℕ
  n0:ℕ
  deriving DecidableEq
def Parameters.cutoff (p:Parameters) (h:ℕ):ℕ:=
  p.m*181059-SecondJetRelaxedDifferentiation.reserve p.k p.n0 h*49990
structure Shape (p:Parameters):Prop where
  slope:2*p.s≤p.B
  middle:p.B≤p.U
  total:p.U≤p.L
  contact:p.s<p.m
  retention:p.k+1≤p.n0
  degree:p.n0≤p.s
  characteristic:p.s<2130706433
def Dimension (p:Parameters) (Kdim:ℕ):Prop:=
  Kdim+262144*SecondJetRelaxedGlobalMap.rankBound p.m p.L p.B p.s p.U
    (fun h=>(p.cutoff h+p.B-1)/131071)≤
    Fintype.card (SecondJetRelaxedGlobalIndex.Index p.cutoff 131071 p.L p.B p.s p.U)
variable {K N:Type} [Field K] [Fintype N]
def Bounds (p:Parameters) (P:SecondJetSupport.Poly (K:=K)):Prop:=
  ∀e∈P.support,2*e 1+e 3≤p.B∧e 1≤p.s∧e 1+e 2+e 3≤p.U∧
    e 1+e 2+e 3+e 4≤p.L∧
    e 0+131071*e 2+131070*e 3+131069*e 1<p.cutoff (e 1)
def Interpolant (p:Parameters) (nodes:N ↪ K) (u0 u1:N→K) (P:SecondJetSupport.Poly (K:=K)):Prop:=
  P≠0∧Bounds p P∧ ∀i,MvPolynomial.X 0^p.m ∣ SecondJetDifferentiation.substitute (K:=K)
    (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P)
theorem DVF (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144):
    ∃V:Submodule K (SecondJetSupport.Poly (K:=K)),Module.Finite K V∧Kdim≤Module.finrank K V∧
      (∀P∈V,Bounds p P)∧(∀P∈V,∀i,MvPolynomial.X 0^p.m ∣
        SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P)):=by
  let e:=SecondJetRelaxedGlobalIndex.exponent (D:=p.cutoff) (w:=131071)
    (L:=p.L) (B:=p.B) (s:=p.s) (U:=p.U)
  have he:=SecondJetRelaxedGlobalIndex.exponent_injective p.cutoff 131071 p.L p.B p.s p.U
  have hb:=SecondJetRelaxedGlobalIndex.exponent_bounds p.cutoff 131071 p.L p.B p.s p.U hp.slope
  obtain ⟨V,hf,hv,hs,hc⟩:=ARW.FAY e he
    p.m p.L p.B p.s p.U 131071 p.cutoff (by decide)
    (fun i=>(hb i).1) (fun i=>(hb i).2.1) (fun i=>(hb i).2.2.1)
    (fun i=>(hb i).2.2.2.1) (fun i=>(hb i).2.2.2.2) nodes u0 u1 Kdim
    (by simpa only [hN,Dimension] using hd)
  refine ⟨V,hf,hv,?_,hc⟩
  intro P hP d hdP
  obtain ⟨i,rfl⟩:=hs P hP d hdP
  exact hb i
theorem _Q3 (p:Parameters) (hp:Shape p) (Kdim:ℕ)
    (hpos:0<Kdim) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144):
    ∃P,Interpolant p nodes u0 u1 P:=by
  obtain ⟨V,hf,hv,hb,hc⟩:=DVF p hp Kdim hd nodes u0 u1 hN
  letI:Module.Finite K V:=hf
  have hn: ∃P∈V,P≠0:=by
    by_contra h
    have hz: ∀P∈V,P=0:=by simpa using h
    have hcard:=ARN (fun i:Fin 0=>Fin.elim0 i)
      V.subtype Subtype.val_injective (by
        intro v e he
        simp [show (v:SecondJetSupport.Poly (K:=K))=0 from hz v.val v.property] at he)
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨P,hP,hne⟩:=hn
  exact ⟨P,hne,hb P hP,hc P hP⟩
theorem AMU (p:Parameters) (hp:Shape p)
    (nodes:N ↪ K) (u0 u1:N→K) (P:SecondJetSupport.Poly (K:=K))
    (hP:Interpolant p nodes u0 u1 P) (d:ℕ) (hd:d≤p.k)
    (f:Polynomial K) (hf:f.natDegree≤131071) (z:K) (A:Finset N)
    (hA:181059≤A.card) (hvalues: ∀i∈A,f.eval (nodes i)=u0 i+u1 i*z):
    SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0:=by
  have hs:=hp.contact
  have hk:=hp.retention
  have hn:=hp.degree
  apply AQ.AMU P p.m 181059 131071 p.k p.n0 d
    (by decide) (by decide) (by omega) hd ?_ nodes u0 u1 hP.2.2 f hf z A hA hvalues
  intro e he
  have hh:=(hP.2.1 e he).2.2.2.2
  dsimp [Parameters.cutoff] at hh
  norm_num
  omega
theorem ATR (p:Parameters) (hp:Shape p)
    (nodes:N ↪ K) (u0 u1:N→K) (P:SecondJetSupport.Poly (K:=K))
    (hP:Interpolant p nodes u0 u1 P) (d:ℕ) (hd:d<p.n0)
    (hfact:(d.factorial:K)≠0)
    (f:Polynomial K) (hf:f.natDegree≤131071) (z:K) (A:Finset N)
    (hA:181059≤A.card) (hvalues: ∀i∈A,f.eval (nodes i)=u0 i+u1 i*z)
    (hh: ∀j,d<j→SecondJetCoefficientSpecialization.coefficientSpecialize f z ((SecondJetCoefficients.asS P).coeff j)=0):
    SecondJetCoefficientSpecialization.coefficientSpecialize f z ((SecondJetCoefficients.asS P).coeff d)=0:=by
  have hdm:d<p.m:=lt_trans (lt_of_lt_of_le hd hp.degree) hp.contact
  have hweight: ∀e∈((SecondJetCoefficients.asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(p.m-d)*181059:=by
    intro e he
    have hb:=(hP.2.1 _ (SecondJetCoefficients.coefficient_support P d e he)).2.2.2.2
    obtain ⟨h0,h1,h2,h3,h4⟩:=SecondJetCoefficients.lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve,if_pos hd] at hb
    omega
  have hdeg:=MovingFiberLeadingCoefficient6815.coefficient_degree ((SecondJetCoefficients.asS P).coeff d)
    f z 131071 ((p.m-d)*181059) hf (by omega) hweight
  have htop:=MovingFiberLeadingCoefficient6815.specialize_top P f z d hh
  have hv:SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0:=by
    refine CAG.ALK _ f z nodes u0 u1 A (p.m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hP.2.2 i
    · rw [htop]
      exact ((Polynomial.natDegree_smul_le d.factorial _).trans_lt hdeg).trans_le
        (Nat.mul_le_mul_left (p.m-d) hA)
  rw [htop,nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by
    simpa only [map_natCast] using Polynomial.C_ne_zero.mpr hfact)
def ProperHelper (p:Parameters) (F Q:MvPolynomial (Fin 4) K) (r y t:ℕ)
    (nodes:N ↪ K) (u0 u1:N→K):Prop:=
  IsRelPrime F Q∧
  (wt RCN156.residualSWeights Q≤p.B+p.s*(r-1)∧wt RCN156.residualYSWeights Q≤p.U+p.s*(y-1)∧
    wt RCN156.residualTotalWeights Q≤p.L+p.s*(t-1))∧
  ∀f:Polynomial K,f.natDegree≤131071→ ∀z:K,∀A:Finset N,
    181059≤A.card→(∀i∈A,f.eval (nodes i)=u0 i+u1 i*z)→
      RCN319.specialization K f z F=0→RCN319.specialization K f z Q=0
theorem EMH [CharP K 2130706433]
    (p:Parameters) (hp:Shape p) (nodes:N ↪ K) (u0 u1:N→K)
    (P:SecondJetSupport.Poly (K:=K)) (hP:Interpolant p nodes u0 u1 P)
    (F:MvPolynomial (Fin 4) K) (hFi:Irreducible F) (hFT:p.L<wt RCN156.residualTotalWeights F)
    (r y t:ℕ) (hr:1≤r) (hy:1≤y) (ht:1≤t)
    (hF:wt RCN156.residualSWeights F≤r∧wt RCN156.residualYSWeights F≤y∧wt RCN156.residualTotalWeights F≤t):
    (∃Q,ProperHelper p F Q r y t nodes u0 u1)∨
      (p.n0≤(SecondJetCoefficients.asS P).natDegree∧ ∀d≤p.k,F∣SecondJetClearedHelper.helper P F (p.s-d) d):=by
  have hflags: ∀e∈P.support,2*e 1+e 3≤p.B∧e 1+e 2+e 3≤p.U∧
      e 1+e 2+e 3+e 4≤p.L:=
    fun e he=>⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
  have hS: ∀e∈P.support,e 1≤p.s:=fun e he=>(hP.2.1 e he).2.1
  have hdegree:(SecondJetCoefficients.asS P).natDegree≤p.s:=by simpa using SecondJetHelperWeights.asS_derivative_degree P p.s 0 hS
  by_cases hn:(SecondJetCoefficients.asS P).natDegree<p.n0
  · left
    let n:=(SecondJetCoefficients.asS P).natDegree
    let Q:=(SecondJetCoefficients.asS P).leadingCoeff
    have hQ:=SecondJetTotalAvoidance.leading_not_dvd P hP.1 F p.L (fun e he=>(hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw:=SecondJetHelperWeights.derivative_coefficient_weights P p.B p.U p.L 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt RCN156.residualSWeights ((SecondJetCoefficients.asS P).coeff n)≤p.B+p.s*(r-1)∧
        wt RCN156.residualYSWeights ((SecondJetCoefficients.asS P).coeff n)≤p.U+p.s*(y-1)∧
        wt RCN156.residualTotalWeights ((SecondJetCoefficients.asS P).coeff n)≤p.L+p.s*(t-1)
      omega
    · intro f hf z A hA hvalues _
      apply ATR p hp nodes u0 u1 P hP n hn
        (SecondJetOwnShape.factorial_ne n (hdegree.trans_lt hp.characteristic)) f hf z A hA hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv: ∀d≤p.k,F∣SecondJetClearedHelper.helper P F (p.s-d) d
    · exact Or.inr ⟨by omega,hdiv⟩
    · left
      push Not at hdiv
      obtain ⟨d,hd,hproper⟩:=hdiv
      refine ⟨SecondJetClearedHelper.helper P F (p.s-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hshape:=hp.slope
        have hmid:=hp.middle
        have htot:=hp.total
        have hret:=hp.retention
        have hdeg:=hp.degree
        have hw:=SecondJetHelperWeights.helper_weights P F p.B p.U p.L p.s d t y r
          (by omega) (by omega) (by omega) (by omega) hr hy ht hflags hF
        have hrr:=Nat.mul_le_mul_right (r-1) (Nat.sub_le p.s d)
        have hyy:=Nat.mul_le_mul_right (y-1) (Nat.sub_le p.s d)
        have htt:=Nat.mul_le_mul_right (t-1) (Nat.sub_le p.s d)
        omega
      · intro f hf z A hA hvalues hFzero
        exact SecondJetClearedHelper.helper_vanish P F (p.s-d) d (SecondJetHelperWeights.asS_derivative_degree P p.s d hS) f z hFzero
          (AMU p hp nodes u0 u1 P hP d hd f hf z A hA hvalues)
theorem VT [CharP K 2130706433]
    (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hpos:0<Kdim) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144)
    (F:MvPolynomial (Fin 4) K) (hFi:Irreducible F) (hFT:p.L<wt RCN156.residualTotalWeights F)
    (r y t:ℕ) (hr:1≤r) (hy:1≤y) (ht:1≤t)
    (hF:wt RCN156.residualSWeights F≤r∧wt RCN156.residualYSWeights F≤y∧wt RCN156.residualTotalWeights F≤t):
    (∃Q,ProperHelper p F Q r y t nodes u0 u1)∨
      ∃S:MovingFiberThreeSources6811.Source F,GZ.Profile S p.B p.U p.L p.s p.k p.n0:=by
  obtain ⟨P,hP⟩:=_Q3 p hp Kdim hpos hd nodes u0 u1 hN
  rcases EMH p hp nodes u0 u1 P hP F hFi hFT r y t hr hy ht hF with hh | hret
  · exact Or.inl hh
  let S:MovingFiberThreeSources6811.Source F:={
    P:=P,B:=p.B,U:=p.U,T:=p.L,s:=p.s,k:=p.k,n0:=p.n0
    hS:=fun e he=>(hP.2.1 e he).2.1
    hshape:=fun e he=>⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
    hBU:=hp.middle,hUT:=hp.total,hdn:=hp.retention
    hB:=by have:=hp.slope;have:=hp.degree;omega
    hn:=hret.1,hdiv:=hret.2}
  exact Or.inr ⟨S,by repeat' constructor⟩
end
end FF
end MergedPart3
section MergedPart4
namespace FF
set_option autoImplicit false
set_option maxHeartbeats 500000
theorem AZ (p:Parameters) (Kdim C R:ℕ)
    (hsB:2*p.s≤p.B) (hBm:p.B≤p.m) (hU:p.m+p.s≤p.U)
    (hL:p.m+p.B+p.s≤p.L) (hUT:p.U≤p.L)
    (hcaps: ∀h,h≤p.s→p.U≤(p.cutoff h+p.B-1)/131071)
    (hC:SecondJetRelaxedGlobalCounts.coefficientCount p.cutoff 131071 p.L p.B p.s p.U=C)
    (hR:SecondJetRelaxedCounts.rankBound p.m p.L p.B p.s p.U=R)
    (hfit:Kdim+262144*R≤C):Dimension p Kdim:=by
  unfold Dimension
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ hsB hBm hU hL hcaps,
    SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUT,hR,hC]
  exact hfit
end FF
end MergedPart4
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace AIA
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 900000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234 RCN244
open RCN095 renaming PolynomialInFlag → BI
open CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open MI NA
open APK ANU
open NL AGT DC
variable {K:Type} [Field K]
structure Route (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J:SecondJetSupport.Poly (K:=K)) (firstFlag delayFlag:FlagDegree):Prop where
  denominator:carrierMap F (linearH J)≠0
  cross: ∀n,F∣(linearH J)^(2*n)*RCN313.numerator K F n-
    (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n
  first:RCN095.PolynomialInFlag firstFlag (PO (linearH J) (linearG J))
  later: ∀mu delay:ℕ,1≤mu→delay≤mu→RCN095.PolynomialInFlag (mu • delayFlag)
    (surfaceMap (RCN135.polynomialEmbedding K)
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay)))
def firstFlag (r y t:ℕ):FlagDegree:=
  ⟨(t-y)*131072,1+(y-r)*131072,r*131072⟩
def delayFlag (r y t:ℕ):FlagDegree:=
  ⟨(t-y)*131073,1+(y-r)*131073,r*131073⟩
theorem GCI [CharP K 2130706433]
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hS:J.degreeOf 1=1)
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (cap:ℕ) (hT: ∀e∈J.support,e 1+e 2+e 3+e 4≤cap)
    (hFT:cap<wt RCN156.residualTotalWeights F)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0)
    (r y t:ℕ) (hry:r≤y) (hyt:y≤t)
    (hw: ∀n,wt RCN156.residualSWeights (numerators (linearH J) (linearG J) n)≤r*n∧
      wt RCN156.residualYSWeights (numerators (linearH J) (linearG J) n)≤1+y*n∧
      wt RCN156.residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+t*n):
    Route F J (firstFlag r y t) (delayFlag r y t):=by
  refine ⟨CQR J hJ hS F cap hT hFT,
    EJN J hJ hS F hpos hchar cap hT hFT hroot,?_,?_⟩
  · have hh:=hw 131072
    have he:=CUS (RCN135.polynomialEmbedding K) _ (r*131072) (1+y*131072) (1+t*131072)
      (by omega) (by omega) hh.1 hh.2.1 hh.2.2
    convert he using 1<;>simp only [firstFlag,RCN326.w,PO]
    · congr 1<;>omega
  · intro mu d hm hd
    have hh:=hw (RCN326.w+1+d)
    have hr:wt RCN156.residualSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(r*131073):=by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left r hd,Nat.mul_le_mul_left (r*131072) hm]
    have hy:wt RCN156.residualYSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+y*131073):=by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left y hd,Nat.mul_le_mul_left (y*131072) hm]
    have ht:wt RCN156.residualTotalWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+t*131073):=by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left t hd,Nat.mul_le_mul_left (t*131072) hm]
    have he:=CUS (RCN135.polynomialEmbedding K) _ (mu*(r*131073))
      (mu*(1+y*131073)) (mu*(1+t*131073)) (by nlinarith) (by nlinarith) hr hy ht
    have eqflag:(⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩:FlagDegree)=mu • delayFlag r y t:=by
      have hz:(1+t*131073)-(1+y*131073)=(t-y)*131073:=by
        rw [Nat.sub_mul t y 131073]
        omega
      have hyz:(1+y*131073)-r*131073=1+(y-r)*131073:=by
        rw [Nat.sub_mul y r 131073]
        exact Nat.add_sub_assoc (Nat.mul_le_mul_right 131073 hry) 1
      change (⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩:FlagDegree)=
        ⟨mu*((t-y)*131073),mu*(1+(y-r)*131073),mu*(r*131073)⟩
      rw [←Nat.mul_sub mu (1+t*131073) (1+y*131073),
        ←Nat.mul_sub mu (1+y*131073) (r*131073),hz,hyz]
    rw [eqflag] at he
    exact he
variable {I:Type} {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ} {stageSupport:RCN275.ResidualSupportParameters}
variable {first delay:FlagDegree}
theorem FLD
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (J:SecondJetSupport.Poly (K:=K)) (hroute:Route S.F J first delay):
    ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (linearH J):=by
  have hF:Irreducible S.F:=Fact.out
  have hn: ¬S.F∣linearH J:=fun hd=>hroute.denominator ((TY S.F _).mpr hd)
  have hrel:=WW.EGB S.F (linearH J) hF.ne_zero
    (hF.isRelPrime_iff_not_dvd.mpr hn)
  intro hd
  exact S.MW.not_isUnit (hrel S.RR hd)
end
end AIA
end MergedPart1
section MergedPart2
namespace CUT
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN121 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open RCN095 renaming PolynomialInFlag → BI
open UQ WB JS
open AEG ARK NL
open MI NA
open AIA XT
theorem EMM {A:Type} [Fintype A]
    (m z u v:A→ℕ) (a b c:ℕ):
    (∑ i,m i*(a*z i+b*u i+c*v i))=
      a*(∑ i,m i*z i)+b*(∑ i,m i*u i)+c*(∑ i,m i*v i):=by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
variable {firstFlag delayFlag:FlagDegree}
theorem DIE
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (J:SecondJetSupport.Poly (K:=K)) (hroute:Route S.F J firstFlag delayFlag)
    {A:Type} [Fintype A] (component:A→CM S)
    (hz: ∀a,Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (hgate: ∀a,
      (letI:=(RCN022.elementEmbedding (GenericField K) (RCN002.CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc (GenericField K)) (RCN002.CoordinateField (GenericField K) (component a).1))∧
      (letI:=(RCN022.elementEmbedding (GenericField K) (RCN002.CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc (GenericField K)) (RCN002.CoordinateField (GenericField K) (component a).1)))
    (D:GammaFrame (fun a=>(component a).1) S.G) (a:A)
    (hH:surfaceMap (RCN135.polynomialEmbedding K) (linearH J)∉(component a).1)
    (delay:ℕ) (hdelay:delay≤FO S (DN S hfirst) (component a))
    (hproper:RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1+delay)∉(component a).1):
    (stageSeeds S (component a)).card≤
      FO S (DN S hfirst) (component a)*
        BET D hz a delayFlag:=by
  classical
  let m:=FO S (DN S hfirst) (component a)
  let N:=surfaceMap (RCN135.polynomialEmbedding K)
    (numerators (linearH J) (linearG J) (RCN326.w+1+delay))
  let seeds:=stageSeeds S (component a)
  let point:=DK (RCN135.polynomialEmbedding K) S.selected
  let points:=seeds.image point
  have hN:=hroute.later m delay
    (YW S hfirst (component a)) hdelay
  have hNproper:=DJU S (component a) (linearH J) (linearG J)
    (RCN326.w+1+delay) (hroute.cross _) hH hproper
  have hpoints: ∀v∈points,(component a).1≤RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    exact RCN264.componentSeeds_on_prime (GenericField K) S.G _ _ Gamma point (component a) gamma hgamma
  have hzero: ∀v∈points,MvPolynomial.aeval v N=0:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    have hGamma:=RCN264.componentSeeds_subset (GenericField K) S.G _ _ Gamma point (component a) hgamma
    exact EFB S (linearH J) (linearG J) (RCN326.w+1+delay)
      (by omega) (hroute.cross _) gamma hGamma
  have hc:=(FNI D hz hgate a).zero_le (m • delayFlag) N hN hNproper
    points hpoints hzero
  have hcard:points.card=seeds.card:=Finset.card_image_of_injective _
    (ABD (RCN135.polynomialEmbedding K) S.selected)
  have hcost:BET D hz a (m • delayFlag)=m*BET D hz a delayFlag:=by
    simp only [BET,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
  rw [hcard,hcost] at hc
  exact hc
theorem ENS
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (J:SecondJetSupport.Poly (K:=K)) (hroute:Route S.F J firstFlag delayFlag)
    (surfaceFlag:FlagDegree) (hS:RCN095.PolynomialInFlag surfaceFlag S.G)
    (hsmall:flagMixed surfaceFlag firstFlag unitZFlag<p):
    (∑ C:AWW S hfirst (linearH J),(stageSeeds S C.1).card)≤
      flagMixed surfaceFlag firstFlag delayFlag:=by
  classical
  let A:=AWW S hfirst (linearH J)
  let component:A→CM S:=Subtype.val
  let hz (a:A):=a.2.1
  by_cases hA:Nonempty A
  · let a0:A:=Classical.choice hA
    have hH: ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (linearH J):=by
      intro hd
      exact a0.2.2.1 (a0.1.1.mem_of_dvd hd (EN (GenericField K) S.G _ _ a0.1))
    have hproper:=CMJ S hfirst (linearH J) (linearG J) (hroute.cross _) hH
    have hT:=hroute.first
    have gate (a:A):=DML S (linearH J) (linearG J) (hroute.cross _) hproper
      surfaceFlag firstFlag hS hT hsmall a.1 (hz a)
    obtain ⟨D,hD⟩:=CLX S hfirst (linearH J) (linearG J)
      (hroute.cross _) hH component Subtype.val_injective hz
      surfaceFlag firstFlag hS hT hsmall
    let m (a:A):=FO S (DN S hfirst) a.1
    have hcount (a:A):(stageSeeds S a.1).card≤m a*BET D hz a delayFlag:=by
      obtain ⟨delay,-,hd,hproper⟩:=a.2.2.2
      exact DIE S hfirst J hroute component hz gate D a a.2.2.1 delay hd hproper
    calc
      _≤∑ a:A,m a*BET D hz a delayFlag:=
        Finset.sum_le_sum (fun a _=>hcount a)
      _=delayFlag.zOnly*(∑ a:A,m a*frameCost D hz .z a)+
          delayFlag.yz*(∑ a:A,m a*frameCost D hz .u a)+
          delayFlag.all*(∑ a:A,m a*frameCost D hz .v a):=by
        exact EMM m (frameCost D hz .z) (frameCost D hz .u) (frameCost D hz .v)
          delayFlag.zOnly delayFlag.yz delayFlag.all
      _≤delayFlag.zOnly*flagMixed surfaceFlag firstFlag unitZFlag+
          delayFlag.yz*flagMixed surfaceFlag firstFlag unitYZFlag+
          delayFlag.all*flagMixed surfaceFlag firstFlag unitAllFlag:=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (hD .z)) (Nat.mul_le_mul_left _ (hD .u)))
          (Nat.mul_le_mul_left _ (hD .v))
      _=_:=(RCN121.flagMixed_projection_decomposition surfaceFlag firstFlag delayFlag).symm
  · letI:IsEmpty A:=⟨fun a=>hA ⟨a⟩⟩
    change (∑ a:A,(stageSeeds S a.1).card)≤_
    simp
end
end CUT
end MergedPart2
section MergedPart3
namespace BTA
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN002 RCN022 RCN042 RCN051 RCN068 RCN074 RCN086 RCN093 RCN095
open RCN095 renaming PolynomialInFlag → BI
open RCN135 RCN136 RCN159 RCN174 RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open JS YL
open UQ WB AEG
open XT NL MI
open DC XK
open AYN ATE WW
open AIA
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
variable {firstFlag delayFlag:FlagDegree}
theorem EJI
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (J:SecondJetSupport.Poly (K:=K)) (hroute:Route S.F J firstFlag delayFlag)
    (hH: ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (linearH J))
    (surfaceFlag:FlagDegree) (hS:RCN095.PolynomialInFlag surfaceFlag S.G):
    (∑ C:AXO S,(stageSeeds S C.1).card)≤
      flagMixed surfaceFlag firstFlag unitYZFlag+flagMixed surfaceFlag firstFlag unitAllFlag:=by
  have hproper:=CMJ S hfirst (linearH J) (linearG J) (hroute.cross _) hH
  have hcard:=DVJ (fun a:AXO S=>a.1.1)
    (fun a b h=>Subtype.ext (Subtype.ext h))
    (fun a=>PU (GenericField K) S.G _ _ a.1) (fun a=>a.2)
    S.G (AGT.PO (linearH J) (linearG J)) S.MW.ne_zero
    (fun hz=>hproper (hz ▸ dvd_zero _)) (S.MW.isRelPrime_iff_not_dvd.mpr hproper)
    (fun a=>EN (GenericField K) S.G _ _ a.1)
    (fun a=>BTW S (linearH J) (linearG J) (hroute.cross _) a.1)
    surfaceFlag firstFlag hS (hroute.first)
  calc
    _≤∑ _:AXO S,1:=by
      apply Finset.sum_le_sum
      intro a _
      exact DNM (RCN135.polynomialEmbedding K) S.selected _ a.1.1 a.2
        (fun gamma hgamma=>RCN264.componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
          (DK (RCN135.polynomialEmbedding K) S.selected) a.1 gamma hgamma)
    _=Fintype.card (AXO S):=by simp
    _≤_:=hcard
theorem EEB
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (J:SecondJetSupport.Poly (K:=K)) (hroute:Route S.F J firstFlag delayFlag)
    (hH: ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (linearH J))
    (surfaceFlag:FlagDegree) (hS:RCN095.PolynomialInFlag surfaceFlag S.G)
    (hsmall:flagMixed surfaceFlag firstFlag unitZFlag<p)
    (agreements bound seedCap slopeCap:ℕ)
    (hnodes:S.nodes.card=agreements+errorCap)
    (hagreement: ∀gamma∈Gamma,agreements≤(S.AJW gamma).card)
    (hwa:RCN326.w<agreements) (hshort:RCN326.w+1≤bound) (hchar:bound<p)
    (hbox:S.F∈RCN174.globalCoefficientBox K bound RCN326.w seedCap slopeCap):
    (∑ C:BJA S,(stageSeeds S C.1).card)≤
      (errorCap+1)*flagMixed surfaceFlag firstFlag unitYZFlag:=by
  let A:=BJA S
  let component:A→CM S:=Subtype.val
  let hz (a:A):=a.2.1
  have hproper:=CMJ S hfirst (linearH J) (linearG J) (hroute.cross _) hH
  have hT:=hroute.first
  have gate (a:A):=DML S (linearH J) (linearG J) (hroute.cross _) hproper
    surfaceFlag firstFlag hS hT hsmall a.1 (hz a)
  obtain ⟨D,hD⟩:=CLX S hfirst (linearH J) (linearG J)
    (hroute.cross _) hH component Subtype.val_injective hz
    surfaceFlag firstFlag hS hT hsmall
  let m (a:A):=FO S (DN S hfirst) a.1
  have hcount (a:A):(stageSeeds S a.1).card≤(errorCap+1)*frameCost D hz .u a:=by
    let base:RCN341.SeparableLiteralCoordinate a.1.1:=⟨2,hz a,(gate a).1,(gate a).2⟩
    have hpole:=DHE D hz gate .u a
    have hprofile:=AON S a.1 hfirst
      bound seedCap slopeCap (frameCost D hz .u a) (by decide:1≤RCN326.w)
      hshort hchar hbox a.2.2 hpole
    have hpos:1≤frameCost D hz .u a:=by
      letI:=(RCN022.elementEmbedding (GenericField K) (RCN002.CoordinateField (GenericField K) a.1.1)
        (RCN093.flagEvaluation (GenericField K) a.1.1 D.lam D.mu (D.mu*D.lam)
          (MvPolynomial.X (Axis.u.order 0))) (frame_trans D hz .u a)).toRingHom.toAlgebra
      letI:=(frame_gate D hz gate .u a (frame_trans D hz .u a)).1
      exact Module.finrank_pos
    have hsub:stageSeeds S a.1⊆Gamma:=RCN264.componentSeeds_subset (GenericField K) S.G _ _ Gamma
      (DK (RCN135.polynomialEmbedding K) S.selected) a.1
    apply RCN145.VP
      (RCN135.polynomialEmbedding K) a.1.1 S.F
      (RP S a.1) (JX S a.1)
      base p RCN326.w agreements errorCap (frameCost D hz .u a)
      S.WG hwa hpos hprofile
      S.selected (stageSeeds S a.1) S.nodes x S.u0 S.u1 S.x_injective hnodes
    · intro gamma hg;exact S.degree_le gamma (hsub hg)
    · intro gamma hg;exact S.solution gamma (hsub hg)
    · intro gamma hg;exact S.regular gamma (hsub hg)
    · intro gamma hg
      exact RCN264.componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) a.1 gamma hg
    · intro gamma hg
      exact hagreement gamma (hsub hg)
    · exact KX S.selected Gamma (stageSeeds S a.1) RCN326.w errorCap
        hsub S.BNN
  have hsum:(∑ a:A,frameCost D hz .u a)≤flagMixed surfaceFlag firstFlag unitYZFlag:=by
    calc
      _≤∑ a:A,m a*frameCost D hz .u a:=Finset.sum_le_sum (fun a _=>by
        have hh:=Nat.mul_le_mul_right (frameCost D hz .u a) (YW S hfirst a.1)
        simpa only [one_mul] using hh)
      _≤_:=hD .u
  calc
    _≤∑ a:A,(errorCap+1)*frameCost D hz .u a:=Finset.sum_le_sum (fun a _=>hcount a)
    _=(errorCap+1)*(∑ a:A,frameCost D hz .u a):=(Finset.mul_sum _ _ _).symm
    _≤_:=Nat.mul_le_mul_left _ hsum
end
end BTA
end MergedPart3
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace BZS
open MvPolynomial CW DJ XB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open scoped MonomialOrder
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
noncomputable section
variable {K:Type*} [Field K]
def order:MonomialOrder (Fin 6):=MonomialOrder.lex
def embed:(Fin 5→₀ ℕ)→+(Fin 6→₀ ℕ) where
  toFun e:=Finsupp.single 0 (Finsupp.weight codeWeights e)+
    Finsupp.single 1 (e 0)+Finsupp.single 2 (e 1)+
    Finsupp.single 3 (e 2)+Finsupp.single 4 (e 3)+Finsupp.single 5 (e 4)
  map_zero' :=by simp
  map_add' a b:=by ext i;fin_cases i<;>simp [Finsupp.add_apply,map_add]
theorem embed_zero (e:Fin 5→₀ ℕ):embed e 0=Finsupp.weight codeWeights e:=by
  simp [embed]
theorem embed_succ (e:Fin 5→₀ ℕ) (i:Fin 5):embed e i.succ=e i:=by
  fin_cases i<;>simp [embed]
theorem embed_injective:Function.Injective embed:=by
  intro a b hab
  ext i
  simpa only [embed_succ] using congrArg (fun e:Fin 6→₀ ℕ↦e i.succ) hab
def lift:SecondJetSupport.Poly (K:=K)→+*MvPolynomial (Fin 6) K:=
  AddMonoidAlgebra.mapDomainRingHom K embed
theorem lift_injective:Function.Injective (lift (K:=K)):=
  AddMonoidAlgebra.mapDomain_injective embed_injective
theorem lift_ne_zero (P:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0):lift P ≠ 0:=by
  intro hz
  apply hP
  exact lift_injective (by simpa only [map_zero] using hz)
theorem support_lift (P:SecondJetSupport.Poly (K:=K)):(lift P).support=P.support.image embed:=
  Finsupp.mapDomain_support_of_injective embed_injective _
theorem FKW (P:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0):
    ∃e ∈ P.support,embed e=order.degree (lift P):=by
  have he:=order.degree_mem_support (lift_ne_zero P hP)
  rw [support_lift] at he
  exact Finset.mem_image.mp he
def leading (P:SecondJetSupport.Poly (K:=K)):Fin 5→₀ ℕ:=by
  classical
  exact if hP:P ≠ 0 then (FKW P hP).choose else 0
theorem leading_spec (P:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0):
    leading P ∈ P.support∧embed (leading P)=order.degree (lift P):=by
  classical
  rw [leading,dif_pos hP]
  exact (FKW P hP).choose_spec
theorem GXX (a b:Fin 6→₀ ℕ) (h:a ≼[order] b):a 0≤b 0:=by
  change toLex a≤toLex b at h
  by_contra hn
  have hba:toLex b<toLex a:=by
    rw [Finsupp.Lex.lt_iff]
    refine ⟨0,?_,?_⟩
    · intro j hj
      exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
    · exact Nat.lt_of_not_ge hn
  exact (not_lt_of_ge h) hba
theorem GSI (P:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0):
    Finsupp.weight codeWeights (leading P)=weightedTotalDegree codeWeights P:=by
  apply le_antisymm
  · exact le_weightedTotalDegree codeWeights (leading_spec P hP).1
  · apply Finset.sup_le
    intro e he
    have hm:embed e ∈ (lift P).support:=by
      rw [support_lift]
      exact Finset.mem_image.mpr ⟨e,he,rfl⟩
    have hz:=GXX _ _ (order.le_degree hm)
    rw [← (leading_spec P hP).2] at hz
    simpa only [embed_zero] using hz
theorem leading_mul (P Q:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0) (hQ:Q ≠ 0):
    leading (P*Q)=leading P+leading Q:=by
  apply embed_injective
  rw [map_add,(leading_spec P hP).2,(leading_spec Q hQ).2,
    (leading_spec (P*Q) (mul_ne_zero hP hQ)).2,map_mul,
    order.degree_mul (lift_ne_zero P hP) (lift_ne_zero Q hQ)]
theorem leading_pow (P:SecondJetSupport.Poly (K:=K)) (hP:P ≠ 0) (q:ℕ):
    leading (P^q)=q • leading P:=by
  apply embed_injective
  rw [map_nsmul,(leading_spec P hP).2,
    (leading_spec (P^q) (pow_ne_zero _ hP)).2,map_pow,order.degree_pow]
theorem EVI (C k n0 gap q cJ:ℕ)
    (P J Q:SecondJetSupport.Poly (K:=K)) (hJ:J ≠ 0) (hQ:Q ≠ 0)
    (heq:P=J^q*Q)
    (hb: ∀e ∈ P.support,
      Finsupp.weight codeWeights e+SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*gap<C)
    (hcJ:cJ≤weightedTotalDegree codeWeights J):
    Finsupp.weight codeWeights (leading Q)<
      C-q*cJ-min ((leading Q) 1) k*gap:=by
  have hP:P ≠ 0:=by rw [heq];exact mul_ne_zero (pow_ne_zero _ hJ) hQ
  have hlead:leading P=q • leading J+leading Q:=by
    rw [heq,leading_mul _ _ (pow_ne_zero _ hJ) hQ,leading_pow J hJ q]
  have hw:Finsupp.weight codeWeights (leading P)=
      q*Finsupp.weight codeWeights (leading J)+Finsupp.weight codeWeights (leading Q):=by
    rw [hlead,map_add,map_nsmul]
    simp
  have hh:(leading Q) 1≤(leading P) 1:=by
    rw [hlead,Finsupp.add_apply,Finsupp.smul_apply]
    exact Nat.le_add_left _ _
  have hmin:min ((leading Q) 1) k≤
      SecondJetRelaxedDifferentiation.reserve k n0 ((leading P) 1):=by
    apply (min_le_min_right k hh).trans
    unfold SecondJetRelaxedDifferentiation.reserve
    split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hlow:cJ≤Finsupp.weight codeWeights (leading J):=by
    rwa [GSI J hJ]
  have hmul:=Nat.mul_le_mul_left q hlow
  have hpenalty:=Nat.mul_le_mul_right gap hmin
  have hbound:=hb (leading P) (leading_spec P hP).1
  omega
theorem DMU {W I:Type*} [AddCommGroup W] [Module K W]
    [Fintype I] (e:I→Fin 5→₀ ℕ) (f:W→ₗ[K] SecondJetSupport.Poly (K:=K))
    (hf:Function.Injective f)
    (hvisible: ∀v:W,f v ≠ 0→ ∃i,leading (f v)=e i):
    Module.finrank K W≤Fintype.card I:=by
  classical
  let A:W→ₗ[K] (I→K):=LinearMap.pi (fun i↦(MvPolynomial.lcoeff K (e i)).comp f)
  have hi:Function.Injective A:=by
    intro v u h
    by_contra hvu
    have hdiff:f (v-u) ≠ 0:=by
      intro hz
      apply hvu
      apply sub_eq_zero.mp
      exact hf (by simpa only [map_zero] using hz)
    obtain ⟨i,hi⟩:=hvisible (v-u) hdiff
    have hnonzero:=MvPolynomial.mem_support_iff.mp (leading_spec (f (v-u)) hdiff).1
    rw [hi] at hnonzero
    apply hnonzero
    have hcoeff:(f v).coeff (e i)=(f u).coeff (e i):=congrFun h i
    rw [map_sub,MvPolynomial.coeff_sub,hcoeff,sub_self]
  simpa using LinearMap.finrank_le_finrank_of_injective hi
open DA
open SecondJetRelaxedGlobalIndex (Index budget exponent)
open SecondJetRelaxedGlobalIndex renaming exponent_injective → ACD
open SecondJetRelaxedGlobalCounts renaming coefficientCount → AW
def cutoff (p:SourceCaps) (a:OwnerBox) (k gap h:ℕ):=
  remC p a-min h k*gap
def count (p:SourceCaps) (a:OwnerBox) (k gap:ℕ):=
  SecondJetRelaxedGlobalCounts.coefficientCount (cutoff p a k gap) 131071 (remT p a) (remB p a) (remS p a) (remU p a)
def exponent (D:ℕ→ℕ) (T R S U:ℕ)
    (i:Index D 131071 T R S U):Fin 5→₀ ℕ:=
  SecondJetRelaxedGlobalIndex.exponent i
theorem AKF (D:ℕ→ℕ) (T R S U:ℕ) (e:Fin 5→₀ ℕ)
    (hc:e 0+131069*e 1+131071*e 2+131070*e 3<D (e 1))
    (ht:e 1+e 2+e 3+e 4≤T)
    (hr:2*e 1+e 3≤R) (hs:e 1≤S) (hu:e 1+e 2+e 3≤U):
    e ∈ Set.range (exponent D T R S U):=by
  have hh:e 1<S+1:=by omega
  have hrr:e 3<R-2*e 1+1:=by omega
  have hx:e 0<SecondJetRelaxedGlobalIndex.budget D 131071 (e 1) (e 3)-131071*e 2:=by
    simp only [SecondJetRelaxedGlobalIndex.budget]
    omega
  have hy:e 2<SecondJetRelaxedGlobalIndex.yCount D 131071 U (e 1) (e 3):=by
    simp only [SecondJetRelaxedGlobalIndex.yCount,SecondJetRelaxedGlobalIndex.budget]
    omega
  have hz:e 4<T+1-e 1-e 3-e 2:=by omega
  refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hrr⟩,⟨e 2,hy⟩,⟨e 0,hx⟩,⟨e 4,hz⟩⟩,?_⟩
  ext i
  fin_cases i<;>simp [exponent,SecondJetRelaxedGlobalIndex.exponent]
theorem EOB (p:SourceCaps) (a:OwnerBox) (k n0 gap:ℕ)
    (P J Q:SecondJetSupport.Poly (K:=K)) (hJ:J ≠ 0) (hQ:Q ≠ 0)
    (heq:P=J^a.q*Q) (hP:Bounds p P) (ha:Covers a J)
    (hsource: ∀e ∈ P.support,
      Finsupp.weight codeWeights e+SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*gap<p.C):
    leading Q ∈ Set.range
      (exponent (cutoff p a k gap) (remT p a) (remB p a) (remS p a) (remU p a)):=by
  obtain ⟨_,hc,ht,hb,hS,hu⟩:=DA.AUL
    p a P J Q hJ hQ heq hP ha
  have hcJ:=XB.BKI J hJ a.loU a.hiB ha.2.2.2.1 ha.2.1
  have c:=EVI p.C k n0 gap a.q (131071*a.loU-a.hiB)
    P J Q hJ hQ heq hsource hcJ
  have he:=(leading_spec Q hQ).1
  have t:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights he).trans ht
  have b:=(le_weightedTotalDegree slopeWeights he).trans hb
  have s:=(MvPolynomial.monomial_le_degreeOf 1 he).trans hS
  have u:=(le_weightedTotalDegree HA he).trans hu
  simp [JW,codeWeights,Koala6831Ordinary.totalWeights,slopeWeights,HA] at c t b u
  apply AKF
  all_goals
    try dsimp only [remS,remU,cutoff,remC]
    omega
theorem ASJ (p:SourceCaps) (a:OwnerBox) (k n0 gap Kdim:ℕ)
    (V:Submodule K (SecondJetSupport.Poly (K:=K))) [Module.Finite K V]
    (hdim:Kdim≤Module.finrank K V)
    (hb: ∀P ∈ V,Bounds p P)
    (hsource: ∀P ∈ V,∀e ∈ P.support,
      Finsupp.weight codeWeights e+SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*gap<p.C)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J ≠ 0) (ha:Covers a J)
    (hgood:(Impossible p a∧0<Kdim)∨count p a k gap<Kdim):
    ∃P ∈ V,¬J^a.q ∣ P:=by
  by_contra hno
  have hd: ∀P ∈ V,J^a.q ∣ P:=by simpa only [not_exists,not_and,not_not] using hno
  let hv: ∀v:V,J^a.q ∣ v.val:=fun v↦hd v.val v.property
  let f:=BKC V J a.q hJ hv
  have hf:Function.Injective f:=by
    intro v u he
    apply Subtype.ext
    rw [RV V J a.q hv v,RV V J a.q hv u]
    exact congrArg (fun Q↦J^a.q*Q) he
  rcases hgood with ⟨hbad,hpos⟩ | hcount
  · have hz: ∀v,f v=0:=by
      intro v
      by_contra hn
      exact (DA.AUL p a v.val J (f v) hJ hn
        (RV V J a.q hv v) (hb v.val v.property) ha).1 hbad
    have hcard:=ARN (fun i:Fin 0↦Fin.elim0 i) f hf
      (by intro v e he;simp [hz v] at he)
    simp only [Fintype.card_fin] at hcard
    omega
  · have hvisible: ∀v,f v ≠ 0→ ∃i,
        leading (f v)=exponent (cutoff p a k gap) (remT p a) (remB p a) (remS p a) (remU p a) i:=by
      intro v hn
      obtain ⟨i,hi⟩:=EOB p a k n0 gap v.val J (f v) hJ hn
        (RV V J a.q hv v) (hb v.val v.property) ha (hsource v.val v.property)
      exact ⟨i,hi.symm⟩
    have hcard:=DMU _ f hf hvisible
    have hUT:remU p a≤remT p a:=min_le_right _ _
    rw [show Fintype.card (Index (cutoff p a k gap) 131071 (remT p a) (remB p a)
      (remS p a) (remU p a))=count p a k gap by
        exact SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUT] at hcard
    omega
end
end BZS
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace AYB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 20000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open BD CB
open MovingFiberThreeSources6811 (direction weight)
open DC FN
open RCN234 RCN156
open SecondJetCoefficients (liftExponent)
variable {K:Type} [Field K] [CharP K 2130706433]
theorem DTC
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT:1700<wt RCN156.residualTotalWeights F)
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (hT:total P≤1700)
    (d:ℕ) (hd:0<d)
    (hpower:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^d∣(SecondJetCoefficients.asS P).map (carrierMap F)):
    ∃S:MovingFiberThreeSources6811.Source F,S.P=P∧d≤S.d:=by
  have hshapeT: ∀e∈P.support,e 1+e 2+e 3+e 4≤1700:=by
    intro e he
    have hh:=(Finset.le_sup (f:=Finsupp.weight Koala6831Ordinary.totalWeights) he).trans hT
    simpa [JW,Koala6831Ordinary.totalWeights] using hh
  have hne:=AKB F P hP 1700 hshapeT hFT
  let m:=((SecondJetCoefficients.asS P).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)
  have hdm:d≤m:=(Polynomial.le_rootMultiplicity_iff hne).mpr hpower
  have hn:=_Q15 P
  have hshape: ∀e∈P.support,2*e 1+e 3≤slope P∧
      e 1+e 2+e 3≤max (slope P) (middle P)∧
      e 1+e 2+e 3+e 4≤max (slope P) (total P):=by
    intro e he
    have hb:Finsupp.weight slopeWeights e≤slope P:=Finset.le_sup he
    have hu:Finsupp.weight HA e≤middle P:=Finset.le_sup he
    have ht:Finsupp.weight Koala6831Ordinary.totalWeights e≤total P:=Finset.le_sup he
    refine ⟨?_,?_,?_⟩
    · simpa [JW,slopeWeights,Nat.mul_comm] using hb
    · have hu' :e 1+e 2+e 3≤middle P:=by simpa [JW,HA] using hu
      exact hu'.trans (le_max_right _ _)
    · have ht' :e 1+e 2+e 3+e 4≤total P:=by simpa [JW,Koala6831Ordinary.totalWeights] using ht
      exact ht'.trans (le_max_right _ _)
  obtain ⟨S,hSP,hSd,_⟩:=DBC P F hpos hsmall m (order P)
    (slope P) (max (slope P) (middle P)) (max (slope P) (total P))
    (by omega) rfl hn.2.2.1 (le_max_left _ _) (max_le_max (le_refl _) hn.1) hshape rfl
  exact ⟨S,hSP,by omega⟩
end
end AYB
end MergedPart0
section MergedPart1
namespace ZD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 20000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open BD CB
open MovingFiberThreeSources6811 (direction weight)
open DC FN
open RCN234 RCN156
open SecondJetCoefficients (liftExponent)
variable {K:Type} [Field K] [CharP K 2130706433]
theorem UN
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (cap:ℕ) (hFT:cap<wt RCN156.residualTotalWeights F)
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (hT:total P≤cap)
    (d:ℕ) (hd:0<d)
    (hpower:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^d ∣
      (SecondJetCoefficients.asS P).map (carrierMap F)):
    ∃S:MovingFiberThreeSources6811.Source F,S.P=P∧d≤S.d:=by
  have hshapeT: ∀e∈P.support,e 1+e 2+e 3+e 4≤cap:=by
    intro e he
    have hh:=(Finset.le_sup (f:=Finsupp.weight Koala6831Ordinary.totalWeights) he).trans hT
    simpa [JW,Koala6831Ordinary.totalWeights] using hh
  have hne:=AKB F P hP cap hshapeT hFT
  let m:=((SecondJetCoefficients.asS P).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)
  have hdm:d≤m:=(Polynomial.le_rootMultiplicity_iff hne).mpr hpower
  have hn:=_Q15 P
  have hshape: ∀e∈P.support,2*e 1+e 3≤slope P∧
      e 1+e 2+e 3≤max (slope P) (middle P)∧
      e 1+e 2+e 3+e 4≤max (slope P) (total P):=by
    intro e he
    have hb:Finsupp.weight slopeWeights e≤slope P:=Finset.le_sup he
    have hu:Finsupp.weight HA e≤middle P:=Finset.le_sup he
    have ht:Finsupp.weight Koala6831Ordinary.totalWeights e≤total P:=Finset.le_sup he
    refine ⟨?_,?_,?_⟩
    · simpa [JW,slopeWeights,Nat.mul_comm] using hb
    · have hu' :e 1+e 2+e 3≤middle P:=by simpa [JW,HA] using hu
      exact hu'.trans (le_max_right _ _)
    · have ht' :e 1+e 2+e 3+e 4≤total P:=by simpa [JW,Koala6831Ordinary.totalWeights] using ht
      exact ht'.trans (le_max_right _ _)
  obtain ⟨S,hSP,hSd,_⟩:=DBC P F hpos hsmall m (order P)
    (slope P) (max (slope P) (middle P)) (max (slope P) (total P))
    (by omega) rfl hn.2.2.1 (le_max_left _ _) (max_le_max (le_refl _) hn.1) hshape rfl
  exact ⟨S,hSP,by omega⟩
end
end ZD
end MergedPart1
section MergedPart2
namespace ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open FF
open SecondJetCoefficients (liftExponent)
open DC CB BD
open MovingFiberThreeSources6811 (direction weight)
open RCN234 RCN156
def caps (p:Parameters):DA.SourceCaps:=
  ⟨p.m*181059,p.L,p.B,p.s,p.U⟩
variable {K N:Type} [Field K] [Fintype N]
theorem CTV (p:Parameters) (hp:Shape p) (P:SecondJetSupport.Poly (K:=K)) (hb:Bounds p P):
    DA.Bounds (caps p) P:=by
  have hc:weightedTotalDegree codeWeights P≤p.m*181059-1:=by
    apply Finset.sup_le
    intro e he
    have hh:=(hb e he).2.2.2.2
    have hcut:p.cutoff (e 1)≤p.m*181059:=Nat.sub_le _ _
    simp [JW,codeWeights]
    omega
  have hm:0<p.m:=lt_of_le_of_lt (Nat.zero_le _) hp.contact
  refine ⟨by dsimp [caps];omega,?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    simpa [caps,JW,Koala6831Ordinary.totalWeights] using (hb e he).2.2.2.1
  · apply Finset.sup_le
    intro e he
    simpa [caps,JW,slopeWeights,Nat.mul_comm] using (hb e he).1
  · exact MvPolynomial.degreeOf_le_iff.mpr (fun e he=>(hb e he).2.1)
  · apply Finset.sup_le
    intro e he
    simpa [caps,JW,HA] using (hb e he).2.2.1
def strongCount (p:Parameters) (a:DA.OwnerBox):ℕ:=
  min (DA.count (caps p) a)
    (BZS.count (caps p) a p.k 49990)
theorem BIV
    (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (a:DA.OwnerBox)
    (ha:DA.Covers a J)
    (hgood:(DA.Impossible (caps p) a∧0<Kdim)∨
      DA.count (caps p) a<Kdim):
    ∃P,Interpolant p nodes u0 u1 P∧ ¬J^a.q∣P:=by
  obtain ⟨V,hf,hv,hb,hc⟩:=DVF p hp Kdim hd nodes u0 u1 hN
  letI:Module.Finite K V:=hf
  obtain ⟨P,hP,hnot⟩:=DA.ASJ (caps p) a Kdim
    V hv (fun P hP=>CTV p hp P (hb P hP)) J hJ ha hgood
  exact ⟨P,⟨by intro hz;exact hnot (by rw [hz];exact dvd_zero _),hb P hP,hc P hP⟩,hnot⟩
theorem CWH
    (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (a:DA.OwnerBox)
    (ha:DA.Covers a J)
    (hgood:(DA.Impossible (caps p) a∧0<Kdim)∨
      BZS.count (caps p) a p.k 49990<Kdim):
    ∃P,Interpolant p nodes u0 u1 P∧ ¬J^a.q∣P:=by
  obtain ⟨V,hf,hv,hb,hc⟩:=DVF p hp Kdim hd nodes u0 u1 hN
  letI:Module.Finite K V:=hf
  obtain ⟨P,hP,hnot⟩:=BZS.ASJ (caps p) a p.k p.n0 49990 Kdim
    V hv (fun P hP=>CTV p hp P (hb P hP)) (by
      intro P hP e he
      have h:=(hb P hP e he).2.2.2.2
      simp only [Parameters.cutoff] at h
      simp only [caps]
      simp [CW.JW,CW.codeWeights]
      omega) J hJ ha hgood
  exact ⟨P,⟨by intro hz;exact hnot (by rw [hz];exact dvd_zero _),hb P hP,hc P hP⟩,hnot⟩
theorem CBA
    (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (a:DA.OwnerBox)
    (ha:DA.Covers a J)
    (hgood:(DA.Impossible (caps p) a∧0<Kdim)∨
      strongCount p a<Kdim):
    ∃P,Interpolant p nodes u0 u1 P∧ ¬J^a.q∣P:=by
  rcases hgood with h | h
  · exact BIV p hp Kdim hd nodes u0 u1 hN J hJ a ha (Or.inl h)
  · rcases min_lt_iff.mp h with h | h
    · exact BIV p hp Kdim hd nodes u0 u1 hN J hJ a ha (Or.inr h)
    · exact CWH p hp Kdim hd nodes u0 u1 hN J hJ a ha (Or.inr h)
theorem BHD [CharP K 2130706433]
    (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
    (nodes:N ↪ K) (u0 u1:N→K) (hN:Fintype.card N=262144)
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT:p.L<wt RCN156.residualTotalWeights F)
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (r y t:ℕ) (hr:1≤r) (hy:1≤y) (ht:1≤t)
    (hF:wt RCN156.residualSWeights F≤r∧wt RCN156.residualYSWeights F≤y∧wt RCN156.residualTotalWeights F≤t)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J)
    (Jcap:ℕ) (hTJ:total J≤Jcap) (hJFT:Jcap<wt RCN156.residualTotalWeights F)
    (m:ℕ) (hm:0<m)
    (hmul:((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=m)
    (hJne:(SecondJetCoefficients.asS J).map (carrierMap F)≠0)
    (a:DA.OwnerBox) (hq:a.q=(p.k+1+m-1)/m)
    (ha:DA.Covers a J)
    (hgood:(DA.Impossible (caps p) a∧0<Kdim)∨
      strongCount p a<Kdim):
    (∃Q,ProperHelper p F Q r y t nodes u0 u1)∨
      ∃e<a.q,∃SJ SQ:MovingFiberThreeSources6811.Source F,SJ.P=J∧IsRelPrime SJ.P SQ.P∧
        0<min m (p.k+1-e*m)∧min m (p.k+1-e*m)≤SJ.d∧p.k+1-e*m≤SQ.d∧
        e*total J+total SQ.P≤p.L∧e*middle J+middle SQ.P≤p.U∧
        e*slope J+slope SQ.P≤p.B∧e*order J+order SQ.P≤p.s:=by
  obtain ⟨P,hP,hnot⟩:=CBA p hp Kdim hd nodes u0 u1 hN J hJ.ne_zero a ha hgood
  rcases EMH p hp nodes u0 u1 P hP F Fact.out hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  have hpow:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^(p.k+1)∣(SecondJetCoefficients.asS P).map (carrierMap F):=by
    by_cases hz:(SecondJetCoefficients.asS P).map (carrierMap F)=0
    · rw [hz];exact dvd_zero _
    have hk:p.k<2130706433:=lt_of_lt_of_le (by have:=hp.retention;omega) (hp.degree.trans hp.characteristic.le)
    exact SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F (carrierMap F) p.s p.k
      (fun e he=>(hP.2.1 e he).2.1) (DQY F) (ALO F hpos hchar) hz
      (SecondJetOwnShape.factorial_ne p.k hk) hret.2
  have hnot' : ¬J^((p.k+1+m-1)/m)∣P:=by rwa [←hq]
  obtain ⟨e,he,Q,hEq,hQ,hcop,hdelta,hpowQ⟩:=DHM.FCK
    (LK.QC (carrierMap F)) (SecondJetCarrierDichotomy.ratio (carrierMap F) F)
    J P hJ (p.k+1) m hm hnot' hJne hmul hpow
  have hb:=CTV p hp P hP.2.1
  obtain ⟨_,hT,hB,hS,hU⟩:=hb
  rw [hEq,weight_mul _ _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow _ _ hJ.ne_zero] at hT hB hU
  rw [hEq,degreeOf_mul_eq (pow_ne_zero _ hJ.ne_zero) hQ,degreeOf_pow_eq _ _ _ hJ.ne_zero] at hS
  have hpowJ:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^m∣(SecondJetCoefficients.asS J).map (carrierMap F):=by
    rw [←hmul];exact Polynomial.pow_rootMultiplicity_dvd _ _
  obtain ⟨SJ,hSJ,hSd⟩:=ZD.UN
    F Jcap hJFT hpos hchar J hJ.ne_zero hTJ m hm hpowJ
  obtain ⟨SQ,hSQ,hQd⟩:=ZD.UN
    F p.L hFT hpos hchar Q hQ
    (by change weightedTotalDegree Koala6831Ordinary.totalWeights Q≤p.L;dsimp [caps] at hT;omega)
    (p.k+1-e*m) (lt_of_lt_of_le hdelta (min_le_right _ _)) hpowQ
  refine Or.inr ⟨e,by simpa only [hq] using he,SJ,SQ,hSJ,?_,hdelta,
    (min_le_left _ _).trans hSd,hQd,?_,?_,?_,?_⟩
  · rwa [hSJ,hSQ]
  · simpa only [hSQ,caps,total] using hT
  · simpa only [hSQ,caps,middle] using hU
  · simpa only [hSQ,caps,CB.slope] using hB
  · simpa only [hSQ,caps,order] using hS
end
end ZGL
end MergedPart2
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace LL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetCoefficients (liftExponent)
open LK CB
open DC BD
open MovingFiberThreeSources6811 (direction weight)
open RCN234 RCN156
variable {K:Type} [Field K] [CharP K 2130706433]
theorem derivative_ne_zero (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0)
    (hn:0<(SecondJetCoefficients.asS J).natDegree) (hsmall:(SecondJetCoefficients.asS J).natDegree<2130706433):
    (SecondJetCoefficients.asS J).derivative≠0:=by
  have hA:SecondJetCoefficients.asS J≠0:=by simpa using hJ
  have hcast:(((SecondJetCoefficients.asS J).natDegree:ℕ):MvPolynomial (Fin 4) K)≠0:=by
    intro hz
    have hd:=(CharP.cast_eq_zero_iff (MvPolynomial (Fin 4) K) 2130706433 _).mp hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hn hd)
  have hcoeff:(SecondJetCoefficients.asS J).coeff (SecondJetCoefficients.asS J).natDegree≠0:=by
    simpa only [Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hA)
  have hc:=mul_ne_zero hcoeff hcast
  intro hz
  have he:=congrArg (fun P:Polynomial (MvPolynomial (Fin 4) K)=>
    P.coeff ((SecondJetCoefficients.asS J).natDegree-1)) hz
  have heq:(SecondJetCoefficients.asS J).natDegree-1+1=(SecondJetCoefficients.asS J).natDegree:=by omega
  have heqCast:(((SecondJetCoefficients.asS J).natDegree-1:ℕ):MvPolynomial (Fin 4) K)+1=
      ((SecondJetCoefficients.asS J).natDegree:MvPolynomial (Fin 4) K):=by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n:ℕ=>(n:MvPolynomial (Fin 4) K)) heq
  rw [Polynomial.coeff_derivative,Polynomial.coeff_zero,heq,heqCast] at he
  exact hc he
theorem EWR (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J)
    (hn:0<(SecondJetCoefficients.asS J).natDegree) (hsmall:(SecondJetCoefficients.asS J).natDegree<2130706433):
    pderiv 1 J≠0∧IsRelPrime J (pderiv 1 J):=by
  have hd:=derivative_ne_zero J hJ.ne_zero hn hsmall
  have hne:pderiv 1 J≠0:=by
    intro hz
    apply hd
    rw [← SecondJetCoefficientSpecialization.asS_pderiv,hz,map_zero]
  refine ⟨hne,hJ.isRelPrime_iff_not_dvd.mpr ?_⟩
  intro hdiv
  have hm:SecondJetCoefficients.asS J∣SecondJetCoefficients.asS (pderiv 1 J):=map_dvd (SecondJetCoefficients.asS (K:=K)).toRingHom hdiv
  rw [SecondJetCoefficientSpecialization.asS_pderiv] at hm
  have hle:=Polynomial.natDegree_le_of_dvd hm hd
  have hlt:=Polynomial.natDegree_derivative_lt (by omega:(SecondJetCoefficients.asS J).natDegree≠0)
  omega
omit [CharP K 2130706433] in
theorem AWV (J:SecondJetSupport.Poly (K:=K)) (weights:Fin 5→ℕ):
    weightedTotalDegree weights (pderiv 1 J)≤weightedTotalDegree weights J-weights 1:=by
  apply Finset.sup_le
  intro d hd
  have hs:d+Finsupp.single 1 1∈J.support:=by
    simpa using SecondJetGlobalDifferentiation.support_iterate J 1 d (by simpa using hd)
  have hh:=MvPolynomial.le_weightedTotalDegree weights hs
  simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
  omega
omit [CharP K 2130706433] in
theorem pderiv_order (J:SecondJetSupport.Poly (K:=K)):(pderiv 1 J).degreeOf 1≤J.degreeOf 1-1:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs:d+Finsupp.single 1 1∈J.support:=by
    simpa using SecondJetGlobalDifferentiation.support_iterate J 1 d (by simpa using hd)
  have hh:=MvPolynomial.monomial_le_degreeOf 1 hs
  simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
  omega
omit [CharP K 2130706433] in
theorem FAJ {E:Type} [Field E]
    (phi:MvPolynomial (Fin 4) K→+*E) (z:E) (J:SecondJetSupport.Poly (K:=K)) (m:ℕ)
    (hm:((SecondJetCoefficients.asS J).map phi).rootMultiplicity z=m):
    (Polynomial.X-Polynomial.C z)^(m-1)∣(SecondJetCoefficients.asS (pderiv 1 J)).map phi:=by
  have hp:=Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd
    (Polynomial.pow_rootMultiplicity_dvd ((SecondJetCoefficients.asS J).map phi) z)
  rw [hm] at hp
  simpa only [SecondJetCoefficientSpecialization.asS_pderiv,Polynomial.derivative_map] using hp
theorem AWG
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT:1700<wt RCN156.residualTotalWeights F)
    (hpos:0<F.degreeOf 2) (hFsmall:F.degreeOf 2<2130706433)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (hT:total J≤1700)
    (hn:0<(SecondJetCoefficients.asS J).natDegree) (hsmall:(SecondJetCoefficients.asS J).natDegree<2130706433)
    (m:ℕ) (hm:2≤m)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=m):
    ∃A B:MovingFiberThreeSources6811.Source F,A.P=J∧B.P=pderiv 1 J∧IsRelPrime A.P B.P∧
      m≤A.d∧m-1≤B.d∧
      (∀weights:Fin 5→ℕ,
        weightedTotalDegree weights B.P≤weightedTotalDegree weights J-weights 1):=by
  obtain ⟨hne,hcop⟩:=EWR J hJ hn hsmall
  have hTQ:total (pderiv 1 J)≤1700:=
    (AWV J Koala6831Ordinary.totalWeights).trans ((Nat.sub_le _ _).trans hT)
  have hpowJ:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^m∣(SecondJetCoefficients.asS J).map (carrierMap F):=by
    rw [← hroot]
    exact Polynomial.pow_rootMultiplicity_dvd _ _
  obtain ⟨A,hAJ,hAm⟩:=AYB.DTC
    F hFT hpos hFsmall J hJ.ne_zero hT m (by omega) hpowJ
  obtain ⟨B,hBQ,hBm⟩:=AYB.DTC
    F hFT hpos hFsmall (pderiv 1 J) hne hTQ (m-1) (by omega)
    (FAJ (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J m hroot)
  refine ⟨A,B,hAJ,hBQ,?_,hAm,hBm,?_⟩
  · simpa only [hAJ,hBQ] using hcop
  · intro weights
    simpa only [hBQ] using AWV J weights
end
end LL
end MergedPart0
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace ER
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open DU BD GZ
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
open SecondJetHelperWeights renaming cleared_weight → BUF
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
def pair (t y r b u l:ℕ):DG:=⟨262144,131071,181059,y,r,t,u,b,l⟩
def Gates (t y r b u l:ℕ):Prop:=
  (pair t y r b u l).mixedCost.y<2130706433∧
  (pair t y r b u l).mixedCost.r<2130706433∧
  (pair t y r b u l).mixedCost.z<2130706433
theorem DHG (P:Packet x t y r) (Q:MvPolynomial (Fin 4) K)
    (b u l:ℕ) (hrel:IsRelPrime P.F Q)
    (hweights:wt RCN156.residualSWeights Q≤b∧wt RCN156.residualYSWeights Q≤u∧wt RCN156.residualTotalWeights Q≤l)
    (hgates:Gates t y r b u l)
    (hzero: ∀gamma∈P.seeds,RCN319.specialization K (P.selected gamma) gamma Q=0):
    P.seeds.card≤GB.FU (pair t y r b u l):=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hyhi:=P.yhigh
  have hthi:=P.thigh
  have hQ:=ZM.ATW Q b u l hweights
  have hc:=BCH.BUM (pair t y r b u l) P.F Q
    P.irreducible P.rdegree hrel 2130706433 P.IZ.1 P.IZ.2.1 P.IZ.2.2
    hQ.1 hQ.2.1 hQ.2.2 (by dsimp [pair];omega) (by dsimp [pair];omega)
    (by dsimp [pair];omega) (by dsimp [pair];omega) hgates.1 hgates.2.1 hgates.2.2
    P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.nodeCount
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    P.degree P.agreement
    (by simpa only [pair,DG.errors,Nat.reduceSub,RCN326.w] using P.noPencil)
    P.solution P.regular hzero
  exact ZM.DUQ (pair t y r b u l) P.F P.IZ.1
    P.IZ.2.1 P.IZ.2.2 P.seeds.card (by norm_num [pair,DG.gap]) hc
theorem EVD (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F):
    wt RCN156.residualSWeights (SecondJetCoefficients.asS S.P).leadingCoeff≤S.B-2*S.n0∧
    wt RCN156.residualYSWeights (SecondJetCoefficients.asS S.P).leadingCoeff≤S.U-S.n0∧
    wt RCN156.residualTotalWeights (SecondJetCoefficients.asS S.P).leadingCoeff≤S.T-S.n0:=by
  have hn:=S.hn
  have hw:=SecondJetHelperWeights.derivative_coefficient_weights S.P S.B S.U S.T 0 (SecondJetCoefficients.asS S.P).natDegree S.hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  rw [Polynomial.leadingCoeff]
  omega
def leadingPrice {F:MvPolynomial (Fin 4) K} (S:MovingFiberThreeSources6811.Source F) (t y r:ℕ):ℕ:=
  GB.FU (pair t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0))
theorem DOU (P:Packet x t y r) (S:MovingFiberThreeSources6811.Source P.F)
    (hFT:S.T<wt RCN156.residualTotalWeights P.F)
    (hgates:Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)):
    (P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma)
      (S.leading (RCN135.polynomialEmbedding K))=0)).card≤leadingPrice S t y r:=by
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma)
    (S.leading (RCN135.polynomialEmbedding K))=0)
  let PB:=P.restrict bad (Finset.filter_subset _ _)
  have hnot:=SecondJetTotalAvoidance.leading_not_dvd S.P (AHY P.F S) P.F S.T
    (fun e he=>(S.hshape e he).2.2) hFT
  have hzero: ∀gamma∈bad,RCN319.specialization K (P.selected gamma) gamma (SecondJetCoefficients.asS S.P).leadingCoeff=0:=by
    intro gamma hg
    have hh:=(Finset.mem_filter.mp hg).2
    change MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma)
      (surfaceMap (RCN135.polynomialEmbedding K) (SecondJetCoefficients.asS S.P).leadingCoeff)=0 at hh
    rw [RCN170.XH] at hh
    exact RCN135.polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  exact DHG PB (SecondJetCoefficients.asS S.P).leadingCoeff (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)
    (P.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2) (EVD P.F S) hgates hzero
end
end ER
end MergedPart0
section MergedPart1
namespace BOE
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334 RCN338 RCN341
open RCN222 renaming GeometricFactor → EX
open RCN206 RCN209 RCN340 RCN344
open FA PR
open CommonLinearChannels6807 (linearA linearU linearZ)
open BD HK HFreeDir6813
open MovingFiberThreeSources6811 (direction weight)
open DU BLL AYR
open BIO BBT _Q7
open AFA RL TW
open GZ CB
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
local notation "Ω" =>GenericField K
local notation "Ext" =>AlgebraicClosure (RatFunc Ω)
abbrev Curve (P:Packet x t y r):=(g:RCN222.GeometricFactor K P.F) × CM (P.stage g)
def active (P:Packet x t y r) (SZ:MovingFiberThreeSources6811.Source P.F):Finset (Curve P):=
  Finset.univ.filter (fun a=>SZ.leading (RCN135.polynomialEmbedding K)∉a.2.1)
def multiplicity (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1)) (a:Curve P):ℕ:=
  FO (MU (P.stage a.1))
    (DN (MU (P.stage a.1)) (P.stage_proper hp a.1)) a.2
def ordinary (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1))
    (geometry: ∀g,ABN (P.stage g)) (a:Curve P) (W:FlagDegree):ℕ:=
  (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).weightedCost W a.2
end
end BOE
end MergedPart1
section MergedPart2
namespace EF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159 RCN174 RCN198
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334
open RCN222 renaming GeometricFactor → EX
open RCN087 RCN199 RCN206 RCN207 RCN271 RCN287 RCN312 RCN330 RCN332 RCN336 RCN338 RCN339 RCN341
open FA DU
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
def MG (t y r:ℕ):ℕ:=
  131073*81086*IY ⟨t-y,y-r,r⟩ (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) w/49988
theorem CNE (P:Packet x t y r) (hidentity:P.F∣numerator K P.F (w+1)):
    P.seeds.card≤MG t y r:=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hylo:=P.ylow
  have hyhi:=P.yhigh
  have hyt:=P.yt
  have hthi:=P.thigh
  let cost:=fun g:RCN222.GeometricFactor K P.F=>
    IY (CO K g) (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) w
  have hsingle (g:RCN222.GeometricFactor K P.F):
      (KK K P.F P.selected P.seeds g).card*49988≤131073*81086*cost g:=by
    let S:=P.stage g
    have hflag:=P.stage_flag g
    have hflagChar:(CO K g).yz+(CO K g).all<2130706433∧
        (CO K g).all<2130706433∧
        (CO K g).zOnly+(CO K g).yz+(CO K g).all<2130706433:=by omega
    have hTailNumerator:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K S.F (w+1)):=
      S.RR.trans (map_dvd (surfaceMap (RCN135.polynomialEmbedding K)) hidentity)
    have hmixed:=BoundaryTailGates.identity_gate (CO K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hnodes:S.nodes.card=262144:=P.nodeCount
    have hprovider:=BRK.AAB S 181059
      hnodes (P.CVV g) (by decide) hTailNumerator P.D t r (by decide)
      P.Dlow P.Dchar P.box hflagChar hmixed
    have hpositive:1≤cost g:=by
      apply Lower80788.FixedStage.CVP
      have hh:=S.y_dependent
      have hd:=RCN084.degreeOf_le_flag_total S.G (CO K g) S.flag_support 1
      omega
    have hinc:=AQH S 181059 _ hprovider (P.CVV g)
      (by decide) (by rw [hnodes];decide) hpositive
    simpa only [cost,hnodes,RCN326.w,Nat.reduceSub,Nat.reduceAdd] using hinc
  have hb:=VD P.F P.irreducible.ne_zero
  have hc:=RCN130.originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hz:=RCN084.sum_flagMixed_le_of_cumulative (CO K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) (w+1)) unitZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp;omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp;omega))
  have hu:=RCN084.sum_flagMixed_le_of_cumulative (CO K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) (w+1)) unitYZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp;omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp;omega))
  have hcost:(∑ g,cost g)≤IY ⟨t-y,y-r,r⟩ (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) w:=by
    simpa only [cost,IY,Finset.sum_add_distrib] using Nat.add_le_add hz hu
  have hsum:=Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hsingle g)
  simp only [←Finset.sum_mul,←Finset.mul_sum] at hsum
  have hfinal:=(Nat.mul_le_mul_right 49988 P.seeds_cover).trans
    (hsum.trans (Nat.mul_le_mul_left (131073*81086) hcost))
  exact (Nat.le_div_iff_mul_le (by decide:0<49988)).mpr hfinal
end
end EF
end MergedPart2
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
variable {K I : Type} [Field K] {x : I → K} {t y r : ℕ}
theorem packet_r_le (P : DU.Packet x t y r) : r ≤ 16 := P.rhigh.trans (by norm_num)
theorem packet_y_le (P : DU.Packet x t y r) : y ≤ 128 := P.yhigh.trans (by norm_num)
theorem packet_t_le (P : DU.Packet x t y r) : t ≤ 7200 := P.thigh.trans (by norm_num)
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero RCN204 RCN095
open RCN095 renaming PolynomialInFlag → BI
variable {L : Type*} [Field L]
def lmono (x : Fin 3 → L) (a : Fin 3 → ℤ) : L := x 0 ^ a 0 * x 1 ^ a 1 * x 2 ^ a 2
def chartExp : Bool → Bool → Bool → Fin 3 → Fin 3 → ℤ
  | false, false, false => ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]
  | true, false, false => ![![0, -1, 0], ![1, 0, 0], ![0, 0, 1]]
  | false, true, false => ![![-1, 1, 0], ![-1, 0, 0], ![0, 0, 1]]
  | true, true, false => ![![1, -1, 0], ![-1, 0, 0], ![0, 0, 1]]
  | false, false, true => ![![0, 1, -1], ![1, 0, -1], ![0, 0, -1]]
  | true, false, true => ![![0, -1, 1], ![1, 0, -1], ![0, 0, -1]]
  | false, true, true => ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, -1]]
  | true, true, true => ![![1, -1, 0], ![-1, 0, 1], ![0, 0, -1]]
def vertexExp (sR sY sZ : Bool) (W : FlagDegree) : Fin 3 → ℤ :=
  ![if sY then (W.yz : ℤ) + W.all - (if sR then (W.all : ℤ) else 0) else 0,
    if sR then (W.all : ℤ) else 0,
    if sZ then (W.zOnly : ℤ) + W.yz + W.all -
      (if sY then (W.yz : ℤ) + W.all - (if sR then (W.all : ℤ) else 0) else 0) -
      (if sR then (W.all : ℤ) else 0) else 0]
theorem lmono_val (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (a : Fin 3 → ℤ) :
    v (lmono x a) =
      exp (a 0 * (v (x 0)).log + a 1 * (v (x 1)).log + a 2 * (v (x 2)).log) := by
  have h : ∀ j, v (x j) = exp (v (x j)).log := fun j =>
    (exp_log ((Valuation.ne_zero_iff v).2 (hx j))).symm
  have hz : ∀ (j : Fin 3) (n : ℤ), v (x j) ^ n = exp (n * (v (x j)).log) := by
    intro j n
    conv_lhs => rw [h j]
    rw [← exp_zsmul, smul_eq_mul]
  rw [lmono, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, hz, hz, hz, ← exp_add, ← exp_add]
theorem lmono_le_one_iff (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (a : Fin 3 → ℤ) :
    v (lmono x a) ≤ 1 ↔
      a 0 * (v (x 0)).log + a 1 * (v (x 1)).log + a 2 * (v (x 2)).log ≤ 0 := by
  rw [lmono_val v x hx, ← exp_zero, exp_le_exp]
theorem flagPole_eq_vertex (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0)
    (sR sY sZ : Bool) (h : ∀ i, v (lmono x (chartExp sR sY sZ i)) ≤ 1) (W : FlagDegree) :
    v (lmono x (vertexExp sR sY sZ W)) = exp (flagPole v x W) := by
  have h0 := (lmono_le_one_iff v x hx _).1 (h 0)
  have h1 := (lmono_le_one_iff v x hx _).1 (h 1)
  have h2 := (lmono_le_one_iff v x hx _).1 (h 2)
  rw [lmono_val v x hx, flagPole, RCN187.poleOrder, RCN187.poleOrder, RCN187.poleOrder]
  congr 1
  generalize (v (x 0)).log = l0 at *
  generalize (v (x 1)).log = l1 at *
  generalize (v (x 2)).log = l2 at *
  generalize hA : max 0 l2 = A
  generalize hB : max (max 0 l0) A = B
  generalize hC : max (max 0 l1) B = C
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    simp [chartExp] at h0 h1 h2
  · have e1 : A = 0 := by omega
    have e2 : B = 0 := by omega
    have e3 : C = 0 := by omega
    subst e1 e2 e3
    simp [vertexExp]
  · have e1 : A = l2 := by omega
    have e2 : B = l2 := by omega
    have e3 : C = l2 := by omega
    subst e1 e2 e3
    simp [vertexExp]; ring
  · have e1 : A = 0 := by omega
    have e2 : B = l0 := by omega
    have e3 : C = l0 := by omega
    subst e1 e2 e3
    simp [vertexExp]; ring
  · have e1 : A = l2 := by omega
    have e2 : B = l0 := by omega
    have e3 : C = l0 := by omega
    subst e1 e2 e3
    simp [vertexExp]; ring
  · have e1 : A = 0 := by omega
    have e2 : B = 0 := by omega
    have e3 : C = l1 := by omega
    subst e1 e2 e3
    simp [vertexExp]
  · have e1 : A = l2 := by omega
    have e2 : B = l2 := by omega
    have e3 : C = l1 := by omega
    subst e1 e2 e3
    simp [vertexExp]; ring
  · have e1 : A = 0 := by omega
    have e2 : B = l0 := by omega
    have e3 : C = l1 := by omega
    subst e1 e2 e3
    simp [vertexExp]
  · have e1 : A = l2 := by omega
    have e2 : B = l0 := by omega
    have e3 : C = l1 := by omega
    subst e1 e2 e3
    simp [vertexExp]; ring
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section FunctionField
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
theorem sum_order_eq_zero (x : L) (hx : x ≠ 0) (T : Finset (RCN026.Place_p19 K L))
    (hT : RCN026.placesFor_p19 K L x hx ⊆ T) : ∑ v ∈ T, RCN026.order_p19 K L v x = 0 := by
  rw [← Finset.sum_subset hT fun v _ hv => by_contra fun h => hv (RCN026.ALB K L x hx v h)]
  exact RCN026.DAL K L x hx
end FunctionField
variable {K : Type} [Field K]
def PlaceOver (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] (v : Fin 3 → K)
    (mu : RCN026.Place_p19 K (RCN002.CoordinateField K P)) : Prop :=
  ∀ g : MvPolynomial (Fin 3) K, MvPolynomial.aeval v g = 0 → mu.val (RCN002.coordinateEvaluation K P g) < 1
section Over
variable {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime] {v : Fin 3 → K}
  {mu : RCN026.Place_p19 K (RCN002.CoordinateField K P)}
theorem PlaceOver.eq_one (h : PlaceOver P v mu) (g : MvPolynomial (Fin 3) K)
    (hg : MvPolynomial.aeval v g ≠ 0) : mu.val (RCN002.coordinateEvaluation K P g) = 1 := by
  have h1 : mu.val (RCN002.coordinateEvaluation K P (g - MvPolynomial.C (MvPolynomial.aeval v g))) < 1 := h _ (by simp)
  have h2 : mu.val (RCN002.coordinateEvaluation K P (MvPolynomial.C (MvPolynomial.aeval v g))) = 1 := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact mu.property.2.eq_one _ hg
  have h3 := mu.val.map_add_eq_of_lt_right (lt_of_lt_of_eq h1 h2.symm)
  rwa [← map_add, sub_add_cancel, h2] at h3
theorem PlaceOver.le_one (h : PlaceOver P v mu) (g : MvPolynomial (Fin 3) K) :
    mu.val (RCN002.coordinateEvaluation K P g) ≤ 1 := by
  by_cases hg : MvPolynomial.aeval v g = 0
  · exact (h g hg).le
  · exact (h.eq_one g hg).le
theorem PlaceOver.point_eq {v' : Fin 3 → K} (h : PlaceOver P v mu) (h' : PlaceOver P v' mu) :
    v = v' := by
  funext i
  by_contra hne
  have h1 : mu.val (RCN002.coordinateEvaluation K P (MvPolynomial.X i - MvPolynomial.C (v i))) < 1 := h _ (by simp)
  have h2 : mu.val (RCN002.coordinateEvaluation K P (MvPolynomial.X i - MvPolynomial.C (v i))) = 1 :=
    h'.eq_one _ (by simpa [sub_eq_zero] using Ne.symm hne)
  exact h1.ne h2
end Over
variable [IsAlgClosed K]
theorem exists_placeOver {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime] (base : RCN341.SeparableLiteralCoordinate P)
    {v : Fin 3 → K} (hv : P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
    ∃ mu : RCN026.Place_p19 K (RCN002.CoordinateField K P), PlaceOver P v mu := by
  let i₀ := base.index
  let hi₀ := base.transcendental
  let _a1 : Algebra (Polynomial K) (RCN002.CoordinateRing K P) := RCN006.quotientPolynomialAlgebra K P i₀
  let _a2 : Algebra (Polynomial K) (RCN002.CoordinateField K P) := RCN006.polynomialBaseAlgebra K P i₀
  let _a3 : Algebra (RatFunc K) (RCN002.CoordinateField K P) := RCN005.rationalBaseAlgebra K P i₀ hi₀
  have _t1 := RCN006.quotientBaseScalarTower K P i₀
  have _t2 := RCN006.polynomialBaseScalarTower K P i₀
  have _t3 := RCN006.quotientFractionScalarTower K P i₀
  have _t4 := RCN006.polynomialRationalScalarTower K P i₀ hi₀
  have _t5 := RCN005.rationalBaseScalarTower K P i₀ hi₀
  have _t6 : FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P) := base.finite
  have _t7 : Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P) := base.separable
  exact ⟨RCN344.modelPlace_p19 K (RCN002.CoordinateField K P) (RCN002.CoordinateRing K P) (RCN007.pointHom K P ⟨v, hv⟩), fun g hg =>
    (RCN000.actual_model_value_lt_one_iff K (RCN002.CoordinateRing K P) (RCN002.CoordinateField K P) _ (Ideal.Quotient.mk P g)).2 hg⟩
theorem Curve.finite_order_ne_zero (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (base : RCN341.SeparableLiteralCoordinate P) (x : RCN002.CoordinateField K P) (hx : x ≠ 0) :
    {mu : RCN026.Place_p19 K (RCN002.CoordinateField K P) | RCN026.order_p19 K (RCN002.CoordinateField K P) mu x ≠ 0}.Finite := by
  let i₀ := base.index
  let hi₀ := base.transcendental
  let _a1 : Algebra (Polynomial K) (RCN002.CoordinateRing K P) := RCN006.quotientPolynomialAlgebra K P i₀
  let _a2 : Algebra (Polynomial K) (RCN002.CoordinateField K P) := RCN006.polynomialBaseAlgebra K P i₀
  let _a3 : Algebra (RatFunc K) (RCN002.CoordinateField K P) := RCN005.rationalBaseAlgebra K P i₀ hi₀
  have _t1 := RCN006.quotientBaseScalarTower K P i₀
  have _t2 := RCN006.polynomialBaseScalarTower K P i₀
  have _t3 := RCN006.quotientFractionScalarTower K P i₀
  have _t4 := RCN006.polynomialRationalScalarTower K P i₀ hi₀
  have _t5 := RCN005.rationalBaseScalarTower K P i₀ hi₀
  have _t6 : FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P) := base.finite
  have _t7 : Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P) := base.separable
  exact (RCN026.placesFor_p19 K (RCN002.CoordinateField K P) x hx).finite_toSet.subset fun mu hmu =>
    RCN026.ALB K (RCN002.CoordinateField K P) x hx mu hmu
theorem Curve.places_count_of_bound (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (base : RCN341.SeparableLiteralCoordinate P) {H G : MvPolynomial (Fin 3) K} (budget : RCN199.RD P H G) (psi : RCN002.CoordinateField K P)
    (hpsi : psi ≠ 0)
    (W : FlagDegree) (k e : RCN026.Place_p19 K (RCN002.CoordinateField K P) → ℕ) (U : Finset (RCN026.Place_p19 K (RCN002.CoordinateField K P)))
    (B : ℕ) (hB : ∀ T : Finset (RCN026.Place_p19 K (RCN002.CoordinateField K P)), ∑ mu ∈ T, e mu ≤ B)
    (h : ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K P),
      (k mu : ℤ) - flagPole mu.val (coordinate K P) W - e mu ≤ RCN026.order_p19 K (RCN002.CoordinateField K P) mu psi) :
    ∑ mu ∈ U, k mu ≤ budget.weightedCost W + B := by
  classical
  let i₀ := base.index
  let hi₀ := base.transcendental
  let _a1 : Algebra (Polynomial K) (RCN002.CoordinateRing K P) := RCN006.quotientPolynomialAlgebra K P i₀
  let _a2 : Algebra (Polynomial K) (RCN002.CoordinateField K P) := RCN006.polynomialBaseAlgebra K P i₀
  let _a3 : Algebra (RatFunc K) (RCN002.CoordinateField K P) := RCN005.rationalBaseAlgebra K P i₀ hi₀
  have _t1 := RCN006.quotientBaseScalarTower K P i₀
  have _t2 := RCN006.polynomialBaseScalarTower K P i₀
  have _t3 := RCN006.quotientFractionScalarTower K P i₀
  have _t4 := RCN006.polynomialRationalScalarTower K P i₀ hi₀
  have _t5 := RCN005.rationalBaseScalarTower K P i₀ hi₀
  have _t6 : FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P) := base.finite
  have _t7 : Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P) := base.separable
  obtain ⟨T, hT, hUT⟩ : ∃ T : Finset (RCN026.Place_p19 K (RCN002.CoordinateField K P)),
      RCN026.placesFor_p19 K (RCN002.CoordinateField K P) psi hpsi ⊆ T ∧ U ⊆ T :=
    ⟨_, Finset.subset_union_left, Finset.subset_union_right⟩
  have h1 : ∑ mu ∈ T, ((k mu : ℤ) - flagPole mu.val (coordinate K P) W - e mu) ≤
      ∑ mu ∈ T, RCN026.order_p19 K (RCN002.CoordinateField K P) mu psi := Finset.sum_le_sum fun mu _ => h mu
  rw [sum_order_eq_zero K (RCN002.CoordinateField K P) psi hpsi T hT, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  have h2 := budget.CUE W T
  have hk : (∑ mu ∈ U, (k mu : ℤ)) ≤ ∑ mu ∈ T, (k mu : ℤ) := by
    exact_mod_cast Finset.sum_le_sum_of_subset (f := k) hUT
  have he' : (∑ mu ∈ T, (e mu : ℤ)) ≤ (B : ℤ) := by
    exact_mod_cast hB T
  have hb : ((∑ mu ∈ U, k mu : ℕ) : ℤ) ≤ ((budget.weightedCost W + B : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hb
theorem Curve.zeros_mul_card_le_of_bound (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (base : RCN341.SeparableLiteralCoordinate P) {H G : MvPolynomial (Fin 3) K} (budget : RCN199.RD P H G) (psi : RCN002.CoordinateField K P)
    (hpsi : psi ≠ 0) (k : ℕ) (points : Finset (Fin 3 → K))
    (hP : ∀ v ∈ points, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hzero : ∀ v ∈ points, ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K P), PlaceOver P v mu →
      (k : ℤ) ≤ RCN026.order_p19 K (RCN002.CoordinateField K P) mu psi)
    (W : FlagDegree) (e : RCN026.Place_p19 K (RCN002.CoordinateField K P) → ℕ) (B : ℕ)
    (hB : ∀ T : Finset (RCN026.Place_p19 K (RCN002.CoordinateField K P)), ∑ mu ∈ T, e mu ≤ B)
    (hpole : ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K P),
      -flagPole mu.val (coordinate K P) W - e mu ≤ RCN026.order_p19 K (RCN002.CoordinateField K P) mu psi) :
    k * points.card ≤ budget.weightedCost W + B := by
  classical
  choose place hplace using fun pt : {v : Fin 3 → K // v ∈ points} => exists_placeOver base (hP pt.1 pt.2)
  have hinj : Function.Injective place := fun pt pt' hpt =>
    Subtype.ext ((hplace pt).point_eq (by rw [hpt]; exact hplace pt'))
  have hmain : ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K P),
      ((if mu ∈ points.attach.image place then k else 0 : ℕ) : ℤ) -
        flagPole mu.val (coordinate K P) W - e mu ≤ RCN026.order_p19 K (RCN002.CoordinateField K P) mu psi := by
    intro mu
    by_cases hmu : mu ∈ points.attach.image place
    · simp only [hmu, ↓reduceIte]
      obtain ⟨pt, -, rfl⟩ := Finset.mem_image.mp hmu
      have h1 := hzero pt.1 pt.2 _ (hplace pt)
      have h2 := RCN204.flagPole_nonneg (place pt).val (coordinate K P) W
      omega
    · simp only [hmu, ↓reduceIte, Nat.cast_zero, zero_sub]
      exact hpole mu
  have h := Curve.places_count_of_bound P base budget psi hpsi W _ e (points.attach.image place) B hB
    hmain
  rw [Finset.sum_congr rfl fun mu hmu => (by simp only [hmu, ↓reduceIte] :
      (if mu ∈ points.attach.image place then k else 0) = k),
    Finset.sum_const, smul_eq_mul, Finset.card_image_of_injective _ hinj, Finset.card_attach,
    mul_comm] at h
  exact h
theorem Curve.curve_count_of_bound (G T H : MvPolynomial (Fin 3) K) (C : RCN264.RegularComponent K G T H)
    (base : RCN341.SeparableLiteralCoordinate C.1) {Hb Gb : MvPolynomial (Fin 3) K} (budget : RCN199.RD C.1 Hb Gb)
    {Seed : Type*} (seeds : Finset Seed) (point : Seed → Fin 3 → K)
    (hinj : Function.Injective point) (psi : RCN002.CoordinateField K C.1) (hpsi : psi ≠ 0) (k : ℕ)
    (hzero : ∀ γ ∈ RCN264.componentSeeds K G T H seeds point C, ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K C.1),
      PlaceOver C.1 (point γ) mu → (k : ℤ) ≤ RCN026.order_p19 K (RCN002.CoordinateField K C.1) mu psi)
    (W : FlagDegree) (e : RCN026.Place_p19 K (RCN002.CoordinateField K C.1) → ℕ) (B : ℕ)
    (hB : ∀ T : Finset (RCN026.Place_p19 K (RCN002.CoordinateField K C.1)), ∑ mu ∈ T, e mu ≤ B)
    (hpole : ∀ mu : RCN026.Place_p19 K (RCN002.CoordinateField K C.1),
      -flagPole mu.val (coordinate K C.1) W - e mu ≤ RCN026.order_p19 K (RCN002.CoordinateField K C.1) mu psi) :
    k * (RCN264.componentSeeds K G T H seeds point C).card ≤ budget.weightedCost W + B := by
  classical
  have h := Curve.zeros_mul_card_le_of_bound C.1 base budget psi hpsi k
    ((RCN264.componentSeeds K G T H seeds point C).image point)
    (fun v hv => by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
      exact RCN264.componentSeeds_on_prime K G T H seeds point C γ hγ)
    (fun v hv mu hmu => by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
      exact hzero γ hγ mu hmu)
    W e B hB hpole
  rwa [Finset.card_image_of_injective _ hinj] at h
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
theorem linearIndependent_of_values_injective (w : Valuation L ℤᵐ⁰)
    (hk : ∀ a : k, a ≠ 0 → w (algebraMap k L a) = 1) {ι : Type*} (f : ι → L)
    (hf0 : ∀ i, f i ≠ 0) (hinj : Function.Injective fun i => w (f i)) : LinearIndependent k f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  set t := s.filter (fun j => c j ≠ 0) with ht
  have hit : i ∈ t := Finset.mem_filter.2 ⟨hi, hci⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image t (fun j => w (f j)) ⟨i, hit⟩
  have hc₀ : c i₀ ≠ 0 := (Finset.mem_filter.1 hi₀).2
  have hval : ∀ j, c j ≠ 0 → w (c j • f j) = w (f j) := by
    intro j hj
    rw [Algebra.smul_def, map_mul, hk _ hj, one_mul]
  have hsum' : ∑ j ∈ t, c j • f j = 0 := by
    rw [← hsum, ht, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : c j = 0 <;> simp [h]
  have hsplit : c i₀ • f i₀ = -∑ j ∈ t.erase i₀, c j • f j := by
    rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase t (fun j => c j • f j) hi₀]
    exact hsum'
  have hlt : w (∑ j ∈ t.erase i₀, c j • f j) < w (f i₀) := by
    apply Valuation.map_sum_lt w ((Valuation.ne_zero_iff w).2 (hf0 i₀))
    intro j hj
    have hjt := Finset.mem_of_mem_erase hj
    rw [hval j (Finset.mem_filter.1 hjt).2]
    exact lt_of_le_of_ne (hmax j hjt) fun h => Finset.ne_of_mem_erase hj (hinj h)
  have h := congrArg w hsplit
  rw [hval i₀ hc₀, Valuation.map_neg] at h
  exact (ne_of_gt hlt) h
theorem ord_le_of_filtration (w : Valuation L ℤᵐ⁰)
    (hk : ∀ a : k, a ≠ 0 → w (algebraMap k L a) = 1) (V : ℕ → Submodule k L)
    (hmul : ∀ d d' x y, x ∈ V d → y ∈ V d' → x * y ∈ V (d + d')) (hone : (1 : L) ∈ V 0)
    (hmono : ∀ d d', d ≤ d' → V d ≤ V d') (n : ℕ) (hfin : ∀ d, Module.Finite k (V d))
    (hdim : ∀ d, Module.finrank k (V d) ≤ n * (d + 1))
    (m : ℕ) (h : L) (hh : h ∈ V m) (c : ℕ) (p₁ p₂ : L) (hp₁ : p₁ ∈ V c) (hp₂ : p₂ ∈ V c)
    (hp₂0 : p₂ ≠ 0) (hπ : w p₁ = exp (-1) * w p₂) (e : ℕ) (he : w h = exp (-(e : ℤ))) :
    e ≤ n * m := by
  classical
  have hpow : ∀ d x, x ∈ V d → ∀ j : ℕ, x ^ j ∈ V (d * j) := by
    intro d x hx j
    induction j with
    | zero => simpa using hone
    | succ j ih => rw [pow_succ, Nat.mul_succ]; exact hmul _ _ _ _ ih hx
  by_contra hlt
  rw [not_le] at hlt
  have he0 : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hlt
  set A := n * (c * (e - 1) + 1) with hA
  set d := m * A + c * (e - 1) with hd
  let f : Fin (A + 1) × Fin e → L := fun p =>
    h ^ (p.1 : ℕ) * (p₁ ^ (p.2 : ℕ) * p₂ ^ (e - 1 - (p.2 : ℕ)))
  have hfV : ∀ p, f p ∈ V d := by
    intro p
    have h1 : h ^ (p.1 : ℕ) ∈ V (m * A) :=
      hmono _ _ (Nat.mul_le_mul_left m (Nat.lt_succ_iff.1 p.1.2)) (hpow m h hh p.1)
    have h2 : p₁ ^ (p.2 : ℕ) * p₂ ^ (e - 1 - (p.2 : ℕ)) ∈ V (c * (e - 1)) := by
      have h3 := hmul _ _ _ _ (hpow c p₁ hp₁ p.2) (hpow c p₂ hp₂ (e - 1 - p.2))
      have hb : (p.2 : ℕ) + (e - 1 - (p.2 : ℕ)) = e - 1 := by have := p.2.2; omega
      rwa [← Nat.mul_add, hb] at h3
    exact hmul _ _ _ _ h1 h2
  have hw2 : w p₂ ≠ 0 := (Valuation.ne_zero_iff w).2 hp₂0
  have hval : ∀ p : Fin (A + 1) × Fin e,
      w (f p) = exp (-((e * (p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℤ)) * w p₂ ^ (e - 1) := by
    intro p
    have hb : (p.2 : ℕ) + (e - 1 - (p.2 : ℕ)) = e - 1 := by have := p.2.2; omega
    calc w (f p) = exp (-(e : ℤ)) ^ (p.1 : ℕ) *
          ((exp (-1) * w p₂) ^ (p.2 : ℕ) * w p₂ ^ (e - 1 - (p.2 : ℕ))) := by
          simp only [f, map_mul, map_pow, he, hπ]
      _ = (exp (-(e : ℤ)) ^ (p.1 : ℕ) * exp (-1) ^ (p.2 : ℕ)) *
          (w p₂ ^ (p.2 : ℕ) * w p₂ ^ (e - 1 - (p.2 : ℕ))) := by
          simp only [mul_pow, mul_assoc]
      _ = exp (-((e * (p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℤ)) * w p₂ ^ (e - 1) := by
          rw [← pow_add, hb, ← exp_nsmul, ← exp_nsmul, ← exp_add]
          congr 2
          simp only [nsmul_eq_mul]
          push_cast
          ring
  have hC : w p₂ ^ (e - 1) ≠ 0 := pow_ne_zero _ hw2
  have hf0 : ∀ p, f p ≠ 0 := by
    intro p
    refine (Valuation.ne_zero_iff w).1 ?_
    rw [hval p]
    exact mul_ne_zero exp_ne_zero hC
  have hinj : Function.Injective fun p => w (f p) := by
    intro p q hpq
    simp only [hval] at hpq
    have h1 := exp_injective (mul_right_cancel₀ hC hpq)
    have h2 : e * (p.1 : ℕ) + (p.2 : ℕ) = e * (q.1 : ℕ) + (q.2 : ℕ) := by exact_mod_cast neg_injective h1
    have hp2 := p.2.2
    have hq2 := q.2.2
    have ha : (p.1 : ℕ) = q.1 := by
      have h3 := congrArg (· / e) h2
      simp only [Nat.mul_add_div he0, Nat.div_eq_of_lt hp2, Nat.div_eq_of_lt hq2, add_zero] at h3
      exact h3
    have hb : (p.2 : ℕ) = q.2 := by
      rw [ha] at h2
      exact Nat.add_left_cancel h2
    exact Prod.ext (Fin.ext ha) (Fin.ext hb)
  have hli := linearIndependent_of_values_injective w hk f hf0 hinj
  let g : Fin (A + 1) × Fin e → V d := fun p => ⟨f p, hfV p⟩
  have hlig : LinearIndependent k g := LinearIndependent.of_comp (V d).subtype hli
  have := hfin d
  have hcard := hlig.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have h1 : (A + 1) * e ≤ n * (m * A + c * (e - 1) + 1) := hcard.trans (hdim d)
  have h2 : (A + 1) * (n * m + 1) ≤ (A + 1) * e := Nat.mul_le_mul_left _ hlt
  have h3 : n * (m * A + c * (e - 1) + 1) = n * m * A + A := by rw [hA]; ring
  have h4 : (A + 1) * (n * m + 1) = n * m * A + A + (n * m + 1) := by ring
  rw [h3] at h1
  omega
def monoSpan (k : Type*) {L : Type*} [Field k] [Field L] [Algebra k L] (u v : L) (d : ℕ) :
    Submodule k L :=
  Submodule.span k {x | ∃ a b : ℕ, a + b ≤ d ∧ x = u ^ a * v ^ b}
def redSpan (k : Type*) {L : Type*} [Field k] [Field L] [Algebra k L] (u v : L) (n d : ℕ) :
    Submodule k L :=
  Submodule.span k (Set.range fun p : Fin (d + 1) × Fin n => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ))
theorem monoSpan_mono (u v : L) {d d' : ℕ} (h : d ≤ d') : monoSpan k u v d ≤ monoSpan k u v d' :=
  Submodule.span_mono fun _ ⟨a, b, hab, hx⟩ => ⟨a, b, hab.trans h, hx⟩
theorem one_mem_monoSpan (u v : L) : (1 : L) ∈ monoSpan k u v 0 :=
  Submodule.subset_span ⟨0, 0, le_rfl, by simp⟩
theorem mul_mem_monoSpan (u v : L) {d d' : ℕ} {x y : L} (hx : x ∈ monoSpan k u v d)
    (hy : y ∈ monoSpan k u v d') : x * y ∈ monoSpan k u v (d + d') := by
  have h := Submodule.mul_mem_mul hx hy
  rw [monoSpan, monoSpan, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, b, hab, rfl⟩, _, ⟨a', b', hab', rfl⟩, rfl⟩
  exact ⟨a + a', b + b', by omega, by ring⟩
theorem monoSpan_le_redSpan (u v : L) (n : ℕ) (c : Fin n → Polynomial k)
    (hc : ∀ b : Fin n, (c b).natDegree + b ≤ n)
    (hF : v ^ n = ∑ b : Fin n, Polynomial.aeval u (c b) * v ^ (b : ℕ)) (d : ℕ) :
    monoSpan k u v d ≤ redSpan k u v n d := by
  rw [monoSpan, Submodule.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  show u ^ a * v ^ b ∈ redSpan k u v n d
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    by_cases hb : b < n
    · exact Submodule.subset_span ⟨(⟨a, by omega⟩, ⟨b, hb⟩), rfl⟩
    · rw [not_lt] at hb
      have hv : v ^ b = ∑ j : Fin n, Polynomial.aeval u (c j) * v ^ (b - n + (j : ℕ)) := by
        calc v ^ b = v ^ (b - n) * v ^ n := by rw [← pow_add]; congr 1; omega
          _ = ∑ j : Fin n, Polynomial.aeval u (c j) * v ^ (b - n + (j : ℕ)) := by
            rw [hF, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [pow_add]; ring
      rw [hv, Finset.mul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hj := j.2
      have hcj := hc j
      have hdeg : (c j).natDegree < n - (j : ℕ) + 1 := by omega
      rw [Polynomial.aeval_eq_sum_range' hdeg, Finset.sum_mul, Finset.mul_sum]
      refine Submodule.sum_mem _ fun i hi => ?_
      have hi' : i ≤ n - (j : ℕ) := by have := Finset.mem_range.1 hi; omega
      have hterm : u ^ a * ((c j).coeff i • u ^ i * v ^ (b - n + (j : ℕ))) =
          (c j).coeff i • (u ^ (a + i) * v ^ (b - n + (j : ℕ))) := by
        rw [pow_add, Algebra.smul_def, Algebra.smul_def]; ring
      rw [hterm]
      exact Submodule.smul_mem _ _ (ih (b - n + j) (by omega) (a + i) (by omega))
theorem finrank_redSpan_le (u v : L) (n d : ℕ) :
    Module.finrank k (redSpan k u v n d) ≤ n * (d + 1) := by
  have h := finrank_range_le_card (R := k)
    (fun p : Fin (d + 1) × Fin n => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ))
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm] at h
  exact h
theorem ord_le_degree_mul (w : Valuation L ℤᵐ⁰) (hk : ∀ a : k, a ≠ 0 → w (algebraMap k L a) = 1)
    (u v : L) (n : ℕ) (c : Fin n → Polynomial k) (hc : ∀ b : Fin n, (c b).natDegree + b ≤ n)
    (hF : v ^ n = ∑ b : Fin n, Polynomial.aeval u (c b) * v ^ (b : ℕ))
    (m : ℕ) (h : L) (hh : h ∈ monoSpan k u v m) (cc : ℕ) (p₁ p₂ : L)
    (hp₁ : p₁ ∈ monoSpan k u v cc) (hp₂ : p₂ ∈ monoSpan k u v cc) (hp₂0 : p₂ ≠ 0)
    (hπ : w p₁ = exp (-1) * w p₂) (e : ℕ) (he : w h = exp (-(e : ℤ))) : e ≤ n * m := by
  have hred : ∀ d, FiniteDimensional k (redSpan k u v n d) := fun d =>
    FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hle := monoSpan_le_redSpan u v n c hc hF
  have hfin : ∀ d, Module.Finite k (monoSpan k u v d) := fun d =>
    Submodule.finiteDimensional_of_le (hle d)
  exact ord_le_of_filtration w hk (monoSpan k u v) (fun d d' x y hx hy => mul_mem_monoSpan u v hx hy)
    (one_mem_monoSpan u v) (fun d d' hdd => monoSpan_mono u v hdd) n hfin
    (fun d => (Submodule.finrank_mono (hle d)).trans (finrank_redSpan_le u v n d))
    m h hh cc p₁ p₂ hp₁ hp₂ hp₂0 hπ e he
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace LevelSurf
open RCN186 RCN188 RCN218 RCN230 RCN270 IsLocalRing
section Height
variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
theorem height_map_mk_span_singleton (g : R) (hg0 : g ≠ 0) (I p : Ideal R) [hIprime : I.IsPrime]
    [p.IsPrime] (hI : I = Ideal.span {g}) (hIp : I ≤ p) (hheight : p.height = 2)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] : (p.map (Ideal.Quotient.mk I)).height = 1 := by
  have hIheight : I.height = 1 := by
    rw [hI]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg0)
      fun hu => hIprime.ne_top (by rw [hI]; exact Ideal.span_singleton_eq_top.mpr hu)
  have hIpne : I ≠ p := by
    intro heq
    have h1 : I.height = p.height := congrArg Ideal.height heq
    rw [hIheight, hheight] at h1
    norm_num at h1
  obtain ⟨x, hxp, hxI⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hIp hIpne)
  have hmin : p ∈ (I ⊔ Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, sup_le hIp ((Ideal.span_singleton_le_iff_mem _).mpr hxp)⟩, ?_⟩
    rintro r ⟨hrprime, hJr⟩ hrp
    have hIrlt : I < r := lt_of_le_of_ne (le_sup_left.trans hJr) fun heq =>
      hxI (heq ▸ hJr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))
    by_contra hnot
    have hrlt : r < p := lt_of_le_of_ne hrp fun h => hnot h.ge
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hIrlt
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hrlt
    rw [hIheight] at h1
    rw [hheight] at h2
    have h3 : (1 : ℕ∞) + 1 + 1 ≤ 2 := (add_le_add_left h1 1).trans h2
    norm_num at h3
  refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hmin) ?_
  rw [Order.one_le_iff_ne_zero]
  intro hz
  have hcomap := RCN186.quotientPrime_comap_quotientMk I p hIp
  rw [RCN186.quotientPrime, Ideal.height_eq_zero_iff_eq_bot.mp hz] at hcomap
  change RingHom.ker (Ideal.Quotient.mk I) = p at hcomap
  rw [Ideal.mk_ker] at hcomap
  exact hIpne hcomap
end Height
variable {K : Type*} [Field K] {ι : Type*} [Finite ι]
theorem isDiscreteValuationRing_quotient_of_pderiv_notMem (g : MvPolynomial ι K) (hg0 : g ≠ 0)
    (I p : Ideal (MvPolynomial ι K)) [I.IsPrime] [p.IsPrime] (hI : I = Ideal.span {g}) (hIp : I ≤ p)
    (hheight : p.height = 2) (j : ι) (hj : MvPolynomial.pderiv j g ∉ p)
    [hq : (p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) := by
  have hq' : (RCN186.quotientPrime I p).IsPrime := hq
  have hdimF : ringKrullDim (RCN186.LocalizedQuotient I p hIp) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (RCN186.quotientPrime I p) (RCN186.LocalizedQuotient I p hIp)]
    exact_mod_cast height_map_mk_span_singleton g hg0 I p hI hIp hheight
  have : IsRegularLocalRing (Localization.AtPrime p) := RCN230.mvPolynomial_atPrime_isRegularLocalRing p
  let A := Localization.AtPrime p
  let f : A := algebraMap (MvPolynomial ι K) A g
  have hdim : ringKrullDim A = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A, hheight]
    norm_num
  have hf : f ∈ maximalIdeal A :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A p g).mpr
      (hIp (hI ▸ Ideal.mem_span_singleton_self g))
  have hf2 : f ∉ maximalIdeal A ^ 2 := by
    intro hf2
    let D : Derivation K A A :=
      RCN188.localizationDerivation p.primeCompl (MvPolynomial.pderiv j : Derivation K (MvPolynomial ι K) _)
    have hDmem : D f ∈ maximalIdeal A := RCN218.derivation_mem_maximal_of_mem_sq D f hf2
    have hD : D f = algebraMap (MvPolynomial ι K) A (MvPolynomial.pderiv j g) :=
      RCN188.localizationDerivation_algebraMap p.primeCompl _ g
    rw [hD] at hDmem
    exact hj ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p _).mp hDmem)
  let e : (A ⧸ Ideal.span {f}) ≃+* RCN186.LocalizedQuotient I p hIp :=
    (Ideal.quotEquivOfEq (by rw [hI, Ideal.map_span, Set.image_singleton])).trans (RCN186.quotientAmbientEquivLocalizedQuotient I p hIp)
  have : IsRegularLocalRing (A ⧸ Ideal.span {f}) :=
    BRW f hf hf2 hdim ((ringKrullDim_eq_of_ringEquiv e).trans hdimF)
  have : IsRegularLocalRing (RCN186.LocalizedQuotient I p hIp) :=
    IsRegularLocalRing.of_ringEquiv (R := A ⧸ Ideal.span {f}) e
  change IsDiscreteValuationRing (RCN186.LocalizedQuotient I p hIp)
  exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdimF
end LevelSurf
end FormalR
end SubmissionLower
end ProximityPrize
end
section
open IsLocalRing
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace KrullIntersection
section Local
variable {B K : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  [IsIntegrallyClosed B] [Field K] [Algebra B K] [IsFractionRing B K]
theorem maximalIdeal_isPrincipal_of_mul_mem (y : K)
    (hy : ∀ z ∈ maximalIdeal B, ∃ w : B, algebraMap B K w = y * algebraMap B K z)
    (hyB : ∀ w : B, algebraMap B K w ≠ y) (hne : maximalIdeal B ≠ ⊥) :
    (maximalIdeal B).IsPrincipal := by
  have hinj := IsFractionRing.injective B K
  by_cases h : ∀ z ∈ maximalIdeal B, ∃ w ∈ maximalIdeal B, algebraMap B K w = y * algebraMap B K z
  · exfalso
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hN : N ≠ ⊥ := by
      intro h0
      apply hne
      rw [eq_bot_iff]
      intro z hz
      have hmem : Algebra.linearMap B K z ∈ N := Submodule.mem_map_of_mem hz
      rw [h0, Submodule.mem_bot, Algebra.linearMap_apply] at hmem
      exact (Submodule.mem_bot B).mpr (hinj (hmem.trans (map_zero _).symm))
    have hfg : N.FG := Submodule.FG.map (Algebra.linearMap B K)
      ((isNoetherianRing_iff_ideal_fg B).mp inferInstance (maximalIdeal B))
    have hint : IsIntegral B y := by
      refine isIntegral_of_smul_mem_submodule N hN hfg y ?_
      intro n hn
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨w, hw, hwz⟩ := h z hz
      exact ⟨w, hw, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, smul_eq_mul, hwz]⟩
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact hyB w hw
  · push Not at h
    obtain ⟨z, hz, hzw⟩ := h
    obtain ⟨w, hw⟩ := hy z hz
    have hwu : IsUnit w := by
      by_contra hnu
      exact hzw w ((mem_maximalIdeal w).mpr hnu) hw
    obtain ⟨u, rfl⟩ := hwu
    have hunit : algebraMap B K (↑u⁻¹ : B) * algebraMap B K (u : B) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hone : algebraMap B K z * algebraMap B K (↑u⁻¹ : B) * y = 1 := by
      calc algebraMap B K z * algebraMap B K (↑u⁻¹ : B) * y
          = algebraMap B K (↑u⁻¹ : B) * (y * algebraMap B K z) := by ring
        _ = 1 := by rw [← hw, hunit]
    refine ⟨⟨z * ↑u⁻¹, ?_⟩⟩
    apply le_antisymm
    · intro z' hz'
      obtain ⟨w', hw'⟩ := hy z' hz'
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
      refine ⟨w', hinj ?_⟩
      rw [map_mul, map_mul, hw']
      calc algebraMap B K z'
          = algebraMap B K z * algebraMap B K (↑u⁻¹ : B) * y * algebraMap B K z' := by
            rw [hone, one_mul]
        _ = algebraMap B K z * algebraMap B K (↑u⁻¹ : B) * (y * algebraMap B K z') := by ring
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mul_mem_right _ _ hz
end Local
section Global
variable {A K : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
theorem isDiscreteValuationRing_of_colon (P : Ideal A) [P.IsPrime]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalization.AtPrime B P]
    [Algebra B K] [IsScalarTower A B K]
    (b d : A) (hb0 : b ≠ 0) (hmem : ∀ a : A, a ∈ P ↔ b ∣ a * d) :
    IsDiscreteValuationRing B := by
  have hinj := IsFractionRing.injective A K
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B P
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl B K
  have : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B P.primeCompl P.primeCompl_le_nonZeroDivisors
  have key : ∀ (a : A) (s : P.primeCompl),
      algebraMap B K (IsLocalization.mk' B a s) * algebraMap A K s = algebraMap A K a := by
    intro a s
    rw [IsScalarTower.algebraMap_apply A B K, IsScalarTower.algebraMap_apply A B K a, ← map_mul,
      IsLocalization.mk'_spec]
  have hsK : ∀ s : P.primeCompl, algebraMap A K s ≠ 0 := fun s =>
    (map_ne_zero_iff _ hinj).mpr (fun h0 => s.2 (h0 ▸ P.zero_mem))
  have hy : ∀ z ∈ maximalIdeal B, ∃ w : B,
      algebraMap B K w = algebraMap A K d / algebraMap A K b * algebraMap B K z := by
    intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    have ha : a ∈ P := (IsLocalization.AtPrime.mk'_mem_maximal_iff B P a s).mp hz
    obtain ⟨e, he⟩ := (hmem a).mp ha
    refine ⟨IsLocalization.mk' B e s, ?_⟩
    apply mul_right_cancel₀ (hsK s)
    rw [key, mul_assoc, key]
    have hK : algebraMap A K a * algebraMap A K d = algebraMap A K b * algebraMap A K e := by
      rw [← map_mul, ← map_mul, he]
    field_simp
    linear_combination -hK
  have hyB : ∀ w : B, algebraMap B K w ≠ algebraMap A K d / algebraMap A K b := by
    intro wB hw
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl wB
    have h1 := key a s
    rw [hw] at h1
    have hK : algebraMap A K (s * d) = algebraMap A K (b * a) := by
      rw [map_mul, map_mul, ← h1]
      field_simp
    exact s.2 ((hmem s).mpr ⟨a, hinj hK⟩)
  have hbP : b ∈ P := (hmem b).mpr ⟨d, rfl⟩
  have hne : maximalIdeal B ≠ ⊥ := by
    intro h0
    have h1 : algebraMap A B b ∈ maximalIdeal B :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff B P b).mpr hbP
    rw [h0, Ideal.mem_bot] at h1
    exact hb0 ((IsLocalization.to_map_eq_zero_iff B P.primeCompl_le_nonZeroDivisors).mp h1)
  have hprin := maximalIdeal_isPrincipal_of_mul_mem (B := B) _ hy hyB hne
  have hfield : ¬IsField B := fun hf => hne (IsLocalRing.isField_iff_maximalIdeal_eq.mp hf)
  exact ((IsDiscreteValuationRing.TFAE B hfield).out 1 5).mpr hprin
theorem exists_dvr_localization_not_mem (x : K) (hx : ∀ a : A, algebraMap A K a ≠ x) :
    ∃ P : Ideal A, ∃ _ : P.IsPrime, IsDiscreteValuationRing (Localization.AtPrime P) ∧
      ∀ a s : A, s ∉ P → x * algebraMap A K s ≠ algebraMap A K a := by
  classical
  have hinj := IsFractionRing.injective A K
  obtain ⟨c, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hc : Ideal.Quotient.mk (Ideal.span {b}) c ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    obtain ⟨e, rfl⟩ := h0
    exact hx e (by rw [map_mul]; field_simp)
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
    (R := A) (M := A ⧸ Ideal.span {b}) _ hc
  obtain ⟨hprime, m, hPm⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hcolon : ∀ (a e : A), a ∈ (⊥ : Submodule A (A ⧸ Ideal.span {b})).colon
      {Ideal.Quotient.mk (Ideal.span {b}) e} ↔ b ∣ a * e := by
    intro a e
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.mem_span_singleton,
      ← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    rfl
  have hmem : ∀ a : A, a ∈ P ↔ b ∣ a * d := fun a => by rw [hPm]; exact hcolon a d
  refine ⟨P, hprime, ?_, ?_⟩
  · let _ : Algebra (Localization.AtPrime P) K := (IsLocalization.lift (M := P.primeCompl)
      (S := Localization.AtPrime P) (g := algebraMap A K) (fun s => IsUnit.mk0 _
        ((map_ne_zero_iff _ hinj).mpr (fun h0 => s.2 (h0 ▸ P.zero_mem))))).toAlgebra
    have : IsScalarTower A (Localization.AtPrime P) K := IsScalarTower.of_algebraMap_eq
      (fun a => (IsLocalization.lift_eq _ a).symm)
    exact isDiscreteValuationRing_of_colon (K := K) P (Localization.AtPrime P) b d hb0 hmem
  · intro a s hs hxs
    have hK : algebraMap A K (s * c) = algebraMap A K (b * a) := by
      rw [map_mul, map_mul, ← hxs]
      field_simp
    exact hs (hle ((hcolon s c).mpr ⟨a, hinj hK⟩))
end Global
end KrullIntersection
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open IsDedekindDomain
open scoped Pointwise
section Closure
variable (B : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Ring.DimensionLEOne B]
  (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K] [Module.Finite B (integralClosure B K)]
scoped instance closure_isDedekindDomain : IsDedekindDomain (integralClosure B K) := by
  have hN : IsNoetherianRing (integralClosure B K) :=
    isNoetherian_of_tower B (isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B K))
  rw [isDedekindDomain_iff (integralClosure B K) K]
  exact ⟨inferInstance, hN, inferInstance, fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩⟩
omit [IsNoetherianRing B] [Ring.DimensionLEOne B] [Module.Finite B (integralClosure B K)] in
theorem closure_algebraMap_injective : Function.Injective (algebraMap B (integralClosure B K)) :=
  FaithfulSMul.algebraMap_injective B (integralClosure B K)
omit [IsDomain B] [IsNoetherianRing B] [IsFractionRing B K]
  [Module.Finite B (integralClosure B K)] in
variable {B K} in
theorem under_eq_maximalIdeal [IsLocalRing B] (V : HeightOneSpectrum (integralClosure B K)) :
    V.asIdeal.under B = IsLocalRing.maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal ((inferInstance : (V.asIdeal.under B).IsPrime).isMaximal
    (Ideal.IsIntegral.under_ne_bot B V.ne_bot))
scoped instance closure_finite_places [IsLocalRing B] :
    Finite (HeightOneSpectrum (integralClosure B K)) := by
  by_cases hm : IsLocalRing.maximalIdeal B = ⊥
  · have : IsEmpty (HeightOneSpectrum (integralClosure B K)) :=
      ⟨fun V => Ideal.IsIntegral.under_ne_bot B V.ne_bot ((under_eq_maximalIdeal V).trans hm)⟩
    infer_instance
  · have hI : (IsLocalRing.maximalIdeal B).map (algebraMap B (integralClosure B K)) ≠ 0 := by
      rwa [Ideal.zero_eq_bot, Ne,
        Ideal.map_eq_bot_iff_of_injective (closure_algebraMap_injective B K)]
    refine Set.finite_univ_iff.mp ((Ideal.finite_factors hI).subset fun V _ => ?_)
    rw [Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    exact (under_eq_maximalIdeal V).ge
theorem closure_finite_maximalIdeals [IsLocalRing B] :
    {I : Ideal (integralClosure B K) | I.IsMaximal}.Finite := by
  refine ((Set.finite_range fun V : HeightOneSpectrum (integralClosure B K) => V.asIdeal).union
    (Set.finite_singleton ⊥)).subset fun I hI => ?_
  by_cases h : I = ⊥
  · exact Or.inr h
  · exact Or.inl ⟨⟨I, hI.isPrime, h⟩, rfl⟩
theorem closure_isPrincipalIdealRing [IsLocalRing B] :
    IsPrincipalIdealRing (integralClosure B K) :=
  IsPrincipalIdealRing.of_finite_maximals (closure_finite_maximalIdeals B K)
omit [IsFractionRing B K] [Module.Finite B (integralClosure B K)] in
variable {B} in
theorem isFiniteLength_of_smul_eq_zero (M : Type*) [AddCommGroup M] [Module B M]
    [Module.Finite B M] {x : B} (hx : x ≠ 0) (h : ∀ m : M, x • m = 0) : IsFiniteLength B M := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' B M
  have hP : Submodule.pi Set.univ (fun _ : Fin n => Ideal.span {x}) ≤ LinearMap.ker f := by
    intro v hv
    choose w hw using fun i => Ideal.mem_span_singleton'.mp (hv i (Set.mem_univ i))
    have : v = x • w := funext fun i => by simp [← hw i, mul_comm]
    rw [LinearMap.mem_ker, this, map_smul, h]
  have h1 : IsFiniteLength B (Fin n → B ⧸ Ideal.span {x}) := by
    rw [← Module.length_ne_top_iff, Module.length_pi]
    exact WithTop.mul_ne_top ENat.card_lt_top_of_finite.ne (Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton B (mem_nonZeroDivisors_of_ne_zero hx)))
  refine (h1.of_surjective (f := (Submodule.quotientPi _).symm.toLinearMap)
    (Submodule.quotientPi _).symm.surjective).of_surjective (f := Submodule.liftQ _ f hP) ?_
  intro m
  obtain ⟨v, rfl⟩ := hf m
  exact ⟨Submodule.Quotient.mk v, rfl⟩
end Closure
section Length
theorem length_quotient_map {R M₁ M : Type*} [Ring R] [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₁] [Module R M] (f : M₁ →ₗ[R] M) (hf : Function.Injective f)
    (N : Submodule R M₁) :
    Module.length R (M ⧸ N.map f) =
      Module.length R (M₁ ⧸ N) + Module.length R (M ⧸ LinearMap.range f) := by
  have hle : N.map f ≤ LinearMap.range f := LinearMap.map_le_range
  refine Module.length_eq_add_of_exact (N.mapQ (N.map f) f (Submodule.le_comap_map f N))
    (Submodule.factor hle) ?_ (Submodule.factor_surjective hle) ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.comap_map_eq_of_injective hf,
      Submodule.mkQ_map_self]
  · rw [LinearMap.exact_iff, Submodule.factor, Submodule.ker_mapQ, Submodule.range_mapQ,
      Submodule.comap_id]
theorem length_quotient_span_mul {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] (a : R)
    {b : R} (hb : b ∈ nonZeroDivisors R) :
    Module.length A (R ⧸ Ideal.span {a * b}) =
      Module.length A (R ⧸ Ideal.span {a}) + Module.length A (R ⧸ Ideal.span {b}) := by
  have h := Module.length_eq_add_of_exact ((Ideal.mulQuot b (Ideal.span {a})).restrictScalars A)
    ((Ideal.quotOfMul b (Ideal.span {a})).restrictScalars A)
    (Ideal.mulQuot_injective (Ideal.span {a}) hb) (Ideal.quotOfMul_surjective (Ideal.span {a}))
    (Ideal.exact_mulQuot_quotOfMul (Ideal.span {a}))
  have lem : b • Ideal.span {a} = Ideal.span {a * b} := by
    rw [← Submodule.singleton_set_smul, mul_comm]
    simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
  rwa [lem] at h
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
noncomputable def ordInt (V : HeightOneSpectrum R) (y : R) : ℕ := (-(V.intValuation y).log).toNat
theorem intValuation_eq_exp_neg_ordInt (V : HeightOneSpectrum R) {y : R} (hy : y ≠ 0) :
    V.intValuation y = WithZero.exp (-(ordInt V y : ℤ)) := by
  have h0 := V.intValuation_ne_zero y hy
  have h1 : (V.intValuation y).log ≤ 0 :=
    (WithZero.log_le_iff_le_exp h0).mpr (by simpa using V.intValuation_le_one y)
  rw [ordInt, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
theorem ordInt_eq_iff (V : HeightOneSpectrum R) {y : R} (hy : y ≠ 0) (n : ℕ) :
    ordInt V y = n ↔ V.intValuation y = WithZero.exp (-(n : ℤ)) := by
  rw [intValuation_eq_exp_neg_ordInt V hy, WithZero.exp_inj, neg_inj, Nat.cast_inj]
theorem ordInt_mul (V : HeightOneSpectrum R) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInt V (x * y) = ordInt V x + ordInt V y := by
  rw [ordInt_eq_iff V (mul_ne_zero hx hy), map_mul, intValuation_eq_exp_neg_ordInt V hx,
    intValuation_eq_exp_neg_ordInt V hy, ← WithZero.exp_add, Nat.cast_add, neg_add]
theorem ordInt_eq_zero (V : HeightOneSpectrum R) {y : R} (hy : y ∉ V.asIdeal) :
    ordInt V y = 0 := by
  simp [ordInt, HeightOneSpectrum.intValuation_eq_one_iff.mpr hy]
theorem ordInt_eq_one (V : HeightOneSpectrum R) {y : R} (hy : y ≠ 0)
    (h : V.asIdeal = Ideal.span {y}) : ordInt V y = 1 := by
  simp [ordInt, V.intValuation_singleton hy h]
theorem length_quotient_span_singleton_eq_sum {A : Type*} [CommRing A] [Algebra A R]
    [IsPrincipalIdealRing R] [Fintype (HeightOneSpectrum R)] {y : R} (hy : y ≠ 0) :
    Module.length A (R ⧸ Ideal.span {y}) =
      ∑ V : HeightOneSpectrum R, Module.length A (R ⧸ V.asIdeal) * (ordInt V y : ℕ∞) := by
  induction y using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hy
  | h₂ x hx =>
    have : Subsingleton (R ⧸ Ideal.span {x}) :=
      Submodule.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hx)
    rw [Module.length_eq_zero]
    refine (Finset.sum_eq_zero fun V _ => ?_).symm
    rw [ordInt_eq_zero V fun h => V.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hx)]
    simp
  | h₃ a p ha hp ih =>
    let V₀ : HeightOneSpectrum R :=
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp, by simpa using hp.ne_zero⟩
    have hsum : ∑ V : HeightOneSpectrum R, Module.length A (R ⧸ V.asIdeal) * (ordInt V p : ℕ∞) =
        Module.length A (R ⧸ Ideal.span {p}) := by
      rw [Finset.sum_eq_single V₀]
      · rw [ordInt_eq_one V₀ hp.ne_zero rfl, Nat.cast_one, mul_one]
      · intro V _ hV
        rw [ordInt_eq_zero V fun hpV => hV (HeightOneSpectrum.ext (V₀.isMaximal.eq_of_le
          V.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hpV)).symm), Nat.cast_zero,
          mul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [length_quotient_span_mul p (mem_nonZeroDivisors_of_ne_zero ha), ih ha, ← hsum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun V _ => by
      rw [ordInt_mul V hp.ne_zero ha, Nat.cast_add, mul_add]
theorem exists_ordInt_eq [IsPrincipalIdealRing R] [Fintype (HeightOneSpectrum R)]
    (c : HeightOneSpectrum R → ℕ) : ∃ y : R, y ≠ 0 ∧ ∀ V, ordInt V y = c V := by
  choose π hπ using fun V : HeightOneSpectrum R =>
    (IsPrincipalIdealRing.principal V.asIdeal).principal
  have hπ' : ∀ V : HeightOneSpectrum R, V.asIdeal = Ideal.span {π V} := hπ
  have hπ0 : ∀ V, π V ≠ 0 := fun V h =>
    V.ne_bot ((hπ' V).trans (Ideal.span_singleton_eq_bot.mpr h))
  have hy0 : ∏ V, π V ^ c V ≠ 0 := Finset.prod_ne_zero_iff.mpr fun V _ => pow_ne_zero _ (hπ0 V)
  refine ⟨∏ V, π V ^ c V, hy0, fun W => ?_⟩
  rw [ordInt_eq_iff W hy0, map_prod, Finset.prod_eq_single W]
  · rw [map_pow, W.intValuation_singleton (hπ0 W) (hπ' W), ← WithZero.exp_nsmul]
    simp
  · intro V _ hV
    rw [map_pow, HeightOneSpectrum.intValuation_eq_one_iff.mpr fun h => hV (HeightOneSpectrum.ext
      (V.isMaximal.eq_of_le W.isPrime.ne_top
        ((hπ' V).trans_le ((Ideal.span_singleton_le_iff_mem _).mpr h)))), one_pow]
  · exact fun h => absurd (Finset.mem_univ _) h
theorem dvd_of_forall_ordInt_le {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ V : HeightOneSpectrum R, ordInt V y ≤ ordInt V x) : y ∣ x := by
  have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hy
  obtain ⟨t, ht⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (FractionRing R)
    (algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y) fun V => by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy')),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        intValuation_eq_exp_neg_ordInt V hx, intValuation_eq_exp_neg_ordInt V hy,
        WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact h V
  refine ⟨t, IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [map_mul, ht, mul_div_cancel₀ _ hy']
end Length
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace PlaceSurf
open IntermediateField
variable {E F : Type*} [Field E] [Field F] [Algebra E F]
theorem finite_separable_of_range_le {K E' : Type*} [Field K] [Algebra K F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F] [Field E'] [Algebra E' F] (M : IntermediateField E' F)
    (h : ∀ x : K, algebraMap K F x ∈ M) : FiniteDimensional M F ∧ Algebra.IsSeparable M F := by
  let _ : Algebra K M := ((algebraMap K F).codRestrict M h).toAlgebra
  have : IsScalarTower K M F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FiniteDimensional.right K M F, Algebra.isSeparable_tower_top_of_isSeparable K M F⟩
theorem finite_separable_of_isSeparable {ξ t : F} [FiniteDimensional E⟮ξ⟯ F]
    [Algebra.IsSeparable E⟮ξ⟯ F] (h : IsSeparable E⟮t⟯ ξ) :
    FiniteDimensional E⟮t⟯ F ∧ Algebra.IsSeparable E⟮t⟯ F := by
  have hle : E⟮ξ⟯ ≤ (E⟮t⟯⟮ξ⟯).restrictScalars E :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (mem_adjoin_simple_self E⟮t⟯ ξ))
  obtain ⟨h1, h2⟩ := finite_separable_of_range_le (K := E⟮ξ⟯) (E⟮t⟯⟮ξ⟯) fun x => hle x.2
  have h3 : FiniteDimensional E⟮t⟯ E⟮t⟯⟮ξ⟯ := adjoin.finiteDimensional h.isIntegral
  have h4 : Algebra.IsSeparable E⟮t⟯ E⟮t⟯⟮ξ⟯ :=
    (isSeparable_adjoin_simple_iff_isSeparable E⟮t⟯ F).mpr h
  exact ⟨FiniteDimensional.trans E⟮t⟯ E⟮t⟯⟮ξ⟯ F, Algebra.IsSeparable.trans E⟮t⟯ E⟮t⟯⟮ξ⟯ F⟩
theorem isAlgebraic_adjoin_of_transcendental {ξ t : F} (hξ : Transcendental E ξ)
    [FiniteDimensional E⟮ξ⟯ F] (ht : Transcendental E t) :
    Algebra.IsAlgebraic (Algebra.adjoin E {t}) F := by
  have hξalg : Algebra.IsAlgebraic (Algebra.adjoin E {ξ}) F :=
    isAlgebraic_adjoin_iff_top.mp (Algebra.IsAlgebraic.of_finite E⟮ξ⟯ F)
  have hξb : IsTranscendenceBasis E (fun _ : PUnit => ξ) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨algebraicIndependent_unique_type_iff.mpr hξ, by rwa [Set.range_const]⟩
  have htb : IsTranscendenceBasis E (fun _ : PUnit => t) :=
    (algebraicIndependent_unique_type_iff.mpr ht).isTranscendenceBasis_of_trdeg_le_of_finite
      hξb.cardinalMk_eq_trdeg.ge
  have h := htb.isAlgebraic
  rwa [Set.range_const] at h
theorem finite_separable_of_pair {ξ t u : F} [FiniteDimensional E⟮ξ⟯ F] [Algebra.IsSeparable E⟮ξ⟯ F]
    (hu : IsSeparable E⟮t⟯ u) (h : ξ = t / u ∨ ξ = u / t) :
    FiniteDimensional E⟮t⟯ F ∧ Algebra.IsSeparable E⟮t⟯ F := by
  refine finite_separable_of_isSeparable (ξ := ξ) ?_
  have ht : t ∈ separableClosure E⟮t⟯ F :=
    mem_separableClosure_iff.mpr (isSeparable_algebraMap (AdjoinSimple.gen E t))
  have hu' : u ∈ separableClosure E⟮t⟯ F := mem_separableClosure_iff.mpr hu
  rcases h with rfl | rfl
  · exact mem_separableClosure_iff.mp (div_mem ht hu')
  · exact mem_separableClosure_iff.mp (div_mem hu' ht)
theorem exists_separating_of_div [PerfectField E] {ξ b s : F} (hξ : Transcendental E ξ)
    [FiniteDimensional E⟮ξ⟯ F] [Algebra.IsSeparable E⟮ξ⟯ F] (hξbs : ξ = b / s) :
    ∃ t, (t = b ∨ t = s) ∧ FiniteDimensional E⟮t⟯ F ∧ Algebra.IsSeparable E⟮t⟯ F := by
  have htr : Transcendental E b ∨ Transcendental E s := by
    by_contra hcon
    rw [not_or, Transcendental, Transcendental, not_not, not_not] at hcon
    refine hξ ?_
    rw [hξbs, div_eq_mul_inv]
    exact hcon.1.mul hcon.2.inv
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' E
  · have key : ∀ t : F, Transcendental E t → FiniteDimensional E⟮t⟯ F ∧ Algebra.IsSeparable E⟮t⟯ F := by
      intro t ht
      have : Algebra.IsAlgebraic E⟮t⟯ F :=
        isAlgebraic_adjoin_iff_top.mpr (isAlgebraic_adjoin_of_transcendental hξ ht)
      have : CharZero E⟮t⟯ := charZero_of_injective_algebraMap (algebraMap E E⟮t⟯).injective
      exact finite_separable_of_isSeparable (Algebra.IsSeparable.isSeparable E⟮t⟯ ξ)
    rcases htr with hb | hs
    · exact ⟨b, Or.inl rfl, key b hb⟩
    · exact ⟨s, Or.inr rfl, key s hs⟩
  have : ExpChar E p := .prime hp.out
  have : CharP F p := .of_ringHom_of_ne_zero (algebraMap E F) p hp.out.ne_zero
  have H : ∀ T : Finset F, LinearIndepOn E id (T : Set F) → LinearIndepOn E (· ^ p) (T : Set F) := by
    intro T hT
    refine hT.map_of_injective_injective (frobeniusEquiv E p).symm (frobenius F p).toAddMonoidHom
      (fun r hr => (map_eq_zero_iff _ (frobeniusEquiv E p).symm.injective).mp hr)
      (fun m hm => (map_eq_zero_iff _ (frobenius_inj F p)).mp hm) fun r m => ?_
    change frobenius F p ((frobeniusEquiv E p).symm r • m) = r • frobenius F p m
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, frobenius_def, frobenius_def, ← map_pow,
      frobeniusEquiv_symm_pow_p]
  have hbasis : ∀ (n : Fin 2) (m : {i : Fin 2 // i ≠ n}), (∀ m' : {i : Fin 2 // i ≠ n}, m' = m) →
      Transcendental E (![b, s] m) →
      IsTranscendenceBasis E fun i : {i : Fin 2 // i ≠ n} => ![b, s] i := by
    intro n m hm ht
    let _ : Unique {i : Fin 2 // i ≠ n} := ⟨⟨m⟩, hm⟩
    refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨algebraicIndependent_unique_type_iff.mpr ht, ?_⟩
    rw [Set.range_unique]
    exact isAlgebraic_adjoin_of_transcendental hξ ht
  have hn : ∃ n : Fin 2, IsTranscendenceBasis E fun i : {i : Fin 2 // i ≠ n} => ![b, s] i := by
    rcases htr with hb | hs
    · exact ⟨1, hbasis 1 ⟨0, by decide⟩ (by rintro ⟨i, hi⟩; fin_cases i <;> simp at hi ⊢) hb⟩
    · exact ⟨0, hbasis 0 ⟨1, by decide⟩ (by rintro ⟨i, hi⟩; fin_cases i <;> simp at hi ⊢) hs⟩
  obtain ⟨n, hn⟩ := hn
  obtain ⟨i, -, hi⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp.out H n hn
  fin_cases i
  · have hset : (![b, s] '' ({0}ᶜ : Set (Fin 2))) = {s} := by
      ext x
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j
        · exact absurd rfl hj
        · rfl
      · rintro rfl
        exact ⟨1, by decide, rfl⟩
    change IsSeparable (adjoin E (![b, s] '' ({0}ᶜ : Set (Fin 2)))) b at hi
    rw [hset] at hi
    exact ⟨s, Or.inr rfl, finite_separable_of_pair hi (Or.inr hξbs)⟩
  · have hset : (![b, s] '' ({1}ᶜ : Set (Fin 2))) = {b} := by
      ext x
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j
        · rfl
        · exact absurd rfl hj
      · rintro rfl
        exact ⟨0, by decide, rfl⟩
    change IsSeparable (adjoin E (![b, s] '' ({1}ᶜ : Set (Fin 2)))) s at hi
    rw [hset] at hi
    exact ⟨b, Or.inl rfl, finite_separable_of_pair hi (Or.inl hξbs)⟩
end PlaceSurf
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
section Module
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
noncomputable def relLength (A B : Submodule R M) : ℕ∞ :=
  Module.length R (B.map A.mkQ)
theorem relLength_top (A : Submodule R M) : relLength A ⊤ = Module.length R (M ⧸ A) := by
  rw [relLength, Submodule.map_top, Submodule.range_mkQ, Module.length_top]
theorem relLength_sup_left (A B : Submodule R M) : relLength A (A ⊔ B) = relLength A B := by
  rw [relLength, relLength, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
theorem length_quotient_eq_relLength_add {A B : Submodule R M} (h : A ≤ B) :
    Module.length R (M ⧸ A) = relLength A B + Module.length R (M ⧸ B) := by
  have hk : LinearMap.ker (Submodule.factor h) = B.map A.mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [relLength, ← hk]
  exact Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    (Submodule.factor_surjective h) (LinearMap.exact_subtype_ker_map _)
theorem relLength_comap (φ : M →ₗ[R] N) (A : Submodule R N) (B : Submodule R M) :
    relLength (A.comap φ) B = relLength A (B.map φ) := by
  have hinj : Function.Injective ((A.comap φ).mapQ A φ le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]
  have hmap : (B.map (A.comap φ).mkQ).map ((A.comap φ).mapQ A φ le_rfl) = (B.map φ).map A.mkQ := by
    rw [← Submodule.map_comp, ← Submodule.map_comp, Submodule.mapQ_mkQ]
  rw [relLength, relLength, ← hmap]
  exact (Submodule.equivMapOfInjective _ hinj _).length_eq
theorem relLength_anti_left {A A' : Submodule R M} (h : A ≤ A') (B : Submodule R M) :
    relLength A' B ≤ relLength A B := by
  have hmap : (B.map A.mkQ).map (Submodule.factor h) = B.map A'.mkQ := by
    rw [← Submodule.map_comp, Submodule.factor_comp_mk]
  rw [relLength, relLength, ← hmap]
  exact Module.length_le_of_surjective ((Submodule.factor h).submoduleMap (B.map A.mkQ))
    (LinearMap.submoduleMap_surjective _ _)
end Module
section Ring
variable {R : Type*} [CommRing R]
theorem relLength_sup_span_mul (P b : Ideal R) (g : R) (hg : ∀ a : R, a * g ∈ P → a ∈ P)
    (hfin : Module.length R (R ⧸ (P ⊔ b)) ≠ ⊤) :
    relLength (P ⊔ Ideal.span {g} * b) b = Module.length R (R ⧸ (P ⊔ Ideal.span {g})) := by
  have hX1 : P ⊔ Ideal.span {g} * b ≤ P ⊔ b := sup_le_sup_left Ideal.mul_le_right _
  have hX2 : P ⊔ Ideal.span {g} * b ≤ P ⊔ Ideal.span {g} := sup_le_sup_left Ideal.mul_le_left _
  have e1 : P ⊔ Ideal.span {g} * b ⊔ b = P ⊔ b :=
    le_antisymm (sup_le hX1 le_sup_right) (sup_le_sup_right le_sup_left _)
  have e2 : P ⊔ Ideal.span {g} * b ⊔ Ideal.span {g} = P ⊔ Ideal.span {g} :=
    le_antisymm (sup_le hX2 le_sup_right) (sup_le_sup_right le_sup_left _)
  have hrange : (⊤ : Submodule R R).map (LinearMap.toSpanSingleton R R g) = Ideal.span {g} := by
    rw [Submodule.map_top, LinearMap.range_toSpanSingleton]
  have hcomap : Submodule.comap (LinearMap.toSpanSingleton R R g) (P ⊔ Ideal.span {g} * b) =
      P ⊔ b := by
    ext a
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
    constructor
    · intro ha
      obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
      have hac : (a - c) * g = p := by linear_combination hpy.symm
      exact Submodule.mem_sup.mpr ⟨a - c, hg _ (hac ▸ hp), c, hc, sub_add_cancel a c⟩
    · intro ha
      obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
      rw [add_mul]
      exact Submodule.add_mem_sup (P.mul_mem_right g hp)
        (Ideal.mem_span_singleton_mul.mpr ⟨c, hc, mul_comm g c⟩)
  have h1 : relLength (P ⊔ Ideal.span {g} * b) b = relLength (P ⊔ Ideal.span {g} * b) (P ⊔ b) := by
    rw [← relLength_sup_left _ b, e1]
  have h4 : relLength (P ⊔ Ideal.span {g} * b) (P ⊔ Ideal.span {g}) =
      Module.length R (R ⧸ (P ⊔ b)) := by
    rw [← e2, relLength_sup_left, ← relLength_top, ← hcomap, relLength_comap, hrange]
  have h2 := length_quotient_eq_relLength_add hX1
  have h3 := length_quotient_eq_relLength_add hX2
  rw [h4] at h3
  rw [h1]
  refine ENat.add_left_injective_of_ne_top hfin ?_
  change relLength _ _ + _ = _ + _
  rw [← h2, h3, add_comm]
theorem length_quotient_ne_top_of_forall_isMaximal [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) : Module.length R (R ⧸ I) ≠ ⊤ := by
  have hdim : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun J hJ => by
    have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    have hmax : (J.comap (Ideal.Quotient.mk I)).IsMaximal :=
      h _ (hJ.comap _) (by
        intro x hx
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact J.zero_mem)
    have hJeq : (J.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = J :=
      Ideal.map_comap_of_surjective _ hsurj J
    rw [← hJeq]
    exact (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hmax).resolve_left
      (by rw [hJeq]; exact hJ.ne_top)
  have : IsArtinianRing (R ⧸ I) := isArtinianRing_iff_krullDimLE_zero.mpr hdim
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_quotient I,
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩
end Ring
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN064 RCN072 RCN084 RCN095 RCN135 RCN136 RCN199 RCN207 RCN208 RCN264 RCN341 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD LF _Q7 OT YE AVZ AGD
open MovingFiberThreeSources6811 (direction weight)
variable {E : Type} [Field E]
namespace Sec
def LocalGen (g s : MvPolynomial (Fin 3) E) (C : Ideal (MvPolynomial (Fin 3) E)) : Prop :=
  ∃ h : MvPolynomial (Fin 3) E, h ∉ C ∧
    ∀ x ∈ C, h * x ∈ Ideal.span ({g, s} : Set (MvPolynomial (Fin 3) E))
def GoodSection (g s D : MvPolynomial (Fin 3) E) : Prop :=
  ¬g ∣ s ∧ ∀ C ∈ RCN072.componentFamily E g s, D ∉ C ∧ LocalGen g s C
def linearForm (b : Fin 3 → E) : MvPolynomial (Fin 3) E :=
  ∑ m, MvPolynomial.C (b m) * MvPolynomial.X m
def linearMinor (b : Fin 3 → E) (i k : Fin 3) (g : MvPolynomial (Fin 3) E) : MvPolynomial (Fin 3) E :=
  MvPolynomial.C (b i) * MvPolynomial.pderiv k g - MvPolynomial.C (b k) * MvPolynomial.pderiv i g
def PencilFinite (E : Type) [Field E] : Prop :=
  ∀ g D ℓ : MvPolynomial (Fin 3) E, Irreducible g → ¬g ∣ D →
    {a : E | ∃ C ∈ RCN072.componentFamily E g (ℓ - MvPolynomial.C a), D ∈ C}.Finite
def SectionLocalGen (E : Type) [Field E] : Prop :=
  ∀ (g : MvPolynomial (Fin 3) E) (b : Fin 3 → E) (a : E) (i k : Fin 3), b i ≠ 0 → i ≠ k →
    ∀ C ∈ RCN072.componentFamily E g (linearForm b - MvPolynomial.C a), linearMinor b i k g ∉ C →
      LocalGen g (linearForm b - MvPolynomial.C a) C
def GoodPencil (E : Type) [Field E] : Prop :=
  ∀ (g D : MvPolynomial (Fin 3) E) (b : Fin 3 → E) (i k : Fin 3), Irreducible g → ¬g ∣ D →
    b i ≠ 0 → i ≠ k → ¬g ∣ linearMinor b i k g →
    {a : E | ¬GoodSection g (linearForm b - MvPolynomial.C a) D}.Finite
end Sec
variable [IsAlgClosed E]
def levelZeros (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime] (H G Q A : MvPolynomial (Fin 3) E) (c : E)
    (V : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E P))) : ℤ :=
  ∑ nu ∈ V, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E P) nu (movingValue P H G Q A - algebraMap E (RCN002.CoordinateField E P) c)
def SectionZeroBudget (K E : Type) [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E]
    [CharP E 2130706433] : Prop :=
  ∀ (eta : GenericField K →+* E) (F : MvPolynomial (Fin 4) K) (SZ : MovingFiberThreeSources6811.Source F) (p W : FlagDegree)
    (s : MvPolynomial (Fin 3) E) (scale z u v : ℕ), F ≠ 0 → RCN095.PolynomialInFlag p (BXI eta F) → RCN095.PolynomialInFlag W s →
    p.zOnly + p.yz + p.all < 2130706433 →
    2 * (p.zOnly + p.yz + p.all) * (W.zOnly + W.yz + W.all) < 2130706433 →
    (∀ Q A : MvPolynomial (Fin 3) E, (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN eta F SZ Q A scale z u v) →
    ∀ (Q A : MvPolynomial (Fin 3) E) (c : E), RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    ∀ active : Finset (ANR (BXI eta F) s (frozenH eta F)),
      (∀ a ∈ active, SZ.leading (codeMap eta) ∉ a.2.1) →
      ∀ V : (a : ANR (BXI eta F) s (frozenH eta F)) → Finset (RCN026.Place_p19 E (RCN002.CoordinateField E a.2.1)),
        (scale : ℤ) * (∑ a ∈ active,
            levelZeros a.2.1 (frozenH eta F) (frozenG eta F) Q A c (V a)) ≤
          ((W.zOnly * z + W.yz * u + W.all * v : ℕ) : ℤ)
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN095 RCN204 RCN313 RCN187
open RCN095 renaming PolynomialInFlag → BI
open BD
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
open SecondJetSupport (Box Poly)
variable {K : Type} [Field K]
theorem sliceProj_flag_le (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (c : MvPolynomial (Fin 4) K) (W : FlagDegree)
    (hc : ∀ e ∈ c.support, e 2 ≤ W.all ∧ e 1 + e 2 ≤ W.all + W.yz ∧
      e 1 + e 2 + e 3 ≤ W.all + W.yz + W.zOnly) :
    v (sliceProj F₀ c) ≤ exp (flagPole v (sliceCoord F₀) W) := by
  classical
  rw [← aeval_slice, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Valuation.map_sum_le v fun e he => ?_
  obtain ⟨h1, h2, h3⟩ := hc e he
  have hcoef : v (algebraMap K (SliceField F₀) (c.coeff e)) ≤ 1 :=
    (hK _ (MvPolynomial.mem_support_iff.1 he)).le
  have hx : ∀ j : Fin 3, v (sliceCoord F₀ j) ≤ exp (poleOrder v (sliceCoord F₀ j)) := fun j =>
    HFree6812.v_le_exp_vpole v _
  have hp : ∀ j : Fin 3, 0 ≤ poleOrder v (sliceCoord F₀ j) := fun j => vpole_nonneg v _
  rw [map_mul, map_prod, Fin.prod_univ_succ, Fin.prod_univ_three]
  simp only [Fin.cons_zero, Fin.cons_succ, map_pow]
  have e1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have e2 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have e3 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  rw [e1, e2, e3]
  have hmono : v (sliceCoord F₀ 0) ^ e 1 * v (sliceCoord F₀ 1) ^ e 2 * v (sliceCoord F₀ 2) ^ e 3 ≤
      exp (flagPole v (sliceCoord F₀) W) := by
    calc v (sliceCoord F₀ 0) ^ e 1 * v (sliceCoord F₀ 1) ^ e 2 * v (sliceCoord F₀ 2) ^ e 3
        ≤ exp (poleOrder v (sliceCoord F₀ 0)) ^ e 1 * exp (poleOrder v (sliceCoord F₀ 1)) ^ e 2 *
          exp (poleOrder v (sliceCoord F₀ 2)) ^ e 3 :=
          mul_le_mul' (mul_le_mul' (pow_le_pow_left' (hx 0) _) (pow_le_pow_left' (hx 1) _))
            (pow_le_pow_left' (hx 2) _)
      _ = exp ((e 1 : ℤ) * poleOrder v (sliceCoord F₀ 0) + (e 2 : ℤ) * poleOrder v (sliceCoord F₀ 1) +
          (e 3 : ℤ) * poleOrder v (sliceCoord F₀ 2)) := by
          rw [← exp_nsmul, ← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_add]
          simp only [nsmul_eq_mul]
      _ ≤ exp (flagPole v (sliceCoord F₀) W) := by
          rw [exp_le_exp, flagPole]
          have h0 := hp 0
          have h1' := hp 1
          have h2' := hp 2
          generalize poleOrder v (sliceCoord F₀ 0) = p0 at *
          generalize poleOrder v (sliceCoord F₀ 1) = p1 at *
          generalize poleOrder v (sliceCoord F₀ 2) = p2 at *
          have m1 : p0 ≤ max p0 p2 := le_max_left _ _
          have m2 : p2 ≤ max p0 p2 := le_max_right _ _
          have m3 : p1 ≤ max p1 (max p0 p2) := le_max_left _ _
          have m4 : max p0 p2 ≤ max p1 (max p0 p2) := le_max_right _ _
          generalize max p1 (max p0 p2) = M3 at *
          generalize max p0 p2 = M2 at *
          have c1 : (e 2 : ℤ) ≤ W.all := by exact_mod_cast h1
          have c2 : (e 1 : ℤ) + e 2 ≤ W.all + W.yz := by exact_mod_cast h2
          have c3 : (e 1 : ℤ) + e 2 + e 3 ≤ W.all + W.yz + W.zOnly := by exact_mod_cast h3
          have n1 : (0 : ℤ) ≤ e 1 := Nat.cast_nonneg _
          have n2 : (0 : ℤ) ≤ e 2 := Nat.cast_nonneg _
          nlinarith [mul_nonneg n1 (sub_nonneg.2 m1), mul_nonneg n2 (sub_nonneg.2 m3),
            mul_nonneg (sub_nonneg.2 c1) (sub_nonneg.2 m4), mul_nonneg (sub_nonneg.2 c2) (sub_nonneg.2 m2),
            mul_nonneg (sub_nonneg.2 c3) h2']
  calc v (algebraMap K (SliceField F₀) (c.coeff e)) *
        (v (sliceProj F₀ (MvPolynomial.X 0)) ^ e 0 *
          (v (sliceCoord F₀ 0) ^ e 1 * v (sliceCoord F₀ 1) ^ e 2 * v (sliceCoord F₀ 2) ^ e 3))
      ≤ 1 * (1 * exp (flagPole v (sliceCoord F₀) W)) :=
        mul_le_mul' hcoef (mul_le_mul' (pow_le_one' hX0 _) hmono)
    _ = exp (flagPole v (sliceCoord F₀) W) := by rw [one_mul, one_mul]
theorem source_place_bound (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (h2 : (2 : K) ≠ 0) (S : MovingFiberThreeSources6811.Source F)
    (hfact : (S.k.factorial : K) ≠ 0) (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1)
    (hlead : sliceProj F₀ (SecondJetCoefficients.asS S.P).leadingCoeff ≠ 0) :
    (S.d : ℤ) * placeT F F₀ v + (v (sliceProj F₀ (SecondJetCoefficients.asS S.P).leadingCoeff)).log ≤
      flagPole v (sliceCoord F₀) S.flag := by
  classical
  set φ := sliceProj F₀ with hφ
  set Q₀ := (SecondJetCoefficients.asS S.P).map φ with hQ₀
  set Nd := (SecondJetCoefficients.asS S.P).natDegree with hNd
  have hQ₀deg : Q₀.natDegree = Nd := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hlead
  have hQ₀lc : Q₀.leadingCoeff = φ (SecondJetCoefficients.asS S.P).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hQ₀deg, hQ₀, Polynomial.coeff_map, hNd, Polynomial.coeff_natDegree]
  have hQ₀ne : Q₀ ≠ 0 := fun h => hlead (by rw [← hQ₀lc, h, Polynomial.leadingCoeff_zero])
  have hφF : φ F = 0 := (HFree6812.sliceProj_eq_zero_iff F₀ F).2 hdvd
  have h2L : (2 : SliceField F₀) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SliceField F₀))).2 h2
    rwa [map_ofNat] at h
  have hφ2H : φ (2 * polyH K F) ≠ 0 := by
    rw [map_mul, map_ofNat]
    exact mul_ne_zero h2L hH
  have hfactL : (S.k.factorial : SliceField F₀) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SliceField F₀))).2 hfact
    simpa using h
  obtain ⟨Q₁, hQ₁⟩ := SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd S.P F φ S.s S.k S.hS hφF
    hφ2H hQ₀ne hfactL S.hdiv
  rw [← hQ₀] at hQ₁
  set t := SecondJetCarrierDichotomy.ratio φ F with ht
  have hv2 : v (2 : SliceField F₀) = 1 := by
    have h := hK 2 h2
    rwa [map_ofNat] at h
  have hvt : v t = v (sliceSigma F F₀) := by
    rw [ht, SecondJetCarrierDichotomy.ratio, sliceSigma, map_mul φ, map_ofNat, map_div₀, map_div₀,
      map_mul, hv2, one_mul]
  have hmonic : ((Polynomial.X - Polynomial.C t) ^ (S.k + 1)).Monic :=
    (Polynomial.monic_X_sub_C t).pow _
  have hQ₁ne : Q₁ ≠ 0 := fun h => hQ₀ne (by rw [hQ₁, h, mul_zero])
  have hdegsum : Nd = (S.k + 1) + Q₁.natDegree := by
    rw [← hQ₀deg, hQ₁, hmonic.natDegree_mul' hQ₁ne, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one]
  have hQ₁lc : Q₁.coeff (Nd - (S.k + 1)) = φ (SecondJetCoefficients.asS S.P).leadingCoeff := by
    have h1 : Nd - (S.k + 1) = Q₁.natDegree := by omega
    rw [h1, Polynomial.coeff_natDegree, ← hQ₀lc, hQ₁, Polynomial.leadingCoeff_monic_mul hmonic]
  set pY := poleOrder v (sliceCoord F₀ 0) with hpY
  set pR := poleOrder v (sliceCoord F₀ 1) with hpR
  set pZ := poleOrder v (sliceCoord F₀ 2) with hpZ
  set β := max pY pZ with hβ
  set α := max pR β with hα
  have hpZ0 : 0 ≤ pZ := vpole_nonneg v _
  have hβα : β ≤ α := le_max_right _ _
  have hβ0 : 0 ≤ β := hpZ0.trans (le_max_right _ _)
  have hlam : 0 ≤ 2 * α - β := by linarith
  have hBU := S.hBU
  have hUT := S.hUT
  have hdn := S.hdn
  have hB := S.hB
  have hn := S.hn
  rw [← hNd] at hn
  have hP : ∀ i, v ((((Polynomial.X - Polynomial.C t) ^ (S.k + 1)) * Q₁).coeff i) *
      (exp (2 * α - β)) ^ i ≤ exp (((S.T - S.U : ℕ) : ℤ) * pZ + ((S.U - S.B : ℕ) : ℤ) * β + (S.B : ℤ) * α) := by
    intro i
    rw [← hQ₁, hQ₀, Polynomial.coeff_map]
    by_cases hci : (SecondJetCoefficients.asS S.P).coeff i = 0
    · rw [hci, map_zero, map_zero, zero_mul]
      exact zero_le
    · obtain ⟨e₀, he₀⟩ := MvPolynomial.support_nonempty.2 hci
      have hb₀ := SecondJetRelaxedFlag.coefficient_bounds S.P S.B S.U S.T S.hshape i e₀ he₀
      have h2i : 2 * i ≤ S.B := by omega
      have hval := sliceProj_flag_le F₀ v hK hX0 ((SecondJetCoefficients.asS S.P).coeff i) ⟨S.T - S.U, S.U - S.B + i, S.B - 2 * i⟩
        (fun e he => by
          have hb := SecondJetRelaxedFlag.coefficient_bounds S.P S.B S.U S.T S.hshape i e he
          dsimp only
          omega)
      rw [flagPole] at hval
      dsimp only at hval
      rw [← hpY, ← hpR, ← hpZ, ← hβ, ← hα] at hval
      calc v (φ ((SecondJetCoefficients.asS S.P).coeff i)) * exp (2 * α - β) ^ i
          ≤ exp (((S.T - S.U : ℕ) : ℤ) * pZ + ((S.U - S.B + i : ℕ) : ℤ) * β +
              ((S.B - 2 * i : ℕ) : ℤ) * α) * exp (2 * α - β) ^ i := mul_le_mul' hval le_rfl
        _ = exp (((S.T - S.U : ℕ) : ℤ) * pZ + ((S.U - S.B : ℕ) : ℤ) * β + (S.B : ℤ) * α) := by
            rw [← exp_nsmul, ← exp_add]
            congr 1
            have c1 : ((S.U - S.B + i : ℕ) : ℤ) = ((S.U - S.B : ℕ) : ℤ) + i := by push_cast; ring
            have c2 : ((S.B - 2 * i : ℕ) : ℤ) = (S.B : ℤ) - 2 * i := by omega
            rw [c1, c2, nsmul_eq_mul]
            ring
  have hmain := RootMultiplicityWeightedHeight.coeff_log_bound_pow_factor v t Q₁ (S.k + 1) _ (2 * α - β)
    hlam hP (Nd - (S.k + 1)) (by rw [hQ₁lc]; exact hlead)
  rw [hQ₁lc] at hmain
  have hpt : poleOrder v t = vpole v (sliceSigma F F₀) := by
    rw [poleOrder, vpole, hvt]
  have hT : placeT F F₀ v = β + max (2 * α - β) (vpole v (sliceSigma F F₀)) := by
    have h : placeT F F₀ v = max (2 * α) (β + vpole v (sliceSigma F F₀)) := rfl
    rw [h, ← max_add_add_left]
    congr 1
    ring
  rw [hT, ← hpt]
  rw [hpt] at hmain
  rw [← hpt] at hmain
  generalize max (2 * α - β) (poleOrder v t) = M at hmain ⊢
  have hflag : flagPole v (sliceCoord F₀) S.flag =
      ((S.T - S.U : ℕ) : ℤ) * pZ + ((S.U - S.B + S.n0 : ℕ) : ℤ) * β +
        ((S.B - 2 * (S.n0 - (S.k + 1)) : ℕ) : ℤ) * α := rfl
  rw [hflag]
  have hd : (S.d : ℤ) = (S.k : ℤ) + 1 := by
    rw [MovingFiberThreeSources6811.Source.d]; push_cast; ring
  have c1 : ((S.U - S.B + S.n0 : ℕ) : ℤ) = ((S.U - S.B : ℕ) : ℤ) + S.n0 := by push_cast; ring
  have c2 : ((S.B - 2 * (S.n0 - (S.k + 1)) : ℕ) : ℤ) = (S.B : ℤ) - 2 * ((S.n0 : ℤ) - (S.k + 1)) := by
    omega
  have c3 : ((Nd - (S.k + 1) : ℕ) : ℤ) = (Nd : ℤ) - (S.k + 1) := by omega
  have c4 : (0 : ℤ) ≤ (Nd : ℤ) - S.n0 := by omega
  rw [c3] at hmain
  rw [hd, c1, c2]
  push_cast at hmain
  linarith [mul_nonneg c4 hlam]
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
section Provider
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN199 RCN237 RCN238 RCN243 RCN244 RCN264 RCN313 RCN327
open RCN095 renaming PolynomialInFlag → BI
open RCN334 RCN339 FA IB
noncomputable section
def cutR (m r v z : ℕ) : FlagDegree :=
  m • (⟨2 * z, 2 * v, 2 * r - 7⟩ : FlagDegree) + ⟨0, 0, 3⟩
def cellCutR (t y r : ℕ) : FlagDegree :=
  cutR (w + 1) r (y - r) (t - y)
end
end Provider
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN002 RCN313 RCN095 BD
open RCN095 renaming PolynomialInFlag → BI
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
noncomputable section
variable {K : Type} [Field K]
abbrev unitField (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (z : SliceField F₀) : IntermediateField K (SliceField F₀) :=
  IntermediateField.adjoin K {z, sliceProj F₀ (MvPolynomial.X 0)}
abbrev xField (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] :
    IntermediateField K (SliceField F₀) :=
  IntermediateField.adjoin K {sliceProj F₀ (MvPolynomial.X 0)}
def chartCoord (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) (i : Fin 3) :
    SliceField F₀ :=
  lmono (sliceCoord F₀) (chartExp sR sY sZ i)
def chartRing (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) :
    Subalgebra (xField F₀) (SliceField F₀) :=
  Algebra.adjoin (xField F₀) (Set.range (chartCoord F₀ sR sY sZ))
structure ChartDivisor (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool)
    (w : Valuation (SliceField F₀) ℤᵐ⁰) : Prop where
  norm : ∃ x, w x = exp (-1)
  le_one : ∀ a ∈ chartRing F₀ sR sY sZ, w a ≤ 1
  nonconst : ∃ t ∈ chartRing F₀ sR sY sZ,
    AlgebraicIndependent K ![t, sliceProj F₀ (MvPolynomial.X 0)] ∧
      ∀ a ∈ unitField F₀ t, a ≠ 0 → w a = 1
def tail (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F) (m : ℕ) :
    SliceField F₀ :=
  (⇑(HFree6812.sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1)
def cutFlag (m : ℕ) (Hf : FlagDegree) : FlagDegree :=
  m • (⟨2 * Hf.zOnly, 2 * Hf.yz, 2 * Hf.all - 5⟩ : FlagDegree) + ⟨0, 0, 3⟩
def srcLead (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (S : MovingFiberThreeSources6811.Source F) : SliceField F₀ :=
  sliceProj F₀ (SecondJetCoefficients.asS S.P).leadingCoeff
def psiS (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F) (S : MovingFiberThreeSources6811.Source F)
    (m : ℕ) : SliceField F₀ :=
  tail F F₀ hdvd m ^ (3 * S.d) * sliceProj F₀ (polyH K F) ^ (2 * m * S.d) * srcLead F F₀ S ^ (4 * m)
def surfaceChartRing {E : Type} [Field E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime]
    (sR sY sZ : Bool) : Subalgebra E (RCN002.CoordinateField E G) :=
  Algebra.adjoin E (Set.range fun i => lmono (coordinate E G) (chartExp sR sY sZ i))
section
variable {F₀ : MvPolynomial (Fin 4) K} [Fact (Irreducible F₀)] {sR sY sZ : Bool}
  {w : Valuation (SliceField F₀) ℤᵐ⁰}
theorem ChartDivisor.coord_le_one (hw : ChartDivisor F₀ sR sY sZ w) (i : Fin 3) :
    w (lmono (sliceCoord F₀) (chartExp sR sY sZ i)) ≤ 1 :=
  hw.le_one _ (Algebra.subset_adjoin ⟨i, rfl⟩)
theorem ChartDivisor.const_le_one (hw : ChartDivisor F₀ sR sY sZ w) (a : xField F₀) :
    w (a : SliceField F₀) ≤ 1 :=
  hw.le_one _ (Subalgebra.algebraMap_mem _ a)
theorem ChartDivisor.x0_le_one (hw : ChartDivisor F₀ sR sY sZ w) :
    w (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 :=
  hw.const_le_one ⟨_, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
theorem ChartDivisor.trivial_on_K (hw : ChartDivisor F₀ sR sY sZ w) (a : K) (ha : a ≠ 0) :
    w (algebraMap K (SliceField F₀) a) = 1 := by
  have h1 : w (algebraMap K (SliceField F₀) a) ≤ 1 := hw.const_le_one (algebraMap K (xField F₀) a)
  have h2 : w (algebraMap K (SliceField F₀) a⁻¹) ≤ 1 :=
    hw.const_le_one (algebraMap K (xField F₀) a⁻¹)
  have h3 : w (algebraMap K (SliceField F₀) a) * w (algebraMap K (SliceField F₀) a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ℤᵐ⁰) = w (algebraMap K (SliceField F₀) a) * w (algebraMap K (SliceField F₀) a⁻¹) := h3.symm
    _ ≤ w (algebraMap K (SliceField F₀) a) * 1 := mul_le_mul' le_rfl h2
    _ = w (algebraMap K (SliceField F₀) a) := mul_one _
end
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
theorem lmono_mem_subfield {L : Type*} [Field L] (E : Subfield L) (t : Fin 3 → L) (c : Fin 3 → ℤ)
    (h : ∀ i, c i ≠ 0 → t i ∈ E) : lmono t c ∈ E := by
  have key : ∀ i, t i ^ c i ∈ E := fun i => by
    by_cases hc : c i = 0
    · rw [hc, zpow_zero]; exact E.one_mem
    · exact E.zpow_mem (h i hc) _
  exact E.mul_mem (E.mul_mem (key 0) (key 1)) (key 2)
theorem natCast_ne_zero_of_lt {K : Type*} [Field K] [CharP K 2130706433] (n : ℕ) (hn : 0 < n)
    (hlt : n < 2130706433) : (n : K) ≠ 0 := fun h =>
  absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)
theorem chart_pole_arith (sR sY sZ : Bool) (i : Fin 3) (l0 l1 l2 B : ℤ)
    (h : ∀ j, -B ≤ chartExp sR sY sZ j 0 * l0 + chartExp sR sY sZ j 1 * l1 +
        chartExp sR sY sZ j 2 * l2 ∧
      chartExp sR sY sZ j 0 * l0 + chartExp sR sY sZ j 1 * l1 + chartExp sR sY sZ j 2 * l2 ≤ 0)
    (hu : chartExp sR sY sZ i 0 * l0 + chartExp sR sY sZ i 1 * l1 +
      chartExp sR sY sZ i 2 * l2 = 0) :
    max (max 0 l1) (max (max 0 l0) (max 0 l2)) ≤ 2 * B := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases i <;>
    simp [chartExp] at h0 h1 h2 hu <;> omega
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial
section Monomials
variable {L : Type*} [Field L]
theorem Chart.lmono_add (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (a b : Fin 3 → ℤ) :
    lmono x (a + b) = lmono x a * lmono x b := by
  simp only [lmono, Pi.add_apply, zpow_add₀ (hx _)]
  ring
theorem lmono_ne_zero (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (a : Fin 3 → ℤ) : lmono x a ≠ 0 :=
  mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (hx 0)) (zpow_ne_zero _ (hx 1))) (zpow_ne_zero _ (hx 2))
theorem Chart.lmono_zpow (x : Fin 3 → L) (a : Fin 3 → ℤ) (n : ℤ) :
    lmono x a ^ n = lmono x fun j => n * a j := by
  rw [lmono, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  simp only [lmono, mul_comm n]
theorem Chart.lmono_lmono (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (E : Fin 3 → Fin 3 → ℤ) (a : Fin 3 → ℤ) :
    lmono (fun i => lmono x (E i)) a =
      lmono x fun j => a 0 * E 0 j + a 1 * E 1 j + a 2 * E 2 j := by
  show lmono x (E 0) ^ a 0 * lmono x (E 1) ^ a 1 * lmono x (E 2) ^ a 2 = _
  rw [lmono_zpow, lmono_zpow, lmono_zpow, ← lmono_add x hx, ← lmono_add x hx]
  rfl
def chartLam (sR sY sZ : Bool) (a b c : ℤ) : Fin 3 → ℤ :=
  ![if sR then -b else b, if sY then -(a + b) else a, if sZ then -(a + b + c) else c]
theorem Chart.lmono_chart (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (sR sY sZ : Bool) (a b c : ℤ) :
    lmono (fun i => lmono x (chartExp sR sY sZ i)) (chartLam sR sY sZ a b c) = lmono x ![a, b, c] := by
  rw [lmono_lmono x hx]
  congr 1
  funext j
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases j <;>
    simp [chartLam, chartExp] <;> ring
theorem coord_eq_lmono_chart (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (sR sY sZ : Bool) (j : Fin 3) :
    x j = lmono (fun i => lmono x (chartExp sR sY sZ i))
      (chartLam sR sY sZ (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) (if j = 2 then 1 else 0)) := by
  rw [Chart.lmono_chart x hx]
  fin_cases j <;> simp [lmono]
theorem coord_mem_of_chart_mem (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (sR sY sZ : Bool) (E : Subfield L)
    (h : ∀ i, lmono x (chartExp sR sY sZ i) ∈ E) (j : Fin 3) : x j ∈ E := by
  rw [coord_eq_lmono_chart x hx sR sY sZ j]
  exact E.mul_mem (E.mul_mem (zpow_mem (h 0) _) (zpow_mem (h 1) _)) (zpow_mem (h 2) _)
def chartNu (sR sY sZ : Bool) (N a b c : ℕ) : Fin 3 → ℕ :=
  ![if sR then N - b else b, if sY then N - (a + b) else a, if sZ then N - (a + b + c) else c]
theorem chartNu_le (sR sY sZ : Bool) (N a b c : ℕ) (h : a + b + c ≤ N) (i : Fin 3) :
    chartNu sR sY sZ N a b c i ≤ N := by
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases i <;>
    simp [chartNu] <;> omega
theorem Chart.chartNu_inj (sR sY sZ : Bool) (N a b c a' b' c' : ℕ) (h : a + b + c ≤ N)
    (h' : a' + b' + c' ≤ N) (he : chartNu sR sY sZ N a b c = chartNu sR sY sZ N a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    simp [chartNu] at h0 h1 h2 <;> omega
theorem chartNu_mono (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (sR sY sZ : Bool) (N a b c : ℕ)
    (h : a + b + c ≤ N) :
    lmono x (chartExp sR sY sZ 0) ^ chartNu sR sY sZ N a b c 0 *
        lmono x (chartExp sR sY sZ 1) ^ chartNu sR sY sZ N a b c 1 *
        lmono x (chartExp sR sY sZ 2) ^ chartNu sR sY sZ N a b c 2 =
      lmono x (chartExp sR sY sZ 0) ^ (if sR then N else 0) *
        lmono x (chartExp sR sY sZ 1) ^ (if sY then N else 0) *
        lmono x (chartExp sR sY sZ 2) ^ (if sZ then N else 0) * (x 0 ^ a * x 1 ^ b * x 2 ^ c) := by
  set t : Fin 3 → L := fun i => lmono x (chartExp sR sY sZ i) with ht
  have ht0 : ∀ i, t i ≠ 0 := fun i => lmono_ne_zero x hx _
  have e1 : ∀ n : Fin 3 → ℕ, t 0 ^ n 0 * t 1 ^ n 1 * t 2 ^ n 2 = lmono t fun i => (n i : ℤ) := by
    intro n
    simp only [lmono, zpow_natCast]
  have e3 : x 0 ^ a * x 1 ^ b * x 2 ^ c = lmono x ![(a : ℤ), b, c] := by
    simp [lmono, zpow_natCast]
  have e2 : t 0 ^ (if sR then N else 0) * t 1 ^ (if sY then N else 0) * t 2 ^ (if sZ then N else 0) =
      lmono t fun i => ((![if sR then N else 0, if sY then N else 0, if sZ then N else 0] i : ℕ) : ℤ) :=
    e1 ![if sR then N else 0, if sY then N else 0, if sZ then N else 0]
  show t 0 ^ _ * t 1 ^ _ * t 2 ^ _ = t 0 ^ _ * t 1 ^ _ * t 2 ^ _ * _
  rw [e1, e2, e3, ← Chart.lmono_chart x hx sR sY sZ, ← Chart.lmono_add t ht0]
  congr 1
  funext i
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases i <;>
    simp [chartNu, chartLam] <;> omega
end Monomials
section Substitution
theorem Chart.exists_monomialSubst {σ τ A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : MvPolynomial σ A) (hF : F ≠ 0) (μ : (σ →₀ ℕ) → (τ →₀ ℕ)) (hμ : Set.InjOn μ F.support)
    (x : σ → B) (y : τ → B) (m : B)
    (h : ∀ d ∈ F.support, ((μ d).prod fun i e => y i ^ e) = m * d.prod fun i e => x i ^ e) :
    ∃ P : MvPolynomial τ A, P ≠ 0 ∧ aeval y P = m * aeval x F ∧
      ∀ e ∈ P.support, ∃ d ∈ F.support, μ d = e := by
  classical
  refine ⟨∑ d ∈ F.support, monomial (μ d) (F.coeff d), ?_, ?_, ?_⟩
  · obtain ⟨d₀, hd₀⟩ : F.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
      exact hF
    intro h0
    have hc : (∑ d ∈ F.support, monomial (μ d) (F.coeff d)).coeff (μ d₀) = 0 := by
      rw [h0]
      rfl
    rw [coeff_sum, Finset.sum_eq_single d₀] at hc
    · simp only [coeff_monomial, ↓reduceIte] at hc
      exact (mem_support_iff.1 hd₀) hc
    · intro d hd hne
      rw [coeff_monomial]
      exact ite_eq_right_iff.2 fun he => absurd (hμ hd hd₀ he) hne
    · intro hn
      exact absurd hd₀ hn
  · rw [map_sum]
    conv_rhs => rw [F.as_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [aeval_monomial, aeval_monomial, h d hd]
    ring
  · intro e he
    obtain ⟨d, hd, hed⟩ := Finset.mem_biUnion.1 (support_sum he)
    exact ⟨d, hd, (Finset.mem_singleton.1 (support_monomial_subset hed)).symm⟩
variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]
theorem Chart.exists_chartPoly (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (F : MvPolynomial (Fin 3) A) (hF : F ≠ 0)
    (hFx : aeval x F = 0) (N : ℕ) (hN : ∀ d ∈ F.support, d 0 + d 1 + d 2 ≤ N) (sR sY sZ : Bool) :
    ∃ P : MvPolynomial (Fin 3) A, P ≠ 0 ∧ aeval (fun i => lmono x (chartExp sR sY sZ i)) P = 0 ∧
      ∀ e ∈ P.support, ∀ i, e i ≤ N := by
  set μ : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) := fun d =>
    Finsupp.equivFunOnFinite.symm (chartNu sR sY sZ N (d 0) (d 1) (d 2)) with hμdef
  have hμ : Set.InjOn μ F.support := by
    intro d hd d' hd' he
    have he' := chartNu_inj sR sY sZ N _ _ _ _ _ _ (hN d hd) (hN d' hd')
      (Finsupp.equivFunOnFinite.symm.injective he)
    ext i
    fin_cases i
    · exact he'.1
    · exact he'.2.1
    · exact he'.2.2
  obtain ⟨P, hP0, hPy, hPs⟩ := exists_monomialSubst F hF μ hμ x
    (fun i => lmono x (chartExp sR sY sZ i))
    (lmono x (chartExp sR sY sZ 0) ^ (if sR then N else 0) *
      lmono x (chartExp sR sY sZ 1) ^ (if sY then N else 0) *
      lmono x (chartExp sR sY sZ 2) ^ (if sZ then N else 0)) (by
    intro d hd
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      Fin.prod_univ_three, Fin.prod_univ_three]
    exact chartNu_mono x hx sR sY sZ N (d 0) (d 1) (d 2) (hN d hd))
  refine ⟨P, hP0, by rw [hPy, hFx, mul_zero], ?_⟩
  intro e he i
  obtain ⟨d, hd, rfl⟩ := hPs e he
  exact chartNu_le sR sY sZ N _ _ _ (hN d hd) i
theorem Chart.exists_chartPoly₄ (x0 : L) (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (F : MvPolynomial (Fin 4) A)
    (hF : F ≠ 0) (hFx : aeval (Fin.cons x0 x : Fin 4 → L) F = 0) (N : ℕ)
    (hN : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ N) (sR sY sZ : Bool) :
    ∃ P : MvPolynomial (Fin 4) A, P ≠ 0 ∧
      aeval (Fin.cons x0 (fun i => lmono x (chartExp sR sY sZ i)) : Fin 4 → L) P = 0 ∧
      ∀ e ∈ P.support, ∀ i : Fin 3, e i.succ ≤ N := by
  set μ : (Fin 4 →₀ ℕ) → (Fin 4 →₀ ℕ) := fun d =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (d 0) (chartNu sR sY sZ N (d 1) (d 2) (d 3))) with hμdef
  have hμ : Set.InjOn μ F.support := by
    intro d hd d' hd' he
    have he0 := Finsupp.equivFunOnFinite.symm.injective he
    have he' := chartNu_inj sR sY sZ N _ _ _ _ _ _ (hN d hd) (hN d' hd')
      (funext fun i => by simpa using congrFun he0 i.succ)
    ext i
    fin_cases i
    · simpa using congrFun he0 0
    · exact he'.1
    · exact he'.2.1
    · exact he'.2.2
  obtain ⟨P, hP0, hPy, hPs⟩ := exists_monomialSubst F hF μ hμ (Fin.cons x0 x : Fin 4 → L)
    (Fin.cons x0 (fun i => lmono x (chartExp sR sY sZ i)) : Fin 4 → L)
    (lmono x (chartExp sR sY sZ 0) ^ (if sR then N else 0) *
      lmono x (chartExp sR sY sZ 1) ^ (if sY then N else 0) *
      lmono x (chartExp sR sY sZ 2) ^ (if sZ then N else 0)) (by
    intro d hd
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      Fin.prod_univ_succ, Fin.prod_univ_succ (n := 3), Fin.prod_univ_three, Fin.prod_univ_three]
    have h3 := chartNu_mono x hx sR sY sZ N (d 1) (d 2) (d 3) (hN d hd)
    simp only [Fin.cons_zero, Fin.cons_succ, μ, Finsupp.equivFunOnFinite_symm_apply_apply]
    show x0 ^ d 0 * _ = _ * (x0 ^ d 0 * (x 0 ^ d 1 * x 1 ^ d 2 * x 2 ^ d 3))
    rw [h3]
    ring)
  refine ⟨P, hP0, by rw [hPy, hFx, mul_zero], ?_⟩
  intro e he i
  obtain ⟨d, hd, rfl⟩ := hPs e he
  simpa [μ] using chartNu_le sR sY sZ N _ _ _ (hN d hd) i
end Substitution
section Core
theorem Chart.exists_corePoly {σ ι A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : MvPolynomial σ A) (hP : P ≠ 0) (ρ : σ → Option ι) (hρ : Function.Injective ρ)
    (w : ι → B) (hw : AlgebraicIndependent A w) (y : B)
    (hPy : aeval (fun s => (ρ s).elim y w) P = 0) (s₀ : σ) (hs₀ : ρ s₀ = none) (N : ℕ)
    (hN : P.degreeOf s₀ ≤ N) :
    ∃ Q : Polynomial B, Q ≠ 0 ∧ Q.eval y = 0 ∧ Q.natDegree ≤ N ∧
      ∀ n, Q.coeff n ∈ Algebra.adjoin A (Set.range w) := by
  set V : Option ι → Polynomial B := fun o => o.elim Polynomial.X fun i => Polynomial.C (w i) with hV
  have hcomp : (aeval V : MvPolynomial (Option ι) A →ₐ[A] Polynomial B) =
      (Polynomial.mapAlgHom (aeval w)).comp (optionEquivLeft A ι).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro (_ | j)
    · simp [V, optionEquivLeft_X_none]
    · simp [V, optionEquivLeft_X_some]
  set R := rename ρ P with hR
  have hR0 : R ≠ 0 := fun h => hP (rename_injective ρ hρ (h.trans (map_zero _).symm))
  have hQ : aeval V R =
      (optionEquivLeft A ι R).map (aeval w : MvPolynomial ι A →ₐ[A] B).toRingHom := by
    rw [hcomp]
    rfl
  refine ⟨aeval V R, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact (Polynomial.map_ne_zero_iff hw).2 fun h =>
      hR0 ((optionEquivLeft A ι).injective (h.trans (map_zero _).symm))
  · have h1 := comp_aeval_apply (f := V) ((Polynomial.aeval (R := B) y).restrictScalars A) R
    rw [AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval] at h1
    rw [h1, hR, aeval_rename, ← hPy]
    refine congrArg (fun f : σ → B => aeval f P) (funext fun s => ?_)
    simp only [Function.comp_apply, AlgHom.restrictScalars_apply]
    rcases ρ s with _ | i <;> simp [V]
  · rw [hQ]
    refine Polynomial.natDegree_map_le.trans ?_
    rw [natDegree_optionEquivLeft, hR, ← hs₀, degreeOf_rename_of_injective hρ]
    exact hN
  · intro n
    rw [hQ, Polynomial.coeff_map, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨_, rfl⟩
end Core
section Specialize
variable {σ τ ι K k : Type*} [CommRing K] [CommRing k] [Algebra K k]
noncomputable def Chart.specialize (e : σ ≃ τ ⊕ ι) (w : ι → k) : MvPolynomial σ K →ₐ[K] MvPolynomial τ k :=
  aeval fun s => Sum.elim (fun j => (MvPolynomial.X j : MvPolynomial τ k)) (fun i => MvPolynomial.C (w i)) (e s)
theorem Chart.specialize_injective (e : σ ≃ τ ⊕ ι) (w : ι → k) (hw : AlgebraicIndependent K w) :
    Function.Injective (specialize (K := K) e w) := by
  have h : specialize (K := K) e w =
      (mapAlgHom (aeval w)).comp ((sumAlgEquiv K τ ι).toAlgHom.comp (rename e)) := by
    apply MvPolynomial.algHom_ext
    intro s
    simp only [specialize, aeval_X, AlgHom.comp_apply, rename_X]
    rcases e s with j | i
    · simp [sumAlgEquiv_X_inl]
    · simp [sumAlgEquiv_X_inr]
  rw [h, AlgHom.coe_comp, AlgHom.coe_comp]
  exact (map_injective _ hw).comp
    ((sumAlgEquiv K τ ι).injective.comp (rename_injective e e.injective))
theorem Chart.support_specialize [Fintype σ] [Fintype τ] [Fintype ι] (e : σ ≃ τ ⊕ ι) (w : ι → k)
    (P : MvPolynomial σ K) :
    ∀ m ∈ (specialize e w P).support, ∃ d ∈ P.support, ∀ j, m j = d (e.symm (Sum.inl j)) := by
  classical
  intro m hm
  have hsum : specialize e w P = ∑ d ∈ P.support,
      monomial (Finsupp.equivFunOnFinite.symm fun j => d (e.symm (Sum.inl j)))
        (algebraMap K k (P.coeff d) * ∏ i, w i ^ d (e.symm (Sum.inr i))) := by
    rw [specialize, aeval_def, eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.prod_equiv e _
      (fun x => Sum.elim (fun j => (MvPolynomial.X j : MvPolynomial τ k)) (fun i => MvPolynomial.C (w i)) x ^ d (e.symm x))
      (fun s => by rw [Equiv.symm_apply_apply]), Fintype.prod_sum_type, monomial_eq,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Sum.elim_inl, Sum.elim_inr, Finsupp.equivFunOnFinite_symm_apply_apply, ← C_pow,
      ← map_prod, C_mul]
    rw [IsScalarTower.algebraMap_apply K k (MvPolynomial τ k), MvPolynomial.algebraMap_eq]
    ring
  rw [hsum] at hm
  obtain ⟨d, hd, hmd⟩ := Finset.mem_biUnion.1 (support_sum hm)
  have hmd' := Finset.mem_singleton.1 (support_monomial_subset hmd)
  exact ⟨d, hd, fun j => by rw [hmd']; rfl⟩
theorem Chart.aeval_specialize {B : Type*} [CommRing B] [Algebra K B] [Algebra k B] [IsScalarTower K k B]
    (e : σ ≃ τ ⊕ ι) (w : ι → k) (y : τ → B) (P : MvPolynomial σ K) :
    aeval y (specialize e w P) =
      aeval (fun s => Sum.elim y (fun i => algebraMap k B (w i)) (e s)) P := by
  have h := comp_aeval_apply
    (f := fun s => Sum.elim (fun j => (MvPolynomial.X j : MvPolynomial τ k)) (fun i => MvPolynomial.C (w i)) (e s))
    ((aeval y : MvPolynomial τ k →ₐ[k] B).restrictScalars K) P
  rw [AlgHom.restrictScalars_apply] at h
  rw [specialize, h]
  refine congrArg (fun f : σ → B => aeval f P) (funext fun s => ?_)
  rw [AlgHom.restrictScalars_apply]
  rcases e s with j | i <;> simp
end Specialize
end FormalR
end SubmissionLower
end ProximityPrize
end
section
open WithZero
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
structure PrimeDivisor (O : Type*) [CommRing O] where
  ideal : Ideal O
  isPrime : ideal.IsPrime
  height_eq_one : ideal.height = 1
abbrev Divisor (O : Type*) [CommRing O] := PrimeDivisor O →₀ ℕ
def DivisorChain (O : Type*) [CommRing O] : Prop :=
  ∀ (P : PrimeDivisor O) (Q : Ideal O), Q.IsPrime → P.ideal < Q → Q.IsMaximal
section Definitions
variable {O : Type*} [CommRing O] (K : Type*) [Field K] [Algebra O K]
structure PrimeDivisor.IsValuation (P : PrimeDivisor O) (v : Valuation K ℤᵐ⁰) : Prop where
  surjective : Function.Surjective v
  le_one : ∀ a : O, v (algebraMap O K a) ≤ 1
  lt_one_iff : ∀ a : O, v (algebraMap O K a) < 1 ↔ a ∈ P.ideal
open Classical in
noncomputable def PrimeDivisor.valuation (P : PrimeDivisor O) : Valuation K ℤᵐ⁰ :=
  if h : ∃ v : Valuation K ℤᵐ⁰, P.IsValuation K v then h.choose else 1
noncomputable def divisorIdeal (D : Divisor O) : Ideal O where
  carrier := {a | ∀ P : PrimeDivisor O, P.valuation K (algebraMap O K a) ≤ exp (-(D P : ℤ))}
  add_mem' ha hb P := by
    rw [map_add]
    exact (Valuation.map_add_le_max' _ _ _).trans (max_le (ha P) (hb P))
  zero_mem' P := by simp
  smul_mem' c a ha P := by
    have h1 : P.valuation K (algebraMap O K c) ≤ 1 := by
      classical
      unfold PrimeDivisor.valuation
      split_ifs with h
      · exact h.choose_spec.le_one c
      · exact Valuation.one_apply_le_one _
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' h1 (ha P)).trans (one_mul _).le
noncomputable def PrimeDivisor.ord (P : PrimeDivisor O) (g : O) : ℕ :=
  (-(P.valuation K (algebraMap O K g)).log).toNat
open Classical in
noncomputable def div (g : O) : Divisor O :=
  if h : (Function.support fun P : PrimeDivisor O => P.ord K g).Finite then
    Finsupp.ofSupportFinite _ h else 0
end Definitions
section CommRing
variable {O : Type*} [CommRing O]
theorem PrimeDivisor.ext_ideal {P Q : PrimeDivisor O} (h : P.ideal = Q.ideal) : P = Q := by
  cases P
  cases Q
  cases h
  rfl
theorem PrimeDivisor.finiteHeight (P : PrimeDivisor O) : P.ideal.FiniteHeight :=
  ⟨Or.inr (by rw [P.height_eq_one]; exact ENat.one_ne_top)⟩
theorem PrimeDivisor.eq_of_le {P Q : PrimeDivisor O} (h : P.ideal ≤ Q.ideal) : P = Q := by
  have := P.isPrime
  have := P.finiteHeight
  exact PrimeDivisor.ext_ideal
    (Ideal.eq_of_le_of_height_le _ h (by rw [P.height_eq_one, Q.height_eq_one]))
theorem PrimeDivisor.exists_mem_notMem {P Q : PrimeDivisor O} (h : Q ≠ P) :
    ∃ a ∈ Q.ideal, a ∉ P.ideal :=
  Set.not_subset.mp fun hle => h (PrimeDivisor.eq_of_le hle)
end CommRing
section Localization
variable {O : Type*} [CommRing O] [IsDomain O]
theorem isDiscreteValuationRing_of_height_eq_one [IsNoetherianRing O] [IsIntegrallyClosed O]
    (P : Ideal O) [P.IsPrime] (hP : P.height = 1) (B : Type*) [CommRing B] [IsDomain B] [Algebra O B]
    [IsLocalization.AtPrime B P] : IsDiscreteValuationRing B := by
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B P
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hnf : ¬IsField B :=
    IsLocalization.AtPrime.not_isField O (Ideal.ne_bot_of_height_eq_one hP) B
  have : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P B, hP]
    rfl
  have h4 : IsIntegrallyClosed B ∧ ∃! Q : Ideal B, Q ≠ ⊥ ∧ Q.IsPrime :=
    ⟨inferInstance, IsLocalRing.maximalIdeal B,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩,
      fun Q hQ => IsLocalRing.eq_maximalIdeal (hQ.2.isMaximal_of_ne_bot hQ.1)⟩
  exact ((IsDiscreteValuationRing.TFAE B hnf).out 1 4).mpr h4
theorem height_eq_one_of_isDiscreteValuationRing (P : Ideal O) [P.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime P)) : P.height = 1 := by
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
  exact_mod_cast h1.symm
end Localization
section DiscreteValuation
variable {O : Type*} [CommRing O]
theorem exists_valuation_of_isDiscreteValuationRing (K : Type*) [Field K] [Algebra O K]
    (P : Ideal O) [P.IsPrime] (B : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B] [IsLocalization.AtPrime B P]
    [Algebra B K] [IsScalarTower O B K] [IsFractionRing B K] :
    ∃ v : Valuation K ℤᵐ⁰, Function.Surjective v ∧ (∀ a : O, v (algebraMap O K a) ≤ 1) ∧
      (∀ a : O, v (algebraMap O K a) < 1 ↔ a ∈ P) ∧
      ∀ x : K, v x ≤ 1 → ∃ a s : O, s ∉ P ∧ x * algebraMap O K s = algebraMap O K a := by
  let m : IsDedekindDomain.HeightOneSpectrum B := IsDiscreteValuationRing.maximalIdeal B
  refine ⟨m.valuation K, m.valuation_surjective K, fun a => ?_, fun a => ?_, fun x hx => ?_⟩
  · rw [IsScalarTower.algebraMap_apply O B K]
    exact m.valuation_le_one _
  · rw [IsScalarTower.algebraMap_apply O B K, m.valuation_lt_one_iff_mem]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff B P a
  · obtain ⟨n, d, hnd⟩ := m.exists_primeCompl_mul_eq_of_integer x hx
    obtain ⟨u, hu⟩ : IsUnit (d : B) := IsLocalRing.notMem_maximalIdeal.mp d.2
    obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq P.primeCompl (n * (↑u⁻¹ : B))
    refine ⟨a, s, s.2, ?_⟩
    have hd0 : algebraMap B K (d : B) ≠ 0 := by
      rw [← hu]
      exact (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr u.ne_zero
    have hx' : x = algebraMap B K (n * (↑u⁻¹ : B)) := by
      apply mul_right_cancel₀ hd0
      rw [hnd, ← map_mul, ← hu, mul_assoc, Units.inv_mul, mul_one]
    rw [hx', ← has, IsScalarTower.algebraMap_apply O B K, IsScalarTower.algebraMap_apply O B K a,
      ← map_mul, IsLocalization.mk'_spec]
theorem eq_one_of_log_eq_zero {y : ℤᵐ⁰} (hy : y ≠ 0) (h : y.log = 0) : y = 1 := by
  rw [← exp_log hy, h, exp_zero]
theorem PrimeDivisor.IsValuation.eq_of_forall {K : Type*} [Field K] [Algebra O K] {P : PrimeDivisor O}
    {v w : Valuation K ℤᵐ⁰} (hv : P.IsValuation K v)
    (hv' : ∀ x : K, v x ≤ 1 → ∃ a s : O, s ∉ P.ideal ∧ x * algebraMap O K s = algebraMap O K a)
    (hw : P.IsValuation K w) : w = v := by
  have hv1 : ∀ s : O, s ∉ P.ideal → v (algebraMap O K s) = 1 := fun s hs =>
    le_antisymm (hv.le_one s) (not_lt.mp fun h => hs ((hv.lt_one_iff s).mp h))
  have hw1 : ∀ s : O, s ∉ P.ideal → w (algebraMap O K s) = 1 := fun s hs =>
    le_antisymm (hw.le_one s) (not_lt.mp fun h => hs ((hw.lt_one_iff s).mp h))
  have hle : ∀ x : K, v x ≤ 1 → w x ≤ 1 := by
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := hv' x hx
    have h := hw.le_one a
    rwa [← hxs, map_mul, hw1 s hs, mul_one] at h
  have hlt : ∀ x : K, v x < 1 → w x < 1 := by
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := hv' x hx.le
    have ha : a ∈ P.ideal := by
      rw [← hv.lt_one_iff, ← hxs, map_mul, hv1 s hs, mul_one]
      exact hx
    have h := (hw.lt_one_iff a).mpr ha
    rwa [← hxs, map_mul, hw1 s hs, mul_one] at h
  have heq1 : ∀ x : K, v x = 1 → w x = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact zero_ne_one hx
    have h2 : w x⁻¹ ≤ 1 := hle x⁻¹ (by rw [map_inv₀, hx, inv_one])
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff w).mpr hx0))] at h2
    exact le_antisymm (hle x hx.le) h2
  obtain ⟨π, hπ⟩ := hv.surjective (exp (-1))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff w).mpr hπ0
  have hwπ : (w π).log < 0 :=
    (log_lt_iff_lt_exp hwπ0).mpr (by rw [exp_zero]; exact hlt π (by rw [hπ, exp_lt_one_iff]; omega))
  have key : ∀ x : K, x ≠ 0 → (w x).log = (v x).log * (-(w π).log) := by
    intro x hx
    have hvx : v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
    have hu : v (x * π ^ (v x).log) = 1 := by
      apply eq_one_of_log_eq_zero ((Valuation.ne_zero_iff _).mpr (mul_ne_zero hx (zpow_ne_zero _ hπ0)))
      rw [map_mul, map_zpow₀, hπ, log_mul hvx (zpow_ne_zero _ exp_ne_zero), log_zpow, log_exp,
        smul_eq_mul]
      ring
    have hwu := congrArg log (heq1 _ hu)
    rw [map_mul, map_zpow₀, log_mul hwx (zpow_ne_zero _ hwπ0), log_zpow, log_one, smul_eq_mul] at hwu
    linarith
  obtain ⟨y, hy⟩ := hw.surjective (exp (-1))
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact exp_ne_zero hy.symm
  have hm : -(w π).log = 1 := by
    have h1 := key y hy0
    rw [hy, log_exp] at h1
    exact Int.eq_one_of_dvd_one (by omega) ⟨-(v y).log, by linarith⟩
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have h1 := key x hx
    rw [hm, mul_one] at h1
    rw [← exp_log ((Valuation.ne_zero_iff w).mpr hx), h1,
      exp_log ((Valuation.ne_zero_iff _).mpr hx)]
end DiscreteValuation
section Valuation
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
theorem PrimeDivisor.exists_valuation (P : PrimeDivisor O) :
    ∃ v : Valuation K ℤᵐ⁰, P.IsValuation K v ∧
      ∀ x : K, v x ≤ 1 → ∃ a s : O, s ∉ P.ideal ∧ x * algebraMap O K s = algebraMap O K a := by
  have := P.isPrime
  have : IsDiscreteValuationRing (Localization.subalgebra.ofField K P.ideal.primeCompl
      P.ideal.primeCompl_le_nonZeroDivisors) :=
    isDiscreteValuationRing_of_height_eq_one P.ideal P.height_eq_one _
  obtain ⟨v, h1, h2, h3, h4⟩ := exists_valuation_of_isDiscreteValuationRing K P.ideal
    (Localization.subalgebra.ofField K P.ideal.primeCompl P.ideal.primeCompl_le_nonZeroDivisors)
  exact ⟨v, ⟨h1, h2, h3⟩, h4⟩
theorem PrimeDivisor.isValuation_valuation (P : PrimeDivisor O) : P.IsValuation K (P.valuation K) := by
  classical
  obtain ⟨v, hv, -⟩ := P.exists_valuation K
  unfold PrimeDivisor.valuation
  split_ifs with h
  · exact h.choose_spec
  · exact absurd ⟨v, hv⟩ h
theorem PrimeDivisor.valuation_surjective (P : PrimeDivisor O) :
    Function.Surjective (P.valuation K) :=
  (P.isValuation_valuation K).surjective
theorem PrimeDivisor.valuation_le_one (P : PrimeDivisor O) (a : O) :
    P.valuation K (algebraMap O K a) ≤ 1 :=
  (P.isValuation_valuation K).le_one a
theorem PrimeDivisor.valuation_lt_one_iff (P : PrimeDivisor O) (a : O) :
    P.valuation K (algebraMap O K a) < 1 ↔ a ∈ P.ideal :=
  (P.isValuation_valuation K).lt_one_iff a
theorem PrimeDivisor.valuation_eq_one_iff (P : PrimeDivisor O) (a : O) :
    P.valuation K (algebraMap O K a) = 1 ↔ a ∉ P.ideal := by
  rw [← P.valuation_lt_one_iff K, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (P.valuation_le_one K a) h⟩
theorem PrimeDivisor.valuation_le_one_iff (P : PrimeDivisor O) (x : K) :
    P.valuation K x ≤ 1 ↔ ∃ a s : O, s ∉ P.ideal ∧ x * algebraMap O K s = algebraMap O K a := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨v, hv, hv'⟩ := P.exists_valuation K
    rw [hv.eq_of_forall hv' (P.isValuation_valuation K)] at hx
    exact hv' x hx
  rintro ⟨a, s, hs, hxs⟩
  have h := P.valuation_le_one K a
  rwa [← hxs, map_mul, (P.valuation_eq_one_iff K s).mpr hs, mul_one] at h
theorem PrimeDivisor.valuation_unique (P : PrimeDivisor O) (w : Valuation K ℤᵐ⁰)
    (hw : P.IsValuation K w) : w = P.valuation K :=
  (P.isValuation_valuation K).eq_of_forall (fun x => (P.valuation_le_one_iff K x).mp) hw
theorem mem_range_of_valuation_le_one (x : K) (h : ∀ P : PrimeDivisor O, P.valuation K x ≤ 1) :
    ∃ a : O, algebraMap O K a = x := by
  by_contra hx
  obtain ⟨P, hP, hdvr, hns⟩ :=
    KrullIntersection.exists_dvr_localization_not_mem x fun a ha => hx ⟨a, ha⟩
  obtain ⟨a, s, hs, hxs⟩ := (PrimeDivisor.valuation_le_one_iff K
    ⟨P, hP, height_eq_one_of_isDiscreteValuationRing P hdvr⟩ x).mp (h _)
  exact hns a s hs hxs
omit [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] in
theorem PrimeDivisor.valuation_ne_zero (P : PrimeDivisor O) {g : O} (hg : g ≠ 0) :
    P.valuation K (algebraMap O K g) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hg)
theorem PrimeDivisor.valuation_eq_exp_neg_ord (P : PrimeDivisor O) {g : O} (hg : g ≠ 0) :
    P.valuation K (algebraMap O K g) = exp (-(P.ord K g : ℤ)) := by
  have h0 := P.valuation_ne_zero K hg
  have hle : (P.valuation K (algebraMap O K g)).log ≤ 0 :=
    (log_le_iff_le_exp h0).mpr (by rw [exp_zero]; exact P.valuation_le_one K g)
  rw [PrimeDivisor.ord, Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]
theorem PrimeDivisor.ord_ne_zero_iff (P : PrimeDivisor O) {g : O} (hg : g ≠ 0) :
    P.ord K g ≠ 0 ↔ g ∈ P.ideal := by
  rw [← P.valuation_lt_one_iff K, P.valuation_eq_exp_neg_ord K hg, exp_lt_one_iff]
  omega
omit [IsIntegrallyClosed O] in
theorem finite_setOf_mem_ideal {g : O} (hg : g ≠ 0) : {P : PrimeDivisor O | g ∈ P.ideal}.Finite := by
  refine Set.Finite.of_finite_image (f := PrimeDivisor.ideal)
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing O (Ideal.span {g})).subset ?_)
    fun P _ Q _ h => PrimeDivisor.ext_ideal h
  rintro _ ⟨P, hP, rfl⟩
  have := P.isPrime
  have := P.finiteHeight
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hP) ?_
  rw [P.height_eq_one]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hg)
theorem finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {P : PrimeDivisor O | P.valuation K x ≠ 1}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  refine ((finite_setOf_mem_ideal ha0).union (finite_setOf_mem_ideal hb0)).subset fun P hP => ?_
  by_contra hmem
  rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, not_or] at hmem
  exact hP (by rw [map_div₀, (P.valuation_eq_one_iff K a).mpr hmem.1,
    (P.valuation_eq_one_iff K b).mpr hmem.2, div_one])
theorem finite_support_ord (g : O) : (Function.support fun P : PrimeDivisor O => P.ord K g).Finite := by
  by_cases hg : g = 0
  · have h0 : (fun P : PrimeDivisor O => P.ord K g) = 0 := by
      funext P
      simp [PrimeDivisor.ord, hg]
    rw [h0, Function.support_zero]
    exact Set.finite_empty
  · exact (finite_setOf_mem_ideal hg).subset fun P hP => (P.ord_ne_zero_iff K hg).mp hP
theorem div_apply (g : O) (P : PrimeDivisor O) : div K g P = P.ord K g := by
  rw [div]
  split_ifs with h
  · rfl
  · exact absurd (finite_support_ord K g) h
theorem valuation_eq_exp_neg_div {g : O} (hg : g ≠ 0) (P : PrimeDivisor O) :
    P.valuation K (algebraMap O K g) = exp (-(div K g P : ℤ)) := by
  rw [div_apply]
  exact P.valuation_eq_exp_neg_ord K hg
theorem mem_support_div {g : O} (hg : g ≠ 0) (P : PrimeDivisor O) :
    P ∈ (div K g).support ↔ g ∈ P.ideal := by
  rw [Finsupp.mem_support_iff, div_apply]
  exact P.ord_ne_zero_iff K hg
omit [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O K] in
theorem mem_divisorIdeal {D : Divisor O} {a : O} :
    a ∈ divisorIdeal K D ↔
      ∀ P : PrimeDivisor O, P.valuation K (algebraMap O K a) ≤ exp (-(D P : ℤ)) :=
  Iff.rfl
theorem divisorIdeal_zero : divisorIdeal K (0 : Divisor O) = ⊤ := by
  refine eq_top_iff.mpr fun a _ => (mem_divisorIdeal K).mpr fun P => ?_
  rw [Finsupp.zero_apply, Nat.cast_zero, neg_zero, exp_zero]
  exact P.valuation_le_one K a
omit [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O K] in
theorem divisorIdeal_anti {D D' : Divisor O} (h : D ≤ D') : divisorIdeal K D' ≤ divisorIdeal K D :=
  fun _ ha P => (ha P).trans (exp_le_exp.mpr (by have := h P; omega))
theorem divisorIdeal_div {g : O} (hg : g ≠ 0) : divisorIdeal K (div K g) = Ideal.span {g} := by
  have hgK : algebraMap O K g ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hg
  ext a
  rw [mem_divisorIdeal, Ideal.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := mem_range_of_valuation_le_one K (algebraMap O K a / algebraMap O K g) fun P => by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr (P.valuation_ne_zero K hg)),
        valuation_eq_exp_neg_div K hg P]
      exact h P
    refine ⟨c, IsFractionRing.injective O K ?_⟩
    rw [map_mul, hc, mul_div_cancel₀ _ hgK]
  · rintro ⟨c, rfl⟩ P
    rw [map_mul, map_mul, ← valuation_eq_exp_neg_div K hg P]
    exact mul_le_of_le_one_right' (P.valuation_le_one K c)
theorem lt_one_iff_le_exp_neg_one {v : ℤᵐ⁰} : v < 1 ↔ v ≤ exp (-1 : ℤ) := by
  have h := lt_mul_exp_iff_le (x := v) (y := exp (-1 : ℤ)) exp_ne_zero
  rwa [← exp_add, neg_add_cancel, exp_zero] at h
theorem exp_mul_lt_one_iff (d : ℕ) (v : ℤᵐ⁰) :
    exp (d : ℤ) * v < 1 ↔ v ≤ exp (-((d + 1 : ℕ) : ℤ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k, v = exp k := ⟨v.log, (exp_log hv).symm⟩
    rw [← exp_add, exp_lt_one_iff, exp_le_exp]
    push_cast
    omega
theorem PrimeDivisor.exists_uniformizer (P : PrimeDivisor O) :
    ∃ t : O, P.valuation K (algebraMap O K t) = exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_surjective K (exp (-1))
  obtain ⟨a, s, hs, hπs⟩ := (P.valuation_le_one_iff K π).mp (by rw [hπ, exp_le_one_iff]; omega)
  refine ⟨a, ?_⟩
  rw [← hπs, map_mul, hπ, (P.valuation_eq_one_iff K s).mpr hs, mul_one]
theorem PrimeDivisor.exists_notMem_valuation_le (P : PrimeDivisor O) (S : Finset (PrimeDivisor O))
    (hS : P ∉ S) (b : PrimeDivisor O → ℤᵐ⁰) (hb : ∀ Q ∈ S, b Q ≠ 0) :
    ∃ w : O, w ∉ P.ideal ∧ ∀ Q ∈ S, Q.valuation K (algebraMap O K w) ≤ b Q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, P.isPrime.one_notMem, fun Q hQ => absurd hQ (Finset.notMem_empty Q)⟩
  | insert Q S hQS ih =>
    have hPQ : Q ≠ P := fun h => hS (h ▸ Finset.mem_insert_self Q S)
    obtain ⟨w, hw, hwS⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
      (fun Q' hQ' => hb Q' (Finset.mem_insert_of_mem hQ'))
    obtain ⟨a, haQ, haP⟩ := PrimeDivisor.exists_mem_notMem hPQ
    obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt (hb Q (Finset.mem_insert_self Q S))
    refine ⟨a ^ n * w, fun h => ?_, fun Q' hQ' => ?_⟩
    · rcases P.isPrime.mem_or_mem h with h1 | h1
      · exact haP (P.isPrime.mem_of_pow_mem n h1)
      · exact hw h1
    · rw [map_mul, map_mul, map_pow, map_pow]
      rcases Finset.mem_insert.mp hQ' with rfl | hQ'S
      · have ha : Q'.valuation K (algebraMap O K a) ≤ exp (-1 : ℤ) :=
          lt_one_iff_le_exp_neg_one.mp ((Q'.valuation_lt_one_iff K a).mpr haQ)
        calc Q'.valuation K (algebraMap O K a) ^ n * Q'.valuation K (algebraMap O K w)
            ≤ exp (-1 : ℤ) ^ n * 1 := mul_le_mul' (pow_le_pow_left' ha n) (Q'.valuation_le_one K w)
          _ = exp (-(n : ℤ)) := by rw [mul_one, ← exp_nsmul, nsmul_eq_mul, mul_neg_one]
          _ ≤ b Q' := hn.le
      · exact (mul_le_of_le_one_left' (pow_le_one' (Q'.valuation_le_one K a) n)).trans
          (hwS Q' hQ'S)
theorem exists_mem_divisorIdeal_valuation_eq (D : Divisor O) (P : PrimeDivisor O) :
    ∃ x ∈ divisorIdeal K D, P.valuation K (algebraMap O K x) = exp (-(D P : ℤ)) := by
  classical
  obtain ⟨t, ht⟩ := P.exists_uniformizer K
  obtain ⟨w, hwP, hw⟩ := P.exists_notMem_valuation_le K (D.support.erase P)
    (Finset.notMem_erase P _) (fun Q => exp (-(D Q : ℤ))) (fun _ _ => exp_ne_zero)
  have hval : P.valuation K (algebraMap O K (t ^ D P * w)) = exp (-(D P : ℤ)) := by
    rw [map_mul, map_mul, map_pow, map_pow, ht, (P.valuation_eq_one_iff K w).mpr hwP, mul_one,
      ← exp_nsmul,
      nsmul_eq_mul, mul_neg_one]
  refine ⟨t ^ D P * w, fun Q => ?_, hval⟩
  by_cases hQP : Q = P
  · rw [hQP, hval]
  · by_cases hQ : Q ∈ D.support
    · rw [map_mul, map_mul, map_pow, map_pow]
      exact (mul_le_of_le_one_left' (pow_le_one' (Q.valuation_le_one K t) _)).trans
        (hw Q (Finset.mem_erase.mpr ⟨hQP, hQ⟩))
    · rw [Finsupp.notMem_support_iff.mp hQ, Nat.cast_zero, neg_zero, exp_zero]
      exact Q.valuation_le_one K _
theorem divisorIdeal_not_le {L : Divisor O} {P : PrimeDivisor O} (h : L P = 0) :
    ¬divisorIdeal K L ≤ P.ideal := by
  obtain ⟨x, hx, hxP⟩ := exists_mem_divisorIdeal_valuation_eq K L P
  rw [h, Nat.cast_zero, neg_zero, exp_zero, P.valuation_eq_one_iff K] at hxP
  exact fun hle => hxP (hle hx)
theorem mem_divisorIdeal_of_mul_mem {D : Divisor O} {g a : O} (hg : ∀ P ∈ D.support, g ∉ P.ideal)
    (h : g * a ∈ divisorIdeal K D) : a ∈ divisorIdeal K D := by
  intro P
  by_cases hP : P ∈ D.support
  · have h1 := h P
    rwa [map_mul, map_mul, (P.valuation_eq_one_iff K g).mpr (hg P hP), one_mul] at h1
  · rw [Finsupp.notMem_support_iff.mp hP, Nat.cast_zero, neg_zero, exp_zero]
    exact P.valuation_le_one K a
structure IsTransfer (D : Divisor O) (P : PrimeDivisor O) (φ : divisorIdeal K D →ₗ[O] O) : Prop where
  valuation_le : ∀ (x : divisorIdeal K D) (Q : PrimeDivisor O),
    Q.valuation K (algebraMap O K (φ x)) ≤ exp (D Q : ℤ) * Q.valuation K (algebraMap O K (x : O))
  valuation_eq : ∀ x : divisorIdeal K D,
    P.valuation K (algebraMap O K (φ x)) = exp (D P : ℤ) * P.valuation K (algebraMap O K (x : O))
variable {K}
theorem IsTransfer.mem_ideal_iff {D : Divisor O} {P : PrimeDivisor O}
    {φ : divisorIdeal K D →ₗ[O] O} (h : IsTransfer K D P φ) (x : divisorIdeal K D) :
    φ x ∈ P.ideal ↔ (x : O) ∈ divisorIdeal K (D + Finsupp.single P 1) := by
  rw [← P.valuation_lt_one_iff K, h.valuation_eq, exp_mul_lt_one_iff, mem_divisorIdeal]
  constructor
  · intro hx Q
    by_cases hQP : Q = P
    · rw [hQP, Finsupp.add_apply, Finsupp.single_eq_same]
      exact hx
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hQP, add_zero]
      exact x.2 Q
  · intro hx
    have h1 := hx P
    rwa [Finsupp.add_apply, Finsupp.single_eq_same] at h1
theorem IsTransfer.mem_divisorIdeal {D : Divisor O} {P : PrimeDivisor O}
    {φ : divisorIdeal K D →ₗ[O] O} (h : IsTransfer K D P φ) {L : Divisor O}
    (hL : ∀ Q, D Q ≠ 0 → L Q = 0) {x : divisorIdeal K D} (hx : (x : O) ∈ divisorIdeal K L) :
    φ x ∈ divisorIdeal K L := by
  intro Q
  by_cases hQ : L Q = 0
  · rw [hQ, Nat.cast_zero, neg_zero, exp_zero]
    exact Q.valuation_le_one K _
  · have hD : D Q = 0 := by
      by_contra hD
      exact hQ (hL Q hD)
    have h1 := h.valuation_le x Q
    rw [hD, Nat.cast_zero, exp_zero, one_mul] at h1
    exact h1.trans (hx Q)
theorem IsTransfer.range_not_le {D : Divisor O} {P : PrimeDivisor O}
    {φ : divisorIdeal K D →ₗ[O] O} (h : IsTransfer K D P φ) :
    ¬Submodule.map φ ⊤ ≤ P.ideal := by
  obtain ⟨x, hx, hxP⟩ := exists_mem_divisorIdeal_valuation_eq K D P
  intro hle
  have h1 : φ ⟨x, hx⟩ ∈ P.ideal := hle (Submodule.mem_map_of_mem Submodule.mem_top)
  rw [← P.valuation_lt_one_iff K, h.valuation_eq, hxP, ← exp_add, add_neg_cancel, exp_zero] at h1
  exact lt_irrefl _ h1
variable (K)
theorem exists_isTransfer (D : Divisor O) (P : PrimeDivisor O) :
    ∃ φ : divisorIdeal K D →ₗ[O] O, IsTransfer K D P φ := by
  classical
  obtain ⟨x₀, hx₀, hx₀P⟩ := exists_mem_divisorIdeal_valuation_eq K D P
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx₀P
    exact exp_ne_zero hx₀P.symm
  obtain ⟨y, hyP, hy⟩ := P.exists_notMem_valuation_le K ((div K x₀).support.erase P)
    (Finset.notMem_erase P _) (fun Q => Q.valuation K (algebraMap O K x₀))
    (fun Q _ => Q.valuation_ne_zero K hx₀0)
  have hzP : P.valuation K (algebraMap O K y / algebraMap O K x₀) = exp (D P : ℤ) := by
    rw [map_div₀, (P.valuation_eq_one_iff K y).mpr hyP, hx₀P, one_div, inv_exp, neg_neg]
  have hz : ∀ Q : PrimeDivisor O,
      Q.valuation K (algebraMap O K y / algebraMap O K x₀) ≤ exp (D Q : ℤ) := by
    intro Q
    by_cases hQP : Q = P
    · rw [hQP, hzP]
    · have hyQ : Q.valuation K (algebraMap O K y) ≤ Q.valuation K (algebraMap O K x₀) := by
        by_cases hQ : Q ∈ (div K x₀).support
        · exact hy Q (Finset.mem_erase.mpr ⟨hQP, hQ⟩)
        · rw [mem_support_div K hx₀0] at hQ
          rw [(Q.valuation_eq_one_iff K x₀).mpr hQ]
          exact Q.valuation_le_one K y
      rw [map_div₀]
      exact ((div_le_one₀ (zero_lt_iff.mpr (Q.valuation_ne_zero K hx₀0))).mpr hyQ).trans
        (by rw [one_le_exp_iff]; omega)
  have hmem : ∀ x ∈ divisorIdeal K D, ∃ a : O,
      algebraMap O K a = algebraMap O K y / algebraMap O K x₀ * algebraMap O K x := by
    intro x hx
    refine mem_range_of_valuation_le_one K _ fun Q => ?_
    rw [map_mul]
    calc Q.valuation K (algebraMap O K y / algebraMap O K x₀) * Q.valuation K (algebraMap O K x)
        ≤ exp (D Q : ℤ) * exp (-(D Q : ℤ)) := mul_le_mul' (hz Q) (hx Q)
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hinj := IsFractionRing.injective O K
  choose f hf using fun x : divisorIdeal K D => hmem x x.2
  refine ⟨{ toFun := f, map_add' := fun x y => hinj ?_, map_smul' := fun c x => hinj ?_ }, ?_, ?_⟩
  · rw [map_add, hf, hf, hf, Submodule.coe_add, map_add, mul_add]
  · rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  · intro x Q
    change Q.valuation K (algebraMap O K (f x)) ≤ _
    rw [hf, map_mul]
    exact mul_le_mul' (hz Q) le_rfl
  · intro x
    change P.valuation K (algebraMap O K (f x)) = _
    rw [hf, map_mul, hzP]
end Valuation
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open Polynomial
theorem isIntegral_of_valuation_le_one (A Kp L : Type*) [CommRing A] [IsDedekindDomain A] [Field Kp]
    [Algebra A Kp] [IsFractionRing A Kp] [Field L] [Algebra Kp L] [Algebra A L] [IsScalarTower A Kp L]
    [FiniteDimensional Kp L] [Algebra.IsSeparable Kp L] [IsDedekindDomain (integralClosure A L)]
    [IsFractionRing (integralClosure A L) L] (x : L)
    (hx : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A L), v.valuation L x ≤ 1) :
    IsIntegral A x := by
  obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one L x hx
  rw [← hb]
  exact b.2
section Global
variable (P Kp L : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
  [Field Kp] [Algebra P Kp] [IsFractionRing P Kp] [Field L] [Algebra Kp L] [Algebra P L]
  [IsScalarTower P Kp L]
theorem isIntegral_of_local (x : L) (halg : IsIntegral Kp x)
    (hx : ∀ (𝔭 : Ideal P) [𝔭.IsPrime], IsDiscreteValuationRing (Localization.AtPrime 𝔭) →
      ∃ s : P, s ∉ 𝔭 ∧ IsIntegral P (algebraMap P L s * x)) : IsIntegral P x := by
  classical
  set μ := minpoly Kp x with hμ
  have hμmonic : μ.Monic := minpoly.monic halg
  have hcoeff : ∀ i, μ.coeff i ∈ Set.range (algebraMap P Kp) := by
    intro i
    by_contra hni
    have hne : ∀ a : P, algebraMap P Kp a ≠ μ.coeff i := fun a ha => hni ⟨a, ha⟩
    obtain ⟨𝔭, h𝔭, hdvr, hout⟩ := KrullIntersection.exists_dvr_localization_not_mem (μ.coeff i) hne
    obtain ⟨s, hs, hint⟩ := hx 𝔭 hdvr
    have hs0 : s ≠ 0 := fun h => hs (h ▸ 𝔭.zero_mem)
    set c := algebraMap P Kp s with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact (map_ne_zero_iff _ (IsFractionRing.injective P Kp)).2 hs0
    set y := algebraMap P L s * x with hy
    have hyc : y = algebraMap Kp L c * x := by
      rw [hy, hc, ← IsScalarTower.algebraMap_apply]
    have hxy : x = algebraMap Kp L c⁻¹ * y := by
      rw [hyc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    have hyint : IsIntegral Kp y := hint.tower_top
    set ν := minpoly Kp y with hν
    have hνmonic : ν.Monic := minpoly.monic hyint
    have hνP : ν = (minpoly P y).map (algebraMap P Kp) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' Kp hint
                                                                             
    have h1 : μ ∣ ν.scaleRoots c⁻¹ := by
      apply minpoly.dvd
      rw [hxy]
      exact scaleRoots_aeval_eq_zero (minpoly.aeval Kp y)
    have h2 : ν ∣ μ.scaleRoots c := by
      apply minpoly.dvd
      rw [hyc]
      exact scaleRoots_aeval_eq_zero (minpoly.aeval Kp x)
    have hm1 : (ν.scaleRoots c⁻¹).Monic := (monic_scaleRoots_iff _).2 hνmonic
    have hm2 : (μ.scaleRoots c).Monic := (monic_scaleRoots_iff _).2 hμmonic
    have hd1 : μ.natDegree ≤ ν.natDegree := by
      have h := natDegree_le_of_dvd h1 hm1.ne_zero
      rwa [natDegree_scaleRoots] at h
    have hd2 : ν.natDegree ≤ μ.natDegree := by
      have h := natDegree_le_of_dvd h2 hm2.ne_zero
      rwa [natDegree_scaleRoots] at h
    have heq : ν.scaleRoots c⁻¹ = μ :=
      eq_of_monic_of_dvd_of_natDegree_le hμmonic hm1 h1 (by rw [natDegree_scaleRoots]; exact hd2)
    have hci : μ.coeff i * c ^ (ν.natDegree - i) = ν.coeff i := by
      rw [← heq, coeff_scaleRoots, mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, mul_one]
    refine hout ((minpoly P y).coeff i) (s ^ (ν.natDegree - i)) (fun h => hs (h𝔭.mem_of_pow_mem _ h)) ?_
    rw [map_pow, ← hc, hci, hνP, coeff_map]
  obtain ⟨q, hq, -, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts μ).2 hcoeff) hμmonic
  refine ⟨q, hqmonic, ?_⟩
  have h := minpoly.aeval Kp x
  rw [← hμ, ← hq, aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq] at h
  exact h
theorem isIntegral_of_dvr_valuations [FiniteDimensional Kp L] [Algebra.IsSeparable Kp L] (x : L)
    (hx : ∀ (𝔭 : Ideal P) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]
      [Algebra (Localization.AtPrime 𝔭) L] [IsScalarTower P (Localization.AtPrime 𝔭) L]
      [IsDedekindDomain (integralClosure (Localization.AtPrime 𝔭) L)]
      [IsFractionRing (integralClosure (Localization.AtPrime 𝔭) L) L]
      (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (Localization.AtPrime 𝔭) L)),
      v.valuation L x ≤ 1) :
    IsIntegral P x := by
  classical
  refine isIntegral_of_local P Kp L x (Algebra.IsIntegral.isIntegral x) ?_
  intro 𝔭 h𝔭 hdvr
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap P Kp y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective P Kp)).2
      (fun h => y.2 (h ▸ 𝔭.zero_mem)))
  let algK : Algebra (Localization.AtPrime 𝔭) Kp := (IsLocalization.lift hunit).toAlgebra
  have towerK : IsScalarTower P (Localization.AtPrime 𝔭) Kp :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have fracK : IsFractionRing (Localization.AtPrime 𝔭) Kp :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ Kp
  let algL : Algebra (Localization.AtPrime 𝔭) L :=
    ((algebraMap Kp L).comp (algebraMap (Localization.AtPrime 𝔭) Kp)).toAlgebra
  have towerKL : IsScalarTower (Localization.AtPrime 𝔭) Kp L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towerL : IsScalarTower P (Localization.AtPrime 𝔭) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply P Kp L, IsScalarTower.algebraMap_apply P (Localization.AtPrime 𝔭) Kp]
      rfl
  have ded : IsDedekindDomain (integralClosure (Localization.AtPrime 𝔭) L) :=
    integralClosure.isDedekindDomain (Localization.AtPrime 𝔭) Kp L
  have frac : IsFractionRing (integralClosure (Localization.AtPrime 𝔭) L) L :=
    integralClosure.isFractionRing_of_finite_extension Kp L
  have hloc : IsIntegral (Localization.AtPrime 𝔭) x :=
    isIntegral_of_valuation_le_one (Localization.AtPrime 𝔭) Kp L x (hx 𝔭)
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔭.primeCompl x hloc
  refine ⟨m, m.2, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def] at hm
  exact hm
end Global
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open IsDedekindDomain
section Place
variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Ring.DimensionLEOne B]
  {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [Module.Finite B (integralClosure B K)]
noncomputable def resDeg (V : HeightOneSpectrum (integralClosure B K)) : ℕ :=
  (Module.length B (integralClosure B K ⧸ V.asIdeal)).toNat
omit [IsFractionRing B K] in
theorem length_closure_quotient_place_ne_top (V : HeightOneSpectrum (integralClosure B K)) :
    Module.length B (integralClosure B K ⧸ V.asIdeal) ≠ ⊤ := by
  obtain ⟨x, hxV, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.IsIntegral.under_ne_bot B V.ne_bot)
  refine Module.length_ne_top_iff.mpr (isFiniteLength_of_smul_eq_zero _ hx0 fun m => ?_)
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def]
  exact V.asIdeal.mul_mem_right t hxV
omit [IsFractionRing B K] in
theorem resDeg_cast (V : HeightOneSpectrum (integralClosure B K)) :
    (resDeg V : ℕ∞) = Module.length B (integralClosure B K ⧸ V.asIdeal) :=
  ENat.natCast_toNat (length_closure_quotient_place_ne_top V)
noncomputable def ordAt (V : HeightOneSpectrum (integralClosure B K)) (b : B) : ℕ :=
  (-(V.valuation K (algebraMap B K b)).log).toNat
theorem ordAt_eq_ordInt (V : HeightOneSpectrum (integralClosure B K)) (b : B) :
    ordAt V b = ordInt V (algebraMap B (integralClosure B K) b) := by
  rw [ordAt, ordInt, IsScalarTower.algebraMap_apply B (integralClosure B K) K,
    HeightOneSpectrum.valuation_of_algebraMap]
theorem valuation_algebraMap_le_one (V : HeightOneSpectrum (integralClosure B K)) (b : B) :
    V.valuation K (algebraMap B K b) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply B (integralClosure B K) K]
  exact V.valuation_le_one _
theorem ordAt_cast (V : HeightOneSpectrum (integralClosure B K)) (b : B) :
    (ordAt V b : ℤ) = -(V.valuation K (algebraMap B K b)).log := by
  rw [ordAt, Int.toNat_of_nonneg]
  rcases eq_or_ne (V.valuation K (algebraMap B K b)) 0 with h0 | h0
  · simp [h0]
  · have := (WithZero.log_le_iff_le_exp h0).mpr
      (by rw [WithZero.exp_zero]; exact valuation_algebraMap_le_one V b)
    omega
variable (B K)
theorem length_closure_quotient_range_ne_top : Module.length B
    (integralClosure B K ⧸ LinearMap.range (Algebra.linearMap B (integralClosure B K))) ≠ ⊤ := by
  obtain ⟨d, hd, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors B) (P := K)
    (I := Subalgebra.toSubmodule (integralClosure B K)) (Module.Finite.iff_fg.mp inferInstance)
  refine Module.length_ne_top_iff.mpr
    (isFiniteLength_of_smul_eq_zero _ (nonZeroDivisors.ne_zero hd) fun m => ?_)
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨c, hc⟩ := h t t.2
  exact ⟨c, Subtype.ext hc⟩
noncomputable def closureColength : ℕ := (Module.length B
  (integralClosure B K ⧸ LinearMap.range (Algebra.linearMap B (integralClosure B K)))).toNat
theorem closureColength_cast : (closureColength B K : ℕ∞) = Module.length B
    (integralClosure B K ⧸ LinearMap.range (Algebra.linearMap B (integralClosure B K))) :=
  ENat.natCast_toNat (length_closure_quotient_range_ne_top B K)
variable {B}
variable {K}
theorem length_quotient_span_singleton_eq_closure {b : B} (hb : b ≠ 0) :
    Module.length B (B ⧸ Ideal.span {b}) = Module.length B
      (integralClosure B K ⧸ Ideal.span {algebraMap B (integralClosure B K) b}) := by
  have hinj := closure_algebraMap_injective B K
  let ι := Algebra.linearMap B (integralClosure B K)
  let μ : integralClosure B K →ₗ[B] integralClosure B K := LinearMap.lsmul B _ b
  have hμ : Function.Injective μ := fun s t h => by
    refine mul_left_cancel₀ ((map_ne_zero_iff _ hinj).mpr hb) ?_
    simpa [μ, Algebra.smul_def] using h
  have hmap : Submodule.map ι (Ideal.span {b}) = (LinearMap.range ι).map μ := by
    ext t
    simp only [Submodule.mem_map, Ideal.mem_span_singleton', LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨ι c, ⟨c, rfl⟩, by simp [ι, μ, Algebra.smul_def, mul_comm]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c * b, ⟨c, rfl⟩, by simp [ι, μ, Algebra.smul_def, mul_comm]⟩
  have hrange : LinearMap.range μ =
      (Ideal.span {algebraMap B (integralClosure B K) b}).restrictScalars B := by
    ext t
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by simp [μ, Algebra.smul_def, mul_comm]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, by simp [μ, Algebra.smul_def, mul_comm]⟩
  have e1 := length_quotient_map ι hinj (Ideal.span {b})
  have e2 := length_quotient_map μ hμ (LinearMap.range ι)
  rw [hmap, e2, add_comm] at e1
  rw [← (Submodule.Quotient.restrictScalarsEquiv B
    (Ideal.span {algebraMap B (integralClosure B K) b})).length_eq, ← hrange]
  exact (WithTop.add_right_cancel (length_closure_quotient_range_ne_top B K) e1).symm
variable [IsLocalRing B] [Fintype (HeightOneSpectrum (integralClosure B K))]
theorem length_closure_quotient_span {y : integralClosure B K} (hy : y ≠ 0) :
    Module.length B (integralClosure B K ⧸ Ideal.span {y}) =
      ∑ V : HeightOneSpectrum (integralClosure B K), (resDeg V : ℕ∞) * (ordInt V y : ℕ∞) := by
  have := closure_isPrincipalIdealRing B K
  rw [length_quotient_span_singleton_eq_sum hy]
  exact Finset.sum_congr rfl fun V _ => by rw [resDeg_cast]
theorem length_quotient_span_singleton {b : B} (hb : b ≠ 0) :
    Module.length B (B ⧸ Ideal.span {b}) =
      ((∑ V : HeightOneSpectrum (integralClosure B K), resDeg V * ordAt V b : ℕ) : ℕ∞) := by
  rw [length_quotient_span_singleton_eq_closure (K := K) hb, length_closure_quotient_span
    ((map_ne_zero_iff _ (closure_algebraMap_injective B K)).mpr hb)]
  push_cast
  exact Finset.sum_congr rfl fun V _ => by rw [ordAt_eq_ordInt]
theorem sum_resDeg_mul_le (J : Ideal B) (c : HeightOneSpectrum (integralClosure B K) → ℕ)
    (hc : ∀ V, ∀ x ∈ J, x ≠ 0 → (c V : ℤ) ≤ -(V.valuation K (algebraMap B K x)).log) :
    ((∑ V, resDeg V * c V : ℕ) : ℕ∞) ≤ Module.length B (B ⧸ J) + closureColength B K := by
  have := closure_isPrincipalIdealRing B K
  have hinj := closure_algebraMap_injective B K
  obtain ⟨y, hy0, hy⟩ := exists_ordInt_eq c
  have hJy : Submodule.map (Algebra.linearMap B (integralClosure B K)) J ≤
      (Ideal.span {y}).restrictScalars B := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · refine dvd_of_forall_ordInt_le ((map_ne_zero_iff _ hinj).mpr hx0) hy0 fun V => ?_
      have h := hc V x hx hx0
      rw [← ordAt_cast, Nat.cast_le] at h
      rwa [hy V, Algebra.linearMap_apply, ← ordAt_eq_ordInt]
  calc ((∑ V, resDeg V * c V : ℕ) : ℕ∞)
      = Module.length B (integralClosure B K ⧸ Ideal.span {y}) := by
        rw [length_closure_quotient_span hy0]
        push_cast
        exact Finset.sum_congr rfl fun V _ => by rw [hy V]
    _ = Module.length B (integralClosure B K ⧸ (Ideal.span {y}).restrictScalars B) :=
        (Submodule.Quotient.restrictScalarsEquiv B _).length_eq.symm
    _ ≤ Module.length B
          (integralClosure B K ⧸ Submodule.map (Algebra.linearMap B (integralClosure B K)) J) :=
        Module.length_le_of_surjective (Submodule.factor hJy) (Submodule.factor_surjective hJy)
    _ = Module.length B (B ⧸ J) + closureColength B K := by
        rw [length_quotient_map _ hinj J, closureColength_cast]
end Place
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Sec
noncomputable section
open scoped Classical BigOperators
open RCN072 MvPolynomial
variable {E : Type} [Field E]
local notation "Poly" => MvPolynomial (Fin 3) E
theorem pencilFinite : PencilFinite E := by
  intro g D ℓ hg hD
  have hgp : (Ideal.span ({g} : Set Poly)).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have h1 : (1 : ℕ∞) ≤ (Ideal.span ({g} : Set Poly)).height := by
    have hbot : (⊥ : Ideal Poly) < Ideal.span {g} :=
      bot_lt_iff_ne_bot.mpr (fun h => hg.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at h
  have key : ∀ a : E, ∀ P ∈ RCN072.componentFamily E g (ℓ - C a), D ∈ P →
      P ∈ (Ideal.span ({g, D} : Set Poly)).minimalPrimes := by
    intro a P hP hDP
    have hPp : P.IsPrime := RCN072.component_isPrime E g _ P hP
    have hgP : g ∈ P := RCN072.cutIdeal_le_component E g _ P hP (Ideal.subset_span (Set.mem_insert g _))
    have hle : Ideal.span ({g, D} : Set Poly) ≤ P := by
      apply Ideal.span_le.mpr
      rintro x (rfl | rfl)
      exacts [hgP, hDP]
    obtain ⟨P', hP', hP'P⟩ := Ideal.exists_minimalPrimes_le hle
    have hP'p : P'.IsPrime := hP'.1.1
    have hlt : Ideal.span ({g} : Set Poly) < P' := by
      refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr
        (hP'.1.2 (Ideal.subset_span (Set.mem_insert g _)))) ?_
      intro heq
      have hDg : D ∈ Ideal.span ({g} : Set Poly) :=
        heq ▸ hP'.1.2 (Ideal.subset_span (Set.mem_insert_of_mem g rfl))
      exact hD (Ideal.mem_span_singleton.mp hDg)
    have h2 : (2 : ℕ∞) ≤ P'.height :=
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (Ideal.span ({g} : Set Poly)).height + 1 := by gcongr
        _ ≤ P'.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have heq : P' = P := by
      by_contra hne
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hP'P hne)
      have h4 : (3 : ℕ∞) ≤ 2 :=
        calc (3 : ℕ∞) = 2 + 1 := by norm_num
          _ ≤ P'.height + 1 := by gcongr
          _ ≤ P.height := h3
          _ ≤ 2 := RCN072.component_height_le_two E g _ P hP
      norm_num at h4
    exact heq ▸ hP'
  refine Set.Finite.subset ((Ideal.span ({g, D} : Set Poly)).finite_minimalPrimes_of_isNoetherianRing.biUnion
    (t := fun P => {a : E | P.IsPrime ∧ ℓ - C a ∈ P}) ?_) ?_
  · intro P _
    apply Set.Subsingleton.finite
    rintro a ⟨hp, ha⟩ a' ⟨-, ha'⟩
    by_contra hne
    have hmem : (C (a' - a) : Poly) ∈ P := by
      have h := P.sub_mem ha ha'
      rwa [sub_sub_sub_cancel_left, ← map_sub] at h
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map C))
  · rintro a ⟨P, hP, hDP⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨P, key a P hP hDP, RCN072.component_isPrime E g _ P hP,
      RCN072.cutIdeal_le_component E g _ P hP (Ideal.subset_span (Set.mem_insert_of_mem g rfl))⟩
theorem localGen_of_graph (g q : Poly) (i : Fin 3) (c : E) (hc : c ≠ 0) (hq : i ∉ q.vars)
    (P : Ideal Poly) (hP : P ∈ RCN072.componentFamily E g (C c * MvPolynomial.X i - q)) (D : Derivation E Poly Poly)
    (hDs : D (C c * MvPolynomial.X i - q) = 0) (hDg : D g ∉ P) : LocalGen g (C c * MvPolynomial.X i - q) P := by
  set s : Poly := C c * MvPolynomial.X i - q with hs
  have hmin : P ∈ (Ideal.span ({g, s} : Set Poly)).minimalPrimes := (RCN072.mem_componentFamily E g s P).mp hP
  have hPp : P.IsPrime := hmin.1.1
  have hgP : g ∈ P := hmin.1.2 (Ideal.subset_span (Set.mem_insert g _))
  have hsP : s ∈ P := hmin.1.2 (Ideal.subset_span (Set.mem_insert_of_mem g rfl))
  let r : Poly := C c⁻¹ * q
  let φ : Poly →ₐ[E] Poly := aeval (Function.update MvPolynomial.X i r)
  have hφX : ∀ m, m ≠ i → φ (MvPolynomial.X m) = MvPolynomial.X m := fun m hm => by
    simp only [φ, aeval_X, Function.update_of_ne hm]
  have hφi : φ (MvPolynomial.X i) = r := by simp only [φ, aeval_X, Function.update_self]
  have hfix : ∀ u : Poly, i ∉ u.vars → φ u = u := fun u hu =>
    hom_congr_vars (f₁ := (φ : Poly →+* Poly)) (f₂ := RingHom.id Poly)
      (by ext x; simp [φ]) (fun m hm _ => hφX m (fun h => hu (h ▸ hm))) rfl
  have hfree : ∀ u : Poly, i ∉ (φ u).vars := by
    intro u hmem
    have he : φ u = bind₁ (Function.update MvPolynomial.X i r) u := by rw [← aeval_eq_bind₁]
    rw [he] at hmem
    obtain ⟨m, -, hm⟩ := mem_vars_bind₁ _ _ hmem
    by_cases h : m = i
    · subst h
      rw [Function.update_self] at hm
      rcases Finset.mem_union.mp (vars_mul _ _ hm) with h1 | h1
      · rw [vars_C] at h1
        exact absurd h1 (Finset.notMem_empty _)
      · exact hq h1
    · rw [Function.update_of_ne h, vars_X, Finset.mem_singleton] at hm
      exact h hm.symm
  have hcc : (C c : Poly) * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  have hφs : φ s = 0 := by
    rw [hs, map_sub, map_mul, hfix q hq, hφi, algHom_C]
    change C c * (C c⁻¹ * q) - q = 0
    rw [← mul_assoc, hcc, one_mul, sub_self]
  have hmod : ∀ u : Poly, u - φ u ∈ Ideal.span ({s} : Set Poly) := by
    have hcomp : (Ideal.Quotient.mk (Ideal.span ({s} : Set Poly))).comp (φ : Poly →+* Poly) =
        Ideal.Quotient.mk (Ideal.span ({s} : Set Poly)) := by
      apply ringHom_ext
      · intro x
        simp [φ]
      · intro m
        by_cases h : m = i
        · subst h
          rw [RingHom.comp_apply, RingHom.coe_coe, hφi, eq_comm, Ideal.Quotient.eq]
          have he : MvPolynomial.X m - r = C c⁻¹ * s := by
            have h1 : C c⁻¹ * (C c * MvPolynomial.X m - q) =
                C c * C c⁻¹ * MvPolynomial.X m - C c⁻¹ * q := by ring
            rw [h1, hcc, one_mul]
          rw [he]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
        · rw [RingHom.comp_apply, RingHom.coe_coe, hφX m h]
    intro u
    rw [← Ideal.Quotient.eq, ← RingHom.congr_fun hcomp u]
    rfl
  have hspanP : Ideal.span ({s} : Set Poly) ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hsP
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (hmod g)
  have hg₀P : φ g ∈ P := by
    have h := P.sub_mem hgP (hspanP (hmod g))
    rwa [sub_sub_cancel] at h
  have hDe : D g = D (φ g) + s * D e := by
    have hg : g = φ g + s * e := by rw [← he]; ring
    conv_lhs => rw [hg]
    rw [map_add, Derivation.leibniz, hDs, smul_zero, add_zero, smul_eq_mul]
  have hg₀ : φ g ≠ 0 := by
    intro h0
    apply hDg
    rw [hDe, h0, map_zero, zero_add]
    exact P.mul_mem_right _ hsP
  obtain ⟨π, hπirr, ⟨h, hh⟩, hπP⟩ : ∃ π, Irreducible π ∧ π ∣ φ g ∧ π ∈ P := by
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hg₀
    have hmem : (UniqueFactorizationMonoid.factors (φ g)).prod ∈ P := by
      rw [(Units.eq_mul_inv_iff_mul_eq u).mpr hu]
      exact P.mul_mem_right _ hg₀P
    obtain ⟨π, hπ, hπP⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hPp _).mp hmem
    exact ⟨π, UniqueFactorizationMonoid.irreducible_of_factor π hπ,
      UniqueFactorizationMonoid.dvd_of_mem_factors hπ, hπP⟩
  have hφπ : φ π = π := by
    apply hfix
    rw [mem_vars_iff_degreeOf_ne_zero, not_not]
    have h1 := RCN137.coordinate_degree_le_of_dvd i π (φ g) ⟨h, hh⟩ hg₀
    have h2 : (φ g).degreeOf i = 0 := by
      have h3 := hfree g
      rwa [mem_vars_iff_degreeOf_ne_zero, not_not] at h3
    omega
  have hπp : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
  have hIP : Ideal.span ({π, s} : Set Poly) ≤ P := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    exacts [hπP, hsP]
  have hstep : ∀ u : Poly, π ∣ φ u → u ∈ Ideal.span ({π, s} : Set Poly) := by
    rintro u ⟨t, ht⟩
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hmod u)
    exact Ideal.mem_span_pair.mpr ⟨t, d, by rw [mul_comm t, ← ht, mul_comm d, ← hd]; ring⟩
  have hI : (Ideal.span ({π, s} : Set Poly)).IsPrime := by
    refine ⟨fun htop => hPp.ne_top (top_le_iff.mp (htop ▸ hIP)), fun {u v} huv => ?_⟩
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp huv
    have hdvd : π ∣ φ u * φ v := by
      rw [← map_mul, ← hαβ, map_add, map_mul, map_mul, hφπ, hφs, mul_zero, add_zero]
      exact dvd_mul_left _ _
    exact (hπp.dvd_or_dvd hdvd).imp (hstep u) (hstep v)
  have hle : Ideal.span ({g, s} : Set Poly) ≤ Ideal.span ({π, s} : Set Poly) := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_pair.mpr ⟨h, e, by rw [mul_comm h, ← hh, mul_comm e, ← he]; ring⟩
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPI : P ≤ Ideal.span ({π, s} : Set Poly) := hmin.2 ⟨hI, hle⟩ hIP
  refine ⟨h, fun hhP => hDg ?_, fun x hx => ?_⟩
  · rw [hDe, hh, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.add_mem (P.mul_mem_right _ hπP) (P.mul_mem_right _ hhP)) (P.mul_mem_right _ hsP)
  · obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hPI hx)
    refine Ideal.mem_span_pair.mpr ⟨α, β * h - α * e, ?_⟩
    have hg : g = π * h + s * e := by rw [← hh, ← he]; ring
    rw [← hαβ, hg]
    ring
theorem linearForm_eq (b : Fin 3 → E) (a : E) (i : Fin 3) :
    linearForm b - C a =
      C (b i) * MvPolynomial.X i - (C a - ∑ m ∈ Finset.univ.erase i, C (b m) * (MvPolynomial.X m : Poly)) := by
  rw [linearForm, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  ring
theorem pderiv_linearForm (b : Fin 3 → E) (k : Fin 3) :
    pderiv k (linearForm b) = (C (b k) : Poly) := by
  rw [linearForm, map_sum, Finset.sum_eq_single k]
  · rw [pderiv_C_mul, pderiv_X_self, mul_one]
  · intro m _ hm
    rw [pderiv_C_mul, pderiv_X_of_ne hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h
theorem sectionLocalGen : SectionLocalGen E := by
  intro g b a i k hbi hik P hP hJ
  have hq : i ∉ (C a - ∑ m ∈ Finset.univ.erase i, C (b m) * (MvPolynomial.X m : Poly)).vars := by
    intro hmem
    rcases Finset.mem_union.mp (vars_sub_subset _ hmem) with h1 | h1
    · rw [vars_C] at h1
      exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨m, hm, hmi⟩ := Finset.mem_biUnion.mp (vars_sum_subset _ _ h1)
      rcases Finset.mem_union.mp (vars_mul _ _ hmi) with h2 | h2
      · rw [vars_C] at h2
        exact absurd h2 (Finset.notMem_empty _)
      · rw [vars_X, Finset.mem_singleton] at h2
        exact (Finset.mem_erase.mp hm).1 h2.symm
  let D : Derivation E Poly Poly := b i • pderiv k - b k • pderiv i
  have hD : ∀ u : Poly, D u = C (b i) * pderiv k u - C (b k) * pderiv i u := fun u => by
    simp only [D, Derivation.sub_apply, Derivation.smul_apply, smul_eq_C_mul]
  rw [linearForm_eq b a i] at hP ⊢
  refine localGen_of_graph g _ i (b i) hbi hq P hP D ?_ (by rw [hD]; exact hJ)
  rw [← linearForm_eq b a i, hD, map_sub, map_sub, pderiv_C, pderiv_C, pderiv_linearForm,
    pderiv_linearForm, sub_zero, sub_zero, mul_comm, sub_self]
theorem goodPencil : GoodPencil E := by
  intro g D b i k hg hD hbi hik hJ
  have hgp : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hg
  have hDJ : ¬g ∣ D * linearMinor b i k g := fun h => (hgp.dvd_or_dvd h).elim hD hJ
  have hsub : {a : E | g ∣ linearForm b - C a}.Subsingleton := by
    intro a ha a' ha'
    by_contra hne
    have hdvd : g ∣ (C (a' - a) : Poly) := by
      have h := dvd_sub ha ha'
      rwa [sub_sub_sub_cancel_left, ← map_sub] at h
    exact hg.not_isUnit (isUnit_of_dvd_unit hdvd
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map C))
  refine (hsub.finite.union
    (pencilFinite g (D * linearMinor b i k g) (linearForm b) hg hDJ)).subset ?_
  · intro a ha
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    refine ha ⟨hnot.1, fun P hP => ?_⟩
    have hDJP : D * linearMinor b i k g ∉ P := fun h => hnot.2 ⟨P, hP, h⟩
    exact ⟨fun h => hDJP (P.mul_mem_right _ h),
      sectionLocalGen g b a i k hbi hik P hP (fun h => hDJP (P.mul_mem_left _ h))⟩
theorem linearMinor_noR (b : Fin 3 → E) (i : Fin 3) (hb : b 1 = 0) (g : Poly) :
    linearMinor b i 1 g = C (b i) * pderiv 1 g := by
  rw [linearMinor, hb, C_0, zero_mul, sub_zero]
theorem not_dvd_linearMinor_noR (b : Fin 3 → E) (i : Fin 3) (hb : b 1 = 0) (hbi : b i ≠ 0) (g : Poly)
    (hg : ¬g ∣ pderiv 1 g) : ¬g ∣ linearMinor b i 1 g := by
  rw [linearMinor_noR b i hb]
  exact fun h => hg (((isUnit_iff_ne_zero.mpr hbi).map (C : E →+* Poly)).dvd_mul_left.mp h)
theorem finite_not_good (gs : Finset Poly) (D : Poly) (b : Fin 3 → E) (i k : Fin 3) (hbi : b i ≠ 0)
    (hik : i ≠ k) (hgs : ∀ g ∈ gs, Irreducible g ∧ ¬g ∣ D ∧ ¬g ∣ linearMinor b i k g) :
    {a : E | ∃ g ∈ gs, ¬GoodSection g (linearForm b - C a) D}.Finite := by
  have he : {a : E | ∃ g ∈ gs, ¬GoodSection g (linearForm b - C a) D} =
      ⋃ g ∈ gs, {a : E | ¬GoodSection g (linearForm b - C a) D} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [he]
  exact gs.finite_toSet.biUnion fun g hg =>
    goodPencil g D b i k (hgs g hg).1 (hgs g hg).2.1 hbi hik (hgs g hg).2.2
theorem exists_good_section [Infinite E] (gs : Finset Poly) (D : Poly) (b : Fin 3 → E) (i k : Fin 3)
    (hbi : b i ≠ 0) (hik : i ≠ k)
    (hgs : ∀ g ∈ gs, Irreducible g ∧ ¬g ∣ D ∧ ¬g ∣ linearMinor b i k g) (bad : Set E)
    (hbad : bad.Finite) : ∃ a : E, a ∉ bad ∧ ∀ g ∈ gs, GoodSection g (linearForm b - C a) D := by
  obtain ⟨a, ha⟩ := ((finite_not_good gs D b i k hbi hik hgs).union hbad).infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at ha
  exact ⟨a, ha.2, fun g hg => by_contra fun hn => ha.1 ⟨g, hg, hn⟩⟩
theorem not_dvd_pderiv_self (i : Fin 3) (g : Poly) (hd : pderiv i g ≠ 0) : ¬g ∣ pderiv i g := by
  intro h
  have hsupp : ∀ d ∈ (pderiv i g).support, d i + 1 ≤ g.degreeOf i := by
    intro d hd'
    have hmem : d + Finsupp.single i 1 ∈ g.support := by
      rw [MvPolynomial.mem_support_iff] at hd' ⊢
      intro h0
      exact hd' (by rw [coeff_pderiv, h0, zero_mul])
    have h1 := degreeOf_le_iff.mp (le_refl (g.degreeOf i)) _ hmem
    rwa [Finsupp.add_apply, Finsupp.single_eq_same] at h1
  obtain ⟨d, hd'⟩ := ne_zero_iff.mp hd
  have h1 := RCN137.coordinate_degree_le_of_dvd i g (pderiv i g) h hd
  have h2 : (pderiv i g).degreeOf i ≤ g.degreeOf i - 1 :=
    degreeOf_le_iff.mpr fun e he => by have := hsupp e he; omega
  have h3 := hsupp d (MvPolynomial.mem_support_iff.mpr hd')
  omega
theorem linearForm_sub_C_inFlag (W : RCN095.FlagDegree) (b : Fin 3 → E) (a : E)
    (h0 : b 0 ≠ 0 → 1 ≤ W.yz + W.all) (h1 : b 1 ≠ 0 → 1 ≤ W.all)
    (h2 : b 2 ≠ 0 → 1 ≤ W.zOnly + W.yz + W.all) : RCN095.PolynomialInFlag W (linearForm b - C a) := by
  intro d hd
  by_cases hd0 : d = 0
  · rw [hd0]
    exact RCN095.inFlag_zero W
  have hex : ∃ m, b m ≠ 0 ∧ d = Finsupp.single m 1 := by
    by_contra hne
    rw [not_exists] at hne
    apply MvPolynomial.mem_support_iff.mp hd
    have h0d : ¬(0 = d) := Ne.symm hd0
    rw [linearForm, coeff_sub, coeff_sum, coeff_C]
    simp only [h0d, ↓reduceIte, sub_zero]
    apply Finset.sum_eq_zero
    intro m _
    rw [coeff_C_mul, coeff_X]
    by_cases hb : b m = 0
    · rw [hb, zero_mul]
    · have hmd : ¬(Finsupp.single m 1 = d) := fun h => hne m ⟨hb, h.symm⟩
      simp only [hmd, ↓reduceIte, mul_zero]
  obtain ⟨m, hb, rfl⟩ := hex
  have hval : ∀ j : Fin 3, (Finsupp.single m (1 : ℕ)) j = if m = j then 1 else 0 := fun j =>
    Finsupp.single_apply
  rw [RCN095.InFlag, hval 0, hval 1, hval 2]
  fin_cases m
  · have := h0 hb
    simp
    omega
  · have := h1 hb
    simp
    omega
  · have := h2 hb
    simp
    omega
theorem val_section_of_localGen {L : Type} [Field L] (g s : Poly) (P : Ideal Poly)
    (hgen : LocalGen g s P) (hsP : s ∈ P) (ev : Poly →+* L) (hg : ev g = 0)
    (hfrac : ∀ y : L, ∃ a b : Poly, ev b ≠ 0 ∧ y * ev b = ev a)
    (v : Valuation L (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hle : ∀ A : Poly, v (ev A) ≤ 1) (hP : ∀ A : Poly, v (ev A) < 1 ↔ A ∈ P) :
    v (ev s) = WithZero.exp (-1) := by
  obtain ⟨h, hh, hgen⟩ := hgen
  have hvh : v (ev h) = 1 := le_antisymm (hle h) (not_lt.mp fun hlt => hh ((hP h).mp hlt))
  have hevh : ev h ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvh
    exact zero_ne_one hvh
  have hlog : ∀ A : Poly, ev A ≠ 0 → (v (ev A)).log ≤ 0 := fun A hA => by
    have h1 := (WithZero.log_le_log (v.ne_zero_iff.mpr hA) one_ne_zero).mpr (hle A)
    rwa [WithZero.log_one] at h1
  obtain ⟨y, hy⟩ := hv (WithZero.exp (-1))
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  obtain ⟨a, b, hb, hab⟩ := hfrac y
  have ha : ev a ≠ 0 := by
    rw [← hab]
    exact mul_ne_zero hy0 hb
  have hs0 : ev s ≠ 0 := by
    intro h0
    have haP : a ∈ P := by
      rw [← hP, ← hab, map_mul, hy]
      calc WithZero.exp (-1) * v (ev b) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (hle b)
        _ < 1 := by
          rw [mul_one, ← WithZero.exp_zero]
          exact WithZero.exp_lt_exp.mpr (by norm_num)
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hgen a haP)
    have he := congrArg ev hαβ
    rw [map_add, map_mul, map_mul, map_mul, hg, h0, mul_zero, mul_zero, add_zero] at he
    exact mul_ne_zero hevh ha he.symm
  have hvs : v (ev s) ≠ 0 := v.ne_zero_iff.mpr hs0
  have hτ1 : (v (ev s)).log ≤ -1 := by
    have h1 : WithZero.exp (v (ev s)).log < WithZero.exp 0 := by
      rw [WithZero.exp_log hvs, WithZero.exp_zero]
      exact (hP s).mpr hsP
    have h2 := WithZero.exp_lt_exp.mp h1
    omega
  have key : ∀ n : ℕ, ∀ A : Poly, ev A ≠ 0 → -(n : ℤ) ≤ (v (ev A)).log →
      ∃ k : ℕ, (v (ev A)).log = k * (v (ev s)).log := by
    intro n
    induction n with
    | zero =>
      intro A hA hn
      refine ⟨0, ?_⟩
      have h1 := hlog A hA
      rw [Nat.cast_zero, neg_zero] at hn
      rw [Nat.cast_zero, zero_mul]
      omega
    | succ n ih =>
      intro A hA hn
      by_cases hAP : A ∈ P
      · obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hgen A hAP)
        have he := congrArg ev hαβ
        rw [map_add, map_mul, map_mul, map_mul, hg, mul_zero, zero_add] at he
        have hβ : ev β ≠ 0 := fun h0 => by
          rw [h0, zero_mul] at he
          exact mul_ne_zero hevh hA he.symm
        have hl := congrArg (fun z => (v z).log) he
        simp only [map_mul, hvh, one_mul] at hl
        rw [WithZero.log_mul (v.ne_zero_iff.mpr hβ) hvs] at hl
        obtain ⟨k, hk⟩ := ih β hβ (by push_cast at hn; omega)
        refine ⟨k + 1, ?_⟩
        rw [← hl, hk]
        push_cast
        ring
      · have h1 : v (ev A) = 1 := le_antisymm (hle A) (not_lt.mp fun hlt => hAP ((hP A).mp hlt))
        exact ⟨0, by rw [h1, WithZero.log_one, Nat.cast_zero, zero_mul]⟩
  have hpow : ∀ A : Poly, ev A ≠ 0 → ∃ k : ℕ, (v (ev A)).log = k * (v (ev s)).log := fun A hA =>
    key (-(v (ev A)).log).toNat A hA (by have h1 := hlog A hA; omega)
  obtain ⟨ka, hka⟩ := hpow a ha
  obtain ⟨kb, hkb⟩ := hpow b hb
  have hl := congrArg (fun z => (v z).log) hab
  simp only [map_mul] at hl
  rw [WithZero.log_mul (v.ne_zero_iff.mpr hy0) (v.ne_zero_iff.mpr hb), hy, WithZero.log_exp, hka, hkb] at hl
  have hunit : IsUnit (v (ev s)).log :=
    IsUnit.of_mul_eq_one ((kb : ℤ) - ka) (by linear_combination hl)
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · omega
  · rw [← WithZero.exp_log hvs, h1]
end
end Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN064 RCN072 RCN084 RCN095 RCN135 RCN136 RCN199 RCN204 RCN207 RCN208 RCN264
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN341 RCN344
open BD LF _Q7 OT YE AVZ AGD
open MovingFiberThreeSources6811 (direction weight)
theorem val_le_exp_pole {L : Type} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : L) : v x ≤ WithZero.exp (RCN187.poleOrder v x) := by
  have hn : max 1 (v x) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
  rw [RCN187.poleOrder, ← RCN187.log_max_one, WithZero.exp_log hn]
  exact le_max_right _ _
theorem field_eval {E : Type} [Field E] (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (B : MvPolynomial (Fin 3) E) :
    MvPolynomial.eval₂Hom (algebraMap E (RCN002.CoordinateField E P)) (coordinate E P) B = RCN002.coordinateEvaluation E P B := by
  rw [RCN002.coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
section Curve
variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E
omit [IsAlgClosed E] in
theorem poleOrder_level_le (P : Ideal Poly) [P.IsPrime] (H G Q A : Poly)
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A) (c : E) (nu : RCN026.Place_p19 E (RCN002.CoordinateField E P)) :
    RCN187.poleOrder nu.val (movingValue P H G Q A - algebraMap E (RCN002.CoordinateField E P) c) ≤ KS P H G nu := by
  have hK : (0 : ℤ) ≤ KS P H G nu := by
    dsimp [KS, RCN187.poleOrder]
    positivity
  have hc := NP E (RCN002.CoordinateField E P) nu
  have hQv : nu.val (RCN002.coordinateEvaluation E P Q) ≤ WithZero.exp (KS P H G nu) := by
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E (RCN002.CoordinateField E P)) hc (coordinate E P) (2 • unitAllFlag) Q hQ
    rw [field_eval, RCN204.flagPole_nsmul, RCN204.flagPole_unitAll] at h
    refine h.trans (WithZero.exp_le_exp.mpr ?_)
    rw [Nat.cast_ofNat]
    exact le_max_left _ _
  have hAv : nu.val (RCN002.coordinateEvaluation E P A * RCN002.coordinateEvaluation E P G / RCN002.coordinateEvaluation E P H) ≤ WithZero.exp (KS P H G nu) := by
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E (RCN002.CoordinateField E P)) hc (coordinate E P) unitYZFlag A hA
    rw [field_eval, RCN204.flagPole_unitYZ] at h
    have hr := val_le_exp_pole nu.val (movingRatio P H G)
    rw [mul_div_assoc, map_mul]
    refine (mul_le_mul' h hr).trans ?_
    rw [← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (le_max_right _ _)
  have hcv : nu.val (algebraMap E (RCN002.CoordinateField E P) c) ≤ WithZero.exp (KS P H G nu) :=
    (hc c).trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr hK)
  apply ActualFirstCutPole6807.pole_le_of_value_le nu.val _ _ hK
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ hcv)
  exact (Valuation.map_add _ _ _).trans (max_le hQv hAv)
theorem levelZeros_le (P : Ideal Poly) [P.IsPrime] (base : RCN341.SeparableLiteralCoordinate P) (H G Q A : Poly)
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A) (c : E) (cost : ℕ)
    (hcost : ∀ V : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E P)), (∑ nu ∈ V, KS P H G nu) ≤ (cost : ℤ))
    (V : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E P))) : levelZeros P H G Q A c V ≤ (cost : ℤ) := by
  by_cases hx0 : movingValue P H G Q A - algebraMap E (RCN002.CoordinateField E P) c = 0
  · simp [levelZeros, hx0, RCN026.zeroOrder_p19, RCN026.order_p19]
  let _ := RCN006.polynomialBaseAlgebra E P base.index
  let _ := RCN005.rationalBaseAlgebra E P base.index base.transcendental
  let _ := RCN006.polynomialBaseScalarTower E P base.index
  let _ := RCN006.polynomialRationalScalarTower E P base.index base.transcendental
  let _ := RCN005.rationalBaseScalarTower E P base.index base.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E P) := base.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E P) := base.separable
  set x := movingValue P H G Q A - algebraMap E (RCN002.CoordinateField E P) c with hx
  calc
    levelZeros P H G Q A c V = ∑ nu ∈ V, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E P) nu x := rfl
    _ ≤ ∑ nu ∈ V ∪ RCN026.placesFor_p19 E (RCN002.CoordinateField E P) x hx0, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E P) nu x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun nu _ _ => RCN026.AUU E (RCN002.CoordinateField E P) nu x)
    _ = ∑ nu ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E P) x hx0, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E P) nu x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro nu _ hnot
      have ho : RCN026.order_p19 E (RCN002.CoordinateField E P) nu x = 0 := by
        by_contra hn
        exact hnot (RCN026.ALB E (RCN002.CoordinateField E P) x hx0 nu hn)
      simp only [RCN026.zeroOrder_p19, ho, max_self]
    _ = ∑ nu ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E P) x hx0, RCN346.poleOrder_p19 E (RCN002.CoordinateField E P) nu x :=
      RCN026.AJO E (RCN002.CoordinateField E P) x hx0
    _ ≤ ∑ nu ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E P) x hx0, KS P H G nu :=
      Finset.sum_le_sum (fun nu _ => poleOrder_level_le P H G Q A hQ hA c nu)
    _ ≤ (cost : ℤ) := hcost _
end Curve
theorem carrier_ne_zero {K E : Type} [Field K] [Field E] (eta : GenericField K →+* E)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) : BXI eta F ≠ 0 :=
  RCN136.surfaceMap_ne_zero (codeMap eta) (DTI eta) F hF
theorem frozenH_mem {K E : Type} [Field K] [Field E] (eta : GenericField K →+* E)
    (F : MvPolynomial (Fin 4) K) :
    frozenH eta F ∈ Ideal.span
      ({BXI eta F, MvPolynomial.pderiv (1 : Fin 3) (BXI eta F)} : Set (MvPolynomial (Fin 3) E)) := by
  apply Ideal.subset_span
  apply Set.mem_insert_of_mem
  rw [Set.mem_singleton_iff, BXI, RCN267.surfaceMap_pderiv_R]
  rfl
section Budget
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
local notation "Poly" => MvPolynomial (Fin 3) E
theorem exists_cost (eta : GenericField K →+* E) (F : MvPolynomial (Fin 4) K) (SZ : MovingFiberThreeSources6811.Source F)
    (W : FlagDegree) (s : Poly) (scale z u v : ℕ) (hF : F ≠ 0) (hs : RCN095.PolynomialInFlag W s)
    (B : SliceBudgets (BXI eta F) s (frozenH eta F) W)
    (hbound : ∀ Q A : Poly, (2 : Poly) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN eta F SZ Q A scale z u v)
    (active : Finset (ANR (BXI eta F) s (frozenH eta F)))
    (hlead : ∀ a ∈ active, SZ.leading (codeMap eta) ∉ a.2.1) :
    ∃ cost : ANR (BXI eta F) s (frozenH eta F) → ℕ,
      (∀ a ∈ active, ∀ V : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E a.2.1)),
        (∑ nu ∈ V, KS a.2.1 (frozenH eta F) (frozenG eta F) nu) ≤ (cost a : ℤ)) ∧
      scale * (∑ a ∈ active, cost a) ≤ W.zOnly * z + W.yz * u + W.all * v := by
  obtain ⟨moving, -, hsum⟩ := APJ.EFP eta F SZ (BXI eta F) s (carrier_ne_zero eta F hF) (dvd_refl _)
    (frozenH_mem eta F) W hs B active hlead scale z u v hbound
  refine ⟨fun a => if h : a ∈ active then (moving ⟨a, h⟩).movingCost else 0, ?_, ?_⟩
  · intro a ha V
    simpa only [ha, ↓reduceDIte] using (moving ⟨a, ha⟩).movingPole V
  · rw [← Finset.sum_coe_sort active]
    simpa only [Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta] using hsum
theorem sectionZeroBudget : SectionZeroBudget K E := by
  intro eta F SZ p W s scale z u v hF hp hs hdeg hmix hbound Q A c hQ hA active hlead V
  obtain ⟨B⟩ := EFX (BXI eta F) s (frozenH eta F) p W (carrier_ne_zero eta F hF) hp hs
    2130706433 hdeg hmix
  obtain ⟨cost, hcost, hsum⟩ := exists_cost eta F SZ W s scale z u v hF hs B hbound active hlead
  have hle : (∑ a ∈ active, levelZeros a.2.1 (frozenH eta F) (frozenG eta F) Q A c (V a)) ≤
      ∑ a ∈ active, (cost a : ℤ) :=
    Finset.sum_le_sum fun a ha => levelZeros_le a.2.1 (B.base a.1 a.2) _ _ Q A hQ hA c
      (cost a) (hcost a ha) (V a)
  calc
    (scale : ℤ) * (∑ a ∈ active, levelZeros a.2.1 (frozenH eta F) (frozenG eta F) Q A c (V a)) ≤
        (scale : ℤ) * ∑ a ∈ active, (cost a : ℤ) :=
      mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg scale)
    _ ≤ ((W.zOnly * z + W.yz * u + W.all * v : ℕ) : ℤ) := by exact_mod_cast hsum
end Budget
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN313
variable {K : Type} [Field K]
theorem hdefer_of_tame_unit (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (v : Valuation (SliceField F₀) ℤᵐ⁰) (hvn : ∃ x, v x = exp (-1))
    (z : SliceField F₀)
    (hkv : ∀ a ∈ unitField F₀ z, a ≠ 0 → v a = 1)
    (s b s₀ : SliceField F₀) (hs1 : v s ≤ 1) (hst : Transcendental (unitField F₀ z) s)
    (hs₀ : Tame v (HFree6812.sliceDerivation F F₀ hdvd) (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd z))) s₀)
    (hss₀ : v (s - s₀) < 1)
    (hgen : ∀ E : Subfield (SliceField F₀),
      (∀ x ∈ unitField F₀ z, x ∈ E) → s ∈ E → b ∈ E → ∀ x, x ∈ E)
    (P : Polynomial (SliceField F₀)) (hP0 : P ≠ 0) (hPb : P.eval b = 0)
    (hPc : ∀ n, P.coeff n ∈ IntermediateField.adjoin (unitField F₀ z) {s})
    (N : ℕ) (hPN : P.natDegree ≤ N) (hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0) :
    (∃ C, CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C) ∧
      HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd) (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd z))) := by
  classical
  set Dd := HFree6812.sliceDerivation F F₀ hdvd with hDd
  set X0 := sliceProj F₀ (MvPolynomial.X 0) with hX0
  set k := unitField F₀ z with hk
  set Λ0 := vpole v (Dd z) with hΛ0
  have hkle : ∀ a ∈ k, v a ≤ 1 := fun a ha => by
    by_cases h0 : a = 0
    · rw [h0, v.map_zero]; exact zero_le
    · exact (hkv a ha h0).le
  have hΛ0nn : 0 ≤ Λ0 := vpole_nonneg _ _
  have hzk : z ∈ k := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have hX0k : X0 ∈ k :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hkT : ∀ a ∈ k, Tame v Dd (exp Λ0) a := by
    intro a ha
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · rw [ha]; exact ⟨hkle _ hzk, HFree6812.v_le_exp_vpole v _⟩
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        refine ⟨hkle _ hX0k, ?_⟩
        show v (Dd X0) ≤ _
        rw [hDd, HFree6812.sliceDerivation_X0 F F₀ hdvd hH, v.map_one, ← exp_zero, exp_le_exp]
        exact hΛ0nn
    | algebraMap r =>
      refine ⟨hkle _ (k.algebraMap_mem r), ?_⟩
      rw [Derivation.map_algebraMap, v.map_zero]; exact zero_le
    | add a c _ _ ha hc => exact (tameSubring v Dd _).add_mem ha hc
    | mul a c _ _ ha hc => exact (tameSubring v Dd _).mul_mem ha hc
    | inv a hak ha =>
      by_cases h0 : a = 0
      · rw [h0, inv_zero]; exact (tameSubring v Dd _).zero_mem
      · exact tame_inv v Dd _ a ha (hkv a hak h0)
  have hkD : ∀ a ∈ k, v (Dd a) ≤ exp Λ0 := fun a ha => (hkT a ha).2
  have hen := engine_p19 v Dd k hkv Λ0 hkD s hs1 hst b hgen P hP0 hPb hPc N hPN hNK hvn
  exact ⟨hen.1, hen.2 s₀ hs₀ hss₀⟩
theorem place_law_of_tame_unit (d : Fin 3) (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (v : Valuation (SliceField F₀) ℤᵐ⁰) (hvn : ∃ x, v x = exp (-1))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1)
    (z : SliceField F₀)
    (hz : v (HFree6812.sliceDerivation F F₀ hdvd z) ≤ max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (hdir : vpole v (HFree6812.sliceDerivation F F₀ hdvd z) ≤ dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)))
    (hkv : ∀ a ∈ unitField F₀ z, a ≠ 0 → v a = 1)
    (s b s₀ : SliceField F₀) (hs1 : v s ≤ 1) (hst : Transcendental (unitField F₀ z) s)
    (hs₀ : Tame v (HFree6812.sliceDerivation F F₀ hdvd) (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd z))) s₀)
    (hss₀ : v (s - s₀) < 1)
    (hgen : ∀ E : Subfield (SliceField F₀),
      (∀ x ∈ unitField F₀ z, x ∈ E) → s ∈ E → b ∈ E → ∀ x, x ∈ E)
    (P : Polynomial (SliceField F₀)) (hP0 : P ≠ 0) (hPb : P.eval b = 0)
    (hPc : ∀ n, P.coeff n ∈ IntermediateField.adjoin (unitField F₀ z) {s})
    (N : ℕ) (hPN : P.natDegree ≤ N) (hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0)
    (h2 : (2 : K) ≠ 0)
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ v) (placeH F F₀ v) → (n : K) ≠ 0)
    (hgen2 : placeP F₀ v = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a) < 1 ∧ v (sliceProj F₀ b) < 1 ∧
      ∀ g, v (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b)
    (m : ℕ) :
    3 * vpole v ((⇑(HFree6812.sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1)) +
        m * capPole d (placeP F₀ v) (placeYZ F₀ v) ≤
      m * (4 * placeT F F₀ v + 2 * placeH F F₀ v) + 3 * placeP F₀ v := by
  obtain ⟨⟨C, hcrude⟩, hsep⟩ := hdefer_of_tame_unit F F₀ hdvd hH v hvn z hkv s b s₀ hs1 hst hs₀ hss₀
    hgen P hP0 hPb hPc N hPN hNK
  exact GIA F F₀ hdvd v d hH hvn hK hX0 z hz hdir C hcrude hsep h2 hchar hgen2 m
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN313
theorem vpole_le_of_le_exp {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) (x : L) (a : ℤ) (ha : 0 ≤ a)
    (h : v x ≤ exp a) : vpole v x ≤ a :=
  (vpole_le_iff v x a ha).2 h
theorem chart_row_arith (sR sY sZ : Bool) (i : Fin 3) (l0 l1 l2 : ℤ)
    (h : ∀ j, chartExp sR sY sZ j 0 * l0 + chartExp sR sY sZ j 1 * l1 +
      chartExp sR sY sZ j 2 * l2 ≤ 0)
    (hu : chartExp sR sY sZ i 0 * l0 + chartExp sR sY sZ i 1 * l1 +
      chartExp sR sY sZ i 2 * l2 = 0) :
    (i = 2 → chartExp sR sY sZ i 0 = 0 ∧ chartExp sR sY sZ i 1 = 0) ∧
    (i = 1 → chartExp sR sY sZ i 1 = 0 ∧ 0 ≤ l0) ∧
    (i = 0 → 0 ≤ l1 ∧ (chartExp sR sY sZ i 0 = 0 ∨ l1 ≤ l0) ∧ l1 ≤ max 0 (max l0 l2)) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases i <;>
    simp [chartExp] at h0 h1 h2 hu ⊢ <;> omega
variable {K : Type} [Field K]
theorem D_lmono (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (a : Fin 3 → ℤ) :
    HFree6812.sliceDerivation F F₀ hdvd (lmono (sliceCoord F₀) a) =
      lmono (sliceCoord F₀) a * ((a 0 : SliceField F₀) * (sliceCoord F₀ 1 / sliceCoord F₀ 0) +
        (a 1 : SliceField F₀) * (sliceSigma F F₀ / sliceCoord F₀ 1)) := by
  have h0 := HFree6812.sliceDerivation_coord0 F F₀ hdvd hH
  have h1 := HFree6812.sliceDerivation_coord1 F F₀ hdvd hH
  have h2 := HFree6812.sliceDerivation_coord2 F F₀ hdvd hH
  have hy := hc 0
  have hr := hc 1
  rw [lmono, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_zpow, Derivation.leibniz_zpow,
    Derivation.leibniz_zpow, h0, h1, h2, zpow_sub_one₀ hy, zpow_sub_one₀ hr]
  simp only [smul_eq_mul, zsmul_eq_mul, mul_zero, smul_zero, zero_add]
  field_simp
  ring
theorem intCast_le_one (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (w : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → w (algebraMap K (SliceField F₀) a) = 1) (n : ℤ) :
    w (n : SliceField F₀) ≤ 1 := by
  rw [← map_intCast (algebraMap K (SliceField F₀)) n]
  by_cases h0 : (n : K) = 0
  · rw [h0, map_zero, w.map_zero]; exact zero_le
  · exact (hK _ h0).le
theorem chart_row (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool)
    (w : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → w (algebraMap K (SliceField F₀) a) = 1)
    (hle : ∀ j, w (chartCoord F₀ sR sY sZ j) ≤ 1) (i : Fin 3)
    (hu : w (chartCoord F₀ sR sY sZ i) = 1) :
    ∃ d : Fin 3,
      w (HFree6812.sliceDerivation F F₀ hdvd (chartCoord F₀ sR sY sZ i)) ≤ max (exp (placeP F₀ w)) (w (sliceSigma F F₀)) ∧
      vpole w (HFree6812.sliceDerivation F F₀ hdvd (chartCoord F₀ sR sY sZ i)) ≤
        dirS d (placeP F₀ w) (vpole w (sliceSigma F F₀)) ∧
      5 * placeP F₀ w ≤ capPole d (placeP F₀ w) (placeYZ F₀ w) := by
  set Dd := HFree6812.sliceDerivation F F₀ hdvd with hDd
  set cY := sliceCoord F₀ 0 with hY
  set cR := sliceCoord F₀ 1 with hR
  set cZ := sliceCoord F₀ 2 with hZ
  set σ := sliceSigma F F₀ with hσ
  set z := chartCoord F₀ sR sY sZ i with hz
  have wY0 : w cY ≠ 0 := (Valuation.ne_zero_iff w).2 (hc 0)
  have wR0 : w cR ≠ 0 := (Valuation.ne_zero_iff w).2 (hc 1)
  have hlY : w cY = exp (w cY).log := (exp_log wY0).symm
  have hlR : w cR = exp (w cR).log := (exp_log wR0).symm
  have harith := chart_row_arith sR sY sZ i (w cY).log (w cR).log (w cZ).log
    (fun j => (lmono_le_one_iff w (sliceCoord F₀) hc _).1 (hle j))
    (by
      have h := hu
      rw [hz, chartCoord, lmono_val w (sliceCoord F₀) hc, ← exp_zero, exp_inj] at h
      exact h)
  have hP : placeP F₀ w = max (max 0 (w cR).log) (max (max 0 (w cY).log) (max 0 (w cZ).log)) := rfl
  have ht : placeYZ F₀ w = max (max 0 (w cY).log) (max 0 (w cZ).log) := rfl
  have hPnn : 0 ≤ placeP F₀ w := by rw [hP]; exact le_max_of_le_left (le_max_left _ _)
  have hRP : w cR ≤ exp (placeP F₀ w) := by
    rw [hlR, exp_le_exp, hP]; exact le_max_of_le_left (le_max_right _ _)
  have hDz : Dd z = z * ((chartExp sR sY sZ i 0 : SliceField F₀) * (cR / cY) +
      (chartExp sR sY sZ i 1 : SliceField F₀) * (σ / cR)) :=
    D_lmono F F₀ hdvd hH hc _
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with h0 | h1 | h2
  · obtain ⟨hR1, hRY, hcap⟩ := harith.2.2 h0
    have hterm1 : w ((chartExp sR sY sZ i 0 : SliceField F₀) * (cR / cY)) ≤ 1 := by
      rcases hRY with h | h
      · rw [h, Int.cast_zero, zero_mul, w.map_zero]; exact zero_le
      · rw [map_mul, map_div₀]
        refine mul_le_one' (intCast_le_one F₀ w hK _) ?_
        rw [div_le_one₀ (zero_lt_iff.2 wY0), hlR, hlY, exp_le_exp]
        exact h
    have hterm2 : w ((chartExp sR sY sZ i 1 : SliceField F₀) * (σ / cR)) ≤ w σ := by
      rw [map_mul, map_div₀]
      refine (mul_le_of_le_one_left' (intCast_le_one F₀ w hK _)).trans ?_
      refine div_le_of_le_mul₀ zero_le zero_le (le_mul_of_one_le_right' ?_)
      rw [hlR, ← exp_zero, exp_le_exp]
      exact hR1
    have hb : w (Dd z) ≤ max 1 (w σ) := by
      rw [hDz, map_mul, hu, one_mul]
      exact (w.map_add _ _).trans (max_le_max hterm1 hterm2)
    refine ⟨2, hb.trans (max_le_max (by rw [← exp_zero, exp_le_exp]; exact hPnn) le_rfl), ?_, ?_⟩
    · refine vpole_le_of_le_exp w _ _ (le_max_of_le_left hPnn) (hb.trans (max_le ?_ ?_))
      · rw [← exp_zero, exp_le_exp]; exact le_max_of_le_left hPnn
      · exact (HFree6812.v_le_exp_vpole w σ).trans (exp_le_exp.2 (le_max_right _ _))
    · have hPt : placeP F₀ w ≤ placeYZ F₀ w := by rw [hP, ht]; omega
      simp [capPole, infCap]
      linarith
  · obtain ⟨ha1, hY1⟩ := harith.2.1 h1
    have hb : w (Dd z) ≤ exp (placeP F₀ w) := by
      rw [hDz, ha1, Int.cast_zero, zero_mul, add_zero, map_mul, hu, one_mul, map_mul, map_div₀]
      refine (mul_le_of_le_one_left' (intCast_le_one F₀ w hK _)).trans ?_
      refine (div_le_of_le_mul₀ zero_le zero_le (le_mul_of_one_le_right' ?_)).trans hRP
      rw [hlY, ← exp_zero, exp_le_exp]
      exact hY1
    refine ⟨1, hb.trans (le_max_left _ _), vpole_le_of_le_exp w _ _ hPnn hb, ?_⟩
    simp [capPole, infCap]
  · obtain ⟨ha0, ha1⟩ := harith.1 h2
    have hD : Dd z = 0 := by
      rw [hDz, ha0, ha1]; simp
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [hD, w.map_zero]; exact zero_le
    · rw [hD]; simp [vpole, dirS]
    · have htnn : 0 ≤ placeYZ F₀ w := by rw [ht]; exact le_max_of_le_left (le_max_left _ _)
      simp [capPole, infCap]
      linarith
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN002 RCN313 RCN095 RCN204 BD
open RCN095 renaming PolynomialInFlag → BI
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
noncomputable section
variable {K : Type} [Field K]
def PlaceLaw (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (w : Valuation (SliceField F₀) ℤᵐ⁰) (m : ℕ) : Prop :=
  3 * vpole w (tail F F₀ hdvd m) + m * (5 * placeP F₀ w) ≤
    m * (4 * placeT F F₀ w + 2 * placeH F F₀ w) + 3 * placeP F₀ w
def ChartPlaceLaw (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (sR sY sZ : Bool) : Prop :=
  ∀ w, ChartDivisor F₀ sR sY sZ w → ∀ m, PlaceLaw F F₀ hdvd w m
def ChartKrull (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) : Prop :=
  ∀ x : SliceField F₀, (∀ w, ChartDivisor F₀ sR sY sZ w → w x ≤ 1) →
    IsIntegral (chartRing F₀ sR sY sZ) x
def ChartCorePoly (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (N : ℕ) (sR sY sZ : Bool) :
    Prop :=
  ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    AlgebraicIndependent K
      ![chartCoord F₀ sR sY sZ i, chartCoord F₀ sR sY sZ j, sliceProj F₀ (MvPolynomial.X 0)] →
    ∃ P : Polynomial (SliceField F₀), P ≠ 0 ∧ P.eval (chartCoord F₀ sR sY sZ k) = 0 ∧
      P.natDegree ≤ N ∧ ∀ n, P.coeff n ∈ Algebra.adjoin K
        {sliceProj F₀ (MvPolynomial.X 0), chartCoord F₀ sR sY sZ i, chartCoord F₀ sR sY sZ j}
def ChartTwoCoord (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (N : ℕ) (sR sY sZ : Bool) :
    Prop :=
  ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    AlgebraicIndependent K ![chartCoord F₀ sR sY sZ i, sliceProj F₀ (MvPolynomial.X 0)] →
    ∃ (a : unitField F₀ (chartCoord F₀ sR sY sZ i)) (n : ℕ)
      (c : Fin n → Polynomial (unitField F₀ (chartCoord F₀ sR sY sZ i))),
      n ≤ 2 * N ∧ (∀ b : Fin n, (c b).natDegree + b ≤ n) ∧
      chartCoord F₀ sR sY sZ k ^ n = ∑ b : Fin n,
        Polynomial.aeval (chartCoord F₀ sR sY sZ j + a * chartCoord F₀ sR sY sZ k) (c b) *
          chartCoord F₀ sR sY sZ k ^ (b : ℕ)
def ChartNoether (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (N : ℕ) (sR sY sZ : Bool) :
    Prop :=
  ∃ s₁ ∈ chartRing F₀ sR sY sZ, ∃ s₂ ∈ chartRing F₀ sR sY sZ,
    AlgebraicIndependent (xField F₀) ![s₁, s₂] ∧
    (∀ a ∈ chartRing F₀ sR sY sZ, IsIntegral (Algebra.adjoin (xField F₀) {s₁, s₂}) a) ∧
    ∀ a : SliceField F₀, ∃ Q : Polynomial (IntermediateField.adjoin (xField F₀) {s₁, s₂}),
      Q ≠ 0 ∧ Q.natDegree ≤ 3 * N ∧ Polynomial.aeval a Q = 0
def ChartUnitCoord (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) : Prop :=
  ∀ w : Valuation (SliceField F₀) ℤᵐ⁰, ChartDivisor F₀ sR sY sZ w →
    ∃ i, AlgebraicIndependent K ![chartCoord F₀ sR sY sZ i, sliceProj F₀ (MvPolynomial.X 0)] ∧
      ∀ a ∈ unitField F₀ (chartCoord F₀ sR sY sZ i), a ≠ 0 → w a = 1
def ChartHchar (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) : Prop :=
  ∀ w : Valuation (SliceField F₀) ℤᵐ⁰, ChartDivisor F₀ sR sY sZ w →
    ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ w) (placeH F F₀ w) → (n : K) ≠ 0
def ChartHgen (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool) : Prop :=
  ∀ w : Valuation (SliceField F₀) ℤᵐ⁰, ChartDivisor F₀ sR sY sZ w →
    placeP F₀ w = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      w (sliceProj F₀ a) < 1 ∧ w (sliceProj F₀ b) < 1 ∧
      ∀ g, w (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        w (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b
def PsiSIntegral (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (S : MovingFiberThreeSources6811.Source F) (Hf : FlagDegree) (sR sY sZ : Bool) : Prop :=
  ∀ m : ℕ, IsIntegral (chartRing F₀ sR sY sZ)
    (psiS F F₀ hdvd S m /
      lmono (sliceCoord F₀) (vertexExp sR sY sZ (S.d • cutFlag m Hf + (4 * m) • S.flag)))
variable {E : Type} [Field E]
def SurfaceDivisorRestrict (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (sR sY sZ : Bool)
    (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (ψ : SliceField F₀ →+* RCN002.CoordinateField E G) : Prop :=
  ∀ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∀ a ∈ surfaceChartRing G sR sY sZ, nu a ≤ 1) →
    (∃ t ∈ surfaceChartRing G sR sY sZ, Transcendental E t ∧
      ∀ a ∈ IntermediateField.adjoin E {t}, a ≠ 0 → nu a = 1) →
    (∀ a, a ≠ 0 → nu (ψ a) = 1) ∨
      ∃ (e : ℕ) (w : Valuation (SliceField F₀) ℤᵐ⁰), 1 ≤ e ∧ ChartDivisor F₀ sR sY sZ w ∧
        ∀ a, nu (ψ a) = w a ^ e
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
universe u
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial
namespace Chart
section Linear
variable {k : Type*} [Field k]
theorem coeff_aeval_C_mul_X {σ : Type*} [Fintype σ] (h : σ → k) (Q : MvPolynomial σ k) (n : ℕ) :
    (aeval (fun i => Polynomial.C (h i) * Polynomial.X) Q : Polynomial k).coeff n =
      eval h (homogeneousComponent n Q) := by
  classical
  rw [aeval_def, eval₂_eq', Polynomial.finsetSum_coeff, eval_eq', support_homogeneousComponent,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hprod : ∏ i, (Polynomial.C (h i) * Polynomial.X) ^ d i =
      Polynomial.C (∏ i, h i ^ d i) * Polynomial.X ^ (∑ i, d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
  rw [hprod, Polynomial.algebraMap_eq, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
    coeff_homogeneousComponent, Finsupp.degree_eq_sum]
  by_cases hd : ∑ i, d i = n
  · simp [hd]
  · simp [hd, Ne.symm hd]
theorem exists_aeval_cons_one_ne_zero [Infinite k] {m : ℕ} (H : MvPolynomial (Fin (m + 1)) k) (n : ℕ)
    (hH : H.IsHomogeneous n) (hH0 : H ≠ 0) :
    ∃ c : Fin m → k, eval (Fin.cons 1 c : Fin (m + 1) → k) H ≠ 0 := by
  have hdeg : ∀ d ∈ H.support, d 0 + ∑ i, d.tail i = n := by
    intro d hd
    have h1 := hH.degree_eq_sum_deg_support hd
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_succ] at h1
    simpa [Finsupp.tail_apply] using h1.symm
  have hμ : Set.InjOn (Finsupp.tail : (Fin (m + 1) →₀ ℕ) → (Fin m →₀ ℕ)) H.support := by
    intro d hd d' hd' he
    have h1 := hdeg d hd
    have h2 := hdeg d' hd'
    rw [he] at h1
    rw [← Finsupp.cons_tail d, ← Finsupp.cons_tail d', he]
    congr 1
    omega
  obtain ⟨G, hG0, hGy, -⟩ := exists_monomialSubst (B := MvPolynomial (Fin m) k) H hH0 Finsupp.tail hμ
    (Fin.cons 1 MvPolynomial.X) MvPolynomial.X 1 (by
      intro d hd
      rw [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
      simp [Finsupp.tail_apply])
  rw [aeval_X_left_apply, one_mul] at hGy
  by_contra hall
  push Not at hall
  apply hG0
  apply MvPolynomial.funext
  intro c
  have h1 := comp_aeval_apply (f := (Fin.cons 1 MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin m) k))
    (aeval c : MvPolynomial (Fin m) k →ₐ[k] k) H
  rw [← hGy] at h1
  have e1 : eval c G = aeval c G := by
    rw [← coe_aeval_eq_eval]
    rfl
  have e2 : ∀ f : Fin (m + 1) → k, aeval f H = eval f H := fun f => by
    rw [← coe_aeval_eq_eval]
    rfl
  rw [map_zero, e1, h1, e2, ← hall c]
  refine congrArg (fun f : Fin (m + 1) → k => eval f H) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem finSuccEquiv_map_eval {B : Type*} [CommRing B] [Algebra k B] {m : ℕ} (τ₀ : B)
    (σ' : Fin m → B) (p : MvPolynomial (Fin (m + 1)) k) :
    ((finSuccEquiv k m p).map (aeval σ' : MvPolynomial (Fin m) k →ₐ[k] B).toRingHom).eval τ₀ =
      aeval (Fin.cons τ₀ σ' : Fin (m + 1) → B) p := by
  have h : ((Polynomial.aeval τ₀ : Polynomial B →ₐ[B] B).restrictScalars k).comp
      ((Polynomial.mapAlgHom (aeval σ')).comp (finSuccEquiv k m).toAlgHom) =
      aeval (Fin.cons τ₀ σ' : Fin (m + 1) → B) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]
  rw [← h]
  rfl
theorem exists_linear_normal [Infinite k] {m : ℕ} (P : MvPolynomial (Fin (m + 1)) k) (hP : P ≠ 0) :
    ∃ (c : Fin m → k) (R : Polynomial (MvPolynomial (Fin m) k)) (γ : k), γ ≠ 0 ∧
      R.natDegree ≤ P.totalDegree ∧ R.coeff P.totalDegree = MvPolynomial.C γ ∧
      (∀ i, R.coeff i ≠ 0 → (R.coeff i).totalDegree + i ≤ P.totalDegree) ∧
      ∀ {B : Type u} [CommRing B] [Algebra k B] (τ₀ : B) (σ' : Fin m → B),
        (R.map (aeval σ' : MvPolynomial (Fin m) k →ₐ[k] B).toRingHom).eval τ₀ =
          aeval (Fin.cons τ₀ fun i => σ' i + c i • τ₀ : Fin (m + 1) → B) P := by
  classical
  set n := P.totalDegree with hn
  have hH0 : homogeneousComponent n P ≠ 0 := by
    obtain ⟨d, hd, hdn⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP)
      fun e => (Finsupp.toMultiset e).card
    rw [← totalDegree_eq] at hdn
    have hdeg : Finsupp.degree d = n := by
      rw [hn, hdn, Finsupp.card_toMultiset, Finsupp.degree_apply]
      rfl
    intro h0
    have h1 : (homogeneousComponent n P).coeff d = 0 := by
      rw [h0]
      rfl
    rw [coeff_homogeneousComponent] at h1
    simp only [hdeg, ↓reduceIte] at h1
    exact (mem_support_iff.1 hd) h1
  obtain ⟨c, hc⟩ := exists_aeval_cons_one_ne_zero (homogeneousComponent n P) n
    (homogeneousComponent_isHomogeneous n P) hH0
  set g : Fin (m + 1) → MvPolynomial (Fin (m + 1)) k := Fin.cons (MvPolynomial.X 0)
    fun i => MvPolynomial.X i.succ + MvPolynomial.C (c i) * MvPolynomial.X 0 with hg
  have hg1 : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [g, totalDegree_X]
    · simp only [g, Fin.cons_succ]
      refine (totalDegree_add _ _).trans (max_le (totalDegree_X _).le ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
  set Q := aeval g P with hQ
  have hQdeg : Q.totalDegree ≤ n := by
    rw [hQ, aeval_def, eval₂_eq']
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [algebraMap_eq, totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg1 i))).trans ?_
    simp only [mul_one]
    have h1 := le_totalDegree hd
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
  set R := finSuccEquiv k m Q with hR
  have hRdeg : R.natDegree ≤ n := by
    rw [hR, natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree _ _).trans hQdeg
  have hRc : ∀ i, R.coeff i ≠ 0 → (R.coeff i).totalDegree + i ≤ n := fun i hi =>
    (totalDegree_coeff_finSuccEquiv_add_le Q i hi).trans hQdeg
  have hRn : R.coeff n = MvPolynomial.C ((R.coeff n).coeff 0) := by
    by_cases h0 : R.coeff n = 0
    · rw [h0]
      simp
    · have h1 := hRc n h0
      exact totalDegree_eq_zero_iff_eq_C.1 (by omega)
  have hγ : (R.coeff n).coeff 0 =
      eval (Fin.cons 1 c : Fin (m + 1) → k) (homogeneousComponent n P) := by
    set φ : MvPolynomial (Fin (m + 1)) k →ₐ[k] Polynomial k :=
      (Polynomial.mapAlgHom (aeval (0 : Fin m → k))).comp (finSuccEquiv k m).toAlgHom with hφ
    have h1 : (φ Q).coeff n = (R.coeff n).coeff 0 := by
      show ((finSuccEquiv k m Q).map _).coeff n = _
      rw [Polynomial.coeff_map, ← hR, hRn]
      simp
    have h2 : φ Q = aeval (fun i =>
        Polynomial.C ((Fin.cons 1 c : Fin (m + 1) → k) i) * Polynomial.X) P := by
      rw [hQ, comp_aeval_apply]
      refine congrArg (fun f => aeval f P) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [φ, g, finSuccEquiv_X_zero]
      · have hC : finSuccEquiv k m (MvPolynomial.C (c j)) =
            Polynomial.C (MvPolynomial.C (c j)) := by
          rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
            MvPolynomial.algebraMap_eq]
        simp [φ, g, finSuccEquiv_X_succ, finSuccEquiv_X_zero, hC]
    rw [← h1, h2, coeff_aeval_C_mul_X]
  refine ⟨c, R, (R.coeff n).coeff 0, by rw [hγ]; exact hc, hRdeg, hRn, hRc, ?_⟩
  intro B _ _ τ₀ σ'
  rw [hR, finSuccEquiv_map_eval, hQ]
  have h1 := comp_aeval_apply (f := g) (aeval (Fin.cons τ₀ σ' : Fin (m + 1) → B)) P
  rw [h1]
  refine congrArg (fun f => aeval f P) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [g]
  · simp [g, Algebra.smul_def]
end Linear
section TwoCoord
variable {k : Type*} [Field k]
theorem natDegree_aeval_X_le {σ : Type*} [Fintype σ] (p : MvPolynomial σ k) :
    (aeval (fun _ : σ => (Polynomial.X : Polynomial k)) p).natDegree ≤ p.totalDegree := by
  classical
  rw [aeval_def, eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have h1 := le_totalDegree hd
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
theorem exists_twoCoord [Infinite k] {B : Type*} [CommRing B] [Algebra k B]
    (P : MvPolynomial (Fin 2) k) (hP : P ≠ 0) (v u₀ : B) (hPv : aeval ![v, u₀] P = 0) :
    ∃ (a : k) (c : Fin P.totalDegree → Polynomial k),
      (∀ b : Fin P.totalDegree, (c b).natDegree + b ≤ P.totalDegree) ∧
      v ^ P.totalDegree =
        ∑ b : Fin P.totalDegree, Polynomial.aeval (u₀ + a • v) (c b) * v ^ (b : ℕ) := by
  obtain ⟨c₀, R, γ, hγ, hRdeg, hRn, hRc, hev⟩ := exists_linear_normal (m := 1) P hP
  set n := P.totalDegree with hn
  set u : B := u₀ + (-c₀ 0) • v with hu
  have hpt : (Fin.cons v fun i : Fin 1 => u + c₀ i • v : Fin 2 → B) = ![v, u₀] := by
    funext i
    fin_cases i
    · rfl
    · simp [u]
  have h0 := hev v fun _ => u
  rw [hpt, hPv, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans hRdeg)),
    Finset.sum_range_succ] at h0
  simp only [Polynomial.coeff_map] at h0
  set p : ℕ → Polynomial k := fun b => aeval (fun _ : Fin 1 => (Polynomial.X : Polynomial k)) (R.coeff b)
    with hp
  have hpu : ∀ b, (aeval (fun _ : Fin 1 => u) : MvPolynomial (Fin 1) k →ₐ[k] B).toRingHom (R.coeff b) =
      Polynomial.aeval u (p b) := by
    intro b
    have h1 := comp_aeval_apply (f := fun _ : Fin 1 => (Polynomial.X : Polynomial k))
      (Polynomial.aeval u : Polynomial k →ₐ[k] B) (R.coeff b)
    rw [hp, h1]
    simp
  have hγu : (aeval (fun _ : Fin 1 => u) : MvPolynomial (Fin 1) k →ₐ[k] B).toRingHom (R.coeff n) =
      algebraMap k B γ := by
    rw [hRn]
    simp
  rw [hγu, Finset.sum_congr rfl fun b _ => by rw [hpu b]] at h0
  refine ⟨-c₀ 0, fun b => (-γ⁻¹) • p b, ?_, ?_⟩
  · intro b
    refine (Nat.add_le_add_right (Polynomial.natDegree_smul_le _ _) _).trans ?_
    by_cases hb : R.coeff b = 0
    · have h1 : p b = 0 := by
        rw [hp]
        simp [hb]
      rw [h1, Polynomial.natDegree_zero, zero_add]
      exact b.2.le
    · exact (Nat.add_le_add_right (natDegree_aeval_X_le _) _).trans (hRc b hb)
  · rw [Fin.sum_univ_eq_sum_range (fun b => Polynomial.aeval u ((-γ⁻¹) • p b) * v ^ b) n]
    have h1 : ∑ b ∈ Finset.range n, Polynomial.aeval u ((-γ⁻¹) • p b) * v ^ b =
        (-γ⁻¹) • ∑ b ∈ Finset.range n, Polynomial.aeval u (p b) * v ^ b := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, smul_mul_assoc]
    rw [h1, eq_neg_of_add_eq_zero_left h0, smul_neg, neg_smul, neg_neg, Algebra.smul_def, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hγ, map_one, one_mul]
end TwoCoord
section Noether
variable {k : Type*} [Field k]
theorem exists_monic_of_linear_normal {B : Type*} [CommRing B] [Algebra k B] {m : ℕ}
    (R : Polynomial (MvPolynomial (Fin m) k)) (n : ℕ) (γ : k) (hγ : γ ≠ 0) (hRdeg : R.natDegree ≤ n)
    (hRn : R.coeff n = MvPolynomial.C γ) (τ₀ : B) (σ' : Fin m → B)
    (h0 : (R.map (aeval σ' : MvPolynomial (Fin m) k →ₐ[k] B).toRingHom).eval τ₀ = 0) :
    ∃ q : Polynomial (Algebra.adjoin k (Set.range σ')), q.Monic ∧ q.natDegree ≤ n ∧
      Polynomial.eval₂ (algebraMap (Algebra.adjoin k (Set.range σ')) B) τ₀ q = 0 := by
  set S := Algebra.adjoin k (Set.range σ') with hS
  set σS : Fin m → S := fun i => ⟨σ' i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ with hσS
  set f : MvPolynomial (Fin m) k →ₐ[k] S := aeval σS with hf
  have hcomp : (algebraMap S B).comp f.toRingHom =
      (aeval σ' : MvPolynomial (Fin m) k →ₐ[k] B).toRingHom := by
    refine RingHom.ext fun p => ?_
    exact comp_aeval_apply (f := σS) S.val p
  refine ⟨Polynomial.C (algebraMap k S γ⁻¹) * R.map f.toRingHom, ?_, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_map_le.trans hRdeg)) ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, hRn]
    have h1 : f.toRingHom (MvPolynomial.C γ) = algebraMap k S γ := by
      simp [f]
    rw [h1, ← map_mul, inv_mul_cancel₀ hγ, map_one]
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_map_le.trans hRdeg)
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map, hcomp,
      Polynomial.eval₂_eq_eval_map, h0, mul_zero]
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_noether_of_relation [Infinite k] {L : Type*} [Field L] [Algebra k L] (t : Fin 3 → L)
    (P : MvPolynomial (Fin 3) k) (hP : P ≠ 0) (hPt : aeval t P = 0)
    (hgen : ∀ E : Subfield L, (∀ a : k, algebraMap k L a ∈ E) → (∀ i, t i ∈ E) → ∀ z, z ∈ E)
    (y : Fin 2 → L) (hy : AlgebraicIndependent k y) :
    ∃ s₁ ∈ Algebra.adjoin k (Set.range t), ∃ s₂ ∈ Algebra.adjoin k (Set.range t),
      AlgebraicIndependent k ![s₁, s₂] ∧
      (∀ a ∈ Algebra.adjoin k (Set.range t), IsIntegral (Algebra.adjoin k {s₁, s₂}) a) ∧
      ∀ a : L, ∃ Q : Polynomial (IntermediateField.adjoin k {s₁, s₂}),
        Q ≠ 0 ∧ Q.natDegree ≤ P.totalDegree ∧ Polynomial.aeval a Q = 0 := by
  classical
  obtain ⟨c, R, γ, hγ, hRdeg, hRn, -, hev⟩ := exists_linear_normal (m := 2) P hP
  set n := P.totalDegree with hn
  set s : Fin 2 → L := fun i => t i.succ - c i • t 0 with hs
  have hpt : (Fin.cons (t 0) fun i => s i + c i • t 0 : Fin 3 → L) = t := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [s]
  have h0 := hev (t 0) s
  rw [hpt, hPt] at h0
  have hrange : Set.range s = {s 0, s 1} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hex : ∃ q : Polynomial (Algebra.adjoin k ({s 0, s 1} : Set L)), q.Monic ∧ q.natDegree ≤ n ∧
      Polynomial.eval₂ (algebraMap (Algebra.adjoin k ({s 0, s 1} : Set L)) L) (t 0) q = 0 := by
    rw [← hrange]
    exact exists_monic_of_linear_normal R n γ hγ hRdeg hRn (t 0) s h0
  set S := Algebra.adjoin k ({s 0, s 1} : Set L) with hS
  set M := IntermediateField.adjoin k ({s 0, s 1} : Set L) with hM
  obtain ⟨q, hqm, hqdeg, hq0⟩ := hex
  have hsS : ∀ i, s i ∈ S := fun i =>
    Algebra.subset_adjoin (by rw [← hrange]; exact ⟨i, rfl⟩)
  have hst : ∀ i, s i ∈ Algebra.adjoin k (Set.range t) := fun i =>
    Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i.succ))
      (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self 0)) _)
  have hint0 : IsIntegral S (t 0) := ⟨q, hqm, hq0⟩
  have hintS : ∀ z ∈ S, IsIntegral S z := fun z hz =>
    (isIntegral_algebraMap : IsIntegral S (algebraMap S L ⟨z, hz⟩))
  have hintt : ∀ i, IsIntegral S (t i) := by
    intro i
    refine Fin.cases hint0 (fun j => ?_) i
    have h1 : t j.succ = s j + c j • t 0 := by simp [s]
    rw [h1]
    exact (hintS _ (hsS j)).add (hint0.smul (c j))
  have hintA : ∀ a ∈ Algebra.adjoin k (Set.range t), IsIntegral S a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact hintt i
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply k S L]
      exact isIntegral_algebraMap
    | add z w _ _ hz hw => exact hz.add hw
    | mul z w _ _ hz hw => exact hz.mul hw
  have hint0M : IsIntegral M (t 0) := hint0.tower_top
  have hdeg0 : (minpoly M (t 0)).natDegree ≤ n := by
    have hroot : Polynomial.aeval (t 0) (q.map (algebraMap S M)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      exact hq0
    refine (Polynomial.natDegree_le_of_dvd (minpoly.dvd M (t 0) hroot)
      (hqm.map _).ne_zero).trans ?_
    rw [hqm.natDegree_map]
    exact hqdeg
  have htop : IntermediateField.adjoin M {t 0} = ⊤ := by
    have hME : ∀ z : M, algebraMap M L z ∈ (IntermediateField.adjoin M {t 0}).toSubfield :=
      fun z => (IntermediateField.adjoin M {t 0}).algebraMap_mem z
    have hkE : ∀ a : k, algebraMap k L a ∈ (IntermediateField.adjoin M {t 0}).toSubfield := fun a => by
      rw [IsScalarTower.algebraMap_apply k M L]
      exact hME _
    have ht0 : t 0 ∈ (IntermediateField.adjoin M {t 0}).toSubfield :=
      IntermediateField.subset_adjoin M {t 0} (Set.mem_singleton _)
    have hall := hgen (IntermediateField.adjoin M {t 0}).toSubfield hkE (fun i => by
      refine Fin.cases ht0 (fun j => ?_) i
      have h1 : t j.succ = s j + algebraMap k L (c j) * t 0 := by simp [s, Algebra.smul_def]
      rw [h1]
      refine add_mem ?_ (mul_mem (hkE _) ht0)
      exact hME ⟨s j, IntermediateField.subset_adjoin k _ (by rw [← hrange]; exact ⟨j, rfl⟩)⟩)
    exact eq_top_iff.2 fun z _ => hall z
  let e : IntermediateField.adjoin M {t 0} ≃ₐ[M] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  have : FiniteDimensional M (IntermediateField.adjoin M {t 0}) :=
    IntermediateField.adjoin.finiteDimensional hint0M
  have : FiniteDimensional M L := e.toLinearEquiv.finiteDimensional
  have hfinrank : Module.finrank M L ≤ n := by
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.adjoin.finrank hint0M]
    exact hdeg0
  have halg : ∀ T : Subalgebra k L, T = S → Algebra.IsAlgebraic T L := by
    rintro T rfl
    exact ⟨fun a => (IsFractionRing.isAlgebraic_iff S M L).2
      (Algebra.IsIntegral.isIntegral (R := M) a).isAlgebraic⟩
  have hset : Set.range ![s 0, s 1] = {s 0, s 1} := by
    rw [← hrange]
    congr 1
    funext i
    fin_cases i <;> rfl
  have := halg (Algebra.adjoin k (Set.range ![s 0, s 1])) (by rw [hset])
  refine ⟨s 0, hst 0, s 1, hst 1, ?_, hintA, fun a => ?_⟩
  · exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k ![s 0, s 1]
      hy.lift_cardinalMk_le_trdeg).1
  · have ha : IsIntegral M a := Algebra.IsIntegral.isIntegral a
    exact ⟨minpoly M a, minpoly.ne_zero ha, (minpoly.natDegree_le a).trans hfinrank,
      minpoly.aeval M a⟩
theorem exists_chart_noether [Infinite k] {L : Type*} [Field L] [Algebra k L] (x : Fin 3 → L)
    (hx : ∀ j, x j ≠ 0) (F : MvPolynomial (Fin 3) k) (hF : F ≠ 0) (hFx : aeval x F = 0) (N : ℕ)
    (hN : ∀ d ∈ F.support, d 0 + d 1 + d 2 ≤ N)
    (hgen : ∀ E : Subfield L, (∀ a : k, algebraMap k L a ∈ E) → (∀ j, x j ∈ E) → ∀ z, z ∈ E)
    (y : Fin 2 → L) (hy : AlgebraicIndependent k y) (sR sY sZ : Bool) :
    ∃ s₁ ∈ Algebra.adjoin k (Set.range fun i => lmono x (chartExp sR sY sZ i)),
      ∃ s₂ ∈ Algebra.adjoin k (Set.range fun i => lmono x (chartExp sR sY sZ i)),
      AlgebraicIndependent k ![s₁, s₂] ∧
      (∀ a ∈ Algebra.adjoin k (Set.range fun i => lmono x (chartExp sR sY sZ i)),
        IsIntegral (Algebra.adjoin k {s₁, s₂}) a) ∧
      ∀ a : L, ∃ Q : Polynomial (IntermediateField.adjoin k {s₁, s₂}),
        Q ≠ 0 ∧ Q.natDegree ≤ 3 * N ∧ Polynomial.aeval a Q = 0 := by
  obtain ⟨P, hP0, hPt, hPs⟩ := exists_chartPoly x hx F hF hFx N hN sR sY sZ
  have hPdeg : P.totalDegree ≤ 3 * N := by
    rw [totalDegree_eq]
    refine Finset.sup_le fun e he => ?_
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]
    have h0 := hPs e he 0
    have h1 := hPs e he 1
    have h2 := hPs e he 2
    simp only [id]
    omega
  obtain ⟨s₁, hs₁, s₂, hs₂, hind, hint, hdeg⟩ := exists_noether_of_relation
    (fun i => lmono x (chartExp sR sY sZ i)) P hP0 hPt
    (fun E hk ht => hgen E hk (coord_mem_of_chart_mem x hx sR sY sZ E ht)) y hy
  refine ⟨s₁, hs₁, s₂, hs₂, hind, hint, fun a => ?_⟩
  obtain ⟨Q, hQ0, hQd, hQa⟩ := hdeg a
  exact ⟨Q, hQ0, hQd.trans hPdeg, hQa⟩
end Noether
end Chart
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace PlaceSurf
open WithZero
section Length
variable {O B : Type*} [CommRing O] [CommRing B]
theorem length_quotient_ker_sup (f : O →+* B) (hf : Function.Surjective f) (I : Ideal O) :
    Module.length O (O ⧸ (RingHom.ker f ⊔ I)) = Module.length B (B ⧸ I.map f) := by
  let _ := f.toAlgebra
  rw [← Module.length_eq_of_surjective (S := O) (R := B) (M := B ⧸ I.map f) hf]
  let g : O →ₗ[O] B ⧸ I.map f := ((I.map f).mkQ.restrictScalars O).comp (Algebra.linearMap O B)
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp hf
  have hker : LinearMap.ker g = RingHom.ker f ⊔ I := by
    ext x
    change Submodule.Quotient.mk (f x) = (0 : B ⧸ I.map f) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hf,
      sup_comm]
    rfl
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hg)).length_eq
end Length
section Value
theorem valuation_eq_one_of_isAlgClosed {E F : Type*} [Field E] [IsAlgClosed E] [Field F]
    [Algebra E F] (v : Valuation F ℤᵐ⁰) {a : E} (ha : a ≠ 0) : v (algebraMap E F a) = 1 := by
  have hne : v (algebraMap E F a) ≠ 0 := (Valuation.ne_zero_iff v).mpr ((map_ne_zero _).mpr ha)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a
    (n := (v (algebraMap E F a)).log.natAbs + 1) (Nat.succ_pos _)
  have hlog : (v (algebraMap E F a)).log =
      (((v (algebraMap E F a)).log.natAbs + 1 : ℕ) : ℤ) * (v (algebraMap E F b)).log := by
    conv_lhs => rw [← hb, map_pow, map_pow, log_pow, nsmul_eq_mul]
  refine eq_one_of_log_eq_zero hne (Int.eq_zero_of_abs_lt_dvd ⟨_, hlog⟩ ?_)
  rw [Int.abs_eq_natAbs]
  push_cast
  omega
theorem eq_exp_neg_toNat {y : ℤᵐ⁰} (h0 : y ≠ 0) (h1 : y ≤ 1) :
    y = exp (-((-y.log).toNat : ℤ)) := by
  have hlog : y.log ≤ 0 := by
    rw [← exp_log h0, ← exp_zero, exp_le_exp] at h1
    exact h1
  rw [Int.toNat_of_nonneg (neg_nonneg.mpr hlog), neg_neg, exp_log h0]
end Value
section Chart
variable {L : Type*} [Field L]
def flip (s : Bool) (a : L) : L := if s then a⁻¹ else a
def denY (x : Fin 3 → L) (sZ : Bool) : L := if sZ then x 2 else 1
def denR (x : Fin 3 → L) (sY sZ : Bool) : L := if sY then x 0 else denY x sZ
theorem lmono_chartExp_two (x : Fin 3 → L) (sR sY sZ : Bool) :
    lmono x (chartExp sR sY sZ 2) = flip sZ (x 2) := by
  cases sR <;> cases sY <;> cases sZ <;> simp [lmono, chartExp, flip]
theorem lmono_chartExp_one (x : Fin 3 → L) (sR sY sZ : Bool) :
    lmono x (chartExp sR sY sZ 1) = flip sY (x 0 / denY x sZ) := by
  cases sR <;> cases sY <;> cases sZ <;> simp [lmono, chartExp, flip, denY, div_eq_mul_inv, mul_comm]
theorem lmono_chartExp_zero (x : Fin 3 → L) (sR sY sZ : Bool) :
    lmono x (chartExp sR sY sZ 0) = flip sR (x 1 / denR x sY sZ) := by
  cases sR <;> cases sY <;> cases sZ <;>
    simp [lmono, chartExp, flip, denR, denY, div_eq_mul_inv, mul_comm]
variable {O W : Set L}
theorem flip_mul_mem (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hU : ∀ a ∈ O, a⁻¹ ∈ W → a⁻¹ ∈ O)
    {y c : L} {s s' : Bool} (hy : flip s y ∈ O) (hc : c ∈ O) (hc' : c⁻¹ ∈ O)
    (hW : flip s' (y * c) ∈ W) : flip s' (y * c) ∈ O := by
  cases s <;> cases s' <;> simp only [flip, ↓reduceIte, Bool.false_eq_true] at hy hW ⊢
  · exact hmul _ hy _ hc
  · exact hU _ (hmul _ hy _ hc) hW
  · have h := hU _ (hmul _ hy _ hc') (by rwa [mul_inv, inv_inv, inv_inv])
    rwa [mul_inv, inv_inv, inv_inv] at h
  · rw [mul_inv]
    exact hmul _ hy _ hc'
theorem chart_overlap (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0) (h1 : (1 : L) ∈ O)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hU : ∀ a ∈ O, a⁻¹ ∈ W → a⁻¹ ∈ O)
    (sR sY sZ sR' sY' sZ' : Bool) (hO : ∀ i, lmono x (chartExp sR sY sZ i) ∈ O)
    (hW : ∀ i, lmono x (chartExp sR' sY' sZ' i) ∈ W) (i : Fin 3) :
    lmono x (chartExp sR' sY' sZ' i) ∈ O := by
  have hO0 := hO 0
  have hO1 := hO 1
  have hO2 := hO 2
  have hW0 := hW 0
  have hW1 := hW 1
  have hW2 := hW 2
  rw [lmono_chartExp_zero] at hO0 hW0
  rw [lmono_chartExp_one] at hO1 hW1
  rw [lmono_chartExp_two] at hO2 hW2
  have h1' : (1 : L)⁻¹ ∈ O := by rwa [inv_one]
  have hZ : flip sZ' (x 2) ∈ O := by
    have h := flip_mul_mem hmul hU hO2 h1 h1' (s' := sZ') (by rwa [mul_one])
    rwa [mul_one] at h
  have hcY : denY x sZ / denY x sZ' ∈ O ∧ (denY x sZ / denY x sZ')⁻¹ ∈ O := by
    cases sZ <;> cases sZ' <;>
      simp only [flip, denY, ↓reduceIte, Bool.false_eq_true, div_one, one_div, inv_inv,
        div_self (hx 2), inv_one] at hO2 hZ ⊢ <;> exact ⟨by assumption, by assumption⟩
  have hYeq : x 0 / denY x sZ' = x 0 / denY x sZ * (denY x sZ / denY x sZ') := by
    have hd : denY x sZ ≠ 0 := by
      cases sZ <;> simp [denY, hx 2]
    field_simp
  have hY : flip sY' (x 0 / denY x sZ') ∈ O := by
    rw [hYeq] at hW1 ⊢
    exact flip_mul_mem hmul hU hO1 hcY.1 hcY.2 hW1
  have hcR : denR x sY sZ / denR x sY' sZ' ∈ O ∧ (denR x sY sZ / denR x sY' sZ')⁻¹ ∈ O := by
    have hdY : ∀ s, denY x s ≠ 0 := fun s => by cases s <;> simp [denY, hx 2]
    cases sY <;> cases sY' <;>
      simp only [flip, denR, ↓reduceIte, Bool.false_eq_true, div_self (hx 0), inv_one]
        at hO1 hY ⊢
    · exact hcY
    · refine ⟨?_, ?_⟩
      · have h := hmul _ hY _ hcY.1
        rwa [show (x 0 / denY x sZ')⁻¹ * (denY x sZ / denY x sZ') = denY x sZ / x 0 by
          field_simp [hx 0, hdY sZ']] at h
      · rwa [inv_div]
    · refine ⟨?_, ?_⟩
      · exact hY
      · have h := hmul _ hO1 _ hcY.2
        rwa [show (x 0 / denY x sZ)⁻¹ * (denY x sZ / denY x sZ')⁻¹ = (x 0 / denY x sZ')⁻¹ by
          field_simp [hx 0, hdY sZ, hdY sZ']] at h
    · exact ⟨h1, h1⟩
  have hReq : x 1 / denR x sY' sZ' = x 1 / denR x sY sZ * (denR x sY sZ / denR x sY' sZ') := by
    have hd : denR x sY sZ ≠ 0 := by
      cases sY <;> cases sZ <;> simp [denR, denY, hx 0, hx 2]
    field_simp
  have hR : flip sR' (x 1 / denR x sY' sZ') ∈ O := by
    rw [hReq] at hW0 ⊢
    exact flip_mul_mem hmul hU hO0 hcR.1 hcR.2 hW0
  fin_cases i
  · change lmono x (chartExp sR' sY' sZ' 0) ∈ O
    rw [lmono_chartExp_zero]
    exact hR
  · change lmono x (chartExp sR' sY' sZ' 1) ∈ O
    rw [lmono_chartExp_one]
    exact hY
  · change lmono x (chartExp sR' sY' sZ' 2) ∈ O
    rw [lmono_chartExp_two]
    exact hZ
theorem chartExp_neg_cases : ∀ (sR sY sZ : Bool) (i j : Fin 3), chartExp sR sY sZ i j < 0 →
    (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) := by
  decide
theorem val_eq_one_of_chartExp_neg (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0)
    (hv : ∀ j, v (x j) ≤ 1) {sR sY sZ : Bool} (hu : ∀ i, v (lmono x (chartExp sR sY sZ i)) ≤ 1)
    {i j : Fin 3} (hneg : chartExp sR sY sZ i j < 0) : v (x j) = 1 := by
  have hl : ∀ j, (v (x j)).log ≤ 0 := fun j =>
    (log_le_iff_le_exp ((Valuation.ne_zero_iff v).2 (hx j))).2 (by rw [exp_zero]; exact hv j)
  have r0 := (lmono_le_one_iff v x hx _).1 (hu 0)
  have r1 := (lmono_le_one_iff v x hx _).1 (hu 1)
  have r2 := (lmono_le_one_iff v x hx _).1 (hu 2)
  have l0 := hl 0
  have l1 := hl 1
  have l2 := hl 2
  have key : (sY = true → (v (x 0)).log = 0) ∧ (sR = true → (v (x 1)).log = 0) ∧
      (sZ = true → (v (x 2)).log = 0) := by
    rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
      simp [chartExp] at r0 r1 r2 ⊢ <;> omega
  rcases chartExp_neg_cases _ _ _ _ _ hneg with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact eq_one_of_log_eq_zero ((Valuation.ne_zero_iff v).2 (hx 0)) (key.1 h)
  · exact eq_one_of_log_eq_zero ((Valuation.ne_zero_iff v).2 (hx 1)) (key.2.1 h)
  · exact eq_one_of_log_eq_zero ((Valuation.ne_zero_iff v).2 (hx 2)) (key.2.2 h)
theorem chart_cover_of_dichotomy (x : Fin 3 → L) (hx : ∀ j, x j ≠ 0)
    (hW : ∀ t : L, t ≠ 0 → t ∈ W ∨ t⁻¹ ∈ W) :
    ∃ sR sY sZ : Bool, ∀ i, lmono x (chartExp sR sY sZ i) ∈ W := by
  have key : ∀ sR sY sZ : Bool, flip sZ (x 2) ∈ W → flip sY (x 0 / denY x sZ) ∈ W →
      flip sR (x 1 / denR x sY sZ) ∈ W → ∀ i, lmono x (chartExp sR sY sZ i) ∈ W := by
    intro sR sY sZ h2 h1 h0 i
    fin_cases i
    · change lmono x (chartExp sR sY sZ 0) ∈ W
      rwa [lmono_chartExp_zero]
    · change lmono x (chartExp sR sY sZ 1) ∈ W
      rwa [lmono_chartExp_one]
    · change lmono x (chartExp sR sY sZ 2) ∈ W
      rwa [lmono_chartExp_two]
  have hflip : ∀ t : L, t ≠ 0 → ∃ s : Bool, flip s t ∈ W := fun t ht =>
    (hW t ht).elim (fun h => ⟨false, h⟩) fun h => ⟨true, h⟩
  obtain ⟨sZ, hZ⟩ := hflip (x 2) (hx 2)
  have hdY : denY x sZ ≠ 0 := by cases sZ <;> simp [denY, hx 2]
  obtain ⟨sY, hY⟩ := hflip (x 0 / denY x sZ) (div_ne_zero (hx 0) hdY)
  have hdR : denR x sY sZ ≠ 0 := by cases sY <;> simp [denR, hx 0, hdY]
  obtain ⟨sR, hR⟩ := hflip (x 1 / denR x sY sZ) (div_ne_zero (hx 1) hdR)
  exact ⟨sR, sY, sZ, key sR sY sZ hZ hY hR⟩
end Chart
end PlaceSurf
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
theorem Divisor.induction_on {O : Type*} [CommRing O] {p : Divisor O → Prop} (D : Divisor O)
    (h0 : p 0) (hadd : ∀ (D : Divisor O) (P : PrimeDivisor O), p D → p (D + Finsupp.single P 1)) :
    p D := by
  induction D using Finsupp.induction₂ with
  | zero => exact h0
  | add_single P n D _ _ ih =>
    clear * - ih hadd
    induction n with
    | zero => rwa [Finsupp.single_zero, add_zero]
    | succ n ihn =>
      rw [Finsupp.single_add, ← add_assoc]
      exact hadd _ P ihn
theorem length_quotient_sup_ne_top {O : Type*} [CommRing O] [IsNoetherianRing O]
    (hO : DivisorChain O) (P : PrimeDivisor O) {I : Ideal O} (hI : ¬I ≤ P.ideal) :
    Module.length O (O ⧸ (P.ideal ⊔ I)) ≠ ⊤ := by
  refine length_quotient_ne_top_of_forall_isMaximal _ fun Q hQ hle =>
    hO P Q hQ (lt_of_le_of_ne (le_sup_left.trans hle) ?_)
  rintro rfl
  exact hI (le_sup_right.trans hle)
theorem length_quotient_sup_span_ne_top {O : Type*} [CommRing O] [IsNoetherianRing O]
    (hO : DivisorChain O) (P : PrimeDivisor O) {g : O} (hg : g ∉ P.ideal) :
    Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) ≠ ⊤ :=
  length_quotient_sup_ne_top hO P fun hle => hg (hle (Ideal.mem_span_singleton_self g))
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
theorem length_quotient_divisorIdeal_add_single (hO : DivisorChain O) {g : O} {D : Divisor O}
    {P : PrimeDivisor O} (hgD : ∀ Q ∈ D.support, g ∉ Q.ideal) (hgP : g ∉ P.ideal) :
    Module.length O (O ⧸ (divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g})) =
      Module.length O (O ⧸ (divisorIdeal K D ⊔ Ideal.span {g})) +
        Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) := by
  obtain ⟨φ, hφ⟩ := exists_isTransfer K D P
  have hJ : divisorIdeal K (D + Finsupp.single P 1) ≤ divisorIdeal K D :=
    divisorIdeal_anti K le_self_add
  have hle : divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g} ≤
      divisorIdeal K D ⊔ Ideal.span {g} := sup_le_sup_right hJ _
  have e1 : divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g} ⊔ divisorIdeal K D =
      divisorIdeal K D ⊔ Ideal.span {g} :=
    le_antisymm (sup_le hle le_sup_left) (sup_le le_sup_right (le_sup_of_le_left le_sup_right))
  have hcomap : Submodule.comap (divisorIdeal K D).subtype
      (divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g}) =
      Submodule.comap φ (P.ideal ⊔ Ideal.span {g} * Submodule.map φ ⊤) := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hx
      obtain ⟨j, hj, c, hc, hjc⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have ha : a ∈ divisorIdeal K D := by
        refine mem_divisorIdeal_of_mul_mem K hgD ?_
        have h1 : g * a = (x : O) - j := by rw [← hjc]; ring
        rw [h1]
        exact (divisorIdeal K D).sub_mem x.2 (hJ hj)
      have hx' : x = (⟨j, hJ hj⟩ : divisorIdeal K D) + g • (⟨a, ha⟩ : divisorIdeal K D) :=
        Subtype.ext (by rw [← hjc, mul_comm]; rfl)
      rw [hx', map_add, map_smul, smul_eq_mul]
      exact Submodule.add_mem_sup ((hφ.mem_ideal_iff _).mpr hj)
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g)
          (Submodule.mem_map_of_mem Submodule.mem_top))
    · intro hx
      obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp hx
      obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
      obtain ⟨a, -, rfl⟩ := Submodule.mem_map.mp hz
      have h1 : φ (x - g • a) ∈ P.ideal := by
        rw [map_sub, map_smul, smul_eq_mul, ← hpy, add_sub_cancel_right]
        exact hp
      have h2 : (x : O) = ((x - g • a : divisorIdeal K D) : O) + (a : O) * g := by
        rw [Submodule.coe_sub, Submodule.coe_smul, smul_eq_mul]
        ring
      rw [h2]
      exact Submodule.add_mem_sup ((hφ.mem_ideal_iff _).mp h1)
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
  have hfin : Module.length O (O ⧸ (P.ideal ⊔ Submodule.map φ ⊤)) ≠ ⊤ :=
    length_quotient_sup_ne_top hO P hφ.range_not_le
  have hprime : ∀ a : O, a * g ∈ P.ideal → a ∈ P.ideal := fun a ha =>
    (P.isPrime.mem_or_mem ha).resolve_right hgP
  rw [length_quotient_eq_relLength_add hle, add_comm]
  congr 1
  calc relLength (divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g})
        (divisorIdeal K D ⊔ Ideal.span {g})
      = relLength (divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g}) (divisorIdeal K D) := by
        rw [← e1, relLength_sup_left]
    _ = relLength (Submodule.comap (divisorIdeal K D).subtype
          (divisorIdeal K (D + Finsupp.single P 1) ⊔ Ideal.span {g})) ⊤ := by
        rw [relLength_comap, Submodule.map_subtype_top]
    _ = relLength (P.ideal ⊔ Ideal.span {g} * Submodule.map φ ⊤) (Submodule.map φ ⊤) := by
        rw [hcomap, relLength_comap]
    _ = Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) :=
        relLength_sup_span_mul P.ideal (Submodule.map φ ⊤) g hprime hfin
theorem length_quotient_divisorIdeal_sup_span (hO : DivisorChain O) (g : O) (L : Divisor O)
    (hg : ∀ P ∈ L.support, g ∉ P.ideal) :
    Module.length O (O ⧸ (divisorIdeal K L ⊔ Ideal.span {g})) =
      L.sum fun P n => (n : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) := by
  induction L using Divisor.induction_on with
  | h0 =>
    rw [divisorIdeal_zero, top_sup_eq, Finsupp.sum_zero_index]
    exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)
  | hadd D P ih =>
    have hgP : g ∉ P.ideal := hg P (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
      omega)
    have hgD : ∀ Q ∈ D.support, g ∉ Q.ideal := fun Q hQ => hg Q (by
      rw [Finsupp.mem_support_iff] at hQ ⊢
      rw [Finsupp.add_apply]
      omega)
    rw [length_quotient_divisorIdeal_add_single K hO hgD hgP, ih hgD,
      Finsupp.sum_add_index' (fun _ => by rw [Nat.cast_zero, zero_mul])
        (fun _ _ _ => by rw [Nat.cast_add, add_mul]),
      Finsupp.sum_single_index (by rw [Nat.cast_zero, zero_mul]), Nat.cast_one, one_mul]
theorem exists_length_quotient_add_le (hO : DivisorChain O) (D : Divisor O) (P : PrimeDivisor O) :
    ∃ κ : ℕ, ∀ L : Divisor O, (∀ Q, D Q ≠ 0 → L Q = 0) →
      Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L)) +
          Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D)) ≤
        Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))) + κ := by
  obtain ⟨φ, hφ⟩ := exists_isTransfer K D P
  have hfin : Module.length O (O ⧸ (P.ideal ⊔ Submodule.map φ ⊤)) ≠ ⊤ :=
    length_quotient_sup_ne_top hO P hφ.range_not_le
  refine ⟨(Module.length O (O ⧸ (P.ideal ⊔ Submodule.map φ ⊤))).toNat, fun L hL => ?_⟩
  rw [ENat.natCast_toNat hfin]
  have hJ : divisorIdeal K (D + Finsupp.single P 1) ≤ divisorIdeal K D :=
    divisorIdeal_anti K le_self_add
  have hle : divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1) ≤
      divisorIdeal K L ⊔ divisorIdeal K D := sup_le_sup_left hJ _
  have e1 : divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1) ⊔ divisorIdeal K D =
      divisorIdeal K L ⊔ divisorIdeal K D :=
    le_antisymm (sup_le hle le_sup_right) (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
  have hcomap : Submodule.comap (divisorIdeal K D).subtype
      (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1)) ≤
      Submodule.comap φ (divisorIdeal K L ⊔ P.ideal) := by
    intro x hx
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.mp hx
    have haD : a ∈ divisorIdeal K D := by
      have h1 : a = (x : O) - j := by rw [← haj]; ring
      rw [h1]
      exact (divisorIdeal K D).sub_mem x.2 (hJ hj)
    have hx' : x = (⟨a, haD⟩ : divisorIdeal K D) + ⟨j, hJ hj⟩ := Subtype.ext haj.symm
    rw [Submodule.mem_comap, hx', map_add]
    exact Submodule.add_mem_sup (hφ.mem_divisorIdeal hL ha) ((hφ.mem_ideal_iff _).mpr hj)
  have h1 : relLength (divisorIdeal K L ⊔ P.ideal) (Submodule.map φ ⊤) ≤
      relLength (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))
        (divisorIdeal K L ⊔ divisorIdeal K D) := by
    calc relLength (divisorIdeal K L ⊔ P.ideal) (Submodule.map φ ⊤)
        = relLength (Submodule.comap φ (divisorIdeal K L ⊔ P.ideal)) ⊤ := by rw [relLength_comap]
      _ ≤ relLength (Submodule.comap (divisorIdeal K D).subtype
            (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))) ⊤ :=
          relLength_anti_left hcomap ⊤
      _ = relLength (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))
            (divisorIdeal K D) := by rw [relLength_comap, Submodule.map_subtype_top]
      _ = relLength (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))
            (divisorIdeal K L ⊔ divisorIdeal K D) := by rw [← e1, relLength_sup_left]
  have h2 := length_quotient_eq_relLength_add
    (le_sup_left : divisorIdeal K L ⊔ P.ideal ≤ divisorIdeal K L ⊔ P.ideal ⊔ Submodule.map φ ⊤)
  rw [relLength_sup_left] at h2
  have hle3 : P.ideal ⊔ Submodule.map φ ⊤ ≤ divisorIdeal K L ⊔ P.ideal ⊔ Submodule.map φ ⊤ :=
    sup_le_sup_right le_sup_right _
  have h3 : Module.length O (O ⧸ (divisorIdeal K L ⊔ P.ideal ⊔ Submodule.map φ ⊤)) ≤
      Module.length O (O ⧸ (P.ideal ⊔ Submodule.map φ ⊤)) :=
    Module.length_le_of_surjective (Submodule.factor hle3) (Submodule.factor_surjective hle3)
  rw [sup_comm P.ideal, h2, length_quotient_eq_relLength_add hle]
  calc relLength (divisorIdeal K L ⊔ P.ideal) (Submodule.map φ ⊤) +
        Module.length O (O ⧸ (divisorIdeal K L ⊔ P.ideal ⊔ Submodule.map φ ⊤)) +
        Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D))
      ≤ relLength (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))
          (divisorIdeal K L ⊔ divisorIdeal K D) +
        Module.length O (O ⧸ (P.ideal ⊔ Submodule.map φ ⊤)) +
        Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D)) :=
        add_le_add (add_le_add h1 h3) le_rfl
    _ = _ := add_right_comm _ _ _
theorem exists_bound_sum_length_quotient_divisorIdeal (hO : DivisorChain O) (D : Divisor O) :
    ∃ K' : ℕ, ∀ L : Divisor O, (∀ Q, D Q ≠ 0 → L Q = 0) →
      (D.sum fun P e => (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L))) ≤
        Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D)) + K' := by
  induction D using Divisor.induction_on with
  | h0 => exact ⟨0, fun L _ => by rw [Finsupp.sum_zero_index]; exact zero_le⟩
  | hadd D P ih =>
    obtain ⟨K₀, hK₀⟩ := ih
    obtain ⟨κ, hκ⟩ := exists_length_quotient_add_le K hO D P
    refine ⟨K₀ + κ, fun L hL => ?_⟩
    have hL' : ∀ Q, D Q ≠ 0 → L Q = 0 := fun Q hQ => hL Q (by
      rw [Finsupp.add_apply]
      omega)
    rw [Finsupp.sum_add_index' (fun _ => by rw [Nat.cast_zero, zero_mul])
        (fun _ _ _ => by rw [Nat.cast_add, add_mul]),
      Finsupp.sum_single_index (by rw [Nat.cast_zero, zero_mul]), Nat.cast_one, one_mul,
      Nat.cast_add]
    calc (D.sum fun P e => (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L))) +
          Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L))
        ≤ Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D)) + K₀ +
          Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L)) := add_le_add (hK₀ L hL') le_rfl
      _ = Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L)) +
          Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K D)) + K₀ := by
          rw [add_right_comm, add_comm (Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L)))]
      _ ≤ Module.length O (O ⧸ (divisorIdeal K L ⊔ divisorIdeal K (D + Finsupp.single P 1))) + κ +
          K₀ := add_le_add (hκ L hL') le_rfl
      _ = _ := by rw [add_assoc, add_comm (κ : ℕ∞)]
theorem exists_bound_sum_length_quotient (hO : DivisorChain O) {g : O} (hg : g ≠ 0) :
    ∃ K' : ℕ, ∀ L : Divisor O, (∀ P ∈ L.support, g ∉ P.ideal) →
      ((div K g).sum fun P e => (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K L))) ≤
        Module.length O (O ⧸ (divisorIdeal K L ⊔ Ideal.span {g})) + K' := by
  obtain ⟨K', hK'⟩ := exists_bound_sum_length_quotient_divisorIdeal K hO (div K g)
  refine ⟨K', fun L hL => ?_⟩
  have h := hK' L fun Q hQ => by
    by_contra hLQ
    exact hL Q (Finsupp.mem_support_iff.mpr hLQ)
      ((mem_support_div K hg Q).mp (Finsupp.mem_support_iff.mpr hQ))
  rwa [divisorIdeal_div K hg] at h
theorem length_quotient_span_sup_span (hO : DivisorChain O) {u : O} (hu : u ≠ 0) (g : O)
    (h : ∀ P : PrimeDivisor O, u ∈ P.ideal → g ∉ P.ideal) :
    Module.length O (O ⧸ (Ideal.span {u} ⊔ Ideal.span {g})) =
      (div K u).sum fun P n => (n : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) := by
  rw [← length_quotient_divisorIdeal_sup_span K hO g (div K u) fun P hP =>
    h P ((mem_support_div K hu P).mp hP), divisorIdeal_div K hu]
theorem sum_div_length_quotient_comm (hO : DivisorChain O) {g u : O} (hg : g ≠ 0) (hu : u ≠ 0)
    (h : ∀ P : PrimeDivisor O, u ∈ P.ideal → g ∉ P.ideal) :
    ((div K u).sum fun P n => (n : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g}))) =
      (div K g).sum fun P e => (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {u})) := by
  rw [← length_quotient_span_sup_span K hO hu g h, sup_comm,
    length_quotient_span_sup_span K hO hg u fun P hgP huP => h P huP hgP]
theorem exists_bound_sum_length_quotient_nsmul (hO : DivisorChain O) {g : O} (hg : g ≠ 0) :
    ∃ K' : ℕ, ∀ L : Divisor O, (∀ P ∈ L.support, g ∉ P.ideal) → ∀ n : ℕ,
      ((div K g).sum fun P e =>
        (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K (n • L)))) ≤
      n * (L.sum fun P m => (m : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g}))) + K' := by
  obtain ⟨K', hK'⟩ := exists_bound_sum_length_quotient K hO hg
  refine ⟨K', fun L hL n => ?_⟩
  have hnL : ∀ P ∈ (n • L).support, g ∉ P.ideal := fun P hP => hL P (Finsupp.support_smul hP)
  have h := hK' (n • L) hnL
  rw [length_quotient_divisorIdeal_sup_span K hO g (n • L) hnL,
    Finsupp.sum_smul_index' (fun _ => by rw [Nat.cast_zero, zero_mul])] at h
  have hsum : (L.sum fun P m =>
      ((n • m : ℕ) : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g}))) =
      n * L.sum fun P m => (m : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g})) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by rw [smul_eq_mul, Nat.cast_mul, mul_assoc]
  rwa [hsum] at h
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial WithZero
namespace Chart
theorem eq_span_prime_of_dvr {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (𝔭 : Ideal R) [h𝔭 : 𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)] :
    ∃ π : R, Prime π ∧ 𝔭 = Ideal.span {π} := by
  have hmax := Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭)
  have hne : 𝔭 ≠ ⊥ := fun h => IsDiscreteValuationRing.not_a_field (Localization.AtPrime 𝔭)
    (hmax.symm.trans ((Ideal.map_eq_bot_iff_le_ker _).2 (h.le.trans bot_le)))
  obtain ⟨π, hπ𝔭, hπ⟩ := h𝔭.exists_mem_prime_of_ne_bot hne
  refine ⟨π, hπ, ?_⟩
  have hπp : (Ideal.span {π} : Ideal R).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hdisj : Disjoint (𝔭.primeCompl : Set R) (Ideal.span {π} : Ideal R) :=
    Set.disjoint_left.2 fun a ha ha' => ha ((Ideal.span_singleton_le_iff_mem _).2 hπ𝔭 ha')
  have hmp : (Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (Ideal.span {π})).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl _ _ hπp hdisj
  have hmne : Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (Ideal.span {π}) ≠ ⊥ := fun h =>
    hπ.ne_zero ((injective_iff_map_eq_zero _).1
      (IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors) π
      ((Ideal.map_eq_bot_iff_le_ker _).1 h (Ideal.mem_span_singleton_self π)))
  have h1 := IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl (Localization.AtPrime 𝔭)
    hπp hdisj
  rw [IsLocalRing.eq_maximalIdeal (hmp.isMaximal hmne), Localization.AtPrime.under_maximalIdeal] at h1
  exact h1
theorem isUnit_of_dvd_of_dvd {k : Type*} [Field k] (π f₀ f₁ : MvPolynomial (Fin 2) k) (hf₀ : f₀ ≠ 0)
    (hf₁ : f₁ ≠ 0) (h0 : f₀.degreeOf 1 = 0) (h1 : f₁.degreeOf 0 = 0) (hπ0 : π ∣ f₀) (hπ1 : π ∣ f₁) :
    IsUnit π := by
  obtain ⟨g₀, rfl⟩ := hπ0
  obtain ⟨g₁, rfl⟩ := hπ1
  have hπ : π ≠ 0 := left_ne_zero_of_mul hf₀
  rw [degreeOf_mul_eq hπ (right_ne_zero_of_mul hf₀)] at h0
  rw [degreeOf_mul_eq hπ (right_ne_zero_of_mul hf₁)] at h1
  have hC : π = MvPolynomial.C (π.coeff 0) := by
    rw [← totalDegree_eq_zero_iff_eq_C, totalDegree_eq_zero_iff]
    intro m hm i
    have hi : π.degreeOf i = 0 := by
      revert i
      rw [Fin.forall_fin_two]
      exact ⟨by omega, by omega⟩
    have := degreeOf_le_iff.1 (le_of_eq hi) m hm
    omega
  have hc : π.coeff 0 ≠ 0 := fun h => hπ (by rw [hC, h, map_zero])
  rw [hC]
  exact (IsUnit.mk0 _ hc).map MvPolynomial.C
theorem degreeOf_aeval_X {σ k : Type*} [Field k] {i j : σ} (hij : i ≠ j) (g : Polynomial k) :
    (Polynomial.aeval (MvPolynomial.X j : MvPolynomial σ k) g).degreeOf i = 0 := by
  classical
  have hv : (Polynomial.aeval (MvPolynomial.X j : MvPolynomial σ k) g).vars ⊆ {j} := by
    induction g using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact (vars_add_subset _ _).trans (Finset.union_subset hp hq)
    | monomial n a =>
      rw [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
      refine (vars_mul _ _).trans
        (Finset.union_subset (by rw [vars_C]; exact Finset.empty_subset _) ?_)
      exact (vars_pow _ _).trans (by rw [vars_X])
  by_contra h
  exact hij (Finset.mem_singleton.1 (hv (mem_vars_iff_degreeOf_ne_zero.2 h)))
section Plane
variable {k L : Type*} [Field k] [Field L] [Algebra k L] (s : Fin 2 → L)
  (hs : AlgebraicIndependent k s)
include hs
theorem exists_adjoin_singleton_disjoint (𝔭 : Ideal (Algebra.adjoin k (Set.range s))) [𝔭.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime 𝔭)] :
    ∃ j, ∀ a : Algebra.adjoin k (Set.range s), a ∈ 𝔭 → (a : L) ∈ Algebra.adjoin k {s j} → a = 0 := by
  have hufd : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range s)) :=
    hs.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨π, hπ, h𝔭⟩ := eq_span_prime_of_dvr 𝔭
  have key : ∀ (j : Fin 2) (a : Algebra.adjoin k (Set.range s)), a ∈ 𝔭 → a ≠ 0 →
      (a : L) ∈ Algebra.adjoin k {s j} → ∃ q : MvPolynomial (Fin 2) k, q ≠ 0 ∧
        hs.aevalEquiv.symm π ∣ q ∧ ∀ i, i ≠ j → q.degreeOf i = 0 := by
    intro j a ha𝔭 ha0 ha
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    have hq : hs.aevalEquiv (Polynomial.aeval (MvPolynomial.X j) g) = a := by
      apply Subtype.ext
      rw [← hg]
      show algebraMap (Algebra.adjoin k (Set.range s)) L (hs.aevalEquiv _) = _
      rw [hs.algebraMap_aevalEquiv, ← Polynomial.aeval_algHom_apply, aeval_X]
      rfl
    refine ⟨Polynomial.aeval (MvPolynomial.X j) g, fun h => ?_, ?_, fun i hij =>
      degreeOf_aeval_X hij g⟩
    · rw [h, map_zero] at hq
      exact ha0 hq.symm
    · have hd := map_dvd hs.aevalEquiv.symm (Ideal.mem_span_singleton.1 (h𝔭 ▸ ha𝔭))
      rwa [← hq, AlgEquiv.symm_apply_apply] at hd
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀𝔭, ha₀, ha₀0⟩ := hcon 0
  obtain ⟨a₁, ha₁𝔭, ha₁, ha₁0⟩ := hcon 1
  obtain ⟨q₀, hq₀, hd₀, hdeg₀⟩ := key 0 a₀ ha₀𝔭 ha₀0 ha₀
  obtain ⟨q₁, hq₁, hd₁, hdeg₁⟩ := key 1 a₁ ha₁𝔭 ha₁0 ha₁
  have hunit := (isUnit_of_dvd_of_dvd _ q₀ q₁ hq₀ hq₁ (hdeg₀ 1 (by decide)) (hdeg₁ 0 (by decide))
    hd₀ hd₁).map hs.aevalEquiv
  rw [AlgEquiv.apply_symm_apply] at hunit
  exact hπ.not_isUnit hunit
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isIntegral_of_noether [FiniteDimensional (IntermediateField.adjoin k (Set.range s)) L]
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range s)) L] (x : L)
    (hx : ∀ w : Valuation L ℤᵐ⁰, (∃ y, w y = exp (-1 : ℤ)) →
      (∀ a : L, IsIntegral (Algebra.adjoin k (Set.range s)) a → w a ≤ 1) →
      (∃ j, ∀ a ∈ IntermediateField.adjoin k {s j}, a ≠ 0 → w a = 1) → w x ≤ 1) :
    IsIntegral (Algebra.adjoin k (Set.range s)) x := by
  have hnoeth : IsNoetherianRing (Algebra.adjoin k (Set.range s)) :=
    isNoetherianRing_of_ringEquiv _ hs.aevalEquiv.toRingEquiv
  have hufd : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range s)) :=
    hs.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  refine isIntegral_of_dvr_valuations (Algebra.adjoin k (Set.range s))
    (IntermediateField.adjoin k (Set.range s)) L x ?_
  intro 𝔭 h𝔭 hdvr halg htower hded hfrac v
  have hB : ∀ c : Localization.AtPrime 𝔭,
      v.valuation L (algebraMap (Localization.AtPrime 𝔭) L c) ≤ 1 := fun c =>
    v.valuation_le_one ⟨_, isIntegral_algebraMap⟩
  refine hx (v.valuation L) (v.valuation_exists_uniformizer L)
    (fun a ha => v.valuation_le_one ⟨a, ha.tower_top⟩) ?_
  obtain ⟨j, hj⟩ := exists_adjoin_singleton_disjoint s hs 𝔭
  have hunit : ∀ a ∈ Algebra.adjoin k {s j}, a ≠ 0 → v.valuation L a = 1 := by
    intro a ha ha0
    have haP : a ∈ Algebra.adjoin k (Set.range s) :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_range_self j)) ha
    have hnot : (⟨a, haP⟩ : Algebra.adjoin k (Set.range s)) ∉ 𝔭 := fun h =>
      ha0 (congrArg Subtype.val (hj ⟨a, haP⟩ h ha))
    obtain ⟨u, hu⟩ := (IsLocalization.map_units (Localization.AtPrime 𝔭)
      (⟨⟨a, haP⟩, hnot⟩ : 𝔭.primeCompl)).exists_right_inv
    have hcast : algebraMap (Localization.AtPrime 𝔭) L
        (algebraMap (Algebra.adjoin k (Set.range s)) (Localization.AtPrime 𝔭) ⟨a, haP⟩) = a :=
      (IsScalarTower.algebraMap_apply (Algebra.adjoin k (Set.range s)) (Localization.AtPrime 𝔭) L
        ⟨a, haP⟩).symm
    have h1 : a * algebraMap (Localization.AtPrime 𝔭) L u = 1 := by
      have h := congrArg (algebraMap (Localization.AtPrime 𝔭) L) hu
      rwa [map_mul, map_one, hcast] at h
    have h2 : v.valuation L a ≤ 1 := hcast ▸ hB _
    have h3 := hB u
    rw [← inv_eq_of_mul_eq_one_right h1, map_inv₀] at h3
    refine le_antisymm h2 ?_
    by_contra h
    rw [not_le] at h
    have hv0 : v.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact absurd h3 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 hv0)).2 h))
  refine ⟨j, fun a ha ha0 => ?_⟩
  obtain ⟨r, hr, q, hq, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 ha
  have hq0 : q ≠ 0 := fun h => ha0 (by rw [h, div_zero])
  have hr0 : r ≠ 0 := fun h => ha0 (by rw [h, zero_div])
  rw [map_div₀, hunit r hr hr0, hunit q hq hq0, div_one]
end Plane
theorem finite_separable_of_natDegree_le {F L : Type*} [Field F] [Field L] [Algebra F L] (p : ℕ)
    [CharP F p] (n : ℕ) (hn : n < p)
    (hdeg : ∀ a : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.natDegree ≤ n ∧ Polynomial.aeval a Q = 0)
    {ι : Type*} [Finite ι] (t : ι → L)
    (hgen : ∀ E : Subfield L, (∀ a : F, algebraMap F L a ∈ E) → (∀ i, t i ∈ E) → ∀ z, z ∈ E) :
    FiniteDimensional F L ∧ Algebra.IsSeparable F L := by
  have hint : ∀ a : L, IsIntegral F a := fun a => by
    obtain ⟨Q, hQ0, -, hQa⟩ := hdeg a
    exact isAlgebraic_iff_isIntegral.1 ⟨Q, hQ0, hQa⟩
  constructor
  · have htop : IntermediateField.adjoin F (Set.range t) = ⊤ :=
      eq_top_iff.2 fun z _ => hgen (IntermediateField.adjoin F (Set.range t)).toSubfield
        (fun a => (IntermediateField.adjoin F (Set.range t)).algebraMap_mem a)
        (fun i => IntermediateField.subset_adjoin F _ (Set.mem_range_self i)) z
    have hfin : FiniteDimensional F (IntermediateField.adjoin F (Set.range t)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => hint x
    exact ((IntermediateField.equivOfEq htop).trans
      IntermediateField.topEquiv).toLinearEquiv.finiteDimensional
  · refine ⟨fun a => ?_⟩
    obtain ⟨Q, hQ0, hQn, hQa⟩ := hdeg a
    have hirr := minpoly.irreducible (hint a)
    rcases Polynomial.separable_or p hirr with h | ⟨-, g, hg, hgf⟩
    · exact h
    · exfalso
      have h1 : (minpoly F a).natDegree ≤ n :=
        (Polynomial.natDegree_le_of_dvd (minpoly.dvd F a hQa) hQ0).trans hQn
      rw [← hgf, Polynomial.natDegree_expand] at h1
      have h2 : 0 < g.natDegree := hg.natDegree_pos
      exact absurd ((Nat.le_mul_of_pos_left p h2).trans h1) (not_le.2 hn)
end Chart
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open IsDedekindDomain
section Normalized
variable {K : Type*} [Field K]
theorem valuation_eq_of_isEquiv {v w : Valuation K (WithZero (Multiplicative ℤ))}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  have key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ WithZero.exp (-1 : ℤ) := fun z hz => by
    rcases eq_or_ne z 0 with rfl | h0
    · exact zero_le
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_one_iff] at hz
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  have h1 : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) :=
    WithZero.exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
  obtain ⟨ρ, hρ⟩ := hw (WithZero.exp (-1 : ℤ))
  have hwπ : w π = WithZero.exp (-1 : ℤ) := by
    refine le_antisymm (key _ (h.lt_one_iff_lt_one.mp (hπ ▸ h1))) ?_
    rw [← hρ]
    refine (h ρ π).mp ?_
    rw [hπ]
    exact key _ (h.lt_one_iff_lt_one.mpr (hρ ▸ h1))
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
    have e : v (π ^ (-(v x).log)) = v x := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hvx]
    calc v x = v (π ^ (-(v x).log)) := e.symm
      _ = w (π ^ (-(v x).log)) := by rw [map_zpow₀, map_zpow₀, hπ, hwπ]
      _ = w x := h.eq_iff.mp e
theorem valuation_le_one_of_isIntegral {A Γ : Type*} [CommRing A] [Algebra A K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hA : ∀ a : A, v (algebraMap A K a) ≤ 1) {x : K} (hx : IsIntegral A x) : v x ≤ 1 := by
  obtain ⟨p, hp, hpx⟩ := hx
  let φ : A →+* v.valuationSubring := (algebraMap A K).codRestrict v.valuationSubring hA
  refine (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp
    ⟨p.map φ, hp.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx
end Normalized
section Dedekind
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]
theorem exists_unique_heightOneSpectrum (v : Valuation K (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) :
    ∃! V : HeightOneSpectrum R, v = V.valuation K := by
  let P : Ideal R :=
    { carrier := {r | v (algebraMap R K r) < 1}
      add_mem' := fun {a b} ha hb => by
        change v (algebraMap R K (a + b)) < 1
        rw [map_add]
        exact (v.map_add _ _).trans_lt (max_lt ha hb)
      zero_mem' := by
        change v (algebraMap R K 0) < 1
        simp
      smul_mem' := fun c x hx => by
        change v (algebraMap R K (c * x)) < 1
        rw [map_mul, map_mul]
        exact mul_lt_of_le_one_of_lt (hR c) hx }
  have hP : ∀ r, r ∈ P ↔ v (algebraMap R K r) < 1 := fun r => Iff.rfl
  have hPprime : P.IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      simp [hP] at h1
    · by_contra hcon
      rw [not_or, hP, hP, not_lt, not_lt] at hcon
      rw [hP, map_mul, map_mul, le_antisymm (hR a) hcon.1, le_antisymm (hR b) hcon.2,
        one_mul] at hab
      exact lt_irrefl _ hab
  have hexp : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) :=
    WithZero.exp_lt_one_iff.mpr (by norm_num)
  have hP0 : P ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) π
    have hs0 : v (algebraMap R K s) ≠ 0 := (Valuation.ne_zero_iff v).mpr
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)
    intro hbot
    have ha : a ∈ P := by
      rw [hP, ← div_mul_cancel₀ (v (algebraMap R K a)) hs0, ← map_div₀, hπ]
      exact mul_lt_of_lt_of_le_one hexp (hR s)
    rw [hbot, Ideal.mem_bot] at ha
    rw [ha, map_zero, zero_div, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let V : HeightOneSpectrum R := ⟨P, hPprime, hP0⟩
  have hd : ∀ d : P.primeCompl, v (algebraMap R K d) = 1 := fun d =>
    le_antisymm (hR d) (not_lt.mp d.2)
  have hle : ∀ x : K, V.valuation K x ≤ 1 → v x ≤ 1 := fun x hx => by
    obtain ⟨n, d, hnd⟩ := V.exists_primeCompl_mul_eq_of_integer x hx
    have h := congrArg v hnd
    rw [map_mul, hd d, mul_one] at h
    rw [h]
    exact hR n
  have hlt : ∀ x : K, V.valuation K x < 1 → v x < 1 := fun x hx => by
    obtain ⟨n, d, hnd⟩ := V.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∈ P := (V.valuation_lt_one_iff_mem (K := K) n).mp (by
      change V.valuation K (algebraMap R K n) < 1
      rw [← hnd, map_mul, V.valuation_eq_one_iff_notMem.mpr d.2, mul_one]
      exact hx)
    have h := congrArg v hnd
    rw [map_mul, hd d, mul_one] at h
    rw [h]
    exact hn
  have hequiv : (V.valuation K).IsEquiv v :=
    Valuation.isEquiv_iff_val_le_one.mpr fun {x} => ⟨hle x, fun hx => by
      by_contra hcon
      rw [not_le] at hcon
      have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hcon
      have h2 := hlt x⁻¹ (by
        rw [map_inv₀]
        exact (inv_lt_one₀ (zero_lt_one.trans hcon)).mpr hcon)
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hx0))] at h2
      exact absurd hx (not_le.mpr h2)⟩
  have hV : v = V.valuation K :=
    (valuation_eq_of_isEquiv (V.valuation_surjective K) hv hequiv).symm
  exact ⟨V, hV, fun W hW => HeightOneSpectrum.valuation_injective K (hW.symm.trans hV)⟩
end Dedekind
section Place
variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Ring.DimensionLEOne B]
  {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [Module.Finite B (integralClosure B K)]
variable (B K) in
theorem exists_unique_place (v : Valuation K (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hB : ∀ b : B, v (algebraMap B K b) ≤ 1) :
    ∃! V : HeightOneSpectrum (integralClosure B K), v = V.valuation K :=
  exists_unique_heightOneSpectrum (integralClosure B K) K v hv fun t =>
    valuation_le_one_of_isIntegral v hB t.2
variable (B K) in
noncomputable def placeEquiv : HeightOneSpectrum (integralClosure B K) ≃
    {v : Valuation K (WithZero (Multiplicative ℤ)) //
      Function.Surjective v ∧ ∀ b : B, v (algebraMap B K b) ≤ 1} :=
  Equiv.ofBijective
    (fun V => ⟨V.valuation K, V.valuation_surjective K, valuation_algebraMap_le_one V⟩)
    ⟨fun _ _ h => HeightOneSpectrum.valuation_injective K (congrArg Subtype.val h), fun v =>
      have ⟨V, hV, _⟩ := exists_unique_place B K v.1 v.2.1 v.2.2
      ⟨V, Subtype.ext hV.symm⟩⟩
theorem valuation_placeEquiv_symm (v : {v : Valuation K (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ b : B, v (algebraMap B K b) ≤ 1}) :
    ((placeEquiv B K).symm v).valuation K = v :=
  congrArg Subtype.val ((placeEquiv B K).apply_symm_apply v)
variable [IsLocalRing B]
omit [IsDomain B] [IsNoetherianRing B] [IsFractionRing B K] in
theorem algebraMap_quotient_place_surjective {k : Type*} [Field k] [IsAlgClosed k] (φ : B →+* k)
    (hφ : Function.Surjective φ) (V : HeightOneSpectrum (integralClosure B K)) :
    Function.Surjective (algebraMap B (integralClosure B K ⧸ V.asIdeal)) := by
  have hker : RingHom.ker φ ≤ RingHom.ker (algebraMap B (integralClosure B K ⧸ V.asIdeal)) := by
    intro x hx
    have hxm := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ) hx
    rw [← under_eq_maximalIdeal V] at hxm
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B (integralClosure B K)
      (integralClosure B K ⧸ V.asIdeal), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hxm
  let ψ : k →+* integralClosure B K ⧸ V.asIdeal :=
    RingHom.liftOfSurjective φ hφ ⟨algebraMap B _, hker⟩
  have hψ : ψ.comp φ = algebraMap B (integralClosure B K ⧸ V.asIdeal) :=
    RingHom.liftOfSurjective_comp φ hφ ⟨algebraMap B _, hker⟩
  have hint : ψ.IsIntegral := RingHom.IsIntegral.tower_top φ ψ (by
    rw [hψ]
    exact algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite B _))
  have := V.isPrime
  rw [← hψ]
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral ψ hint).2.comp hφ
theorem resDeg_eq_one_of_surjective {k : Type*} [Field k] [IsAlgClosed k] (φ : B →+* k)
    (hφ : Function.Surjective φ) (V : HeightOneSpectrum (integralClosure B K)) : resDeg V = 1 := by
  have : IsSimpleModule B (integralClosure B K ⧸ V.asIdeal) := by
    rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := integralClosure B K ⧸ V.asIdeal) (algebraMap_quotient_place_surjective φ hφ V)]
    have := V.isMaximal
    let _ := Ideal.Quotient.field V.asIdeal
    exact instIsSimpleModule _
  rw [resDeg, Module.length_eq_one, ENat.toNat_one]
end Place
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
section Frame
noncomputable section
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 DU BLL AYR BIO BBT _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)
structure PacketFrame (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) (lam mu : Ω)
    (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)) : Prop where
  lam_mem : lam ∈ Set.range (RCN135.polynomialEmbedding K)
  mu_mem : mu ∈ Set.range (RCN135.polynomialEmbedding K)
  frame : ∀ g, (geometry g).data.lam = lam ∧ (geometry g).data.mu = mu
  value : ∀ (j : Fin 3) (a : Curve P),
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω a.2.1)
      (![(suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zProjection a.2,
        (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzProjection a.2,
        (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).NV a.2] j) =
      RCN002.coordinateEvaluation Ω a.2.1 (DSG lam mu j)
  cost : ∀ a, (budget a).zCost =
      (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2 ∧
    (budget a).yzCost =
      (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2 ∧
    (budget a).allCost =
      (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2
  moving : scale * (∑ a ∈ active P SZ, (budget a).movingCost) ≤ price (rawFirstFlag t y r) z u v
  point_budget : ∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN (RingHom.id Ω) P.F SZ Q A scale z u v
def CurveCount (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F)
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (moving : Curve P → ℕ) (o : ℕ → Curve P → ℕ) : Prop :=
  ∀ n : ℕ, ∀ a ∈ active P SZ, ∀ delay : ℕ, 1 ≤ delay →
    RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1 + delay) ∉ a.2.1 →
    3 * n * (RCN264.componentSeeds Ω (P.stage a.1).G
        (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
        (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F)
        (KK K P.F P.selected P.seeds a.1)
        (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2).card ≤
      n * (budget a).weightedCost (cutR (w + delay) r (y - r) (t - y)) +
        4 * (w + delay) * (n * moving a + o n a)
def LevelCount (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) (moving : Curve P → ℕ) (Lam : ℕ) : Prop :=
  3 * SZ.d * scale * (∑ a ∈ active P SZ, multiplicity P hp a * moving a) + scale * Lam ≤
    SZ.d * price (cellCutR t y r) z u v + 4 * (w + 1) * price SZ.flag z u v
def ExchangeCount (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (o : ℕ → Curve P → ℕ) (Lam Kc : ℕ) : Prop :=
  ∀ n : ℕ, 3 * SZ.d * (∑ a ∈ active P SZ, multiplicity P hp a * o n a) ≤ n * Lam + Kc
theorem mixed_swap (p q r : FlagDegree) : flagMixed p q r = flagMixed p r q := by
  unfold flagMixed
  ring
theorem swap_weighted_sum {A : Type} [Fintype A]
    (scale : ℕ) (weight : Fin 3 → ℕ) (mu : A → ℕ) (degree : Fin 3 → A → ℕ) :
    (∑ j : Fin 3, weight j * (scale * ∑ a, mu a * degree j a)) =
      scale * (∑ a, mu a * (∑ j : Fin 3, weight j * degree j a)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem sum_scaled_prices (W : FlagDegree) (scale coeff z u v : ℕ) (fixed : Fin 3 → ℕ) :
    (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * (scale * fixed j + coeff * price (MovingFiberThreeSources6811.direction j) z u v)) =
      scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * fixed j) + coeff * price W z u v := by
  simp only [Nat.mul_add, Finset.sum_add_distrib, Nat.mul_left_comm, ← Finset.mul_sum]
  rw [GEV]
theorem exists_packet_frame
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ SP SQ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433) :
    ∃ (lam mu : Ω) (geometry : ∀ g, ABN (P.stage g))
      (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)),
      PacketFrame P hp SZ (stageScale SZ delta)
        (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
        lam mu geometry budget ∧
      ∀ W : FlagDegree, 3 * stageScale SZ delta *
          (∑ a ∈ active P SZ, multiplicity P hp a * ordinary P hp geometry a W) ≤
        stageScale SZ delta * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j *
            flagMixed ⟨t - y, y - r, r⟩ (ASY t y r j) (MovingFiberThreeSources6811.direction j)) +
          4 * (w + 1) * price W
            (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
            (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
            (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag) := by
  have hrlo := P.rlow
  have hrhi := packet_r_le P
  have hylo := P.ylow
  have hyhi := packet_y_le P
  have hyt := P.yt
  have hthi := packet_t_le P
  have hflags (g : RCN222.GeometricFactor K P.F) : (CO K g).yz + (CO K g).all < 2130706433 ∧
      (CO K g).all < 2130706433 ∧
      (CO K g).zOnly + (CO K g).yz + (CO K g).all < 2130706433 := by
    have hh := P.stage_flag g
    omega
  have hmixed (g : RCN222.GeometricFactor K P.F) := BoundaryTailGates.reduced_gate
    (CO K g) t y r (by omega) (by omega) (by omega) (by omega) (by omega)
    (P.stage_flag g).1 (P.stage_flag g).2.1
  obtain ⟨lam, mu, hlam, hmu, geometry, heq⟩ := DYG
    (KK K P.F P.selected P.seeds) x (CO K) P.stage (P.stage_proper hp) hflags hmixed
  let unit := fun g => suppliedUnit (P.stage g) (P.stage_proper hp g) (geometry g)
  let scale := SZ.d * delta
  let zCap := delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag
  let uCap := SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag
  let vCap := SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag
  let live := active P SZ
  have hFchar : P.F.degreeOf 2 < 2130706433 := P.IZ.2.1.trans_lt (by omega : r < 2130706433)
  have hraw : ∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
      AGN (RingHom.id Ω) P.F SZ Q A scale zCap uCap vCap := by
    intro Q A hden hQf hAf
    exact BSF (RingHom.id Ω) P.F P.irreducible.ne_zero P.rdegree hFchar
      SP SQ hcop delta hd hP hQ (by omega) SZ hZd ⟨t - y, y - r, r⟩ (P.parent_flag _ _) (by dsimp; omega)
      Q A hden hQf hAf (by omega) (by omega)
  obtain ⟨budget, hcost, hmoving⟩ := CTF P.F SZ
    (fun a : Curve P => a.1.val) (fun a => (P.stage a.1).RR)
    (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) w (by decide)
    P.support.IZ.2.1 P.support.ys_weight P.support.total_weight
    (fun a : Curve P => suppliedBase (P.stage a.1) (geometry a.1))
    (fun a : Curve P => CO K a.1) (LocatorHybridCells.cellFirstTail t y r)
    (fun a : Curve P => unit a.1) (fun a : Curve P => a.2) (P.FDF hp)
    live (fun a ha => (Finset.mem_filter.mp ha).2) scale zCap uCap vCap hraw
  let projection : (j : Fin 3) → (a : Curve P) → Coordinate Ω (RCN002.CoordinateField Ω a.2.1) :=
    fun j a => ![(unit a.1).zProjection a.2, (unit a.1).yzProjection a.2, (unit a.1).NV a.2] j
  have hvalue (j : Fin 3) (a : Curve P) :
      RCN344.coordinateValue Ω (RCN002.CoordinateField Ω a.2.1) (projection j a) = RCN002.coordinateEvaluation Ω a.2.1 (DSG lam mu j) := by
    fin_cases j
    · exact FKV (unit a.1) a.2
    · exact GDG (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam (heq a.1).1 a.2
    · exact GAA (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam mu (heq a.1).1 (heq a.1).2 a.2
  refine ⟨lam, mu, geometry, budget, ⟨hlam, hmu, heq, hvalue, hcost, hmoving, hraw⟩, ?_⟩
  have hR : WeightBound RCN156.residualSWeights P.F (r : ℤ) := Or.inr (by exact_mod_cast P.r_weight)
  have hYR : WeightBound RCN156.residualYSWeights P.F ((r + (y - r) : ℕ) : ℤ) :=
    Or.inr (by exact_mod_cast (show wt RCN156.residualYSWeights P.F ≤ r + (y - r) by have := P.y_weight; omega))
  have hAll : MvPolynomial.weightedTotalDegree RCN156.residualTotalWeights P.F ≤ r + (y - r) + (t - y) := by
    have hh : MvPolynomial.weightedTotalDegree RCN156.residualTotalWeights P.F ≤ t := P.total_weight
    omega
  have hnormal (j : Fin 3) :
      3 * scale * (∑ a : live, multiplicity P hp a.val *
          RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω a.val.2.1) (projection j a.val)) ≤
        scale * flagMixed ⟨t - y, y - r, r⟩ (ASY t y r j) (MovingFiberThreeSources6811.direction j) +
          4 * (w + 1) * price (MovingFiberThreeSources6811.direction j) zCap uCap vCap := by
    have hh := DXA (E := Ext)
      (fun a : live => KK K P.F P.selected P.seeds a.val.1)
      (fun a : live => CO K a.val.1)
      (fun a : live => MU (P.stage a.val.1))
      P.F P.irreducible.ne_zero (fun _ => rfl) ⟨t - y, y - r, r⟩ P.parent_flag
      (fun a => P.stage_proper hp a.val.1) (fun a : live => a.val.2)
      (fun a b hh => Subtype.ext (P.FDF hp hh))
      lam mu hlam hmu j (fun a => projection j a.val) (fun a => hvalue j a.val) (by dsimp; omega)
      SZ SP SQ (fun a => (Finset.mem_filter.mp a.property).2) r (y - r) (t - y) (by omega) (by omega)
      hR hYR hAll (by omega) P.rdegree hFchar hcop delta hd hP hQ (by omega) hZd (by omega) (by omega)
    simpa only [BOE.multiplicity, scale, zCap, uCap, vCap, price, ASY, mixed_swap] using hh
  intro W
  change 3 * scale * (∑ a ∈ live, multiplicity P hp a * ordinary P hp geometry a W) ≤
    scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * flagMixed ⟨t - y, y - r, r⟩ (ASY t y r j) (MovingFiberThreeSources6811.direction j)) +
      4 * (w + 1) * price W zCap uCap vCap
  have hordinary (a : Curve P) : ordinary P hp geometry a W =
      ∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω a.2.1) (projection j a) := by
    simp only [Fin.sum_univ_three, projection, MovingFiberThreeSources6811.weight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, ordinary, BLJ, FE.weightedCost, unit, EE.toFE, QZ.toFE, EE.toQZ]
    rfl
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Nat.mul_le_mul_left (MovingFiberThreeSources6811.weight W j) (hnormal j))
  rw [swap_weighted_sum, sum_scaled_prices] at hh
  rw [← Finset.sum_coe_sort live (fun a => multiplicity P hp a * ordinary P hp geometry a W)]
  simpa only [hordinary] using hh
end
end Frame
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Local
def PrimeChain (A : Type*) [CommRing A] : Prop :=
  ∀ p p' : Ideal A, p.IsPrime → p'.IsPrime → p ≠ ⊥ → p < p' → p'.IsMaximal
def localNumber {O : Type*} [CommRing O] (D : Divisor O) (g : O) : ℕ∞ :=
  D.sum fun P m => (m : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g}))
variable {A : Type*} [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  [IsFractionRing A L]
abbrev pointRing (q : Ideal A) [q.IsPrime] : Subalgebra A L :=
  Localization.subalgebra.ofField L q.primeCompl q.primeCompl_le_nonZeroDivisors
def centre (v : Valuation L ℤᵐ⁰) (h : ∀ a : A, v (algebraMap A L a) ≤ 1) : Ideal A where
  carrier := {a | v (algebraMap A L a) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact (v.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (h c)) hx
end Local
section Level
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L]
open Classical in
def zeroDivisor (x : L) : Divisor O :=
  if h : (Function.support fun P : PrimeDivisor O => (-(P.valuation L x).log).toNat).Finite then
    Finsupp.ofSupportFinite _ h else 0
variable {E : Type*} [Field E] [Algebra E L]
def levelDivisor (f : L) (c : E) : Divisor O := zeroDivisor L (f - algebraMap E L c)
def levelIdeal (f : L) (c : E) (n : ℕ) : Ideal O :=
  divisorIdeal L (n • levelDivisor (O := O) L f c)
end Level
section Specialization
structure Specialization (L F : Type*) [Field L] [Field F] where
  val : Valuation L ℤᵐ⁰
  surjective : Function.Surjective val
  res : val.valuationSubring →+* F
  res_surjective : Function.Surjective res
  res_eq_zero_iff : ∀ x, res x = 0 ↔ val (x : L) < 1
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
def Specialization.resOn (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) :
    O →+* F :=
  S.res.comp ((algebraMap O L).codRestrict S.val.valuationSubring fun a =>
    (Valuation.mem_valuationSubring_iff S.val _).mpr (hO a))
def Specialization.image (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) :
    Subring F :=
  (S.resOn hO).range
variable (E : Type*) [Field E] [Algebra E F]
def Specialization.placesOn (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) :
    Set (RCN026.Place_p19 E F) :=
  {μ | ∀ b ∈ S.image hO, μ.val b ≤ 1}
variable {E}
def Specialization.leastOrder (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
    (I : Ideal O) (μ : Valuation F ℤᵐ⁰) : ℕ :=
  sInf {k : ℕ | ∃ x ∈ I, S.val (algebraMap O L x) = 1 ∧ μ (S.resOn hO x) = exp (-(k : ℤ))}
def Specialization.levelOrder [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [IsFractionRing O L] [Algebra E L] (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (f : L) (c : E) (n : ℕ) : ℕ :=
  ∑ᶠ μ ∈ S.placesOn E hO, S.leastOrder hO (levelIdeal L f c n) μ.val
end Specialization
section Surface
variable {E : Type} [Field E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (sR sY sZ : Bool)
abbrev normalChart : Subalgebra E (RCN002.CoordinateField E G) :=
  (integralClosure (surfaceChartRing G sR sY sZ) (RCN002.CoordinateField E G)).restrictScalars E
structure SurfaceDivisor (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) : Prop where
  surjective : Function.Surjective nu
  le_one : ∀ a ∈ surfaceChartRing G sR sY sZ, nu a ≤ 1
  nonconst : ∃ t ∈ surfaceChartRing G sR sY sZ, Transcendental E t ∧
    ∀ a ∈ IntermediateField.adjoin E {t}, a ≠ 0 → nu a = 1
def SurfaceNoether (N : ℕ) : Prop :=
  ∃ s₁ ∈ surfaceChartRing G sR sY sZ, ∃ s₂ ∈ surfaceChartRing G sR sY sZ,
    AlgebraicIndependent E ![s₁, s₂] ∧
    (∀ a ∈ surfaceChartRing G sR sY sZ, IsIntegral (Algebra.adjoin E {s₁, s₂}) a) ∧
    ∀ a : RCN002.CoordinateField E G, ∃ Q : Polynomial (IntermediateField.adjoin E {s₁, s₂}),
      Q ≠ 0 ∧ Q.natDegree ≤ 3 * N ∧ Polynomial.aeval a Q = 0
structure SurfacePoint where
  ring : Subalgebra E (RCN002.CoordinateField E G)
  isNoetherianRing : IsNoetherianRing ring
  isIntegrallyClosed : IsIntegrallyClosed ring
  isFractionRing : IsFractionRing ring (RCN002.CoordinateField E G)
  primeChain : PrimeChain ring
  residue : ∃ φ : ring →ₐ[E] E, ∀ x, φ x = 0 ↔ ¬IsUnit x
  chart : ∃ sR sY sZ, normalChart G sR sY sZ ≤ ring ∧
    ∀ x ∈ ring, ∃ s ∈ normalChart G sR sY sZ, s ≠ 0 ∧ s⁻¹ ∈ ring ∧ x * s ∈ normalChart G sR sY sZ
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
variable {G}
namespace SurfacePoint
theorem ext_ring {q q' : SurfacePoint G} (h : q.ring = q'.ring) : q = q' := by
  cases q
  cases q'
  cases h
  rfl
variable (q : SurfacePoint G)
def chartOf : Bool × Bool × Bool :=
  (q.chart.choose, q.chart.choose_spec.choose, q.chart.choose_spec.choose_spec.choose)
theorem chartOf_spec : normalChart G q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 ≤ q.ring ∧
    ∀ x ∈ q.ring, ∃ s ∈ normalChart G q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2,
      s ≠ 0 ∧ s⁻¹ ∈ q.ring ∧ x * s ∈ normalChart G q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 :=
  q.chart.choose_spec.choose_spec.choose_spec
def localFunction (A₁ : RCN002.CoordinateField E G) (W : FlagDegree) : RCN002.CoordinateField E G :=
  A₁ / lmono (coordinate E G) (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 W)
def level (f : RCN002.CoordinateField E G) (c : E) : Divisor q.ring :=
  levelDivisor (RCN002.CoordinateField E G) f c
open Classical in
def levelNumber (f : RCN002.CoordinateField E G) (c : E) (g : RCN002.CoordinateField E G) : ℕ :=
  if h : g ∈ q.ring then (localNumber (q.level f c) ⟨g, h⟩).toNat else 0
variable {F : Type*} [Field F]
abbrev On (S : Specialization (RCN002.CoordinateField E G) F) : Prop :=
  ∀ a : q.ring, S.val (algebraMap q.ring (RCN002.CoordinateField E G) a) ≤ 1
variable [Algebra E F]
open Classical in
def order (S : Specialization (RCN002.CoordinateField E G) F) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) : ℕ :=
  if h : q.On S then S.levelOrder h f c n else 0
end SurfacePoint
variable {F : Type*} [Field F] [Algebra E F]
open Classical in
def curveMoving (S : Specialization (RCN002.CoordinateField E G) F) (f : RCN002.CoordinateField E G) (c : E) : ℕ :=
  ∑ᶠ q : SurfacePoint G, if f ∈ q.ring then q.order S f c 1 else 0
open Classical in
def curveBase (S : Specialization (RCN002.CoordinateField E G) F) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) : ℕ :=
  ∑ᶠ q : SurfacePoint G, if f ∈ q.ring then 0 else q.order S f c n
open Classical in
def baseNumber (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) (W : FlagDegree) : ℕ :=
  ∑ᶠ q : SurfacePoint G, if f ∈ q.ring then 0 else q.levelNumber f c (q.localFunction A₁ W)
end Surface
section Curve
variable {E : Type} [Field E] (G C : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] [C.IsPrime]
def IsCurveOnSurface (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)) : Prop :=
  ∀ A : MvPolynomial (Fin 3) E, ∃ h : RCN002.coordinateEvaluation E G A ∈ S.val.valuationSubring,
    S.res ⟨RCN002.coordinateEvaluation E G A, h⟩ = RCN002.coordinateEvaluation E C A
end Curve
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN136 RCN204
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Graph
variable {R S U : Type*} [CommRing R] [Field S] [Field U]
def resGraph (f : R →+* S) (g : R →+* U) : Subring (S × U) where
  carrier := {p | ∃ a b : R, f b ≠ 0 ∧ g b ≠ 0 ∧ p = (f a / f b, g a / g b)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, hb', rfl⟩ ⟨c, d, hd, hd', rfl⟩
    exact ⟨a * c, b * d, by rw [map_mul]; exact mul_ne_zero hb hd,
      by rw [map_mul]; exact mul_ne_zero hb' hd',
      by rw [Prod.mk_mul_mk, map_mul, map_mul, map_mul, map_mul, div_mul_div_comm, div_mul_div_comm]⟩
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, map_one, div_one, div_one]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨a, b, hb, hb', rfl⟩ ⟨c, d, hd, hd', rfl⟩
    refine ⟨a * d + b * c, b * d, by rw [map_mul]; exact mul_ne_zero hb hd,
      by rw [map_mul]; exact mul_ne_zero hb' hd', ?_⟩
    rw [Prod.mk_add_mk, div_add_div _ _ hb hd, div_add_div _ _ hb' hd']
    simp only [map_add, map_mul]
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact one_ne_zero,
    by rw [map_zero, map_zero, zero_div, zero_div]; rfl⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, hb', rfl⟩
    exact ⟨-a, b, hb, hb', by rw [Prod.neg_mk, map_neg, map_neg, neg_div, neg_div]⟩
variable {f : R →+* S} {g : R →+* U}
theorem mem_resGraph (hfg : ∀ a, f a = 0 → g a = 0) (a b : R) (hb : g b ≠ 0) :
    (f a / f b, g a / g b) ∈ resGraph f g :=
  ⟨a, b, fun h => hb (hfg b h), hb, rfl⟩
theorem resGraph_snd_eq_zero (hfg : ∀ a, f a = 0 → g a = 0) {y : U}
    (h : ((0 : S), y) ∈ resGraph f g) : y = 0 := by
  obtain ⟨a, b, hb, -, h⟩ := h
  rw [Prod.mk.injEq] at h
  have ha : f a = 0 := by
    have h1 := h.1.symm
    rwa [div_eq_zero_iff, or_iff_left hb] at h1
  rw [h.2, hfg a ha, zero_div]
theorem zpow_mem_resGraph (hfg : ∀ a, f a = 0 → g a = 0) (q : R) (n : ℤ) (hn : n < 0 → g q ≠ 0) :
    (f q ^ n, g q ^ n) ∈ resGraph f g := by
  have h1 : (f q, g q) ∈ resGraph f g := by
    simpa only [map_one, div_one] using mem_resGraph hfg q 1 (by rw [map_one]; exact one_ne_zero)
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast, Prod.pow_mk] using pow_mem h1 k
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa only [Nat.cast_zero, neg_zero, zpow_zero, Prod.mk_one_one] using (resGraph f g).one_mem
    · have h2 := mem_resGraph hfg 1 q (hn (by omega))
      simp only [map_one, one_div] at h2
      simpa only [zpow_neg, zpow_natCast, inv_pow, Prod.pow_mk] using pow_mem h2 k
theorem le_one_of_isIntegral_resGraph (hfg : ∀ a, f a = 0 → g a = 0) {A Γ : Type*} [CommRing A]
    [Algebra A S] [LinearOrderedCommGroupWithZero Γ] (nu : Valuation U Γ)
    (hA : ∀ a : A, ∃ b, (algebraMap A S a, b) ∈ resGraph f g ∧ nu b ≤ 1) {x : S} {y : U}
    (hxy : (x, y) ∈ resGraph f g) (hx : IsIntegral A x) : nu y ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨p, hp, hpx⟩ := hx
  rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hpx
  have hy0 : 0 < nu y := zero_lt_one.trans hlt
  obtain ⟨y', hy', hlt'⟩ : ∃ y', (∑ i ∈ Finset.range p.natDegree,
      Polynomial.eval₂ (algebraMap A S) x (Polynomial.C (p.coeff i) * Polynomial.X ^ i), y') ∈
        resGraph f g ∧ nu y' < nu y ^ p.natDegree := by
    refine Finset.sum_induction _
      (fun s => ∃ y', (s, y') ∈ resGraph f g ∧ nu y' < nu y ^ p.natDegree) ?_ ?_ ?_
    · rintro s t ⟨b, hb, hb1⟩ ⟨c, hc, hc1⟩
      exact ⟨b + c, add_mem hb hc, nu.map_add_lt hb1 hc1⟩
    · exact ⟨0, zero_mem _, by rw [map_zero]; exact pow_pos hy0 _⟩
    · intro i hi
      obtain ⟨b, hb, hb1⟩ := hA (p.coeff i)
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      refine ⟨b * y ^ i, ?_, ?_⟩
      · simpa only [Prod.mk_mul_mk, Prod.pow_mk] using mul_mem hb (pow_mem hxy i)
      · rw [map_mul, map_pow]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hb1)
          (pow_lt_pow_right₀ hlt (Finset.mem_range.1 hi))
  have hsum := add_mem (pow_mem hxy p.natDegree) hy'
  rw [Prod.pow_mk, Prod.mk_add_mk, hpx] at hsum
  have hz := resGraph_snd_eq_zero hfg hsum
  have h1 : nu y ^ p.natDegree = nu y' := by
    rw [← map_pow, eq_neg_of_add_eq_zero_left hz, Valuation.map_neg]
  rw [h1] at hlt'
  exact lt_irrefl _ hlt'
end Graph
variable {K E : Type} [Field K] [Field E]
section Carrier
variable {F₀ : MvPolynomial (Fin 4) K} [Fact (Irreducible F₀)] {phi : Polynomial K →+* E}
  {C : Ideal (MvPolynomial (Fin 3) E)} [C.IsPrime]
theorem GP_X_succ (phi : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (j : Fin 3) : SecondJetComponentRoots.coefficientMap phi C (MvPolynomial.X j.succ) = coordinate E C j := by
  change RCN002.coordinateEvaluation E C (surfaceMap phi (MvPolynomial.X j.succ)) = RCN002.coordinateEvaluation E C (MvPolynomial.X j)
  rw [RCN136.surfaceMap_X_succ]
end Carrier
section Select
variable {L : Type*} [Field L]
theorem chartExp_neg (sR sY sZ : Bool) (i j : Fin 3) (h : chartExp sR sY sZ i j < 0) :
    (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) := by
  revert sR sY sZ i j
  decide
theorem vertexExp_nonneg (sR sY sZ : Bool) (W : FlagDegree) (j : Fin 3) :
    0 ≤ vertexExp sR sY sZ W j := by
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases j <;>
    simp [vertexExp] <;> omega
theorem vertexExp_ne_zero (sR sY sZ : Bool) (W : FlagDegree) (j : Fin 3)
    (h : vertexExp sR sY sZ W j ≠ 0) :
    (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) := by
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases j <;>
    simp [vertexExp] at h ⊢
theorem chart_select (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) :
    ∃ sR sY sZ : Bool, (sR = true → x 1 ≠ 0) ∧ (sY = true → x 0 ≠ 0) ∧ (sZ = true → x 2 ≠ 0) ∧
      (∀ i, v (lmono x (chartExp sR sY sZ i)) ≤ 1) ∧
      ∀ W, v (lmono x (vertexExp sR sY sZ W)) = exp (flagPole v x W) := by
  classical
  let x' : Fin 3 → L := fun j => if x j = 0 then 1 else x j
  have hx'0 : ∀ j, x j = 0 → x' j = 1 := fun j h => ite_eq_left_iff.2 fun hn => absurd h hn
  have hx'1 : ∀ j, x j ≠ 0 → x' j = x j := fun j h => ite_eq_right_iff.2 fun hp => absurd hp h
  have hx' : ∀ j, x' j ≠ 0 := fun j => by
    by_cases h : x j = 0
    · rw [hx'0 j h]; exact one_ne_zero
    · rw [hx'1 j h]; exact h
  have hlog : ∀ j, (v (x' j)).log = (v (x j)).log := fun j => by
    by_cases h : x j = 0
    · rw [hx'0 j h, h, map_one, map_zero, log_one, log_zero]
    · rw [hx'1 j h]
  have hpole : ∀ W, flagPole v x' W = flagPole v x W := fun W => by
    simp only [flagPole, RCN187.poleOrder, hlog]
  have hmono_eq : ∀ a : Fin 3 → ℤ, (∀ j, a j ≠ 0 → x j ≠ 0) → lmono x a = lmono x' a := by
    intro a ha
    have h : ∀ j, x j ^ a j = x' j ^ a j := fun j => by
      by_cases hj : x j = 0
      · have h0 : a j = 0 := by
          by_contra h
          exact ha j h hj
        rw [h0, zpow_zero, zpow_zero]
      · rw [hx'1 j hj]
    rw [lmono, lmono, h 0, h 1, h 2]
  have hmono_le : ∀ a : Fin 3 → ℤ, (∀ j, a j < 0 → x j ≠ 0) → v (lmono x a) ≤ v (lmono x' a) := by
    intro a ha
    by_cases h : ∀ j, a j ≠ 0 → x j ≠ 0
    · rw [hmono_eq a h]
    · obtain ⟨j, hj⟩ := not_forall.1 h
      obtain ⟨hj, hxj⟩ := Classical.not_imp.1 hj
      rw [not_not] at hxj
      have hz : x j ^ a j = 0 := by rw [hxj, zero_zpow _ hj]
      have h0 : lmono x a = 0 := by
        rw [lmono]
        fin_cases j
        · rw [show x 0 ^ a 0 = 0 from hz, zero_mul, zero_mul]
        · rw [show x 1 ^ a 1 = 0 from hz, mul_zero, zero_mul]
        · rw [show x 2 ^ a 2 = 0 from hz, mul_zero]
      rw [h0, map_zero]
      exact zero_le
  have key : ∀ sR sY sZ : Bool,
      (∀ i : Fin 3, chartExp sR sY sZ i 0 * (v (x 0)).log + chartExp sR sY sZ i 1 * (v (x 1)).log +
        chartExp sR sY sZ i 2 * (v (x 2)).log ≤ 0) →
      (sR = true → x 1 ≠ 0) → (sY = true → x 0 ≠ 0) → (sZ = true → x 2 ≠ 0) →
      ∃ sR sY sZ : Bool, (sR = true → x 1 ≠ 0) ∧ (sY = true → x 0 ≠ 0) ∧ (sZ = true → x 2 ≠ 0) ∧
        (∀ i, v (lmono x (chartExp sR sY sZ i)) ≤ 1) ∧
        ∀ W, v (lmono x (vertexExp sR sY sZ W)) = exp (flagPole v x W) := by
    intro sR sY sZ h hR hY hZ
    have hbit : ∀ j : Fin 3, (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) →
        x j ≠ 0 := by
      rintro j (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      exacts [hY h, hR h, hZ h]
    have h' : ∀ i, v (lmono x' (chartExp sR sY sZ i)) ≤ 1 := fun i => by
      rw [lmono_le_one_iff v x' hx', hlog, hlog, hlog]
      exact h i
    refine ⟨sR, sY, sZ, hR, hY, hZ, fun i => (hmono_le _ fun j hj =>
      hbit j (chartExp_neg sR sY sZ i j hj)).trans (h' i), fun W => ?_⟩
    rw [hmono_eq _ fun j hj => hbit j (vertexExp_ne_zero sR sY sZ W j hj),
      flagPole_eq_vertex v x' hx' sR sY sZ h' W, hpole]
  have hl : ∀ j, x j = 0 → (v (x j)).log = 0 := fun j h => by rw [h, map_zero, log_zero]
  have hl0 := hl 0
  have hl1 := hl 1
  have hl2 := hl 2
  generalize (v (x 0)).log = l0 at key hl0
  generalize (v (x 1)).log = l1 at key hl1
  generalize (v (x 2)).log = l2 at key hl2
  by_cases hZ : l2 ≤ 0
  · by_cases hY : l0 ≤ 0
    · by_cases hR : l1 ≤ 0
      · exact key false false false (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          nofun nofun nofun
      · exact key true false false (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          (fun _ hx => hR (hl1 hx).le) nofun nofun
    · by_cases hR : l1 ≤ l0
      · exact key false true false (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          nofun (fun _ hx => hY (hl0 hx).le) nofun
      · exact key true true false (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          (fun _ hx => hR (by have := hl1 hx; omega)) (fun _ hx => hY (hl0 hx).le) nofun
  · by_cases hY : l0 ≤ l2
    · by_cases hR : l1 ≤ l2
      · exact key false false true (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          nofun nofun (fun _ hx => hZ (hl2 hx).le)
      · exact key true false true (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          (fun _ hx => hR (by have := hl1 hx; omega)) nofun (fun _ hx => hZ (hl2 hx).le)
    · by_cases hR : l1 ≤ l0
      · exact key false true true (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          nofun (fun _ hx => hY (by have := hl0 hx; omega)) (fun _ hx => hZ (hl2 hx).le)
      · exact key true true true (by intro i; fin_cases i <;> simp [chartExp] <;> omega)
          (fun _ hx => hR (by have := hl1 hx; omega)) (fun _ hx => hY (by have := hl0 hx; omega))
          (fun _ hx => hZ (hl2 hx).le)
end Select
end
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
open RCN095 RCN204 RCN313 RCN187
open RCN095 renaming PolynomialInFlag → BI
open BD
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
theorem flagPole_cutFlag {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (m : ℕ)
    (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all) :
    flagPole v x (cutFlag m Hf) =
      m * (2 * flagPole v x Hf -
          5 * max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2)))) +
        3 * max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))) := by
  have c : ((2 * Hf.all - 5 : ℕ) : ℤ) = 2 * (Hf.all : ℤ) - 5 := by omega
  rw [cutFlag, flagPole_add, RCN204.flagPole_nsmul]
  simp only [flagPole]
  rw [c]
  push_cast
  ring
variable {K : Type} [Field K]
theorem tail_cube_bound (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (v : Valuation (SliceField F₀) ℤᵐ⁰) (m : ℕ)
    (hPL : PlaceLaw F F₀ hdvd v m) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : v (sliceProj F₀ (polyH K F)) ≤ exp (flagPole v (sliceCoord F₀) Hf)) :
    v (tail F F₀ hdvd m) ^ 3 * v (sliceProj F₀ (polyH K F)) ^ (2 * m) ≤
      exp (4 * m * placeT F F₀ v + flagPole v (sliceCoord F₀) (cutFlag m Hf)) := by
  set τ := tail F F₀ hdvd m with hτdef
  set Hs := sliceProj F₀ (polyH K F) with hHs
  have hHs0 : v Hs ≠ 0 := (Valuation.ne_zero_iff v).2 hH
  have hHsexp : v Hs = exp (v Hs).log := (exp_log hHs0).symm
  have hτ : v τ ≤ exp (vpole v τ) := HFree6812.v_le_exp_vpole v τ
  have hq : (v Hs).log ≤ flagPole v (sliceCoord F₀) Hf := by
    rw [hHsexp, exp_le_exp] at hHf
    exact hHf
  have hq0 := RCN204.flagPole_nonneg v (sliceCoord F₀) Hf
  have hh : placeH F F₀ v = max 0 (-(v Hs).log) := rfl
  have hα : placeP F₀ v = max (poleOrder v (sliceCoord F₀ 1))
      (max (poleOrder v (sliceCoord F₀ 0)) (poleOrder v (sliceCoord F₀ 2))) := rfl
  calc v τ ^ 3 * v Hs ^ (2 * m) ≤ exp (vpole v τ) ^ 3 * exp (v Hs).log ^ (2 * m) := by
        rw [← hHsexp]
        exact mul_le_mul' (pow_le_pow_left' hτ 3) le_rfl
    _ = exp (3 * vpole v τ + 2 * m * (v Hs).log) := by
        rw [← exp_nsmul, ← exp_nsmul, ← exp_add]
        simp only [nsmul_eq_mul]
        push_cast
        rfl
    _ ≤ _ := by
        rw [exp_le_exp, flagPole_cutFlag v _ m Hf h5, ← hα]
        unfold PlaceLaw at hPL
        rw [hh, ← hτdef] at hPL
        have hmax : max 0 (-(v Hs).log) + (v Hs).log ≤ flagPole v (sliceCoord F₀) Hf := by
          rcases le_total 0 (-(v Hs).log) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
        nlinarith [mul_le_mul_of_nonneg_left hmax hm]
theorem psiS_bound (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (h2 : (2 : K) ≠ 0) (S : MovingFiberThreeSources6811.Source F)
    (hfact : (S.k.factorial : K) ≠ 0) (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (hlead : srcLead F F₀ S ≠ 0) (m : ℕ)
    (hPL : PlaceLaw F F₀ hdvd v m) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : v (sliceProj F₀ (polyH K F)) ≤ exp (flagPole v (sliceCoord F₀) Hf)) :
    v (psiS F F₀ hdvd S m) ≤
      exp (flagPole v (sliceCoord F₀) (S.d • cutFlag m Hf + (4 * m) • S.flag)) := by
  have h1 := tail_cube_bound F F₀ hdvd hH v m hPL Hf h5 hHf
  have hN : (S.d : ℤ) * placeT F F₀ v + (v (srcLead F F₀ S)).log ≤ flagPole v (sliceCoord F₀) S.flag :=
    source_place_bound F F₀ hdvd hH h2 S hfact v hK hX0 hlead
  have hc0 : v (srcLead F F₀ S) ≠ 0 := (Valuation.ne_zero_iff v).2 hlead
  have hcexp : v (srcLead F F₀ S) = exp (v (srcLead F F₀ S)).log := (exp_log hc0).symm
  have e1 : v (tail F F₀ hdvd m) ^ (3 * S.d) * v (sliceProj F₀ (polyH K F)) ^ (2 * m * S.d) =
      (v (tail F F₀ hdvd m) ^ 3 * v (sliceProj F₀ (polyH K F)) ^ (2 * m)) ^ S.d := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [psiS, map_mul, map_mul, map_pow, map_pow, map_pow, e1]
  calc (v (tail F F₀ hdvd m) ^ 3 * v (sliceProj F₀ (polyH K F)) ^ (2 * m)) ^ S.d *
        v (srcLead F F₀ S) ^ (4 * m)
      ≤ exp (4 * m * placeT F F₀ v + flagPole v (sliceCoord F₀) (cutFlag m Hf)) ^ S.d *
        exp (v (srcLead F F₀ S)).log ^ (4 * m) := by
        rw [← hcexp]
        exact mul_le_mul' (pow_le_pow_left' h1 _) le_rfl
    _ = exp (S.d * (4 * m * placeT F F₀ v + flagPole v (sliceCoord F₀) (cutFlag m Hf)) +
        4 * m * (v (srcLead F F₀ S)).log) := by
        rw [← exp_nsmul, ← exp_nsmul, ← exp_add]
        simp only [nsmul_eq_mul]
        push_cast
        rfl
    _ ≤ _ := by
        rw [exp_le_exp, flagPole_add, RCN204.flagPole_nsmul, RCN204.flagPole_nsmul]
        have hm : (0 : ℤ) ≤ 4 * m := by positivity
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hN hm]
theorem psiS_div_vertex_le_one (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (h2 : (2 : K) ≠ 0) (S : MovingFiberThreeSources6811.Source F)
    (hfact : (S.k.factorial : K) ≠ 0) (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (hlead : srcLead F F₀ S ≠ 0) (m : ℕ)
    (hPL : PlaceLaw F F₀ hdvd v m) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : v (sliceProj F₀ (polyH K F)) ≤ exp (flagPole v (sliceCoord F₀) Hf))
    (sR sY sZ : Bool) (hc : ∀ j, sliceCoord F₀ j ≠ 0)
    (hchart : ∀ i, v (lmono (sliceCoord F₀) (chartExp sR sY sZ i)) ≤ 1) :
    v (psiS F F₀ hdvd S m /
      lmono (sliceCoord F₀) (vertexExp sR sY sZ (S.d • cutFlag m Hf + (4 * m) • S.flag))) ≤ 1 := by
  rw [map_div₀, flagPole_eq_vertex v _ hc sR sY sZ hchart]
  exact (div_le_one₀ (zero_lt_iff.2 exp_ne_zero)).2
    (psiS_bound F F₀ hdvd hH h2 S hfact v hK hX0 hlead m hPL Hf h5 hHf)
theorem psiS_integral (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (h2 : (2 : K) ≠ 0) (S : MovingFiberThreeSources6811.Source F)
    (hfact : (S.k.factorial : K) ≠ 0) (hlead : srcLead F F₀ S ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0)
    (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : ∀ w : Valuation (SliceField F₀) ℤᵐ⁰,
      (∀ a : K, a ≠ 0 → w (algebraMap K (SliceField F₀) a) = 1) →
      w (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 →
      w (sliceProj F₀ (polyH K F)) ≤ exp (flagPole w (sliceCoord F₀) Hf))
    (sR sY sZ : Bool) (hKr : ChartKrull F₀ sR sY sZ) (hPL : ChartPlaceLaw F F₀ hdvd sR sY sZ) :
    PsiSIntegral F F₀ hdvd S Hf sR sY sZ :=
  fun m => hKr _ fun w hw =>
    psiS_div_vertex_le_one F F₀ hdvd hH h2 S hfact w hw.trivial_on_K hw.x0_le_one hlead m
      (hPL w hw m) Hf h5 (hHf w hw.trivial_on_K hw.x0_le_one) sR sY sZ hc hw.coord_le_one
theorem coeff_pderiv_succ {σ : Type*} [DecidableEq σ] (i : σ) (F : MvPolynomial σ K) (e : σ →₀ ℕ) :
    (pderiv i F).coeff e = ((e i + 1 : ℕ) : K) * F.coeff (e + Finsupp.single i 1) := by
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = e + Finsupp.single i 1
    · subst h
      simp [mul_comm]
    · simp only [h, ↓reduceIte, mul_zero]
      split_ifs with h1
      · have hs : s i = 0 := by
          by_contra hne
          apply h
          rw [← h1]
          ext j
          by_cases hj : j = i
          · subst hj
            simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]
            omega
          · simp [Finsupp.single_eq_of_ne hj]
        rw [hs, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
theorem polyH_flag_le (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (z y r : ℕ)
    (hF : ∀ e ∈ F.support, e 2 ≤ r ∧ e 1 + e 2 ≤ r + y ∧ e 1 + e 2 + e 3 ≤ r + y + z) :
    v (sliceProj F₀ (polyH K F)) ≤ exp (flagPole v (sliceCoord F₀) ⟨z, y, r - 1⟩) := by
  classical
  refine sliceProj_flag_le F₀ v hK hX0 (polyH K F) ⟨z, y, r - 1⟩ fun e he => ?_
  have hne : (pderiv (2 : Fin 4) F).coeff e ≠ 0 := MvPolynomial.mem_support_iff.1 he
  rw [coeff_pderiv_succ] at hne
  have hmem : e + Finsupp.single (2 : Fin 4) 1 ∈ F.support :=
    MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hne)
  obtain ⟨h1, h2, h3⟩ := hF _ hmem
  have e2 : (e + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) 2 = e 2 + 1 := by simp
  have e1 : (e + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) 1 = e 1 := by
    simp [Finsupp.single_eq_of_ne (show (1 : Fin 4) ≠ 2 by decide)]
  have e3 : (e + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) 3 = e 3 := by
    simp [Finsupp.single_eq_of_ne (show (3 : Fin 4) ≠ 2 by decide)]
  rw [e2] at h1
  rw [e1, e2] at h2
  rw [e1, e2, e3] at h3
  dsimp only
  omega
theorem coeff_X_mul_pderiv {σ : Type*} [DecidableEq σ] (i : σ) (F : MvPolynomial σ K) (e : σ →₀ ℕ) :
    (MvPolynomial.X i * pderiv i F).coeff e = (e i : K) * F.coeff e := by
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    split_ifs with h
    · subst h
      rw [nsmul_eq_mul]
    · rw [smul_zero, mul_zero]
  | add p q hp hq =>
    rw [map_add, mul_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
theorem polyH_euler_le (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (v : Valuation (SliceField F₀) ℤᵐ⁰)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (z y r : ℕ)
    (hF : ∀ e ∈ F.support, e 2 ≤ r ∧ e 1 + e 2 ≤ r + y ∧ e 1 + e 2 + e 3 ≤ r + y + z) :
    v (sliceProj F₀ (polyH K F)) ≤ exp (flagPole v (sliceCoord F₀) ⟨z, y + 1, r - 2⟩) := by
  classical
  have hpY : 0 ≤ poleOrder v (sliceCoord F₀ 0) := vpole_nonneg v _
  have hpR : 0 ≤ poleOrder v (sliceCoord F₀ 1) := vpole_nonneg v _
  have hβ : 0 ≤ max (poleOrder v (sliceCoord F₀ 0)) (poleOrder v (sliceCoord F₀ 2)) :=
    hpY.trans (le_max_left _ _)
  rcases le_or_gt (poleOrder v (sliceCoord F₀ 1))
      (max (poleOrder v (sliceCoord F₀ 0)) (poleOrder v (sliceCoord F₀ 2))) with hcase | hcase
  · refine (polyH_flag_le F F₀ v hK hX0 z y r hF).trans ?_
    rw [exp_le_exp]
    simp only [flagPole, max_eq_right hcase]
    have c : ((r - 1 : ℕ) : ℤ) ≤ ((r - 2 : ℕ) : ℤ) + 1 := by omega
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right c hβ]
  · have hvR : v (sliceCoord F₀ 1) = exp (poleOrder v (sliceCoord F₀ 1)) := by
      have epole : poleOrder v (sliceCoord F₀ 1) = max 0 (v (sliceCoord F₀ 1)).log := rfl
      have hlog : 0 < (v (sliceCoord F₀ 1)).log := by
        by_contra h
        rw [epole, max_eq_left (not_lt.1 h)] at hcase
        exact absurd hβ (not_le.2 hcase)
      have hne : v (sliceCoord F₀ 1) ≠ 0 := fun h0 => by
        rw [h0, log_zero] at hlog
        exact lt_irrefl _ hlog
      rw [epole, max_eq_right hlog.le, exp_log hne]
    have hE := sliceProj_flag_le F₀ v hK hX0
      (C (r : K) * F - MvPolynomial.X 2 * pderiv 2 F) ⟨z, y + 1, r - 1⟩ (fun e he => by
        have hne : (C (r : K) * F - MvPolynomial.X 2 * pderiv 2 F).coeff e ≠ 0 :=
          MvPolynomial.mem_support_iff.1 he
        rw [coeff_sub, coeff_C_mul, coeff_X_mul_pderiv, ← sub_mul] at hne
        have hr : e 2 ≠ r := fun h => hne (by rw [h, sub_self, zero_mul])
        obtain ⟨h1, h2, h3⟩ := hF e (MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hne))
        dsimp only
        omega)
    have hval : sliceProj F₀ (C (r : K) * F - MvPolynomial.X 2 * pderiv 2 F) =
        -(sliceCoord F₀ 1 * sliceProj F₀ (polyH K F)) := by
      rw [map_sub, map_mul, (HFree6812.sliceProj_eq_zero_iff F₀ F).2 hdvd, mul_zero, zero_sub, map_mul]
      rfl
    rw [hval, Valuation.map_neg, map_mul, hvR] at hE
    have hmul := mul_le_mul_right hE (exp (-poleOrder v (sliceCoord F₀ 1)))
    rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul, ← exp_add] at hmul
    refine hmul.trans ?_
    rw [exp_le_exp]
    simp only [flagPole, max_eq_left hcase.le]
    have c : ((r - 1 : ℕ) : ℤ) - 1 ≤ ((r - 2 : ℕ) : ℤ) := by omega
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right c hpR]
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
section Residue
def ResAlg (k : Type*) {L : Type*} [Field k] [Field L] [Algebra k L] (w : Valuation L ℤᵐ⁰)
    (x : L) : Prop :=
  w x ≤ 1 ∧ ∃ p : Polynomial k, p.Monic ∧ w (Polynomial.aeval x p) < 1
variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Valuation L ℤᵐ⁰)
theorem resAlg_closure (hk : ∀ a : k, w (algebraMap k L a) ≤ 1) :
    (∀ x y, ResAlg k w x → ResAlg k w y → ResAlg k w (x + y)) ∧
    (∀ x y, ResAlg k w x → ResAlg k w y → ResAlg k w (x * y)) ∧
    (∀ x, ResAlg k w x → w x = 1 → ResAlg k w x⁻¹) ∧
    (∀ x, w x ≤ 1 → ∀ p : Polynomial k, w (Polynomial.aeval x p) ≤ 1) := by
  classical
  let O := w.valuationSubring
  let j : k →+* O := (algebraMap k L).codRestrict O fun a =>
    (Valuation.mem_valuationSubring_iff _ _).2 (hk a)
  let r : O →+* IsLocalRing.ResidueField O := IsLocalRing.residue O
  let ι : k →+* IsLocalRing.ResidueField O := r.comp j
  have hev : ∀ (x : L) (hx : w x ≤ 1) (p : Polynomial k),
      ((p.eval₂ j ⟨x, hx⟩ : O) : L) = Polynomial.aeval x p := fun x hx p =>
    Polynomial.hom_eval₂ p j O.subtype ⟨x, hx⟩
  have hres0 : ∀ y : O, r y = 0 ↔ w (y : L) < 1 := fun y => by
    rw [← HFree6812.residue_eq_zero_iff_lt_one w y.1 y.2, HFree6812.residue_of_le w y.1 y.2]
  have hiff : ∀ (x : L) (hx : w x ≤ 1), ResAlg k w x ↔ ι.IsIntegralElem (r ⟨x, hx⟩) := by
    intro x hx
    constructor
    · rintro ⟨-, p, hp, hlt⟩
      refine ⟨p, hp, ?_⟩
      rw [← Polynomial.hom_eval₂, hres0, hev]
      exact hlt
    · rintro ⟨p, hp, h0⟩
      rw [← Polynomial.hom_eval₂, hres0, hev] at h0
      exact ⟨hx, p, hp, h0⟩
  refine ⟨fun x y hx hy => ?_, fun x y hx hy => ?_, fun x hx h1 => ?_, fun x hx p => ?_⟩
  · have hxy : w (x + y) ≤ 1 := (w.map_add _ _).trans (max_le hx.1 hy.1)
    exact (hiff _ hxy).2 (RingHom.IsIntegralElem.add ι ((hiff x hx.1).1 hx) ((hiff y hy.1).1 hy))
  · have hxy : w (x * y) ≤ 1 := by rw [map_mul]; exact mul_le_one' hx.1 hy.1
    exact (hiff _ hxy).2 (RingHom.IsIntegralElem.mul ι ((hiff x hx.1).1 hx) ((hiff y hy.1).1 hy))
  · have hxi : w x⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    have hx0 : x ≠ 0 := by rintro rfl; rw [w.map_zero] at h1; exact zero_ne_one h1
    have hmul : r ⟨x⁻¹, hxi⟩ * r ⟨x, hx.1⟩ = 1 := by
      rw [← map_mul, ← map_one r]
      exact congrArg r (Subtype.ext (inv_mul_cancel₀ hx0))
    refine (hiff _ hxi).2 ?_
    rw [eq_inv_of_mul_eq_one_left hmul]
    let _ : Algebra k (IsLocalRing.ResidueField O) := ι.toAlgebra
    exact IsIntegral.inv (R := k) ((hiff x hx.1).1 hx)
  · rw [← hev x hx p]
    exact (p.eval₂ j ⟨x, hx⟩).2
end Residue
end FormalR
end SubmissionLower
end ProximityPrize
end
