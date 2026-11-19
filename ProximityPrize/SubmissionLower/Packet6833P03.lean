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
import ProximityPrize.SubmissionLower.Packet6833P02
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
namespace ProximityPrize
namespace SubmissionLower
namespace Codec0
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
def s164:ℕ:=0x9a35fc07e09bcc8a7d297004e6027e2037d0b2e43ee9bbdf39706f6fbdec2caeefa7ceef4e54c7d09b771329f1e749baf793b1f172dc90c9a0f87fee47e4babc13770d3230bdbd7b66f9151edd8db5ac86e767b6d76e3d87aac768971eb3d4c9b3bd
def s165:ℕ:=0xab96183feb63d4b50a5c750569cf844c7a2c74a241b55ceb1a2e60a23e5ffd0a683d77292e82e81a73929b3e7e08afc7bd9e8e0315e34dce988080714be7187fe3b87d33645fb53c2a1
def table (i:ℕ):ℕ:=match i with
 | 0=>s0
 | 1=>s1
 | 2=>s2
 | 3=>s3
 | 4=>s4
 | 5=>s5
 | 6=>s6
 | 7=>s7
 | 8=>s8
 | 9=>s9
 | 10=>s10
 | 11=>s11
 | 12=>s12
 | 13=>s13
 | 14=>s14
 | 15=>s15
 | 16=>s16
 | 17=>s17
 | 18=>s18
 | 19=>s19
 | 20=>s20
 | 21=>s21
 | 22=>s22
 | 23=>s23
 | 24=>s24
 | 25=>s25
 | 26=>s26
 | 27=>s27
 | 28=>s28
 | 29=>s29
 | 30=>s30
 | 31=>s31
 | 32=>s32
 | 33=>s33
 | 34=>s34
 | 35=>s35
 | 36=>s36
 | 37=>s37
 | 38=>s38
 | 39=>s39
 | 40=>s40
 | 41=>s41
 | 42=>s42
 | 43=>s43
 | 44=>s44
 | 45=>s45
 | 46=>s46
 | 47=>s47
 | 48=>s48
 | 49=>s49
 | 50=>s50
 | 51=>s51
 | 52=>s52
 | 53=>s53
 | 54=>s54
 | 55=>s55
 | 56=>s56
 | 57=>s57
 | 58=>s58
 | 59=>s59
 | 60=>s60
 | 61=>s61
 | 62=>s62
 | 63=>s63
 | 64=>s64
 | 65=>s65
 | 66=>s66
 | 67=>s67
 | 68=>s68
 | 69=>s69
 | 70=>s70
 | 71=>s71
 | 72=>s72
 | 73=>s73
 | 74=>s74
 | 75=>s75
 | 76=>s76
 | 77=>s77
 | 78=>s78
 | 79=>s79
 | 80=>s80
 | 81=>s81
 | 82=>s82
 | 83=>s83
 | 84=>s84
 | 85=>s85
 | 86=>s86
 | 87=>s87
 | 88=>s88
 | 89=>s89
 | 90=>s90
 | 91=>s91
 | 92=>s92
 | 93=>s93
 | 94=>s94
 | 95=>s95
 | 96=>s96
 | 97=>s97
 | 98=>s98
 | 99=>s99
 | 100=>s100
 | 101=>s101
 | 102=>s102
 | 103=>s103
 | 104=>s104
 | 105=>s105
 | 106=>s106
 | 107=>s107
 | 108=>s108
 | 109=>s109
 | 110=>s110
 | 111=>s111
 | 112=>s112
 | 113=>s113
 | 114=>s114
 | 115=>s115
 | 116=>s116
 | 117=>s117
 | 118=>s118
 | 119=>s119
 | 120=>s120
 | 121=>s121
 | 122=>s122
 | 123=>s123
 | 124=>s124
 | 125=>s125
 | 126=>s126
 | 127=>s127
 | 128=>s128
 | 129=>s129
 | 130=>s130
 | 131=>s131
 | 132=>s132
 | 133=>s133
 | 134=>s134
 | 135=>s135
 | 136=>s136
 | 137=>s137
 | 138=>s138
 | 139=>s139
 | 140=>s140
 | 141=>s141
 | 142=>s142
 | 143=>s143
 | 144=>s144
 | 145=>s145
 | 146=>s146
 | 147=>s147
 | 148=>s148
 | 149=>s149
 | 150=>s150
 | 151=>s151
 | 152=>s152
 | 153=>s153
 | 154=>s154
 | 155=>s155
 | 156=>s156
 | 157=>s157
 | 158=>s158
 | 159=>s159
 | 160=>s160
 | 161=>s161
 | 162=>s162
 | 163=>s163
 | 164=>s164
 | 165=>s165
 | _=>0
def slope (i:ℕ):=table (i/16)/(2^(49*(i%16)))%2^49
def readCurve:ℕ→ℕ→ℕ→ℕ→ℕ→ℕ→List Piece
 | 0,_,_,_,_,_=>[]
 | n+1,code,prevBase,prevSlope,prevStart,start=>
  let stop:=code%16384
  let si:=code/16384%2^12
  let digits:=code/2^26%2^5
  let payload:=code/2^31
  let difference:=payload%(16^digits)
  let predicted:=prevBase+prevSlope*(start-prevStart)
  let base:=if difference%2=0 then predicted+difference/2 else predicted-difference/2
  let sl:=slope si
  ⟨stop,base,sl⟩::readCurve n (payload/(16^digits)) base sl start stop
def curve (code:ℕ):=readCurve (code%65536) (code/65536) 0 0 0 0
end Codec0
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace OP
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" =>MvPolynomial (Fin 3) K
local notation "PE" =>MvPolynomial (Fin 3) E
abbrev GDI (F A R:Poly) (C:RCN264.RegularComponent K F A R):
    RCN264.RegularComponent K F (filteredCut 0 (fun _:Fin 1=>A) 1 0) 1:=
  ⟨C.1,by
    classical
    apply (AJF K).mpr
    constructor
    · simpa only [GenericSlicePoints6807.filteredCut_zero] using AAS K F A R C
    · intro h
      have hz:RCN002.coordinateEvaluation K C.1 (1:Poly)=0:=by
        apply RingHom.mem_ker.mp
        change (1:Poly) ∈ RingHom.ker (RCN002.coordinateEvaluation K C.1).toRingHom
        rwa [RCN002.coordinateEvaluation_ker K C.1]
      exact one_ne_zero (by simpa only [map_one] using hz)⟩
theorem VX
    (F A R ell:Poly) (C:RCN264.RegularComponent K F A R)
    [Algebra (RatFunc K) (RCN002.CoordinateField K C.1)]
    [IsScalarTower K (RatFunc K) (RCN002.CoordinateField K C.1)]
    [FiniteDimensional (RatFunc K) (RCN002.CoordinateField K C.1)]
    (hj:algebraMap (RatFunc K) (RCN002.CoordinateField K C.1)
      (RCN202.rationalVariable K)=RCN002.coordinateEvaluation K C.1 ell)
    (f:RCN002.CoordinateField K C.1→ₐ[RatFunc K] E):
    let mu:=RCN208.scalarPolynomialMap K E
    let v:=RCN134.embeddingPoint C.1 (f.restrictScalars K)
    MvPolynomial.eval v (mu F)=0∧
      MvPolynomial.eval v (GenericSlicePoints6807.sliceEquation (E:=E) ell)=0∧
      MvPolynomial.aeval v (mu A)=0∧
      MvPolynomial.eval v (mu R) ≠ 0∧
      RCN084.IsolatedPoint (mu F) (GenericSlicePoints6807.sliceEquation (E:=E) ell) (mu A) v:=by
  let C0:=GDI F A R C
  have hj0:algebraMap (RatFunc K) (RCN002.CoordinateField K C0.1)
      (RCN202.rationalVariable K)=movingValue C0.1 1 0 ell 1:=by
    simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero]
      using hj
  have h1:(1:Poly) ∉ C0.1:=_Q6 K _ _ _ C0
  have hcert:=RCN202.VX F 1 0 ell 1 0
    (fun _:Fin 1=>A) C0 hj0 h1 f
  have hc:
      MvPolynomial.eval (RCN134.embeddingPoint C.1 (f.restrictScalars K))
        (RCN208.scalarPolynomialMap K E F)=0∧
      MvPolynomial.eval (RCN134.embeddingPoint C.1 (f.restrictScalars K))
        (GenericSlicePoints6807.sliceEquation (E:=E) ell)=0∧
      MvPolynomial.aeval (RCN134.embeddingPoint C.1 (f.restrictScalars K))
        (RCN208.scalarPolynomialMap K E A)=0∧
      MvPolynomial.eval (RCN134.embeddingPoint C.1 (f.restrictScalars K)) (1:PE) ≠ 0∧
      RCN084.IsolatedPoint (RCN208.scalarPolynomialMap K E F) (GenericSlicePoints6807.sliceEquation (E:=E) ell)
        (RCN208.scalarPolynomialMap K E A) (RCN134.embeddingPoint C.1 (f.restrictScalars K)):=by
    simpa only [map_one,map_zero,
      RCN207.movingEquation,RCN207.eliminatedCut,GenericSlicePoints6807.filteredCut_zero,one_mul,mul_zero,
      sub_zero,GenericSlicePoints6807.sliceEquation] using hcert
  exact ⟨hc.1,hc.2.1,hc.2.2.1,
    GenericSlicePoints6807.scalar_eval_ne_zero C.1 (f.restrictScalars K) R
      (_Q6 K F A R C),hc.2.2.2.2⟩
end
end OP
end MergedPart0
section MergedPart2
namespace BEN
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095
open RCN095 renaming PolynomialInFlag → BI
open RCN134 RCN135 RCN136 RCN208 RCN217 RCN244 RCN248 RCN313
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
variable {K I E:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "PK4" =>MvPolynomial (Fin 4) K
def YA (D:Ideal PE):PK4→+*RCN002.CoordinateRing E D:=
  (Ideal.Quotient.mk D).comp ((RCN208.scalarPolynomialMap Ω E).comp
    (surfaceMap (RCN135.polynomialEmbedding K)))
def slicePoint (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:RCN002.CoordinateField Ω C.1→ₐ[Ω] E)
    (D:Ideal PE)
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (RCN134.embeddingPoint C.1 emb):PE→ₐ[E] E).toRingHom):
    PointOn E D:=⟨RCN134.embeddingPoint C.1 emb,hD⟩
theorem CMD
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:RCN002.CoordinateField Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (RCN134.embeddingPoint C.1 emb):PE→ₐ[E] E).toRingHom)
    (F:PK4):
    pointHom E D (slicePoint S C emb D hD) (YA (K:=K) D F)=
      emb (RCN002.coordinateEvaluation Ω C.1 (surfaceMap (RCN135.polynomialEmbedding K) F)):=by
  change MvPolynomial.eval (RCN134.embeddingPoint C.1 emb)
    (RCN208.scalarPolynomialMap Ω E (surfaceMap (RCN135.polynomialEmbedding K) F))=_
  exact GenericSlicePoints6807.scalar_eval_embedding C.1 emb _
theorem DXH
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:RCN002.CoordinateField Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (RCN134.embeddingPoint C.1 emb):PE→ₐ[E] E).toRingHom):
    Ideal.comap (YA (K:=K) D)
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom)=
        QP S C:=by
  ext F
  change pointHom E D (slicePoint S C emb D hD) (YA D F)=0 ↔
    surfaceMap (RCN135.polynomialEmbedding K) F ∈ C.1
  rw [CMD S C emb D hD,
    map_eq_zero_iff emb emb.injective]
  change surfaceMap (RCN135.polynomialEmbedding K) F ∈
    RingHom.ker (RCN002.coordinateEvaluation Ω C.1).toRingHom ↔ _
  rw [RCN002.coordinateEvaluation_ker Ω C.1]
theorem FEX
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (D:Ideal PE) [D.IsPrime]
    (hcarrier:RCN208.scalarPolynomialMap Ω E S.G ∈ D):
    YA (K:=K) D (originalData_p19 S C).factor=0:=by
  change Ideal.Quotient.mk D
    (RCN208.scalarPolynomialMap Ω E
      (surfaceMap (RCN135.polynomialEmbedding K) (originalData_p19 S C).factor))=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact D.mem_of_dvd (map_dvd (RCN208.scalarPolynomialMap Ω E)
    (originalData_p19 S C).factor_dvd) hcarrier
def AKZ
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    RCN002.CoordinateRing E D:=
  Ideal.Quotient.mk D (RCN208.scalarPolynomialMap Ω E
    (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1)))
def ZA (D:Ideal PE):RCN002.CoordinateRing E D:=
  Ideal.Quotient.mk D (RCN208.scalarPolynomialMap Ω E
    (MvPolynomial.C ((-(RCN135.polynomialEmbedding K) Polynomial.X)^(RCN326.w+1))))
theorem BQY
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    AKZ S D=YA (K:=K) D
      (numerator K S.F (RCN326.w+1))*ZA (K:=K) D:=by
  simp only [AKZ,ZA,YA,
    RCN086.globalTailCut_eq,map_mul,RingHom.comp_apply]
theorem BKK
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (C:CM S) (emb:RCN002.CoordinateField Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (RCN134.embeddingPoint C.1 emb):PE→ₐ[E] E).toRingHom)
    (hcarrier:RCN208.scalarPolynomialMap Ω E S.G ∈ D):
    AKZ S D ∈
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom)^
        FO S (DN S hproper) C:=by
  let phi:=pointHom E D (slicePoint S C emb D hD)
  let J:=RingHom.ker phi.toRingHom
  letI:J.IsMaximal:=RCN017.pointKernel_isMaximal phi
  have hf:=FEX S C D hcarrier
  have hc:=DXH S C emb D hD
  have h:=AGK S hproper C
    (YA (K:=K) D) 0 (AKZ S D)
    (ZA (K:=K) D) J
    (by rw [hf];exact Ideal.zero_mem _)
    (J.zero_mem) hc (BQY S D)
  simpa [J] using h
theorem CXZ
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:RCN002.CoordinateField Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (RCN134.embeddingPoint C.1 emb):PE→ₐ[E] E).toRingHom):
    pointHom E D (slicePoint S C emb D hD)
      (YA (K:=K) D (polyH K S.F)) ≠ 0:=by
  rw [CMD S C emb D hD]
  intro hz
  have he:=(map_eq_zero_iff emb emb.injective).mp hz
  apply RCN312.JX S C
  rw [← RCN002.coordinateEvaluation_ker Ω C.1]
  exact he
theorem BWR (F:PK4):
    RCN208.scalarPolynomialMap Ω E (surfaceMap (RCN135.polynomialEmbedding K) F)=
      surfaceMap ((algebraMap Ω E).comp (RCN135.polynomialEmbedding K)) F:=by
  simp only [RCN208.scalarPolynomialMap,RCN136.surfaceMap,
    RingHom.comp_apply,MvPolynomial.map_map]
theorem EAS
    (D:Ideal PE) [D.IsPrime] (point:PointOn E D):
    pointHom E D point (ZA (K:=K) D)=
      algebraMap Ω E ((-(RCN135.polynomialEmbedding K) Polynomial.X)^(RCN326.w+1)):=by
  simp only [ZA,pointHom_mk,
    RCN208.scalarPolynomialMap,MvPolynomial.map_C,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]
theorem BWP
    (D:Ideal PE) [D.IsPrime] (point:PointOn E D):
    pointHom E D point (ZA (K:=K) D) ≠ 0:=by
  rw [EAS]
  exact (map_ne_zero (algebraMap Ω E)).mpr (RCN086.tail_scalar_ne_zero (RCN135.polynomialEmbedding K)
    (RCN135.polynomialEmbedding_injective K) (RCN326.w+1))
theorem CAZ
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    AKZ S D=ZA (K:=K) D*
      (YA (K:=K) D (polyH K S.F))^3*
        YA (K:=K) D (RCN055.baseNumerator S.F (RCN326.w-1)):=by
  rw [BQY,
    show RCN326.w+1=(RCN326.w-1)+2 by decide,
    RCN055.numerator_eq_H_cube,map_mul,map_pow]
  ring
theorem AKL (D:Ideal PE) [D.IsPrime] (F:PK4):
    algebraMap (RCN002.CoordinateRing E D) (RCN002.CoordinateField E D)
      (YA (K:=K) D F)=
      RCN002.coordinateEvaluation E D
        (surfaceMap ((algebraMap Ω E).comp (RCN135.polynomialEmbedding K)) F):=by
  change RCN002.coordinateEvaluation E D
    (RCN208.scalarPolynomialMap Ω E (surfaceMap (RCN135.polynomialEmbedding K) F))=_
  rw [BWR]
theorem DAU
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (D:Ideal PE)
    (hproper:RCN208.scalarPolynomialMap Ω E
      (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1)) ∉ D):
    AKZ S D ≠ 0:=by
  intro hz
  exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hz)
theorem BRC {A L:Type*}
    [CommRing A] [Field L] (ev:A→+*L)
    (tail base H kappa:A) (w:ℕ)
    (hrel:tail=kappa*H^3*base)
    (hH:ev H ≠ 0) (hk:ev kappa ≠ 0):
    ev tail/ev (kappa*H^(w+3))=ev base/(ev H)^w:=by
  rw [hrel]
  simp only [map_mul,map_pow]
  rw [pow_add]
  field_simp
  <;>ring
end
end BEN
end MergedPart2
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace AKA
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN026 RCN046 RCN084 RCN095 RCN114
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN204 RCN234 RCN237 RCN264 RCN340 RCN341
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {E:Type} [Field E] [IsAlgClosed E]
  {G T H:MvPolynomial (Fin 3) E} {p q:FlagDegree}
  {base: ∀C:RCN264.RegularComponent E G T H,RCN341.SeparableLiteralCoordinate C.1}
theorem CUE (U:QZ base p q)
    (C:RCN264.RegularComponent E G T H) (r:FlagDegree)
    (W:Finset (Place_p19 E (RCN002.CoordinateField E C.1))):
    (∑ v ∈ W,flagPole v.val (coordinate E C.1) r)≤
      (U.toFE.weightedCost r C:ℤ):=by
  have hz:=U.zPole C W
  have hy:=U.yzPole C W
  have ha:=U.allPole C W
  simp only [UC] at hz
  simp only [QD] at hy
  simp only [SF] at ha
  have h:=add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    FE.weightedCost,
    QZ.toFE,Nat.cast_add,Nat.cast_mul] using h
theorem EHZ (F N R:MvPolynomial (Fin 3) E)
    (hF:F ≠ 0) (p q r:FlagDegree) (hFp:RCN095.PolynomialInFlag p F)
    (base: ∀g: ↥(RCN084.activeFactors F N),∀C:RCN264.RegularComponent E g.1 N R,
      RCN341.SeparableLiteralCoordinate C.1)
    (U: ∀g: ↥(RCN084.activeFactors F N),QZ (base g) (exactFlag g.1) q):
    (∑ g: ↥(RCN084.activeFactors F N),∑ C:RCN264.RegularComponent E g.1 N R,
      (U g).toFE.weightedCost r C)≤flagMixed p q r:=by
  exact (Finset.sum_le_sum (fun g _=>
    (U g).toFE.DGB r)).trans
      (RCN084.activeFactors_mixed_sum_le F N hF p q r hFp)
end
end AKA
end MergedPart1
section MergedPart2
namespace DOW
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
section ActualAffinePlaces
variable (K A L:Type*) [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
  [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:IsScalarTower K (RatFunc K) L:=
  IsScalarTower.of_algebraMap_eq fun a=>by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) L]
theorem DQM (phi:A→ₐ[K] K)
    (n:ℕ) (a b:A) (ha:a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb:phi b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0):
    (n:ℤ)≤RCN026.order_p19 K L (RCN344.modelPlace_p19 K L A phi)
      (algebraMap A L a/algebraMap A L b):=by
  exact WeightedPlaceOrder6807.normalized_order_ge_pow (algebraMap A L)
    ((RCN000.actualPointPlace K A L phi).valuation L)
    (RCN000.actual_model_value_le_one K A L phi) phi
    (RCN000.actual_model_value_lt_one_iff K A L phi) n a b ha hb hx
end ActualAffinePlaces
end
end DOW
end MergedPart2
section MergedPart3
namespace CVS
open scoped Classical BigOperators WithZero
open RCN026
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
theorem EDY {I:Type*} [Fintype I]
    (x:L) (hx:x ≠ 0) (place:I→Place_p19 K L)
    (hinj:Function.Injective place) (mu:I→ℕ)
    (hmu: ∀i,1≤mu i)
    (horder: ∀i,(mu i:ℤ)≤order_p19 K L (place i) x):
    (∑ i,(mu i:ℤ))≤
      ∑ v ∈ placesFor_p19 K L x hx,RCN346.poleOrder_p19 K L v x:=by
  classical
  let U:Finset (Place_p19 K L):=Finset.univ.image place
  have hsub:U ⊆ placesFor_p19 K L x hx:=by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    apply ALB K L x hx (place i)
    have hi:=horder i
    have hm:(1:ℤ)≤(mu i:ℤ):=by exact_mod_cast hmu i
    omega
  calc
    (∑ i,(mu i:ℤ))≤ ∑ i,zeroOrder_p19 K L (place i) x:=by
      apply Finset.sum_le_sum
      intro i _
      exact (horder i).trans (le_max_right _ _)
    _= ∑ v ∈ U,zeroOrder_p19 K L v x:=by
      dsimp only [U]
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤ ∑ v ∈ placesFor_p19 K L x hx,zeroOrder_p19 K L v x:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact AUU K L v x
    _=_:=AJO K L x hx
section Affine
variable (A:Type*) [CommRing A] [IsDomain A]
  [Algebra K A] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
  [IsScalarTower (Polynomial K) A L]
theorem CXI {I:Type*} [Fintype I]
    (phi:I→(A→ₐ[K] K)) (hinj:Function.Injective phi)
    (mu:I→ℕ) (hmu: ∀i,1≤mu i) (a b:A)
    (ha: ∀i,a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb: ∀i,phi i b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0):
    (∑ i,(mu i:ℤ))≤
      ∑ v ∈ placesFor_p19 K L (algebraMap A L a/algebraMap A L b) hx,
        RCN346.poleOrder_p19 K L v (algebraMap A L a/algebraMap A L b):=by
  apply EDY K L _ hx
    (fun i=>RCN344.modelPlace_p19 K L A (phi i))
    ((RCN344.BQJ K L A).comp hinj) mu hmu
  intro i
  exact DOW.DQM K A L
    (phi i) (mu i) a b (ha i) (hb i) hx
theorem BUY {I:Type*} [Fintype I]
    (phi:I→(A→ₐ[K] K)) (hinj:Function.Injective phi)
    (mu:I→ℕ) (hmu: ∀i,1≤mu i) (a b:A)
    (ha: ∀i,a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb: ∀i,phi i b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0)
    (d cost:ℕ)
    (hpole: ∀W:Finset (Place_p19 K L),
      (d:ℤ)*(∑ v ∈ W,
        RCN346.poleOrder_p19 K L v (algebraMap A L a/algebraMap A L b))≤cost):
    d*(∑ i,mu i)≤cost:=by
  have hm:=CXI K L A phi hinj mu hmu a b ha hb hx
  have hs:=(mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg d)).trans
    (hpole (placesFor_p19 K L _ hx))
  exact_mod_cast hs
end Affine
end
end CVS
end MergedPart3
section MergedPart5
namespace YE
open scoped Classical BigOperators
open RCN002 RCN007 RCN072 RCN084 RCN095 RCN134 RCN264
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
local instance {A:Type*}:DecidableEq A:=Classical.decEq A
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {E I:Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" =>MvPolynomial (Fin 3) E
abbrev ANR (F N R:Poly):=
  (g: ↥(RCN084.activeFactors F N)) × RCN264.RegularComponent E g.1 N R
theorem DIX (F N R:Poly) (point:I→Fin 3→E)
    (hcover: ∀i,∃g: ↥(RCN084.activeFactors F N),MvPolynomial.eval (point i) g.1=0)
    (hN: ∀i,MvPolynomial.eval (point i) N=0)
    (hR: ∀i,MvPolynomial.eval (point i) R ≠ 0):
    ∃assign:I→ANR F N R,
      ∀i,(assign i).2.1≤RingHom.ker
        (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom:=by
  classical
  have he (i:I): ∃a:ANR F N R,
      a.2.1≤RingHom.ker (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom:=by
    obtain ⟨g,hg⟩:=hcover i
    obtain ⟨C,hC⟩:=AZA E g.1 N R (point i) hg (hN i) (hR i)
    exact ⟨⟨g,C⟩,hC⟩
  exact ⟨fun i=>(he i).choose,fun i=>(he i).choose_spec⟩
omit [Field E] [IsAlgClosed E] in
theorem DKM {A:Type*} [Fintype A] [DecidableEq A]
    (assign:I→A) (mu:I→ℕ):
    (∑ a,∑ i with assign i=a,mu i)= ∑ i,mu i:=by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ)
    (g:=assign) (fun _ _=>Finset.mem_univ _) _
theorem CLZ (F N A R:Poly)
    (point:I→Fin 3→E) (assign:I→ANR F N R)
    (hpoint: ∀i,(assign i).2.1≤RingHom.ker
      (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom)
    (hisolated: ∀i,RCN084.IsolatedPoint F N A (point i)) (i:I):
    A ∉ (assign i).2.1:=by
  let g:=(assign i).1
  let C:=(assign i).2
  exact hisolated i C.1 inferInstance (PU E g.1 N R C)
    (hpoint i)
    (C.1.mem_of_dvd (RCN084.activeFactors_spec F N g).2.1
      (EN E g.1 N R C))
    (GV E g.1 N R C)
end
end YE
end MergedPart5
section MergedPart6
namespace AVZ
open scoped Classical BigOperators
open RCN095 RCN237 RCN264 RCN340 RCN341 RCN084 RCN039 RCN046
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
variable {E:Type} [Field E] [IsAlgClosed E]
local notation "Poly" =>MvPolynomial (Fin 3) E
structure SliceBudgets (F N R:Poly) (q:FlagDegree) where
  base: ∀g: ↥(RCN084.activeFactors F N),∀C:RCN264.RegularComponent E g.1 N R,
    RCN341.SeparableLiteralCoordinate C.1
  unit: ∀g: ↥(RCN084.activeFactors F N),
    QZ (base g) (exactFlag g.1) q
theorem EFX (F N R:Poly) (p q:FlagDegree)
    (hF:F ≠ 0) (hFp:RCN095.PolynomialInFlag p F) (hNq:RCN095.PolynomialInFlag q N)
    (c:ℕ) [CharP E c] (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c):
    Nonempty (SliceBudgets F N R q):=by
  classical
  obtain ⟨base,hY,hZ⟩:=AOE F N R hF p q hFp hNq
    c hdeg hmix
  have he (g: ↥(RCN084.activeFactors F N)):
      Nonempty (EE (base g) (exactFlag g.1) q):=by
    have hg:=RCN084.activeFactors_spec F N g
    exact ACA (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((RCN095.support_subset_flagSupport_iff _ _).mpr (RCN084.polynomialIn_exactFlag g.1))
      ((RCN095.support_subset_flagSupport_iff _ _).mpr hNq)
  exact ⟨⟨base,fun g=>(Classical.choice (he g)).toQZ⟩⟩
theorem sum_cost_le (F N R:Poly) (p q r:FlagDegree)
    (hF:F ≠ 0) (hFp:RCN095.PolynomialInFlag p F) (B:SliceBudgets F N R q):
    (∑ g: ↥(RCN084.activeFactors F N),∑ C:RCN264.RegularComponent E g.1 N R,
      (B.unit g).toFE.weightedCost r C)≤flagMixed p q r:=
  AKA.EHZ F N R hF p q r hFp B.base B.unit
end
end AVZ
end MergedPart6
section MergedPart9
namespace PR
open scoped Classical BigOperators
open RCN002 RCN022 RCN030 RCN037 RCN038 RCN040 RCN042 RCN046 RCN093
open RCN095 RCN207 RCN237 RCN264 RCN340 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 40000
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local notation "Poly" =>MvPolynomial (Fin 3) Ω
theorem inFlag_X (i:Fin 3) (q:FlagDegree)
    (hi:InFlag q (Finsupp.single i 1)):RCN095.PolynomialInFlag q (MvPolynomial.X i:Poly):=by
  intro e he
  have hh:e=Finsupp.single i 1:=by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
theorem ELM {q:FlagDegree} {A B:Poly}
    (hA:RCN095.PolynomialInFlag q A) (hB:RCN095.PolynomialInFlag q B):RCN095.PolynomialInFlag q (A+B):=by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
theorem EBS {q:FlagDegree} {A:Poly}
    (c:Ω) (hA:RCN095.PolynomialInFlag q A):RCN095.PolynomialInFlag q (MvPolynomial.C c*A):=by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)
theorem FFR:RCN095.PolynomialInFlag unitZFlag (CommonLinearChannels6807.linearZ:Poly):=by
  exact inFlag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem FDG (lam:Ω):RCN095.PolynomialInFlag unitYZFlag (CommonLinearChannels6807.linearU lam):=by
  exact ELM
    (inFlag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (EBS lam (inFlag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem FFE (mu lam:Ω):RCN095.PolynomialInFlag unitAllFlag (CommonLinearChannels6807.linearA mu lam):=by
  exact ELM (ELM
    (inFlag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (EBS mu (inFlag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (EBS (mu*lam) (inFlag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))
variable {G T H:MvPolynomial (Fin 3) Ω} {p q:FlagDegree}
  {base: ∀C:RCN264.RegularComponent Ω G T H,RCN341.SeparableLiteralCoordinate C.1}
structure AND
    (unit:EE (Omega:=Ω) (G:=G) (T:=T) (H:=H) base p q) where
  lam:Ω
  mu:Ω
  yzValue: ∀C:RCN264.RegularComponent Ω G T H,
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.yzProjection C)=affineU Ω C.1 lam
  allValue: ∀C:RCN264.RegularComponent Ω G T H,
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.NV C)=affineV Ω C.1 mu (mu*lam)
theorem FKV (unit:EE base p q)
    (C:RCN264.RegularComponent Ω G T H):
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.zProjection C)=
      RCN002.coordinateEvaluation Ω C.1 (CommonLinearChannels6807.linearZ:Poly):=unit.zValue C
theorem ETQ (unit:EE base p q)
    (D:AND unit) (C:RCN264.RegularComponent Ω G T H):
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.yzProjection C)=
      RCN002.coordinateEvaluation Ω C.1 (CommonLinearChannels6807.linearU D.lam):=by
  rw [CommonLinearChannels6807.eval_linearU]
  exact D.yzValue C
theorem FKF (unit:EE base p q)
    (D:AND unit) (C:RCN264.RegularComponent Ω G T H):
    RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.NV C)=
      RCN002.coordinateEvaluation Ω C.1 (CommonLinearChannels6807.linearA D.mu D.lam):=by
  rw [CommonLinearChannels6807.eval_linearA]
  exact D.allValue C
def EYJ
    (base: ∀C:RCN264.RegularComponent Ω G T H,RCN341.SeparableLiteralCoordinate C.1)
    (hactive: ∀C:RCN264.RegularComponent Ω G T H,
      KaehlerDifferential.D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 0) ≠ 0∨
      KaehlerDifferential.D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 2) ≠ 0)
    (hZ: ∀C:RCN264.RegularComponent Ω G T H,RCN037.LiteralProjectionGate C 2)
    (hSderiv:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (D:JO (Omega:=Ω) (G:=G) (T:=T) (H:=H)
      base hactive hSderiv)
    (hG:Irreducible G) (hproper: ¬G ∣ T)
    (hGsupport:G.support ⊆ flagSupport p) (hTsupport:T.support ⊆ flagSupport q):
    AND (NJ base hactive hZ hSderiv D hG hproper hGsupport hTsupport) where
  lam:=D.lam
  mu:=D.mu
  yzValue:=by
    intro C
    change RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1)
      (RCN042.coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C))=_
    exact RCN042.coordinateOfGate_value _ _
  allValue:=by
    intro C
    change (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
      (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.GN C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=_
    exact RCN022.elementEmbedding_variable Ω (RCN002.CoordinateField Ω C.1) _ _
def EZN {T' :Poly} (h:G ∣ T-T')
    {base' : ∀C:RCN264.RegularComponent Ω G T' H,RCN341.SeparableLiteralCoordinate C.1}
    (U:EE base' p q)
    (newBase: ∀C:RCN264.RegularComponent Ω G T H,RCN341.SeparableLiteralCoordinate C.1)
    (D:AND U):
    AND (JN.YV h U newBase) where
  lam:=D.lam
  mu:=D.mu
  yzValue C:=D.yzValue (RCN066.JA h C)
  allValue C:=D.allValue (RCN066.JA h C)
end
end PR
end MergedPart9
end SubmissionLower
end ProximityPrize
end
section
section MergedPart0
namespace ProximityPrize
namespace SubmissionLower
namespace BIZ
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place_p19)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN095 renaming PolynomialInFlag → BI
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open ActualFirstCutPole6807 renaming pole_le_of_value_le → BIH
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" =>RCN326.w
section Slice
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
structure GEZ (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0:FlagDegree):Prop where
  pole_le: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu+
        2*RCN026.zeroOrder_p19 E (RCN002.CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F)))+
      3*flagPole nu.val (coordinate E C) C0)
end Slice
end
end BIZ
end SubmissionLower
end ProximityPrize
end MergedPart0
section MergedPart1
namespace ProximityPrize
namespace SubmissionLower
namespace HK
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open FA JN IB
open PR BD
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap:ℕ}
local notation "Ω" =>GenericField K
def rawFirstFlag (t y r:ℕ):FlagDegree:=
  RCN198.center (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r)+
    w • (⟨LocatorHybridCells.cellA t y,LocatorHybridCells.cellB y r+1,LocatorHybridCells.cellS r+2⟩:FlagDegree)
end
end HK
end SubmissionLower
end ProximityPrize
end MergedPart1
section MergedPart4
namespace ProximityPrize
namespace SubmissionLower
namespace BJU
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN156 RCN234 FA RCN130 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
structure Data (nodes:I ↪ K) (u0 u1:I→K) where
  D:ℕ
  t:ℕ
  y:ℕ
  r:ℕ
  Dlow:131072≤D
  Dchar:D<2130706433
  tbound:t≤7501
  ybound:y≤142
  rbound:r≤31
  rpos:3≤r
  ry:r+2≤y
  yt:y+2≤t
  F:MvPolynomial (Fin 4) K
  irreducible:Irreducible F
  rdegree:0<F.degreeOf 2
  box:F ∈ RCN174.globalCoefficientBox K D w t r
  support:RCN275.ResidualSupportData (LocatorHybridCells.cellSupport t y r) F
  selected:K→Polynomial K
  seeds:Finset K
  degree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w
  agreement: ∀gamma ∈ seeds,181265≤
    (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  solution: ∀gamma ∈ seeds,RCN319.specialization K (selected gamma) gamma F=0
  regular: ∀gamma ∈ seeds,
    RCN319.specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil:BL selected seeds w 80879
end
end BJU
end SubmissionLower
end ProximityPrize
end MergedPart4
end
section
section MergedPart2
namespace ProximityPrize
namespace SubmissionLower
namespace AAG
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN156 RCN234 FA RCN130 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
structure Data (nodes:I ↪ K) (u0 u1:I→K) where
  D:ℕ
  t:ℕ
  y:ℕ
  r:ℕ
  Dlow:131072≤D
  Dchar:D<2130706433
  tbound:t≤7501
  ybound:y≤142
  rbound:r≤31
  rpos:3≤r
  ry:r+2≤y
  yt:y+2≤t
  F:MvPolynomial (Fin 4) K
  irreducible:Irreducible F
  rdegree:0<F.degreeOf 2
  box:F ∈ RCN174.globalCoefficientBox K D w t r
  support:RCN275.ResidualSupportData (LocatorHybridCells.cellSupport t y r) F
  selected:K→Polynomial K
  seeds:Finset K
  degree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w
  agreement: ∀gamma ∈ seeds,181059≤
    (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  solution: ∀gamma ∈ seeds,RCN319.specialization K (selected gamma) gamma F=0
  regular: ∀gamma ∈ seeds,
    RCN319.specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil:BL selected seeds w 81085
namespace Data
variable {nodes:I ↪ K} {u0 u1:I→K}
def restrict (S:Data nodes u0 u1) (Delta:Finset K) (hsub:Delta ⊆ S.seeds):
    Data nodes u0 u1:=
  {S with
           seeds:=Delta
           degree:=fun gamma h=>S.degree gamma (hsub h)
           agreement:=fun gamma h=>S.agreement gamma (hsub h)
           solution:=fun gamma h=>S.solution gamma (hsub h)
           regular:=fun gamma h=>S.regular gamma (hsub h)
           noPencil:=KX S.selected S.seeds Delta w 81085 hsub S.noPencil}
def pair (S:Data nodes u0 u1) (R capY T:ℕ):DG:=
  ⟨262144,131071,181059,S.y,S.r,S.t,capY,R,T⟩
end Data
end
end AAG
end SubmissionLower
end ProximityPrize
end MergedPart2
section MergedPart3
namespace ProximityPrize
namespace SubmissionLower
namespace KB
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN222 renaming GeometricFactor → EX
open RCN319 renaming specialization → BM
open FA
open AAG BD BB
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
structure Params where
  m:ℕ
  B:ℕ
  s:ℕ
  U:ℕ
  L:ℕ
  k:ℕ
  n0:ℕ
  deriving DecidableEq,Repr
def Params.d (P:Params):ℕ:=P.k+1
def Params.flag (P:Params):FlagDegree:=SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
end
end KB
end SubmissionLower
end ProximityPrize
end MergedPart3
section MergedPart5
namespace ProximityPrize
namespace SubmissionLower
namespace GU
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 FA
open RCN095 renaming PolynomialInFlag → BI
open KB BD AAG
open MovingFiberThreeSources6811 (direction weight)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def CZ (a b c capY capR capT:ℕ):ℕ:=
  131073*((1+262142*(a+b+5))*((a+3)*capT+(a+b+c+5)*capR)+
    131071*(2*a+5)*((a+b+5)*capT+(a+b+c+5)*capY)+
    (1+262142*(a+b+c+5))*((a+b+5)*capR+(a+3)*capY))+
    81086*49988*((a+b+5)*capR+(a+3)*capY)
def coeff (P:Params) (a b c:ℕ):ℕ:=CZ a b c P.U P.B P.L
end GU
end SubmissionLower
end ProximityPrize
end MergedPart5
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open MvPolynomial
variable {Ω:Type*} [Field Ω]
theorem FUC {R:Type*} [CommRing R] [Algebra Ω R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (z:Fin 3→R) (hGz:aeval z G=0) (hPz:aeval z P=0):
    ∃Q:MvPolynomial (Fin 2) Ω,Q ≠ 0∧aeval (fun m=>z m.succ) Q=0:=by
  classical
  let e:=finSuccEquiv Ω 2
  have hback: ∀q:MvPolynomial (Fin 2) Ω,
      aeval z (e.symm (Polynomial.C q))=aeval (fun m=>z m.succ) q:=by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a=>
      have h1:e.symm (Polynomial.C (C a))=C a:=
        RingHom.congr_fun (finSuccEquiv_comp_C_eq_C (R:=Ω) 2) a
      rw [h1,aeval_C,aeval_C]
    | add p q hp hq=>simp only [map_add,hp,hq]
    | mul_X p j hp=>
      have h1:e.symm (Polynomial.C (MvPolynomial.X j))=MvPolynomial.X j.succ:=by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply,finSuccEquiv_X_succ]
      simp only [map_mul,h1,hp,aeval_X]
  have hg:Irreducible (e G):=(MulEquiv.irreducible_iff e).mpr hG
  have hgp: ¬e G ∣ e P:=by
    rintro ⟨c,hc⟩
    exact hGP ⟨e.symm c,by apply e.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hc]⟩
  by_cases hdeg:(e G).natDegree=0
  · refine ⟨(e G).coeff 0,?_,?_⟩
    · intro h0
      apply hg.ne_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg,h0,map_zero]
    · rw [← hback,← Polynomial.eq_C_of_natDegree_eq_zero hdeg,AlgEquiv.symm_apply_apply,hGz]
  · obtain ⟨a,b,-,-,hab⟩:=
      Polynomial.exists_mul_add_mul_eq_C_resultant (e G) (e P) le_rfl le_rfl (Or.inl hdeg)
    refine ⟨(e G).resultant (e P),
      HFree6812.resultant_ne_zero_of_not_dvd (e G) (e P) hg (by omega) hgp,?_⟩
    rw [← hback,← hab,map_add,map_mul,map_mul,AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply,map_add,map_mul,map_mul,hGz,hPz,zero_mul,zero_mul,
      add_zero]
theorem GET {R:Type*} [CommRing R] [Algebra Ω R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (z:Fin 3→R) (hGz:aeval z G=0) (hPz:aeval z P=0) (m i:Fin 3) (hmi:m ≠ i):
    ∃Q:MvPolynomial (Fin 2) Ω,Q ≠ 0∧aeval ![z m,z i] Q=0:=by
  classical
  let i' :=Equiv.swap 1 m i
  have hi' :i' ≠ 1:=by
    intro h
    exact hmi ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_left 1 m)).symm
  let σ:Equiv.Perm (Fin 3):=Equiv.swap 1 m*Equiv.swap 2 i'
  have hσ1:σ 1=m:=by
    change Equiv.swap 1 m (Equiv.swap 2 i' 1)=m
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) hi'.symm,Equiv.swap_apply_left]
  have hσ2:σ 2=i:=by
    change Equiv.swap 1 m (Equiv.swap 2 i' 2)=i
    rw [Equiv.swap_apply_left,Equiv.swap_apply_self]
  let r:=renameEquiv Ω σ.symm
  have hr: ∀p:MvPolynomial (Fin 3) Ω,aeval (z ∘ σ) (r p)=aeval z p:=by
    intro p
    change aeval (z ∘ σ) (rename σ.symm p)=aeval z p
    rw [aeval_rename,show (z ∘ σ) ∘ σ.symm=z by funext x;simp]
  have hG' :Irreducible (r G):=(MulEquiv.irreducible_iff r).mpr hG
  have hGP' : ¬r G ∣ r P:=by
    rintro ⟨c,hc⟩
    exact hGP ⟨r.symm c,by apply r.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hc]⟩
  obtain ⟨Q,hQ,hQz⟩:=FUC (r G) (r P) hG' hGP' (z ∘ σ)
    (by rw [hr,hGz]) (by rw [hr,hPz])
  have hfun:(fun j:Fin 2=>(z ∘ σ) j.succ)= ![z m,z i]:=by
    funext j
    fin_cases j
    · simp [hσ1]
    · simp [hσ2]
  rw [hfun] at hQz
  exact ⟨Q,hQ,hQz⟩
theorem EOA {E R:Type*} [Field E] [Field R] [Algebra Ω E] [Algebra E R]
    [Algebra Ω R] [IsScalarTower Ω E R] (t:E) (ht:Transcendental Ω t) (a:R)
    (Q:MvPolynomial (Fin 2) Ω) (hQ:Q ≠ 0) (h:aeval ![a,algebraMap E R t] Q=0):
    IsAlgebraic E a:=by
  classical
  let e:=finSuccEquiv Ω 1
  let φt:MvPolynomial (Fin 1) Ω→ₐ[Ω] E:=aeval ![t]
  have hinj:Function.Injective φt:=
    algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_iff_transcendental.mpr ht)
  let q:Polynomial E:=(e Q).map φt.toRingHom
  have hq0:q ≠ 0:=by
    intro h
    apply hQ
    have h1:e Q=0:=by
      apply Polynomial.map_injective φt.toRingHom hinj
      rw [Polynomial.map_zero]
      exact h
    simpa using congrArg e.symm h1
  refine ⟨q,hq0,?_⟩
  let Ψ:MvPolynomial (Fin 2) Ω→ₐ[Ω] R:=
    ((Polynomial.aeval a).restrictScalars Ω).comp ((Polynomial.mapAlgHom φt).comp e.toAlgHom)
  have hΨ:Ψ=aeval ![a,algebraMap E R t]:=by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · simp [Ψ,e,finSuccEquiv_X_zero]
    · have hX1:e (MvPolynomial.X 1)=Polynomial.C (MvPolynomial.X 0):=finSuccEquiv_X_succ (j:=0)
      show Polynomial.aeval a ((e (MvPolynomial.X 1)).map (φt:MvPolynomial (Fin 1) Ω→+*E))=_
      rw [hX1,Polynomial.map_C,Polynomial.aeval_C]
      simp [φt]
  have h1:Ψ Q=Polynomial.aeval a q:=rfl
  rw [← h1,hΨ,h]
theorem DLB {E R:Type*} [Field E] [Field R] [Algebra Ω E]
    [Algebra E R] [Algebra Ω R] [IsScalarTower Ω E R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (y:Fin 3→R) (hGy:aeval y G=0) (hPy:aeval y P=0)
    (i:Fin 3) (c:Fin 3→Ω) (hci:c i=1) (t:E) (ht:Transcendental Ω t)
    (hℓ: ∑ m,algebraMap Ω R (c m)*y m=algebraMap E R t):
    ∀m,IsAlgebraic E (y m):=by
  classical
  let f:Fin 3→MvPolynomial (Fin 3) Ω:=fun m=>
    if m=i then MvPolynomial.X i- ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' else MvPolynomial.X m
  let g:Fin 3→MvPolynomial (Fin 3) Ω:=fun m=>
    if m=i then ∑ m',C (c m')*MvPolynomial.X m' else MvPolynomial.X m
  have herase: ∀T:MvPolynomial (Fin 3) Ω,
      ∑ m' ∈ Finset.univ.erase i,C (c m')*(if m' =i then T else MvPolynomial.X m')=
        ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' :=fun T=>
    Finset.sum_congr rfl (fun m' hm' =>by rw [if_neg (Finset.ne_of_mem_erase hm')])
  have hsplit: ∑ m',C (c m')*(MvPolynomial.X m' :MvPolynomial (Fin 3) Ω)=
      MvPolynomial.X i+ ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' :=by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),hci,map_one,one_mul]
  have hgf: ∀m,bind₁ g (f m)=MvPolynomial.X m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,g,if_true,map_sub,map_sum,map_mul,bind₁_X_right,bind₁_C_right]
      rw [herase,hsplit]
      ring
    · simp [f,g,hm]
  have hfg: ∀m,bind₁ f (g m)=MvPolynomial.X m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,g,if_true,map_sum,map_mul,bind₁_X_right,bind₁_C_right]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul,if_pos rfl,
        herase]
      ring
    · simp [f,g,hm]
  let τ:MvPolynomial (Fin 3) Ω ≃ₐ[Ω] MvPolynomial (Fin 3) Ω:=
    AlgEquiv.ofAlgHom (bind₁ f) (bind₁ g)
      (MvPolynomial.algHom_ext fun m=>by simp [hfg])
      (MvPolynomial.algHom_ext fun m=>by simp [hgf])
  let z:Fin 3→R:=fun m=>if m=i then algebraMap E R t else y m
  have hz: ∀m,aeval z (f m)=y m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,z,if_true,map_sub,map_sum,map_mul,aeval_X,aeval_C]
      rw [Finset.sum_congr rfl (fun m' hm' =>by rw [if_neg (Finset.ne_of_mem_erase hm')]),
        ← hℓ,← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul]
      ring
    · simp [f,z,hm]
  have hτ: ∀p,aeval z (τ p)=aeval y p:=by
    intro p
    change aeval z (bind₁ f p)=aeval y p
    rw [aeval_bind₁,show (fun m=>aeval z (f m))=y from funext hz]
  have hG' :Irreducible (τ G):=(MulEquiv.irreducible_iff τ).mpr hG
  have hGP' : ¬τ G ∣ τ P:=by
    rintro ⟨d,hd⟩
    exact hGP ⟨τ.symm d,by apply τ.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hd]⟩
  have hother: ∀m,m ≠ i→IsAlgebraic E (y m):=by
    intro m hm
    obtain ⟨Q,hQ,hQz⟩:=GET (τ G) (τ P) hG' hGP' z
      (by rw [hτ,hGy]) (by rw [hτ,hPy]) m i hm
    have hzz: ![z m,z i]= ![y m,algebraMap E R t]:=by simp [z,hm]
    rw [hzz] at hQz
    exact EOA t ht (y m) Q hQ hQz
  intro m
  by_cases hm:m=i
  · subst hm
    have hy:y m=algebraMap E R t-
        ∑ m' ∈ Finset.univ.erase m,algebraMap Ω R (c m')*y m' :=by
      rw [← hℓ,← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul]
      ring
    rw [isAlgebraic_iff_isIntegral,hy]
    refine (integralClosure E R).sub_mem (IsIntegral.algebraMap isIntegral_algebraMap)
      ((integralClosure E R).sum_mem fun m' hm' => ?_)
    refine (integralClosure E R).mul_mem ?_ ?_
    · rw [IsScalarTower.algebraMap_apply Ω E R]
      exact IsIntegral.algebraMap isIntegral_algebraMap
    · exact isAlgebraic_iff_isIntegral.mp (hother m' (Finset.ne_of_mem_erase hm'))
  · exact hother m hm
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341
section Contraction
variable {Ω E:Type} [Field Ω] [Field E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
theorem GPB (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:RCN341.SeparableLiteralCoordinate D) (G:MvPolynomial (Fin 3) Ω) (hG:Irreducible G)
    (hGD:RCN208.scalarPolynomialMap Ω E G ∈ D) (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue Ω E)-
      RCN208.scalarPolynomialMap Ω E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    D.comap (RCN208.scalarPolynomialMap Ω E)=Ideal.span {G}:=by
  classical
  have hev: ∀A:MvPolynomial (Fin 3) Ω,
      aeval (coordinate E D) A=RCN002.coordinateEvaluation E D (RCN208.scalarPolynomialMap Ω E A):=by
    intro A
    rw [RCN002.coordinateEvaluation_eq_aeval,RCN208.scalarPolynomialMap,aeval_map_algebraMap]
  have hzero: ∀A:MvPolynomial (Fin 3) E,A ∈ D→RCN002.coordinateEvaluation E D A=0:=
    fun A hA=>(HFree6812.coordEval_eq_zero_iff D A).2 hA
  apply le_antisymm
  · intro P hP
    rw [Ideal.mem_span_singleton]
    by_contra hGP
    have hℓ: ∑ m,algebraMap Ω (RCN002.CoordinateField E D) (c m)*coordinate E D m=
        algebraMap E (RCN002.CoordinateField E D) (sliceValue Ω E):=by
      have h1:=hzero _ hslice
      rw [map_sub,sub_eq_zero] at h1
      rw [← hev] at h1
      have h2:RCN002.coordinateEvaluation E D (MvPolynomial.C (sliceValue Ω E))=
          algebraMap E (RCN002.CoordinateField E D) (sliceValue Ω E):=
        (RCN002.coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum,map_mul,aeval_C,aeval_X]
    have halg:=DLB G P hG hGP (coordinate E D)
      (by rw [hev];exact hzero _ hGD) (by rw [hev];exact hzero _ hP) i c hci
      (sliceValue Ω E) HFree6812.sliceValue_transcendental hℓ
    exact sep.transcendental (halg sep.index)
  · rw [Ideal.span_le,Set.singleton_subset_iff]
    exact hGD
end Contraction
section Descent
variable {K:Type} [Field K] {E:Type} [Field E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
theorem FVZ (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:RCN341.SeparableLiteralCoordinate D) (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hFD:surfaceMap ((algebraMap (GenericField K) E).comp (RCN135.polynomialEmbedding K)) F ∈ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    ∃F₀:MvPolynomial (Fin 4) K,Irreducible F₀∧F₀ ∣ F∧
      RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀}:=by
  classical
  set φ:=RCN135.polynomialEmbedding K
  have hA:surfaceMap φ F ≠ 0:=RCN136.surfaceMap_ne_zero φ (RCN135.polynomialEmbedding_injective K) F hF
  have hAD:RCN208.scalarPolynomialMap (GenericField K) E (surfaceMap φ F) ∈ D:=by
    rw [← HFree6812.surfaceMap_generic_eq];exact hFD
  obtain ⟨G,hG,-,hGD⟩:=HFree6812.exists_irreducible_mem D (surfaceMap φ F) hA hAD
  have hcomap:=GPB D sep G hG hGD c i hci hslice
  have hker:RingHom.ker (sliceMap (K:=K) D)=RCN219.originalPrime (Ideal.span {G}):=by
    ext A
    rw [RingHom.mem_ker,RCN219.mem_originalPrime_iff,← hcomap,Ideal.mem_comap,
      ← HFree6812.surfaceMap_generic_eq]
    exact HFree6812.coordEval_eq_zero_iff D _
  haveI hGprime:(Ideal.span {G}).IsPrime:=
    (Ideal.span_singleton_prime hG.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hG)
  have hGheight:(Ideal.span {G}).height=1:=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hG.ne_zero) hG.not_isUnit
  set Q:=RingHom.ker (sliceMap (K:=K) D)
  haveI hQprime:Q.IsPrime:=RingHom.ker_isPrime _
  have hQheight:Q.height≤1:=by
    rw [hker,← hGheight]
    exact RCN219.originalPrime_height_le _
  have hFQ:F ∈ Q:=(HFree6812.coordEval_eq_zero_iff D _).2 hFD
  have hQbot:Q ≠ ⊥ :=by
    intro h;rw [h] at hFQ;exact hF ((Submodule.mem_bot _).mp hFQ)
  obtain ⟨F₀,hF₀Q,hF₀⟩:=hQprime.exists_mem_prime_of_ne_bot hQbot
  haveI hF₀prime:(Ideal.span {F₀}).IsPrime:=(Ideal.span_singleton_prime hF₀.ne_zero).mpr hF₀
  have hF₀height:(Ideal.span {F₀}).height=1:=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hF₀.ne_zero) hF₀.not_unit
  have hle:Ideal.span {F₀}≤Q:=by
    rw [Ideal.span_le,Set.singleton_subset_iff];exact hF₀Q
  have heq:Ideal.span {F₀}=Q:=by
    by_contra hne
    have hlt:=Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hF₀height] at hlt
    have h2:(2:ℕ∞)≤1:=hlt.trans hQheight
    exact absurd h2 (by decide)
  refine ⟨F₀,hF₀.irreducible,?_,heq.symm⟩
  rw [← Ideal.mem_span_singleton,heq]
  exact hFQ
end Descent
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero Polynomial
section Local
variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)
variable {A:Type*} [CommRing A] (φ:A→+*L)
theorem node_case_p19 (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g)
    (a b:A) (ha:v (φ a)<1)
    (hgen: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*a+y*b)
    (α β γ:A) (hγ:v (φ γ)=1) (hδ:v (φ (β^2-4*α*γ))=1)
    (hrel:φ α*φ a^2+φ β*φ a*φ b+φ γ*φ b^2=0):
    v (φ a)=exp (-1):=by
  have hγ0:φ γ ≠ 0:=by intro h;rw [h,v.map_zero] at hγ;exact zero_ne_one hγ
  have hunit: ∀g:A,v (φ g)=1→φ g ≠ 0:=by
    intro g hg h;rw [h,v.map_zero] at hg;exact zero_ne_one hg

  have ha0:φ a ≠ 0:=by
    intro ha0
    have hb0:φ b=0:=by
      rw [ha0] at hrel
      have h1:φ γ*φ b^2=0:=by linear_combination hrel
      exact pow_eq_zero_iff (n:=2) (by norm_num) |>.1 ((mul_eq_zero.1 h1).resolve_left hγ0)
    obtain ⟨f,hf,hf0⟩:=HFree6812.center_nonzero v φ hint hsurj hfrac
    obtain ⟨s,x,y,hs,hsf⟩:=hgen f hf
    have h1:=congrArg φ hsf
    simp only [map_mul,map_add,ha0,hb0,mul_zero,add_zero] at h1
    exact hf0 ((mul_eq_zero.1 h1).resolve_left (hunit s hs))
  set z:L:=φ b/φ a with hz_def
  have hz:φ b=φ a*z:=by rw [hz_def,mul_div_cancel₀ _ ha0]
  have hQ:φ α+φ β*z+φ γ*z^2=0:=by
    have h1:φ a^2*(φ α+φ β*z+φ γ*z^2)=0:=by
      rw [hz] at hrel;linear_combination hrel
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 ha0)

  have hzint:v z≤1:=by
    by_contra hz1
    rw [not_le] at hz1
    have h1:φ γ*z^2= -(φ α+φ β*z):=by linear_combination hQ
    have h2:=congrArg v h1
    rw [v.map_mul,hγ,one_mul,v.map_pow,v.map_neg] at h2
    have h3:v (φ α+φ β*z)≤v z:=by
      refine (v.map_add _ _).trans (max_le ((hint α).trans hz1.le) ?_)
      rw [v.map_mul];exact mul_le_of_le_one_left' (hint β)
    have h4:v z<v z^2:=by
      rw [sq];exact lt_mul_of_one_lt_left (zero_lt_one.trans hz1) hz1
    rw [← h2] at h3
    exact absurd h3 (not_le.2 h4)

  set w:L:=2*φ γ*z+φ β with hw_def
  have hw2:w^2=φ (β^2-4*α*γ):=by
    rw [hw_def];simp only [map_sub,map_mul,map_pow,map_ofNat]
    linear_combination 4*φ γ*hQ
  have hw:v w=1:=by
    have h1:v w^2=1:=by rw [← v.map_pow,hw2,hδ]
    rcases lt_trichotomy (v w) 1 with h | h | h
    · exact absurd h1 (ne_of_lt (by rw [sq];exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h h.le))
    · exact h
    · exact absurd h1 (ne_of_gt (by rw [sq];exact one_lt_mul_of_lt_of_le h h.le))

  set S:Subring L:=(Polynomial.eval₂RingHom φ z).range with hS_def
  have hSφ: ∀g:A,φ g ∈ S:=fun g=>⟨C g,by simp⟩
  have hSz:z ∈ S:=⟨Polynomial.X,by simp⟩
  have h2S:(2:L) ∈ S:=by rw [← map_ofNat φ 2];exact hSφ 2
  have hSint: ∀h ∈ S,v h≤1:=by
    rintro _ ⟨P,rfl⟩
    rw [Polynomial.coe_eval₂RingHom]
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ' =>rw [Polynomial.eval₂_add];exact (v.map_add _ _).trans (max_le hP hQ')
    | monomial n g=>
      rw [Polynomial.eval₂_monomial,v.map_mul,v.map_pow]
      exact mul_le_one' (hint g) (pow_le_one' hzint n)

  have hpow: ∀n:ℕ,∃c₀ c₁:A,φ γ^n*z^n=φ c₀+φ c₁*z:=by
    intro n
    induction n with
    | zero=>exact ⟨1,0,by simp⟩
    | succ n ih=>
      obtain ⟨c₀,c₁,h⟩:=ih
      refine ⟨-(c₁*α),γ*c₀-c₁*β,?_⟩
      simp only [map_neg,map_mul,map_sub]
      linear_combination (φ γ*z)*h+φ c₁*hQ
  have hlin: ∀P:A[X],∃N:ℕ,∃c₀ c₁:A,
      φ γ^N*P.eval₂ φ z=φ c₀+φ c₁*z:=by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ' =>
      obtain ⟨N₁,c₀,c₁,h₁⟩:=hP
      obtain ⟨N₂,d₀,d₁,h₂⟩:=hQ'
      refine ⟨N₁+N₂,γ^N₂*c₀+γ^N₁*d₀,γ^N₂*c₁+γ^N₁*d₁,?_⟩
      simp only [Polynomial.eval₂_add,map_add,map_mul,map_pow,pow_add]
      linear_combination φ γ^N₂*h₁+φ γ^N₁*h₂
    | monomial n g=>
      obtain ⟨c₀,c₁,h⟩:=hpow n
      refine ⟨n,g*c₀,g*c₁,?_⟩
      simp only [Polynomial.eval₂_monomial,map_mul]
      linear_combination φ g*h

  have hdeg1: ∀c₀ c₁:A,v (φ c₀+φ c₁*z)<1→
      ∃u ∈ S,v u=1∧ ∃h' ∈ S,u*(φ c₀+φ c₁*z)=φ a*h' :=by
    intro c₀ c₁ he
    by_cases hc₁:v (φ c₁)<1
    · have hc₀:v (φ c₀)<1:=by
        have h1:φ c₀=(φ c₀+φ c₁*z)-φ c₁*z:=by ring
        rw [h1]
        refine (v.map_sub _ _).trans_lt (max_lt he ?_)
        rw [v.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' hzint) hc₁
      obtain ⟨s₀,x₀,y₀,hs₀,h₀⟩:=hgen c₀ hc₀
      obtain ⟨s₁,x₁,y₁,hs₁,h₁⟩:=hgen c₁ hc₁
      have h₀' :=congrArg φ h₀
      have h₁' :=congrArg φ h₁
      simp only [map_mul,map_add] at h₀' h₁'
      refine ⟨φ (s₀*s₁),hSφ _,by rw [map_mul,v.map_mul,hs₀,hs₁,one_mul],
        φ s₁*(φ x₀+φ y₀*z)+φ s₀*(φ x₁+φ y₁*z)*z,?_,?_⟩
      · exact S.add_mem (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)))
          (S.mul_mem (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz))) hSz)
      · rw [map_mul]
        linear_combination φ s₁*h₀' +φ s₀*z*h₁' +(φ s₁*φ y₀+φ s₀*φ y₁*z)*hz
    · have hc₁1:v (φ c₁)=1:=HFree6812.v_eq_one_of_not_lt v φ hint c₁ hc₁
      set e:L:=φ c₀+φ c₁*z with he_def
      set M:L:=φ c₁*w-φ γ*e with hM_def
      have hM:v M=1:=by
        rw [hM_def,Valuation.map_sub_eq_of_lt_left]
        · rw [v.map_mul,hc₁1,hw,one_mul]
        · rw [v.map_mul,v.map_mul,hγ,hc₁1,hw,one_mul,one_mul];exact he
      have hN:φ (c₁^2*α-c₁*c₀*β+c₀^2*γ)= -(e*M):=by
        rw [hM_def,he_def,hw_def];simp only [map_sub,map_add,map_mul,map_pow]
        linear_combination φ c₁^2*hQ
      have hNlt:v (φ (c₁^2*α-c₁*c₀*β+c₀^2*γ))<1:=by
        rw [hN,v.map_neg,v.map_mul,hM,mul_one];exact he
      obtain ⟨s,x,y,hs,hsN⟩:=hgen _ hNlt
      have h1:=congrArg φ hsN
      rw [map_mul,hN,map_add,map_mul,map_mul] at h1
      have hMS:M ∈ S:=by
        rw [hM_def,hw_def,he_def]
        exact S.sub_mem (S.mul_mem (hSφ _) (S.add_mem (S.mul_mem (S.mul_mem h2S (hSφ _)) hSz)
          (hSφ _))) (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)))
      refine ⟨φ s*M,S.mul_mem (hSφ _) hMS,by rw [v.map_mul,hs,hM,one_mul],
        -(φ x+φ y*z),S.neg_mem (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)),?_⟩
      linear_combination-h1-φ y*hz

  have hloc: ∀h ∈ S,v h<1→ ∃u ∈ S,v u=1∧ ∃h' ∈ S,u*h=φ a*h' :=by
    rintro _ ⟨P,rfl⟩ hlt
    rw [Polynomial.coe_eval₂RingHom] at hlt ⊢
    obtain ⟨N,c₀,c₁,hN⟩:=hlin P
    have hvN:v (φ γ^N)=1:=by rw [v.map_pow,hγ,one_pow]
    have he:v (φ c₀+φ c₁*z)<1:=by rw [← hN,v.map_mul,hvN,one_mul];exact hlt
    obtain ⟨u,huS,hu,h',hh',hu'⟩:=hdeg1 c₀ c₁ he
    refine ⟨u*φ γ^N,S.mul_mem huS (S.pow_mem (hSφ _) _),by
      rw [v.map_mul,hu,hvN,one_mul],h',hh',?_⟩
    rw [mul_assoc,hN,hu']
  have hfracS: ∀x:L,∃f ∈ S,∃g ∈ S,g ≠ 0∧x=f/g:=by
    intro x
    obtain ⟨f,g,hg,rfl⟩:=hfrac x
    exact ⟨φ f,hSφ f,φ g,hSφ g,hg,rfl⟩
  exact HFree6812.smooth_branch v S hSint hfracS hsurj (φ a) ha hloc
variable {R:Type*} [CommRing R] [Algebra R A] (D₀:Derivation R A A)
theorem GIW (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g) (h2:v (2:L)=1)
    (F:A) (hF:φ F=0)
    (a b:A) (ha:v (φ a)<1) (hb:v (φ b)<1)
    (hgen: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*a+y*b)
    (n₁:ℕ) (hn₁: ∀g:A,v (φ g)<1→v (φ g)≤exp (-(n₁:ℤ))):
    n₁≤1∨v (φ (D₀ F))^2≤exp (-(3*n₁:ℤ)):=by
  have hone: ∀t:A,v (φ t)<1→v (φ t)=exp (-1)→n₁≤1:=by
    intro t ht h1
    have h3:=hn₁ t ht
    rw [h1,exp_le_exp] at h3;omega
  have hswap: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*b+y*a:=by
    intro g hg
    obtain ⟨s,x,y,h1,h3⟩:=hgen g hg
    exact ⟨s,y,x,h1,by rw [h3];ring⟩
  have hunit:=HFree6812.v_eq_one_of_not_lt v φ hint
  have hFP:v (φ F)<1:=by rw [hF,v.map_zero];exact zero_lt_one
  obtain ⟨s,α,β,hs,hsF⟩:=hgen F hFP
  have hφsF:=congrArg φ hsF
  simp only [map_mul,map_add,hF,mul_zero] at hφsF

  by_cases hα:v (φ α)<1
  swap
  · exact Or.inl (hone b hb (linear_case v φ hint hsurj hfrac a b hb hgen α β (hunit α hα)
      (by linear_combination-hφsF)))
  by_cases hβ:v (φ β)<1
  swap
  · exact Or.inl (hone a ha (linear_case v φ hint hsurj hfrac b a ha hswap β α (hunit β hβ)
      (by linear_combination-hφsF)))

  obtain ⟨s₁,α₁,α₂,hs₁,h₁⟩:=hgen α hα
  obtain ⟨s₂,β₁,β₂,hs₂,h₂⟩:=hgen β hβ
  have hrep:(s₁*s₂*s)*F=(s₂*α₁)*a^2+(s₂*α₂+s₁*β₁)*a*b+
      (s₁*β₂)*b^2:=by
    linear_combination (s₁*s₂)*hsF+s₂*a*h₁+s₁*b*h₂
  set s' :=s₁*s₂*s
  set A₂:=s₂*α₁
  set B₂:=s₂*α₂+s₁*β₁
  set C₂:=s₁*β₂
  have hs' :v (φ s')=1:=by simp only [s',map_mul,v.map_mul,hs,hs₁,hs₂,one_mul]
  have hrel:φ A₂*φ a^2+φ B₂*φ a*φ b+φ C₂*φ b^2=0:=by
    have h3:=congrArg φ hrep
    simp only [map_mul,map_add,map_pow,hF,mul_zero] at h3
    linear_combination-h3

  by_cases hall:v (φ A₂)<1∧v (φ B₂)<1∧v (φ C₂)<1
  · right
    have h3:=cube_case v φ D₀ hint F hF n₁ hn₁ a b ha hb s' A₂ B₂ C₂ hs' hall.1 hall.2.1
      hall.2.2 hrep
    rw [sq]
    refine (mul_le_mul' h3 h3).trans ?_
    rw [← exp_add,exp_le_exp];omega
  by_cases hδ:v (φ (B₂^2-4*A₂*C₂))<1
  ·
    right
    by_cases hA:v (φ A₂)<1
    · have hC: ¬v (φ C₂)<1:=by
        intro hC
        apply hall
        refine ⟨hA,?_,hC⟩
        by_contra hB
        have hB1:=hunit B₂ hB
        have h3:φ B₂^2=φ (B₂^2-4*A₂*C₂)+4*φ A₂*φ C₂:=by
          simp only [map_sub,map_mul,map_pow,map_ofNat];ring
        have h4:=congrArg v h3
        rw [v.map_pow,hB1,one_pow] at h4
        have h5:v (4*φ A₂*φ C₂)<1:=by
          rw [v.map_mul,v.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (mul_le_one' (by
            rw [show (4:L)=φ 4 from (map_ofNat φ 4).symm];exact hint 4) (hint A₂)))
            hC
        exact absurd h4 (ne_of_gt ((v.map_add _ _).trans_lt (max_lt hδ h5)))
      exact cusp_case v φ D₀ hint h2 F hF n₁ hn₁ b a ha s' C₂ B₂ A₂ hs' (hunit C₂ hC)
        (by rwa [show B₂^2-4*C₂*A₂=B₂^2-4*A₂*C₂ by ring])
        (by rw [hrep];ring)
    · exact cusp_case v φ D₀ hint h2 F hF n₁ hn₁ a b hb s' A₂ B₂ C₂ hs' (hunit A₂ hA) hδ hrep

  left
  have hδ1:=hunit _ hδ
  by_cases hC:v (φ C₂)<1
  · by_cases hA:v (φ A₂)<1
    ·
      have hB:v (φ B₂)=1:=by
        by_contra hB
        have hB' :v (φ B₂)<1:=lt_of_le_of_ne (hint B₂) hB
        exact hall ⟨hA,hB',hC⟩
      have hγ' :v (φ (A₂-B₂+C₂))=1:=by
        have h3:φ (A₂-B₂+C₂)= -φ B₂+(φ A₂+φ C₂):=by
          simp only [map_add,map_sub];ring
        rw [h3,Valuation.map_add_eq_of_lt_left,v.map_neg,hB]
        rw [v.map_neg,hB]
        exact (v.map_add _ _).trans_lt (max_lt hA hC)
      have hgen' : ∀g:A,v (φ g)<1→
          ∃s x y:A,v (φ s)=1∧s*g=x*(a+b)+y*b:=by
        intro g hg
        obtain ⟨s,x,y,h1,h3⟩:=hgen g hg
        exact ⟨s,x,y-x,h1,by rw [h3];ring⟩
      have hab:v (φ (a+b))<1:=by
        rw [map_add];exact (v.map_add _ _).trans_lt (max_lt ha hb)
      exact hone _ hab (node_case_p19 v φ hint hsurj hfrac (a+b) b hab hgen' A₂ (B₂-2*A₂)
        (A₂-B₂+C₂) hγ'
        (by rwa [show (B₂-2*A₂)^2-4*A₂*(A₂-B₂+C₂)=B₂^2-4*A₂*C₂ by ring])
        (by simp only [map_add,map_sub,map_mul,map_ofNat];linear_combination hrel))
    · exact hone b hb (node_case_p19 v φ hint hsurj hfrac b a hb hswap C₂ B₂ A₂ (hunit A₂ hA)
        (by rwa [show B₂^2-4*C₂*A₂=B₂^2-4*A₂*C₂ by ring])
        (by linear_combination hrel))
  · exact hone a ha (node_case_p19 v φ hint hsurj hfrac a b ha hgen A₂ B₂ C₂ (hunit C₂ hC) hδ1 hrel)
end Local
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN313 RCN055
section Slice
variable {K:Type} [Field K] (F F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]
  (hdvd:F₀ ∣ F)
set_option linter.unusedSectionVars false
variable (v:Valuation (SliceField F₀) ℤᵐ⁰)
theorem place_bound_p19 (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm: ∃x,v x=exp (-1))
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1)
    (ℓ:SliceField F₀)
    (hℓ:v (HFree6812.sliceDerivation F F₀ hdvd ℓ)≤max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (C:ℤ) (hcrude:CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)
    (hsep:HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
      (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd ℓ))))
    (h2:(2:K) ≠ 0)
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0)
    (hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b)
    (m:ℕ):
    3*vpole v ((⇑(HFree6812.sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1))≤
      m*(4*placeT F F₀ v+2*placeH F F₀ v)+3*placeP F₀ v:=by
  classical
  haveI:v.IsTrivialOn K:=⟨hK⟩
  set Dd:=HFree6812.sliceDerivation F F₀ hdvd with hDd
  set P:=placeP F₀ v with hPdef
  set T:=placeT F F₀ v with hTdef
  set h:=placeH F F₀ v with hhdef
  set pσ:=vpole v (sliceSigma F F₀) with hpσdef
  set s:=vpole v (Dd ℓ) with hsdef
  set p0:=vpole v (sliceCoord F₀ 0)
  set p1:=vpole v (sliceCoord F₀ 1)
  set p2:=vpole v (sliceCoord F₀ 2)
  have hp0:0≤p0:=vpole_nonneg _ _
  have hp1:0≤p1:=vpole_nonneg _ _
  have hp2:0≤p2:=vpole_nonneg _ _
  have hPeq:P=max p1 (max p0 p2):=rfl
  have hTeq:T=max (2*P) (max p0 p2+pσ):=rfl
  have hP0:0≤P:=by rw [hPeq];exact le_max_of_le_left hp1
  have hh0:0≤h:=vzero_nonneg _ _
  have hpσ0:0≤pσ:=vpole_nonneg _ _
  have hs0:0≤s:=vpole_nonneg _ _
  have hTP:2*P≤T:=by rw [hTeq];exact le_max_left _ _
  have hTσ:pσ≤T:=by
    rw [hTeq];exact le_max_of_le_right (by have:=le_max_left p0 p2;omega)
  have hsP:s≤max P pσ:=by
    rw [hsdef,vpole_le_iff _ _ _ (le_max_of_le_left hP0)]
    refine hℓ.trans (max_le ?_ ?_)
    · rw [exp_le_exp];exact le_max_left _ _
    · exact (HFree6812.v_le_exp_vpole v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
  obtain ⟨π₀,hπ₀⟩:=hnorm
  have hmθ: ∀θ:ℤ,0≤θ→3*θ≤4*T+2*h→
      3*((m:ℤ)*θ)≤m*(4*T+2*h):=by
    intro θ _ hθ
    have:=mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α:=ℤ) m)
    linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  ·
    have hPz' :P=0:=hPz.symm
    have hq0:p0=0:=by have:=le_max_left p0 p2;have:=le_max_right p1 (max p0 p2);omega
    have hq1:p1=0:=by have:=le_max_left p1 (max p0 p2);omega
    have hq2:p2=0:=by have:=le_max_right p0 p2;have:=le_max_right p1 (max p0 p2);omega
    have hcint: ∀j:Fin 3,v (sliceCoord F₀ j)≤1:=by
      intro j
      have hj:vpole v (sliceCoord F₀ j)≤0:=by
        fin_cases j
        · exact hq0.le
        · exact hq1.le
        · exact hq2.le
      have:=(vpole_le_iff v _ 0 le_rfl).1 hj
      rwa [exp_zero] at this
    have hint_all: ∀g:MvPolynomial (Fin 4) K,v (sliceProj F₀ g)≤1:=by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a=>
        rw [sliceProj_C]
        exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v a
      | add p q hp hq=>rw [map_add];exact (v.map_add _ _).trans (max_le hp hq)
      | mul_X p i hp=>
        rw [map_mul,v.map_mul]
        refine mul_le_one' hp ?_
        fin_cases i
        · exact hX0
        · exact hcint 0
        · exact hcint 1
        · exact hcint 2
    have hfrac: ∀x:SliceField F₀,∃f g:MvPolynomial (Fin 4) K,
        sliceProj F₀ g ≠ 0∧x=sliceProj F₀ f/sliceProj F₀ g:=by
      intro x
      obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=SliceRing F₀) x
      obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective a
      obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective b
      refine ⟨f,g,?_,rfl⟩
      exact (map_ne_zero_iff _ (IsFractionRing.injective (SliceRing F₀) (SliceField F₀))).2
        (nonZeroDivisors.ne_zero hb)
    have h2v:v (2:SliceField F₀)=1:=by
      rw [← map_ofNat (algebraMap K (SliceField F₀)) 2]
      exact hK 2 h2
    have hFz:sliceProj F₀ F₀=0:=(HFree6812.sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl
    obtain ⟨a,b,ha,hb,hgen'⟩:=hgen hPz'

    obtain ⟨g₀,hg₀,hg₀0⟩:=HFree6812.center_nonzero v (sliceProj F₀) hint_all ⟨π₀,hπ₀⟩ hfrac
    have hex: ∃n:ℕ,0<n∧ ∃g,v (sliceProj F₀ g)=exp (-(n:ℤ)):=by
      have hne:v (sliceProj F₀ g₀) ≠ 0:=(Valuation.ne_zero_iff v).2 hg₀0
      have hl:(v (sliceProj F₀ g₀)).log<0:=by
        rw [log_lt_iff_lt_exp hne,exp_zero];exact hg₀
      exact ⟨(-(v (sliceProj F₀ g₀)).log).toNat,by omega,g₀,
        (exp_log hne).symm.trans (by congr 1;omega)⟩
    set n₁:=Nat.find hex with hn₁def
    obtain ⟨hn₁pos,f₀,hf₀⟩:=Nat.find_spec hex
    have hn₁: ∀g,v (sliceProj F₀ g)<1→v (sliceProj F₀ g)≤exp (-(n₁:ℤ)):=by
      intro g hg
      by_cases hz:v (sliceProj F₀ g)=0
      · rw [hz];exact zero_le
      have hl:(v (sliceProj F₀ g)).log<0:=by
        rw [log_lt_iff_lt_exp hz,exp_zero];exact hg
      have hmin:=Nat.find_min' hex (m:=(-(v (sliceProj F₀ g)).log).toNat)
        ⟨by omega,g,(exp_log hz).symm.trans (by congr 1;omega)⟩
      rw [← exp_log hz,exp_le_exp]
      omega
    have hdich:=GIW v (sliceProj F₀) (MvPolynomial.pderiv (2:Fin 4)) hint_all
      ⟨π₀,hπ₀⟩ hfrac h2v F₀ hFz a b ha hb hgen' n₁ hn₁
    obtain ⟨F₁,hHF⟩:=HFree6812.sliceProj_H_eq F F₀ hdvd
    have hHne:v (sliceProj F₀ (polyH K F)) ≠ 0:=(Valuation.ne_zero_iff v).2 hH
    have hdich' :n₁≤1∨3*(n₁:ℤ)≤2*h:=by
      rcases hdich with h1 | h1
      · exact Or.inl h1
      right
      have hle:v (sliceProj F₀ (polyH K F))≤v (sliceProj F₀ (pderiv 2 F₀)):=by
        rw [hHF,v.map_mul];exact mul_le_of_le_one_left' (hint_all F₁)
      have h2' :v (sliceProj F₀ (polyH K F))^2≤exp (-(3*n₁:ℤ)):=
        (pow_le_pow_left₀ zero_le hle 2).trans h1
      rw [← exp_log hHne,← exp_nsmul,exp_le_exp] at h2'
      have:h=max 0 (-(v (sliceProj F₀ (polyH K F))).log):=rfl
      simp only [nsmul_eq_mul] at h2'
      push_cast at h2'
      omega
    have hn₁K:(n₁:K) ≠ 0:=by
      rcases hdich' with h1 | h1
      · have:n₁=1:=by omega
        rw [this,Nat.cast_one];exact one_ne_zero
      · exact hchar n₁ hn₁pos (by rw [hPz'];omega)

    have hTa:T=pσ:=by rw [hTeq,hPz',hq0,hq2];omega
    have hsσ:s≤pσ:=by have:=hsP;rw [hPz'] at this;omega
    have hDf:v (Dd (sliceProj F₀ f₀))≤exp pσ:=by
      rw [hDd,HFree6812.sliceDerivation_proj_eq F F₀ hdvd hH]
      refine (v.map_add _ _).trans (max_le ?_ ?_)
      · exact (hint_all _).trans (by rw [← exp_zero,exp_le_exp];exact hpσ0)
      · rw [v.map_mul]
        refine (mul_le_of_le_one_left' (hint_all _)).trans ?_
        exact HFree6812.v_le_exp_vpole v _
    have hθ:=HFree6812.theta_of_element v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceProj F₀ f₀) n₁ hn₁K
      hf₀ pσ hDf
    have hmax:max s (pσ+n₁)=pσ+n₁:=max_eq_right (by omega)
    rw [hmax] at hθ
    by_cases hA:pσ=0∧n₁=1
    ·
      have hπ:=HFree6812.pi_bound_general v Dd π₀ hπ₀ s pσ
        (HFree6812.integral_bound v Dd π₀ hπ₀ s hs0 C hcrude hsep) (sliceProj F₀ f₀) n₁ hn₁K hf₀ hDf
      have hs00:s=0:=by omega
      have hmx:max s (pσ+n₁)-1=0:=by rw [hmax];omega
      rw [hmx,exp_zero] at hπ
      have hD1: ∀u,v u≤1→v (Dd u)≤1:=by
        intro u hu
        refine (HFree6812.integral_bound v Dd π₀ hπ₀ s hs0 C hcrude hsep u hu).trans (max_le ?_ hπ)
        rw [hs00,exp_zero]
      have hit:=HFree6812.integral_iterate v Dd hD1 m _ (hcint 1)
      have hz:vpole v ((⇑Dd)^[m] (sliceCoord F₀ 1))≤0:=
        (vpole_le_iff v _ 0 le_rfl).2 (by rwa [exp_zero])
      have:=vpole_nonneg v ((⇑Dd)^[m] (sliceCoord F₀ 1))
      have:0≤(m:ℤ)*(4*T+2*h):=
        mul_nonneg (Nat.cast_nonneg m) (by omega)
      omega
    ·
      have hσh:pσ≤h:=by
        rw [hpσdef,vpole_le_iff _ _ _ hh0,sliceSigma,map_div₀]
        by_cases hG0:v (sliceProj F₀ (polyG K F))=0
        · rw [hG0,zero_div];exact zero_le
        · rw [div_le_iff₀ (zero_lt_iff.2 hHne)]
          calc v (sliceProj F₀ (polyG K F))≤1:=hint_all _
            _≤exp h*v (sliceProj F₀ (polyH K F)):=by
              rw [← exp_log hHne,← exp_add,← exp_zero,exp_le_exp]
              have:h=max 0 (-(v (sliceProj F₀ (polyH K F))).log):=rfl
              omega
      have hlaw:3*(pσ+n₁)≤4*T+2*h:=by
        rw [hTa]
        rcases hdich' with h1 | h1
        · have:n₁=1:=by omega
          have:pσ ≠ 0:=fun h0=>hA ⟨h0,by omega⟩
          omega
        · omega
      have hit:=HFree6812.pole_iterate_of_bound v Dd (pσ+n₁) (by omega) hθ m (sliceCoord F₀ 1)
      have:=hmθ (pσ+n₁) (by omega) hlaw
      have hc1:vpole v (sliceCoord F₀ 1)=0:=hq1
      rw [hc1,zero_add] at hit
      rw [hPz']
      omega
  ·
    obtain ⟨j,hj⟩: ∃j:Fin 3,vpole v (sliceCoord F₀ j)=P:=by
      rcases max_choice p1 (max p0 p2) with h1 | h1
      · exact ⟨1,by rw [hPeq,h1]⟩
      · rcases max_choice p0 p2 with h2 | h2
        · exact ⟨0,by rw [hPeq,h1,h2]⟩
        · exact ⟨2,by rw [hPeq,h1,h2]⟩
    have hcj0:v (sliceCoord F₀ j) ≠ 0:=by
      intro h0
      have:vpole v (sliceCoord F₀ j)=0:=by simp [vpole,h0]
      omega
    have hcj:v (sliceCoord F₀ j)=exp ((P.toNat:ℕ):ℤ):=by
      rw [← exp_log hcj0]
      congr 1
      have:vpole v (sliceCoord F₀ j)=max 0 (v (sliceCoord F₀ j)).log:=rfl
      omega
    have hPK:((P.toNat:ℕ):K) ≠ 0:=
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hP0];exact le_max_left _ _)
    have hQ:v (Dd (sliceCoord F₀ j))≤exp (max P pσ):=by
      fin_cases j
      · show v (Dd (sliceCoord F₀ 0))≤_
        rw [hDd,HFree6812.sliceDerivation_coord0 F F₀ hdvd hH]
        exact (HFree6812.v_le_exp_vpole v _).trans (by
          rw [exp_le_exp];have:=le_max_left p1 (max p0 p2);exact le_max_of_le_left (by omega))
      · show v (Dd (sliceCoord F₀ 1))≤_
        rw [hDd,HFree6812.sliceDerivation_coord1 F F₀ hdvd hH]
        exact (HFree6812.v_le_exp_vpole v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
      · show v (Dd (sliceCoord F₀ 2))≤_
        rw [hDd,HFree6812.sliceDerivation_coord2 F F₀ hdvd hH,v.map_zero];exact zero_le
    have hθ:=HFree6812.infinity_theta v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat hPK
      hcj (max P pσ) hQ
    set θ:=max s (max 0 (max P pσ-2*((P.toNat:ℕ):ℤ))+((P.toNat:ℕ):ℤ)) with hθdef
    have hPn:((P.toNat:ℕ):ℤ)=P:=Int.toNat_of_nonneg hP0
    have hθT:θ≤T:=by
      rw [hθdef,hPn]
      refine max_le (hsP.trans (max_le (by omega) hTσ)) ?_
      rcases le_total P pσ with h1 | h1
      · rw [max_eq_right h1];omega
      · rw [max_eq_left h1];omega
    have hθ0:0≤θ:=le_max_of_le_left hs0
    have hit:=HFree6812.pole_iterate_of_bound v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1:vpole v (sliceCoord F₀ 1)≤P:=by rw [hPeq];exact le_max_left _ _
    have h1:(m:ℤ)*θ≤m*T:=mul_le_mul_of_nonneg_left hθT (Nat.cast_nonneg m)
    have h3:0≤(m:ℤ)*T:=mul_nonneg (Nat.cast_nonneg m) (by omega)
    have h4:0≤(m:ℤ)*h:=mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith
end Slice
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
section Slice
variable {K:Type} [Field K] (F F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]
  (hdvd:F₀ ∣ F)
set_option linter.unusedSectionVars false
variable (v:Valuation (SliceField F₀) ℤᵐ⁰)
theorem GIA (d:Fin 3) (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm: ∃x,v x=exp (-1))
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1)
    (ℓ:SliceField F₀)
    (hℓ:v (HFree6812.sliceDerivation F F₀ hdvd ℓ)≤max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (hdir:vpole v (HFree6812.sliceDerivation F F₀ hdvd ℓ)≤
      dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)))
    (C:ℤ) (hcrude:CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)
    (hsep:HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
      (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd ℓ))))
    (h2:(2:K) ≠ 0)
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0)
    (hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b)
    (m:ℕ):
    3*vpole v ((⇑(HFree6812.sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1))+
        m*capPole d (placeP F₀ v) (placeYZ F₀ v)≤
      m*(4*placeT F F₀ v+2*placeH F F₀ v)+3*placeP F₀ v:=by
  classical
  haveI:v.IsTrivialOn K:=⟨hK⟩
  set Dd:=HFree6812.sliceDerivation F F₀ hdvd with hDd
  set P:=placeP F₀ v with hPdef
  set T:=placeT F F₀ v with hTdef
  set h:=placeH F F₀ v with hhdef
  set pσ:=vpole v (sliceSigma F F₀) with hpσdef
  set s:=vpole v (Dd ℓ) with hsdef
  set t:=placeYZ F₀ v with htdef
  set p0:=vpole v (sliceCoord F₀ 0)
  set p1:=vpole v (sliceCoord F₀ 1)
  set p2:=vpole v (sliceCoord F₀ 2)
  have hp0:0≤p0:=vpole_nonneg _ _
  have hp1:0≤p1:=vpole_nonneg _ _
  have hp2:0≤p2:=vpole_nonneg _ _
  have hPeq:P=max p1 (max p0 p2):=rfl
  have hteq:t=max p0 p2:=rfl
  have hTeq:T=max (2*P) (max p0 p2+pσ):=rfl
  have ht0:0≤t:=le_max_of_le_left hp0
  have htP:t≤P:=le_max_right _ _
  have hh0:0≤h:=vzero_nonneg _ _
  have hs0:0≤s:=vpole_nonneg _ _
  have hTP:2*P≤T:=le_max_left _ _
  have hTσ:t+pσ≤T:=le_max_right _ _
  have hold:=place_bound_p19 F F₀ hdvd v hH hnorm hK hX0 ℓ hℓ C hcrude hsep h2 hchar hgen m
  rcases eq_or_lt_of_le (le_max_of_le_left hp1:0≤P) with hPz | hPpos
  ·
    have hcap:capPole d P t=0:=by
      have hPz' :P=0:=hPz.symm
      have htz:t=0:=by omega
      rw [capPole,htz,hPz'];ring
    rw [hcap,mul_zero,add_zero]
    exact hold
  ·
    have hPpos:0<P:=hPpos
    obtain ⟨π₀,hπ₀⟩:=hnorm
    obtain ⟨j,hj⟩: ∃j:Fin 3,vpole v (sliceCoord F₀ j)=P:=by
      rcases max_choice p1 (max p0 p2) with h1 | h1
      · exact ⟨1,by rw [hPeq,h1]⟩
      · rcases max_choice p0 p2 with h2 | h2
        · exact ⟨0,by rw [hPeq,h1,h2]⟩
        · exact ⟨2,by rw [hPeq,h1,h2]⟩
    have hcj0:v (sliceCoord F₀ j) ≠ 0:=by
      intro h0
      have:vpole v (sliceCoord F₀ j)=0:=by simp [vpole,h0]
      omega
    have hcj:v (sliceCoord F₀ j)=exp ((P.toNat:ℕ):ℤ):=by
      rw [← exp_log hcj0]
      congr 1
      have:vpole v (sliceCoord F₀ j)=max 0 (v (sliceCoord F₀ j)).log:=rfl
      omega
    have hPK:((P.toNat:ℕ):K) ≠ 0:=
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hPpos.le];exact le_max_left _ _)
    have hQ:v (Dd (sliceCoord F₀ j))≤exp (max P pσ):=by
      fin_cases j
      · show v (Dd (sliceCoord F₀ 0))≤_
        rw [hDd,HFree6812.sliceDerivation_coord0 F F₀ hdvd hH]
        exact (HFree6812.v_le_exp_vpole v _).trans (by
          rw [exp_le_exp];have:=le_max_left p1 (max p0 p2);exact le_max_of_le_left (by omega))
      · show v (Dd (sliceCoord F₀ 1))≤_
        rw [hDd,HFree6812.sliceDerivation_coord1 F F₀ hdvd hH]
        exact (HFree6812.v_le_exp_vpole v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
      · show v (Dd (sliceCoord F₀ 2))≤_
        rw [hDd,HFree6812.sliceDerivation_coord2 F F₀ hdvd hH,v.map_zero];exact zero_le
    have hθ:=HFree6812.infinity_theta_signed v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat
      hPK hcj (max P pσ) hQ
    have hPn:((P.toNat:ℕ):ℤ)=P:=Int.toNat_of_nonneg hPpos.le
    rw [hPn] at hθ
    set θ:=max s (max P pσ-P) with hθdef
    have hθ0:0≤θ:=le_max_of_le_left hs0

    have hlaw:3*θ+capPole d P t≤4*T:=by
      rw [hθdef]
      fin_cases d<;>simp only [capPole,infCap,dirS] at hdir ⊢ <;>simp at hdir ⊢ <;>omega
    have hit:=HFree6812.pole_iterate_of_bound v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1:vpole v (sliceCoord F₀ 1)≤P:=by rw [hPeq];exact le_max_left _ _
    have h1:(m:ℤ)*(3*θ+capPole d P t)≤m*(4*T):=
      mul_le_mul_of_nonneg_left hlaw (Nat.cast_nonneg m)
    have h4:0≤(m:ℤ)*h:=mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith
end Slice
section Budget
variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local notation "w" =>RCN326.w
omit [IsAlgClosed E] in
theorem GCV (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (H G:MvPolynomial (Fin 3) E) (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D)) (d:Fin 3):
    flagPole ν.val (coordinate E D) (infCap d)≤4*RCN064.KS D H G ν:=by
  have hT:=le_max_left (2*max (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2))))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2))+
      RCN187.poleOrder ν.val (RCN064.movingRatio D H G))
  have ht:=le_max_right (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2)))
  have ht0:0≤max (RCN187.poleOrder ν.val (coordinate E D 0))
      (RCN187.poleOrder ν.val (coordinate E D 2)):=
    le_max_of_le_left (le_max_left _ _)
  unfold RCN064.KS
  fin_cases d<;>simp only [flagPole,infCap]<;>simp<;>omega
theorem FNW (d:Fin 3) (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
    (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
    (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K) (hqd:DirShape d q)
    (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (h2:(2:K) ≠ 0)
    (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D))
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
      (RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
        (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))→(n:K) ≠ 0)
    (hdefer: ∀(e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (HFree6812.sliceEmbedding D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)∧
      HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
        (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd (sliceLinearL F₀ q))))):
    3*RCN187.poleOrder ν.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1))+
      ((w+1:ℕ):ℤ)*flagPole ν.val (coordinate E D) (infCap d)≤
    ((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν+
        2*RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))+
      3*flagPole ν.val (coordinate E D) unitAllFlag:=by
  classical
  set ψ:=HFree6812.sliceEmbedding D F₀ hker with hψdef
  set Dd:=HFree6812.sliceDerivation F F₀ hdvd with hDd
  set wv:Valuation (SliceField F₀) ℤᵐ⁰:=ν.val.comap ψ with hwvdef
  have hwv: ∀x,wv x=ν.val (ψ x):=fun _=>rfl
  have hHψ:ψ (sliceProj F₀ (polyH K F)) ≠ 0:=by
    rw [hψdef,HFree6812.sliceEmbedding_proj]
    intro h
    exact hHD ((HFree6812.coordEval_eq_zero_iff D _).1 h)
  have hH:sliceProj F₀ (polyH K F) ≠ 0:=fun h=>hHψ (by rw [h,map_zero])
  have hτ:SecondJetComponentRoots.coefficientMap (phiE K E) D (RCN055.baseNumerator F (w-1))/
      SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1)=
      ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)):=by
    have h:=HFree6812.sliceDerivation_iterate F F₀ hdvd hH (w-1)
    have hw1:w-1+1=w:=rfl
    have hw2:2*(w-1)+1=2*w-1:=rfl
    rw [hw1,hw2] at h
    rw [show sliceCoord F₀ 1=sliceProj F₀ (MvPolynomial.X 2) from rfl,h,map_div₀,map_pow,
      hψdef,HFree6812.sliceEmbedding_proj,HFree6812.sliceEmbedding_proj]
    rfl
  rw [hτ]
  have hcap4:=GCV D (surfaceMap (phiE K E) (polyH K F))
    (surfaceMap (phiE K E) (polyG K F)) ν d
  have hRHS0:((w+1:ℕ):ℤ)*flagPole ν.val (coordinate E D) (infCap d)≤
      ((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν+
        2*RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))+
      3*flagPole ν.val (coordinate E D) unitAllFlag:=by
    have h2:=RCN026.AUU E (RCN002.CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))
    have h3:=RCN204.flagPole_nonneg ν.val (coordinate E D) unitAllFlag
    have hw:(0:ℤ)≤((w+1:ℕ):ℤ):=by positivity
    have h4:=mul_le_mul_of_nonneg_left hcap4 hw
    have h5:=mul_nonneg hw (mul_nonneg (show (0:ℤ)≤2 by norm_num) h2)
    rw [mul_add]
    linarith
  by_cases hnt: ∃x,wv x ≠ 0∧wv x ≠ 1
  swap
  · have hpole:RCN187.poleOrder ν.val (ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)))=0:=by
      set x:=(⇑Dd)^[w] (sliceCoord F₀ 1)
      have hx:wv x=0∨wv x=1:=by
        by_contra h;rw [not_or] at h;exact hnt ⟨x,h.1,h.2⟩
      show max 0 (ν.val (ψ x)).log=0
      rw [← hwv]
      rcases hx with h | h<;>simp [h]
    rw [hpole,mul_zero,zero_add]
    exact hRHS0
  obtain ⟨e,v,he,hvn,hwve⟩:=HFree6812.exists_normalization wv hnt
  have he0:e ≠ 0:=by omega
  have hν: ∀x,ν.val (ψ x)=v x^e:=fun x=>hwve x
  have hpole: ∀x,RCN187.poleOrder ν.val (ψ x)=e*vpole v x:=
    fun x=>HFree6812.poleOrder_pow v wv e hwve x
  have hzeroν: ∀x,RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν (ψ x)=e*vzero v x:=
    fun x=>HFree6812.zeroOrder_pow v wv e hwve x
  have hνE: ∀a:E,a ≠ 0→ν.val (algebraMap E (RCN002.CoordinateField E D) a)=1:=
    fun a ha=>(ν.property.2).eq_one a ha
  have hφinj:Function.Injective (phiE K E):=
    (algebraMap (GenericField K) E).injective.comp (RCN135.polynomialEmbedding_injective K)
  have hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1:=by
    intro a ha
    have h1:ν.val (ψ (algebraMap K _ a))=1:=by
      rw [hψdef,psi_const]
      exact hνE _ (fun h=>ha (Polynomial.C_eq_zero.mp (hφinj (h.trans (map_zero _).symm))))
    rw [hν] at h1
    exact le_antisymm ((HFree6812.zm_pow_le_one he0).1 h1.le)
      (not_lt.1 fun hlt=>absurd h1 (ne_of_lt ((HFree6812.zm_pow_lt_one he0).2 hlt)))
  have hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1:=by
    have h1:ν.val (ψ (sliceProj F₀ (MvPolynomial.X 0)))≤1:=by
      rw [hψdef,psi_X0]
      haveI:=ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    rw [hν] at h1
    exact (HFree6812.zm_pow_le_one he0).1 h1
  obtain ⟨⟨C,hcrude⟩,hsep⟩:=hdefer e v he hvn hwve
  have hℓ:=HFree6812.sliceLinearL_bound F F₀ hdvd v hH hK hX0 q
  have hdir:=HFree6812.sliceLinearL_dir F F₀ hdvd v hH hK hX0 d q hqd

  have hcoordν: ∀j,RCN187.poleOrder ν.val (coordinate E D j)=
      e*vpole v (sliceCoord F₀ j):=by
    intro j;rw [← psi_coord D F₀ hker j,← hψdef,hpole]
  have hPν:flagPole ν.val (coordinate E D) unitAllFlag=e*placeP F₀ v:=by
    simp only [flagPole,unitAllFlag,Nat.cast_zero,zero_mul,Nat.cast_one,one_mul,zero_add]
    rw [hcoordν,hcoordν,hcoordν,placeP,scale_flag (e:ℤ) (by positivity)]
  have hcapν:flagPole ν.val (coordinate E D) (infCap d)=
      e*capPole d (placeP F₀ v) (placeYZ F₀ v):=by
    simp only [flagPole,infCap_zOnly,Nat.cast_zero,zero_mul,zero_add]
    rw [hcoordν,hcoordν,hcoordν,capPole,placeP,placeYZ,scale_flag (e:ℤ) (by positivity),
      ← mul_max_of_nonneg _ _ (by positivity:(0:ℤ)≤e)]
    ring
  have hhν:RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))=
        e*placeH F F₀ v:=by
    have:SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)=
        ψ (sliceProj F₀ (polyH K F)):=by rw [hψdef,HFree6812.sliceEmbedding_proj];rfl
    rw [this,hzeroν]
    rfl
  have hTν:RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
      (surfaceMap (phiE K E) (polyG K F)) ν=e*placeT F F₀ v:=by
    unfold RCN064.KS
    rw [hcoordν,hcoordν,hcoordν,← psi_sigma D F₀ hker F,← hψdef,hpole,placeT,placeP,
      scale_target (e:ℤ) (by positivity)]
  have hPv0:0≤placeP F₀ v:=le_max_of_le_left (vpole_nonneg _ _)
  have hhv0:0≤placeH F F₀ v:=vzero_nonneg _ _
  have hcharv: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0:=by
    intro n hn hle
    refine hchar n hn ?_
    rw [hPν,hhν]
    have h1:placeP F₀ v≤e*placeP F₀ v:=le_mul_of_one_le_left hPv0 (by exact_mod_cast he)
    have h2:placeH F F₀ v≤e*placeH F F₀ v:=le_mul_of_one_le_left hhv0 (by exact_mod_cast he)
    exact hle.trans (max_le_max h1 h2)
  have hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b:=by
    intro hP0
    have hint:=place_hint F₀ v hK hX0 hP0
    set 𝔓:=valCentre (sliceProj F₀) v hint with h𝔓def
    set y:Fin 3→RCN002.CoordinateField E D:=coordinate E D
    have hev: ∀P:MvPolynomial (Fin 3) (GenericField K),
        aeval y P=RCN002.coordinateEvaluation E D (RCN208.scalarPolynomialMap (GenericField K) E P):=by
      intro P
      rw [RCN002.coordinateEvaluation_eq_aeval,RCN208.scalarPolynomialMap,aeval_map_algebraMap]
    have hνΩ: ∀a:GenericField K,
        ν.val (algebraMap (GenericField K) (RCN002.CoordinateField E D) a)≤1:=by
      intro a
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (RCN002.CoordinateField E D)]
      haveI:=ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    have hyint: ∀j,ν.val (y j)≤1:=by
      intro j
      rw [show y j=ψ (sliceCoord F₀ j) from (psi_coord D F₀ hker j).symm,hν]
      exact pow_le_one' (hint _) e
    let fy:MvPolynomial (Fin 3) (GenericField K)→+*RCN002.CoordinateField E D:=(aeval y).toRingHom
    have hintΩ: ∀P:MvPolynomial (Fin 3) (GenericField K),ν.val (fy P)≤1:=by
      intro P
      change ν.val (aeval y P)≤1
      induction P using MvPolynomial.induction_on with
      | C a=>rw [aeval_C];exact hνΩ a
      | add p r hp hr=>rw [map_add];exact (ν.val.map_add _ _).trans (max_le hp hr)
      | mul_X p j hp=>
        rw [map_mul,ν.val.map_mul,aeval_X];exact mul_le_one' hp (hyint j)
    set 𝔮:=valCentre fy ν.val hintΩ with h𝔮def
    have hP𝔮:RCN219.originalPrime 𝔮=𝔓:=by
      ext g
      rw [RCN219.mem_originalPrime_iff,h𝔮def,h𝔓def,HFree6812.mem_valCentre,HFree6812.mem_valCentre]
      change ν.val (aeval y _)<1 ↔ _
      rw [hev,← HFree6812.surfaceMap_generic_eq]
      change ν.val (sliceMap D g)<1 ↔ _
      rw [← HFree6812.sliceEmbedding_proj D F₀ hker,← hψdef,hν,HFree6812.zm_pow_lt_one he0]
    have hcω: ∀a:GenericField K,a ≠ 0→
        ν.val (algebraMap (GenericField K) (RCN002.CoordinateField E D) a)=1:=by
      intro a ha
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (RCN002.CoordinateField E D)]
      exact hνE _ ((map_ne_zero_iff _ (algebraMap (GenericField K) E).injective).2 ha)
    have hsl: ∑ m,algebraMap (GenericField K) (RCN002.CoordinateField E D) (c m)*y m=
        algebraMap E (RCN002.CoordinateField E D) (sliceValue (GenericField K) E):=by
      have h1:=(HFree6812.coordEval_eq_zero_iff D _).2 hslice
      rw [map_sub,sub_eq_zero,← hev] at h1
      have h2:RCN002.coordinateEvaluation E D (MvPolynomial.C (sliceValue (GenericField K) E))=
          algebraMap E (RCN002.CoordinateField E D) (sliceValue (GenericField K) E):=
        (RCN002.coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum,map_mul,aeval_C,aeval_X]
    have hℓ' : ∀a:Fin 3→GenericField K,
        ν.val (∑ m,algebraMap (GenericField K) (RCN002.CoordinateField E D) (c m)*y m-
          algebraMap (GenericField K) (RCN002.CoordinateField E D) (∑ m,c m*a m))=1:=by
      intro a
      rw [hsl,IsScalarTower.algebraMap_apply (GenericField K) E (RCN002.CoordinateField E D),
        ← map_sub]
      apply hνE
      intro h
      apply HFree6812.sliceValue_transcendental (Ω:=GenericField K) (E:=E)
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap _
    have h𝔮h:𝔮.height≤2:=
      HFree6812.centre_height_le_two ν.val y 𝔮 (fun P=>HFree6812.mem_valCentre _ _ _ P) c hcω hℓ'
    have h𝔓h:𝔓.height≤2:=hP𝔮 ▸ (RCN219.originalPrime_height_le 𝔮).trans h𝔮h
    haveI:=RCN230.mvPolynomial_atPrime_isRegularLocalRing 𝔓
    obtain ⟨a,ha,b,hb,hgen'⟩:=HFree6812.exists_two_local_generators 𝔓 h𝔓h
    refine ⟨a,b,ha,hb,fun g hg=> ?_⟩
    obtain ⟨s,hs,x,y,hsg⟩:=hgen' g hg
    exact ⟨s,x,y,le_antisymm (hint s) (not_lt.1 hs),hsg⟩
  have hmain:=GIA F F₀ hdvd v d hH hvn hK hX0 (sliceLinearL F₀ q) hℓ hdir C hcrude
    hsep h2 hcharv hgen w
  rw [hpole,hTν,hhν,hPν,hcapν]
  rw [hcapν,hTν] at hcap4
  have hk:=mul_le_mul_of_nonneg_left hmain (show (0:ℤ)≤e by positivity)
  have heh:0≤(e:ℤ)*placeH F F₀ v:=mul_nonneg (by positivity) hhv0
  push_cast at hk ⊢
  linarith
theorem DOC (d:Fin 3) (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (sep:RCN341.SeparableLiteralCoordinate D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hqd:DirShape d q) (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (h2:(2:K) ≠ 0)
    (hchar: ∀ν:RCN026.Place_p19 E (RCN002.CoordinateField E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))→(n:K) ≠ 0)
    (hdefer: ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (HFree6812.sliceEmbedding D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)∧
      HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
        (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))))
    (W:Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D))):
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) nu+
        2*RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) nu
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))-
        flagPole nu.val (coordinate E D) (infCap d))+
      3*flagPole nu.val (coordinate E D) unitAllFlag):=by
  have hF:F ≠ 0:=by
    rintro rfl
    apply hHD
    simp [polyH]
  obtain ⟨F₀,hirr,hdvd,hker⟩:=FVZ D sep F hF hFD c i hci hslice
  haveI:Fact (Irreducible F₀):=⟨hirr⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _=> ?_
  have h:=FNW d F D F₀ hdvd hker hHD c q hqd hq hslice h2 ν (hchar ν)
    (hdefer F₀ hdvd hker ν)
  linarith
end Budget
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN005 RCN006 RCN095 RCN135 RCN136 RCN202 RCN204 RCN208 RCN313 RCN341
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
section SliceForm
variable {Ω E:Type} [Field Ω] [Field E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
theorem CQT {a:MvPolynomial (Fin 3) E} (ha:a ≠ 0)
    (h:a.totalDegree=0):IsUnit a:=by
  rw [totalDegree_eq_zero_iff_eq_C] at h
  rw [h] at ha ⊢
  exact (isUnit_iff_ne_zero.mpr fun h0=>ha (by rw [h0,map_zero])).map C
theorem FBG (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1):
    Irreducible (sliceForm (E:=E) c):=by
  have hd:=HFree6812.sliceForm_totalDegree (E:=E) c i hci
  have hne:sliceForm (E:=E) c ≠ 0:=fun h=>by rw [h] at hd;simp at hd
  refine ⟨fun hu=> ?_,fun a b hab=> ?_⟩
  · obtain ⟨q,hq⟩:=hu.exists_right_inv
    have h1:=congrArg totalDegree hq
    rw [totalDegree_mul_of_isDomain hne (right_ne_zero_of_mul_eq_one hq),totalDegree_one,
      hd] at h1
    omega
  · have ha:a ≠ 0:=by rintro rfl;exact hne (by rw [hab,zero_mul])
    have hb:b ≠ 0:=by rintro rfl;exact hne (by rw [hab,mul_zero])
    have h1:=congrArg totalDegree hab
    rw [totalDegree_mul_of_isDomain ha hb,hd] at h1
    rcases Nat.eq_zero_or_pos a.totalDegree with h | h
    · exact Or.inl (CQT ha h)
    · exact Or.inr (CQT hb (by omega))
end SliceForm
section Gate
variable {E:Type} [Field E]
theorem GFP (P:Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime] (j:Fin 3)
    (hj:Transcendental E (coordinate E P j)) (p:ℕ) [CharP E p]
    (G H:MvPolynomial (Fin 3) E) (hG:Irreducible G) (hGP:G ∈ P) (hHP:H ∈ P)
    (hGH: ¬G ∣ H) (hdeg: ∀k,G.degreeOf k<p)
    (hmix:RCN001.coordinateMixedDegree E G H j<p):
    letI:=RCN005.rationalBaseAlgebra E P j hj
    FiniteDimensional (RatFunc E) (RCN002.CoordinateField E P)∧
      Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E P)∧
      Module.finrank (RatFunc E) (RCN002.CoordinateField E P)≤
        RCN001.coordinateMixedDegree E G H j:=by
  have key: ∀k (hk:Transcendental E (coordinate E P k)),k=j→
      (letI:=RCN005.rationalBaseAlgebra E P k hk
       FiniteDimensional (RatFunc E) (RCN002.CoordinateField E P)∧
        Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E P)∧
        Module.finrank (RatFunc E) (RCN002.CoordinateField E P)≤
        RCN001.coordinateMixedDegree E G H j)→
      (letI:=RCN005.rationalBaseAlgebra E P j hj
       FiniteDimensional (RatFunc E) (RCN002.CoordinateField E P)∧
        Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E P)∧
        Module.finrank (RatFunc E) (RCN002.CoordinateField E P)≤
        RCN001.coordinateMixedDegree E G H j):=by
    rintro k hk rfl h;exact h
  have hj' :Transcendental E (coordinate E P ((Equiv.swap 0 j) 0)):=by
    rwa [Equiv.swap_apply_left]
  exact key _ hj' (Equiv.swap_apply_left 0 j)
    (RCN004.AGY E (Equiv.swap 0 j) P hj' p G H hG hGP hHP hGH
      (hdeg _) (hdeg _) hmix)
end Gate
section Char
variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
theorem hchar_holds_p19 [CharP K 2130706433] (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep:RCN341.SeparableLiteralCoordinate D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N) (hN9:N≤9678):
    ∀ν:RCN026.Place_p19 E (RCN002.CoordinateField E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))→(n:K) ≠ 0:=by
  classical
  haveI:CharP E 2130706433:=
    charP_of_injective_algebraMap (algebraMap (GenericField K) E).injective 2130706433
  set L:=RCN002.CoordinateField E D
  set y:=coordinate E D
  set Fp:=surfaceMap (phiE K E) F with hFp
  have hF:F ≠ 0:=by rintro rfl;apply hHD;simp [polyH]
  have hFflag:RCN095.PolynomialInFlag ⟨0,0,N⟩ Fp:=inFlag_total _ F N hN
  have hHflag:RCN095.PolynomialInFlag ⟨0,0,N⟩ (surfaceMap (phiE K E) (polyH K F)):=
    inFlag_total _ _ N ((RCN234.wt_polyH_le _ F N hN).trans (Nat.sub_le _ _))
  have hirr:=FBG (E:=E) c i hci
  have hdvd: ¬sliceForm (E:=E) c ∣ Fp:=by
    rw [hFp,HFree6812.surfaceMap_generic_eq]
    exact HFree6812.sliceForm_not_dvd c i hci _ (RCN136.surfaceMap_ne_zero _ (RCN135.polynomialEmbedding_injective K) F hF)
  have hdeg1: ∀k,(sliceForm (E:=E) c).degreeOf k≤1:=fun k=>
    (degreeOf_le_totalDegree _ k).trans (HFree6812.sliceForm_totalDegree c i hci).le
  have hdegF: ∀k,Fp.degreeOf k≤N:=fun k=>by
    simpa using RCN084.degreeOf_le_flag_total Fp _ hFflag k

  have hpole: ∀j (W:Finset (RCN026.Place_p19 E L)),
      (∑ ν ∈ W,RCN187.poleOrder ν.val (y j))≤2*N:=by
    intro j W
    have hmix:RCN001.coordinateMixedDegree E (sliceForm c) Fp j≤2*N:=
      (Nat.add_le_add (Nat.mul_le_mul (hdegF _) (hdeg1 _))
        (Nat.mul_le_mul (hdeg1 _) (hdegF _))).trans (by omega)
    have gate:=fun hx:Transcendental E (y j)=>GFP D j hx 2130706433 _ _ hirr
      hslice hFD hdvd (fun k=>by have:=hdeg1 k;omega) (by omega)
    have h:=RCN344.PY E L
      (RCN042.coordinateOfGate (y j) (fun hx=>⟨(gate hx).1,(gate hx).2.1⟩)) W
    rw [RCN042.coordinateOfGate_value] at h
    refine h.trans ?_
    by_cases hx:Transcendental E (y j)
    · rw [RCN042.coordinateOfGate_degree_of_transcendental _ _ hx]
      exact_mod_cast (gate hx).2.2.trans hmix
    · rw [RCN042.coordinateOfGate_degree_of_isAlgebraic _ _ (not_not.mp hx)]
      positivity
  have hp (j) (ν:RCN026.Place_p19 E L):RCN187.poleOrder ν.val (y j)≤2*N:=by
    simpa using hpole j {ν}

  set Hev:=SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)
  have hHne:Hev ≠ 0:=fun h=>hHD ((SecondJetComponentRoots.evaluation_zero_iff D _).mp h)
  letI:=RCN006.polynomialBaseAlgebra E D sep.index
  letI:=RCN005.rationalBaseAlgebra E D sep.index sep.transcendental
  letI:=RCN006.polynomialBaseScalarTower E D sep.index
  letI:=RCN006.polynomialRationalScalarTower E D sep.index sep.transcendental
  letI:=RCN005.rationalBaseScalarTower E D sep.index sep.transcendental
  letI:FiniteDimensional (RatFunc E) L:=sep.finite
  letI:Algebra.IsSeparable (RatFunc E) L:=sep.separable
  set Pl:=RCN026.placesFor_p19 E L Hev hHne
  have hpoleH (μ:RCN026.Place_p19 E L):RCN346.poleOrder_p19 E L μ Hev≤
      N*(RCN187.poleOrder μ.val (y 0)+RCN187.poleOrder μ.val (y 1)+
        RCN187.poleOrder μ.val (y 2)):=by
    have h0:0≤RCN187.poleOrder μ.val (y 0):=le_max_left _ _
    have h1:0≤RCN187.poleOrder μ.val (y 1):=le_max_left _ _
    have h2:0≤RCN187.poleOrder μ.val (y 2):=le_max_left _ _
    have hle:flagPole μ.val y ⟨0,0,N⟩≤N*(RCN187.poleOrder μ.val (y 0)+
        RCN187.poleOrder μ.val (y 1)+RCN187.poleOrder μ.val (y 2)):=by
      simp only [flagPole,Nat.cast_zero,zero_mul,zero_add]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) (max_le (by linarith) (by linarith)))
        (by positivity)
    refine le_trans ?_ hle
    apply ActualFirstCutPole6807.pole_le_of_value_le μ.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h:=RCN204.valuation_eval_le_flag μ.val (algebraMap E L)
      (RCN344.NP E L μ) y ⟨0,0,N⟩ _ hHflag
    simpa only [Hev,SecondJetComponentRoots.coefficientMap,
      RCN002.coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h
  have hzero (ν:RCN026.Place_p19 E L):RCN026.zeroOrder_p19 E L ν Hev≤N*(6*N):=by
    have hsum:RCN026.zeroOrder_p19 E L ν Hev≤ ∑ μ ∈ Pl,RCN026.zeroOrder_p19 E L μ Hev:=by
      by_cases hν:ν ∈ Pl
      · exact Finset.single_le_sum (fun μ _=>RCN026.AUU E L μ Hev) hν
      · have hno:RCN026.order_p19 E L ν Hev=0:=by
          by_contra hne;exact hν (RCN026.ALB E L Hev hHne ν hne)
        simp only [RCN026.zeroOrder_p19,hno,max_self]
        exact Finset.sum_nonneg fun μ _=>RCN026.AUU E L μ Hev
    rw [RCN026.AJO] at hsum
    refine hsum.trans ((Finset.sum_le_sum fun μ _=>hpoleH μ).trans ?_)
    rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (by linarith [hpole 0 Pl,hpole 1 Pl,hpole 2 Pl])
      (by positivity)
  intro ν n hn hle
  have hf:flagPole ν.val y unitAllFlag≤2*N:=by
    rw [RCN204.flagPole_unitAll]
    exact max_le (hp 1 ν) (max_le (hp 0 ν) (hp 2 ν))
  have hN9' :(N:ℤ)≤9678:=by exact_mod_cast hN9
  have hlt:(n:ℤ)<2130706433:=by
    have h1:=le_max_iff.mp hle
    rcases h1 with h1 | h1
    · linarith
    · have:=hzero ν;nlinarith
  intro h
  exact absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)
end Char
end
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero Polynomial
section Basic
variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)
theorem ASC {R:Type*} [CommRing R] [Algebra R L]
    (hR: ∀r:R,v (algebraMap R L r)≤1) {x:L} (hx:IsIntegral R x):v x≤1:=by
  obtain ⟨f,hf,hfx⟩:=hx
  by_contra h
  rw [not_le] at h
  have hx0:v x ≠ 0:=(lt_trans zero_lt_one h).ne'
  rw [hf.as_sum,eval₂_add,eval₂_X_pow,eval₂_finsetSum] at hfx
  have hlt:v (∑ i ∈ Finset.range f.natDegree,
      eval₂ (algebraMap R L) x (C (f.coeff i)*Polynomial.X^i))<v (x^f.natDegree):=by
    refine v.map_sum_lt (by rw [v.map_pow];exact pow_ne_zero _ hx0) fun i hi=> ?_
    rw [eval₂_mul,eval₂_C,eval₂_X_pow,v.map_mul,v.map_pow,v.map_pow]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hR _)) ?_
    exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have:=v.map_add_eq_of_lt_left hlt
  rw [hfx,v.map_zero,v.map_pow] at this
  exact pow_ne_zero _ hx0 this.symm
end Basic
section Dedekind
variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)
variable (A K' :Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]
include K' in
theorem FQL (hA: ∀a:A,v (algebraMap A L a)≤1) (hπ: ∃x,v x=exp (-1))
    (z:L) (hz:v z≤1):
    ∃r u:L,IsIntegral A r∧IsIntegral A u∧v u=1∧z=r/u:=by
  classical
  set C:=integralClosure A L
  haveI:IsDedekindDomain C:=integralClosure.isDedekindDomain A K' L
  haveI:IsFractionRing C L:=IsIntegralClosure.isFractionRing_of_finite_extension A K' L C
  have hCv: ∀c:C,v (c:L)≤1:=fun c=>ASC v hA c.2
  let ρ:C→+*v.valuationSubring:=
    (algebraMap C L).codRestrict v.valuationSubring fun c=>(Valuation.mem_valuationSubring_iff _ _).2 (hCv c)
  set 𝔓:Ideal C:=(IsLocalRing.maximalIdeal v.valuationSubring).comap ρ
  have hmem: ∀c:C,c ∈ 𝔓 ↔ v (c:L)<1:=by
    intro c
    rw [Ideal.mem_comap,← IsLocalRing.residue_eq_zero_iff,← HFree6812.residue_eq_zero_iff_lt_one v _ (hCv c),
      HFree6812.residue_of_le v _ (hCv c)]
    rfl
  have hunit: ∀c:C,c ∉ 𝔓→v (c:L)=1:=fun c hc=>
    le_antisymm (hCv c) (not_lt.1 fun h=>hc ((hmem c).2 h))
  have h𝔓:𝔓 ≠ ⊥ :=by
    obtain ⟨π,hπ⟩:=hπ
    obtain ⟨y,hy0,hy⟩:=exists_integral_multiples A K' ({π}:Finset L)
    have hint:=hy π (Finset.mem_singleton_self π)
    have hinj:Function.Injective (algebraMap A L):=by
      rw [IsScalarTower.algebraMap_eq A K' L]
      exact (algebraMap K' L).injective.comp (IsFractionRing.injective A K')
    have hπ0:π ≠ 0:=by rintro rfl;rw [v.map_zero] at hπ;exact exp_ne_zero hπ.symm
    intro hbot
    have hmem' :(⟨y • π,hint⟩:C) ∈ 𝔓:=by
      rw [hmem]
      change v (y • π)<1
      rw [Algebra.smul_def,v.map_mul,hπ]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' (hA y)) ?_
      rw [← exp_zero,exp_lt_exp];omega
    rw [hbot,Ideal.mem_bot] at hmem'
    have h0:=congrArg (fun c:C=>(c:L)) hmem'
    simp only [ZeroMemClass.coe_zero] at h0
    change y • π=0 at h0
    rw [Algebra.smul_def] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hy0 (hinj (h.trans (map_zero _).symm))
    · exact hπ0 h
  haveI:𝔓.IsPrime:=Ideal.comap_isPrime _ _
  set Bp:=Localization.subalgebra.ofField L 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors
  haveI:IsDiscreteValuationRing Bp:=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C h𝔓 Bp
  have hBp: ∀y:Bp,∃a s:C,s ∉ 𝔓∧(y:L)=(a:L)/(s:L):=by
    intro y
    obtain ⟨a,s,hs,hy⟩:=y.2
    exact ⟨a,s,hs,by rw [hy,div_eq_mul_inv];rfl⟩
  rcases ValuationRing.isInteger_or_isInteger Bp z with ⟨y,hy⟩ | ⟨y,hy⟩
  · obtain ⟨a,s,hs,hys⟩:=hBp y
    refine ⟨a,s,a.2,s.2,hunit s hs,?_⟩
    rw [← hy,← hys];rfl
  · obtain ⟨a,s,hs,hys⟩:=hBp y
    have hyz:z⁻¹=(a:L)/(s:L):=by rw [← hy,← hys];rfl
    by_cases hz0:z=0
    · exact ⟨0,1,isIntegral_zero,isIntegral_one,v.map_one,by rw [hz0,zero_div]⟩
    by_cases ha:a ∈ 𝔓
    · exfalso
      have h1:v z⁻¹<1:=by
        rw [hyz,map_div₀,hunit s hs,div_one];exact (hmem a).1 ha
      rw [map_inv₀] at h1
      have hz1:v z ≠ 0:=(Valuation.ne_zero_iff v).2 hz0
      have:1<v z:=by
        by_contra hle;rw [not_lt] at hle
        exact absurd h1 (not_lt.2 (one_le_inv₀ (zero_lt_iff.2 hz1) |>.2 hle))
      exact absurd hz (not_le.2 this)
    · have ha0:(a:L) ≠ 0:=by
        intro h;have:=hunit a ha;rw [h,v.map_zero] at this;exact zero_ne_one this
      refine ⟨s,a,s.2,a.2,hunit a ha,?_⟩
      rw [← inv_inv z,hyz,inv_div]
end Dedekind
section Tame
variable {K L:Type*} [Field K] [Field L] [Algebra K L] (v:Valuation L ℤᵐ⁰)
  (D:Derivation K L L)
variable (A K' :Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]
include K' in
theorem GXV (Λ0:ℤ) (hA: ∀a:A,Tame v D (exp Λ0) (algebraMap A L a)):
    ∃C:ℤ,∀r:L,IsIntegral A r→Tame v D (exp C) r:=by
  classical
  set B:=integralClosure A L
  haveI:Module.Finite A B:=IsIntegralClosure.finite A K' L B
  obtain ⟨G,hG⟩:=Module.Finite.fg_top (R:=A) (M:=B)
  set n:ℤ:= ∑ g ∈ G,max 0 (v (D (g:L))).log
  refine ⟨max Λ0 n,fun r hr=> ?_⟩
  have hgen: ∀g ∈ G,Tame v D (exp (max Λ0 n)) (g:L):=by
    intro g hg
    refine ⟨ASC v (fun a=>(hA a).1) g.2,(HFree6812.v_le_exp_max_log v _).trans ?_⟩
    rw [exp_le_exp]
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f:=fun g:B=>max 0 (v (D (g:L))).log)
      (fun _ _=>le_max_left _ _) hg
  have key: ∀c:B,c ∈ Submodule.span A (G:Set B)→Tame v D (exp (max Λ0 n)) (c:L):=by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx=>exact hgen x hx
    | zero=>exact (tameSubring v D _).zero_mem
    | add x y _ _ hx hy=>exact (tameSubring v D _).add_mem hx hy
    | smul a x _ hx=>
      change Tame v D _ (a • (x:L))
      rw [Algebra.smul_def]
      exact (tameSubring v D _).mul_mem
        ((hA a).mono v D (by rw [exp_le_exp];exact le_max_left _ _)) hx
  exact key ⟨r,hr⟩ (by rw [hG];exact Submodule.mem_top)
omit [Field K] [Algebra K L] [Algebra.IsSeparable K' L] in
include K' in
theorem FIC (hA: ∀a:A,v (algebraMap A L a)≤1)
    (F' :Subfield (IsLocalRing.ResidueField v.valuationSubring))
    (hF' : ∀a:A,residue v (algebraMap A L a) ∈ F') (N:ℕ) (hN:Module.finrank K' L≤N)
    (hNF: ∀n:ℕ,0<n→n≤N→(n:IsLocalRing.ResidueField v.valuationSubring) ≠ 0)
    (r:L) (hr:IsIntegral A r):
    IsSeparable F' (residue v r):=by
  classical
  have hr1:v r≤1:=ASC v hA hr
  let ρA:A→+*v.valuationSubring:=(algebraMap A L).codRestrict v.valuationSubring fun a=>
    (Valuation.mem_valuationSubring_iff _ _).2 (hA a)
  let ψ0:A→+*IsLocalRing.ResidueField v.valuationSubring:=
    (IsLocalRing.residue v.valuationSubring).comp ρA
  have hψ0: ∀a,ψ0 a=residue v (algebraMap A L a):=fun a=>(HFree6812.residue_of_le v _ (hA a)).symm
  let φ:A→+*F' :=ψ0.codRestrict F' fun a=>by rw [hψ0];exact hF' a
  set f:=minpoly A r
  have hfm:f.Monic:=minpoly.monic hr
  have hfdeg:f.natDegree≤N:=by
    have h1:=minpoly.isIntegrallyClosed_eq_field_fractions' K' hr
    have h2:(minpoly K' r).natDegree≤Module.finrank K' L:=minpoly.natDegree_le r
    rw [h1,hfm.natDegree_map] at h2
    exact h2.trans hN
  set g:=f.map φ
  have hgm:g.Monic:=hfm.map φ
  have hg0:aeval (residue v r) g=0:=by
    have hcomp:(algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)).comp φ=ψ0:=by
      ext a;rfl
    rw [aeval_def,eval₂_map,hcomp,HFree6812.residue_of_le v r hr1]
    change eval₂ ((IsLocalRing.residue v.valuationSubring).comp ρA)
      (IsLocalRing.residue v.valuationSubring ⟨r,hr1⟩) f=0
    rw [← hom_eval₂]
    have h0:eval₂ ρA ⟨r,(Valuation.mem_valuationSubring_iff _ _).2 hr1⟩ f=0:=by
      apply Subtype.ext
      have:=hom_eval₂ f ρA v.valuationSubring.subtype
        ⟨r,(Valuation.mem_valuationSubring_iff _ _).2 hr1⟩
      refine this.trans ?_
      exact minpoly.aeval A r
    rw [h0,map_zero]
  have hint:IsIntegral F' (residue v r):=⟨g,hgm,hg0⟩
  have hdvd:=minpoly.dvd F' (residue v r) hg0
  have hdeg:(minpoly F' (residue v r)).natDegree≤N:=
    (natDegree_le_of_dvd hdvd hgm.ne_zero).trans (by rw [hfm.natDegree_map];exact hfdeg)
  refine HFree6812.separable_of_natDegree_ne_zero (minpoly.irreducible hint) ?_
  intro h0
  apply hNF _ (minpoly.natDegree_pos hint) hdeg
  have:=congrArg (algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)) h0
  simpa using this
end Tame
section Engine
variable {K L:Type*} [Field K] [Field L] [Algebra K L] (v:Valuation L ℤᵐ⁰)
  (D:Derivation K L L)
theorem engine_p19 (k:IntermediateField K L) (hkv: ∀a ∈ k,a ≠ 0→v a=1) (Λ0:ℤ)
    (hkD: ∀a ∈ k,v (D a)≤exp Λ0) (s:L) (hs1:v s≤1) (hst:Transcendental k s)
    (b:L) (hgen: ∀E:Subfield L,(∀x ∈ k,x ∈ E)→s ∈ E→b ∈ E→ ∀x,x ∈ E)
    (P:L[X]) (hP0:P ≠ 0) (hPb:P.eval b=0)
    (hPc: ∀n,P.coeff n ∈ IntermediateField.adjoin k {s}) (N:ℕ) (hPN:P.natDegree≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0) (hπ: ∃x,v x=exp (-1)):
    (∃C,CrudeBound v D C)∧
      ∀s₀:L,Tame v D (exp Λ0) s₀→v (s-s₀)<1→HFree6812.ResiduallySeparable v D (exp Λ0):=by
  classical
  let A:=Polynomial k
  letI:Algebra A L:=(Polynomial.aeval s).toRingHom.toAlgebra
  have hAmap: ∀a:A,algebraMap A L a=aeval s a:=fun _=>rfl
  have hinj:Function.Injective (algebraMap A L):=transcendental_iff_injective.1 hst
  haveI:FaithfulSMul A L:=(faithfulSMul_iff_algebraMap_injective A L).2 hinj
  let K' :=FractionRing A
  letI:Algebra K' L:=FractionRing.liftAlgebra A L
  have hAK' : ∀a:A,algebraMap K' L (algebraMap A K' a)=aeval s a:=fun a=>by
    rw [← IsScalarTower.algebraMap_apply];rfl
  have hrange: ∀x ∈ IntermediateField.adjoin k {s},∃y:K',algebraMap K' L y=x:=by
    intro x hx
    obtain ⟨r,t,rfl⟩:=(IntermediateField.mem_adjoin_simple_iff k x).1 hx
    exact ⟨algebraMap A K' r/algebraMap A K' t,by rw [map_div₀,hAK',hAK']⟩
  have hlift:P ∈ Polynomial.lifts (algebraMap K' L):=by
    rw [Polynomial.lifts_iff_coeff_lifts];intro n;exact hrange _ (hPc n)
  obtain ⟨P',hP'⟩:=(Polynomial.mem_lifts P).1 hlift
  have hP'0:P' ≠ 0:=by rintro rfl;exact hP0 (by rw [← hP',Polynomial.map_zero])
  have hP'b:aeval b P' =0:=by rw [aeval_def,← eval_map,hP'];exact hPb
  have hbint:IsIntegral K' b:=IsAlgebraic.isIntegral ⟨P',hP'0,hP'b⟩
  have hdegb:(minpoly K' b).natDegree≤N:=by
    refine (natDegree_le_of_dvd (minpoly.dvd K' b hP'b) hP'0).trans ?_
    rw [← natDegree_map_eq_of_injective (algebraMap K' L).injective,hP'];exact hPN
  have htop:IntermediateField.adjoin K' {b}= ⊤ :=by
    have hK'E: ∀y:K',algebraMap K' L y ∈ (IntermediateField.adjoin K' {b}).toSubfield:=
      fun y=>(IntermediateField.adjoin K' {b}).algebraMap_mem y
    have hall:=hgen (IntermediateField.adjoin K' {b}).toSubfield
      (fun x hx=>by
        have h1:=hAK' (Polynomial.C ⟨x,hx⟩)
        rw [aeval_C] at h1
        rw [← show algebraMap k L ⟨x,hx⟩=x from rfl,← h1];exact hK'E _)
      (by have h1:=hAK' Polynomial.X
          rw [aeval_X] at h1
          rw [← h1];exact hK'E _)
      (IntermediateField.subset_adjoin K' {b} (Set.mem_singleton b))
    exact eq_top_iff.2 fun x _=>hall x
  let e:IntermediateField.adjoin K' {b} ≃ₐ[K'] L:=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  haveI:FiniteDimensional K' (IntermediateField.adjoin K' {b}):=
    IntermediateField.adjoin.finiteDimensional hbint
  haveI:FiniteDimensional K' L:=e.toLinearEquiv.finiteDimensional
  have hfinrank:Module.finrank K' L≤N:=by
    rw [← e.toLinearEquiv.finrank_eq,IntermediateField.adjoin.finrank hbint];exact hdegb
  have hcharL: ∀n:ℕ,0<n→n≤N→(n:L) ≠ 0:=by
    intro n hn hnN h
    apply hNK n hn hnN
    rw [← map_natCast (algebraMap K L)] at h
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h
  haveI:Algebra.IsSeparable K' L:=⟨fun x=>by
    have hx:IsIntegral K' x:=Algebra.IsIntegral.isIntegral x
    refine HFree6812.separable_of_natDegree_ne_zero (minpoly.irreducible hx) fun h=> ?_
    refine hcharL _ (minpoly.natDegree_pos hx) ((minpoly.natDegree_le x).trans hfinrank) ?_
    have:=congrArg (algebraMap K' L) h
    rwa [map_natCast,map_zero] at this⟩

  have hkle: ∀a ∈ k,v a≤1:=by
    intro a ha
    by_cases h0:a=0
    · rw [h0,v.map_zero];exact zero_le
    · exact (hkv a ha h0).le
  set Λ1:ℤ:=max Λ0 (max 0 (v (D s)).log)
  have hAtame: ∀Λ:ℤ,Λ0≤Λ→Tame v D (exp Λ) s→ ∀a:A,Tame v D (exp Λ) (aeval s a):=by
    intro Λ hΛ hs a
    induction a using Polynomial.induction_on' with
    | add p q hp hq=>rw [map_add];exact (tameSubring v D _).add_mem hp hq
    | monomial n c=>
      rw [aeval_monomial]
      refine (tameSubring v D _).mul_mem ⟨hkle _ c.2,(hkD _ c.2).trans ?_⟩
        ((tameSubring v D _).pow_mem hs n)
      rw [exp_le_exp];exact hΛ
  have hsΛ1:Tame v D (exp Λ1) s:=
    ⟨hs1,(HFree6812.v_le_exp_max_log v _).trans (by rw [exp_le_exp];exact le_max_right _ _)⟩
  have hA1: ∀a:A,Tame v D (exp Λ1) (algebraMap A L a):=
    hAtame Λ1 (le_max_left _ _) hsΛ1
  have hfrac:=FQL v A K' (fun a=>(hA1 a).1) hπ
  refine ⟨?_,fun s₀ hs₀ hss₀=> ?_⟩
  · obtain ⟨C,hC⟩:=GXV v D A K' Λ1 hA1
    refine ⟨C,HFree6812.continuity_of_localization v D (tameSubring v D (exp C)) C (fun r hr=>hr)
      fun z hz=> ?_⟩
    obtain ⟨r,u,hr,hu,hu1,rfl⟩:=hfrac z hz
    exact ⟨r,hC r hr,u,hC u hu,hu1,rfl⟩
  · set S:Set L:=(k:Set L) ∪ {s₀}
    have hS: ∀z ∈ S,Tame v D (exp Λ0) z:=by
      rintro z (hz | hz)
      · exact ⟨hkle z hz,hkD z hz⟩
      · rw [Set.mem_singleton_iff.1 hz];exact hs₀
    set F' :=Subfield.closure (residue v '' S)
    have hs₀1:v s₀≤1:=hs₀.1
    have hress:residue v s=residue v s₀:=by
      have h1:v (s-s₀)≤1:=hss₀.le
      have h2:=residue_add v (s-s₀) s₀ h1 hs₀1
      rw [sub_add_cancel,(HFree6812.residue_eq_zero_iff_lt_one v _ h1).2 hss₀,zero_add] at h2
      exact h2
    have hF' : ∀a:A,residue v (algebraMap A L a) ∈ F' :=by
      intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq=>
        rw [map_add,residue_add v _ _ (hA1 p).1 (hA1 q).1];exact F'.add_mem hp hq
      | monomial n c=>
        have hpow: ∀n:ℕ,v (s^n)≤1:=fun n=>by rw [v.map_pow];exact pow_le_one' hs1 n
        rw [hAmap,aeval_monomial]
        change residue v ((c:L)*s^n) ∈ F'
        rw [residue_mul v _ _ (hkle _ c.2) (hpow n)]
        refine F'.mul_mem (Subfield.subset_closure ⟨c,Or.inl c.2,rfl⟩) ?_
        induction n with
        | zero=>
          rw [pow_zero];exact Subfield.subset_closure ⟨1,Or.inl k.one_mem,rfl⟩
        | succ n ih=>
          rw [pow_succ,residue_mul v _ _ (hpow n) hs1,hress]
          exact F'.mul_mem ih (Subfield.subset_closure ⟨s₀,Or.inr rfl,rfl⟩)
    have hNF: ∀n:ℕ,0<n→n≤N→
        (n:IsLocalRing.ResidueField v.valuationSubring) ≠ 0:=by
      intro n hn hnN h
      have hvn:v (n:L)=1:=hkv _ (by
        rw [← map_natCast (algebraMap K L)];exact k.algebraMap_mem _) (hcharL n hn hnN)
      have h1:residue v (n:L)=0:=by
        rw [HFree6812.residue_of_le v _ hvn.le,← h,← map_natCast (IsLocalRing.residue _)];rfl
      rw [HFree6812.residue_eq_zero_iff_lt_one v _ hvn.le,hvn] at h1
      exact lt_irrefl _ h1
    have hsepres:=FIC v A K' (fun a=>(hA1 a).1) F' hF' N hfinrank hNF
    haveI:Algebra.IsSeparable F' (IsLocalRing.ResidueField v.valuationSubring):=⟨fun x=>by
      obtain ⟨z,rfl⟩:=IsLocalRing.residue_surjective x
      obtain ⟨r,u,hr,hu,hu1,hz⟩:=hfrac z z.2
      have hr1:v r≤1:=ASC v (fun a=>(hA1 a).1) hr
      have hu0:residue v u ≠ 0:=fun h=>
        (lt_irrefl (1:ℤᵐ⁰)) (hu1 ▸ (HFree6812.residue_eq_zero_iff_lt_one v u hu1.le).1 h)
      have hzr:residue v (z:L)*residue v u=residue v r:=by
        rw [← residue_mul v _ _ z.2 hu1.le,hz,div_mul_cancel₀]
        intro h;rw [h,v.map_zero] at hu1;exact zero_ne_one hu1
      have hx:IsLocalRing.residue v.valuationSubring z=residue v r/residue v u:=by
        rw [eq_div_iff hu0,← hzr,HFree6812.residue_of_le v _ z.2]
      rw [hx]
      exact (separableClosure F' _).div_mem (hsepres r hr) (hsepres u hu)⟩
    exact HFree6812.residuallySeparable_of_isSeparable v D (exp Λ0) S hS
end Engine
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open MvPolynomial
section Core
variable {K L:Type*} [Field K] [Field L] [Algebra K L]
theorem core_poly_p19 (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0) (N:ℕ)
    (hN: ∀d ∈ F.support,d 1+d 2+d 3≤N) (x0:L) (x:Fin 3→L)
    (hFx:aeval (Fin.cons x0 x:Fin 4→L) F=0) (q:Fin 3→Polynomial K) (i a c:Fin 3)
    (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c) (hqi:q i=1)
    (hind:AlgebraicIndependent K (fun o:Option (Fin 2)=>
      o.elim (x a) ![∑ m,Polynomial.aeval x0 (q m)*x m,x0])):
    ∃P:Polynomial L,P ≠ 0∧P.eval (x c)=0∧P.natDegree≤N∧
      ∀n,P.coeff n ∈ Algebra.adjoin K {x0,∑ m,Polynomial.aeval x0 (q m)*x m,x a}:=by
  classical
  set ℓ:= ∑ m,Polynomial.aeval x0 (q m)*x m with hℓ
  set S:=Algebra.adjoin K ({x0,ℓ,x a}:Set L)
  set w:Option (Fin 2)→L:=fun o=>o.elim (x a) ![ℓ,x0]
  have hwS: ∀o,w o ∈ S:=by
    rintro (_ | j)
    · exact Algebra.subset_adjoin (by simp [w])
    · fin_cases j
      · exact Algebra.subset_adjoin (by simp [w])
      · exact Algebra.subset_adjoin (by simp [w])
  let wS:Option (Fin 2)→S:=fun o=>⟨w o,hwS o⟩
  have hwSind:AlgebraicIndependent K wS:=AlgebraicIndependent.of_comp S.val hind
  let V:Option (Option (Fin 2))→Polynomial S:=
    fun o=>o.elim Polynomial.X fun j=>Polynomial.C (wS j)
  let σv:Fin 4→MvPolynomial (Option (Option (Fin 2))) K:=
    subVals q a c (MvPolynomial.X (some (some 1))) (MvPolynomial.X (some (some 0))) (MvPolynomial.X (some none)) (MvPolynomial.X none)
  let τv:Option (Option (Fin 2))→MvPolynomial (Fin 4) K:=fun o=>
    o.elim (MvPolynomial.X c.succ) fun o' =>o'.elim (MvPolynomial.X a.succ)
      ![∑ m,Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) (q m)*MvPolynomial.X m.succ,MvPolynomial.X 0]
  have hτσ:(fun m=>aeval τv (σv m))=MvPolynomial.X:=by
    rw [map_subVals]
    simp only [aeval_X]
    rw [show τv (some (some 0))= ∑ m,Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) (q m)*
      (fun m:Fin 3=>(MvPolynomial.X m.succ:MvPolynomial (Fin 4) K)) m from rfl,
      show τv (some (some 1))=MvPolynomial.X 0 from rfl,show τv (some none)=MvPolynomial.X a.succ from rfl,
      show τv none=MvPolynomial.X c.succ from rfl]
    rw [subVals_cons q i a c hia hic hac hqi]
    funext m
    refine Fin.cases rfl (fun m=>rfl) m
  have hσF:aeval σv F ≠ 0:=by
    intro h
    apply hF
    have h1:=congrArg (aeval τv) h
    rw [comp_aeval_apply,map_zero,hτσ,aeval_X_left_apply] at h1
    exact h1
  set Q:Polynomial S:=aeval V (aeval σv F)
  have hQ0:Q ≠ 0:=fun h=>
    hσF (HFree6812.aeval_optionElim_injective wS hwSind (h.trans (map_zero _).symm))
  have hSinj:Function.Injective (algebraMap S L):=Subtype.val_injective
  refine ⟨Q.map (algebraMap S L),?_,?_,?_,?_⟩
  · exact (Polynomial.map_ne_zero_iff hSinj).2 hQ0
  · rw [Polynomial.eval_map,← Polynomial.aeval_def]
    have h1:=comp_aeval_apply ((Polynomial.aeval (R:=S) (x c)).restrictScalars K) (f:=V)
      (aeval σv F)
    rw [AlgHom.restrictScalars_apply] at h1
    rw [show (Polynomial.aeval (x c)) Q=_ from h1,comp_aeval_apply,map_subVals]
    simp only [aeval_X]
    rw [← hFx,← subVals_cons q i a c hia hic hac hqi x0 x]
    simp only [V,Option.elim,AlgHom.restrictScalars_apply,Polynomial.aeval_C,
      Polynomial.aeval_X]
    rfl
  · rw [Polynomial.natDegree_map_eq_of_injective hSinj]
    change (aeval V (aeval σv F)).natDegree≤N
    rw [comp_aeval_apply,map_subVals]
    simp only [aeval_X]
    have hC: ∀j,(V (some j)).natDegree=0:=fun j=>Polynomial.natDegree_C _
    refine HFree6812.natDegree_aeval_le F _ N hN (hC _) fun m=> ?_
    refine Fin.cases ((hC _).le.trans zero_le_one) (fun m=> ?_) m
    simp only [subVals,Fin.cons_succ]
    split_ifs
    · exact (hC _).le.trans zero_le_one
    · exact Polynomial.natDegree_X_le
    · have h1: ∀p:Polynomial K,(Polynomial.aeval (V (some (some 1))) p).natDegree=0:=
        fun p=>by
          rw [show V (some (some 1))=Polynomial.C (wS (some 1)) from rfl,
            ← Polynomial.algebraMap_eq (R:=S),Polynomial.aeval_algebraMap_apply,
            Polynomial.algebraMap_eq]
          exact Polynomial.natDegree_C _
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ((hC _).le.trans zero_le_one) ?_)) ?_)
      · exact Polynomial.natDegree_mul_le.trans (by rw [h1,hC];simp)
      · refine Polynomial.natDegree_mul_le.trans ?_
        rw [h1,zero_add];exact Polynomial.natDegree_X_le
  · intro n
    rw [Polynomial.coeff_map]
    exact (Q.coeff n).2
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
section SliceField
variable {K:Type} [Field K] (F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
theorem DJT {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰) {k:Type*}
    [Field k] [Algebra k L] (hk: ∀a:k,v (algebraMap k L a)≤1) {z:L} (hz0:z ≠ 0)
    (hz:IsAlgebraic k z):v z=1:=by
  have h1:=ASC v hk hz.isIntegral
  have h2:=ASC v hk (IsAlgebraic.inv_iff.2 hz).isIntegral
  rw [map_inv₀] at h2
  have hv0:v z ≠ 0:=(Valuation.ne_zero_iff v).2 hz0
  refine le_antisymm h1 ?_
  by_contra h
  rw [not_le] at h
  exact absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 hv0)).2 h))
end SliceField
section Slice
variable {K:Type} [Field K] {E:Type} [Field E] [Algebra (GenericField K) E]
  [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
  (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀:MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
theorem GCL (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K)
    (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰)
    (he:1≤e) (hwve: ∀x,ν.val (HFree6812.sliceEmbedding D F₀ hker x)=v x^e):
    ∀z ∈ kField F₀ q,z ≠ 0→v z=1:=by
  intro z hz hz0
  obtain ⟨y,hy⟩:=psi_kField D F₀ hker c q hq hslice z hz
  have hy0:y ≠ 0:=by
    rintro rfl
    rw [map_zero,eq_comm,map_eq_zero_iff _ (HFree6812.sliceEmbedding D F₀ hker).injective] at hy
    exact hz0 hy
  have h1:ν.val (HFree6812.sliceEmbedding D F₀ hker z)=1:=by
    rw [← hy];exact (ν.property.2).eq_one y hy0
  rw [hwve] at h1
  have he0:e ≠ 0:=by omega
  exact le_antisymm ((HFree6812.zm_pow_le_one he0).1 h1.le)
    (not_lt.1 fun hlt=>absurd h1 (ne_of_lt ((HFree6812.zm_pow_lt_one he0).2 hlt)))
end Slice
section Main
variable {K:Type} [Field K] {E:Type} [Field E] [Algebra (GenericField K) E]
  [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
theorem hdefer_holds_p19 (F:MvPolynomial (Fin 4) K) (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0):
    ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (HFree6812.sliceEmbedding D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)∧
      HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
        (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))):=by
  intro F₀ _ hdvd hker ν e v he hvn hwve
  classical
  set Dd:=HFree6812.sliceDerivation F F₀ hdvd with hDd
  set X0:=sliceProj F₀ (MvPolynomial.X 0) with hX0
  set x:=sliceCoord F₀ with hx
  set ℓ:=sliceLinearL F₀ q with hℓ
  set k:=kField F₀ q with hk
  set Λ0:=vpole v (Dd ℓ) with hΛ0
  have hqi:q i=1:=RCN135.polynomialEmbedding_injective K (by rw [hq,hci,map_one])
  have hH:sliceProj F₀ (polyH K F) ≠ 0:=by
    intro h
    apply hHD
    have h1:HFree6812.sliceEmbedding D F₀ hker (sliceProj F₀ (polyH K F))=0:=by rw [h,map_zero]
    rw [HFree6812.sliceEmbedding_proj] at h1
    exact (HFree6812.coordEval_eq_zero_iff D _).1 h1
  have hF:F ≠ 0:=by rintro rfl;apply hHD;simp [polyH]
  have hkv: ∀z ∈ k,z ≠ 0→v z=1:=GCL D F₀ hker c q hq hslice ν e v he hwve
  have hkle: ∀z ∈ k,v z≤1:=fun z hz=>by
    by_cases h0:z=0
    · rw [h0,v.map_zero];exact zero_le
    · exact (hkv z hz h0).le
  have hkle' : ∀r:k,v (algebraMap k (SliceField F₀) r)≤1:=fun r=>hkle r r.2
  have hAI1:=HFree6812.algInd_ell_X0 D F₀ hker c q hq hslice
  have hΛ0nn:0≤Λ0:=vpole_nonneg _ _
  have hℓk:ℓ ∈ k:=IntermediateField.subset_adjoin K _ ⟨0,rfl⟩
  have hX0k:X0 ∈ k:=IntermediateField.subset_adjoin K _ ⟨1,rfl⟩
  have hkT: ∀z ∈ k,Tame v Dd (exp Λ0) z:=by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem z hz=>
      obtain ⟨j,rfl⟩:=hz
      fin_cases j
      · exact ⟨hkle _ hℓk,HFree6812.v_le_exp_vpole v _⟩
      · refine ⟨hkle _ hX0k,?_⟩
        show v (Dd X0)≤_
        rw [hDd,HFree6812.sliceDerivation_X0 F F₀ hdvd hH,v.map_one,← exp_zero,exp_le_exp]
        exact hΛ0nn
    | algebraMap r=>
      refine ⟨hkle _ (k.algebraMap_mem r),?_⟩
      rw [Derivation.map_algebraMap,v.map_zero];exact zero_le
    | add z w _ _ hz hw=>exact (tameSubring v Dd _).add_mem hz hw
    | mul z w _ _ hz hw=>exact (tameSubring v Dd _).mul_mem hz hw
    | inv z hzk hz=>
      by_cases h0:z=0
      · rw [h0,inv_zero];exact (tameSubring v Dd _).zero_mem
      · exact tame_inv v Dd _ z hz (hkv z hzk h0)
  have hkD: ∀z ∈ k,v (Dd z)≤exp Λ0:=fun z hz=>(hkT z hz).2
  have hN' :=HFree6812.support_bound_of_weighted F N hN
  have hFx:aeval (Fin.cons X0 x:Fin 4→SliceField F₀) F=0:=by
    rw [aeval_slice];exact (HFree6812.sliceProj_eq_zero_iff F₀ F).2 hdvd
  have haevk: ∀p:Polynomial K,Polynomial.aeval X0 p ∈ k:=by
    intro p
    have h1:=Polynomial.aeval_algebraMap_apply (SliceField F₀) (⟨X0,hX0k⟩:k) p
    rw [show algebraMap k (SliceField F₀) ⟨X0,hX0k⟩=X0 from rfl] at h1
    rw [h1];exact (Polynomial.aeval (⟨X0,hX0k⟩:k) p).2

  have key: ∀a c',i ≠ a→i ≠ c' →a ≠ c' →
      AlgebraicIndependent K (fun o:Option (Fin 2)=>o.elim (x a) ![ℓ,X0])→
      ∀s:SliceField F₀,(s=x a∨s*x a=1)→v s≤1→
      ∀s₀,Tame v Dd (exp Λ0) s₀→v (s-s₀)<1→
      (∃C,CrudeBound v Dd C)∧HFree6812.ResiduallySeparable v Dd (exp Λ0):=by
    intro a c' hia hic hac hind s hs hs1 s₀ hs₀ hss₀
    obtain ⟨P,hP0,hPb,hPN,hPc⟩:=
      core_poly_p19 F hF N hN' X0 x hFx q i a c' hia hic hac hqi hind
    have htr:Transcendental k (x a):=
      IntermediateField.transcendental_adjoin_iff.2 (AlgebraicIndependent.option_iff.1 hind).2
    have hinv:s*x a=1→x a=s⁻¹:=fun h=>eq_inv_of_mul_eq_one_right h
    have hxa:x a ∈ IntermediateField.adjoin k {s}:=by
      rcases hs with rfl | hs
      · exact IntermediateField.mem_adjoin_simple_self k _
      · rw [hinv hs];exact inv_mem (IntermediateField.mem_adjoin_simple_self k s)
    have hst:Transcendental k s:=by
      rcases hs with rfl | hs
      · exact htr
      · have h1:s=(x a)⁻¹:=by rw [hinv hs,inv_inv]
        rw [h1];exact fun h=>htr (IsAlgebraic.inv_iff.1 h)
    have hkin: ∀z ∈ k,z ∈ IntermediateField.adjoin k {s}:=fun z hz=>
      (IntermediateField.adjoin k {s}).algebraMap_mem ⟨z,hz⟩
    have hPc' : ∀n,P.coeff n ∈ IntermediateField.adjoin k {s}:=by
      intro n
      have hle:Algebra.adjoin K {X0,ℓ,x a}≤
          ((IntermediateField.adjoin k {s}).restrictScalars K).toSubalgebra:=by
        rw [Algebra.adjoin_le_iff]
        rintro z (rfl | rfl | rfl)
        · exact hkin _ hX0k
        · exact hkin _ hℓk
        · exact hxa
      exact hle (hPc n)
    have hgen: ∀E' :Subfield (SliceField F₀),(∀z ∈ k,z ∈ E')→s ∈ E' →x c' ∈ E' →
        ∀z,z ∈ E' :=by
      intro E' hkE hsE hcE
      have haE:x a ∈ E' :=by
        rcases hs with rfl | hs
        · exact hsE
        · rw [hinv hs];exact E'.inv_mem hsE
      refine slice_gen F₀ E' (fun r=>hkE _ (k.algebraMap_mem r)) (hkE _ hX0k) fun j=> ?_
      by_cases hja:j=a
      · rw [hja];exact haE
      by_cases hjc:j=c'
      · rw [hjc];exact hcE
      rw [HFree6812.eq_of_ne_of_ne hia hic hac hja hjc]
      change x i ∈ E'
      rw [split_sum' q i a c' hia hic hac hqi X0 x]
      exact E'.sub_mem (E'.sub_mem (hkE _ hℓk) (E'.mul_mem (hkE _ (haevk _)) haE))
        (E'.mul_mem (hkE _ (haevk _)) hcE)
    have hen:=engine_p19 v Dd k hkv Λ0 hkD s hs1 hst (x c') hgen P hP0 hPb hPc' N hPN hNK hvn
    exact ⟨hen.1,hen.2 s₀ hs₀ hss₀⟩
  obtain ⟨π,hπ⟩:=hvn
  by_cases hinf: ∃j,j ≠ i∧1<v (x j)
  ·
    obtain ⟨a,hai,ha⟩:=hinf
    obtain ⟨c',hci',hca⟩:=exists_third i a hai
    have hxa0:x a ≠ 0:=by
      intro h;rw [h,v.map_zero] at ha;exact not_lt.2 zero_le ha
    have htr:Transcendental k (x a):=fun halg=>
      (ne_of_gt ha) (DJT v hkle' hxa0 halg)
    have hind:=AlgebraicIndependent.option_iff.2
      ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 htr⟩
    have hvs:v (x a)⁻¹<1:=by
      rw [map_inv₀];exact inv_lt_one_of_one_lt₀ ha
    refine key a c' (Ne.symm hai) (Ne.symm hci') (Ne.symm hca) hind (x a)⁻¹
      (Or.inr (inv_mul_cancel₀ hxa0)) hvs.le 0 (tameSubring v Dd _).zero_mem (by rwa [sub_zero])

  push Not at hinf
  obtain ⟨a1,a2,h1,h2,h12⟩:=HFree6812.exists_two_others i
  have hall: ∀j,v (x j)≤1:=by
    intro j
    by_cases hji:j=i
    · rw [hji,split_sum' q i a1 a2 h1 h2 h12 hqi X0 x]
      have hq' : ∀m,v (Polynomial.aeval X0 (q m))≤1:=fun m=>hkle _ (haevk _)
      refine (v.map_sub _ _).trans (max_le ((v.map_sub _ _).trans (max_le (hkle _ hℓk) ?_)) ?_)
      · rw [v.map_mul];exact mul_le_one' (hq' _) (hinf a1 (Ne.symm h1))
      · rw [v.map_mul];exact mul_le_one' (hq' _) (hinf a2 (Ne.symm h2))
    · exact hinf j hji
  have htame: ∀a:Fin 3,a ≠ 1→Tame v Dd (exp Λ0) (x a):=by
    intro a ha1
    refine ⟨hall a,?_⟩
    fin_cases a
    · show v (Dd (sliceCoord F₀ 0))≤_
      rw [hDd,HFree6812.sliceDerivation_coord0 F F₀ hdvd hH]
      exact (hall 1).trans (by rw [← exp_zero,exp_le_exp];exact hΛ0nn)
    · exact absurd rfl ha1
    · show v (Dd (sliceCoord F₀ 2))≤_
      rw [hDd,HFree6812.sliceDerivation_coord2 F F₀ hdvd hH,v.map_zero];exact zero_le
  have hself: ∀a:Fin 3,v (x a-x a)<1:=fun a=>by
    rw [sub_self,v.map_zero];exact zero_lt_one
  by_cases hi1:i=1
  · subst hi1
    by_cases ht0:Transcendental k (x 0)
    · exact key 0 2 (by decide) (by decide) (by decide) (AlgebraicIndependent.option_iff.2
        ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 ht0⟩) (x 0) (Or.inl rfl) (hall 0)
        (x 0) (htame 0 (by decide)) (hself 0)
    by_cases ht2:Transcendental k (x 2)
    · exact key 2 0 (by decide) (by decide) (by decide) (AlgebraicIndependent.option_iff.2
        ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 ht2⟩) (x 2) (Or.inl rfl) (hall 2)
        (x 2) (htame 2 (by decide)) (hself 2)
    exfalso
    have hA: ∀z,z ∈ (algebraicClosure k (SliceField F₀)).toSubfield:=by
      have hkA: ∀z ∈ k,z ∈ (algebraicClosure k (SliceField F₀)).toSubfield:=fun z hz=>
        mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap (⟨z,hz⟩:k))
      set A:=(algebraicClosure k (SliceField F₀)).toSubfield
      have h0:x 0 ∈ A:=mem_algebraicClosure_iff.2 (not_not.1 ht0)
      have h2' :x 2 ∈ A:=mem_algebraicClosure_iff.2 (not_not.1 ht2)
      refine slice_gen F₀ A (fun r=>hkA _ (k.algebraMap_mem r)) (hkA _ hX0k) fun j=> ?_
      fin_cases j
      · exact h0
      · change x 1 ∈ A
        rw [split_sum' q 1 0 2 (by decide) (by decide) (by decide) hqi X0 x]
        exact A.sub_mem (A.sub_mem (hkA _ hℓk) (A.mul_mem (hkA _ (haevk _)) h0))
          (A.mul_mem (hkA _ (haevk _)) h2')
      · exact h2'
    have hπ0:π ≠ 0:=by rintro rfl;rw [v.map_zero] at hπ;exact exp_ne_zero hπ.symm
    have h1:=DJT v hkle' hπ0 (mem_algebraicClosure_iff.1 (hA π))
    rw [hπ,← exp_zero,exp_inj] at h1
    omega
  · have hq10:q 1=0:=hq1.resolve_left hi1
    have h2vars:(2:Fin 4) ∈ F₀.vars:=by
      obtain ⟨F₁,hF₁⟩:=HFree6812.sliceProj_H_eq F F₀ hdvd
      by_contra h
      rw [pderiv_eq_zero_of_notMem_vars h,map_zero,mul_zero] at hF₁
      exact hH hF₁
    obtain ⟨a,hia,ha1⟩:=HFree6812.exists_not_one i hi1
    exact key a 1 hia hi1 ha1 (algInd_of_Y'_free F₀ q i a hia hi1 ha1 hqi hq10 h2vars) (x a)
      (Or.inl rfl) (hall a) (x a) (htame a ha1) (hself a)
end Main
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
section Gaps
variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
theorem hdefer_gap_p19 (F:MvPolynomial (Fin 4) K) (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hq: ∀m,RCN135.polynomialEmbedding K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0):
    ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place_p19 E (RCN002.CoordinateField E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (HFree6812.sliceEmbedding D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (HFree6812.sliceDerivation F F₀ hdvd) C)∧
      HFree6812.ResiduallySeparable v (HFree6812.sliceDerivation F F₀ hdvd)
        (exp (vpole v (HFree6812.sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))):=
  hdefer_holds_p19 F D hHD c i hci q hq hq1 hslice N hN hNK
theorem hchar_gap_p19 [CharP K 2130706433] (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep:RCN341.SeparableLiteralCoordinate D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      RCN208.scalarPolynomialMap (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N) (hN9:N≤9678):
    ∀ν:RCN026.Place_p19 E (RCN002.CoordinateField E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)))→(n:K) ≠ 0:=
  hchar_holds_p19 F D sep hFD hHD c i hci hslice N hN hN9
end Gaps
end
end HFree6812
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace HFreeDir6813
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place_p19)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN095 renaming PolynomialInFlag → BI
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open BIZ
open ActualFirstCutPole6807 renaming pole_le_of_value_le → BIH
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
section Slice
local notation "w" =>RCN326.w
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
structure APH (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 Cap:FlagDegree):Prop where
  pole_le: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu+
        2*RCN026.zeroOrder_p19 E (RCN002.CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F))-
        flagPole nu.val (coordinate E C) Cap)+
      3*flagPole nu.val (coordinate E C) C0)
end Slice
section Stage
local notation "w" =>RCN326.w
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "φE" =>RingHom.comp (algebraMap (GenericField K) E) (RCN135.polynomialEmbedding K)
variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
def CTP (F:MvPolynomial (Fin 4) K) (ell:MvPolynomial (Fin 3) Ω)
    (C0:FlagDegree) (d:Fin 3):Prop:=
  ∀(D:Ideal PE) [D.IsPrime],RCN341.SeparableLiteralCoordinate D→
    surfaceMap φE F ∈ D→GenericSlicePoints6807.sliceEquation (E:=E) ell ∈ D→
    surfaceMap φE (polyH K F) ∉ D→APH φE F D C0 (HFree6812.infCap d)
end Stage
section Retained
open HK PR FA
open CommonLinearChannels6807 (linearA linearU linearZ)
open RCN046 RCN084 RCN159 RCN198 RCN199 RCN206 RCN207 RCN237 RCN238 RCN243
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN263 RCN264 RCN271 RCN275 RCN287 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339
open RCN340 RCN344
open JN IB
open BD
open MovingFiberThreeSources6811 (direction weight)
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap:ℕ}
local notation "Ω" =>GenericField K
def ASY (t y r:ℕ) (j:Fin 3):FlagDegree:=
  hfreeFlagDir j r (y-r) (t-y) unitAllFlag
end Retained
end
end HFreeDir6813
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart2
namespace LD
open RCN100 ClosedRank
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
def rankAffine (m s:ℕ) (L:ℤ):ℤ:=
  sourceTwelve m L s-ClosedRank.removedPartialTwelve m L s (min s (m/2):ℕ)
def rankSlope (m s:ℕ):ℤ:=rankAffine m s 1-rankAffine m s 0
def CPJ (m s:ℕ):ℤ:=rankAffine m s 0
def countSlope (D s:ℕ):ℤ:=ECJ (D/131071) (D%131071) 131071 s
def WY (D s:ℕ):ℤ:=CSW (D/131071) (D%131071) 131071 s
def marginA (D nu s R m mu:ℕ):ℤ:=
  12*(countSlope D s-countSlope (D-nu) (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def marginB (D nu s R m mu:ℕ):ℤ:=
  12*countSlope (D-nu) (s-R)-262144*rankSlope (m-mu) (s-R)
def marginC (D nu s R m mu:ℕ):ℤ:=
  12*(WY D s-WY (D-nu) (s-R))-
    262144*(CPJ m s-CPJ (m-mu) (s-R))
end LD
end MergedPart2
section MergedPart3
namespace AP
open LD
open RCN100
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000
structure Band where
  R:ℕ
  B:ℕ
  T0:ℕ
  T1:ℕ
  count:ℕ
  deriving DecidableEq
structure Rectangle where
  lo:ℕ
  hi:ℕ
  alpha:ℕ
  beta:ℕ
  s:ℕ
  L0:ℕ
  L1:ℕ
  U:ℕ
  deriving DecidableEq
def tail (b:Band):ℕ:=(b.B+b.R-1)*181059+131071-1
def cutoff (b:Band) (d:Rectangle):ℕ:=
  d.alpha*181059-d.beta*min (d.hi-131071+1) ((b.B+b.R-1)*181059)
def lowerTotal (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  max (T+d.alpha+d.s) (max (cutoff b d/131071+1) (T+(cutoff b d-d.lo)/131071+1))
def total (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  if b.T0=b.T1 then d.L0 else ceilBlend b.T0 b.T1 d.L0 d.L1 T
def Shape (b:Band) (d:Rectangle):Prop:=
  b.T0≤b.T1∧b.R≤d.s∧d.s<131071∧131071≤d.lo∧d.lo≤d.hi∧
  d.hi≤tail b∧0<cutoff b d∧d.s≤cutoff b d/131071∧
  d.s-b.R≤(cutoff b d-d.lo)/131071∧
  lowerTotal b d b.T0≤d.L0∧lowerTotal b d b.T1≤d.L1
def rowGood (b:Band) (d:Rectangle) (mu:ℕ):Prop:=
  let m:=d.alpha-d.beta*(mu-1)
  let a:=marginA (cutoff b d) d.lo d.s b.R m mu
  let v:=marginB (cutoff b d) d.lo d.s b.R m mu
  let c:=marginC (cutoff b d) d.lo d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c∧max 0 (-a)<a*d.L1+v*b.T1+c
instance shapeDecidable (b:Band) (d:Rectangle):Decidable (Shape b d):=by
  unfold Shape
  infer_instance
instance rowGoodDecidable (b:Band) (d:Rectangle) (mu:ℕ):Decidable (rowGood b d mu):=by
  unfold rowGood
  infer_instance
def checkRows (b:Band) (d:Rectangle):ℕ→Bool
  | 0=>true
  | n+1=>checkRows b d n && decide (rowGood b d n)
end
end AP
end MergedPart3
section MergedPart4
namespace AP
open LD
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 BY
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN122 renaming specialization → BM
open ContactOrderBridge (Poly4)
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000
def pair (b:Band) (d:Rectangle):DG:=
  ⟨262144,131071,181059,b.B,b.R,b.T1,d.U,d.s,max d.L0 d.L1⟩
def Valid (b:Band) (d:Rectangle):Prop:=
  Shape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutoff b d≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧
  GB.FU (pair b d)≤b.count∧
  checkRows b d (b.B+b.R+1)=true
instance validDecidable (b:Band) (d:Rectangle):Decidable (Valid b d):=by
  unfold Valid
  infer_instance
end
end AP
end MergedPart4
section MergedPart6
namespace AP
open LD
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
structure Cubic where
  c0:ℤ
  c1:ℤ
  c2:ℤ
  c3:ℤ
def Cubic.eval (p:Cubic) (x:ℤ):ℤ:=((p.c3*x+p.c2)*x+p.c1)*x+p.c0
def Cubic.deriv (p:Cubic) (x:ℤ):ℤ:=(3*p.c3*x+2*p.c2)*x+p.c1
def Cubic.Check (p:Cubic) (a b:ℕ):Prop:=
  b<a∨(0<p.eval a∧0<p.eval b∧
    0≤3*p.eval a+((b:ℤ)-a)*p.deriv a∧
    0≤3*p.eval b-((b:ℤ)-a)*p.deriv b)
instance cubicCheckDecidable (p:Cubic) (a b:ℕ):Decidable (p.Check a b):=by
  unfold Cubic.Check
  infer_instance
def AVK (base rate L s:ℤ):Cubic:=
  let a0:=s*(s+1)*((4*s+2)*L-s*s+5*s+2)
  let a1:= -2*(s+1)*(3*L*s-3*L+6*s-4)
  let a2:=6*(L+1)*(s+1)
  let a3:= -2*(s+1)
  ⟨a0+a1*base+a2*base^2+a3*base^3,
    -rate*(a1+2*a2*base+3*a3*base^2),
    rate^2*(a2+3*a3*base),-a3*rate^3⟩
def BDN (b:Band) (d:Rectangle) (T L:ℕ):Cubic:=
  let p:=AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s
  let q:=AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)
  let c:=12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    WY (cutoff b d) d.s-WY (cutoff b d-d.lo) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩
end AP
end MergedPart6
section MergedPart7
namespace AP
open LD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000
structure FastWitness where
  normalEnd:ℕ
  firstExact:ℕ
  lastExact:ℕ
def checkRange (b:Band) (d:Rectangle) (start:ℕ):ℕ→Bool
  | 0=>true
  | n+1=>checkRange b d start n && decide (rowGood b d (start+n))
def corners (b:Band) (d:Rectangle) (a z:ℕ):Prop:=
  (BDN b d b.T0 d.L0).Check a z∧
  (BDN b d b.T0 (d.L0+1)).Check a z∧
  (BDN b d b.T1 d.L1).Check a z∧
  (BDN b d b.T1 (d.L1+1)).Check a z
instance cornersDecidable (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by
  unfold corners
  infer_instance
def FastRows (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  corners b d 1 (w.firstExact-1)∧corners b d (w.lastExact+1) w.normalEnd∧
  rowGood b d 0∧checkRange b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  checkRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true
instance fastRowsDecidable (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by
  unfold FastRows
  infer_instance
def Header (b:Band) (d:Rectangle):Prop:=
  Shape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutoff b d≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧GB.FU (pair b d)≤b.count
def FastValid (b:Band) (dw:Rectangle × FastWitness):Prop:=Header b dw.1∧FastRows b dw.1 dw.2
instance fastValidDecidable (b:Band) (dw:Rectangle × FastWitness):Decidable (FastValid b dw):=by
  unfold FastValid Header
  infer_instance
end
end AP
end MergedPart7
section MergedPart8
namespace AN
open AP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000
structure Profile where
  alpha:ℕ
  beta:ℕ
  s:ℕ
structure Entry where
  hi:ℕ
  profile:ℕ
  L0:ℕ
  deltaL:ℕ
  witness:ℕ
open MvPolynomial RCN100 RCN119 BY
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open ContactOrderBridge (Poly4)
open RCN234 (wt)
end
end AN
end MergedPart8
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace LD
open RCN100 ClosedRank
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
def tanMarginA (Dh k E s R m mu:ℕ):ℤ:=
  12*(countSlope Dh s+k*(countSlope (Dh+1) s-countSlope Dh s)-countSlope E (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def tanMarginB (E s R m mu:ℕ):ℤ:=
  12*countSlope E (s-R)-262144*rankSlope (m-mu) (s-R)
def tanMarginC (Dh k E s R m mu:ℕ):ℤ:=
  12*(WY Dh s+k*(WY (Dh+1) s-WY Dh s)-
      WY E (s-R))-
    262144*(CPJ m s-CPJ (m-mu) (s-R))
end LD
end MergedPart0
section MergedPart1
namespace AP
open LD
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 BY
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN122 renaming specialization → BM
open ContactOrderBridge (Poly4)
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000
def hiRect (d:Rectangle):Rectangle:={d with lo:=d.hi}
def cutAt (b:Band) (d:Rectangle) (nu:ℕ):ℕ:=
  d.alpha*181059-d.beta*min (nu-131071+1) ((b.B+b.R-1)*181059)
def tanK (b:Band) (d:Rectangle):ℕ:=cutAt b d d.lo-cutoff b d
def tanE (b:Band) (d:Rectangle):ℕ:=cutAt b d d.lo-d.lo
def tanLower (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  max ((cutoff b d+1)/131071+1) (T+tanE b d/131071+1)
def tanRowGood (b:Band) (d:Rectangle) (mu:ℕ):Prop:=
  let m:=d.alpha-d.beta*(mu-1)
  let a:=tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  let v:=tanMarginB (tanE b d) d.s b.R m mu
  let c:=tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c∧max 0 (-a)<a*d.L1+v*b.T1+c
instance tanRowGoodDecidable (b:Band) (d:Rectangle) (mu:ℕ):Decidable (tanRowGood b d mu):=by
  unfold tanRowGood
  infer_instance
def checkTanRows (b:Band) (d:Rectangle):ℕ→Bool
  | 0=>true
  | n+1=>checkTanRows b d n && decide (tanRowGood b d n)
def WideShape (b:Band) (d:Rectangle):Prop:=
  Shape b (hiRect d)∧131071≤d.lo∧d.lo≤d.hi∧d.hi<cutoff b d∧
  d.s≤(cutoff b d+1)/131071∧d.s-b.R≤tanE b d/131071∧
  tanLower b d b.T0≤d.L0∧tanLower b d b.T1≤d.L1
instance wideShapeDecidable (b:Band) (d:Rectangle):Decidable (WideShape b d):=by
  unfold WideShape Shape
  infer_instance
def WideValid (b:Band) (d:Rectangle):Prop:=
  WideShape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutAt b d d.lo≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧
  GB.FU (pair b d)≤b.count∧
  checkRows b (hiRect d) (b.B+b.R+1)=true∧checkTanRows b d (b.B+b.R+1)=true
instance wideValidDecidable (b:Band) (d:Rectangle):Decidable (WideValid b d):=by
  unfold WideValid
  infer_instance
end
end AP
end MergedPart1
section MergedPart3
namespace AP
open LD
open RCN100 ClosedRank
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000
def APE (b:Band) (d:Rectangle) (T L:ℕ):Cubic:=
  let p:=AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s
  let q:=AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)
  let c:=12*((countSlope (cutoff b d) d.s+
        (tanK b d:ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
        countSlope (tanE b d) (d.s-b.R))*L+
      countSlope (tanE b d) (d.s-b.R)*T+
      WY (cutoff b d) d.s+
        (tanK b d:ℤ)*(WY (cutoff b d+1) d.s-WY (cutoff b d) d.s)-
      WY (tanE b d) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩
def tanCorners (b:Band) (d:Rectangle) (a z:ℕ):Prop:=
  (APE b d b.T0 d.L0).Check a z∧
  (APE b d b.T0 (d.L0+1)).Check a z∧
  (APE b d b.T1 d.L1).Check a z∧
  (APE b d b.T1 (d.L1+1)).Check a z
instance tanCornersDecidable (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by
  unfold tanCorners
  infer_instance
def DSU (b:Band) (d:Rectangle) (start:ℕ):ℕ→Bool
  | 0=>true
  | n+1=>DSU b d start n && decide (tanRowGood b d (start+n))
def TanFastRows (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  tanCorners b d 1 (w.firstExact-1)∧tanCorners b d (w.lastExact+1) w.normalEnd∧
  tanRowGood b d 0∧DSU b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  DSU b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true
instance tanFastRowsDecidable (b:Band) (d:Rectangle) (w:FastWitness):
    Decidable (TanFastRows b d w):=by
  unfold TanFastRows
  infer_instance
def WideHeader (b:Band) (d:Rectangle):Prop:=
  WideShape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutAt b d d.lo≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧GB.FU (pair b d)≤b.count
structure WideRow where
  rect:Rectangle
  hiW:FastWitness
  tanW:FastWitness
def DRX (b:Band) (x:WideRow):Prop:=
  WideHeader b x.rect∧FastRows b (hiRect x.rect) x.hiW∧TanFastRows b x.rect x.tanW
instance wideFastValidDecidable (b:Band) (x:WideRow):Decidable (DRX b x):=by
  unfold DRX WideHeader
  infer_instance
end
end AP
end MergedPart3
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AI
open AP LD AN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000
structure WideEntry where
  hi:ℕ
  profile:ℕ
  L0:ℕ
  deltaL:ℕ
  hiW:FastWitness
  tanW:FastWitness
open MvPolynomial RCN100 RCN119 BY
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open ContactOrderBridge (Poly4)
open RCN234 (wt)
end
end AI
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace NatWideKernel80909
open LD AP AN AI
set_option autoImplicit false
set_option maxHeartbeats 10000000
structure Diff where
 pos : ℕ
 neg : ℕ
def value (d:Diff):ℤ:= (d.pos:ℤ)-d.neg
def ofInt:ℤ→Diff
 | .ofNat n => ⟨n,0⟩
 | .negSucc n => ⟨0,n+1⟩
def add (a b:Diff):Diff:=⟨a.pos+b.pos,a.neg+b.neg⟩
def sub (a b:Diff):Diff:=⟨a.pos+b.neg,a.neg+b.pos⟩
def scale (k:ℕ) (a:Diff):Diff:=⟨k*a.pos,k*a.neg⟩
lemma ofInt_eq (z:ℤ):value (ofInt z)=z:=by cases z <;> simp [value,ofInt] <;> omega
lemma add_eq (a b:Diff):value (add a b)=value a+value b:=by simp [value,add];ring
lemma sub_eq (a b:Diff):value (sub a b)=value a-value b:=by simp [value,sub];ring
lemma scale_eq (k:ℕ) (a:Diff):value (scale k a)= (k:ℤ)*value a:=by simp [value,scale];ring
lemma pos_iff (d:Diff): (0<value d)↔d.neg<d.pos:=by unfold value;omega
lemma nonneg_iff (d:Diff): (0≤value d)↔d.neg≤d.pos:=by unfold value;omega
def eval (p:Cubic) (x:ℕ):Diff:=add  (scale x  (add  (scale x  (add  (scale x  (ofInt p.c3))  (ofInt p.c2)))  (ofInt p.c1)))  (ofInt p.c0)
def deriv (p:Cubic) (x:ℕ):Diff:=add  (scale x  (add  (scale  (3*x)  (ofInt p.c3))  (scale 2  (ofInt p.c2))))  (ofInt p.c1)
lemma eval_eq (p:Cubic) (x:ℕ):value (eval p x)=p.eval x:=by
 simp only [eval,add_eq,scale_eq,ofInt_eq,Cubic.eval]
 ring
lemma deriv_eq (p:Cubic) (x:ℕ):value (deriv p x)=p.deriv x:=by
 simp only [deriv,add_eq,scale_eq,ofInt_eq,Cubic.deriv,Nat.cast_mul,Nat.cast_ofNat]
 ring
def mid1 (p:Cubic) (a b:ℕ):Diff:=add  (scale 3  (eval p a))  (scale  (b-a)  (deriv p a))
def mid2 (p:Cubic) (a b:ℕ):Diff:=sub  (scale 3  (eval p b))  (scale  (b-a)  (deriv p b))
def NatCheck (p:Cubic) (a b:ℕ):Prop:=b<a ∨
  (eval p a).neg< (eval p a).pos ∧  (eval p b).neg< (eval p b).pos ∧
  (mid1 p a b).neg≤ (mid1 p a b).pos ∧  (mid2 p a b).neg≤ (mid2 p a b).pos
instance (p:Cubic) (a b:ℕ):Decidable (NatCheck p a b):=by unfold NatCheck;infer_instance
lemma check_iff (p:Cubic) (a b:ℕ):NatCheck p a b↔p.Check a b:=by
 by_cases h:b<a
 · simp only [NatCheck,Cubic.Check,h,true_or]
 · have hab:a≤b:=by omega
   have hw: ( (b-a:ℕ):ℤ)= (b:ℤ)-a:=Int.ofNat_sub hab
   have h1:value (mid1 p a b)=3*p.eval a+ ( (b:ℤ)-a)*p.deriv a:=by
    simp only [mid1,add_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   have h2:value (mid2 p a b)=3*p.eval b- ( (b:ℤ)-a)*p.deriv b:=by
    simp only [mid2,sub_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   simp only [NatCheck,Cubic.Check,h,false_or]
   rw [←pos_iff,←pos_iff,←nonneg_iff,←nonneg_iff,eval_eq,eval_eq,h1,h2]
def checkDec (p:Cubic) (a b:ℕ):Decidable (p.Check a b):=decidable_of_iff  (NatCheck p a b)  (check_iff p a b)
attribute [local instance] checkDec
def cornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by unfold corners;infer_instance
attribute [local instance] cornersDec
def rowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by unfold FastRows;infer_instance
attribute [local instance] rowsDec
def tanCornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by unfold tanCorners;infer_instance
end NatWideKernel80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace NatRankWide80909
open LD AP AN AI
set_option autoImplicit false
set_option maxHeartbeats 10000000
def rank (base rate L s : ℕ) : Cubic :=
 let p0 : ℕ := s*(s+1)*((4*s+2)*L+5*s+2)+2*(s+1)*(3*L+4)*base+6*(L+1)*(s+1)*base^2
 let n0 : ℕ := s*(s+1)*s^2+2*(s+1)*(3*L*s+6*s)*base+2*(s+1)*base^3
 let p1 : ℕ := rate*(2*(s+1)*(3*L*s+6*s)+6*(s+1)*base^2)
 let n1 : ℕ := rate*(2*(s+1)*(3*L+4)+12*(L+1)*(s+1)*base)
 let p2 : ℕ := rate^2*6*(L+1)*(s+1)
 let n2 : ℕ := rate^2*6*(s+1)*base
 let p3 : ℕ := 2*(s+1)*rate^3
 ⟨(p0:ℤ)-n0,(p1:ℤ)-n1,(p2:ℤ)-n2,p3⟩
lemma rank_eq (base rate L s : ℕ) : rank base rate L s=AVK base rate L s := by
 simp only [rank,AVK,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 congr 1 <;> ring
def hiConstant (b : Band) (d : Rectangle) (T L : ℕ) : ℤ :=
 12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    WY (cutoff b d) d.s-WY (cutoff b d-d.lo) (d.s-b.R))
def tanConstant (b : Band) (d : Rectangle) (T L : ℕ) : ℤ :=
 12*((countSlope (cutoff b d) d.s+
        (tanK b d : ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
        countSlope (tanE b d) (d.s-b.R))*L+
      countSlope (tanE b d) (d.s-b.R)*T+
      WY (cutoff b d) d.s+
        (tanK b d : ℤ)*(WY (cutoff b d+1) d.s-WY (cutoff b d) d.s)-
      WY (tanE b d) (d.s-b.R))
def margin (c : ℤ) (b : Band) (d : Rectangle) (T L : ℕ) : Cubic :=
 let p := rank (d.alpha+d.beta) d.beta L d.s
 let q := rank (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩
lemma hi_eq (b : Band) (d : Rectangle) (T L : ℕ) (hL : T≤L) (hR : b.R≤d.s) :
 margin (hiConstant b d T L) b d T L=BDN b d T L := by
 simp only [margin,hiConstant,BDN,rank_eq,Nat.cast_add,Nat.cast_one,Nat.cast_sub hL,Nat.cast_sub hR]
lemma tan_eq (b : Band) (d : Rectangle) (T L : ℕ) (hL : T≤L) (hR : b.R≤d.s) :
 margin (tanConstant b d T L) b d T L=APE b d T L := by
 simp only [margin,tanConstant,APE,rank_eq,Nat.cast_add,Nat.cast_one,Nat.cast_sub hL,Nat.cast_sub hR]
end NatRankWide80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace NatPoly80909
open LD AP AN AI NatWideKernel80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
structure Poly where
 c0:Diff
 c1:Diff
 c2:Diff
 c3:Diff
def polyValue (p:Poly):Cubic:=⟨value p.c0,value p.c1,value p.c2,value p.c3⟩
def rank (base rate L s : ℕ) : Poly :=
 let p0 : ℕ := s*(s+1)*((4*s+2)*L+5*s+2)+2*(s+1)*(3*L+4)*base+6*(L+1)*(s+1)*base^2
 let n0 : ℕ := s*(s+1)*s^2+2*(s+1)*(3*L*s+6*s)*base+2*(s+1)*base^3
 let p1 : ℕ := rate*(2*(s+1)*(3*L*s+6*s)+6*(s+1)*base^2)
 let n1 : ℕ := rate*(2*(s+1)*(3*L+4)+12*(L+1)*(s+1)*base)
 let p2 : ℕ := rate^2*6*(L+1)*(s+1)
 let n2 : ℕ := rate^2*6*(s+1)*base
 let p3 : ℕ := 2*(s+1)*rate^3
 ⟨⟨p0,n0⟩,⟨p1,n1⟩,⟨p2,n2⟩,⟨p3,0⟩⟩
lemma rank_eq (base rate L s:ℕ):polyValue (rank base rate L s)=NatRankWide80909.rank base rate L s:=by
 simp only [polyValue,rank,NatRankWide80909.rank,value]
 rfl
def counts (D s:ℕ):Diff:=⟨ECJ (D/131071) (D%131071) 131071 s,0⟩
lemma counts_eq (D s:ℕ):value (counts D s)=countSlope D s:=by simp [counts,value,countSlope]
def intercept (q r w s:ℕ):Diff:=⟨LocatorFastKernelArithmetic.oneResidueCoefficientCount q r w q s,oneSlope q r w s*q⟩
def base (D s:ℕ):Diff:=
 let q:=D/131071
 let r:=D%131071
 if r+s≤131071 then intercept q r 131071 s else
 sub (add (intercept q r 131071 (131071-r-1)) (intercept (q+1-(131071-r)) 0 131071 (s-(131071-r))))
  ⟨oneSlope (q+1-(131071-r)) 0 131071 (s-(131071-r))*(131071-r),0⟩
lemma base_eq (D s:ℕ):value (base D s)=WY D s:=by
 dsimp only [base,WY,CSW]
 split_ifs with h <;> simp only [h,ite_true,ite_false,intercept,sub,add,value,oneIntercept,Nat.cast_mul,Nat.cast_add,Nat.cast_zero,sub_zero,Nat.cast_sub (show D%131071≤131071 from Nat.le_of_lt (Nat.mod_lt _ (by decide)))] <;> ring
def hiConstant (b:Band)(d:Rectangle)(T L:ℕ):Diff:=
 let D:=cutoff b d
 let E:=D-d.lo
 scale 12 (add (add (scale L (sub (counts D d.s) (counts E (d.s-b.R))))
  (scale T (counts E (d.s-b.R)))) (sub (base D d.s) (base E (d.s-b.R))))
lemma hi_eq (b:Band)(d:Rectangle)(T L:ℕ):value (hiConstant b d T L)=NatRankWide80909.hiConstant b d T L:=by
 simp only [hiConstant,scale_eq,add_eq,sub_eq,counts_eq,base_eq,NatRankWide80909.hiConstant]
 ring
def tanConstant (b:Band)(d:Rectangle)(T L:ℕ):Diff:=
 let D:=cutoff b d
 let E:=tanE b d
 let K:=tanK b d
 scale 12 (add (add (scale L (sub (add (counts D d.s) (scale K (sub (counts (D+1) d.s) (counts D d.s)))) (counts E (d.s-b.R))))
  (scale T (counts E (d.s-b.R)))) (sub (add (base D d.s) (scale K (sub (base (D+1) d.s) (base D d.s)))) (base E (d.s-b.R))))
lemma tan_eq (b:Band)(d:Rectangle)(T L:ℕ):value (tanConstant b d T L)=NatRankWide80909.tanConstant b d T L:=by
 simp only [tanConstant,scale_eq,add_eq,sub_eq,counts_eq,base_eq,NatRankWide80909.tanConstant]
 ring
def margin (c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):Poly:=
 let p:=rank (d.alpha+d.beta) d.beta L d.s
 let q:=rank (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 ⟨sub c (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),
  scale 262144 (sub q.c2 p.c2),scale 262144 (sub q.c3 p.c3)⟩
lemma margin_eq (c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):
 polyValue (margin c b d T L)=NatRankWide80909.margin (value c) b d T L:=by
 have hp:=rank_eq (d.alpha+d.beta) d.beta L d.s
 have hq:=rank_eq (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 simp only [NatRankWide80909.margin,←hp,←hq,margin,polyValue,sub_eq,scale_eq]
 congr 1 <;> ring
def eval (p:Poly) (x:ℕ):Diff:=add  (scale x  (add  (scale x  (add  (scale x  (p.c3))  (p.c2)))  (p.c1)))  (p.c0)
def deriv (p:Poly) (x:ℕ):Diff:=add  (scale x  (add  (scale  (3*x)  (p.c3))  (scale 2  (p.c2))))  (p.c1)
lemma eval_eq (p:Poly) (x:ℕ):value (eval p x)=(polyValue p).eval x:=by
 simp only [eval,add_eq,scale_eq,ofInt_eq,Cubic.eval,polyValue]
 ring
lemma deriv_eq (p:Poly) (x:ℕ):value (deriv p x)=(polyValue p).deriv x:=by
 simp only [deriv,add_eq,scale_eq,ofInt_eq,Cubic.deriv,polyValue,Nat.cast_mul,Nat.cast_ofNat]
 ring
def mid1 (p:Poly) (a b:ℕ):Diff:=add  (scale 3  (eval p a))  (scale  (b-a)  (deriv p a))
def mid2 (p:Poly) (a b:ℕ):Diff:=sub  (scale 3  (eval p b))  (scale  (b-a)  (deriv p b))
def NatCheck (p:Poly) (a b:ℕ):Prop:=b<a ∨
  (eval p a).neg< (eval p a).pos ∧  (eval p b).neg< (eval p b).pos ∧
  (mid1 p a b).neg≤ (mid1 p a b).pos ∧  (mid2 p a b).neg≤ (mid2 p a b).pos
instance (p:Poly) (a b:ℕ):Decidable (NatCheck p a b):=by unfold NatCheck;infer_instance
lemma check_iff (p:Poly) (a b:ℕ):NatCheck p a b↔(polyValue p).Check a b:=by
 by_cases h:b<a
 · simp only [NatCheck,Cubic.Check,h,true_or]
 · have hab:a≤b:=by omega
   have hw: ( (b-a:ℕ):ℤ)= (b:ℤ)-a:=Int.ofNat_sub hab
   have h1:value (mid1 p a b)=3*(polyValue p).eval a+ ( (b:ℤ)-a)*(polyValue p).deriv a:=by
    simp only [mid1,add_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   have h2:value (mid2 p a b)=3*(polyValue p).eval b- ( (b:ℤ)-a)*(polyValue p).deriv b:=by
    simp only [mid2,sub_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   simp only [NatCheck,Cubic.Check,h,false_or]
   rw [←pos_iff,←pos_iff,←nonneg_iff,←nonneg_iff,eval_eq,eval_eq,h1,h2]
def hiDec (b:Band)(d:Rectangle)(T L a z:ℕ):Decidable ((BDN b d T L).Check a z):=
 if h:T≤L ∧ b.R≤d.s then decidable_of_iff (NatCheck (margin (hiConstant b d T L) b d T L) a z)
  (by rw [check_iff,margin_eq,hi_eq,NatRankWide80909.hi_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] hiDec
def tanDec (b:Band)(d:Rectangle)(T L a z:ℕ):Decidable ((APE b d T L).Check a z):=
 if h:T≤L ∧ b.R≤d.s then decidable_of_iff (NatCheck (margin (tanConstant b d T L) b d T L) a z)
  (by rw [check_iff,margin_eq,tan_eq,NatRankWide80909.tan_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] tanDec
def cornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by unfold corners;infer_instance
attribute [local instance] cornersDec
def rowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by unfold FastRows;infer_instance
attribute [local instance] rowsDec
def tanCornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by unfold tanCorners;infer_instance
end NatPoly80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace NatRows80909
open LD AP AN AI NatWideKernel80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def rankSlopeN (m s:ℕ):Diff:=
 let u:=min s (m/2)
 let K:=(s+1)*m*(m+1)
 let p0:=(m+1)*(s+1)
 let P:=m+2*s+3
 ⟨6*K+6*P*u*(u+1),12*p0*u+4*u*(u+1)*(2*u+1)⟩
def rankBaseN (m s:ℕ):Diff:=
 let u:=min s (m/2)
 let K:=(s+1)*m*(m+1)
 let p0:=(m+1)*(s+1)
 let P:=m+2*s+3
 let C:Diff:=⟨2,m+s⟩
 sub ⟨8*K,K*(2*m+3*s)⟩
  (add (add (scale (6*p0*u) C) (scale (3*u*(u+1)) (sub ⟨p0,0⟩ (scale P C))))
   (add (scale (u*(u+1)*(2*u+1)) (sub (scale 2 C) ⟨P,0⟩)) ⟨3*u*u*(u+1)*(u+1),0⟩))
def rankAffineN (m s L:ℕ):Diff:=add (scale L (rankSlopeN m s)) (rankBaseN m s)
lemma rankAffine_eq (m s L:ℕ):value (rankAffineN m s L)=rankAffine m s L:=by
 simp only [rankAffineN,rankSlopeN,rankBaseN,add,sub,scale,value,rankAffine,ClosedRank.sourceTwelve,ClosedRank.removedPartialTwelve,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,sub_zero]
 ring
lemma rankSlope_eq (m s:ℕ):value (rankSlopeN m s)=rankSlope m s:=by
 have h1:=rankAffine_eq m s 1
 have h0:=rankAffine_eq m s 0
 simp only [Nat.cast_one,Nat.cast_zero] at h1 h0
 unfold rankSlope
 rw [←h1,←h0]
 simp only [rankAffineN,add_eq,scale_eq,Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,zero_add]
 ring
lemma rankBase_eq (m s:ℕ):value (rankBaseN m s)=CPJ m s:=by
 have h0:=rankAffine_eq m s 0
 simp only [Nat.cast_zero] at h0
 unfold CPJ
 rw [←h0]
 simp only [rankAffineN,add_eq,scale_eq,Nat.cast_zero,zero_mul,zero_add]
def rowA (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (NatPoly80909.counts D s) (NatPoly80909.counts (D-nu) (s-R))))
  (scale 262144 (sub (rankSlopeN m s) (rankSlopeN (m-mu) (s-R))))
def rowB (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (NatPoly80909.counts (D-nu) (s-R))) (scale 262144 (rankSlopeN (m-mu) (s-R)))
def rowC (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (NatPoly80909.base D s) (NatPoly80909.base (D-nu) (s-R))))
  (scale 262144 (sub (rankBaseN m s) (rankBaseN (m-mu) (s-R))))
lemma rowA_eq (D nu s R m mu:ℕ):value (rowA D nu s R m mu)=marginA D nu s R m mu:=by
 simp only [rowA,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,marginA];ring
lemma rowB_eq (D nu s R m mu:ℕ):value (rowB D nu s R m mu)=marginB D nu s R m mu:=by
 simp only [rowB,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,marginB];ring
lemma rowC_eq (D nu s R m mu:ℕ):value (rowC D nu s R m mu)=marginC D nu s R m mu:=by
 simp only [rowC,sub_eq,scale_eq,NatPoly80909.base_eq,rankBase_eq,marginC];ring
def tanA (D k E s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (add (NatPoly80909.counts D s) (scale k (sub (NatPoly80909.counts (D+1) s) (NatPoly80909.counts D s)))) (NatPoly80909.counts E (s-R))))
  (scale 262144 (sub (rankSlopeN m s) (rankSlopeN (m-mu) (s-R))))
def tanB (E s R m mu:ℕ):Diff:=
 sub (scale 12 (NatPoly80909.counts E (s-R))) (scale 262144 (rankSlopeN (m-mu) (s-R)))
def tanC (D k E s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (add (NatPoly80909.base D s) (scale k (sub (NatPoly80909.base (D+1) s) (NatPoly80909.base D s)))) (NatPoly80909.base E (s-R))))
  (scale 262144 (sub (rankBaseN m s) (rankBaseN (m-mu) (s-R))))
lemma tanA_eq (D k E s R m mu:ℕ):value (tanA D k E s R m mu)=tanMarginA D k E s R m mu:=by
 simp only [tanA,sub_eq,add_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,tanMarginA];ring
lemma tanB_eq (E s R m mu:ℕ):value (tanB E s R m mu)=tanMarginB E s R m mu:=by
 simp only [tanB,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,tanMarginB];ring
lemma tanC_eq (D k E s R m mu:ℕ):value (tanC D k E s R m mu)=tanMarginC D k E s R m mu:=by
 simp only [tanC,sub_eq,add_eq,scale_eq,NatPoly80909.base_eq,rankBase_eq,tanMarginC];ring
def testAt (a b c:Diff)(T L:ℕ):Prop:=
 let f:=add (add (scale L a) (scale T b)) c
 let g:=add a f
 f.neg<f.pos ∧ g.neg<g.pos
instance (a b c:Diff)(T L:ℕ):Decidable (testAt a b c T L):=by unfold testAt;infer_instance
lemma testAt_iff (a b c:Diff)(T L:ℕ):testAt a b c T L ↔ max 0 (-value a)<value a*L+value b*T+value c:=by
 dsimp only [testAt]
 rw [←pos_iff,←pos_iff]
 simp only [add_eq,scale_eq,mul_comm]
 omega
def RowN (b:Band)(d:Rectangle)(mu:ℕ):Prop:=
 let m:=d.alpha-d.beta*(mu-1)
 let a:=rowA (cutoff b d) d.lo d.s b.R m mu
 let v:=rowB (cutoff b d) d.lo d.s b.R m mu
 let c:=rowC (cutoff b d) d.lo d.s b.R m mu
 testAt a v c b.T0 d.L0 ∧ testAt a v c b.T1 d.L1
instance (b:Band)(d:Rectangle)(mu:ℕ):Decidable (RowN b d mu):=by unfold RowN;infer_instance
lemma row_iff (b:Band)(d:Rectangle)(mu:ℕ):RowN b d mu ↔ rowGood b d mu:=by
 simp only [RowN,testAt_iff,rowA_eq,rowB_eq,rowC_eq,rowGood]
def rowDec (b:Band)(d:Rectangle)(mu:ℕ):Decidable (rowGood b d mu):=decidable_of_iff (RowN b d mu) (row_iff b d mu)
attribute [local instance] rowDec
def TanRowN (b:Band)(d:Rectangle)(mu:ℕ):Prop:=
 let m:=d.alpha-d.beta*(mu-1)
 let a:=tanA (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
 let v:=tanB (tanE b d) d.s b.R m mu
 let c:=tanC (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
 testAt a v c b.T0 d.L0 ∧ testAt a v c b.T1 d.L1
instance (b:Band)(d:Rectangle)(mu:ℕ):Decidable (TanRowN b d mu):=by unfold TanRowN;infer_instance
lemma tanRow_iff (b:Band)(d:Rectangle)(mu:ℕ):TanRowN b d mu ↔ tanRowGood b d mu:=by
 simp only [TanRowN,testAt_iff,tanA_eq,tanB_eq,tanC_eq,tanRowGood]
def tanRowDec (b:Band)(d:Rectangle)(mu:ℕ):Decidable (tanRowGood b d mu):=decidable_of_iff (TanRowN b d mu) (tanRow_iff b d mu)
attribute [local instance] tanRowDec
lemma decide_irrel (p:Prop)(a b:Decidable p):@decide p a=@decide p b:=congrArg (fun d=>@decide p d) (Subsingleton.elim a b)
def range (b:Band)(d:Rectangle)(start:ℕ):ℕ→Bool
 | 0=>true
 | n+1=>range b d start n && decide (rowGood b d (start+n))
lemma range_eq (b:Band)(d:Rectangle)(start n:ℕ):range b d start n=checkRange b d start n:=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [range,checkRange,ih];congr 1;exact decide_irrel _ _ _
def tanRange (b:Band)(d:Rectangle)(start:ℕ):ℕ→Bool
 | 0=>true
 | n+1=>tanRange b d start n && decide (tanRowGood b d (start+n))
lemma tanRange_eq (b:Band)(d:Rectangle)(start n:ℕ):tanRange b d start n=DSU b d start n:=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [tanRange,DSU,ih];congr 1;exact decide_irrel _ _ _
attribute [local instance] NatPoly80909.cornersDec NatPoly80909.tanCornersDec
def FastRowsN (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  corners b d 1 (w.firstExact-1)∧corners b d (w.lastExact+1) w.normalEnd∧
  rowGood b d 0∧range b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  range b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true
instance (b:Band)(d:Rectangle)(w:FastWitness):Decidable (FastRowsN b d w):=by unfold FastRowsN;infer_instance
lemma FastRows_iff (b:Band)(d:Rectangle)(w:FastWitness):FastRowsN b d w ↔ FastRows b d w:=by
 simp only [FastRowsN,FastRows,range_eq,tanRange_eq]
def rowsDec (b:Band)(d:Rectangle)(w:FastWitness):Decidable (FastRows b d w):=decidable_of_iff (FastRowsN b d w) (FastRows_iff b d w)
attribute [local instance] rowsDec
def TanFastRowsN (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  tanCorners b d 1 (w.firstExact-1)∧tanCorners b d (w.lastExact+1) w.normalEnd∧
  tanRowGood b d 0∧tanRange b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  tanRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true
instance (b:Band)(d:Rectangle)(w:FastWitness):Decidable (TanFastRowsN b d w):=by unfold TanFastRowsN;infer_instance
end NatRows80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace MonotoneCheck80909
open AP NatWideKernel80909 NatPoly80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def curv(p:Poly)(x:ℕ):Diff:=add p.c2 (scale (3*x) p.c3)
lemma curv_eq(p:Poly)(x:ℕ):value (curv p x)=value p.c2+3*value p.c3*x:=by
 simp only [curv,add_eq,scale_eq,Nat.cast_mul,Nat.cast_ofNat];ring
def positive(p:Poly)(a b:ℕ):Bool:=
 if a=1 then
  let c:=curv p b
  let d:=NatPoly80909.deriv p b
  Nat.ble c.neg c.pos && Nat.ble d.pos d.neg
 else
  let c:=curv p a
  let d:=NatPoly80909.deriv p a
  Nat.ble c.neg c.pos && Nat.ble d.neg d.pos
lemma middle_of_positive(p:Poly)(a b:ℕ)(hab:a≤b)
 (ha:0<value (NatPoly80909.eval p a))(hb:0<value (NatPoly80909.eval p b))
 (hc:positive p a b=true):0≤value (NatPoly80909.mid1 p a b) ∧ 0≤value (NatPoly80909.mid2 p a b):=by
 have hsub:((b-a:ℕ):ℤ)=(b:ℤ)-a:=Int.ofNat_sub hab
 have hab':(a:ℤ)≤b:=by exact_mod_cast hab
 have hh:0≤(b:ℤ)-a:=by omega
 unfold positive at hc
 by_cases h:a=1
 · simp only [h,ite_true,Bool.and_eq_true,Nat.ble_eq] at hc
   have cv:0≤value (curv p b):=by unfold value;omega
   have dv:value (NatPoly80909.deriv p b)≤0:=by unfold value;omega
   have hm:=mul_nonpos_of_nonneg_of_nonpos hh dv
   have hs:=mul_nonneg (sq_nonneg ((b:ℤ)-a)) cv
   have he:value (NatPoly80909.mid1 p a b)=3*value (NatPoly80909.eval p b)-2*((b:ℤ)-a)*value (NatPoly80909.deriv p b)+((b:ℤ)-a)^2*value (curv p b):=by
    simp only [NatPoly80909.mid1,add_eq,scale_eq,NatPoly80909.eval_eq,NatPoly80909.deriv_eq,hsub,Nat.cast_ofNat,curv_eq,Cubic.eval,Cubic.deriv,polyValue]
    ring
   rw [he]
   simp only [NatPoly80909.mid2,sub_eq,scale_eq,hsub,Nat.cast_ofNat]
   constructor <;> nlinarith
 · simp only [h,ite_false,Bool.and_eq_true,Nat.ble_eq] at hc
   have cv:0≤value (curv p a):=by unfold value;omega
   have dv:0≤value (NatPoly80909.deriv p a):=by unfold value;omega
   have hm:=mul_nonneg hh dv
   have hs:=mul_nonneg (sq_nonneg ((b:ℤ)-a)) cv
   have he:value (NatPoly80909.mid2 p a b)=3*value (NatPoly80909.eval p a)+2*((b:ℤ)-a)*value (NatPoly80909.deriv p a)+((b:ℤ)-a)^2*value (curv p a):=by
    simp only [NatPoly80909.mid2,sub_eq,scale_eq,NatPoly80909.eval_eq,NatPoly80909.deriv_eq,hsub,Nat.cast_ofNat,curv_eq,Cubic.eval,Cubic.deriv,polyValue]
    ring
   rw [he]
   simp only [NatPoly80909.mid1,add_eq,scale_eq,hsub,Nat.cast_ofNat]
   constructor <;> nlinarith
def Check(p:Poly)(a b:ℕ):Prop:=b<a ∨
 (eval p a).neg<(eval p a).pos ∧ (eval p b).neg<(eval p b).pos ∧
 (positive p a b=true ∨ (mid1 p a b).neg≤(mid1 p a b).pos ∧ (mid2 p a b).neg≤(mid2 p a b).pos)
instance(p:Poly)(a b:ℕ):Decidable (Check p a b):=by unfold Check;infer_instance
lemma check_iff(p:Poly)(a b:ℕ):Check p a b↔NatPoly80909.NatCheck p a b:=by
 by_cases h:b<a
 · simp only [Check,NatPoly80909.NatCheck,h,true_or]
 · have hab:a≤b:=by omega
   simp only [Check,NatPoly80909.NatCheck,h,false_or]
   constructor
   · rintro ⟨ha,hb,hc⟩
     refine ⟨ha,hb,?_⟩
     rcases hc with hc|hc
     · have hh:=middle_of_positive p a b hab ((pos_iff _).mpr ha) ((pos_iff _).mpr hb) hc
       exact ⟨(nonneg_iff _).mp hh.1,(nonneg_iff _).mp hh.2⟩
     · exact hc
   · rintro ⟨ha,hb,hc⟩
     exact ⟨ha,hb,Or.inr hc⟩
end MonotoneCheck80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace MonotoneBoolCheck80909
open NatPoly80909
set_option autoImplicit false
def check(p:Poly)(a b:ℕ):Bool:=
 Nat.blt b a || (Nat.blt (eval p a).neg (eval p a).pos &&
 (Nat.blt (eval p b).neg (eval p b).pos &&
 (MonotoneCheck80909.positive p a b ||
 (Nat.ble (mid1 p a b).neg (mid1 p a b).pos && Nat.ble (mid2 p a b).neg (mid2 p a b).pos))))
lemma check_iff(p:Poly)(a b:ℕ):check p a b=true ↔ NatCheck p a b:=by
 rw [←MonotoneCheck80909.check_iff]
 simp only [check,MonotoneCheck80909.Check,Bool.or_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq]
def checkDec(p:Poly)(a b:ℕ):Decidable (NatCheck p a b):=
 decidable_of_iff (check p a b=true) (check_iff p a b)
end MonotoneBoolCheck80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace PairedBool80909
open AI AP AN LD NatWideKernel80909 NatPoly80909
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local instance] MonotoneBoolCheck80909.checkDec
def addP(p q:Poly):Poly:=⟨add p.c0 q.c0,add p.c1 q.c1,add p.c2 q.c2,add p.c3 q.c3⟩
def rankSlopeP(base rate s:ℕ):Poly:=
 ⟨⟨s*(s+1)*(4*s+2)+6*(s+1)*base+6*(s+1)*base^2,6*s*(s+1)*base⟩,
 ⟨rate*6*s*(s+1),rate*(6*(s+1)+12*(s+1)*base)⟩,
 ⟨rate^2*6*(s+1),0⟩,⟨0,0⟩⟩
def delta(c:Diff)(b:Band)(d:Rectangle):Poly:=
 let p:=rankSlopeP (d.alpha+d.beta) d.beta d.s
 let q:=rankSlopeP (d.alpha+d.beta) (d.beta+1) (d.s-b.R)
 ⟨sub c (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),
  scale 262144 (sub q.c2 p.c2),⟨0,0⟩⟩
def hiDelta(b:Band)(d:Rectangle):Poly:=delta (scale 12 (sub (counts (cutoff b d) d.s) (counts (cutoff b d-d.lo) (d.s-b.R)))) b d
def tanDelta(b:Band)(d:Rectangle):Poly:=
 let D:=cutoff b d
 delta (scale 12 (sub (add (counts D d.s) (scale (tanK b d) (sub (counts (D+1) d.s) (counts D d.s)))) (counts (tanE b d) (d.s-b.R)))) b d
lemma hi_step(b:Band)(d:Rectangle)(T L:ℕ)(h:T≤L):
 polyValue (addP (margin (hiConstant b d T L) b d T L) (hiDelta b d))=
 polyValue (margin (hiConstant b d T (L+1)) b d T (L+1)):=by
 have hh:L+1-T=(L-T)+1:=by omega
 simp only [polyValue,addP,margin,hiDelta,delta,rankSlopeP,NatPoly80909.rank,hiConstant,hh,
  NatWideKernel80909.add,NatWideKernel80909.sub,NatWideKernel80909.scale,value,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero,sub_zero]
 congr 1 <;> ring
def hiFast(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin (hiConstant b d b.T0 d.L0) b d b.T0 d.L0
 let q:=margin (hiConstant b d b.T1 d.L1) b d b.T1 d.L1
 let r:=hiDelta b d
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(b:Band)(d:Rectangle)(a z:ℕ):Decidable (hiFast b d a z):=by unfold hiFast;infer_instance
lemma hiFast_iff(b:Band)(d:Rectangle)(a z:ℕ)(h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s):
 hiFast b d a z ↔ corners b d a z:=by
 simp only [hiFast,NatPoly80909.check_iff,hi_step b d b.T0 d.L0 h.1,hi_step b d b.T1 d.L1 h.2.1,
  NatPoly80909.margin_eq,NatPoly80909.hi_eq]
 rw [NatRankWide80909.hi_eq b d b.T0 d.L0 h.1 h.2.2,
  NatRankWide80909.hi_eq b d b.T0 (d.L0+1) (by omega) h.2.2,
  NatRankWide80909.hi_eq b d b.T1 d.L1 h.2.1 h.2.2,
  NatRankWide80909.hi_eq b d b.T1 (d.L1+1) (by omega) h.2.2]
 rfl
def hiDec(b:Band)(d:Rectangle)(a z:ℕ):Decidable (corners b d a z):=
 if h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s then decidable_of_iff (hiFast b d a z) (hiFast_iff b d a z h)
 else NatPoly80909.cornersDec b d a z
attribute [local instance] hiDec
def tanFast(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin (tanConstant b d b.T0 d.L0) b d b.T0 d.L0
 let q:=margin (tanConstant b d b.T1 d.L1) b d b.T1 d.L1
 let r:=tanDelta b d
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(b:Band)(d:Rectangle)(a z:ℕ):Decidable (tanFast b d a z):=by unfold tanFast;infer_instance
end PairedBool80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AffineRank80909
open AI AP AN NatWideKernel80909 NatPoly80909 PairedBool80909
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def scaleP (k:ℕ)(p:Poly):Poly:=⟨scale k p.c0,scale k p.c1,scale k p.c2,scale k p.c3⟩
end AffineRank80909
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ProfileCached6816
open AI AP AN LD NatWideKernel80909 NatPoly80909 PairedBool80909
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local instance] MonotoneBoolCheck80909.checkDec
structure Parts(base rate s:ℕ) where
 zero:Poly
 slope:Poly
 hz:zero=NatPoly80909.rank base rate 0 s
 hs:slope=rankSlopeP base rate s
structure CachedProfile where
 p:Profile
 high:Parts (p.alpha+p.beta) p.beta p.s
 low:(R:ℕ)→Parts (p.alpha+p.beta) (p.beta+1) (p.s-R)
def fromParts{base rate s:ℕ}(p:Parts base rate s)(L:ℕ):Poly:=addP p.zero (AffineRank80909.scaleP L p.slope)
def margin(c:CachedProfile)(v:Diff)(b:Band)(T L:ℕ):Poly:=
 let p:=fromParts c.high L
 let q:=fromParts (c.low b.R) (L-T)
 ⟨sub v (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),scale 262144 (sub q.c2 p.c2),scale 262144 (sub q.c3 p.c3)⟩
def delta(c:CachedProfile)(v:Diff)(b:Band):Poly:=
 let p:=c.high.slope
 let q:=(c.low b.R).slope
 ⟨sub v (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),scale 262144 (sub q.c2 p.c2),⟨0,0⟩⟩
def hiFast(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin c (hiConstant b d b.T0 d.L0) b b.T0 d.L0
 let q:=margin c (hiConstant b d b.T1 d.L1) b b.T1 d.L1
 let r:=delta c (scale 12 (sub (counts (cutoff b d) d.s) (counts (cutoff b d-d.lo) (d.s-b.R)))) b
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Decidable (hiFast c b d a z):=by unfold hiFast;infer_instance
def tanFast(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin c (tanConstant b d b.T0 d.L0) b b.T0 d.L0
 let q:=margin c (tanConstant b d b.T1 d.L1) b b.T1 d.L1
 let r:=delta c (scale 12 (sub (add (counts (cutoff b d) d.s) (scale (tanK b d) (sub (counts (cutoff b d+1) d.s) (counts (cutoff b d) d.s)))) (counts (tanE b d) (d.s-b.R)))) b
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Decidable (tanFast c b d a z):=by unfold tanFast;infer_instance
instance headerDec(b:Band)(d:Rectangle):Decidable (WideHeader b d):=by unfold WideHeader;infer_instance
end ProfileCached6816
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
namespace ProximityPrize
namespace SubmissionLower
namespace WideBits6816
open AI LD
set_option autoImplicit false
set_option maxRecDepth 100000
def field(code off bits:ℕ):ℕ:=Nat.land (Nat.shiftRight code off) (2^bits-1)
def aux(layout:ℕ):ℕ→ℕ→List WideEntry
 | 0,_=>[]
 | n+1,code=>
  let b0:=field layout 0 5
  let b1:=field layout 5 5
  let b2:=field layout 10 5
  let b3:=field layout 15 5
  let b4:=field layout 20 5
  let b5:=field layout 25 5
  let b6:=field layout 30 5
  let b7:=field layout 35 5
  let b8:=field layout 40 5
  let o0:=0
  let o1:=o0+b0
  let o2:=o1+b1
  let o3:=o2+b2
  let o4:=o3+b3
  let o5:=o4+b4
  let o6:=o5+b5
  let o7:=o6+b6
  let o8:=o7+b7
  let o9:=o8+b8
  let v0:=field code o0 b0
  let v1:=field code o1 b1
  let v2:=field code o2 b2
  let v3:=field code o3 b3
  let v4:=field code o4 b4
  let v5:=field code o5 b5
  let v6:=field code o6 b6
  let v7:=field code o7 b7
  let v8:=field code o8 b8
  ⟨v0,v1,v2,v3,⟨v4,v5,v5+v6⟩,⟨v4,v7,v7+v8⟩⟩::aux layout n (Nat.shiftRight code o9)
def data(layout n code:ℕ):List WideEntry:=aux layout n code
end WideBits6816
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
abbrev WB:=WideBits6816.data
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart3
namespace AID
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
variable {E:Type*} [Field E]
theorem DOQ (j:Polynomial E) (t:E) (e:ℕ)
    (hj:j ≠ 0):(j^e).rootMultiplicity t=e*j.rootMultiplicity t:=by
  induction e with
  | zero=>simp
  | succ e ih=>
    rw [pow_succ,Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hj) hj),ih]
    ring
open RCN095
open RCN095 renaming PolynomialInFlag → BI
end
end AID
end MergedPart3
section MergedPart5
namespace CW
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial
variable {K:Type*} [Field K]
def weightEmbed (w:Fin 5→ℕ):(Fin 5→₀ ℕ)→+(Fin 6→₀ ℕ) where
  toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
    Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+Finsupp.single 4 (d 4)+
    Finsupp.single 5 (Finsupp.weight w d)
  map_zero' :=by simp
  map_add' d e:=by ext i;fin_cases i<;>simp [Finsupp.add_apply,map_add]
theorem FWO (w:Fin 5→ℕ) (d:Fin 5→₀ ℕ) (i:Fin 5):
    weightEmbed w d i.castSucc=d i:=by
  fin_cases i<;>simp [weightEmbed]
theorem AJC (w:Fin 5→ℕ):Function.Injective (weightEmbed w):=by
  intro d e h
  ext i
  simpa only [FWO] using congrArg (fun x:Fin 6→₀ ℕ=>x i.castSucc) h
def weightedLift (w:Fin 5→ℕ):SecondJetSupport.Poly (K:=K)→+*MvPolynomial (Fin 6) K:=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed w)
theorem CCQ (w:Fin 5→ℕ):Function.Injective (weightedLift (K:=K) w):=
  AddMonoidAlgebra.mapDomain_injective (AJC w)
theorem DFM (w:Fin 5→ℕ) (P:SecondJetSupport.Poly (K:=K)):
    (weightedLift w P).degreeOf 5=weightedTotalDegree w P:=by
  have hs:(weightedLift w P).support=P.support.image (weightEmbed w):=
    Finsupp.mapDomain_support_of_injective (AJC w) _
  rw [degreeOf_eq_sup,hs,Finset.sup_image]
  change P.support.sup (fun d=>weightEmbed w d 5)=P.support.sup (Finsupp.weight w)
  congr 1
  funext d
  simp [weightEmbed]
theorem weight_mul (w:Fin 5→ℕ) (P Q:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (hQ:Q≠0):
    weightedTotalDegree w (P*Q)=weightedTotalDegree w P+weightedTotalDegree w Q:=by
  have hn (A:SecondJetSupport.Poly (K:=K)) (hA:A≠0):weightedLift w A ≠ 0:=by
    intro hz
    apply hA
    exact CCQ w (by simpa only [map_zero] using hz)
  rw [←DFM,map_mul,degreeOf_mul_eq (hn P hP) (hn Q hQ),
    DFM,DFM]
theorem weight_pow (w:Fin 5→ℕ) (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (n:ℕ):
    weightedTotalDegree w (P^n)=n*weightedTotalDegree w P:=by
  induction n with
  | zero=>simp [weightedTotalDegree]
  | succ n ih=>
    rw [pow_succ,weight_mul w _ _ (pow_ne_zero _ hP) hP,ih]
    ring
def codeWeights:Fin 5→ℕ:= ![1,131069,131071,131070,0]
def HA:Fin 5→ℕ:= ![0,1,1,1,0]
theorem JW (w:Fin 5→ℕ) (e:Fin 5→₀ ℕ):
    Finsupp.weight w e=e 0*w 0+e 1*w 1+e 2*w 2+e 3*w 3+e 4*w 4:=by
  have he:e=Finsupp.single 0 (e 0)+Finsupp.single 1 (e 1)+
      Finsupp.single 2 (e 2)+Finsupp.single 3 (e 3)+Finsupp.single 4 (e 4):=by
    ext i;fin_cases i<;>simp
  rw [he,map_add,map_add,map_add,map_add]
  simp [Finsupp.weight_single]
theorem ARN {W I:Type*} [AddCommGroup W] [Module K W]
    [Fintype I] (e:I→Fin 5→₀ ℕ) (f:W→ₗ[K] SecondJetSupport.Poly (K:=K))
    (hf:Function.Injective f)
    (hs: ∀v:W,∀d ∈ (f v).support,d ∈ Set.range e):
    Module.finrank K W≤Fintype.card I:=by
  let A:W→ₗ[K] (I→K):=LinearMap.pi (fun i=>(MvPolynomial.lcoeff K (e i)).comp f)
  have hi:Function.Injective A:=by
    intro v u h
    apply hf
    ext d
    have hh (i:I):(f v).coeff (e i)=(f u).coeff (e i):=congrFun h i
    by_cases hv:d ∈ (f v).support
    · obtain ⟨i,rfl⟩:=hs v d hv
      exact hh i
    by_cases hu:d ∈ (f u).support
    · obtain ⟨i,rfl⟩:=hs u d hu
      exact hh i
    rw [MvPolynomial.notMem_support_iff.mp hv,MvPolynomial.notMem_support_iff.mp hu]
  simpa using LinearMap.finrank_le_finrank_of_injective hi
end
end CW
end MergedPart5
section MergedPart6
namespace DJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial CW
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
variable {K:Type*} [Field K]
def slopeWeights:Fin 5→ℕ:= ![0,2,0,1,0]
open RCN095 AID
open RCN095 renaming PolynomialInFlag → BI
end
end DJ
end MergedPart6
section MergedPart8
namespace ARW
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open scoped BigOperators
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open DLW (APX)
variable {K N I:Type*} [Field K] [Fintype N] [Fintype I]
theorem FAY
    (e:I→Fin 5→₀ ℕ) (he:Function.Injective e)
    (m L B s U w:ℕ) (D:ℕ→ℕ) (hw:2≤w)
    (hb: ∀i,2*e i 1+e i 3≤B) (hs: ∀i,e i 1≤s)
    (hu: ∀i,e i 1+e i 2+e i 3≤U)
    (hl: ∀i,e i 1+e i 2+e i 3+e i 4≤L)
    (hd: ∀i,e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1<D (e i 1))
    (nodes:N ↪ K) (u0 u1:N→K) (bound:ℕ)
    (hcard:bound+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h=>(D h+B-1)/w)≤Fintype.card I):
    ∃V:Submodule K (SecondJetSupport.Poly (K:=K)),Module.Finite K V∧
      bound≤Module.finrank K V∧
      (∀P ∈ V,∀d ∈ P.support,d ∈ Set.range e)∧
      (∀P ∈ V,∀n,MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K:=K)
        (SecondJetGlobalSupport.localize (nodes n) (u0 n) (u1 n) P)):=by
  classical
  let caps:=fun h=>(D h+B-1)/w
  let f:=AEB.COQ (K:=K) m L B s U caps
  letI:AddCommGroup f.range:=inferInstance
  letI:Module K f.range:=f.range.module
  letI:FiniteDimensional K f.range:=by
    change FiniteDimensional K
      (AEB.COQ (K:=K) m L B s U caps).range
    infer_instance
  let ell (n:N):(I→K)→ₗ[K] ABQ.source (K:=K) m L B s U caps:=
    (APX e m (nodes n) (u0 n) (u1 n)).codRestrict _
      (EG.EAG e m L B s U w D hw
        (nodes n) (u0 n) (u1 n) hb hs hu hl hd)
  let g:(I→K)→ₗ[K] (N→f.range):=
    LinearMap.pi (fun n=>f.rangeRestrict.comp (ell n))
  have htarget:Module.finrank K (N→f.range)≤
      Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U caps:=by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    exact Nat.mul_le_mul_left _
      (EG.EEU m L B s U caps)
  have hrange:=g.range.finrank_le
  have hsum:=g.finrank_range_add_finrank_ker
  have hdimI:Module.finrank K (I→K)=Fintype.card I:=by simp
  have hkernel:bound≤Module.finrank K g.ker:=by
    dsimp only [caps] at htarget
    omega
  let recon:g.ker→ₗ[K] SecondJetSupport.Poly (K:=K):=
    (SC.reconstruct e).comp g.ker.subtype
  have hrecon:Function.Injective recon:=by
    intro a b hh
    apply Subtype.ext
    exact SC.ABR e he hh
  let V:=recon.range
  have hdimV:bound≤Module.finrank K V:=by
    rw [LinearMap.finrank_range_of_inj hrecon]
    exact hkernel
  refine ⟨V,inferInstance,hdimV,?_,?_⟩
  · rintro P ⟨c,rfl⟩
    exact (SC.mem_range_iff e he _).mp ⟨c.val,rfl⟩
  · rintro P ⟨c,rfl⟩ n
    have hc:g c.val=0:=c.property
    have hz:=congrArg Subtype.val (congrFun hc n)
    change SecondJetRank.contactMap (K:=K) m
      (APX e m (nodes n) (u0 n) (u1 n) c.val)=0 at hz
    have hc' :Polynomial.X^m ∣ SecondJetLocal.contact (K:=K)
        (APX e m (nodes n) (u0 n) (u1 n) c.val):=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    have hh:=SecondJetGlobalMap.untruncate_contact (SecondJetLocal.contact (K:=K)).toRingHom
      Polynomial.X m _ SecondJetLocal.contact_X hc'
    exact SecondJetGlobalDifferentiation.nested_to_flat_contact _ m hh
end
end ARW
end MergedPart8
section MergedPart9
namespace TH
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open MvPolynomial RCN095 RCN136 RCN207
open RCN095 renaming PolynomialInFlag → BI
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
section Polynomial
variable {R:Type*} [CommRing R]
def PH (P:Polynomial R) (n:ℕ) (h q:R):Polynomial R:=
  SecondJetClearedHelper.cleared (P.map Polynomial.C) n (Polynomial.C h) (Polynomial.X-Polynomial.C q)
def WE (h q:R):Polynomial R→+*Polynomial R:=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C h*Polynomial.X+Polynomial.C q)
theorem CPW (h q a:R):
    WE h q (Polynomial.C a)=Polynomial.C a:=by
  simp [WE]
theorem BJK (P:Polynomial R) (n:ℕ) (h q:R)
    (hn:P.natDegree≤n):
    WE h q (PH P n h q)=(Polynomial.C h)^n*P:=by
  have hc:(WE h q).comp Polynomial.C=Polynomial.C:=by
    apply RingHom.ext
    intro a
    exact CPW h q a
  rw [PH,SecondJetClearedHelper.map_cleared,Polynomial.map_map,hc]
  simp only [CPW,map_sub]
  have hx:WE h q Polynomial.X-Polynomial.C q=Polynomial.C h*Polynomial.X:=by
    simp [WE]
  rw [hx,SecondJetClearedHelper.cleared_eval (P.map Polynomial.C) n (Polynomial.natDegree_map_le.trans hn)
    (Polynomial.C h) (Polynomial.C h*Polynomial.X) Polynomial.X rfl]
  rw [Polynomial.eval_map,Polynomial.eval₂_C_X]
theorem FAN {S:Type*} [CommRing S] (f:R→+*S)
    (P:Polynomial R) (n:ℕ) (h q:R) (t:S):
    Polynomial.eval₂ f t (PH P n h q)=
      SecondJetClearedHelper.cleared (P.map f) n (f h) (t-f q):=by
  change (Polynomial.eval₂RingHom f t) (PH P n h q)=_
  have hc:(Polynomial.eval₂RingHom f t).comp Polynomial.C=f:=by
    apply RingHom.ext
    intro a
    simp
  rw [PH,SecondJetClearedHelper.map_cleared,Polynomial.map_map]
  rw [hc]
  simp
end Polynomial
section Surface
variable {K E:Type*} [Field K] [Field E]
local notation "Poly3" =>MvPolynomial (Fin 3) E
def coefficients (phi:Polynomial K→+*E) (P:SecondJetSupport.Poly (K:=K)):
    Polynomial Poly3:=(SecondJetCoefficients.asS P).map (surfaceMap phi)
def movingCut (phi:Polynomial K→+*E) (P:SecondJetSupport.Poly (K:=K))
    (s:ℕ) (Q A:Poly3) (target:E):Poly3:=
  SecondJetClearedHelper.cleared (coefficients phi P) s (2*A) (MvPolynomial.C target-Q)
theorem FPY (A:Poly3) (hA:RCN095.PolynomialInFlag unitYZFlag A):
    RCN095.PolynomialInFlag unitYZFlag (2*A):=by
  intro e he
  have he' :e ∈ ((2:E) • A).support:=by
    simpa only [MvPolynomial.smul_eq_C_mul,map_ofNat] using he
  exact hA e (MvPolynomial.support_smul he')
end Surface
end
end TH
end MergedPart9
section MergedPart10
namespace ARX
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open TH
section GCD
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
theorem FWV (a p q d:A) (h:IsRelPrime p q)
    (hp:d ∣ a*p) (hq:d ∣ a*q):d ∣ a:=by
  have hg:IsUnit (gcd p q):=h (gcd_dvd_left p q) (gcd_dvd_right p q)
  have hh:d ∣ a*gcd p q:=(dvd_gcd hp hq).trans (gcd_mul_left' a p q).dvd
  exact hg.dvd_mul_right.mp hh
end GCD
section Polynomial
variable {R:Type*} [CommRing R] [IsDomain R] [GCDMonoid (Polynomial R)]
theorem EEZ (P:Polynomial R) (h q:R) (hh:h≠0):
    (WE h q P).natDegree=P.natDegree:=by
  change (P.comp (Polynomial.C h*Polynomial.X+Polynomial.C q)).natDegree=P.natDegree
  rw [Polynomial.natDegree_comp,Polynomial.natDegree_add_C,
    Polynomial.natDegree_C_mul_X h hh,mul_one]
theorem BQG (P:Polynomial R) (n:ℕ) (h q:R)
    (hP:P≠0) (hn:P.natDegree≤n) (hh:h≠0):PH P n h q≠0:=by
  intro hz
  have he:=BJK P n h q hn
  rw [hz,map_zero] at he
  exact mul_ne_zero (pow_ne_zero n (Polynomial.C_ne_zero.mpr hh)) hP he.symm
theorem DYH (P Q:Polynomial R) (n m:ℕ) (h q:R)
    (hn:P.natDegree≤n) (hm:Q.natDegree≤m) (hh:h≠0)
    (hrel:IsRelPrime P Q) (D:Polynomial R) (hD:Prime D)
    (hDP:D ∣ PH P n h q)
    (hDQ:D ∣ PH Q m h q):D ∣ Polynomial.C h:=by
  by_contra hnot
  have hp:=map_dvd (WE h q) hDP
  have hq:=map_dvd (WE h q) hDQ
  rw [BJK P n h q hn] at hp
  rw [BJK Q m h q hm] at hq
  have hp' :WE h q D ∣ (Polynomial.C h)^(n+m)*P:=by
    apply hp.trans
    refine ⟨(Polynomial.C h)^m,?_⟩
    rw [pow_add];ring
  have hq' :WE h q D ∣ (Polynomial.C h)^(n+m)*Q:=by
    apply hq.trans
    refine ⟨(Polynomial.C h)^n,?_⟩
    rw [pow_add];ring
  have hscalar:=FWV ((Polynomial.C h)^(n+m)) P Q
    (WE h q D) hrel hp' hq'
  have hdegree:=Polynomial.natDegree_le_of_dvd hscalar
    (pow_ne_zero (n+m) (Polynomial.C_ne_zero.mpr hh))
  rw [EEZ D h q hh] at hdegree
  have hdegree0:D.natDegree=0:=by
    simpa using Nat.eq_zero_of_le_zero (by simpa using hdegree)
  have hconstant:=Polynomial.eq_C_of_natDegree_eq_zero hdegree0
  have hinverse:WE h q D=D:=by
    rw [hconstant,CPW]
  rw [hinverse] at hp hq
  have hnp: ¬D ∣ (Polynomial.C h)^n:=fun hpow=>hnot (hD.dvd_of_dvd_pow hpow)
  have hnq: ¬D ∣ (Polynomial.C h)^m:=fun hpow=>hnot (hD.dvd_of_dvd_pow hpow)
  have hdP:D ∣ P:=(hD.dvd_or_dvd hp).resolve_left hnp
  have hdQ:D ∣ Q:=(hD.dvd_or_dvd hq).resolve_left hnq
  exact hD.irreducible.not_isUnit (hrel hdP hdQ)
end Polynomial
end
end ARX
end MergedPart10
section MergedPart11
namespace VM
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid
section Flat
variable {A B:Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B] [IsNoetherianRing B]
  [Algebra A B] [Module.Flat A B]
theorem BHU (hinj:Function.Injective (algebraMap A B))
    (P Q:A) (hP:P≠0) (hrel:IsRelPrime P Q):
    IsRelPrime (algebraMap A B P) (algebraMap A B Q):=by
  classical
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · rintro ⟨hz,_⟩
    exact hP (hinj (by simpa only [map_zero] using hz))
  intro g hg hgP hgQ
  let I:Ideal B:=Ideal.span {g}
  haveI:I.IsPrime:=Ideal.isPrime_span_singleton_of_prime hg.prime
  let psi:A→+*B ⧸ I:=(Ideal.Quotient.mk I).comp (algebraMap A B)
  have hz:psi P=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hgP)
  obtain ⟨factors,hfactors,hprod⟩:=WfDvdMonoid.exists_factors P hP
  have hassoc:=Associated.map psi hprod
  rw [hz] at hassoc
  have hp:psi factors.prod=0:=(associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi:Irreducible f:=hfactors f hf
  have hgf:g ∣ algebraMap A B f:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hfzero)
  have he:=RCN350.under_prime_factor_eq hinj f hfi.prime g hg.prime hgf
  have hQmem:Q ∈ (Ideal.span ({g}:Set B)).under A:=Ideal.mem_span_singleton.mpr hgQ
  rw [he] at hQmem
  exact hfi.not_isUnit (hrel ((Multiset.dvd_prod hf).trans hprod.dvd) (Ideal.mem_span_singleton.mp hQmem))
end Flat
section Coefficients
variable {R S σ:Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem CTQ:Module.Flat (MvPolynomial σ R) (MvPolynomial σ S):=by
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R (MvPolynomial σ R) S (MvPolynomial σ S)).symm.toLinearEquiv
end Coefficients
section Equivalence
variable {A B:Type*} [CommRing A] [CommRing B]
theorem BDS (e:A ≃+*B) (P Q:A) (h:IsRelPrime P Q):
    IsRelPrime (e P) (e Q):=by
  intro d hdP hdQ
  have hP:=map_dvd e.symm hdP
  have hQ:=map_dvd e.symm hdQ
  simp only [RingEquiv.symm_apply_apply] at hP hQ
  have hu:=(h hP hQ).map e.toMonoidHom
  change IsUnit (e (e.symm d)) at hu
  simpa only [RingEquiv.apply_symm_apply] using hu
end Equivalence
end
end VM
end MergedPart11
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace XK
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN135 VM TH
variable (K:Type*) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem AQX {σ:Type*} [Finite σ]
    (P Q:MvPolynomial σ (Polynomial K)) (hP:P≠0) (hrel:IsRelPrime P Q):
    IsRelPrime (MvPolynomial.map (RCN135.polynomialEmbedding K) P)
      (MvPolynomial.map (RCN135.polynomialEmbedding K) Q):=by
  letI:Module.Flat (Polynomial K) (RationalBase K):=
    IsLocalization.flat (RationalBase K) (nonZeroDivisors (Polynomial K))
  letI:Module.Flat (Polynomial K) (GenericField K):=
    Module.Flat.trans (Polynomial K) (RationalBase K) (GenericField K)
  letI:Module.Flat (MvPolynomial σ (Polynomial K)) (MvPolynomial σ (GenericField K)):=
    CTQ
  have hemb:RCN135.polynomialEmbedding K=algebraMap (Polynomial K) (GenericField K):=
    (IsScalarTower.algebraMap_eq (Polynomial K) (RationalBase K) (GenericField K)).symm
  rw [hemb]
  exact BHU (MvPolynomial.map_injective _ (by rw [←hemb];exact RCN135.polynomialEmbedding_injective K)) P Q hP hrel
def collectCode:SecondJetSupport.Poly (K:=K) ≃ₐ[K] MvPolynomial (Fin 4) (Polynomial K):=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 4)).trans
    (MvPolynomial.optionEquivRight K (Fin 4))
def sourceMap {E:Type*} [Field E] (phi:Polynomial K→+*E):
    SecondJetSupport.Poly (K:=K)→+*MvPolynomial (Fin 4) E:=
  (MvPolynomial.map phi).comp (collectCode K).toRingHom
abbrev AVG:=sourceMap K (RCN135.polynomialEmbedding K)
theorem GBZ {E:Type*} [Field E] (phi:Polynomial K→+*E):
    sourceMap K phi (MvPolynomial.X 0)=MvPolynomial.C (phi Polynomial.X):=by
  simp [sourceMap,collectCode,MvPolynomial.renameEquiv_apply]
theorem EYX {E:Type*} [Field E] (phi:Polynomial K→+*E) (i:Fin 4):
    sourceMap K phi (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
  simp [sourceMap,collectCode,MvPolynomial.renameEquiv_apply]
theorem asS_X_code:SecondJetCoefficients.asS (MvPolynomial.X (0:Fin 5):SecondJetSupport.Poly (K:=K))=
    Polynomial.C (MvPolynomial.X 0):=by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  change MvPolynomial.finSuccEquiv K 4 (MvPolynomial.X (0:Fin 4).succ)=_
  exact MvPolynomial.finSuccEquiv_X_succ
theorem asS_X_jet:SecondJetCoefficients.asS (MvPolynomial.X (1:Fin 5):SecondJetSupport.Poly (K:=K))=
    Polynomial.X:=by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  change MvPolynomial.finSuccEquiv K 4 (MvPolynomial.X 0)=_
  exact MvPolynomial.finSuccEquiv_X_zero
theorem asS_X_tail (i:Fin 3):
    SecondJetCoefficients.asS (MvPolynomial.X i.succ.succ:SecondJetSupport.Poly (K:=K))=
      Polynomial.C (MvPolynomial.X i.succ):=by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  have h0:i.succ.succ ≠ (0:Fin 5):=by fin_cases i<;>decide
  have h1:i.succ.succ ≠ (1:Fin 5):=by fin_cases i<;>decide
  rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
  exact MvPolynomial.finSuccEquiv_X_succ
theorem EIC (J Q:SecondJetSupport.Poly (K:=K))
    (hJ:J≠0) (hrel:IsRelPrime J Q):IsRelPrime (AVG K J) (AVG K Q):=by
  have hJ' :collectCode K J≠0:=by
    intro hz
    exact hJ ((collectCode K).injective (by simpa only [map_zero] using hz))
  exact AQX K _ _ hJ'
    (BDS (collectCode K).toRingEquiv J Q hrel)
theorem FLC {E:Type*} [Field E] (phi:Polynomial K→+*E)
    (P:SecondJetSupport.Poly (K:=K)):
    MvPolynomial.finSuccEquiv E 3 (sourceMap K phi P)=coefficients phi P:=by
  have hx (i:Fin 5):MvPolynomial.finSuccEquiv E 3 (sourceMap K phi (MvPolynomial.X i))=
      coefficients phi (MvPolynomial.X i):=by
    refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=> ?_) j) i
    · rw [GBZ,coefficients,asS_X_code,Polynomial.map_C,RCN136.surfaceMap_X_zero]
      simp [MvPolynomial.finSuccEquiv_apply]
    · rw [EYX,MvPolynomial.finSuccEquiv_X_zero,coefficients]
      rw [show (0:Fin 4).succ=(1:Fin 5) by decide,asS_X_jet,Polynomial.map_X]
    · rw [EYX,MvPolynomial.finSuccEquiv_X_succ,coefficients,asS_X_tail,
        Polynomial.map_C,RCN136.surfaceMap_X_succ]
  induction P using MvPolynomial.induction_on with
  | C c=>
    simp [sourceMap,collectCode,coefficients,SecondJetCoefficients.asS,
      MvPolynomial.renameEquiv_apply,MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ=>
    simp only [map_add,coefficients,Polynomial.map_add] at hP hQ ⊢
    rw [hP,hQ]
  | mul_X P i hP=>
    have hi:=hx i
    dsimp only [coefficients] at hi
    simp only [map_mul,coefficients,Polynomial.map_mul] at hP ⊢
    rw [hP,hi]
end
end XK
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace XB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
variable {K:Type*} [Field K]
structure Box where
  q:ℕ
  loB:ℕ
  hiB:ℕ
  loU:ℕ
  loT:ℕ
  deriving DecidableEq
def Box.R (a:Box):=31-a.q*a.loB
def Box.U (a:Box):=98-a.q*a.loU
def Box.T (a:Box):=1700-a.q*a.loT
def Box.C (a:Box):=13050360-a.q*(131071*a.loU-a.hiB)
def Box.n (a:Box):=a.R/2+1
abbrev Index (a:Box):=Σ j:Fin a.n,Σ r:Fin (a.R+1-2*j.val),
  Σ y:Fin (a.U+1),Fin (a.C-131071*y.val) × Fin (a.T+1)
theorem BKI (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (u b:ℕ)
    (hu:u≤weightedTotalDegree HA J)
    (hb:weightedTotalDegree slopeWeights J≤b):
    131071*u-b≤weightedTotalDegree codeWeights J:=by
  obtain ⟨e,he,hmax⟩:=Finset.exists_mem_eq_sup J.support
    (support_nonempty.mpr hJ) (Finsupp.weight HA)
  have hm:u≤Finsupp.weight HA e:=by
    change u≤J.support.sup (Finsupp.weight HA) at hu
    rwa [hmax] at hu
  have hs:=(Finset.le_sup (f:=Finsupp.weight slopeWeights) he).trans hb
  have hc:Finsupp.weight codeWeights e≤weightedTotalDegree codeWeights J:=Finset.le_sup he
  simp [JW,codeWeights,HA,slopeWeights] at hm hs hc
  dsimp only [codeWeights]
  omega
def FBU (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)) (q:ℕ)
    (hd: ∀v:V,J^q∣v.val) (v:V):SecondJetSupport.Poly (K:=K):=Classical.choose (hd v)
theorem RV (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)) (q:ℕ)
    (hd: ∀v:V,J^q∣v.val) (v:V):v.val=J^q*FBU V J q hd v:=
  Classical.choose_spec (hd v)
def BKC (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)) (q:ℕ)
    (hJ:J≠0) (hd: ∀v:V,J^q∣v.val):V→ₗ[K] SecondJetSupport.Poly (K:=K) where
  toFun:=FBU V J q hd
  map_add' v u:=by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [mul_add,←RV,←RV,←RV]
    rfl
  map_smul' c v:=by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [←RV]
    change c • v.val=J^q*(c • FBU V J q hd v)
    rw [RV V J q hd v]
    simp only [MvPolynomial.smul_eq_C_mul]
    ac_rfl
end
end XB
end MergedPart0
section MergedPart2
namespace RB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetRelaxedGlobalIndex (Index budget exponent)
open SecondJetRelaxedGlobalIndex renaming exponent_injective → ACD
open SecondJetRelaxedGlobalCounts renaming coefficientCount → AW
abbrev Index (C T R S U:ℕ):=
  SecondJetRelaxedGlobalIndex.Index (fun _=>C) 131071 T R S U
def exponent (C T R S U:ℕ) (i:Index C T R S U):Fin 5→₀ ℕ:=
  SecondJetRelaxedGlobalIndex.exponent i
theorem card_eq (C T R S U:ℕ) (hUT:U≤T):
    Fintype.card (Index C T R S U)=SecondJetRelaxedGlobalCounts.coefficientCount (fun _=>C) 131071 T R S U:=
  SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUT
theorem AKF (C T R S U:ℕ) (e:Fin 5→₀ ℕ)
    (hc:e 0+131069*e 1+131071*e 2+131070*e 3<C)
    (ht:e 1+e 2+e 3+e 4≤T)
    (hr:2*e 1+e 3≤R) (hs:e 1≤S) (hu:e 1+e 2+e 3≤U):
    e∈Set.range (exponent C T R S U):=by
  have hh:e 1<S+1:=by omega
  have hrr:e 3<R-2*e 1+1:=by omega
  have hx:e 0<SecondJetRelaxedGlobalIndex.budget (fun _=>C) 131071 (e 1) (e 3)-131071*e 2:=by
    simp only [SecondJetRelaxedGlobalIndex.budget]
    omega
  have hy:e 2<SecondJetRelaxedGlobalIndex.yCount (fun _=>C) 131071 U (e 1) (e 3):=by
    simp only [SecondJetRelaxedGlobalIndex.yCount,SecondJetRelaxedGlobalIndex.budget]
    omega
  have hz:e 4<T+1-e 1-e 3-e 2:=by omega
  refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hrr⟩,⟨e 2,hy⟩,⟨e 0,hx⟩,⟨e 4,hz⟩⟩,?_⟩
  ext i
  fin_cases i<;>simp [exponent,SecondJetRelaxedGlobalIndex.exponent]
end
end RB
end MergedPart2
section MergedPart3
namespace DA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open XB
open SecondJetRelaxedGlobalCounts renaming coefficientCount → AW
structure SourceCaps where
  C:ℕ
  T:ℕ
  B:ℕ
  S:ℕ
  U:ℕ
structure OwnerBox where
  q:ℕ
  loB:ℕ
  hiB:ℕ
  loS:ℕ
  loU:ℕ
  loT:ℕ
def remC (p:SourceCaps) (a:OwnerBox):=p.C-a.q*(131071*a.loU-a.hiB)
def remT (p:SourceCaps) (a:OwnerBox):=p.T-a.q*a.loT
def remB (p:SourceCaps) (a:OwnerBox):=p.B-a.q*a.loB
def remU (p:SourceCaps) (a:OwnerBox):=min (p.U-a.q*a.loU) (remT p a)
def remS (p:SourceCaps) (a:OwnerBox):=min (p.S-a.q*a.loS) (min (remB p a/2) (remU p a))
def count (p:SourceCaps) (a:OwnerBox):=
  SecondJetRelaxedGlobalCounts.coefficientCount (fun _=>remC p a) 131071 (remT p a) (remB p a) (remS p a) (remU p a)
def Impossible (p:SourceCaps) (a:OwnerBox):Prop:=
  p.B<a.q*a.loB∨p.S<a.q*a.loS∨p.U<a.q*a.loU∨p.T<a.q*a.loT∨
    p.C≤a.q*(131071*a.loU-a.hiB)
variable {K:Type*} [Field K]
def Bounds (p:SourceCaps) (P:SecondJetSupport.Poly (K:=K)):Prop:=
  weightedTotalDegree codeWeights P<p.C∧weightedTotalDegree Koala6831Ordinary.totalWeights P≤p.T∧
  weightedTotalDegree slopeWeights P≤p.B∧P.degreeOf 1≤p.S∧
  weightedTotalDegree HA P≤p.U
def Covers (a:OwnerBox) (J:SecondJetSupport.Poly (K:=K)):Prop:=
  a.loB≤weightedTotalDegree slopeWeights J∧weightedTotalDegree slopeWeights J≤a.hiB∧
  a.loS≤J.degreeOf 1∧a.loU≤weightedTotalDegree HA J∧
  a.loT≤weightedTotalDegree Koala6831Ordinary.totalWeights J
theorem AUL (p:SourceCaps) (a:OwnerBox)
    (P J Q:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hQ:Q≠0)
    (heq:P=J^a.q*Q) (hP:Bounds p P) (ha:Covers a J):
    ¬Impossible p a∧
    weightedTotalDegree codeWeights Q<remC p a∧
    weightedTotalDegree Koala6831Ordinary.totalWeights Q≤remT p a∧
    weightedTotalDegree slopeWeights Q≤remB p a∧
    Q.degreeOf 1≤p.S-a.q*a.loS∧
    weightedTotalDegree HA Q≤p.U-a.q*a.loU:=by
  obtain ⟨hc,ht,hb,hs,hu⟩:=hP
  obtain ⟨hb0,hb1,hs0,hu0,ht0⟩:=ha
  rw [heq,weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hc ht hb hu
  rw [heq,degreeOf_mul_eq (pow_ne_zero _ hJ) hQ,degreeOf_pow_eq _ _ _ hJ] at hs
  have hcode:=BKI J hJ a.loU a.hiB hu0 hb1
  have hbc:=Nat.mul_le_mul_left a.q hb0
  have hsc:=Nat.mul_le_mul_left a.q hs0
  have huc:=Nat.mul_le_mul_left a.q hu0
  have htc:=Nat.mul_le_mul_left a.q ht0
  have hcc:=Nat.mul_le_mul_left a.q hcode
  simp only [Impossible,remC,remT,remB]
  omega
theorem EZL (p:SourceCaps) (a:OwnerBox)
    (P J Q:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hQ:Q≠0)
    (heq:P=J^a.q*Q) (hP:Bounds p P) (ha:Covers a J):
    ∀e∈Q.support,e∈Set.range
      (RB.exponent (remC p a) (remT p a) (remB p a) (remS p a) (remU p a)):=by
  obtain ⟨_,hc,ht,hb,hs,hu⟩:=AUL p a P J Q hJ hQ heq hP ha
  intro e he
  have c:=(le_weightedTotalDegree codeWeights he).trans_lt hc
  have t:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights he).trans ht
  have b:=(le_weightedTotalDegree slopeWeights he).trans hb
  have s:=(MvPolynomial.monomial_le_degreeOf 1 he).trans hs
  have u:=(le_weightedTotalDegree HA he).trans hu
  simp [JW,codeWeights,Koala6831Ordinary.totalWeights,slopeWeights,HA] at c t b u
  apply RB.AKF
  all_goals
    try dsimp only [remS,remU]
    omega
theorem ASJ (p:SourceCaps) (a:OwnerBox) (Kdim:ℕ)
    (V:Submodule K (SecondJetSupport.Poly (K:=K))) [Module.Finite K V]
    (hdim:Kdim≤Module.finrank K V)
    (hb: ∀P∈V,Bounds p P)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
    (hgood:(Impossible p a∧0<Kdim)∨count p a<Kdim):
    ∃P∈V,¬J^a.q∣P:=by
  by_contra hno
  have hd: ∀P∈V,J^a.q∣P:=by simpa only [not_exists,not_and,not_not] using hno
  let hv: ∀v:V,J^a.q∣v.val:=fun v=>hd v.val v.property
  let f:=BKC V J a.q hJ hv
  have hf:Function.Injective f:=by
    intro v u he
    apply Subtype.ext
    rw [RV V J a.q hv v,RV V J a.q hv u]
    exact congrArg (fun Q=>J^a.q*Q) he
  rcases hgood with ⟨hbad,hpos⟩ | hcount
  · have hz: ∀v,f v=0:=by
      intro v
      by_contra hn
      exact (AUL p a v.val J (f v) hJ hn
        (RV V J a.q hv v) (hb v.val v.property) ha).1 hbad
    have hcard:=ARN (fun i:Fin 0=>Fin.elim0 i) f hf
      (by intro v e he;simp [hz v] at he)
    simp only [Fintype.card_fin] at hcard
    omega
  · have hsupport: ∀v,∀e∈(f v).support,e∈Set.range
        (RB.exponent (remC p a) (remT p a) (remB p a) (remS p a) (remU p a)):=by
      intro v e he
      have hn:f v≠0:=by intro hz;simp [hz] at he
      exact EZL p a v.val J (f v) hJ hn
        (RV V J a.q hv v) (hb v.val v.property) ha e he
    have hcard:=ARN _ f hf hsupport
    have hUT:remU p a≤remT p a:=min_le_right _ _
    rw [RB.card_eq (remC p a) (remT p a) (remB p a)
      (remS p a) (remU p a) hUT] at hcard
    change Module.finrank K V≤count p a at hcard
    omega
end
end DA
end MergedPart3
section MergedPart4
namespace BJN
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid TH ARX RCN259
variable {R:Type*} [CommRing R] [IsDomain R]
  [GCDMonoid (Polynomial R)] [NormalizationMonoid (Polynomial R)]
  [UniqueFactorizationMonoid (Polynomial R)]
theorem EXA {E:Type*} [CommRing E] [IsDomain E]
    (P Q:Polynomial R) (n m:ℕ) (h q:R)
    (hP:P≠0) (hn:P.natDegree≤n) (hm:Q.natDegree≤m) (hh:h≠0)
    (hrel:IsRelPrime P Q) (ev:Polynomial R→+*E) (hev:ev (Polynomial.C h)≠0):
    ev (gcd (PH P n h q) (PH Q m h q))≠0:=by
  classical
  let A:=PH P n h q
  let B:=PH Q m h q
  have hA:A≠0:=BQG P n h q hP hn hh
  have hG:gcd A B≠0:=gcd_ne_zero_of_left hA
  intro hz
  have hassoc:=Associated.map ev (prod_normalizedFactors hG)
  rw [hz] at hassoc
  have hp:ev (normalizedFactors (gcd A B)).prod=0:=(associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi:Irreducible f:=irreducible_of_normalized_factor f hf
  have hfg:=dvd_of_mem_normalizedFactors hf
  have hfh:f ∣ Polynomial.C h:=DYH P Q n m h q hn hm hh hrel
    f hfi.prime (hfg.trans (gcd_dvd_left A B)) (hfg.trans (gcd_dvd_right A B))
  obtain ⟨g,hg⟩:=hfh
  apply hev
  rw [hg,map_mul,hfzero,zero_mul]
end
end BJN
end MergedPart4
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace AQM
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN135 RCN136
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open TH XK BJN
variable (K:Type*) [Field K]
local notation "Omega" =>GenericField K
local notation "Poly3" =>MvPolynomial (Fin 3) Omega
local instance:StrongNormalizationMonoid (Polynomial Poly3):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid (Polynomial Poly3):=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _
def FBS (E:Type*) [Field E]:
    Polynomial (MvPolynomial (Fin 3) E) ≃ₐ[E] MvPolynomial (Fin 3) (Polynomial E):=
  (MvPolynomial.finSuccEquiv E 3).symm.trans (RCN136.collectX E)
def VY (E:Type*) [Field E]:
    Polynomial (MvPolynomial (Fin 3) E)→+*MvPolynomial (Fin 3) (GenericField E):=
  (RCN136.surfaceMap (RCN135.polynomialEmbedding E)).comp (MvPolynomial.finSuccEquiv E 3).symm.toRingHom
theorem EGV (E:Type*) [Field E]:
    Function.Injective (VY E):=
  (RCN136.surfaceMap_injective (RCN135.polynomialEmbedding E) (RCN135.polynomialEmbedding_injective E)).comp
    (MvPolynomial.finSuccEquiv E 3).symm.injective
theorem EKY (E:Type*) [Field E]
    (U V:Polynomial (MvPolynomial (Fin 3) E)) (hU:U≠0) (hrel:IsRelPrime U V):
    IsRelPrime (VY E U) (VY E V):=by
  have hU' :FBS E U≠0:=by
    intro hz
    exact hU ((FBS E).injective (by simpa only [map_zero] using hz))
  exact AQX E _ _ hU'
    (VM.BDS (FBS E).toRingEquiv U V hrel)
theorem DZB (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0):
    coefficients (RCN135.polynomialEmbedding K) P≠0:=by
  intro hz
  apply hP
  apply (SecondJetCoefficients.asS (K:=K)).injective
  apply Polynomial.map_injective (surfaceMap (RCN135.polynomialEmbedding K))
    (RCN136.surfaceMap_injective (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz
end
end AQM
end MergedPart0
section MergedPart1
namespace CKL
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN095 RCN135 RCN136 RCN207
open RCN095 renaming PolynomialInFlag → BI
open TH AQM
variable (E:Type*) [Field E]
theorem FGR (i:Fin 3):
    VY E (Polynomial.C (MvPolynomial.X i))=MvPolynomial.X i:=by
  have hi:(MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.X i))=
      MvPolynomial.X i.succ:=by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_succ]
  change surfaceMap (RCN135.polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hi,RCN136.surfaceMap_X_succ]
theorem EMK (P:MvPolynomial (Fin 3) E):
    VY E (Polynomial.C P)=MvPolynomial.map (RCN135.coefficientEmbedding E) P:=by
  induction P using MvPolynomial.induction_on with
  | C c=>
    have hc:(MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.C c))=
        MvPolynomial.C c:=by
      apply (MvPolynomial.finSuccEquiv E 3).injective
      simp [MvPolynomial.finSuccEquiv_apply]
    change surfaceMap (RCN135.polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
    rw [hc,surfaceMap_C,MvPolynomial.map_C]
    rfl
  | add P Q hP hQ=>simp only [map_add,hP,hQ]
  | mul_X P i hP=>simp only [map_mul,hP,FGR,MvPolynomial.map_X]
theorem FMS:
    VY E Polynomial.X=MvPolynomial.C (RCN135.initialCoordinate E):=by
  have hx:(MvPolynomial.finSuccEquiv E 3).symm Polynomial.X=MvPolynomial.X 0:=by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_zero]
  change surfaceMap (RCN135.polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hx,RCN136.surfaceMap_X_zero]
  rfl
theorem ENL:
    VY E=Polynomial.eval₂RingHom (MvPolynomial.map (RCN135.coefficientEmbedding E))
      (MvPolynomial.C (RCN135.initialCoordinate E)):=by
  apply Polynomial.ringHom_ext
  · intro P
    change VY E (Polynomial.C P)=Polynomial.eval₂ _ _ (Polynomial.C P)
    rw [Polynomial.eval₂_C]
    exact EMK E P
  · change VY E Polynomial.X=Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X]
    exact FMS E
section Sources
variable {K:Type*} [Field K]
theorem GBE {L:Type*} [Field L] (f:E→+*L)
    (phi:Polynomial K→+*E) (P:SecondJetSupport.Poly (K:=K)):
    (coefficients phi P).map (MvPolynomial.map f)=coefficients (f.comp phi) P:=by
  have he:(MvPolynomial.map f).comp (surfaceMap phi)=surfaceMap (f.comp phi):=by
    apply RingHom.ext
    intro A
    simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]
  rw [coefficients,Polynomial.map_map,he]
  rfl
theorem BDY
    (phi:Polynomial K→+*E) (P:SecondJetSupport.Poly (K:=K))
    (s:ℕ) (quadratic A:MvPolynomial (Fin 3) E):
    VY E (PH (coefficients phi P) s (2*A) quadratic)=
      movingCut ((RCN135.coefficientEmbedding E).comp phi) P s
        (MvPolynomial.map (RCN135.coefficientEmbedding E) quadratic)
        (MvPolynomial.map (RCN135.coefficientEmbedding E) A) (RCN135.initialCoordinate E):=by
  rw [ENL]
  change Polynomial.eval₂ _ _ (PH _ _ _ _)=_
  rw [FAN,GBE]
  simp only [map_mul,map_ofNat,movingCut]
end Sources
theorem flag_of_dvd (P Q:MvPolynomial (Fin 3) E) (p:FlagDegree)
    (hdiv:P ∣ Q) (hQ:Q≠0) (hflag:RCN095.PolynomialInFlag p Q):RCN095.PolynomialInFlag p P:=by
  have hw (w:Fin 3→ℕ) (c:ℕ)
      (hc: ∀e ∈ Q.support,Finsupp.weight w e≤c):
      ∀e ∈ P.support,Finsupp.weight w e≤c:=by
    intro e he
    have h1:Finsupp.weight w e≤weightedTotalDegree w P:=Finset.le_sup he
    have h2:=RCN071.weightedTotalDegree_le_of_dvd_fin3 w P Q hdiv hQ
    have h3:weightedTotalDegree w Q≤c:=Finset.sup_le hc
    exact h1.trans (h2.trans h3)
  intro e he
  refine ⟨?_,?_,?_⟩
  · have hh:=hw flagSWeights p.all (by
      intro d hd
      simpa [RCN095.flag_weight_fin3,flagSWeights] using (hflag d hd).1) e he
    simpa [RCN095.flag_weight_fin3,flagSWeights] using hh
  · have hh:=hw RCN095.flagYSWeights (p.yz+p.all) (by
      intro d hd
      simpa [RCN095.flag_weight_fin3,RCN095.flagYSWeights] using (hflag d hd).2.1) e he
    simpa [RCN095.flag_weight_fin3,RCN095.flagYSWeights] using hh
  · have hh:=hw RCN095.flagTotalWeights (p.zOnly+p.yz+p.all) (by
      intro d hd
      simpa [RCN095.flag_weight_fin3,RCN095.flagTotalWeights] using (hflag d hd).2.2) e he
    simpa [RCN095.flag_weight_fin3,RCN095.flagTotalWeights] using hh
end
end CKL
end MergedPart1
section MergedPart2
namespace BAI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial RCN136 RCN207
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open TH
variable {K E:Type*} [Field K] [Field E]
theorem EEI
    (P:SecondJetSupport.Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (phi:MvPolynomial (Fin 4) K→+*E)
    (hker: ∀A,phi A=0 ↔ F ∣ A)
    (s:ℕ) (hS: ∀e ∈ P.support,e 1≤s)
    (hH:phi (2*RCN313.polyH K F)≠0)
    (hroot:((SecondJetCoefficients.asS P).map phi).eval (SecondJetCarrierDichotomy.ratio phi F)=0):F ∣ SecondJetClearedHelper.helper P F s 0:=by
  apply (hker _).mp
  have hh:=SecondJetCarrierDichotomy.mapped_helper P F phi s 0 hS hH
  simpa only [Nat.sub_zero,Function.iterate_zero,id_eq,hroot,mul_zero] using hh
end
end BAI
end MergedPart2
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace BQV
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
variable {K:Type} [Field K]
theorem FZF (p:Polynomial K)
    (hp:Irreducible (Polynomial.C p:Polynomial (Polynomial K))):Irreducible p:=by
  refine ⟨fun hu=>hp.not_isUnit (hu.map Polynomial.C),?_⟩
  intro a b hab
  have hh:=hp.isUnit_or_isUnit (by rw [hab,map_mul])
  exact hh.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp
theorem EMU (p:Polynomial K) (hp:Irreducible p)
    {E:Type} [Field E] [Algebra K E] (y:E) (hy:Polynomial.aeval y p=0):
    Associated p (minpoly K y):=by
  have hi:IsIntegral K y:=IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  exact (minpoly.irreducible hi).associated_of_dvd hp (minpoly.dvd K y hy) |>.symm
theorem EWV (p:Polynomial K) (hp:Irreducible p)
    (Q:Polynomial (Polynomial K)) (hproper: ¬Polynomial.C p ∣ Q)
    {E:Type} [Field E] [Algebra K E] (y:E) (hy:Polynomial.aeval y p=0):
    Q.map (Polynomial.eval₂RingHom (algebraMap K E) y)≠0:=by
  intro hz
  apply hproper
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have hj:=congrArg (fun A:Polynomial E=>A.coeff j) hz
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero,
    Polynomial.coe_eval₂RingHom] at hj
  exact (EMU p hp y hy).dvd.trans (minpoly.dvd K y hj)
theorem EOH
    (p:Polynomial K) (hp:Irreducible p) (Q:Polynomial (Polynomial K))
    (hproper: ¬Polynomial.C p ∣ Q)
    {E:Type} [Field E] [Algebra K E] (y r:E)
    (hy:Polynomial.aeval y p=0)
    (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0)
    (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤):
    FiniteDimensional K E:=by
  classical
  letI:DecidableEq K:=Classical.decEq K
  have hyi:IsIntegral K y:=IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  let S:IntermediateField K E:=IntermediateField.adjoin K {y}
  let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
  let g:Polynomial K→+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
  have hcoeff:(algebraMap S E).comp g=
      Polynomial.eval₂RingHom (algebraMap K E) y:=by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
        Polynomial.eval₂ (algebraMap K E) y (Polynomial.C c)
      rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S E c).symm
    · change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
        Polynomial.eval₂ (algebraMap K E) y Polynomial.X
      simp only [Polynomial.eval₂_X]
      rfl
  have hQne:Q.map g≠0:=by
    intro hz
    have hh:=congrArg (Polynomial.map (algebraMap S E)) hz
    rw [Polynomial.map_map,hcoeff,Polynomial.map_zero] at hh
    exact EWV p hp Q hproper y hy hh
  have hr:Polynomial.aeval r (Q.map g)=0:=by
    change Polynomial.eval₂ (algebraMap S E) r (Q.map g)=0
    rw [Polynomial.eval₂_map,hcoeff]
    exact hQ
  have hri:IsIntegral S r:=IsAlgebraic.isIntegral ⟨Q.map g,hQne,hr⟩
  letI:FiniteDimensional K S:=IntermediateField.adjoin.finiteDimensional hyi
  letI:Algebra.IsIntegral K S:=Algebra.IsIntegral.of_finite K S
  exact RCN024.finiteDimensional_of_integral_generating_pair y r hyi
    (isIntegral_trans r hri) hgen
theorem FDW
    {I:Type*} [Fintype I] (E:I→Type)
    [∀i,Field (E i)] [∀i,Algebra K (E i)] [∀i,FiniteDimensional K (E i)]
    (p:Polynomial K) (hp:Irreducible p) (Q:Polynomial (Polynomial K))
    (hproper: ¬Polynomial.C p ∣ Q) (y r: ∀i,E i)
    (hgen: ∀i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i=>RCN361.relationIdeal K (E i) (y i) (r i)))
    (hy: ∀i,Polynomial.aeval (y i) p=0)
    (hQ: ∀i,RCN361.planeEval K (E i) (y i) (r i) Q=0):
    (∑ i,Module.finrank K (E i))≤Q.natDegree*p.natDegree:=by
  classical
  letI:DecidableEq K:=Classical.decEq K
  have hspecial: ∀f ∈ Finset.univ.image (fun i=>minpoly K (y i)),
      Q.map (AdjoinRoot.mk f)≠0:=by
    intro f hf hz
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
    apply hproper
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    have hj:=congrArg (fun A:Polynomial (AdjoinRoot (minpoly K (y i)))=>A.coeff j) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hj
    exact (EMU p hp (y i) (hy i)).dvd.trans (AdjoinRoot.mk_eq_zero.mp hj)
  have hroot: ∀i,RCN361.planeEval K (E i) (y i) (r i) (Polynomial.C p)=0:=by
    intro i
    rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C]
    exact hy i
  have hres:Polynomial.resultant Q (Polynomial.C p) Q.natDegree 0≠0:=by
    simpa only [Polynomial.resultant_C_right,pow_zero,one_mul] using pow_ne_zero Q.natDegree hp.ne_zero
  have hb:=RCN025.sum_finrank_le_resultant_of_relationIdeal_injective
    E Q (Polynomial.C p) Q.natDegree 0 le_rfl (by simp) y r hgen hkernels
    hQ hroot hspecial hres
  simpa only [Polynomial.resultant_C_right,pow_zero,one_mul,Polynomial.natDegree_pow] using hb
theorem DPL
    {I:Type*} [Fintype I] (E:I→Type)
    [∀i,Field (E i)] [∀i,Algebra K (E i)]
    (P Q:Polynomial (Polynomial K)) (hP:Irreducible P) (hproper: ¬P∣Q)
    (y r: ∀i,E i)
    (hgen: ∀i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i=>RCN361.relationIdeal K (E i) (y i) (r i)))
    (hProot: ∀i,RCN361.planeEval K (E i) (y i) (r i) P=0)
    (hQroot: ∀i,RCN361.planeEval K (E i) (y i) (r i) Q=0):
    (∀i,FiniteDimensional K (E i))∧
      (∑ i,Module.finrank K (E i))≤(Polynomial.resultant P Q).natDegree:=by
  classical
  letI:DecidableEq K:=Classical.decEq K
  by_cases hzero:P.natDegree=0
  · have he:=Polynomial.eq_C_of_natDegree_eq_zero hzero
    rw [he] at hP hproper hProot ⊢
    have hp:=FZF (P.coeff 0) hP
    have hy: ∀i,Polynomial.aeval (y i) (P.coeff 0)=0:=by
      intro i
      have hh:=hProot i
      rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C] at hh
      exact hh
    have hfinite: ∀i,FiniteDimensional K (E i):=fun i=>
      EOH (P.coeff 0) hp Q hproper (y i) (r i) (hy i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI: ∀i,FiniteDimensional K (E i):=hfinite
    refine ⟨hfinite,?_⟩
    have hh:=FDW E (P.coeff 0) hp Q hproper y r hgen hkernels hy hQroot
    simpa only [Polynomial.natDegree_C,Polynomial.resultant_C_left,zero_mul,pow_zero,
      one_mul,Polynomial.natDegree_pow] using hh
  · have hpositive:=Nat.pos_of_ne_zero hzero
    have hfinite: ∀i,FiniteDimensional K (E i):=fun i=>
      RCN024.BAC P Q hP hpositive hproper (y i) (r i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hProot i))
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI: ∀i,FiniteDimensional K (E i):=hfinite
    exact ⟨hfinite,RCN124.AEL
      E P Q hP hpositive hproper y r hgen hkernels hProot hQroot⟩
end
end BQV
end MergedPart0
section MergedPart1
namespace JS
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN009 RCN013 RCN021 RCN022
open RCN371 renaming RationalPolynomials → KU
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN084 RCN137 RCN071
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
theorem DUR
    (K:Type) [Field K] (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
    (E:I→Type) [∀i,Field (E i)] [∀i,Algebra K (E i)]
    (e: ∀i,Original K→ₐ[K] E i)
    (ht: ∀i,Transcendental K (e i (MvPolynomial.X (order 0))))
    (hgen: ∀i,
      letI:Algebra (RatFunc K) (E i):=
        (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i=>RingHom.ker (e i).toRingHom))
    (G H:Original K) (hG:Irreducible G)
    (hGroot: ∀i,e i G=0) (hHroot: ∀i,e i H=0) (hproper: ¬G∣H):
    letI: ∀i,Algebra (RatFunc K) (E i):=fun i=>
      (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀i,FiniteDimensional (RatFunc K) (E i))∧
      (∑ i,Module.finrank (RatFunc K) (E i))≤
        (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree:=by
  classical
  letI: ∀i,Algebra (RatFunc K) (E i):=fun i=>
    (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
      (ht i)).toRingHom.toAlgebra
  by_cases hI:Nonempty I
  · let i₀:I:=Classical.choice hI
    have hirr:Irreducible (planeMap K order G):=
      RCN021.planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
        G hG (hGroot i₀) (ht i₀)
    have hproperPlane: ¬planeMap K order G ∣ planeMap K order H:=by
      intro hdiv
      exact hproper ((RCN021.planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
        G H hG (hGroot i₀) (ht i₀)).mp hdiv)
    have hGroots: ∀i,RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order G)=0:=by
      intro i
      change RCN021.planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
      rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
      exact hGroot i
    have hHroots: ∀i,RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order H)=0:=by
      intro i
      change RCN021.planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
      rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
      exact hHroot i
    have hrelation:Function.Injective (fun i=>RCN361.relationIdeal (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))):=by
      intro i j hij
      apply hkernels
      change RCN021.relationKernel K (E i) order (e i) (ht i)=
        RCN021.relationKernel K (E j) order (e j) (ht j) at hij
      have hc:=congrArg (Ideal.comap (planeMap K order)) hij
      simpa only [RCN021.relationKernel_contract] using hc
    exact BQV.DPL E
      (planeMap K order G) (planeMap K order H) hirr hproperPlane
      (fun i=>e i (MvPolynomial.X (order 2)))
      (fun i=>e i (MvPolynomial.X (order 1))) hgen hrelation hGroots hHroots
  · letI:IsEmpty I:=⟨fun i=>hI ⟨i⟩⟩
    exact ⟨fun i=>isEmptyElim i,by simp⟩
theorem EPS
    {K:Type} [Field K] (B:MvPolynomial (Fin 3) K) (hB:B≠0)
    (p q r:FlagDegree) (hsupport:RCN095.PolynomialInFlag p B):
    (∑ g: ↥(RCN137.normalizedFactorSet B),flagMixed (exactFlag g.1) q r)≤flagMixed p q r:=by
  classical
  have hc:=RCN084.inFlag_weight_caps B p hsupport
  have hw (w:Fin 3→ℕ):
      (∑ g: ↥(RCN137.normalizedFactorSet B),MvPolynomial.weightedTotalDegree w g.1)≤
        MvPolynomial.weightedTotalDegree w B:=by
    rw [Finset.sum_coe_sort]
    exact RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (RCN137.normalizedFactorSet B) id B hB
      (RCN137.normalizedFactorSet_product_dvd B hB)
  apply RCN084.sum_flagMixed_le_of_cumulative
  · simpa only [(RCN084.exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
  · calc
      _=∑ g: ↥(RCN137.normalizedFactorSet B),MvPolynomial.weightedTotalDegree RCN095.flagYSWeights g.1:=
        Finset.sum_congr rfl (fun g _=>(RCN084.exactFlag_cumulative g.1).2.1)
      _≤_:=(hw RCN095.flagYSWeights).trans hc.2.1
  · calc
      _=∑ g: ↥(RCN137.normalizedFactorSet B),MvPolynomial.weightedTotalDegree RCN095.flagTotalWeights g.1:=
        Finset.sum_congr rfl (fun g _=>(RCN084.exactFlag_cumulative g.1).2.2)
      _≤_:=(hw RCN095.flagTotalWeights).trans hc.2.2
inductive Axis | z | u | v
def Axis.order:Axis→(Fin 3 ≃ Fin 3)
  | .z=>zOrder_p19
  | .u=>uOrder_p19
  | .v=>vOrder_p19
def Axis.flag:Axis→FlagDegree
  | .z=>unitZFlag
  | .u=>unitYZFlag
  | .v=>unitAllFlag
theorem BPQ
    {K:Type} [Field K] (axis:Axis) (lam mu nu:K)
    (G H:MvPolynomial (Fin 3) K) (p q:FlagDegree)
    (hG:RCN095.PolynomialInFlag p G) (hH:RCN095.PolynomialInFlag q H) (hHne:H≠0):
    (Polynomial.resultant (planeMap K axis.order (flagAlgHom_p19 lam mu nu G))
      (planeMap K axis.order (flagAlgHom_p19 lam mu nu H))).natDegree≤flagMixed p q axis.flag:=by
  have hGs:=(RCN095.support_subset_flagSupport_iff _ _).mpr hG
  have hHs:=(RCN095.support_subset_flagSupport_iff _ _).mpr hH
  cases axis with
  | z=>exact RCN112.BQT p q lam mu nu hGs hHs hHne
  | u=>exact RCN112.BRJ p q lam mu nu hGs hHs hHne
  | v=>exact RCN112.BRI p q lam mu nu hGs hHs hHne
end
end JS
end MergedPart1
section MergedPart2
namespace CAW
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN022 RCN095 RCN093 RCN123 RCN121 RCN084 RCN137
open RCN371 renaming RationalPolynomials → KU
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN125 (flagAlgHom_p19 ARZ flag_dvd_iff_p19)
open JS
theorem DIH
    (K:Type) [Field K] (axis:Axis) (lam mu nu:K) {I:Type} [Fintype I]
    (E:I→Type) [∀i,Field (E i)] [∀i,Algebra K (E i)]
    (e: ∀i,Original K→ₐ[K] E i)
    (ht: ∀i,Transcendental K (e i (MvPolynomial.X (axis.order 0))))
    (hgen: ∀i,
      letI:Algebra (RatFunc K) (E i):=
        (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (axis.order 2)),e i (MvPolynomial.X (axis.order 1))}:
          Set (E i))=⊤)
    (hkernels:Function.Injective (fun i=>RingHom.ker (e i).toRingHom))
    (B H:Original K) (hB:B≠0) (hH:H≠0) (hrel:IsRelPrime B H)
    (hBroot: ∀i,e i (flagAlgHom_p19 lam mu nu B)=0)
    (hHroot: ∀i,e i (flagAlgHom_p19 lam mu nu H)=0)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q H):
    letI: ∀i,Algebra (RatFunc K) (E i):=fun i=>
      (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀i,FiniteDimensional (RatFunc K) (E i))∧
      (∑ i,Module.finrank (RatFunc K) (E i))≤flagMixed p q axis.flag:=by
  classical
  letI: ∀i,Algebra (RatFunc K) (E i):=fun i=>
    (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
      (ht i)).toRingHom.toAlgebra
  have hex: ∀i,∃g: ↥(RCN137.normalizedFactorSet B),e i (flagAlgHom_p19 lam mu nu g.1)=0:=by
    intro i
    obtain ⟨g,hg,hroot⟩:=RCN137.exists_normalizedFactorSet_zero
      ((e i).toRingHom.comp (flagAlgHom_p19 lam mu nu).toRingHom) B hB (hBroot i)
    exact ⟨⟨g,hg⟩,hroot⟩
  choose owner howner using hex
  have hgroup (g: ↥(RCN137.normalizedFactorSet B)):
      (∀i:{i//owner i=g},FiniteDimensional (RatFunc K) (E i.1))∧
        (∑ i:{i//owner i=g},Module.finrank (RatFunc K) (E i.1))≤
          flagMixed (exactFlag g.1) q axis.flag:=by
    have hg:=RCN137.normalizedFactorSet_spec B g.1 g.2
    have hproper: ¬g.1∣H:=fun hgH=>hg.1.not_isUnit (hrel hg.2 hgH)
    have hker:Function.Injective
        (fun i:{i//owner i=g}=>RingHom.ker (e i.1).toRingHom):=by
      intro i j hij
      exact Subtype.ext (hkernels hij)
    have hgroot: ∀i:{i//owner i=g},e i.1 (flagAlgHom_p19 lam mu nu g.1)=0:=by
      intro i
      have hh:=howner i.1
      rw [i.2] at hh
      exact hh
    have hb:=DUR K axis.order
      (fun i:{i//owner i=g}=>E i.1)
      (fun i=>e i.1) (fun i=>ht i.1) (fun i=>hgen i.1) hker
      (flagAlgHom_p19 lam mu nu g.1) (flagAlgHom_p19 lam mu nu H)
      ((ARZ lam mu nu g.1).mpr hg.1)
      hgroot (fun i=>hHroot i.1) (by simpa only [flag_dvd_iff_p19] using hproper)
    exact ⟨hb.1,hb.2.trans (BPQ axis lam mu nu g.1 H
      (exactFlag g.1) q (RCN084.polynomialIn_exactFlag g.1) hq hH)⟩
  refine ⟨fun i=>(hgroup (owner i)).1 ⟨i,rfl⟩,?_⟩
  calc
    (∑ i,Module.finrank (RatFunc K) (E i))=
        ∑ g: ↥(RCN137.normalizedFactorSet B),
          ∑ i:{i//owner i=g},Module.finrank (RatFunc K) (E i.1):=
      (Fintype.sum_fiberwise owner (fun i=>Module.finrank (RatFunc K) (E i))).symm
    _≤ ∑ g: ↥(RCN137.normalizedFactorSet B),flagMixed (exactFlag g.1) q axis.flag:=
      Finset.sum_le_sum (fun g _=>(hgroup g).2)
    _≤flagMixed p q axis.flag:=EPS B hB p q axis.flag hp
end
end CAW
end MergedPart2
section MergedPart3
namespace YL
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN011 RCN022 RCN116 RCN095 RCN093 RCN123 RCN121
open RCN095 renaming PolynomialInFlag → BI
open RCN125 (flagAlgHom_p19 zOrder_p19 uOrder_p19 vOrder_p19)
open JS CAW
theorem ELQ
    {K E:Type} [Field K] [Field E] [Algebra K E]
    {x y:E} (hx:Transcendental K x) (hy:Transcendental K y) (h:x=y):
    RCN022.elementEmbedding K E x hx=RCN022.elementEmbedding K E y hy:=by
  subst y
  rfl
theorem CWN
    (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis:Axis) (lam mu nu:K)
    (ht:Transcendental K (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0)))):
    letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
      (RCN022.elementEmbedding K (RCN002.CoordinateField K P)
        (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 2)),
        RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 1))}:
        Set (RCN002.CoordinateField K P))=⊤ :=by
  cases axis with
  | z=>
    have hz:Transcendental K (coordinate K P 2):=by
      simpa [Axis.order,zOrder_p19,Equiv.swap_apply_def] using ht
    have he:RCN022.elementEmbedding K (RCN002.CoordinateField K P)
        (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.z.order 0))) ht=
        RCN022.elementEmbedding K (RCN002.CoordinateField K P) (coordinate K P 2) hz:=
      ELQ ht hz (by simp [Axis.order,zOrder_p19])
    rw [he]
    simpa [Axis.order,zOrder_p19,Equiv.swap_apply_def] using BKE K P lam mu nu hz
  | u=>
    have hu:Transcendental K (affineU K P lam):=by
      simpa [Axis.order,uOrder_p19] using ht
    have he:RCN022.elementEmbedding K (RCN002.CoordinateField K P)
        (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.u.order 0))) ht=
        RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineU K P lam) hu:=
      ELQ ht hu (by simp [Axis.order,uOrder_p19])
    rw [he]
    simpa [Axis.order,uOrder_p19] using BUX K P lam mu nu hu
  | v=>
    have hv:Transcendental K (affineV K P mu nu):=by
      simpa [Axis.order,vOrder_p19,Equiv.swap_apply_def] using ht
    have he:RCN022.elementEmbedding K (RCN002.CoordinateField K P)
        (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.v.order 0))) ht=
        RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineV K P mu nu) hv:=
      ELQ ht hv (by simp [Axis.order,vOrder_p19])
    rw [he]
    simpa [Axis.order,vOrder_p19,Equiv.swap_apply_def] using BTS K P lam mu nu hv
theorem BSL
    (K:Type) [Field K] (axis:Axis) (lam mu nu:K) {I:Type} [Fintype I]
    (P:I→Ideal (MvPolynomial (Fin 3) K)) [∀i,(P i).IsPrime]
    (hinj:Function.Injective P)
    (ht: ∀i,Transcendental K
      (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H:MvPolynomial (Fin 3) K) (hB:B≠0) (hH:H≠0) (hrel:IsRelPrime B H)
    (hBmem: ∀i,B∈P i) (hHmem: ∀i,H∈P i)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q H):
    letI: ∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=fun i=>
      (RCN022.elementEmbedding K (RCN002.CoordinateField K (P i))
        (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
    (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i)))∧
      (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i)))≤flagMixed p q axis.flag:=by
  have hroot (A:MvPolynomial (Fin 3) K) (ha: ∀i,A∈P i):
      ∀i,RCN093.flagEvaluation K (P i) lam mu nu (flagAlgHom_p19 lam mu nu A)=0:=by
    intro i
    rw [ACO]
    change A∈RingHom.ker (RCN002.coordinateEvaluation K (P i)).toRingHom
    rw [RCN002.coordinateEvaluation_ker]
    exact ha i
  exact DIH K axis lam mu nu
    (fun i=>RCN002.CoordinateField K (P i)) (fun i=>RCN093.flagEvaluation K (P i) lam mu nu)
    ht (fun i=>CWN K (P i) axis lam mu nu (ht i))
    (AVC K P hinj lam mu nu)
    B H hB hH hrel (hroot B hBmem) (hroot H hHmem) p q hp hq
end
end YL
end MergedPart3
section MergedPart4
namespace BJX
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN042 RCN046 RCN093 RCN095 RCN114 RCN116 RCN237 RCN264 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open JS YL
theorem ESR
    (K:Type) [Field K] [IsAlgClosed K] (axis:Axis) (lam mu nu:K)
    {I:Type} [Fintype I]
    (P:I→Ideal (MvPolynomial (Fin 3) K)) [∀i,(P i).IsPrime]
    (hinj:Function.Injective P)
    (hgate: ∀i,∀ht:Transcendental K
        (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))),
      (letI:Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
        (RCN022.elementEmbedding K (RCN002.CoordinateField K (P i))
          (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i)))∧
      (letI:Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
        (RCN022.elementEmbedding K (RCN002.CoordinateField K (P i))
          (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K (P i))))
    (B H:MvPolynomial (Fin 3) K) (hB:B≠0) (hH:H≠0) (hrel:IsRelPrime B H)
    (hBmem: ∀i,B∈P i) (hHmem: ∀i,H∈P i)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q H):
    (∑ i,RCN344.coordinateDegree K (RCN002.CoordinateField K (P i))
      (RCN042.coordinateOfGate (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
        (hgate i)))≤flagMixed p q axis.flag:=by
  classical
  rw [RCN042.sum_coordinateOfGate_degree_eq]
  exact (BSL K axis lam mu nu
    (fun i:{i//Transcendental K
      (RCN093.flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))}=>P i.1)
    (fun i j hij=>Subtype.ext (hinj hij)) (fun i=>i.2)
    B H hB hH hrel (fun i=>hBmem i.1) (fun i=>hHmem i.1) p q hp hq).2
variable {K:Type} [Field K] [IsAlgClosed K]
    {G T R:MvPolynomial (Fin 3) K}
def BKX
    (base: ∀C:RCN264.RegularComponent K G T R,RCN341.SeparableLiteralCoordinate C.1)
    (hY: ∀C:RCN264.RegularComponent K G T R,RCN037.LiteralProjectionGate C 0)
    (hZ: ∀C:RCN264.RegularComponent K G T R,RCN037.LiteralProjectionGate C 2)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
    (D:AOH base hY hZ hderiv)
    (B H:MvPolynomial (Fin 3) K) (hB:B≠0) (hH:H≠0) (hrel:IsRelPrime B H)
    (hBmem: ∀C:RCN264.RegularComponent K G T R,B∈C.1)
    (hHmem: ∀C:RCN264.RegularComponent K G T R,H∈C.1)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q H):
    EE base p q:=by
  classical
  let x (axis:Axis) (C:RCN264.RegularComponent K G T R):=
    RCN093.flagEvaluation K C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis:Axis) (C:RCN264.RegularComponent K G T R)
      (ht:Transcendental K (x axis C)):
      (letI:Algebra (RatFunc K) (RCN002.CoordinateField K C.1):=
        (RCN022.elementEmbedding K (RCN002.CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (RCN002.CoordinateField K C.1))∧
      (letI:Algebra (RatFunc K) (RCN002.CoordinateField K C.1):=
        (RCN022.elementEmbedding K (RCN002.CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K C.1)):=by
    cases axis with
    | z=>
      have hz:Transcendental K (coordinate K C.1 2):=by
        simpa only [x,Axis.order,RCN125.zOrder_p19,Equiv.swap_apply_left,RCN093.flagEvaluation_X_two] using ht
      have he:=RCN116.elementEmbedding_congr ht hz (by
        simp only [x,Axis.order,RCN125.zOrder_p19,Equiv.swap_apply_left,RCN093.flagEvaluation_X_two])
      rw [he]
      exact hZ C hz
    | u=>
      have hu:Transcendental K (affineU K C.1 D.lam):=by
        simpa only [x,Axis.order,RCN125.uOrder_p19,Equiv.refl_apply,RCN093.flagEvaluation_X_zero] using ht
      have he:=RCN116.elementEmbedding_congr ht hu (by
        simp only [x,Axis.order,RCN125.uOrder_p19,Equiv.refl_apply,RCN093.flagEvaluation_X_zero])
      rw [he]
      exact D.uGate C hu
    | v=>
      have he:=RCN116.elementEmbedding_congr ht (D.GN C) (by
        simp only [x,Axis.order,RCN125.vOrder_p19,Equiv.swap_apply_left,RCN093.flagEvaluation_X_one])
      rw [he]
      exact ⟨D.allFinite C,D.allSeparable C⟩
  let projection (axis:Axis) (C:RCN264.RegularComponent K G T R):=
    RCN042.coordinateOfGate (x axis C) (gate axis C)
  have hsum (axis:Axis):
      (∑ C:RCN264.RegularComponent K G T R,
        RCN344.coordinateDegree K (RCN002.CoordinateField K C.1) (projection axis C))≤flagMixed p q axis.flag:=
    ESR K axis D.lam D.mu (D.mu*D.lam)
      (fun C:RCN264.RegularComponent K G T R=>C.1)
      (fun _ _ h=>Subtype.ext h) (gate axis) B H hB hH hrel hBmem hHmem p q hp hq
  have hz (C:RCN264.RegularComponent K G T R):
      RCN344.coordinateValue K (RCN002.CoordinateField K C.1) (projection .z C)=coordinate K C.1 2:=by
    simp only [projection,RCN042.coordinateOfGate_value,x,Axis.order,RCN125.zOrder_p19,
      Equiv.swap_apply_left,RCN093.flagEvaluation_X_two]
  have hu (C:RCN264.RegularComponent K G T R):
      RCN344.coordinateValue K (RCN002.CoordinateField K C.1) (projection .u C)=affineU K C.1 D.lam:=by
    simp only [projection,RCN042.coordinateOfGate_value,x,Axis.order,RCN125.uOrder_p19,
      Equiv.refl_apply,RCN093.flagEvaluation_X_zero]
  have hv (C:RCN264.RegularComponent K G T R):
      RCN344.coordinateValue K (RCN002.CoordinateField K C.1) (projection .v C)=affineV K C.1 D.mu (D.mu*D.lam):=by
    simp only [projection,RCN042.coordinateOfGate_value,x,Axis.order,RCN125.vOrder_p19,
      Equiv.swap_apply_left,RCN093.flagEvaluation_X_one]
  refine {
    zProjection:=projection .z
    yzProjection:=projection .u
    NV:=projection .v
    zValue:=hz
    ACE:= ?_
    zPole_eq:= ?_
    yzPole_eq:= ?_
    allPole_eq:= ?_
    ARJ:=hsum .z
    ALE:=hsum .u
    AQB:=hsum .v}
  · intro C
    rw [hv C]
    exact D.GN C
  · intro C v
    rw [UC]
    change _=RCN187.poleOrder v.val _
    rw [hz C]
  · intro C v
    rw [QD]
    change _=RCN187.poleOrder v.val _
    rw [hu C,←D.uValue C]
    exact (D.uPole C v).symm
  · intro C v
    rw [SF]
    change _=RCN187.poleOrder v.val _
    rw [hv C,←D.allValue C]
    exact (D.allPole C v).symm
end
end BJX
end MergedPart4
section MergedPart5
namespace DC
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open BAI RCN234 RCN156
variable {K:Type} [Field K]
instance carrierSpanPrime (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]:
    (Ideal.span ({F}:Set (MvPolynomial (Fin 4) K))).IsPrime:=
  Ideal.isPrime_span_singleton_of_prime (Fact.out:Irreducible F).prime
abbrev CarrierRing (F:MvPolynomial (Fin 4) K):=
  MvPolynomial (Fin 4) K ⧸ Ideal.span ({F}:Set (MvPolynomial (Fin 4) K))
abbrev CarrierField (F:MvPolynomial (Fin 4) K):=FractionRing (CarrierRing F)
def carrierMap (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]:
    MvPolynomial (Fin 4) K→+*CarrierField F:=
  (algebraMap (CarrierRing F) (CarrierField F)).comp (Ideal.Quotient.mk _)
theorem TY (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P:MvPolynomial (Fin 4) K):carrierMap F P=0 ↔ F∣P:=by
  change algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P)=0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (CarrierRing F) (CarrierField F)),
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
theorem DQY (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]:
    carrierMap F F=0:=(TY F F).mpr (dvd_refl F)
instance carrierField_charP (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (p:ℕ) [CharP K p]:CharP (CarrierField F) p:=
  charP_of_injective_ringHom ((carrierMap F).comp MvPolynomial.C).injective p
theorem ALO (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    [CharP K 2130706433] (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433):
    carrierMap F (2*RCN313.polyH K F)≠0:=by
  have hh:carrierMap F (RCN313.polyH K F)≠0:=by
    intro hz
    exact RCN267.equation_not_dvd_R_derivative F 2130706433 hpos hsmall
      ((TY F _).mp hz)
  rw [map_mul,map_ofNat]
  apply mul_ne_zero _ hh
  exact (CharP.cast_eq_zero_iff (CarrierField F) 2130706433 2).not.mpr (by decide)
theorem AKB
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (cap:ℕ)
    (hshape: ∀e ∈ P.support,e 1+e 2+e 3+e 4≤cap)
    (hF:cap<wt RCN156.residualTotalWeights F):(SecondJetCoefficients.asS P).map (carrierMap F)≠0:=by
  have hh:=SecondJetTotalAvoidance.leading_not_dvd P hP F cap hshape hF
  have hl:carrierMap F (SecondJetCoefficients.asS P).leadingCoeff≠0:=by
    exact fun hz=>hh.2 ((TY F _).mp hz)
  exact (SecondJetCoefficientAvoidance.map_degree_preserved (SecondJetCoefficients.asS P) (carrierMap F) hl).1
end
end DC
end MergedPart5
section MergedPart6
namespace BDQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
open scoped BigOperators
open RCN002 RCN037 RCN042 RCN046 RCN072 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN341 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open AUK BD BFL
open MovingFiberThreeSources6811 (direction weight)
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local notation "Poly3" =>MvPolynomial (Fin 3) Ω
theorem DRC
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F)
    (carrier:Poly3) (p:FlagDegree)
    (hcarrier:carrier≠0) (hcarrierF:carrier∣surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (h2:(2:Ω)≠0) (hfact:(S.k.factorial:Ω)≠0)
    (Q A:Poly3) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (R:Poly3)
    (hH: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      surfaceMap phi (RCN313.polyH K F)∉C.1)
    (hL: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      S.leading phi∉C.1)
    (base: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      RCN341.SeparableLiteralCoordinate C.1)
    (pNew qNew:FlagDegree) (unit:EE base pNew qNew):
    S.d*(∑ C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω C.1) (unit.zProjection C))≤
      flagMixed p unitZFlag S.flag:=by
  classical
  let H:=surfaceMap phi (RCN313.polyH K F)
  let M:=RCN207.movingEquation H (surfaceMap phi (RCN313.polyG K F)) Q A target
  let Family:=RCN264.RegularComponent Ω carrier M R
  let forget (C:Family):RCN264.RegularComponent Ω carrier M (H*S.leading phi):=
    ⟨C.1,(AJF Ω).mpr ⟨AAS Ω carrier M R C,by
      intro hz
      exact ((inferInstance:C.1.IsPrime).mem_or_mem hz).elim (hH C) (hL C)⟩⟩
  have hinj:Function.Injective forget:=by
    intro C D h
    exact Subtype.ext (congrArg (fun C0:RCN264.RegularComponent Ω carrier M (H*S.leading phi)=>C0.1) h)
  let Ext:=AlgebraicClosure (RatFunc Ω)
  letI:Algebra Ω Ext:=((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI:SMul (RatFunc Ω) Ext:=(inferInstance:Algebra (RatFunc Ω) Ext).toSMul
  letI:SMul Ω Ext:=(inferInstance:Algebra Ω Ext).toSMul
  letI:IsScalarTower Ω (RatFunc Ω) Ext:=by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI:CharP Ext c:=by infer_instance
  have h2e:(2:Ext)≠0:=by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfe:(S.k.factorial:Ext)≠0:=by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne hfact
  exact BIQ (E:=Ext) phi F carrier p unitZFlag hcarrier hcarrierF hflag
    linearZ linearZ_flag c (by omega) (by simpa [unitZFlag] using hunit)
    S.P S.B S.U S.T S.s S.k S.n0 S.hS S.hshape S.hBU S.hUT S.hdn S.hB S.hn S.hdiv
    h2e hfe Q A target hQ hA forget hinj unit.zProjection unit.zValue
end
end BDQ
end MergedPart6
section MergedPart7
namespace BHF
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN046 RCN095 RCN264 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
variable {K:Type} [Field K]
    {G M R:MvPolynomial (Fin 3) K}
def forgetExtra (L:MvPolynomial (Fin 3) K)
    (C:RCN264.RegularComponent K G M (R*L)):RCN264.RegularComponent K G M R:=by
  classical
  exact ⟨C.1,(AJF K).mpr ⟨AAS K G M (R*L) C,by
    intro hz
    exact _Q6 K G M (R*L) C (C.1.mul_mem_right L hz)⟩⟩
theorem APC (L:MvPolynomial (Fin 3) K):
    Function.Injective (forgetExtra (G:=G) (M:=M) (R:=R) L):=by
  intro C D h
  exact Subtype.ext (congrArg (fun C0:RCN264.RegularComponent K G M R=>C0.1) h)
theorem GVE (L:MvPolynomial (Fin 3) K)
    (C:RCN264.RegularComponent K G M (R*L)):L∉C.1:=by
  intro hz
  exact _Q6 K G M (R*L) C (C.1.mul_mem_left R hz)
theorem BNI {I J:Type} [Fintype I] [Fintype J]
    (f:I→J) (hf:Function.Injective f) (v:J→ℕ):
    (∑ i,v (f i))≤∑ j,v j:=by
  classical
  letI:DecidableEq J:=Classical.decEq J
  calc
    _= ∑ j ∈ Finset.univ.image f,v j:=(Finset.sum_image (fun _ _ _ _ h=>hf h)).symm
    _≤_:=Finset.sum_le_sum_of_subset (Finset.subset_univ _)
def CQW [IsAlgClosed K]
    (base: ∀C:RCN264.RegularComponent K G M R,RCN341.SeparableLiteralCoordinate C.1)
    (p q:FlagDegree) (unit:EE base p q)
    (L:MvPolynomial (Fin 3) K):
    EE (fun C=>base (forgetExtra L C)) p q where
  zProjection:=fun C=>unit.zProjection (forgetExtra L C)
  yzProjection:=fun C=>unit.yzProjection (forgetExtra L C)
  NV:=fun C=>unit.NV (forgetExtra L C)
  zValue:=fun C=>unit.zValue (forgetExtra L C)
  ACE:=fun C=>unit.ACE (forgetExtra L C)
  zPole_eq:=fun C v=>unit.zPole_eq (forgetExtra L C) v
  yzPole_eq:=fun C v=>unit.yzPole_eq (forgetExtra L C) v
  allPole_eq:=fun C v=>unit.allPole_eq (forgetExtra L C) v
  ARJ:=(BNI (forgetExtra L) (APC L)
    (fun C=>RCN344.coordinateDegree K (RCN002.CoordinateField K C.1) (unit.zProjection C))).trans unit.ARJ
  ALE:=(BNI (forgetExtra L) (APC L)
    (fun C=>RCN344.coordinateDegree K (RCN002.CoordinateField K C.1) (unit.yzProjection C))).trans unit.ALE
  AQB:=(BNI (forgetExtra L) (APC L)
    (fun C=>RCN344.coordinateDegree K (RCN002.CoordinateField K C.1) (unit.NV C))).trans unit.AQB
open RCN084 RCN136 RCN207
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open BD BDQ
open MovingFiberThreeSources6811 (direction weight)
end
end BHF
end MergedPart7
section MergedPart10
namespace ALP
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN046 RCN093 RCN095 RCN116 RCN264 RCN341
open RCN095 renaming PolynomialInFlag → BI
open JS YL BJX
theorem DYQ
    {K E:Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (c:ℕ) [CharP K c] (h:Module.finrank K E<c):Algebra.IsSeparable K E:=by
  classical
  letI:DecidableEq K:=Classical.decEq K
  letI:DecidableEq E:=Classical.decEq E
  refine ⟨fun x=> ?_⟩
  exact (RCN364.WS c (minpoly K x) x
    (minpoly.ne_zero (IsIntegral.of_finite K x)) (minpoly.aeval K x)
    ((minpoly.natDegree_le x).trans_lt h)).2
theorem CNW
    {K:Type} [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis:Axis) (lam mu nu:K)
    (ht:Transcendental K (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H:MvPolynomial (Fin 3) K) (hB:B≠0) (hH:H≠0) (hrel:IsRelPrime B H)
    (hBmem:B∈P) (hHmem:H∈P)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q H)
    (c:ℕ) [CharP K c] (hsmall:flagMixed p q axis.flag<c):
    letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
      (RCN022.elementEmbedding K (RCN002.CoordinateField K P)
        (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
      Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=by
  letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
    (RCN022.elementEmbedding K (RCN002.CoordinateField K P)
      (RCN093.flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
  have hfamily:=BSL K axis lam mu nu (fun _:Unit=>P)
    (fun _ _ _=>Subsingleton.elim _ _) (fun _=>ht)
    B H hB hH hrel (fun _=>hBmem) (fun _=>hHmem) p q hp hq
  letI:FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P):=hfamily.1 ()
  have hdegree:Module.finrank (RatFunc K) (RCN002.CoordinateField K P)≤flagMixed p q axis.flag:=by
    simpa only [Fintype.sum_unique] using hfamily.2
  exact ⟨inferInstance,DYQ c (hdegree.trans_lt hsmall)⟩
end
end ALP
end MergedPart10
section MergedPart11
namespace AIO
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open RCN135
variable (K:Type) [Field K]
theorem ANT:
    RCN135.coefficientEmbedding K=algebraMap K (GenericField K):=by
  ext c
  change algebraMap (RationalBase K) (GenericField K)
    (algebraMap (Polynomial K) (RationalBase K) (algebraMap K (Polynomial K) c))=
      algebraMap K (GenericField K) c
  rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RationalBase K),
    ←IsScalarTower.algebraMap_apply K (RationalBase K) (GenericField K)]
def DSO:RatFunc K→ₐ[K] GenericField K:=
  (IsScalarTower.toAlgHom K (RationalBase K) (GenericField K)).comp
    (RatFunc.toFractionRingAlgEquiv K K).toAlgHom
theorem EFR:
    DSO K (RCN202.rationalVariable K)=RCN135.initialCoordinate K:=by
  change algebraMap (RationalBase K) (GenericField K)
    ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X).toFractionRing)=_
  rw [←RatFunc.ofFractionRing_algebraMap]
  rfl
abbrev CPM:Algebra (RatFunc K) (GenericField K):=
  (DSO K).toRingHom.toAlgebra
theorem target_tower:
    letI:=CPM K
    IsScalarTower K (RatFunc K) (GenericField K):=by
  letI:=CPM K
  exact IsScalarTower.of_algebraMap_eq fun c=>((DSO K).commutes c).symm
theorem FES:
    letI:=CPM K
    algebraMap (RatFunc K) (GenericField K) (RCN202.rationalVariable K)=RCN135.initialCoordinate K:=
  EFR K
end
end AIO
end MergedPart11
section MergedPart12
namespace AFA
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD AIO
open MovingFiberThreeSources6811 (direction weight)
variable {K:Type} [Field K]
local notation "Omega" =>GenericField K
local notation "OmegaT" =>GenericField (GenericField K)
local notation "phi" =>RingHom.comp (RCN135.coefficientEmbedding (GenericField K)) (RCN135.polynomialEmbedding K)
local notation "lift" =>MvPolynomial.map (RCN135.coefficientEmbedding (GenericField K))
local instance:Algebra (RatFunc Omega) OmegaT:=CPM Omega
local instance:IsScalarTower Omega (RatFunc Omega) OmegaT:=target_tower Omega
def baseCarrier (F:MvPolynomial (Fin 4) K):=surfaceMap (RCN135.polynomialEmbedding K) F
def baseH (F:MvPolynomial (Fin 4) K):=surfaceMap (RCN135.polynomialEmbedding K) (polyH K F)
def baseG (F:MvPolynomial (Fin 4) K):=surfaceMap (RCN135.polynomialEmbedding K) (polyG K F)
def targetCut (n:ℕ) (coeff:Fin (n+1)→MvPolynomial (Fin 3) Omega)
    (Q A:MvPolynomial (Fin 3) Omega):MvPolynomial (Fin 3) OmegaT:=
  RCN207.eliminatedCut n (fun j=>lift (coeff j)) (lift Q) (lift A) (RCN135.initialCoordinate Omega)
theorem EQP (P:MvPolynomial (Fin 3) Omega):RCN208.scalarPolynomialMap Omega OmegaT P=lift P:=by
  rw [RCN208.scalarPolynomialMap,←ANT Omega]
theorem FGH
    (F:MvPolynomial (Fin 4) K) (a b s n:ℕ) (center:FlagDegree)
    (coeff:Fin (n+1)→MvPolynomial (Fin 3) Omega) (flags:Fin (n+1)→FlagDegree)
    (hH:RCN095.PolynomialInFlag ⟨a,b+1,s+1⟩ (baseH F))
    (hG:RCN095.PolynomialInFlag ⟨a,b,s+3⟩ (baseG F))
    (hcoeff: ∀j,RCN095.PolynomialInFlag (flags j) (coeff j))
    (heq: ∀j,flags j+(n-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
      j.val • (⟨a,b,s+3⟩:FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
    (Q A:MvPolynomial (Fin 3) Omega)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A):
    RCN095.PolynomialInFlag (center+n • (⟨a,b+1,s+2⟩:FlagDegree)) (targetCut n coeff Q A):=by
  have hh:=(DSK (E:=OmegaT) a b s n center (baseH F) (baseG F) Q A coeff flags
    hH hG hQ hA hcoeff heq).2
  simpa only [fiberCut,EQP,FES,targetCut] using hh
end
end AFA
end MergedPart12
section MergedPart13
namespace FN
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open BD DC
open MovingFiberThreeSources6811 (direction weight)
variable {K E:Type} [Field K] [Field E]
theorem ABW (P:SecondJetSupport.Poly (K:=K)):
    (SecondJetCoefficients.asS P).natDegree=P.degreeOf 1:=by
  change (MvPolynomial.finSuccEquiv K 4 (MvPolynomial.rename (Equiv.swap (0:Fin 5) 1) P)).natDegree=_
  rw [MvPolynomial.natDegree_finSuccEquiv]
  simpa only [Equiv.swap_apply_right] using
    (MvPolynomial.degreeOf_rename_of_injective (p:=P) (Equiv.swap (0:Fin 5) 1).injective 1)
theorem EAO
    (J:SecondJetSupport.Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (phi:MvPolynomial (Fin 4) K→+*E) (hker: ∀P,phi P=0 ↔ F∣P)
    (hH:phi (2*RCN313.polyH K F)≠0)
    (m s B U T:ℕ) (hm:0<m) (hs:J.degreeOf 1=s)
    (h2s:2*s≤B) (hBU:B≤U) (hUT:U≤T)
    (hshape: ∀e ∈ J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤T)
    (hroot:((SecondJetCoefficients.asS J).map phi).rootMultiplicity (SecondJetCarrierDichotomy.ratio phi F)=m):
    ∃S:MovingFiberThreeSources6811.Source F,S.P=J∧S.d=m∧
      S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s:=by
  have hne:(SecondJetCoefficients.asS J).map phi≠0:=by
    intro hz
    rw [hz,Polynomial.rootMultiplicity_zero] at hroot
    omega
  have hpow:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi F))^m ∣ (SecondJetCoefficients.asS J).map phi:=by
    rw [←hroot]
    exact Polynomial.pow_rootMultiplicity_dvd _ _
  have hms:m≤s:=by
    have hh:=Polynomial.natDegree_le_of_dvd hpow hne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq ((ABW J).trans hs))
  have hS: ∀e ∈ J.support,e 1≤s:=MvPolynomial.degreeOf_le_iff.mp hs.le
  have hdiv (d:ℕ) (hd:d≤m-1):F∣SecondJetClearedHelper.helper J F (s-d) d:=by
    apply (hker _).mp
    rw [SecondJetCarrierDichotomy.mapped_helper J F phi s d hS hH]
    have hz:((Polynomial.derivative)^[d] ((SecondJetCoefficients.asS J).map phi)).eval (SecondJetCarrierDichotomy.ratio phi F)=0:=
      Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot];omega)
    rw [hz,mul_zero]
  let S:MovingFiberThreeSources6811.Source F:={
    P:=J,B:=B,U:=U,T:=T,s:=s,k:=m-1,n0:=s
    hS:=hS
    hshape:=hshape
    hBU:=hBU
    hUT:=hUT
    hdn:=by omega
    hB:=by omega
    hn:=by rw [ABW,hs]
    hdiv:=hdiv}
  have hd:S.d=m:=by dsimp [S,MovingFiberThreeSources6811.Source.d];omega
  exact ⟨S,rfl,hd,by simp only [MovingFiberThreeSources6811.Source.flag,hd];rfl⟩
theorem DBC [CharP K 2130706433]
    (J:SecondJetSupport.Poly (K:=K)) (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (m s B U T:ℕ) (hm:0<m) (hs:J.degreeOf 1=s)
    (h2s:2*s≤B) (hBU:B≤U) (hUT:U≤T)
    (hshape: ∀e ∈ J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤T)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=m):
    ∃S:MovingFiberThreeSources6811.Source F,S.P=J∧S.d=m∧S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s:=
  EAO J F (carrierMap F) (TY F)
    (ALO F hpos hsmall) m s B U T hm hs h2s hBU hUT hshape hroot
end
end FN
end MergedPart13
section MergedPart14
namespace LK
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN137 CW
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open AID
open SecondJetCoefficients (liftExponent)
variable {K E:Type} [Field K] [Field E]
local notation "SecondJetSupport.Poly" =>MvPolynomial (Fin 5) K
def UniqueOwner (ev:SecondJetSupport.Poly→+*E) (J P:SecondJetSupport.Poly):Prop:=
  ∀D,Irreducible D→D∣P→ev D=0→Associated D J
theorem CDE (ev:SecondJetSupport.Poly→+*E) (P J:SecondJetSupport.Poly)
    (hP:P≠0) (hJ:Irreducible J) (hu:UniqueOwner ev J P):
    ∃e Q,P=J^e*Q∧ev Q≠0:=by
  obtain ⟨e,Q,hnot,hEq⟩:=WfDvdMonoid.max_power_factor hP hJ
  have hQ:Q≠0:=by intro hz;apply hP;rw [hEq,hz,mul_zero]
  refine ⟨e,Q,hEq,?_⟩
  intro hz
  obtain ⟨D,hD,hDz⟩:=RCN137.exists_normalizedFactorSet_zero ev Q hQ hz
  have hd:=RCN137.normalizedFactorSet_spec Q D hD
  have hDP:D∣P:=hd.2.trans (by rw [hEq];exact dvd_mul_left _ _)
  exact hnot (((hu D hd.1 hDP hDz).symm.dvd).trans hd.2)
theorem EYA (ev:SecondJetSupport.Poly→+*E) (P Q:SecondJetSupport.Poly)
    (hP:P≠0) (hQ:Q≠0) (hz:ev P=0):
    ∃J,Irreducible J∧J∣P∧ev J=0∧
      ((UniqueOwner ev J P∧UniqueOwner ev J Q∧
          (∃e R,P=J^e*R∧ev R≠0)∧(∃e R,Q=J^e*R∧ev R≠0))∨
        ∃D,Irreducible D∧(D∣P∨D∣Q)∧ev D=0∧IsRelPrime J D):=by
  classical
  obtain ⟨J,hJ,hJz⟩:=RCN137.exists_normalizedFactorSet_zero ev P hP hz
  have hj:=RCN137.normalizedFactorSet_spec P J hJ
  refine ⟨J,hj.1,hj.2,hJz,?_⟩
  rcases Classical.em (∃D,Irreducible D∧(D∣P∨D∣Q)∧ev D=0∧ ¬Associated D J) with hex | hex
  · right
    obtain ⟨D,hD,hd,hzD,hnot⟩:=hex
    refine ⟨D,hD,hd,hzD,hj.1.isRelPrime_iff_not_dvd.mpr ?_⟩
    intro hdiv
    exact hnot (hj.1.associated_of_dvd hD hdiv).symm
  · have hp:UniqueOwner ev J P:=by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inl hd,hzD,hn⟩
    have hq:UniqueOwner ev J Q:=by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inr hd,hzD,hn⟩
    exact Or.inl ⟨hp,hq,CDE ev P J hP hj.1 hp,
      CDE ev Q J hQ hj.1 hq⟩
def QC (phi:MvPolynomial (Fin 4) K→+*E):SecondJetSupport.Poly→+*Polynomial E:=
  (Polynomial.mapRingHom phi).comp (SecondJetCoefficients.asS (K:=K)).toRingHom
def NT (phi:MvPolynomial (Fin 4) K→+*E) (z:E):SecondJetSupport.Poly→+*E:=
  (Polynomial.evalRingHom z).comp (QC phi)
end
end LK
end MergedPart14
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace GZ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open MvPolynomial
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open ARW
open BD DC
open MovingFiberThreeSources6811 (direction weight)
open RCN234 RCN156
variable {K N:Type} [Field K] [Fintype N]
def Profile {F:MvPolynomial (Fin 4) K} (S:MovingFiberThreeSources6811.Source F) (B U T s k n0:ℕ):Prop:=
  S.B=B∧S.U=U∧S.T=T∧S.s=s∧S.k=k∧S.n0=n0
theorem AHY (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F):S.P≠0:=by
  intro hz
  have hh:=S.hn
  rw [hz,map_zero,Polynomial.natDegree_zero] at hh
  have hd:=S.hdn
  omega
theorem ADG [CharP K 2130706433]
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (S:MovingFiberThreeSources6811.Source F)
    (hT:S.T<wt RCN156.residualTotalWeights F) (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (hk:S.k<2130706433):
    (SecondJetCoefficients.asS S.P).map (carrierMap F)≠0∧
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^S.d ∣
        (SecondJetCoefficients.asS S.P).map (carrierMap F):=by
  have hn:=AKB F S.P (AHY F S) S.T
    (fun e he=>(S.hshape e he).2.2) hT
  exact ⟨hn,SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd S.P F (carrierMap F)
    S.s S.k S.hS (DQY F) (ALO F hpos hsmall) hn
    (SecondJetOwnShape.factorial_ne S.k hk) S.hdiv⟩
end
end GZ
end MergedPart0
section MergedPart1
namespace AZX
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial
open SecondJetCoefficients (liftExponent)
open CW DJ BD
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open MovingFiberThreeSources6811 (direction weight)
open DC FN LK
open GZ
open RCN234 RCN156
variable {K:Type} [Field K]
theorem source_caps (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F):
    weightedTotalDegree slopeWeights S.P≤S.B∧weightedTotalDegree HA S.P≤S.U∧
      weightedTotalDegree Koala6831Ordinary.totalWeights S.P≤S.T∧S.P.degreeOf 1≤S.s:=by
  refine ⟨Finset.sup_le ?_,Finset.sup_le ?_,Finset.sup_le ?_,MvPolynomial.degreeOf_le_iff.mpr S.hS⟩
  · intro e he
    simpa [JW,slopeWeights,Nat.mul_comm] using (S.hshape e he).1
  · intro e he
    simpa [JW,HA] using (S.hshape e he).2.1
  · intro e he
    simpa [JW,Koala6831Ordinary.totalWeights] using (S.hshape e he).2.2
end
end AZX
end MergedPart1
section MergedPart2
namespace MI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open MvPolynomial
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open SecondJetHelperWeights renaming cleared_weight → BUF
open FN DC BAI
open RCN234 RCN156
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 4) K
def linearH (J:SecondJetSupport.Poly (K:=K)):Poly:=(SecondJetCoefficients.asS J).coeff 1
def linearG (J:SecondJetSupport.Poly (K:=K)):Poly:= -2*(SecondJetCoefficients.asS J).coeff 0
def flow (H G:Poly):Derivation K Poly Poly:=
  H • RCN055.horizontalDerivation+G • MvPolynomial.pderiv (2:Fin 4)
theorem flow_apply (H G P:Poly):
    flow H G P=H*(MvPolynomial.pderiv 0 P+MvPolynomial.X 2*MvPolynomial.pderiv 1 P)+
      G*MvPolynomial.pderiv 2 P:=by
  simp only [flow,RCN055.horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul]
theorem GUL (J:SecondJetSupport.Poly (K:=K)) (F:Poly):
    SecondJetClearedHelper.helper J F 1 0=linearH J*RCN313.polyG K F-linearG J*RCN313.polyH K F:=by
  change (∑ j:Fin 2,(SecondJetCoefficients.asS J).coeff j.val*(2*RCN313.polyH K F)^(1-j.val)*(RCN313.polyG K F)^j.val)=_
  rw [Fin.sum_univ_two]
  norm_num [linearH,linearG]
  ring
theorem CQC (J:SecondJetSupport.Poly (K:=K)) (B U T:ℕ)
    (hshape: ∀e ∈ J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤T):
    (wt RCN156.residualSWeights (linearH J)≤B-2∧wt RCN156.residualYSWeights (linearH J)≤U-1∧
      wt RCN156.residualTotalWeights (linearH J)≤T-1)∧
    (wt RCN156.residualSWeights (linearG J)≤B∧wt RCN156.residualYSWeights (linearG J)≤U∧
      wt RCN156.residualTotalWeights (linearG J)≤T):=by
  have hh:=SecondJetHelperWeights.derivative_coefficient_weights J B U T 0 1 hshape
  have hg:=SecondJetHelperWeights.derivative_coefficient_weights J B U T 0 0 hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hh hg
  have hscale (w:Fin 4→ℕ):wt w (linearG J)≤wt w ((SecondJetCoefficients.asS J).coeff 0):=by
    have hb:=wt_mul_le w (-2:Poly) ((SecondJetCoefficients.asS J).coeff 0)
    have ht:wt w (2:Poly)=0:=wt_natCast w 2
    rw [wt_neg,ht,zero_add] at hb
    exact hb
  exact ⟨hh,⟨(hscale _).trans hg.1,(hscale _).trans hg.2.1,(hscale _).trans hg.2.2⟩⟩
theorem CQR
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hs:J.degreeOf 1=1)
    (F:Poly) [Fact (Irreducible F)] (T:ℕ)
    (hshape: ∀e ∈ J.support,e 1+e 2+e 3+e 4≤T) (hFT:T<wt RCN156.residualTotalWeights F):
    carrierMap F (linearH J)≠0:=by
  have hh:=SecondJetTotalAvoidance.leading_not_dvd J hJ F T hshape hFT
  have he:linearH J=(SecondJetCoefficients.asS J).leadingCoeff:=by
    rw [Polynomial.leadingCoeff,ABW,hs]
    rfl
  rw [he]
  exact fun hz=>hh.2 ((TY F _).mp hz)
theorem EWO [CharP K 2130706433]
    (J:SecondJetSupport.Poly (K:=K)) (hs:J.degreeOf 1=1)
    (F:Poly) [Fact (Irreducible F)]
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).eval (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0):
    F∣linearH J*RCN313.polyG K F-linearG J*RCN313.polyH K F:=by
  rw [←GUL]
  exact EEI J F (carrierMap F) (TY F) 1
    (MvPolynomial.degreeOf_le_iff.mp hs.le) (ALO F hpos hsmall) hroot
theorem flow_carrier (F H G:Poly):
    flow H G F= -(H*RCN313.polyG K F-G*RCN313.polyH K F):=by
  rw [flow_apply]
  unfold RCN313.polyG RCN313.polyH
  ring
theorem EUY (F H G:Poly)
    (hcross:F∣H*RCN313.polyG K F-G*RCN313.polyH K F):
    ∀P,F∣P→F∣flow H G P:=by
  intro P hP
  obtain ⟨Q,rfl⟩:=hP
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
  apply dvd_add
  · exact dvd_mul_right _ _
  · apply dvd_mul_of_dvd_right
    rw [flow_carrier]
    exact dvd_neg.mpr hcross
end
end MI
end MergedPart2
section MergedPart3
namespace NA
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313 MI
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 4) K
def step (H G:Poly) (n:ℕ) (P:Poly):Poly:=
  clearedStep (2*n) P (pderiv 0 P) (pderiv 1 P) (pderiv 2 P)
    (MvPolynomial.X 2) G H (pderiv 0 H) (pderiv 1 H) (pderiv 2 H)
def numerators (H G:Poly):ℕ→Poly
  | 0=>MvPolynomial.X 1
  | n+1=>step H G n (numerators H G n)
theorem step_eq (H G P:Poly) (n:ℕ):
    step H G n P=H*flow H G P-(2*n:ℕ)*P*flow H G H:=by
  simp only [step,clearedStep,flow_apply]
  ring
theorem GLN (F:Poly) (n:ℕ):
    numerators (polyH K F) (polyG K F) n=numerator K F n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [numerators,ih,RCN313.numerator_succ]
    rfl
theorem EFT
    {E:Type} [Field E] [Algebra K E]
    (D:Derivation K E E) (phi:Poly→+*E) (H G:Poly) (hH:phi H≠0)
    (hchain: ∀P,D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P)) (n:ℕ):
    D^[n] (phi (MvPolynomial.X 1))=phi (numerators H G n)*(phi H)⁻¹^(2*n):=by
  induction n with
  | zero=>simp [numerators]
  | succ n ih=>
    rw [Function.iterate_succ_apply',ih,numerators,step,RCN313.map_clearedStep]
    have hu:D ((phi H)⁻¹)= -((phi H)⁻¹^2*
        (phi (pderiv 0 H)+phi (MvPolynomial.X 2)*phi (pderiv 1 H)+
          phi G*(phi H)⁻¹*phi (pderiv 2 H))):=by
      rw [D.leibniz_inv,hchain H]
      simp only [smul_eq_mul,neg_mul]
    have hh:=RCN313.differentiated_fraction_step D (2*n)
      (phi (numerators H G n)) (phi (pderiv 0 (numerators H G n)))
      (phi (pderiv 1 (numerators H G n))) (phi (pderiv 2 (numerators H G n)))
      (phi (MvPolynomial.X 2)) (phi G) (phi H)
      (phi (pderiv 0 H)) (phi (pderiv 1 H)) (phi (pderiv 2 H)) ((phi H)⁻¹)
      (mul_inv_cancel₀ hH) (hchain _) hu
    simpa only [show 2*(n+1)=2*n+2 by omega] using hh
theorem FMK
    {E:Type} [Field E] [Algebra K E]
    (D:Derivation K E E) (phi:Poly→+*E) (H G H' G' :Poly)
    (hH:phi H≠0) (hH' :phi H'≠0)
    (hchain: ∀P,D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P))
    (hchain' : ∀P,D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G'*(phi H')⁻¹*phi (pderiv 2 P)) (n:ℕ):
    phi (numerators H G n)*(phi H')^(2*n)=phi (numerators H' G' n)*(phi H)^(2*n):=by
  have hh:=(EFT D phi H G hH hchain n).symm.trans
    (EFT D phi H' G' hH' hchain' n)
  have he:phi (numerators H G n)/(phi H)^(2*n)=
      phi (numerators H' G' n)/(phi H')^(2*n):=by
    simpa only [div_eq_mul_inv,inv_pow] using hh
  exact (div_eq_div_iff (pow_ne_zero _ hH) (pow_ne_zero _ hH')).mp he
end
end NA
end MergedPart3
section MergedPart4
namespace APK
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313
open MI NA DC
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 4) K
theorem GHZ (F:Poly):
    ∀P ∈ Ideal.span ({F}:Set Poly),flow (polyH K F) (polyG K F) P∈Ideal.span ({F}:Set Poly):=by
  intro P hP
  rw [Ideal.mem_span_singleton] at hP ⊢
  apply EUY F (polyH K F) (polyG K F) ?_ P hP
  rw [mul_comm (polyH K F),sub_self]
  exact dvd_zero F
def quotientD (F:Poly):Derivation K (CarrierRing F) (CarrierRing F):=
  RCN077.quotientDerivation (flow (polyH K F) (polyG K F)) _ (GHZ F)
def carrierD (F:Poly) [Fact (Irreducible F)]:Derivation K (CarrierField F) (CarrierField F):=
  (carrierMap F (polyH K F))⁻¹ •
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)
theorem FJY (F:Poly) [Fact (Irreducible F)]
    (hH:carrierMap F (polyH K F)≠0) (P:Poly):
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹*carrierMap F (pderiv 2 P):=by
  change (carrierMap F (polyH K F))⁻¹*
    RCN188.localizationDerivation (nonZeroDivisors (CarrierRing F)) (quotientD F)
      (algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P))=_
  rw [RCN188.localizationDerivation_algebraMap,quotientD,RCN077.quotientDerivation_mk]
  change (carrierMap F (polyH K F))⁻¹*carrierMap F (flow (polyH K F) (polyG K F) P)=_
  rw [flow_apply]
  simp only [map_add,map_mul]
  field_simp
theorem FYC (F:Poly) [Fact (Irreducible F)] (H G:Poly)
    (hOld:carrierMap F (polyH K F)≠0) (hNew:carrierMap F H≠0)
    (hcross:F∣H*polyG K F-G*polyH K F) (P:Poly):
    carrierD F (carrierMap F P)=carrierMap F (pderiv 0 P)+
      carrierMap F (MvPolynomial.X 2)*carrierMap F (pderiv 1 P)+
      carrierMap F G*(carrierMap F H)⁻¹*carrierMap F (pderiv 2 P):=by
  have hh:=(TY F _).mpr hcross
  simp only [map_sub,map_mul] at hh
  have he:carrierMap F (polyG K F)*(carrierMap F (polyH K F))⁻¹=
      carrierMap F G*(carrierMap F H)⁻¹:=by
    field_simp
    linear_combination hh
  rw [FJY F hOld P,he]
theorem FMD (F:Poly) [Fact (Irreducible F)] (H G:Poly)
    (hOld:carrierMap F (polyH K F)≠0) (hNew:carrierMap F H≠0)
    (hcross:F∣H*polyG K F-G*polyH K F) (n:ℕ):
    F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n:=by
  apply (TY F _).mp
  simp only [map_sub,map_mul,map_pow]
  have hh:=FMK (carrierD F) (carrierMap F) (polyH K F) (polyG K F)
    H G hOld hNew (FJY F hOld) (FYC F H G hOld hNew hcross) n
  rw [GLN] at hh
  linear_combination hh
theorem EJN [CharP K 2130706433]
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hs:J.degreeOf 1=1)
    (F:Poly) [Fact (Irreducible F)]
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (T:ℕ) (hshape: ∀e ∈ J.support,e 1+e 2+e 3+e 4≤T)
    (hFT:T<RCN234.wt RCN156.residualTotalWeights F)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0) (n:ℕ):
    F∣(linearH J)^(2*n)*numerator K F n-
      (polyH K F)^(2*n)*numerators (linearH J) (linearG J) n:=by
  have hH:carrierMap F (polyH K F)≠0:=by
    intro hz
    apply ALO F hpos hsmall
    rw [map_mul,hz,mul_zero]
  exact FMD F (linearH J) (linearG J) hH
    (CQR J hJ hs F T hshape hFT)
    (EWO J hs F hpos hsmall hroot) n
theorem GBA {R:Type} [CommRing R] [IsDomain R]
    (ev:Poly→+*R) (F H G:Poly) (n:ℕ) (hF:ev F=0)
    (hOld:IsUnit (ev (polyH K F))) (hNew:IsUnit (ev H))
    (hdiv:F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n):
    Associated (ev (numerator K F n)) (ev (numerators H G n)):=by
  have hh:=map_dvd ev hdiv
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,sub_eq_zero] at hh
  have he:ev (numerator K F n)*(ev H)^(2*n)=
      ev (numerators H G n)*(ev (polyH K F))^(2*n):=by simpa only [mul_comm] using hh
  apply associated_of_dvd_dvd
  · apply (hOld.pow (2*n)).dvd_mul_right.mp
    rw [←he]
    exact dvd_mul_right _ _
  · apply (hNew.pow (2*n)).dvd_mul_right.mp
    rw [he]
    exact dvd_mul_right _ _
end
end APK
end MergedPart4
section MergedPart5
namespace ANU
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN234 RCN156
open MI NA
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 4) K
theorem BMV
    (w:Fin 4→ℕ) (A P:Poly) (i:Fin 4) (c d:ℕ)
    (hA:wt w A≤d+w i) (hP:wt w P≤c):
    wt w (A*pderiv i P)≤c+d:=by
  by_cases hi:w i≤c
  · have hp:=wt_pderiv_le w P i c hP
    have hm:=wt_mul_le w A (pderiv i P)
    omega
  · have hz:pderiv i P=0:=RCN262.pderiv_eq_zero_of_wt_lt w P i (hP.trans_lt (by omega))
    rw [hz,mul_zero]
    simp [wt,MvPolynomial.weightedTotalDegree]
theorem flow_weight
    (w:Fin 4→ℕ) (H G P:Poly) (c h d:ℕ)
    (hH:wt w H≤h) (hG:wt w G≤d+w 2)
    (hx:h≤d+w 0) (hy:w 2+h≤d+w 1) (hP:wt w P≤c):
    wt w (flow H G P)≤c+d:=by
  have hRH:wt w (MvPolynomial.X 2*H)≤d+w 1:=by
    have hh:=wt_mul_le w (MvPolynomial.X 2) H
    rw [wt_X] at hh
    omega
  have h0:=BMV w H P 0 c d (hH.trans hx) hP
  have h1:=BMV w (MvPolynomial.X 2*H) P 1 c d hRH hP
  have h2:=BMV w G P 2 c d hG hP
  have he:flow H G P=H*pderiv 0 P+(MvPolynomial.X 2*H)*pderiv 1 P+G*pderiv 2 P:=by
    rw [flow_apply]
    ring
  rw [he]
  exact (wt_add_le w _ _).trans (max_le
    ((wt_add_le w _ _).trans (max_le h0 h1)) h2)
theorem step_weight
    (w:Fin 4→ℕ) (H G P:Poly) (c h d n:ℕ)
    (hH:wt w H≤h) (hG:wt w G≤d+w 2)
    (hx:h≤d+w 0) (hy:w 2+h≤d+w 1) (hP:wt w P≤c):
    wt w (step H G n P)≤c+(h+d):=by
  have hDP:=flow_weight w H G P c h d hH hG hx hy hP
  have hDH:=flow_weight w H G H h h d hH hG hx hy hH
  have hleft:=wt_mul_le w H (flow H G P)
  have hscale:=wt_mul_le w ((2*n:ℕ):Poly) P
  rw [wt_natCast,zero_add] at hscale
  have hright:=wt_mul_le w (((2*n:ℕ):Poly)*P) (flow H G H)
  rw [step_eq]
  exact (wt_sub_le w _ _).trans (max_le (by omega) (by omega))
theorem EAZ
    (w:Fin 4→ℕ) (H G:Poly) (h d:ℕ)
    (hH:wt w H≤h) (hG:wt w G≤d+w 2)
    (hx:h≤d+w 0) (hy:w 2+h≤d+w 1) (n:ℕ):
    wt w (numerators H G n)≤w 1+n*(h+d):=by
  induction n with
  | zero=>simp [numerators,wt_X]
  | succ n ih=>
    have hh:=step_weight w H G (numerators H G n) (w 1+n*(h+d)) h d n hH hG hx hy ih
    change wt w (step H G n (numerators H G n))≤_
    convert hh using 1;ring
end
end ANU
end MergedPart5
section MergedPart6
namespace BBN
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open NA APK
variable {K Ω R:Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" =>MvPolynomial (Fin 4) K
theorem EQX
    (phi:Polynomial K→+*Ω) (hphi:Function.Injective phi)
    (ev:MvPolynomial (Fin 3) Ω→+*R) (F H G:Poly) (n:ℕ)
    (hF:ev (surfaceMap phi F)=0)
    (hOld:IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew:IsUnit (ev (surfaceMap phi H)))
    (hdiv:F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n):
    Associated (ev (RCN086.globalTailCut phi F n)) (ev (surfaceMap phi (numerators H G n))):=by
  have hh:=GBA (ev.comp (surfaceMap phi)) F H G n hF hOld hNew hdiv
  have hu:IsUnit ((-phi Polynomial.X)^n):=
    isUnit_iff_ne_zero.mpr (RCN086.tail_scalar_ne_zero phi hphi n)
  have hu' :IsUnit (ev (MvPolynomial.C ((-phi Polynomial.X)^n))):=
    (hu.map (MvPolynomial.C:Ω→+*MvPolynomial (Fin 3) Ω)).map ev
  rw [RCN086.globalTailCut_eq,map_mul]
  exact (associated_mul_unit_left _ _ hu').trans hh
end
end BBN
end MergedPart6
section MergedPart7
namespace BQM
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN248
open RCN095 renaming PolynomialInFlag → BI
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN120 RCN313
open NA
theorem EXJ
    {R:Type*} [CommRing R] (J:Ideal R) [J.IsMaximal]
    (surface oldTail newTail a b:R) (n:ℕ) (hn:1≤n)
    (hsurface:surface∈J) (hb:b∉J)
    (hold:oldTail∈Ideal.span {surface} ⊔ J^n)
    (hcross:a*oldTail-b*newTail∈Ideal.span {surface}):
    newTail∈Ideal.span {surface} ⊔ J^n:=by
  let Q:=Ideal.span {surface} ⊔ J^n
  have hprod:b*newTail∈Q:=by
    have hc:a*oldTail-b*newTail∈Q:=
      (show Ideal.span {surface}≤Q from le_sup_left) hcross
    simpa only [sub_sub_cancel] using Q.sub_mem (Q.mul_mem_left a hold) hc
  exact RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
    surface newTail b J hsurface n hn hb hprod
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
theorem CXR
    {B:Type*} [CommRing B]
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (C:CM S)
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (f:MvPolynomial (Fin 4) K→+*B)
    (surface:B) (J:Ideal B) [J.IsMaximal]
    (hfactor:f (originalData_p19 S C).factor∈Ideal.span {surface})
    (hsurface:surface∈J)
    (hcontract:Ideal.comap f J=QP S C):
    f (numerators H G (RCN326.w+1))∈Ideal.span {surface} ⊔
      J^FO S (DN S hfirst) C:=by
  have hold:=AGK S hfirst C f surface
    (f (numerator K S.F (RCN326.w+1))) 1 J hfactor hsurface hcontract (mul_one _).symm
  have hF:f S.F∈Ideal.span {surface}:=by
    rw [(originalData_p19 S C).product,map_mul]
    exact (Ideal.span {surface}).mul_mem_right _ hfactor
  have hdiff:=(Ideal.span {surface}).mem_of_dvd (map_dvd f hcross) hF
  simp only [map_sub,map_mul,map_pow] at hdiff
  have hH:f (polyH K S.F)∉J:=by
    intro hh
    have hp:polyH K S.F∈QP S C:=by
      rw [←hcontract]
      exact hh
    exact RCN312.JX S C hp
  have hpow:(f (polyH K S.F))^(2*(RCN326.w+1))∉J:=by
    intro hh
    exact hH ((inferInstance:J.IsPrime).mem_of_pow_mem _ hh)
  exact EXJ J surface _ _ _ _ _
    (YW S hfirst C) hsurface hpow hold hdiff
theorem DIK
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    {A:Type} [Fintype A] (component:A→BXT S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht: ∀a,Transcendental (GenericField K)
      (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0))))
    (hfinite: ∀a,
      letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      FiniteDimensional (RatFunc (GenericField K)) (RCN002.CoordinateField (GenericField K) (component a).1))
    (hgen: ∀a,
      letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      IntermediateField.adjoin (RatFunc (GenericField K))
        ({RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 2)),
          RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
          Set (RCN002.CoordinateField (GenericField K) (component a).1))=⊤)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
    (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):
    RCN107.indexedFiberTail q hq
        (RCN113.flagPlaneMap_p19 (GenericField K) lam mu nu order
          (surfaceMap (RCN135.polynomialEmbedding K) (numerators H G (RCN326.w+1))))∈
      Ideal.span {RCN107.indexedFiberSurface q hq (TL S lam mu nu order)} ⊔
        RCN106.indexedFiberRelation component lam mu nu order ht q hq a^
          FO S (DN S hfirst) (component a.1):=by
  let D:=CPY S component lam mu nu order ht hfinite hgen q hq a
  letI:(RCN106.indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=D.relationMax
  exact CXR S hfirst (component a.1) H G hcross
    (BKL S lam mu nu order q hq)
    (RCN107.indexedFiberSurface q hq (TL S lam mu nu order)) _
    D.factor_mem D.surface_mem D.contract
end
end BQM
end MergedPart7
section MergedPart8
namespace AGT
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN249 RCN252
open RCN095 renaming PolynomialInFlag → BI
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN108 RCN109 RCN111 RCN112 RCN113
open RCN120 RCN125 RCN313 RCN333 RCN102
open NA BQM
theorem EJV
    {Ω:Type} [Field Ω] {F T R:MvPolynomial (Fin 3) Ω}
    (C:RCN264.RegularComponent Ω F T R)
    (lam mu nu:Ω) (order:Fin 3 ≃ Fin 3)
    (ht:Transcendental Ω
      (RCN093.flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF:Irreducible F) (N:MvPolynomial (Fin 3) Ω) (hN: ¬F∣N):
    ¬flagPlaneMap_p19 Ω lam mu nu order F∣flagPlaneMap_p19 Ω lam mu nu order N:=by
  have hroot:RCN093.flagEvaluation Ω C.1 lam mu nu (flagAlgHom_p19 lam mu nu F)=0:=by
    rw [ACO]
    change F∈RingHom.ker (RCN002.coordinateEvaluation Ω C.1).toRingHom
    rw [RCN002.coordinateEvaluation_ker]
    exact RCN264.EN Ω F T R C
  intro hd
  have hh:=(RCN021.planeMap_dvd_iff_of_evaluation Ω (RCN002.CoordinateField Ω C.1) order
    (RCN093.flagEvaluation Ω C.1 lam mu nu) (flagAlgHom_p19 lam mu nu F) (flagAlgHom_p19 lam mu nu N)
    ((ARZ lam mu nu F).mpr hF) hroot ht).mp hd
  exact hN ((flag_dvd_iff_p19 lam mu nu F N).mp hh)
theorem EPH
    {Ω:Type} [Field Ω] {F T R:MvPolynomial (Fin 3) Ω}
    (C:RCN264.RegularComponent Ω F T R)
    (lam mu nu:Ω) (order:Fin 3 ≃ Fin 3)
    (ht:Transcendental Ω
      (RCN093.flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF:Irreducible F) (N:MvPolynomial (Fin 3) Ω) (hN: ¬F∣N)
    (hpos:0<(flagPlaneMap_p19 Ω lam mu nu order F).natDegree):
    RW lam mu nu order F N≠0:=by
  classical
  have hi:=RCN103.ADV lam mu nu order hF C ht
  have hn:=EJV C lam mu nu order ht hF N hN
  exact RCN362.irreducible_resultant_ne_zero_of_not_dvd _ _ hi hpos hn
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
def PO (H G:MvPolynomial (Fin 4) K):
    MvPolynomial (Fin 3) (GenericField K):=
  surfaceMap (RCN135.polynomialEmbedding K) (numerators H G (RCN326.w+1))
theorem EAB
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    {A:Type} [Fintype A] (F:SO S A) (a:A)
    (H G:MvPolynomial (Fin 4) K) (hproper: ¬S.G∣PO H G):
    RW F.lam F.mu F.nu F.order S.G (PO H G)≠0:=by
  exact EPH (F.component a) F.lam F.mu F.nu F.order (F.ht a)
    S.MW (PO H G) hproper F.positive
theorem EJK
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper: ¬S.G∣PO H G)
    {A:Type} [Fintype A] (F:SO S A) (W:BNZ S A F):
    W.q^CQI S A hfirst F W.q∣
      RW F.lam F.mu F.nu F.order S.G (PO H G):=by
  let surface:=TL S F.lam F.mu F.nu F.order
  let oldTail:=CPZ S F.lam F.mu F.nu F.order
  let newTail:=flagPlaneMap_p19 (GenericField K) F.lam F.mu F.nu F.order (PO H G)
  letI:(Ideal.span {RCN107.indexedFiberSurface W.q W.irreducible surface}).IsPrime:=
    BKV F.component F.lam F.mu F.nu F.order F.ht
      S.MW W.q W.irreducible W.witness
  have hsurface:=BLI S F.component F.lam F.mu F.nu F.order F.ht
  have holdRoot: ∀a:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q,
      oldTail∈RCN021.relationKernel (GenericField K) (RCN002.CoordinateField (GenericField K) (F.component a.1).1)
        F.order (RCN093.flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu) (F.ht a.1):=by
    intro a
    exact AFZ (F.component a.1).1 F.lam F.mu F.nu F.order (F.ht a.1)
      (RCN264.GV (GenericField K) S.G _ _ (F.component a.1))
  have holdProper:RCN107.indexedFiberTail W.q W.irreducible oldTail∉
      Ideal.span {RCN107.indexedFiberSurface W.q W.irreducible surface}:=
    BLD F.component F.lam F.mu F.nu F.order F.ht
      S.MW hfirst W.q W.irreducible W.witness
  have hbar:=RCN107.indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order F.ht
    W.q W.irreducible surface oldTail holdRoot holdProper
  have htail:=DIK S hfirst H G hcross F.component
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible
  have hres:Polynomial.resultant surface newTail surface.natDegree newTail.natDegree≠0:=
    EAB S F W.witness.1 H G hproper
  have hmod:(RCN107.indexedFiberSurface W.q W.irreducible surface).map
      (IsLocalRing.residue (RCN102.FiberCoefficient W.q W.irreducible))≠0:=
    CQH S F W
  exact ACC F.component F.injective
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible W.monic
    surface newTail surface.natDegree newTail.natDegree
    (fun a=>hsurface a.1) hbar
    (fun a=>FO S (DN S hfirst) (F.component a.1))
    htail Polynomial.natDegree_map_le Polynomial.natDegree_map_le hres hmod
theorem EJP
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper: ¬S.G∣PO H G)
    {A:Type} [Fintype A] (F:SO S A)
    (hgate: ∀a,∀hx:Transcendental (GenericField K)
        (RCN093.flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
          (MvPolynomial.X (F.order 0))),
      (letI:=RCN120.flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        FiniteDimensional (RatFunc (GenericField K)) (RCN002.CoordinateField (GenericField K) (F.component a).1))∧
      (letI:=RCN120.flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        Algebra.IsSeparable (RatFunc (GenericField K)) (RCN002.CoordinateField (GenericField K) (F.component a).1)))
    (axis:JS.Axis) (horder:F.order=axis.order)
    (surfaceFlag tailFlag:FlagDegree)
    (hSflag:RCN095.PolynomialInFlag surfaceFlag S.G)
    (hTflag:RCN095.PolynomialInFlag tailFlag (PO H G)):
    (∑ a,FO S (DN S hfirst) (F.component a)*
      RCN344.coordinateDegree (GenericField K) (RCN002.CoordinateField (GenericField K) (F.component a).1)
        (RCN042.coordinateOfGate
          (RCN093.flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
            (MvPolynomial.X (F.order 0))) (hgate a)))≤
      RCN095.flagMixed surfaceFlag tailFlag axis.flag:=by
  classical
  by_cases hA:Nonempty A
  · let a0:A:=Classical.choice hA
    have hres:=EAB S F a0 H G hproper
    have hTne:PO H G≠0:=fun hz=>hproper (hz ▸ dvd_zero _)
    have hdegree:(RW F.lam F.mu F.nu F.order S.G
        (PO H G)).natDegree≤RCN095.flagMixed surfaceFlag tailFlag axis.flag:=by
      rw [horder]
      exact JS.BPQ axis F.lam F.mu F.nu
        S.G (PO H G) surfaceFlag tailFlag hSflag hTflag hTne
    let channel:=RCN104.RI F.component F.lam F.mu F.nu
      F.order F.ht F.finite F.generates hgate
      (fun a=>FO S (DN S hfirst) (F.component a))
      (RW F.lam F.mu F.nu F.order S.G (PO H G))
      (RCN095.flagMixed surfaceFlag tailFlag axis.flag) hres hdegree
      (fun q hq hmonic a=>EJK S hfirst H G hcross hproper F
        ⟨q,hq,hmonic,a⟩)
    exact channel.CTA
  · letI:IsEmpty A:=⟨fun a=>hA ⟨a⟩⟩
    simp
end
end AGT
end MergedPart8
section MergedPart9
namespace NL
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN002 RCN022 RCN037 RCN042 RCN093 RCN341
open NA AGT
open JS ALP
open MI
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
theorem BTW
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (C:CM S):PO H G∈C.1:=by
  let ev:=surfaceMap (RCN135.polynomialEmbedding K)
  have hF:ev S.F∈C.1:=RCN312.RP S C
  have hold:ev (numerator K S.F (RCN326.w+1))∈C.1:=
    (RCN330.globalTailCut_mem_iff (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K)
      S.F (RCN326.w+1) C.1).mp
      (GV (GenericField K) S.G _ _ C)
  have hc:=C.1.mem_of_dvd (map_dvd ev hcross) hF
  simp only [map_sub,map_mul,map_pow] at hc
  have hm:=C.1.sub_mem (C.1.mul_mem_left ((ev H)^(2*(RCN326.w+1))) hold) hc
  simp only [sub_sub_cancel] at hm
  have hprime:C.1.IsPrime:=inferInstance
  have hOld:(ev (polyH K S.F))^(2*(RCN326.w+1))∉C.1:=by
    intro hh
    exact RCN312.JX S C
      (hprime.mem_of_pow_mem _ hh)
  exact (hprime.mem_or_mem hm).resolve_left hOld
theorem CMJ
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH: ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) H): ¬S.G∣PO H G:=by
  let ev:=surfaceMap (RCN135.polynomialEmbedding K)
  have hc:=S.RR.trans (map_dvd ev hcross)
  simp only [map_sub,map_mul,map_pow] at hc
  intro hd
  change S.G∣ev (numerators H G (RCN326.w+1)) at hd
  have hprod:=hc.add (dvd_mul_of_dvd_right hd ((ev (polyH K S.F))^(2*(RCN326.w+1))))
  rw [sub_add_cancel] at hprod
  have hpow: ¬S.G∣(ev H)^(2*(RCN326.w+1)):=
    fun hh=>hH (S.MW.prime.dvd_of_dvd_pow hh)
  have hraw:=(S.MW.prime.dvd_or_dvd hprod).resolve_left hpow
  apply hfirst
  rw [RCN086.globalTailCut_eq]
  exact dvd_mul_of_dvd_left hraw _
theorem CUS
    {Ω:Type} [Field Ω] (phi:Polynomial K→+*Ω)
    (N:MvPolynomial (Fin 4) K) (B A C:ℕ) (hBA:B≤A) (hAC:A≤C)
    (hB:RCN234.wt RCN156.residualSWeights N≤B)
    (hA:RCN234.wt RCN156.residualYSWeights N≤A)
    (hC:RCN234.wt RCN156.residualTotalWeights N≤C):
    RCN095.PolynomialInFlag ⟨C-A,A-B,B⟩ (surfaceMap phi N):=by
  intro e he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (RCN136.support_surfaceMap_subset phi N he)
  have hb:=(MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights hd).trans hB
  have ha:=(MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd).trans hA
  have hc:=(MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hd).trans hC
  rw [RCN081.weight_fin4] at hb ha hc
  simp [RCN156.residualSWeights,RCN156.residualYSWeights,RCN156.residualTotalWeights] at hb ha hc
  change d 2≤B∧d 1+d 2≤A-B+B∧d 1+d 2+d 3≤C-A+(A-B)+B
  omega
theorem DML
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper: ¬S.G∣PO H G)
    (surfaceFlag tailFlag:FlagDegree)
    (hS:RCN095.PolynomialInFlag surfaceFlag S.G)
    (hT:RCN095.PolynomialInFlag tailFlag (PO H G))
    (hsmall:flagMixed surfaceFlag tailFlag unitZFlag<p)
    (C:CM S):RCN037.LiteralProjectionGate C 2:=by
  intro ht
  have ht' :Transcendental (GenericField K)
      (RCN093.flagEvaluation (GenericField K) C.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))):=by
    simpa [Axis.order,RCN125.zOrder_p19] using ht
  have he:=RCN116.elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder_p19])
  have hh:=CNW C.1 .z 0 0 0 ht' S.G (PO H G)
    S.MW.ne_zero (fun hz=>hproper (hz ▸ dvd_zero _))
    (S.MW.isRelPrime_iff_not_dvd.mpr hproper)
    (EN (GenericField K) S.G _ _ C)
    (BTW S H G hcross C) surfaceFlag tailFlag hS hT p hsmall
  rw [he] at hh
  exact hh
end
end NL
end MergedPart9
section MergedPart10
namespace UQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped Classical WithZero
open RCN002 RCN022 RCN035 RCN042 RCN044 RCN093 RCN096 RCN099 RCN116 RCN341 RCN344
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
theorem DIN
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (base:RCN341.SeparableLiteralCoordinate P)
    (a:Ω) (ha:a≠0) (x y:RCN002.CoordinateField Ω P)
    (hval: ∀v∈OW base,v.val (x+a • y)=max (v.val x) (v.val y))
    (hout: ∀v:Place_p19 Ω (RCN002.CoordinateField Ω P),v∉OW base→
      RCN187.poleOrder v.val x=0∧RCN187.poleOrder v.val y=0)
    (v:Place_p19 Ω (RCN002.CoordinateField Ω P)):
    RCN187.poleOrder v.val (x+a • y)=max (RCN187.poleOrder v.val x) (RCN187.poleOrder v.val y):=by
  by_cases hv:v∈OW base
  · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (hval v hv)
  · obtain ⟨hx,hy⟩:=hout v hv
    have hxle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hx
    have hyle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hy
    letI:v.val.IsTrivialOn Ω:=v.property.2
    have hs:v.val (a • y)=v.val y:=by
      rw [Algebra.smul_def,map_mul,Valuation.IsTrivialOn.eq_one a ha,one_mul]
    have hle:v.val (x+a • y)≤1:=
      (v.val.map_add _ _).trans (by rw [hs];exact max_le hxle hyle)
    have hzero:RCN187.poleOrder v.val (x+a • y)=0:=
      RCN346._Q11 Ω (RCN002.CoordinateField Ω P) v _ hle
    rw [hzero,hx,hy]
    rfl
structure GammaFrame {A:Type} [Fintype A]
    (P:A→Ideal (MvPolynomial (Fin 3) Ω)) [∀a,(P a).IsPrime]
    (surface:MvPolynomial (Fin 3) Ω) where
  lam:Ω
  mu:Ω
  lam_ne:lam≠0
  mu_ne:mu≠0
  ZG: ∀a,Transcendental Ω (affineU Ω (P a) lam)
  CVM: ∀a,Transcendental Ω (affineV Ω (P a) mu (mu*lam))
  uFinite: ∀a,
    letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (ZG a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a))
  uSeparable: ∀a,
    letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (ZG a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))
  vFinite: ∀a,
    letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (CVM a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a))
  vSeparable: ∀a,
    letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (CVM a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))
  uPole: ∀a (v:Place_p19 Ω (RCN002.CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineU Ω (P a) lam)=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
        (RCN187.poleOrder v.val (coordinate Ω (P a) 2))
  vPole: ∀a (v:Place_p19 Ω (RCN002.CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineV Ω (P a) mu (mu*lam))=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 1))
        (max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
          (RCN187.poleOrder v.val (coordinate Ω (P a) 2)))
  directional:MvPolynomial.pderiv (0:Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) surface≠0
theorem FLQ
    {A:Type} [Fintype A]
    (P:A→Ideal (MvPolynomial (Fin 3) Ω)) [∀a,(P a).IsPrime]
    (hz: ∀a,Transcendental Ω (coordinate Ω (P a) 2))
    (hgate: ∀a,
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a)))∧
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))))
    (surface:MvPolynomial (Fin 3) Ω) (hderiv:MvPolynomial.pderiv (1:Fin 3) surface≠0):
    Nonempty (GammaFrame P surface):=by
  classical
  let base (a:A):RCN341.SeparableLiteralCoordinate (P a):=⟨2,hz a,(hgate a).1,(hgate a).2⟩
  let E (a:A):=RCN002.CoordinateField Ω (P a)
  let z (a:A):E a:=coordinate Ω (P a) 2
  let y (a:A):E a:=coordinate Ω (P a) 0
  let r (a:A):E a:=coordinate Ω (P a) 1
  let W (a:A):=OW (base a)
  let bases (a:A):=RCN042.literalToSeparableCoordinate (base a)
  have hzD (a:A):KaehlerDifferential.D Ω (E a) (z a)≠0:=
    RCN042.differential_ne_zero_of_gate _ (hz a) (hgate a)
  obtain ⟨lam,hlam0,hlam⟩:=AFY
    E y z W bases (fun a=>Or.inr (hzD a))
  let U (a:A):E a:=y a+lam • z a
  have huPole (a:A) (v:Place_p19 Ω (E a)):
      RCN187.poleOrder v.val (U a)=max (RCN187.poleOrder v.val (y a)) (RCN187.poleOrder v.val (z a)):=by
    exact DIN (P a) (base a) lam hlam0 (y a) (z a)
      (hlam a).choose_spec.2.2
      (fun v hv=>⟨DW (base a) v hv 0,
        DW (base a) v hv 2⟩) v
  have huD (a:A):KaehlerDifferential.D Ω (E a) (U a)≠0:=
    RCN042.differential_ne_zero_of_gate _ (hlam a).choose
      ⟨(hlam a).choose_spec.1,(hlam a).choose_spec.2.1⟩
  let Extra (mu:Ω):=MvPolynomial.pderiv (0:Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) surface=0
  have hextra: ∀{a b},Extra a→Extra b→a=b:=
    RCN096.directional_bad_coefficient_subsingleton surface hderiv
  obtain ⟨mu,hmu0,hdir,hmu⟩:=YC
    E r U W Extra hextra bases (fun a=>Or.inr (huD a))
  let V (a:A):E a:=r a+mu • U a
  have hvPole (a:A) (v:Place_p19 Ω (E a)):
      RCN187.poleOrder v.val (V a)=max (RCN187.poleOrder v.val (r a)) (RCN187.poleOrder v.val (U a)):=by
    apply DIN (P a) (base a) mu hmu0 (r a) (U a) (hmu a).choose_spec.2.2 ?_ v
    intro v hv
    refine ⟨DW (base a) v hv 1,?_⟩
    rw [huPole a v]
    rw [DW (base a) v hv 0,
      DW (base a) v hv 2]
    rfl
  have hvEq (a:A):affineV Ω (P a) mu (mu*lam)=V a:=by
    simp only [V,U,r,y,z,affineV,smul_add,smul_smul,add_assoc]
  have hvt (a:A):Transcendental Ω (affineV Ω (P a) mu (mu*lam)):=
    hvEq a ▸ (hmu a).choose
  have hev (a:A):
      RCN022.elementEmbedding Ω (E a) (affineV Ω (P a) mu (mu*lam)) (hvt a)=
        RCN022.elementEmbedding Ω (E a) (V a) (hmu a).choose:=
    RCN116.elementEmbedding_congr (hvt a) (hmu a).choose (hvEq a)
  refine ⟨{
    lam:=lam,mu:=mu,lam_ne:=hlam0,mu_ne:=hmu0
    ZG:=fun a=>(hlam a).choose
    CVM:=hvt
    uFinite:=fun a=>(hlam a).choose_spec.1
    uSeparable:=fun a=>(hlam a).choose_spec.2.1
    vFinite:= ?_,vSeparable:= ?_,uPole:=huPole
    vPole:= ?_,directional:=hdir}⟩
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.1
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.2.1
  · intro a v
    rw [hvEq a,hvPole a v,huPole a v]
end
end UQ
end MergedPart10
section MergedPart11
namespace WB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN116 RCN117 RCN125
open RCN095 renaming PolynomialInFlag → BI
open JS YL
open UQ
section General
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
variable {A:Type} [Fintype A]
variable {P:A→Ideal (MvPolynomial (Fin 3) Ω)} [∀a,(P a).IsPrime]
variable {surface:MvPolynomial (Fin 3) Ω}
theorem frame_trans (D:GammaFrame P surface)
    (hz: ∀a,Transcendental Ω (coordinate Ω (P a) 2)) (axis:Axis) (a:A):
    Transcendental Ω (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0))):=by
  cases axis with
  | z=>simpa [Axis.order,zOrder_p19] using hz a
  | u=>simpa [Axis.order,uOrder_p19] using D.ZG a
  | v=>simpa [Axis.order,vOrder_p19] using D.CVM a
theorem frame_gate (D:GammaFrame P surface)
    (hz: ∀a,Transcendental Ω (coordinate Ω (P a) 2))
    (hgate: ∀a,
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a)))∧
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))))
    (axis:Axis) (a:A)
    (ht:Transcendental Ω (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0)))):
    (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a))
      (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a)))∧
    (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a))
      (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))):=by
  cases axis with
  | z=>
    have he:=RCN116.elementEmbedding_congr ht (hz a) (by simp [Axis.order,zOrder_p19])
    rw [he]
    exact hgate a
  | u=>
    have he:=RCN116.elementEmbedding_congr ht (D.ZG a) (by simp [Axis.order,uOrder_p19])
    rw [he]
    exact ⟨D.uFinite a,D.uSeparable a⟩
  | v=>
    have he:=RCN116.elementEmbedding_congr ht (D.CVM a) (by simp [Axis.order,vOrder_p19])
    rw [he]
    exact ⟨D.vFinite a,D.vSeparable a⟩
def frameCost (D:GammaFrame P surface)
    (hz: ∀a,Transcendental Ω (coordinate Ω (P a) 2)) (axis:Axis) (a:A):ℕ:=
  letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a))
    (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_trans D hz axis a)).toRingHom.toAlgebra
  Module.finrank (RatFunc Ω) (RCN002.CoordinateField Ω (P a))
end General
open RCN135 RCN136 RCN074 RCN086 RCN244 RCN245 RCN249 RCN313
open NA AGT NL
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
theorem CLX
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H G:MvPolynomial (Fin 4) K)
    (hcross:S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH: ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) H)
    {A:Type} [Fintype A] (component:A→CM S)
    (hinj:Function.Injective component)
    (hz: ∀a,Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (surfaceFlag tailFlag:FlagDegree)
    (hS:RCN095.PolynomialInFlag surfaceFlag S.G)
    (hT:RCN095.PolynomialInFlag tailFlag (PO H G))
    (hsmall:flagMixed surfaceFlag tailFlag unitZFlag<p):
    ∃D:GammaFrame (fun a=>(component a).1) S.G,∀axis:Axis,
      (∑ a,FO S (DN S hfirst) (component a)*frameCost D hz axis a)≤
        flagMixed surfaceFlag tailFlag axis.flag:=by
  classical
  have hproper:=CMJ S hfirst H G hcross hH
  have hgate (a:A):=DML S H G hcross hproper surfaceFlag tailFlag hS hT hsmall
    (component a) (hz a)
  have hderiv:=RCN315.EH S
  obtain ⟨D⟩:=FLQ (fun a=>(component a).1) hz hgate S.G hderiv
  refine ⟨D,fun axis=> ?_⟩
  let F:SO S A:={
    component:=component,injective:=hinj
    lam:=D.lam,mu:=D.mu,nu:=D.mu*D.lam,order:=axis.order
    ht:=frame_trans D hz axis
    finite:=fun a=>(frame_gate D hz hgate axis a (frame_trans D hz axis a)).1
    generates:=fun a=>CWN (GenericField K) (component a).1
      axis D.lam D.mu (D.mu*D.lam) (frame_trans D hz axis a)
    positive:=by
      cases axis with
      | z=>exact (MV D.lam D.mu S.G hderiv).2
      | u=>exact (MV D.lam D.mu S.G hderiv).1
      | v=>exact XD D.lam D.mu S.G D.directional}
  have hb:=EJP S hfirst H G hcross hproper F
    (frame_gate D hz hgate axis) axis rfl surfaceFlag tailFlag hS hT
  have he (a:A):
      RCN344.coordinateDegree (GenericField K) (RCN002.CoordinateField (GenericField K) (component a).1)
        (RCN042.coordinateOfGate
          (RCN093.flagEvaluation (GenericField K) (component a).1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (axis.order 0))) (frame_gate D hz hgate axis a))=frameCost D hz axis a:=
    RCN042.coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  simpa only [F,he] using hb
end
end WB
end MergedPart11
section MergedPart12
namespace AEG
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators WithZero
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN114 RCN165 RCN295 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open JS UQ
open WB
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
variable {A:Type} [Fintype A]
variable {P:A→Ideal (MvPolynomial (Fin 3) Ω)} [∀a,(P a).IsPrime]
variable {surface:MvPolynomial (Fin 3) Ω}
variable (D:GammaFrame P surface)
variable (hz: ∀a,Transcendental Ω (coordinate Ω (P a) 2))
variable (hgate: ∀a,
  (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (P a)))∧
  (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
    (hz a)).toRingHom.toAlgebra;
    Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (P a))))
include hgate in
theorem DHE (axis:Axis) (a:A)
    (W:Finset (Place_p19 Ω (RCN002.CoordinateField Ω (P a)))):
    (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag))≤
      (frameCost D hz axis a:ℤ):=by
  let projection:=RCN042.coordinateOfGate
    (RCN093.flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_gate D hz hgate axis a)
  have he:RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (P a)) projection=frameCost D hz axis a:=
    RCN042.coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  have hp (v:Place_p19 Ω (RCN002.CoordinateField Ω (P a))):
      RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport axis.flag)=
        RCN346.poleOrder_p19 Ω (RCN002.CoordinateField Ω (P a)) v
          (RCN344.coordinateValue Ω (RCN002.CoordinateField Ω (P a)) projection):=by
    dsimp only [projection]
    rw [RCN042.coordinateOfGate_value]
    change _=RCN187.poleOrder v.val _
    cases axis with
    | z=>simp only [Axis.flag,Axis.order,RCN125.zOrder_p19,Equiv.swap_apply_left,
        RCN093.flagEvaluation_X_two,UC]
    | u=>
      simp only [Axis.flag,Axis.order,RCN125.uOrder_p19,Equiv.refl_apply,
        RCN093.flagEvaluation_X_zero,QD]
      exact (D.uPole a v).symm
    | v=>
      simp only [Axis.flag,Axis.order,RCN125.vOrder_p19,Equiv.swap_apply_left,
        RCN093.flagEvaluation_X_one,SF]
      exact (D.vPole a v).symm
  calc
    _=∑ v∈W,RCN346.poleOrder_p19 Ω (RCN002.CoordinateField Ω (P a)) v
        (RCN344.coordinateValue Ω (RCN002.CoordinateField Ω (P a)) projection):=
      Finset.sum_congr rfl (fun v _=>hp v)
    _≤(RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (P a)) projection:ℤ):=
      PY Ω (RCN002.CoordinateField Ω (P a)) projection W
    _=_:=by rw [he]
def BET (a:A) (r:FlagDegree):ℕ:=
  r.zOnly*frameCost D hz .z a+r.yz*frameCost D hz .u a+r.all*frameCost D hz .v a
def FNI (a:A):BIR (P a) (BET D hz a):=by
  classical
  let base:RCN341.SeparableLiteralCoordinate (P a):=⟨2,hz a,(hgate a).1,(hgate a).2⟩
  refine ⟨?_⟩
  intro r N hN hproper points hpointsP hpointsN
  have hpole: ∀W:Finset (Place_p19 Ω (RCN002.CoordinateField Ω (P a))),
      (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport r))≤
        (BET D hz a r:ℤ):=by
    intro W
    have hz' :=DHE D hz hgate .z a W
    have hu' :=DHE D hz hgate .u a W
    have hv' :=DHE D hz hgate .v a W
    calc
      _≤∑ v∈W,((r.zOnly:ℤ)*RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag)+
          (r.yz:ℤ)*RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag)+
          (r.all:ℤ)*RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)):=
        Finset.sum_le_sum (fun v _=>AEI v.val (coordinate Ω (P a)) r)
      _=(r.zOnly:ℤ)*(∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitZFlag))+
          (r.yz:ℤ)*(∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitYZFlag))+
          (r.all:ℤ)*(∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω (P a)) (flagSupport unitAllFlag)):=by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _≤(r.zOnly:ℤ)*(frameCost D hz .z a:ℤ)+
          (r.yz:ℤ)*(frameCost D hz .u a:ℤ)+(r.all:ℤ)*(frameCost D hz .v a:ℤ):=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hz' (by positivity))
          (mul_le_mul_of_nonneg_left hu' (by positivity)))
          (mul_le_mul_of_nonneg_left hv' (by positivity))
      _=_:=by simp only [BET,Nat.cast_add,Nat.cast_mul]
  exact AEK (P a) base
    (flagSupport r) (BET D hz a r) hpole N
    ((RCN095.support_subset_flagSupport_iff r N).mpr hN) hproper points hpointsP hpointsN
end
end AEG
end MergedPart12
section MergedPart13
namespace ARK
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN002 RCN135 RCN136 RCN074 RCN086 RCN095 RCN238 RCN243 RCN244 RCN264 RCN313 RCN330
open RCN095 renaming PolynomialInFlag → BI
open NA BBN
open NL MI
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
theorem EFB
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (H G:MvPolynomial (Fin 4) K) (n:ℕ) (hn:RCN326.w<n)
    (hcross:S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (gamma:K) (hgamma:gamma∈Gamma):
    MvPolynomial.aeval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
      (surfaceMap (RCN135.polynomialEmbedding K) (numerators H G n))=0:=by
  let f:MvPolynomial (Fin 3) (GenericField K)→+*GenericField K:=
    (MvPolynomial.aeval (DK (RCN135.polynomialEmbedding K) S.selected gamma)).toRingHom
  let ev:=f.comp (surfaceMap (RCN135.polynomialEmbedding K))
  have hF:ev S.F=0:=by
    have hh:=map_dvd f S.RR
    have hG:f S.G=0:=S.on_component gamma hgamma
    rw [hG,zero_dvd_iff] at hh
    exact hh
  have holdGlobal:RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F n∈RingHom.ker f:=
    VZ (RCN135.polynomialEmbedding K) S.F S.selected gamma RCN326.w n
      (S.degree_le gamma hgamma) (S.solution gamma hgamma) hn
  have hold:ev (numerator K S.F n)=0:=
    (RCN330.globalTailCut_mem_iff (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K)
      S.F n (RingHom.ker f)).mp holdGlobal
  have hOld:ev (polyH K S.F)≠0:=by
    change MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
      (surfaceMap (RCN135.polynomialEmbedding K) (MvPolynomial.pderiv (2:Fin 4) S.F))≠0
    rw [WQ]
    exact S.regular gamma hgamma
  have he:=map_dvd ev hcross
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,hold,mul_zero,
    zero_sub,neg_eq_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hOld)
theorem DJU
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (H G:MvPolynomial (Fin 4) K) (n:ℕ)
    (hcross:S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (hH:surfaceMap (RCN135.polynomialEmbedding K) H∉C.1)
    (hproper:RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F n∉C.1):
    surfaceMap (RCN135.polynomialEmbedding K) (numerators H G n)∉C.1:=by
  let ev:=(RCN002.coordinateEvaluation (GenericField K) C.1).toRingHom
  have he (N:MvPolynomial (Fin 3) (GenericField K)):ev N=0 ↔ N∈C.1:=by
    change N∈RingHom.ker (RCN002.coordinateEvaluation (GenericField K) C.1).toRingHom ↔ N∈C.1
    rw [RCN002.coordinateEvaluation_ker]
  have hF:=(he _).mpr (RCN312.RP S C)
  have hold:IsUnit (ev (surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F))):=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr (RCN312.JX S C))
  have hnew:IsUnit (ev (surfaceMap (RCN135.polynomialEmbedding K) H)):=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr hH)
  have hassoc:=EQX (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K)
    ev S.F H G n hF hold hnew hcross
  intro hmem
  have hh:=hassoc.symm.dvd
  rw [(he _).mpr hmem,zero_dvd_iff] at hh
  exact hproper ((he _).mp hh)
end
end ARK
end MergedPart13
section MergedPart14
namespace XT
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
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
abbrev stageSeeds (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):=
  RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (CR (RCN135.polynomialEmbedding K) S.F) Gamma
    (DK (RCN135.polynomialEmbedding K) S.selected) C
abbrev AWW
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (H:MvPolynomial (Fin 4) K):=
  {C:CM S//
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2)∧
    surfaceMap (RCN135.polynomialEmbedding K) H∉C.1∧
    ∃delay,1≤delay∧delay≤FO S (DN S hfirst) C∧
      RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1+delay)∉C.1}
end
end XT
end MergedPart14
section MergedPart15
namespace AYN
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN093 RCN095 RCN135 RCN136 RCN238 RCN243 RCN264
open RCN095 renaming PolynomialInFlag → BI
open JS YL
open XT NL
open MI
theorem DNM
    {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
    (phi:Polynomial K→+*Ω) (selected:K→Polynomial K) (seeds:Finset K)
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hconstant:IsAlgebraic Ω (coordinate Ω P 2))
    (hon: ∀gamma∈seeds,P≤RingHom.ker (MvPolynomial.aeval (DK phi selected gamma)).toRingHom):
    seeds.card≤1:=by
  obtain ⟨c,hc⟩:=RCN370.eq_algebraMap_of_isAlgebraic Ω (RCN002.CoordinateField Ω P) _ hconstant
  have hmem:MvPolynomial.X (2:Fin 3)-MvPolynomial.C c∈P:=by
    rw [←RCN002.coordinateEvaluation_ker Ω P]
    change RCN002.coordinateEvaluation Ω P (MvPolynomial.X 2-MvPolynomial.C c)=0
    rw [RCN002.coordinateEvaluation_eq_aeval]
    simpa using sub_eq_zero.mpr hc.symm
  have hvalue (gamma:K) (hgamma:gamma∈seeds):(phi.comp Polynomial.C) gamma=c:=by
    have hh:=hon gamma hgamma hmem
    change MvPolynomial.aeval (DK phi selected gamma)
      (MvPolynomial.X (2:Fin 3)-MvPolynomial.C c)=0 at hh
    simpa only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Algebra.algebraMap_self,RingHom.id_apply,EMD,sub_eq_zero] using hh
  apply Finset.card_le_one.mpr
  intro gamma hgamma eta heta
  exact (phi.comp Polynomial.C).injective ((hvalue gamma hgamma).trans (hvalue eta heta).symm)
theorem CYE
    {Ω:Type} [Field Ω] {A:Type} [Fintype A]
    (P:A→Ideal (MvPolynomial (Fin 3) Ω)) [∀a,(P a).IsPrime]
    (hinj:Function.Injective P) (axis:Axis)
    (ht: ∀a,Transcendental Ω
      (RCN093.flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))))
    (F N:MvPolynomial (Fin 3) Ω) (hF:F≠0) (hN:N≠0) (hrel:IsRelPrime F N)
    (hFmem: ∀a,F∈P a) (hNmem: ∀a,N∈P a)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p F) (hq:RCN095.PolynomialInFlag q N):
    Fintype.card A≤flagMixed p q axis.flag:=by
  letI: ∀a,Algebra (RatFunc Ω) (RCN002.CoordinateField Ω (P a)):=fun a=>
    (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω (P a))
      (RCN093.flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))) (ht a)).toRingHom.toAlgebra
  have hb:=BSL Ω axis 0 0 0 P hinj ht F N hF hN hrel hFmem hNmem p q hp hq
  calc
    Fintype.card A=∑ _:A,1:=by simp
    _≤∑ a:A,Module.finrank (RatFunc Ω) (RCN002.CoordinateField Ω (P a)):=by
      apply Finset.sum_le_sum
      intro a _
      letI:=hb.1 a
      exact Module.finrank_pos
    _≤_:=hb.2
theorem DVJ
    {Ω:Type} [Field Ω] [IsAlgClosed Ω] {A:Type} [Fintype A]
    (P:A→Ideal (MvPolynomial (Fin 3) Ω)) [∀a,(P a).IsPrime]
    (hinj:Function.Injective P)
    (hnonpoint: ∀a,∀v:Fin 3→Ω,P a≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hconstant: ∀a,IsAlgebraic Ω (coordinate Ω (P a) 2))
    (F N:MvPolynomial (Fin 3) Ω) (hF:F≠0) (hN:N≠0) (hrel:IsRelPrime F N)
    (hFmem: ∀a,F∈P a) (hNmem: ∀a,N∈P a)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p F) (hq:RCN095.PolynomialInFlag q N):
    Fintype.card A≤flagMixed p q unitYZFlag+flagMixed p q unitAllFlag:=by
  let activeY (a:A):=Transcendental Ω (coordinate Ω (P a) 0)
  have hr (a:A) (ha: ¬activeY a):Transcendental Ω (coordinate Ω (P a) 1):=by
    obtain ⟨i,hi⟩:=RCN002.exists_transcendental_coordinate_of_ne_point_kernel Ω (P a) (hnonpoint a)
    fin_cases i
    · exact False.elim (ha hi)
    · exact hi
    · exact False.elim (hi (hconstant a))
  have hycap:Fintype.card {a:A//activeY a}≤flagMixed p q unitYZFlag:=
    CYE (fun a:{a:A//activeY a}=>P a.1)
      (fun a b h=>Subtype.ext (hinj h)) .u
      (fun a=>by simpa [Axis.order,RCN125.uOrder_p19,affineU] using a.2)
      F N hF hN hrel (fun a=>hFmem a.1) (fun a=>hNmem a.1) p q hp hq
  have hrcap:Fintype.card {a:A// ¬activeY a}≤flagMixed p q unitAllFlag:=
    CYE (fun a:{a:A// ¬activeY a}=>P a.1)
      (fun a b h=>Subtype.ext (hinj h)) .v
      (fun a=>by simpa [Axis.order,RCN125.vOrder_p19,affineV] using hr a.1 a.2)
      F N hF hN hrel (fun a=>hFmem a.1) (fun a=>hNmem a.1) p q hp hq
  have hcomp:=Fintype.card_subtype_compl activeY
  have hle:Fintype.card {a:A//activeY a}≤Fintype.card A:=
    Fintype.card_le_of_injective (fun a:{a:A//activeY a}=>a.1) Subtype.val_injective
  omega
open RCN074 RCN086 RCN244
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
abbrev AXO (S:Stage_p19 K I Gamma x p flag errorCap stageSupport):=
  {C:CM S//IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)}
end
end AYN
end MergedPart15
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace ATE
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN174
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open JS UQ WB
open AEG XT NL
open MI
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
abbrev BJA (S:Stage_p19 K I Gamma x p flag errorCap stageSupport):=
  {C:CM S//
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2)∧
      ∀delay,RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1+delay)∈C.1}
end
end ATE
end MergedPart0
section MergedPart1
namespace WW
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN051 RCN068 RCN074 RCN086 RCN095 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open RCN095 renaming PolynomialInFlag → BI
open MI DC
open VM XK NL
variable {K I:Type} [Field K]
theorem EGB (F H:MvPolynomial (Fin 4) K) (hF:F≠0) (hrel:IsRelPrime F H):
    IsRelPrime (surfaceMap (RCN135.polynomialEmbedding K) F) (surfaceMap (RCN135.polynomialEmbedding K) H):=by
  have hFc:collectX K F≠0:=fun hz=>hF ((collectX K).injective (hz.trans (map_zero _).symm))
  exact AQX K (collectX K F) (collectX K H) hFc
    (BDS (collectX K).toRingEquiv F H hrel)
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
def BPG (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (J:SecondJetSupport.Poly (K:=K)):Finset K:=
  Gamma.filter (fun gamma=>MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
    (surfaceMap (RCN135.polynomialEmbedding K) (linearH J))=0)
end
end WW
end MergedPart1
section MergedPart2
namespace BHE
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN136 RCN174 RCN238 RCN243 RCN244 RCN264 RCN330
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open MI NL
open XT AYN ATE
open WW
theorem GGY {A:Type} [DecidableEq A] (s a b c:Finset A):
    (s∪(a∪(b∪c))).card≤s.card+(a.card+(b.card+c.card)):=
  (Finset.card_union_le s _).trans (Nat.add_le_add_left
    ((Finset.card_union_le a _).trans (Nat.add_le_add_left (Finset.card_union_le b c) _)) _)
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.ResidualSupportParameters}
theorem FPI
    (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
    (hfirst: ¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
    (J:SecondJetSupport.Poly (K:=K)):
    Gamma.card≤(BPG S J).card+
      ((∑ C:AWW S hfirst (linearH J),(stageSeeds S C.1).card)+
        ((∑ C:AXO S,(stageSeeds S C.1).card)+
          (∑ C:BJA S,(stageSeeds S C.1).card))):=by
  let proper:=Finset.univ.biUnion (fun C:AWW S hfirst (linearH J)=>stageSeeds S C.1)
  let constant:=Finset.univ.biUnion (fun C:AXO S=>stageSeeds S C.1)
  let persistent:=Finset.univ.biUnion (fun C:BJA S=>stageSeeds S C.1)
  have hproperCard:proper.card≤∑ C:AWW S hfirst (linearH J),(stageSeeds S C.1).card:=
    Finset.card_biUnion_le
  have hconstantCard:constant.card≤∑ C:AXO S,(stageSeeds S C.1).card:=
    Finset.card_biUnion_le
  have hpersistentCard:persistent.card≤∑ C:BJA S,(stageSeeds S C.1).card:=
    Finset.card_biUnion_le
  have hcover:Gamma⊆BPG S J∪(proper∪(constant∪persistent)):=by
    intro gamma hg
    by_cases hdenom:MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
        (surfaceMap (RCN135.polynomialEmbedding K) (linearH J))=0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,hdenom⟩)
    have hreg:MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
        (CR (RCN135.polynomialEmbedding K) S.F)≠0:=by
      rw [CR,WQ]
      exact S.regular gamma hg
    have htail:MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected gamma)
        (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))=0:=
      VZ (RCN135.polynomialEmbedding K) S.F S.selected gamma RCN326.w (RCN326.w+1)
        (S.degree_le gamma hg) (S.solution gamma hg) (by omega)
    obtain ⟨C,hon⟩:=AZA (GenericField K) S.G
      (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (RCN326.w+1))
      (CR (RCN135.polynomialEmbedding K) S.F)
      (DK (RCN135.polynomialEmbedding K) S.selected gamma) (S.on_component gamma hg) htail hreg
    have hCS:gamma∈stageSeeds S C:=Finset.mem_filter.mpr ⟨hg,hon⟩
    have hH:surfaceMap (RCN135.polynomialEmbedding K) (linearH J)∉C.1:=fun hh=>hdenom (hon hh)
    apply Finset.mem_union_right
    by_cases hconstant:IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant⟩,Finset.mem_univ _,hCS⟩
    rcases (AEM S (DN S hfirst) C hfirst).2 with hd | hall
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant,hH,hd⟩,Finset.mem_univ _,hCS⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant,hall⟩,Finset.mem_univ _,hCS⟩
  calc
    _≤(BPG S J∪(proper∪(constant∪persistent))).card:=Finset.card_le_card hcover
    _≤(BPG S J).card+(proper.card+(constant.card+persistent.card)):=GGY _ _ _ _
    _≤_:=Nat.add_le_add_left (Nat.add_le_add hproperCard
      (Nat.add_le_add hconstantCard hpersistentCard)) _
end
end BHE
end MergedPart2
section MergedPart3
namespace CB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open MvPolynomial RCN095 RCN136 RCN207
open RCN095 renaming PolynomialInFlag → BI
open TH CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
variable {K E:Type} [Field K] [Field E]
local notation "Poly5" =>MvPolynomial (Fin 5) K
def slope (P:Poly5):=weightedTotalDegree slopeWeights P
def middle (P:Poly5):=weightedTotalDegree HA P
def total (P:Poly5):=weightedTotalDegree Koala6831Ordinary.totalWeights P
def order (P:Poly5):=P.degreeOf 1
def ordinaryFlag (P:Poly5):FlagDegree:=⟨total P-middle P,middle P+order P-slope P,slope P⟩
theorem _Q15 (P:Poly5):
    middle P≤total P∧order P≤middle P∧2*order P≤slope P∧slope P≤middle P+order P:=by
  have hcoef (e) (he:e∈P.support):
      e 1+e 2+e 3≤middle P∧2*e 1+e 3≤slope P∧e 1≤order P:=by
    refine ⟨?_,?_,MvPolynomial.monomial_le_degreeOf _ he⟩
    · simpa [middle,JW,HA] using MvPolynomial.le_weightedTotalDegree HA he
    · simpa [CB.slope,JW,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
  refine ⟨?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    have ht:Finsupp.weight Koala6831Ordinary.totalWeights e≤total P:=MvPolynomial.le_weightedTotalDegree Koala6831Ordinary.totalWeights he
    simp only [JW,HA,Koala6831Ordinary.totalWeights] at ht ⊢
    simp at ht ⊢
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hh:=hcoef e he
    omega
  · have h:order P≤slope P/2:=MvPolynomial.degreeOf_le_iff.mpr (by
      intro e he
      have hh:=hcoef e he
      omega)
    omega
  · apply Finset.sup_le
    intro e he
    have hh:=hcoef e he
    simp [JW,slopeWeights]
    omega
theorem RJ (P:Poly5):
    (ordinaryFlag P).all=slope P∧
    (ordinaryFlag P).yz+(ordinaryFlag P).all=middle P+order P∧
    (ordinaryFlag P).zOnly+(ordinaryFlag P).yz+(ordinaryFlag P).all=total P+order P:=by
  have hh:=_Q15 P
  dsimp only [ordinaryFlag]
  omega
theorem BUF
    (w:Fin 3→ℕ) (P:Polynomial (MvPolynomial (Fin 3) E))
    (s cap drop a b:ℕ) (hcap:drop*s≤cap) (hbalance:drop+a=b)
    (H Q:MvPolynomial (Fin 3) E)
    (hP: ∀j:Fin (s+1),RCN372.wt_p19 w (P.coeff j.val)≤cap-drop*j.val)
    (hH:RCN372.wt_p19 w H≤a) (hQ:RCN372.wt_p19 w Q≤b):
    RCN372.wt_p19 w (SecondJetClearedHelper.cleared P s H Q)≤cap+s*a:=by
  unfold SecondJetClearedHelper.cleared
  apply RCN372.CLG
  intro j _
  have hp:=hP j
  have hh:=(RCN372.wt_pow_le_p19 w H (s-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hq:=(RCN372.wt_pow_le_p19 w Q j.val).trans (Nat.mul_le_mul_left _ hQ)
  have hm:=RCN372.wt_mul_le_p19 w (P.coeff j.val) (H^(s-j.val))
  have hn:=RCN372.wt_mul_le_p19 w (P.coeff j.val*H^(s-j.val)) (Q^j.val)
  have hj:j.val≤s:=Nat.le_of_lt_succ j.isLt
  have hsub:=Nat.sub_add_cancel ((Nat.mul_le_mul_left drop hj).trans hcap)
  have hs:=Nat.sub_add_cancel hj
  nlinarith
theorem FJA
    (phi:Polynomial K→+*E) (P:Poly5) (j:ℕ):
    RCN372.wt_p19 RCN125.sWeight_p19 ((coefficients phi P).coeff j)≤slope P-2*j∧
    RCN372.wt_p19 RCN125.ysWeight_p19 ((coefficients phi P).coeff j)≤middle P-j∧
    RCN372.wt_p19 RCN125.totalWeight_p19 ((coefficients phi P).coeff j)≤total P-j:=by
  have hb: ∀e∈P.support,2*e 1+e 3≤slope P∧e 1+e 2+e 3≤middle P∧
      e 1+e 2+e 3+e 4≤total P:=by
    intro e he
    refine ⟨?_,?_,?_⟩
    · simpa [CB.slope,JW,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
    · simpa [middle,JW,HA] using MvPolynomial.le_weightedTotalDegree HA he
    · simpa [total,JW,Koala6831Ordinary.totalWeights] using MvPolynomial.le_weightedTotalDegree Koala6831Ordinary.totalWeights he
  have hw:=SecondJetHelperWeights.derivative_coefficient_weights P (slope P) (middle P) (total P) 0 j hb
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  have hs:=RCN130.CBQ phi ((SecondJetCoefficients.asS P).coeff j)
  rw [coefficients,Polynomial.coeff_map]
  exact ⟨hs.1.trans hw.1,hs.2.1.trans hw.2.1,hs.2.2.trans hw.2.2⟩
theorem EVL
    (phi:Polynomial K→+*E) (P:Poly5)
    (Q A:MvPolynomial (Fin 3) E) (target:E)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A):
    RCN095.PolynomialInFlag (ordinaryFlag P) (movingCut phi P (order P) Q A target):=by
  have hn:=_Q15 P
  have hcoeff:=FJA phi P
  have hAf:=FPY A hA
  have hQf:=RCN207.inFlag_sub_poly (inFlag_const (2 • unitAllFlag) target) hQ
  have hR:=BUF RCN125.sWeight_p19 (coefficients phi P) (order P) (slope P) 2 0 2
    hn.2.2.1 rfl (2*A) (MvPolynomial.C target-Q) (fun j=>(hcoeff j.val).1)
    (RCN125.DWH hAf) (RCN125.DWH hQf)
  have hM:=BUF RCN125.ysWeight_p19 (coefficients phi P) (order P) (middle P) 1 1 2
    (by simpa using hn.2.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j=>by simpa only [one_mul] using (hcoeff j.val).2.1)
    (RCN125.DNV hAf) (RCN125.DNV hQf)
  have hT:=BUF RCN125.totalWeight_p19 (coefficients phi P) (order P) (total P) 1 1 2
    (by simpa using hn.2.1.trans hn.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j=>by simpa only [one_mul] using (hcoeff j.val).2.2)
    (RCN125.COV hAf) (RCN125.COV hQf)
  intro e he
  have er:=(MvPolynomial.le_weightedTotalDegree RCN125.sWeight_p19 he).trans hR
  have em:=(MvPolynomial.le_weightedTotalDegree RCN125.ysWeight_p19 he).trans hM
  have et:=(MvPolynomial.le_weightedTotalDegree RCN125.totalWeight_p19 he).trans hT
  rw [RCN372.weight_fin3_p19] at er em et
  simp [RCN125.sWeight_p19,RCN125.ysWeight_p19,RCN125.totalWeight_p19] at er em et
  have hc:=RJ P
  change e 1≤_∧e 0+e 1≤_∧e 0+e 1+e 2≤_
  rw [hc.2.2,hc.2.1,hc.1]
  exact ⟨er,em,et⟩
end
end CB
end MergedPart3
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace NX
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open LK BD GZ
open MovingFiberThreeSources6811 (direction weight)
open CB
open CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
variable {K E:Type} [Field K] [Field E]
local notation "Poly5" =>MvPolynomial (Fin 5) K
theorem ADQ (ev:Poly5→+*E) (P:Poly5) (hP:P≠0) (hz:ev P=0):
    ∃J,Irreducible J∧J∣P∧ev J=0∧
      (UniqueOwner ev J P∨ ∃D,Irreducible D∧D∣P∧ev D=0∧IsRelPrime J D):=by
  obtain ⟨J,hJ,hJP,hroot,hsplit⟩:=EYA ev P P hP hP hz
  refine ⟨J,hJ,hJP,hroot,?_⟩
  rcases hsplit with huni | ⟨D,hD,hDP,hdroot,hcop⟩
  · exact Or.inl huni.1
  · exact Or.inr ⟨D,hD,hDP.elim id id,hdroot,hcop⟩
end
end NX
end MergedPart1
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace BVC
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open Polynomial
open SecondJetClearedHelper (cleared helper)
theorem DGM
    {R:Type*} [CommRing R] (P:Polynomial R) (x y:R) (d:ℕ)
    (hunit: ∀j<d,IsUnit (j.factorial:R))
    (hderiv: ∀j<d,((Polynomial.derivative)^[j] P).eval x=0)
    (hdiff:(y-x)^d=0):P.eval y=0:=by
  have hcoeff (j:ℕ) (hj:j<d):(Polynomial.taylor x P).coeff j=0:=by
    rw [Polynomial.taylor_coeff]
    have he0:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=R) (k:=j)) P
    change j.factorial • (Polynomial.hasseDeriv j P)=((Polynomial.derivative)^[j] P) at he0
    have he:=congrArg (fun Q:Polynomial R=>Q.eval x) he0
    simp only [nsmul_eq_mul,Polynomial.eval_mul,Polynomial.eval_natCast,hderiv j hj] at he
    exact (hunit j hj).mul_left_cancel (he.trans (mul_zero _).symm)
  obtain ⟨Q,hQ⟩:=Polynomial.X_pow_dvd_iff.mpr hcoeff
  have he:=congrArg (fun Q:Polynomial R=>Q.eval (y-x)) hQ
  rw [Polynomial.taylor_eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,hdiff,zero_mul] at he
  exact he
theorem AKH
    {R:Type*} [CommRing R] (J:Ideal R) [J.IsMaximal]
    (surface:R) (d:ℕ) (h:R) (hh:h∉J):
    IsUnit (Ideal.Quotient.mk (Ideal.span {surface} ⊔ J^d) h):=by
  have hu:=Ideal.Quotient.isUnit_mk_pow_of_notMem J (n:=d) hh
  have hm:=hu.map (Ideal.Quotient.factor (show J^d≤Ideal.span {surface} ⊔ J^d from le_sup_right))
  simpa only [Ideal.Quotient.factor_mk] using hm
theorem DQP
    {R:Type*} [CommRing R] (J:Ideal R) [J.IsMaximal]
    (surface H G A B:R) (s d:ℕ) (P:Polynomial R)
    (hdegree:P.natDegree≤s)
    (hH:H∉J) (hA:A∉J) (hM:H*B-A*G∈J)
    (hfact: ∀j<d,IsUnit (j.factorial:R))
    (hhelpers: ∀j<d,SecondJetClearedHelper.cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈Ideal.span {surface}):
    SecondJetClearedHelper.cleared P s A B∈Ideal.span {surface} ⊔ J^d:=by
  let I:=Ideal.span {surface} ⊔ J^d
  let q:=Ideal.Quotient.mk I
  obtain ⟨u,hu⟩:=AKH J surface d H hH
  obtain ⟨v,hv⟩:=AKH J surface d A hA
  change (↑u:R ⧸ I)=q H at hu
  change (↑v:R ⧸ I)=q A at hv
  let x:R ⧸ I:=(↑u⁻¹:R ⧸ I)*q G
  let y:R ⧸ I:=(↑v⁻¹:R ⧸ I)*q B
  have hx:q H*x=q G:=by simp [x,←hu,←mul_assoc]
  have hy:q A*y=q B:=by simp [y,←hv,←mul_assoc]
  have hh: ∀j<d,((Polynomial.derivative)^[j] (P.map q)).eval x=0:=by
    intro j hj
    have hm:SecondJetClearedHelper.cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈I:=
      (show Ideal.span {surface}≤I from le_sup_left) (hhelpers j hj)
    have he:q (SecondJetClearedHelper.cleared ((Polynomial.derivative)^[j] P) (s-j) H G)=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [SecondJetClearedHelper.map_cleared] at he
    have hdeg:(((Polynomial.derivative)^[j] P).map q).natDegree≤s-j:=
      Polynomial.natDegree_map_le.trans ((Polynomial.natDegree_iterate_derivative P j).trans
        (Nat.sub_le_sub_right hdegree j))
    rw [SecondJetClearedHelper.cleared_eval _ _ hdeg _ _ x hx,←Polynomial.iterate_derivative_map] at he
    exact ((AKH J surface d H hH).pow (s-j)).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hdiff:(y-x)^d=0:=by
    have hpow:(H*B-A*G)^d∈I:=
      (show J^d≤I from le_sup_right) (Ideal.pow_mem_pow hM d)
    have he:q (H*B-A*G)^d=0:=by
      rw [←map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpow
    have hrel:q H*q A*(y-x)=q (H*B-A*G):=by
      rw [map_sub,map_mul,map_mul]
      calc
        _=q H*(q A*y)-q A*(q H*x):=by ring
        _=_:=by rw [hy,hx]
    rw [←hrel,mul_pow] at he
    exact (((AKH J surface d H hH).mul
      (AKH J surface d A hA)).pow d).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hf (j:ℕ) (hj:j<d):IsUnit (j.factorial:R ⧸ I):=by
    simpa only [map_natCast] using (hfact j hj).map q
  have hz:=DGM (P.map q) x y d hf hh hdiff
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (SecondJetClearedHelper.cleared P s A B)=0
  rw [SecondJetClearedHelper.map_cleared,SecondJetClearedHelper.cleared_eval _ _ (Polynomial.natDegree_map_le.trans hdegree) _ _ y hy,hz,mul_zero]
end
end BVC
end MergedPart0
section MergedPart1
namespace CUG
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open RCN136 RCN207 RCN313
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open BD TH BVC
open MovingFiberThreeSources6811 (direction weight)
theorem DFN
    {R:Type*} [CommRing R] (J:Ideal R) [J.IsMaximal]
    (surface A B:R) (d n m:ℕ) (P:Polynomial R)
    (hn:P.natDegree≤n) (hm:P.natDegree≤m) (hA:A∉J)
    (hmem:SecondJetClearedHelper.cleared P n A B∈Ideal.span {surface} ⊔ J^d):
    SecondJetClearedHelper.cleared P m A B∈Ideal.span {surface} ⊔ J^d:=by
  let I:=Ideal.span {surface} ⊔ J^d
  let q:=Ideal.Quotient.mk I
  obtain ⟨u,hu⟩:=AKH J surface d A hA
  change (↑u:R ⧸ I)=q A at hu
  let y:R ⧸ I:=(↑u⁻¹:R ⧸ I)*q B
  have hy:q A*y=q B:=by simp [y,←hu,←mul_assoc]
  have hz:q (SecondJetClearedHelper.cleared P n A B)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [SecondJetClearedHelper.map_cleared,SecondJetClearedHelper.cleared_eval _ _ (Polynomial.natDegree_map_le.trans hn) _ _ y hy] at hz
  have he:=((AKH J surface d A hA).pow n).mul_left_cancel
    (hz.trans (mul_zero _).symm)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (SecondJetClearedHelper.cleared P m A B)=0
  rw [SecondJetClearedHelper.map_cleared,SecondJetClearedHelper.cleared_eval _ _ (Polynomial.natDegree_map_le.trans hm) _ _ y hy,he,mul_zero]
theorem EWD
    {K Ω R:Type} [Field K] [CharP K 2130706433] [Field Ω] [CommRing R]
    (phi:Polynomial K→+*Ω) (ev:MvPolynomial (Fin 3) Ω→+*R)
    (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (J:Ideal R) [J.IsMaximal] (surface:R) (d:ℕ)
    (hd:d≤S.d) (hchar:d≤2130706433)
    (hF:ev (surfaceMap phi F)∈Ideal.span {surface})
    (hH:ev (surfaceMap phi (2*polyH K F))∉J) (hA:ev (2*A)∉J)
    (hM:ev (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)∈J):
    ev (movingCut phi S.P S.s Q A target)∈Ideal.span {surface} ⊔ J^d:=by
  let psi:=ev.comp (surfaceMap phi)
  let P:=(SecondJetCoefficients.asS S.P).map psi
  have hdegree:P.natDegree≤S.s:=Polynomial.natDegree_map_le.trans (by
    simpa using SecondJetHelperWeights.asS_derivative_degree S.P S.s 0 S.hS)
  have hhelpers (j:ℕ) (hj:j<d):
      SecondJetClearedHelper.cleared ((Polynomial.derivative)^[j] P) (S.s-j) (psi (2*polyH K F)) (psi (polyG K F))∈Ideal.span {surface}:=by
    have hjk:j≤S.k:=by change d≤S.k+1 at hd;omega
    have hm:=(Ideal.span {surface}).mem_of_dvd (map_dvd psi (S.hdiv j hjk)) hF
    simpa only [SecondJetClearedHelper.helper,SecondJetClearedHelper.map_cleared,SecondJetCoefficientSpecialization.asS_iterate,Polynomial.iterate_derivative_map,P] using hm
  have hf (j:ℕ) (hj:j<d):IsUnit (j.factorial:R):=by
    have hk:IsUnit (j.factorial:K):=isUnit_iff_ne_zero.mpr
      (SecondJetOwnShape.factorial_ne j (by omega))
    simpa only [map_natCast] using hk.map (psi.comp MvPolynomial.C)
  have hm:psi (2*polyH K F)*ev (MvPolynomial.C target-Q)-ev (2*A)*psi (polyG K F)∈J:=by
    have he:psi (2*polyH K F)*ev (MvPolynomial.C target-Q)-ev (2*A)*psi (polyG K F)=
        2*ev (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target):=by
      simp only [psi,RingHom.comp_apply,RCN207.movingEquation,map_sub,map_mul,map_ofNat]
      ring
    rw [he]
    exact J.mul_mem_left _ hM
  have hh:=DQP J surface (psi (2*polyH K F)) (psi (polyG K F))
    (ev (2*A)) (ev (MvPolynomial.C target-Q)) S.s d P hdegree hH hA hm hf hhelpers
  simpa only [movingCut,SecondJetClearedHelper.map_cleared,coefficients,Polynomial.map_map,P,psi] using hh
theorem BKT
    {K Ω R:Type} [Field K] [CharP K 2130706433] [Field Ω] [CommRing R]
    (phi:Polynomial K→+*Ω) (ev:MvPolynomial (Fin 3) Ω→+*R)
    (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (J:Ideal R) [J.IsMaximal] (surface:R) (d n:ℕ)
    (hn:S.P.degreeOf 1≤n) (hd:d≤S.d) (hchar:d≤2130706433)
    (hF:ev (surfaceMap phi F)∈Ideal.span {surface})
    (hH:ev (surfaceMap phi (2*polyH K F))∉J) (hA:ev (2*A)∉J)
    (hM:ev (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)∈J):
    ev (movingCut phi S.P n Q A target)∈Ideal.span {surface} ⊔ J^d:=by
  have hfull:=EWD phi ev F S Q A target J surface d hd hchar hF hH hA hM
  have hn' :((coefficients phi S.P).map ev).natDegree≤n:=
    Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans
      ((FN.ABW S.P).trans_le hn))
  have hs' :((coefficients phi S.P).map ev).natDegree≤S.s:=
    Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans (by
      simpa using SecondJetHelperWeights.asS_derivative_degree S.P S.s 0 S.hS))
  simp only [movingCut,SecondJetClearedHelper.map_cleared] at hfull ⊢
  exact DFN J surface _ _ d S.s n _ hs' hn' hA hfull
section DUJ
variable {A:Type*} [CommRing A] [IsDomain A]
  [GCDMonoid (Polynomial A)] [NormalizationMonoid (Polynomial A)]
  [UniqueFactorizationMonoid (Polynomial A)]
theorem ECQ
    (P Q:Polynomial A) (n m:ℕ) (h q:A)
    (hP:P≠0) (hn:P.natDegree≤n) (hm:Q.natDegree≤m) (hh:h≠0) (hrel:IsRelPrime P Q)
    {R:Type*} [CommRing R] (ev:Polynomial A→+*R)
    (J:Ideal R) [J.IsMaximal] (surface:R) (d:ℕ)
    (hden:ev (Polynomial.C h)∉J)
    (hleft:ev (PH P n h q)∈Ideal.span {surface} ⊔ J^d)
    (hright:ev (PH Q m h q)∈Ideal.span {surface} ⊔ J^d):
    ev (RCN259.BZX (PH P n h q) (PH Q m h q))∈
        Ideal.span {surface} ⊔ J^d∧
    ev (RCN259.BPA (PH P n h q) (PH Q m h q))∈
        Ideal.span {surface} ⊔ J^d:=by
  let B:=PH P n h q
  let C:=PH Q m h q
  let I:=Ideal.span {surface} ⊔ J^d
  let red:=Ideal.Quotient.mk I
  let evJ:=(Ideal.Quotient.mk J).comp ev
  letI:Field (R ⧸ J):=Ideal.Quotient.field J
  have hnz:evJ (Polynomial.C h)≠0:=by
    intro hz
    exact hden (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hg:ev (gcd B C)∉J:=by
    intro hmem
    exact BJN.EXA P Q n m h q hP hn hm hh hrel evJ hnz
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hu:IsUnit (red (ev (gcd B C))):=AKH J surface d _ hg
  have htransfer (N T:Polynomial A) (heq:T=gcd B C*N) (hT:ev T∈I):ev N∈I:=by
    have hz:red (ev T)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hT
    rw [heq,map_mul,map_mul] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hu.mul_left_cancel (hz.trans (mul_zero _).symm))
  exact ⟨htransfer _ B (RCN259.AIV B C) hleft,
    htransfer _ C (RCN259.AGO B C) hright⟩
end DUJ
end
end CUG
end MergedPart1
section MergedPart2
namespace BFV
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN225 RCN307 RCN309
def thickPiece {R I:Type*} [CommRing R]
    (surface:I→R) (relation:I→Ideal R) (d:I→ℕ) (i:I):Ideal R:=
  Ideal.span {surface i} ⊔ relation i^d i
theorem FJJ {R I:Type*} [CommRing R]
    (surface:I→R) (relation:I→Ideal R) (d:I→ℕ)
    (hcop:Pairwise fun i j=>IsCoprime (relation i) (relation j)):
    Pairwise fun i j=>IsCoprime (thickPiece surface relation d i) (thickPiece surface relation d j):=by
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [←Ideal.pow_sup_pow_eq_top (hcop hij).sup_eq (m:=d i) (n:=d j)]
  exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
section Certificates
variable {R I:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [Fintype I]
def FAW
    (P Q:Polynomial R) (surface:I→Polynomial R)
    [∀i,(Ideal.span {surface i}).IsPrime]
    (relation:I→Ideal (Polynomial R))
    (relationBar: ∀i,Ideal (RCN225.SurfaceQuotient (surface i)))
    [∀i,(relationBar i).IsMaximal]
    [∀i,IsNoetherianRing (RCN225.SurfaceQuotient (surface i))]
    (hbar: ∀i,relationBar i=Ideal.map (Ideal.Quotient.mk (Ideal.span {surface i})) (relation i))
    (hbarNe: ∀i,relationBar i≠⊥)
    [∀i,IsLocalHom (algebraMap R (Localization.AtPrime (relationBar i)))]
    [∀i,FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))]
    (d:I→ℕ)
    (hP: ∀i,P∈thickPiece surface relation d i)
    (hQ: ∀i,Q∈thickPiece surface relation d i)
    (hcop:Pairwise fun i j=>IsCoprime (relation i) (relation j)):
    RCN307.PrimaryPiecesCertificate P Q (fun i=>d i*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))) where
  pieces:=thickPiece surface relation d
  coprime:=FJJ surface relation d hcop
  contains i:=by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ hP i
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hQ i
  length_le i:=RCN225.exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
    (R:=R) (surface i) (relation i) (relationBar i) (hbar i) (hbarNe i) (d i)
theorem FVF
    (surface:I→Polynomial R) (relation:I→Ideal (Polynomial R)) (d:I→ℕ)
    (hmonic: ∀i,∃M:Polynomial R,M.Monic∧M∈relation i) (i:I):
    Module.Finite R (Polynomial R ⧸ thickPiece surface relation d i):=by
  obtain ⟨M,hM,hmem⟩:=hmonic i
  exact RCN309.moduleFinite_quotient_of_monic_mem (thickPiece surface relation d i)
    (M^d i) (hM.pow _) ((show relation i^d i≤thickPiece surface relation d i from le_sup_right)
      (Ideal.pow_mem_pow hmem (d i)))
def FFD {P Q:Polynomial R} {d:I→ℕ} (C:RCN307.PrimaryPiecesCertificate P Q d):
    RCN307.PrimaryPiecesCertificate Q P d where
  pieces:=C.pieces
  coprime:=C.coprime
  contains i:=by simpa only [RCN307.intersectionIdeal,Set.pair_comm] using C.contains i
  length_le:=C.length_le
end Certificates
end
end BFV
end MergedPart2
section MergedPart3
namespace BXF
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN143 RCN307 BFV
variable {Base:Type} [Field Base]
local instance:DecidableEq Base:=Classical.decEq Base
theorem CTO
    (P Q:Polynomial (Polynomial Base)) (hP:P≠0) (hcop:IsRelPrime P Q):
    Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
  let R:=Polynomial Base
  let E:=FractionRing R
  let f:R→+*E:=algebraMap R E
  letI:Algebra (Polynomial R) (Polynomial E):=Polynomial.algebra R E
  letI:IsLocalization ((nonZeroDivisors R).map (Polynomial.C:R→+*Polynomial R).toMonoidHom)
      (Polynomial E):=Polynomial.isLocalization (nonZeroDivisors R) E
  letI:Module.Flat (Polynomial R) (Polynomial E):=IsLocalization.flat _
    ((nonZeroDivisors R).map (Polynomial.C:R→+*Polynomial R).toMonoidHom)
  have hinj:Function.Injective f:=IsFractionRing.injective R E
  have hrel:IsRelPrime (P.map f) (Q.map f):=
    VM.BHU (A:=Polynomial R) (B:=Polynomial E)
      (Polynomial.map_injective f hinj) P Q hP hcop
  have hr:=Polynomial.resultant_ne_zero (P.map f) (Q.map f) hrel.isCoprime
  rw [Polynomial.natDegree_map_eq_of_injective hinj,Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at hr
  intro hz
  exact hr (by rw [hz,map_zero])
theorem CKV
    (I:Ideal (Polynomial Base)) [I.IsPrime] (f:Polynomial Base) (hI:I=Ideal.span {f})
    (P:Polynomial (Polynomial Base))
    (hz:(P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0):
    Polynomial.C f∣P:=by
  apply (Polynomial.C_dvd_iff_dvd_coeff f P).mpr
  intro n
  have he:=congrArg (fun Q:Polynomial (IsLocalRing.ResidueField (LocalBase I))=>Q.coeff n) hz
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at he
  have hm:algebraMap (Polynomial Base) (LocalBase I) (P.coeff n)∈IsLocalRing.maximalIdeal (LocalBase I):=by
    rw [←IsLocalRing.ker_residue]
    exact he
  have hmem:=(IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalBase I) I (P.coeff n)).mp hm
  rw [hI,Ideal.mem_span_singleton] at hmem
  exact hmem
theorem EFG
    (I:Ideal (Polynomial Base)) [I.IsPrime] (f:Polynomial Base)
    (hI:I=Ideal.span {f}) (hf:Irreducible f)
    (P Q:Polynomial (Polynomial Base)) (hcop:IsRelPrime P Q):
    (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0∨
    (Q.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0:=by
  by_cases hp:(P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0
  · right
    intro hq
    exact hf.not_isUnit (Polynomial.isUnit_C.mp (hcop
      (CKV I f hI P hp) (CKV I f hI Q hq)))
  · exact Or.inl hp
theorem EVX
    (I:Ideal (Polynomial Base)) [I.IsPrime] (f:Polynomial Base)
    (hI:I=Ideal.span {f}) (hf:Irreducible f) (hfmonic:f.Monic)
    (P Q:Polynomial (Polynomial Base)) (m n:ℕ)
    (hP:P.natDegree≤m) (hQ:Q.natDegree≤n)
    (hcop:IsRelPrime P Q) (hres:Polynomial.resultant P Q m n≠0)
    {A:Type*} [Fintype A] (weight:A→ℕ)
    (C:RCN307.PrimaryPiecesCertificate
      (P.map (algebraMap (Polynomial Base) (LocalBase I)))
      (Q.map (algebraMap (Polynomial Base) (LocalBase I))) weight)
    [Module.Finite (LocalBase I) (∀a,Polynomial (LocalBase I) ⧸ C.pieces a)]:
    f^(∑ a,weight a)∣Polynomial.resultant P Q m n:=by
  rcases EFG I f hI hf P Q hcop with hp | hq
  · exact RN
      I f weight hI hf hfmonic P Q m n _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hP) (Polynomial.natDegree_map_le.trans hQ) hres hp C
  · have hr:Polynomial.resultant Q P n m≠0:=by
      rw [Polynomial.resultant_comm]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hres
    letI:Module.Finite (LocalBase I)
        (∀a,Polynomial (LocalBase I) ⧸ (FFD C).pieces a):=
      (inferInstance:Module.Finite (LocalBase I) (∀a,Polynomial (LocalBase I) ⧸ C.pieces a))
    have hb:=RN
      I f weight hI hf hfmonic Q P n m _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hQ) (Polynomial.natDegree_map_le.trans hP)
      hr hq (FFD C)
    rw [Polynomial.resultant_comm P Q m n]
    exact dvd_mul_of_dvd_right hb _
end
end BXF
end MergedPart3
section MergedPart4
namespace LF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 20000
open MvPolynomial RCN135 RCN136
open TH XK VM
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K E:Type} [Field K] [Field E]
def codeMap (f:GenericField K→+*E):Polynomial K→+*E:=
  f.comp (RCN135.polynomialEmbedding K)
theorem DTI (f:GenericField K→+*E):Function.Injective (codeMap f):=
  f.injective.comp (RCN135.polynomialEmbedding_injective K)
theorem ENE (f:GenericField K→+*E) (P:SecondJetSupport.Poly (K:=K)):
    sourceMap K (codeMap f) P=MvPolynomial.map f (AVG K P):=by
  simp only [sourceMap,AVG,codeMap,RingHom.comp_apply,MvPolynomial.map_map]
theorem BWA (f:GenericField K→+*E)
    (P:SecondJetSupport.Poly (K:=K)) (hP:P≠0):coefficients (codeMap f) P≠0:=by
  intro hz
  apply hP
  apply (SecondJetCoefficients.asS (K:=K)).injective
  apply Polynomial.map_injective (surfaceMap (codeMap f))
    (RCN136.surfaceMap_injective (codeMap f) (DTI f))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz
theorem CBP (f:GenericField K→+*E)
    (P:SecondJetSupport.Poly (K:=K)):
    (coefficients (codeMap f) P).natDegree≤P.degreeOf 1:=by
  exact Polynomial.natDegree_map_le.trans_eq (FN.ABW P)
theorem DPZ (f:GenericField K→+*E)
    (P Q:SecondJetSupport.Poly (K:=K)) (hP:P≠0) (hrel:IsRelPrime P Q):
    IsRelPrime (coefficients (codeMap f) P) (coefficients (codeMap f) Q):=by
  letI:Algebra (GenericField K) E:=f.toAlgebra
  letI:Module.Flat (MvPolynomial (Fin 4) (GenericField K)) (MvPolynomial (Fin 4) E):=CTQ
  have hsource:AVG K P≠0:=by
    intro hz
    have hv:=FLC K (RCN135.polynomialEmbedding K) P
    change MvPolynomial.finSuccEquiv (GenericField K) 3 (AVG K P)=
      coefficients (RCN135.polynomialEmbedding K) P at hv
    rw [hz,map_zero] at hv
    exact AQM.DZB K P hP hv.symm
  have hc:=BHU
    (MvPolynomial.map_injective (algebraMap (GenericField K) E) (algebraMap (GenericField K) E).injective)
    (AVG K P) (AVG K Q) hsource (EIC K P Q hP hrel)
  have hc' :IsRelPrime (sourceMap K (codeMap f) P) (sourceMap K (codeMap f) Q):=by
    rw [ENE,ENE]
    exact hc
  have hv:=BDS (MvPolynomial.finSuccEquiv E 3).toRingEquiv _ _ hc'
  change IsRelPrime (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) P))
    (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) Q)) at hv
  simpa only [FLC] using hv
end
end LF
end MergedPart4
section MergedPart5
namespace WC
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN095 RCN135 RCN136 RCN207 RCN259
open RCN095 renaming PolynomialInFlag → BI
open BD GZ
open MovingFiberThreeSources6811 (direction weight)
open TH AQM CKL
open CB CUG
open LF
variable {K E:Type} [Field K] [CharP K 2130706433] [Field E]
variable (f:GenericField K→+*E)
local notation "Omega" =>E
local notation "OmegaT" =>GenericField E
local notation "Poly3" =>MvPolynomial (Fin 3) E
local notation "Poly3T" =>MvPolynomial (Fin 3) OmegaT
local notation "phi" =>RingHom.comp (RCN135.coefficientEmbedding E) (codeMap f)
local notation "lift" =>MvPolynomial.map (RCN135.coefficientEmbedding E)
def OO (F:MvPolynomial (Fin 4) K):Poly3T:=surfaceMap phi F
def XC (F:MvPolynomial (Fin 4) K) (Q A:Poly3):Poly3T:=
  RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F))
    (lift Q) (lift A) (RCN135.initialCoordinate E)
def AOT (F:MvPolynomial (Fin 4) K) (A:Poly3):Poly3T:=
  surfaceMap phi (2*RCN313.polyH K F)*lift (2*A)
theorem BMZ:Function.Injective (OO f):=
  RCN136.surfaceMap_injective phi ((RCN135.coefficientEmbedding E).injective.comp (DTI f))
theorem CWZ
    (F:MvPolynomial (Fin 4) K) (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433):
    MvPolynomial.pderiv (1:Fin 3) (OO f F)≠0:=by
  rw [OO,RCN267.surfaceMap_pderiv_R]
  intro hz
  apply RCN267.R_derivative_nonzero F 2130706433 hpos hsmall
  apply BMZ f
  simpa only [OO,map_zero] using hz
theorem CBI
    (J:SecondJetSupport.Poly (K:=K)) (Q A:Poly3)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A):
    RCN095.PolynomialInFlag (ordinaryFlag J)
      (VY E (PH (coefficients (codeMap f) J) (order J) (2*A) Q)):=by
  rw [BDY]
  exact EVL phi J (lift Q) (lift A) (RCN135.initialCoordinate E)
    (inFlag_map _ hQ) (inFlag_map _ hA)
theorem EFY
    (F:MvPolynomial (Fin 4) K) (S T:MovingFiberThreeSources6811.Source F) (hcop:IsRelPrime S.P T.P)
    (d:ℕ) (hS:d≤S.d) (hT:d≤T.d) (hchar:d≤2130706433)
    (Q A:Poly3) (hden:(2:Poly3)*A≠0)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A):
    ∃B C:Poly3T,B≠0∧C≠0∧IsRelPrime B C∧
      RCN095.PolynomialInFlag (ordinaryFlag S.P) B∧RCN095.PolynomialInFlag (ordinaryFlag T.P) C∧
      ∀(R:Type) [CommRing R] (ev:Poly3T→+*R) (J:Ideal R) [J.IsMaximal] (surface:R),
        ev (OO f F)∈Ideal.span {surface}→
        ev (surfaceMap phi (2*RCN313.polyH K F))∉J→
        ev (lift (2*A))∉J→ev (XC f F Q A)∈J→
        ev B∈Ideal.span {surface} ⊔ J^d∧ev C∈Ideal.span {surface} ⊔ J^d:=by
  letI:StrongNormalizationMonoid (Polynomial Poly3):=UniqueFactorizationMonoid.strongNormalizationMonoid
  letI:NormalizedGCDMonoid (Polynomial Poly3):=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let P:=coefficients (codeMap f) S.P
  let U:=coefficients (codeMap f) T.P
  let rawP:=PH P (order S.P) (2*A) Q
  let rawU:=PH U (order T.P) (2*A) Q
  let B0:=BZX rawP rawU
  let C0:=BPA rawP rawU
  have hp:P≠0:=BWA f S.P (AHY F S)
  have hu:U≠0:=BWA f T.P (AHY F T)
  have hnp:P.natDegree≤order S.P:=CBP f S.P
  have hnu:U.natDegree≤order T.P:=CBP f T.P
  have hPU:IsRelPrime P U:=DPZ f
    S.P T.P (AHY F S) hcop
  have hrawP:rawP≠0:=ARX.BQG P _ (2*A) Q hp hnp hden
  have hrawU:rawU≠0:=ARX.BQG U _ (2*A) Q hu hnu hden
  have hPB:rawP=gcd rawP rawU*B0:=AIV rawP rawU
  have hUC:rawU=gcd rawP rawU*C0:=AGO rawP rawU
  have hB0:B0≠0:=fun hz=>hrawP (by rw [hPB,hz,mul_zero])
  have hC0:C0≠0:=fun hz=>hrawU (by rw [hUC,hz,mul_zero])
  have hBdiv:B0∣rawP:=⟨gcd rawP rawU,hPB.trans (mul_comm _ _)⟩
  have hCdiv:C0∣rawU:=⟨gcd rawP rawU,hUC.trans (mul_comm _ _)⟩
  have hmapne {V:Polynomial Poly3} (hV:V≠0):VY Omega V≠0:=
    fun hz=>hV (EGV Omega (by simpa only [map_zero] using hz))
  refine ⟨VY Omega B0,VY Omega C0,hmapne hB0,hmapne hC0,
    EKY Omega B0 C0 hB0 (DKA hrawP),?_,?_,?_⟩
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (VY Omega) hBdiv)
      (hmapne hrawP) (CBI f S.P Q A hQ hA)
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (VY Omega) hCdiv)
      (hmapne hrawU) (CBI f T.P Q A hQ hA)
  · intro R _ ev J _ surface hF hH hdenJ hM
    let ev0:=ev.comp (VY Omega)
    have hden0:ev0 (Polynomial.C (2*A))∉J:=by
      simpa only [ev0,RingHom.comp_apply,EMK] using hdenJ
    have hAprime:ev (2*lift A)∉J:=by
      simpa only [map_mul,map_ofNat] using hdenJ
    have hleft:=BKT phi ev F S (lift Q) (lift A)
      (RCN135.initialCoordinate Omega) J surface d (order S.P) le_rfl hS hchar hF hH hAprime hM
    have hright:=BKT phi ev F T (lift Q) (lift A)
      (RCN135.initialCoordinate Omega) J surface d (order T.P) le_rfl hT hchar hF hH hAprime hM
    have hl:ev0 rawP∈Ideal.span {surface} ⊔ J^d:=by
      simpa only [ev0,rawP,P,RingHom.comp_apply,BDY] using hleft
    have hr:ev0 rawU∈Ideal.span {surface} ⊔ J^d:=by
      simpa only [ev0,rawU,U,RingHom.comp_apply,BDY] using hright
    exact ECQ P U _ _ (2*A) Q hp hnp hnu hden hPU ev0 J surface d hden0 hl hr
end
end WC
end MergedPart5
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace BAE
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped Classical
open RCN143
theorem CRQ
    {R:Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (I:Ideal R) [I.IsPrime] (F:R) (hF:F≠0) (hmem:F∈I):
    ∃G,Irreducible G∧G∣F∧G∈I:=by
  obtain ⟨factors,hfactor,hprod⟩:=WfDvdMonoid.exists_factors F hF
  let ev:=Ideal.Quotient.mk I
  have hz:ev F=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have ha:=Associated.map ev hprod
  rw [hz] at ha
  have hp:ev factors.prod=0:=(associated_zero_iff_eq_zero _).mp ha
  rw [map_multiset_prod] at hp
  obtain ⟨g,hg,hzero⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  exact ⟨g,hfactor g hg,(Multiset.dvd_prod hg).trans hprod.dvd,
    Ideal.Quotient.eq_zero_iff_mem.mp hzero⟩
variable {Base:Type} [Field Base]
local instance:DecidableEq Base:=Classical.decEq Base
@[reducible] local instance localPlaneSemiring (I:Ideal (Polynomial Base)) [I.IsPrime]:
    Semiring (Polynomial (LocalBase I)):=Polynomial.commSemiring.toSemiring
theorem BLA
    (I:Ideal (Polynomial Base)) [I.IsPrime]
    (J:Ideal (Polynomial (Polynomial Base)))
    (hcontract:J.comap Polynomial.C=I)
    (G:Polynomial (Polynomial Base)) (hG:Irreducible G) (hGmem:G∈J):
    (Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))}).IsPrime∧
    (Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))}).comap
        (Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I)))=Ideal.span {G}:=by
  let C:Polynomial Base→+*Polynomial (Polynomial Base):=Polynomial.C
  let M:=I.primeCompl.map C.toMonoidHom
  let R:=Polynomial (LocalBase I)
  letI:Algebra (Polynomial (Polynomial Base)) R:=Polynomial.algebra (Polynomial Base) (LocalBase I)
  letI:IsLocalization M R:=Polynomial.isLocalization I.primeCompl (LocalBase I)
  have hd:Disjoint (M:Set (Polynomial (Polynomial Base)))
      (Ideal.span {G}:Set (Polynomial (Polynomial Base))):=by
    rw [Set.disjoint_left]
    intro x hx hxG
    obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
    have hm:C r∈J:=J.mem_of_dvd (Ideal.mem_span_singleton.mp hxG) hGmem
    have hh:r∈J.comap Polynomial.C:=hm
    rw [hcontract] at hh
    exact hr hh
  have hprime:=Ideal.isPrime_span_singleton_of_prime hG.prime
  have hp:=IsLocalization.isPrime_of_isPrime_disjoint M R (Ideal.span {G}) hprime hd
  have hc:=IsLocalization.under_map_of_isPrime_disjoint M R hprime hd
  have hval:algebraMap (Polynomial (Polynomial Base)) R G=
      G.map (algebraMap (Polynomial Base) (LocalBase I)):=rfl
  have hspan:(Ideal.span {G.map (algebraMap (Polynomial Base) (LocalBase I))}:Ideal R)=
      Ideal.map (algebraMap (Polynomial (Polynomial Base)) R) (Ideal.span {G}):=by
    rw [Ideal.map_span,Set.image_singleton,hval]
  constructor
  · rw [hspan]
    exact hp
  · rw [hspan]
    exact hc
theorem DFH
    (I:Ideal (Polynomial Base)) [I.IsPrime]
    (J:Ideal (Polynomial (Polynomial Base)))
    (hcontract:J.comap Polynomial.C=I)
    (G:Polynomial (Polynomial Base)) (hG:Irreducible G) (hGmem:G∈J)
    (P Q:Polynomial (Polynomial Base)) (hcop:IsRelPrime P Q) (hP:P∈J) (hQ:Q∈J):
    let f:=Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I))
    Ideal.map (Ideal.Quotient.mk (Ideal.span {f G})) (Ideal.map f J)≠⊥ :=by
  let f:=Polynomial.mapRingHom (algebraMap (Polynomial Base) (LocalBase I))
  let q:=Ideal.Quotient.mk (Ideal.span {f G})
  change Ideal.map q (Ideal.map f J)≠⊥
  intro hbot
  have hc:=(BLA I J hcontract G hG hGmem).2
  have hd (N:Polynomial (Polynomial Base)) (hN:N∈J):G∣N:=by
    have hm:q (f N)∈Ideal.map q (Ideal.map f J):=
      Ideal.mem_map_of_mem q (Ideal.mem_map_of_mem f hN)
    have hz:q (f N)=0:=Ideal.mem_bot.mp (hbot ▸ hm)
    have hh:f N∈Ideal.span {f G}:=Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hn:N∈(Ideal.span {f G}).comap f:=hh
    have hc' :(Ideal.span {f G}).comap f=Ideal.span {G}:=by
      simpa only [f,Polynomial.coe_mapRingHom] using hc
    rw [hc',Ideal.mem_span_singleton] at hn
    exact hn
  exact hG.not_isUnit (hcop (hd P hP) (hd Q hQ))
end
end BAE
end MergedPart0
section MergedPart1
namespace CKZ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open RCN002 RCN011 RCN021 RCN022 RCN093 RCN102 RCN106 RCN107 RCN110 RCN111 RCN120 RCN226 RCN264
open BFV BXF BAE
variable {Ω:Type} [Field Ω]
variable {G T H:MvPolynomial (Fin 3) Ω} {A:Type} [Fintype A]
variable (component:A→RCN264.RegularComponent Ω G T H) (hinj:Function.Injective component)
variable (lam mu nu:Ω) (order:Fin 3 ≃ Fin 3)
variable (ht: ∀a,Transcendental Ω
  (RCN093.flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite: ∀a,
  letI:=RCN120.flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
  FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (component a).1))
variable (hgen: ∀a,
  letI:=RCN120.flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
  IntermediateField.adjoin (RatFunc Ω)
    ({RCN093.flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 2)),
      RCN093.flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
      Set (RCN002.CoordinateField Ω (component a).1))=⊤)
include hinj hgen in
theorem DQX
    (P Q:PlaneRing Ω) (hPne:P≠0) (hcop:IsRelPrime P Q)
    (hPmem: ∀a,P∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (hQmem: ∀a,Q∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (carrier:A→PlaneRing Ω) (hcarrier: ∀a,Irreducible (carrier a))
    (hcarrierMem: ∀a,carrier a∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (d:A→ℕ) (q:Polynomial (RatFunc Ω)) (hq:Irreducible q) (hqMonic:q.Monic)
    (hleft: ∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
      RCN102.fiberLocalizePlane q hq P∈Ideal.span {RCN102.fiberLocalizePlane q hq (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu order ht q hq a^d a.1)
    (hright: ∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
      RCN102.fiberLocalizePlane q hq Q∈Ideal.span {RCN102.fiberLocalizePlane q hq (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu order ht q hq a^d a.1):
    q^(∑ a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
      d a.1*RCN111.indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1)∣
      Polynomial.resultant P Q P.natDegree Q.natDegree:=by
  let Fib:=RCN106.IndexedFactorFiber component lam mu nu order ht q
  let I:Ideal (Polynomial (RatFunc Ω)):=Ideal.span {q}
  letI:I.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
  let R:=RCN102.FiberCoefficient q hq
  let surf (a:Fib):=RCN102.fiberLocalizePlane q hq (carrier a.1)
  let rel:=RCN106.indexedFiberRelation component lam mu nu order ht q hq
  let bar (a:Fib):=RCN106.indexedFiberRelationBar component lam mu nu order ht q hq (carrier a.1) a
  have hcontract (a:Fib):
      (RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a.1).1) order
        (RCN093.flagEvaluation Ω (component a.1).1 lam mu nu) (ht a.1)).comap Polynomial.C=I:=by
    rw [RCN226.relationKernel_comap_C]
    exact congrArg (fun f=>Ideal.span {f}) a.2.symm
  letI: ∀a:Fib,(Ideal.span {surf a}).IsPrime:=fun a=>
    (BLA I _ (hcontract a) (carrier a.1) (hcarrier a.1) (hcarrierMem a.1)).1
  letI: ∀a:Fib,(rel a).IsMaximal:=
    RCN106.indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen q hq
  letI: ∀a:Fib,(bar a).IsMaximal:=fun a=>by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f:=Ideal.Quotient.mk (Ideal.span {surf a})) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker,Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.mem_map_of_mem (RCN102.fiberLocalizePlane q hq) (hcarrierMem a.1)
  have hbar (a:Fib):bar a=Ideal.map (Ideal.Quotient.mk (Ideal.span {surf a})) (rel a):=rfl
  have hbarNe (a:Fib):bar a≠⊥ :=
    DFH I _ (hcontract a) (carrier a.1) (hcarrier a.1)
      (hcarrierMem a.1) P Q hcop (hPmem a.1) (hQmem a.1)
  letI: ∀a:Fib,IsLocalHom (algebraMap R (Localization.AtPrime (bar a))):=fun a=>
    RCN110.indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite q hq (carrier a.1) a
  letI: ∀a:Fib,FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (bar a))):=fun a=>
    RCN110.indexedNaturalSurfaceResidue_finite component lam mu nu order ht hfinite hgen q hq
      (carrier a.1) a (hcarrierMem a.1)
  let C:=FAW (RCN102.fiberLocalizePlane q hq P) (RCN102.fiberLocalizePlane q hq Q)
    surf rel bar hbar hbarNe (fun a:Fib=>d a.1) hleft hright
    (AYL component hinj lam mu nu order ht hfinite hgen q hq)
  letI: ∀a:Fib,Module.Finite R (Polynomial R ⧸ C.pieces a):=
    FVF surf rel (fun a:Fib=>d a.1)
      (RCN107.exists_monic_mem_indexedFiberRelation component lam mu nu order ht hfinite hgen q hq)
  letI:Module.Finite R (∀a:Fib,Polynomial R ⧸ C.pieces a):=inferInstance
  have hp:=EVX I q rfl hq hqMonic P Q P.natDegree Q.natDegree
    le_rfl le_rfl hcop (CTO P Q hPne hcop) _ C
  have he (a:Fib):Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (bar a)))=
        RCN111.indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
    RCN110.indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu order ht hfinite hgen q hq
      (carrier a.1) a (hcarrierMem a.1)
  change q^(∑ a:Fib,d a.1*Module.finrank (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (Localization.AtPrime (bar a))))∣_ at hp
  simpa only [he] using hp
include hinj hgen hfinite in
theorem EFQ
    [IsAlgClosed Ω]
    (hgate: ∀a,∀hx:Transcendental Ω
        (RCN093.flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))),
      (letI:=RCN120.flagBaseAlgebra Ω (component a).1 lam mu nu order hx;
        FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (component a).1))∧
      (letI:=RCN120.flagBaseAlgebra Ω (component a).1 lam mu nu order hx;
        Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (component a).1)))
    (P Q:PlaneRing Ω) (hPne:P≠0) (hcop:IsRelPrime P Q)
    (hPmem: ∀a,P∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (hQmem: ∀a,Q∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (carrier:A→PlaneRing Ω) (hcarrier: ∀a,Irreducible (carrier a))
    (hcarrierMem: ∀a,carrier a∈RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component a).1) order
      (RCN093.flagEvaluation Ω (component a).1 lam mu nu) (ht a))
    (d:A→ℕ)
    (hthick: ∀(q:Polynomial (RatFunc Ω)) (hq:Irreducible q)
      (a:RCN106.IndexedFactorFiber component lam mu nu order ht q),
      (RCN102.fiberLocalizePlane q hq P∈Ideal.span {RCN102.fiberLocalizePlane q hq (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu order ht q hq a^d a.1)∧
      (RCN102.fiberLocalizePlane q hq Q∈Ideal.span {RCN102.fiberLocalizePlane q hq (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu order ht q hq a^d a.1)):
    (∑ a,d a*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (component a).1)
      (RCN042.coordinateOfGate
        (RCN093.flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))) (hgate a)))≤
      (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree:=by
  let C:=RCN104.RI component lam mu nu order
    ht hfinite hgen hgate d (Polynomial.resultant P Q P.natDegree Q.natDegree)
    (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree
    (CTO P Q hPne hcop) le_rfl
    (fun q hq hm _=>DQX component hinj lam mu nu order ht hfinite hgen
      P Q hPne hcop hPmem hQmem carrier hcarrier hcarrierMem d q hq hm
      (fun a=>(hthick q hq a).1) (fun a=>(hthick q hq a).2))
  exact C.CTA
end
end CKZ
end MergedPart1
section MergedPart2
namespace ANV
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 700000
open scoped BigOperators Classical
open RCN002 RCN011 RCN021 RCN022 RCN093 RCN095 RCN102 RCN106 RCN113 RCN120 RCN125 RCN264 RCN333 RCN371
open RCN095 renaming PolynomialInFlag → BI
open RCN371 renaming RationalPolynomials → KU
open VM JS YL
open BAE CKZ
variable {Ω:Type} [Field Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem FSF (order:Fin 3 ≃ Fin 3)
    (B C:MvPolynomial (Fin 3) Ω) (hB:B≠0) (hcop:IsRelPrime B C):
    IsRelPrime (planeMap Ω order B) (planeMap Ω order C):=by
  letI:Module.Flat (Polynomial Ω) (RatFunc Ω):=
    IsLocalization.flat (RatFunc Ω) (nonZeroDivisors (Polynomial Ω))
  letI:Algebra (Collected Ω) (RCN371.RationalPolynomials Ω):=MvPolynomial.algebraMvPolynomial
  letI:Module.Flat (Collected Ω) (RCN371.RationalPolynomials Ω):=CTQ
  have hcol:collect Ω order B≠0:=fun hz=>hB ((collect Ω order).injective (hz.trans (map_zero _).symm))
  have hh:IsRelPrime (rationalMap Ω order B) (rationalMap Ω order C):=
    BHU (A:=Collected Ω) (B:=RCN371.RationalPolynomials Ω)
      (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)))
      (collect Ω order B) (collect Ω order C) hcol
      (BDS (collect Ω order).toRingEquiv B C hcop)
  exact BDS (RCN011.bivariateEquiv (RatFunc Ω)).toRingEquiv _ _ hh
def HasThickness (G H A M B C:MvPolynomial (Fin 3) Ω) (d:ℕ):Prop:=
  ∀(R:Type) [CommRing R] (ev:MvPolynomial (Fin 3) Ω→+*R)
    (J:Ideal R) [J.IsMaximal] (surface:R),
    ev G∈Ideal.span {surface}→ev H∉J→ev A∉J→ev M∈J→
    ev B∈Ideal.span {surface} ⊔ J^d∧ev C∈Ideal.span {surface} ⊔ J^d
theorem HasThickness.mem_regular
    {G H A M B C:MvPolynomial (Fin 3) Ω} {d:ℕ}
    (thick:HasThickness G H A M B C d) (hd:0<d)
    (V:RCN264.RegularComponent Ω G M (H*A)):B∈V.1∧C∈V.1:=by
  let E:=RCN002.CoordinateField Ω V.1
  let ev:=(RCN002.coordinateEvaluation Ω V.1).toRingHom
  letI:(⊥ :Ideal E).IsMaximal:=Ideal.bot_isMaximal
  have he (P:MvPolynomial (Fin 3) Ω):ev P=0 ↔ P∈V.1:=by
    change P∈RingHom.ker (RCN002.coordinateEvaluation Ω V.1).toRingHom ↔ P∈V.1
    rw [RCN002.coordinateEvaluation_ker]
  have hH:H∉V.1:=fun hm=>_Q6 Ω G M (H*A) V (V.1.mul_mem_right A hm)
  have hA:A∉V.1:=fun hm=>_Q6 Ω G M (H*A) V (V.1.mul_mem_left H hm)
  have hz:=thick E ev ⊥ 0
    (by rw [(he G).mpr (EN Ω G M (H*A) V)];exact Ideal.zero_mem _)
    (by simpa only [Ideal.mem_bot] using (he H).not.mpr hH)
    (by simpa only [Ideal.mem_bot] using (he A).not.mpr hA)
    (by exact (he M).mpr (GV Ω G M (H*A) V))
  have hI:(Ideal.span ({(0:E)}:Set E) ⊔ (⊥ :Ideal E)^d)=(⊥ :Ideal E):=by
    rw [Ideal.span_singleton_eq_bot.mpr rfl,Ideal.bot_pow (Nat.ne_of_gt hd),sup_bot_eq]
  have hB0:ev B=0:=Ideal.mem_bot.mp (hI ▸ hz.1)
  have hC0:ev C=0:=Ideal.mem_bot.mp (hI ▸ hz.2)
  exact ⟨(he B).mp hB0,(he C).mp hC0⟩
theorem ECO
    [IsAlgClosed Ω]
    (G H A M B C:MvPolynomial (Fin 3) Ω) (hG:G≠0) (hB:B≠0) (hC:C≠0)
    (hcop:IsRelPrime B C) (d:ℕ) (hd:0<d) (thick:HasThickness G H A M B C d)
    {ι:Type} [Fintype ι] (component:ι→RCN264.RegularComponent Ω G M (H*A))
    (hinj:Function.Injective component) (axis:Axis) (lam mu nu:Ω)
    (ht: ∀i,Transcendental Ω
      (RCN093.flagEvaluation Ω (component i).1 lam mu nu (MvPolynomial.X (axis.order 0))))
    (hgate: ∀i,∀hx:Transcendental Ω
      (RCN093.flagEvaluation Ω (component i).1 lam mu nu (MvPolynomial.X (axis.order 0))),
      (letI:=RCN120.flagBaseAlgebra Ω (component i).1 lam mu nu axis.order hx;
        FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (component i).1))∧
      (letI:=RCN120.flagBaseAlgebra Ω (component i).1 lam mu nu axis.order hx;
        Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (component i).1)))
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q C):
    d*(∑ i,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (component i).1)
      (RCN042.coordinateOfGate (RCN093.flagEvaluation Ω (component i).1 lam mu nu
        (MvPolynomial.X (axis.order 0))) (hgate i)))≤flagMixed p q axis.flag:=by
  let plane:=flagPlaneMap_p19 Ω lam mu nu axis.order
  let P:=plane B
  let Q:=plane C
  let W:=plane G
  have hFlagInj:Function.Injective (flagAlgHom_p19 lam mu nu:MvPolynomial (Fin 3) Ω→ₐ[Ω] _):=by
    intro P₁ P₂ h
    apply (flagEquiv_p19 lam mu nu).injective
    exact h
  have hinjPlane:Function.Injective plane:=by
    intro P₁ P₂ hh
    change planeMap Ω axis.order (flagAlgHom_p19 lam mu nu P₁)=
      planeMap Ω axis.order (flagAlgHom_p19 lam mu nu P₂) at hh
    exact hFlagInj (RCN011.planeMap_injective Ω axis.order hh)
  have hPne:P≠0:=by
    intro hz
    apply hB
    apply hinjPlane
    exact hz.trans (map_zero plane).symm
  have hWne:W≠0:=by
    intro hz
    apply hG
    apply hinjPlane
    exact hz.trans (map_zero plane).symm
  have hflagB:flagAlgHom_p19 lam mu nu B≠0:=fun hz=>
    hB (hFlagInj (hz.trans (map_zero (flagAlgHom_p19 lam mu nu)).symm))
  have hflagRel:IsRelPrime (flagAlgHom_p19 lam mu nu B) (flagAlgHom_p19 lam mu nu C):=by
    simpa only [AlgEquiv.coe_ringEquiv,EKI] using
      BDS (flagEquiv_p19 lam mu nu).toRingEquiv B C hcop
  have hrel:IsRelPrime P Q:=FSF (Ω:=Ω) axis.order
    (flagAlgHom_p19 lam mu nu B) (flagAlgHom_p19 lam mu nu C) hflagB hflagRel
  let hfinite i:=(hgate i (ht i)).1
  have hgen i:=CWN Ω (component i).1 axis lam mu nu (ht i)
  let rel i:=RCN021.relationKernel Ω (RCN002.CoordinateField Ω (component i).1) axis.order
    (RCN093.flagEvaluation Ω (component i).1 lam mu nu) (ht i)
  letI: ∀i,(rel i).IsPrime:=fun i=>RingHom.ker_isPrime _
  have hroot i:P∈rel i∧Q∈rel i:=by
    have hm:=thick.mem_regular hd (component i)
    exact ⟨AFZ (component i).1 lam mu nu axis.order (ht i) hm.1,
      AFZ (component i).1 lam mu nu axis.order (ht i) hm.2⟩
  have hWmem i:W∈rel i:=AFZ (component i).1 lam mu nu axis.order (ht i)
    (EN Ω G M (H*A) (component i))
  have hex i: ∃V,Irreducible V∧V∣W∧V∈rel i:=
    CRQ (rel i) W hWne (hWmem i)
  choose carrier hcarrier hdiv hcarrierMem using hex
  have hthick (r:Polynomial (RatFunc Ω)) (hr:Irreducible r)
      (a:RCN106.IndexedFactorFiber component lam mu nu axis.order ht r):
      (RCN102.fiberLocalizePlane r hr P∈Ideal.span {RCN102.fiberLocalizePlane r hr (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu axis.order ht r hr a^d)∧
      (RCN102.fiberLocalizePlane r hr Q∈Ideal.span {RCN102.fiberLocalizePlane r hr (carrier a.1)} ⊔
        RCN106.indexedFiberRelation component lam mu nu axis.order ht r hr a^d):=by
    let J:=RCN106.indexedFiberRelation component lam mu nu axis.order ht r hr a
    let ev:=(RCN102.fiberLocalizePlane r hr).comp plane
    letI:J.IsMaximal:=RCN106.indexedFiberRelation_isMaximal component lam mu nu axis.order ht
      hfinite hgen r hr a
    have hc:J.comap ev=(component a.1).1:=by
      change J.comap ((RCN102.fiberLocalizePlane r hr).comp
        ((planeMap Ω axis.order).comp (flagAlgHom_p19 lam mu nu).toRingHom))=_
      rw [←Ideal.comap_comap,RCN106.indexedFiberRelation_under,←Ideal.comap_comap,
        RCN021.relationKernel_contract,AEE]
    have hF:ev G∈Ideal.span {RCN102.fiberLocalizePlane r hr (carrier a.1)}:=
      Ideal.mem_span_singleton.mpr (map_dvd (RCN102.fiberLocalizePlane r hr) (hdiv a.1))
    have hH:ev H∉J:=by
      intro hm
      have hh:H∈(component a.1).1:=by rw [←hc];exact hm
      exact _Q6 Ω G M (H*A) (component a.1)
        ((component a.1).1.mul_mem_right A hh)
    have hA:ev A∉J:=by
      intro hm
      have hh:A∈(component a.1).1:=by rw [←hc];exact hm
      exact _Q6 Ω G M (H*A) (component a.1)
        ((component a.1).1.mul_mem_left H hh)
    have hM:ev M∈J:=by
      change M∈J.comap ev
      rw [hc]
      exact GV Ω G M (H*A) (component a.1)
    have hh:=thick (Polynomial (RCN102.FiberCoefficient r hr)) ev J
      (RCN102.fiberLocalizePlane r hr (carrier a.1)) hF hH hA hM
    have hBvalue:ev B=RCN102.fiberLocalizePlane r hr P:=rfl
    have hCvalue:ev C=RCN102.fiberLocalizePlane r hr Q:=rfl
    rw [hBvalue,hCvalue] at hh
    exact hh
  have hb:=EFQ component hinj lam mu nu axis.order ht hfinite hgen hgate
    P Q hPne hrel (fun i=>(hroot i).1) (fun i=>(hroot i).2)
    carrier hcarrier hcarrierMem (fun _=>d) hthick
  rw [←Finset.mul_sum] at hb
  exact hb.trans (BPQ axis lam mu nu B C p q hp hq hC)
end
end ANV
end MergedPart2
section MergedPart3
namespace BHB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 700000
open scoped BigOperators Classical
open RCN002 RCN022 RCN032 RCN037 RCN042 RCN046 RCN093 RCN095 RCN116 RCN264 RCN338 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open JS BJX ALP
open ANV
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
variable {G H A M B C:MvPolynomial (Fin 3) Ω}
def EJC
    (base: ∀V:RCN264.RegularComponent Ω G M (H*A),RCN341.SeparableLiteralCoordinate V.1)
    (hY: ∀V:RCN264.RegularComponent Ω G M (H*A),RCN037.LiteralProjectionGate V 0)
    (hZ: ∀V:RCN264.RegularComponent Ω G M (H*A),RCN037.LiteralProjectionGate V 2)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
    (D:AOH base hY hZ hderiv)
    (hG:G≠0) (hB:B≠0) (hC:C≠0) (hcop:IsRelPrime B C)
    (d:ℕ) (hd:0<d) (thick:HasThickness G H A M B C d)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q C):
    let unit:=BKX base hY hZ hderiv D B C hB hC hcop
      (fun V=>(thick.mem_regular hd V).1) (fun V=>(thick.mem_regular hd V).2) p q hp hq
    EY unit.toFE (fun _=>d):=by
  let x (axis:Axis) (V:RCN264.RegularComponent Ω G M (H*A)):=
    RCN093.flagEvaluation Ω V.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis:Axis) (V:RCN264.RegularComponent Ω G M (H*A)) (ht:Transcendental Ω (x axis V)):
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω V.1))∧
      (letI:=(RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω V.1)):=by
    cases axis with
    | z=>
      have hz:Transcendental Ω (coordinate Ω V.1 2):=by simpa [x,Axis.order,RCN125.zOrder_p19] using ht
      have he:=RCN116.elementEmbedding_congr ht hz (by simp [x,Axis.order,RCN125.zOrder_p19])
      rw [he]
      exact hZ V hz
    | u=>
      have hu:Transcendental Ω (affineU Ω V.1 D.lam):=by simpa [x,Axis.order,RCN125.uOrder_p19] using ht
      have he:=RCN116.elementEmbedding_congr ht hu (by simp [x,Axis.order,RCN125.uOrder_p19])
      rw [he]
      exact D.uGate V hu
    | v=>
      have he:=RCN116.elementEmbedding_congr ht (D.GN V) (by simp [x,Axis.order,RCN125.vOrder_p19])
      rw [he]
      exact ⟨D.allFinite V,D.allSeparable V⟩
  have hsum (axis:Axis):
      (∑ V:RCN264.RegularComponent Ω G M (H*A),d*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω V.1)
        (RCN042.coordinateOfGate (x axis V) (gate axis V)))≤flagMixed p q axis.flag:=by
    rw [RCN032.sum_mul_coordinateOfGate_eq_active
      (fun V:RCN264.RegularComponent Ω G M (H*A)=>RCN002.CoordinateField Ω V.1)
      (x axis) (gate axis) (fun _=>d)]
    have hh:=ECO G H A M B C hG hB hC hcop d hd thick
      (fun V:{V:RCN264.RegularComponent Ω G M (H*A)//Transcendental Ω (x axis V)}=>V.1)
      Subtype.val_injective axis D.lam D.mu (D.mu*D.lam) (fun V=>V.2)
      (fun V=>gate axis V.1) p q hp hq
    simpa only [Finset.mul_sum] using hh
  exact {z:=hsum .z,yz:=hsum .u,all:=hsum .v}
theorem EAU
    (G H A M B C:MvPolynomial (Fin 3) Ω)
    (hG:G≠0) (hB:B≠0) (hC:C≠0) (hcop:IsRelPrime B C)
    (d:ℕ) (hd:0<d) (thick:HasThickness G H A M B C d)
    (p q:FlagDegree) (hp:RCN095.PolynomialInFlag p B) (hq:RCN095.PolynomialInFlag q C)
    (c:ℕ) [CharP Ω c]
    (hZsmall:flagMixed p q unitZFlag<c) (hYsmall:flagMixed p q unitYZFlag<c)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
    ∃base: ∀V:RCN264.RegularComponent Ω G M (H*A),RCN341.SeparableLiteralCoordinate V.1,
      ∃unit:EE base p q,
        Nonempty (EY unit.toFE (fun _=>d)):=by
  have mems (V:RCN264.RegularComponent Ω G M (H*A)):=thick.mem_regular hd V
  have hY (V:RCN264.RegularComponent Ω G M (H*A)):RCN037.LiteralProjectionGate V 0:=by
    intro ht
    have ht' :Transcendental Ω (RCN093.flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.u.order 0))):=by
      simpa [Axis.order,RCN125.uOrder_p19,affineU] using ht
    have he:=RCN116.elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.uOrder_p19,affineU])
    have hh:=CNW V.1 .u 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hYsmall
    rw [he] at hh
    exact hh
  have hZ (V:RCN264.RegularComponent Ω G M (H*A)):RCN037.LiteralProjectionGate V 2:=by
    intro ht
    have ht' :Transcendental Ω (RCN093.flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))):=by
      simpa [Axis.order,RCN125.zOrder_p19] using ht
    have he:=RCN116.elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder_p19])
    have hh:=CNW V.1 .z 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hZsmall
    rw [he] at hh
    exact hh
  let base (V:RCN264.RegularComponent Ω G M (H*A)):RCN341.SeparableLiteralCoordinate V.1:=
    Classical.choice (RCN341.exists_separableLiteralCoordinate_of_YZ_gates V.1
      (PU Ω G M (H*A) V) (hY V) (hZ V))
  obtain ⟨D⟩:=ALD base hY hZ hderiv
  let unit:=BKX base hY hZ hderiv D B C hB hC hcop
    (fun V=>(mems V).1) (fun V=>(mems V).2) p q hp hq
  exact ⟨base,unit,⟨EJC base hY hZ hderiv D hG hB hC hcop d hd thick p q hp hq⟩⟩
end
end BHB
end MergedPart3
section MergedPart4
namespace BGY
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN046 RCN072 RCN084 RCN095 RCN237 RCN264 RCN338 RCN341 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BHF BDQ BD
open MovingFiberThreeSources6811 (direction weight)
theorem BNI {I J:Type} [Fintype I] [Fintype J]
    (f:I→J) (hf:Function.Injective f) (v:J→ℕ):
    (∑ i,v (f i))≤∑ j,v j:=by
  classical
  letI:DecidableEq J:=Classical.decEq J
  calc
    _=∑ j∈Finset.univ.image f,v j:=(Finset.sum_image (fun _ _ _ _ h=>hf h)).symm
    _≤_:=Finset.sum_le_sum_of_subset (Finset.subset_univ _)
theorem FXD {I:Type} [Fintype I]
    (z u v:I→ℕ) (a b c n d count zCap uCap vCap:ℕ)
    (hcount:count≤∑ i,(a*z i+b*u i+c*v i))
    (hz:n*(∑ i,z i)≤zCap) (hu:(∑ i,d*u i)≤uCap) (hv:(∑ i,d*v i)≤vCap):
    n*d*count≤d*a*zCap+n*(b*uCap+c*vCap):=by
  have he:n*d*(∑ i,(a*z i+b*u i+c*v i))=
      d*a*(n*∑ i,z i)+n*(b*(∑ i,d*u i)+c*(∑ i,d*v i)):=by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  exact (Nat.mul_le_mul_left (n*d) hcount).trans (he.le.trans
    (Nat.add_le_add (Nat.mul_le_mul_left (d*a) hz)
      (Nat.mul_le_mul_left n (Nat.add_le_add (Nat.mul_le_mul_left b hu) (Nat.mul_le_mul_left c hv)))))
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
variable {G M R:MvPolynomial (Fin 3) Ω} {p q:FlagDegree}
def DRZ
    (base: ∀V:RCN264.RegularComponent Ω G M R,RCN341.SeparableLiteralCoordinate V.1)
    (unit:EE base p q) (d:ℕ)
    (cert:EY unit.toFE (fun _=>d))
    (L:MvPolynomial (Fin 3) Ω):
    EY
      (CQW base p q unit L).toFE (fun _=>d) where
  z:=(BNI (forgetExtra L) (APC L)
    (fun V=>d*unit.toFE.zCost V)).trans cert.z
  yz:=(BNI (forgetExtra L) (APC L)
    (fun V=>d*unit.toFE.yzCost V)).trans cert.yz
  all:=(BNI (forgetExtra L) (APC L)
    (fun V=>d*unit.toFE.allCost V)).trans cert.all
theorem DLM
    (base: ∀V:RCN264.RegularComponent Ω G M R,RCN341.SeparableLiteralCoordinate V.1)
    (unit:EE base p q) (d:ℕ)
    (cert:EY unit.toFE (fun _=>d))
    (n zCap:ℕ)
    (hZ:n*(∑ V:RCN264.RegularComponent Ω G M R,unit.toFE.zCost V)≤zCap)
    (W:FlagDegree) (cut:MvPolynomial (Fin 3) Ω) (hcut:RCN095.PolynomialInFlag W cut)
    (points:Finset (Fin 3→Ω))
    (hG: ∀x∈points,MvPolynomial.eval x G=0)
    (hM: ∀x∈points,MvPolynomial.eval x M=0)
    (hR: ∀x∈points,MvPolynomial.eval x R≠0)
    (hzero: ∀x∈points,MvPolynomial.aeval x cut=0)
    (hisolated: ∀x∈points,RCN084.IsolatedPoint G M cut x):
    n*d*points.card≤d*W.zOnly*zCap+n*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag):=by
  let budget:=unit.toFE
  have hcard:points.card≤∑ V:RCN264.RegularComponent Ω G M R,budget.weightedCost W V:=by
    apply (WX Ω G M R points id hG hM hR).trans
    apply Finset.sum_le_sum
    intro V _
    by_cases he:(RCN264.componentSeeds Ω G M R points id V).Nonempty
    · obtain ⟨x,hx⟩:=he
      have hxS:=RCN264.componentSeeds_subset Ω G M R points id V hx
      have hxV:=RCN264.componentSeeds_on_prime Ω G M R points id V x hx
      apply (budget.primeBudget V).zero_le W cut hcut
        (hisolated x hxS V.1 inferInstance (PU Ω G M R V)
          hxV (EN Ω G M R V) (GV Ω G M R V))
      · intro y hy
        exact RCN264.componentSeeds_on_prime Ω G M R points id V y hy
      · intro y hy
        exact hzero y (RCN264.componentSeeds_subset Ω G M R points id V hy)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  exact FXD budget.zCost budget.yzCost budget.allCost W.zOnly W.yz W.all n d
    points.card zCap (flagMixed p q unitYZFlag) (flagMixed p q unitAllFlag) hcard hZ cert.yz cert.all
open RCN136 RCN207
theorem CLA
    {K:Type} [Field K]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F)
    (carrier:MvPolynomial (Fin 3) Ω) (pOld:FlagDegree)
    (hcarrier:carrier≠0) (hcarrierF:carrier∣surfaceMap phi F) (hp:RCN095.PolynomialInFlag pOld carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(pOld.zOnly+pOld.yz+pOld.all)<c)
    (h2:(2:Ω)≠0) (hfact:(S.k.factorial:Ω)≠0)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (R:MvPolynomial (Fin 3) Ω) (hHdiv:surfaceMap phi (RCN313.polyH K F)∣R)
    (base: ∀V:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      RCN341.SeparableLiteralCoordinate V.1)
    (unit:EE base p q) (d:ℕ)
    (cert:EY unit.toFE (fun _=>d))
    (W:FlagDegree) (cut:MvPolynomial (Fin 3) Ω) (hcut:RCN095.PolynomialInFlag W cut)
    (points:Finset (Fin 3→Ω))
    (hG: ∀v∈points,MvPolynomial.eval v carrier=0)
    (hM: ∀v∈points,MvPolynomial.eval v
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target)=0)
    (hR: ∀v∈points,MvPolynomial.eval v (R*S.leading phi)≠0)
    (hzero: ∀v∈points,MvPolynomial.aeval v cut=0)
    (hisolated: ∀v∈points,RCN084.IsolatedPoint carrier
      (RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) cut v):
    S.d*d*points.card≤d*W.zOnly*flagMixed pOld unitZFlag S.flag+
      S.d*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag):=by
  let M:=RCN207.movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target
  let base' :=fun V:RCN264.RegularComponent Ω carrier M (R*S.leading phi)=>base (forgetExtra (S.leading phi) V)
  let unit' :=CQW base p q unit (S.leading phi)
  let cert' :=DRZ base unit d cert (S.leading phi)
  have hH (V:RCN264.RegularComponent Ω carrier M (R*S.leading phi)):surfaceMap phi (RCN313.polyH K F)∉V.1:=by
    intro hh
    exact _Q6 Ω carrier M (R*S.leading phi) V
      (V.1.mem_of_dvd (dvd_mul_of_dvd_left hHdiv _) hh)
  have hZ:=DRC phi F S carrier pOld hcarrier hcarrierF hp
    c hunit h2 hfact Q A target hQ hA (R*S.leading phi)
    hH (GVE (S.leading phi)) base' p q unit'
  exact DLM base' unit' d cert' S.d (flagMixed pOld unitZFlag S.flag)
    hZ W cut hcut points hG hM hR hzero hisolated
end
end BGY
end MergedPart4
section MergedPart5
namespace AIW
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
open MvPolynomial RCN084 RCN207
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 3) K
theorem BIG (F G:Poly) (hdiv:G∣F)
    (x:Fin 3→K) (hG:MvPolynomial.eval x G=0)
    (hreg:MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) F)≠0):
    ∃Q:Poly,F=G*Q∧MvPolynomial.eval x Q≠0:=by
  obtain ⟨Q,hQ⟩:=hdiv
  refine ⟨Q,hQ,?_⟩
  rw [hQ,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hG,zero_mul,add_zero] at hreg
  exact (mul_ne_zero_iff.mp hreg).2
theorem DAZ (F G N A:Poly) (hdiv:G∣F)
    (x:Fin 3→K) (hG:MvPolynomial.eval x G=0)
    (hreg:MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) F)≠0)
    (hisolated:RCN084.IsolatedPoint G N A x):RCN084.IsolatedPoint F N A x:=by
  obtain ⟨Q,hQ,hQne⟩:=BIG F G hdiv x hG hreg
  intro P hprime hnotpoint hpoint hFmem hNmem
  have hQnot:Q∉P:=by
    intro hmem
    apply hQne
    exact hpoint hmem
  have hGmem:G∈P:=by
    rw [hQ] at hFmem
    exact (hprime.mem_or_mem hFmem).resolve_right hQnot
  exact hisolated P hprime hnotpoint hpoint hGmem hNmem
end
end AIW
end MergedPart5
section MergedPart7
namespace _Q7
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 700000
open RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN264 RCN313 RCN338 RCN341
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD CB
open MovingFiberThreeSources6811 (direction weight)
open ANV BHB BGY
open LF WC
variable {K E:Type} [Field K] [CharP K 2130706433] [Field E] [CharP E 2130706433]
variable (f:GenericField K→+*E)
local notation "Omega" =>E
local notation "OmegaT" =>GenericField E
local notation "Poly3" =>MvPolynomial (Fin 3) E
local notation "Poly3T" =>MvPolynomial (Fin 3) OmegaT
local notation "phi" =>RingHom.comp (RCN135.coefficientEmbedding E) (codeMap f)
local notation "lift" =>MvPolynomial.map (RCN135.coefficientEmbedding E)
abbrev FEK (F:MvPolynomial (Fin 4) K) (Q A:Poly3):=
  RCN264.RegularComponent OmegaT (OO f F) (XC f F Q A) (AOT f F A)
theorem EBY
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (S T:MovingFiberThreeSources6811.Source F) (hcop:IsRelPrime S.P T.P)
    (d:ℕ) (hd:0<d) (hS:d≤S.d) (hT:d≤T.d) (hchar:d≤2130706433)
    (Q A:Poly3) (hden:(2:Poly3)*A≠0)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hz:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433):
    ∃base: ∀V:FEK f F Q A,RCN341.SeparableLiteralCoordinate V.1,
      ∃unit:EE base (ordinaryFlag S.P) (ordinaryFlag T.P),
        Nonempty (EY unit.toFE (fun _=>d)):=by
  obtain ⟨B,C,hB,hC,hBC,hBflag,hCflag,hthick⟩:=EFY f F S T hcop d hS hT hchar Q A hden hQ hA
  have ht:HasThickness (OO f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
      (XC f F Q A) B C d:=hthick
  have hG:OO f F≠0:=by
    intro hh
    exact hF (BMZ f (by simpa only [OO,map_zero] using hh))
  exact EAU (OO f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
    (XC f F Q A) B C hG hB hC hBC d hd ht
    (ordinaryFlag S.P) (ordinaryFlag T.P) hBflag hCflag 2130706433 hz hu
    (CWZ f F hpos hsmall)
theorem DIA
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (S T:MovingFiberThreeSources6811.Source F) (hcop:IsRelPrime S.P T.P)
    (d:ℕ) (hd:0<d) (hS:d≤S.d) (hT:d≤T.d) (hchar:d≤2130706433)
    (SZ:MovingFiberThreeSources6811.Source F) (hZchar:SZ.k<2130706433)
    (p:FlagDegree) (hp:RCN095.PolynomialInFlag p (OO f F))
    (hunit:2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A:Poly3) (hden:(2:Poly3)*A≠0)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hz:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433)
    (W:FlagDegree) (cut:Poly3T) (hcut:RCN095.PolynomialInFlag W cut)
    (points:Finset (Fin 3→OmegaT))
    (hG: ∀v∈points,MvPolynomial.eval v (OO f F)=0)
    (hM: ∀v∈points,MvPolynomial.eval v (XC f F Q A)=0)
    (hregular: ∀v∈points,MvPolynomial.eval v (AOT f F A*SZ.leading phi)≠0)
    (hzero: ∀v∈points,MvPolynomial.aeval v cut=0)
    (hisolated: ∀v∈points,RCN084.IsolatedPoint (OO f F) (XC f F Q A) cut v):
    SZ.d*d*points.card≤d*W.zOnly*flagMixed p unitZFlag SZ.flag+
      SZ.d*(W.yz*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag+
        W.all*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag):=by
  obtain ⟨base,unit,⟨cert⟩⟩:=EBY f F hF hpos hsmall S T hcop d hd hS hT hchar
    Q A hden hQ hA hz hu
  have hGne:OO f F≠0:=by
    intro hh
    exact hF (BMZ f (by simpa only [OO,map_zero] using hh))
  have hHdiv:surfaceMap phi (polyH K F)∣AOT f F A:=by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2:(2:OmegaT)≠0:=(CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact:(SZ.k.factorial:OmegaT)≠0:=SecondJetOwnShape.factorial_ne SZ.k hZchar
  exact CLA phi F SZ (OO f F) p hGne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift Q) (lift A) (RCN135.initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA) (AOT f F A) hHdiv base unit d cert
    W cut hcut points hG hM hregular hzero hisolated
def AGN (F:MvPolynomial (Fin 4) K) (SZ:MovingFiberThreeSources6811.Source F)
    (Q A:Poly3) (scale z u v:ℕ):Prop:=
  ∀(W:FlagDegree) (cut:Poly3T),RCN095.PolynomialInFlag W cut→
    ∀points:Finset (Fin 3→OmegaT),
      (∀x∈points,MvPolynomial.eval x (OO f F)=0)→
      (∀x∈points,MvPolynomial.eval x (XC f F Q A)=0)→
      (∀x∈points,MvPolynomial.eval x (AOT f F A*SZ.leading phi)≠0)→
      (∀x∈points,MvPolynomial.aeval x cut=0)→
      (∀x∈points,RCN084.IsolatedPoint (OO f F) (XC f F Q A) cut x)→
      scale*points.card≤W.zOnly*z+W.yz*u+W.all*v
theorem BSF
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<2130706433)
    (S T:MovingFiberThreeSources6811.Source F) (hcop:IsRelPrime S.P T.P)
    (d:ℕ) (hd:0<d) (hS:d≤S.d) (hT:d≤T.d) (hchar:d≤2130706433)
    (SZ:MovingFiberThreeSources6811.Source F) (hZchar:SZ.k<2130706433)
    (p:FlagDegree) (hp:RCN095.PolynomialInFlag p (OO f F))
    (hunit:2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A:Poly3) (hden:(2:Poly3)*A≠0)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hz:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433):
    AGN f F SZ Q A (SZ.d*d) (d*flagMixed p unitZFlag SZ.flag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag):=by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hh:=DIA f F hF hpos hsmall S T hcop d hd hS hT hchar
    SZ hZchar p hp hunit Q A hden hQ hA hz hu W cut hcut points hG hM hregular hzero hisolated
  convert hh using 1<;>ring
end
end _Q7
end MergedPart7
section MergedPart8
namespace OT
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
variable {K E:Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta:GenericField K→+*E)
local notation "Omega" =>E
local notation "OmegaT" =>GenericField E
local notation "phi" =>RingHom.comp (RCN135.coefficientEmbedding E) (codeMap eta)
local notation "lift" =>MvPolynomial.map (RCN135.coefficientEmbedding E)
local instance:Algebra (RatFunc E) OmegaT:=CPM E
local instance:IsScalarTower E (RatFunc E) OmegaT:=target_tower E
def BXI (F:MvPolynomial (Fin 4) K):=surfaceMap (codeMap eta) F
def frozenH (F:MvPolynomial (Fin 4) K):=surfaceMap (codeMap eta) (polyH K F)
def frozenG (F:MvPolynomial (Fin 4) K):=surfaceMap (codeMap eta) (polyG K F)
abbrev CWU (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) E)
    (n:ℕ) (coeff:Fin (n+1)→MvPolynomial (Fin 3) E):=
  RCN264.RegularComponent E G (filteredCut n coeff (frozenH eta F) (frozenG eta F)) (frozenH eta F)
def ZN (n:ℕ) (coeff:Fin (n+1)→MvPolynomial (Fin 3) E)
    (Q A:MvPolynomial (Fin 3) E):MvPolynomial (Fin 3) OmegaT:=
  RCN207.eliminatedCut n (fun j=>lift (coeff j)) (lift Q) (lift A) (RCN135.initialCoordinate E)
theorem EQP (P:MvPolynomial (Fin 3) E):RCN208.scalarPolynomialMap E OmegaT P=lift P:=by
  rw [RCN208.scalarPolynomialMap,←ANT E]
theorem lift_frozen (P:MvPolynomial (Fin 4) K):
    lift (surfaceMap (codeMap eta) P)=surfaceMap phi P:=by
  simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]
theorem FJX (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (f:RCN002.CoordinateField E C→ₐ[E] OmegaT) (P:MvPolynomial (Fin 3) E):
    MvPolynomial.eval (RCN134.embeddingPoint C f) (lift P)=f (RCN002.coordinateEvaluation E C P):=by
  rw [MvPolynomial.eval_map,ANT E]
  exact AlgHom.congr_fun (RCN134.embeddingPoint_aeval C f) P
end
end OT
end MergedPart8
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace AHX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators WithZero
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place_p19)
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN095 renaming PolynomialInFlag → BI
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open HFreeDir6813
open ActualFirstCutPole6807 renaming pole_le_of_value_le → BIH
local notation "w" =>RCN326.w
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
theorem DJW
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:RCN341.SeparableLiteralCoordinate C)
    (hH:surfaceMap phi (polyH K F)∉C)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hbudget:APH phi F C C0 (HFree6812.infCap d))
    (scale CX CV:ℕ)
    (hXbudget: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
      (∑ nu∈W,flagPole nu.val (coordinate E C) (hfreeFlagDir d r v z C0))≤(CX:ℤ))
    (hMoving: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
      (scale:ℤ)*(∑ nu∈W,RCN064.KS C (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) nu)≤(CV:ℤ))
    (W:Finset (Place_p19 E (RCN002.CoordinateField E C))):
    ((3*scale:ℕ):ℤ)*(∑ nu∈W,RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
      (scale:ℤ)*(CX:ℤ)+((4*(w+1):ℕ):ℤ)*(CV:ℤ):=by
  letI:=RCN006.polynomialBaseAlgebra E C base.index
  letI:=RCN005.rationalBaseAlgebra E C base.index base.transcendental
  letI:=RCN006.polynomialBaseScalarTower E C base.index
  letI:=RCN006.polynomialRationalScalarTower E C base.index base.transcendental
  letI:=RCN005.rationalBaseScalarTower E C base.index base.transcendental
  letI:FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C):=base.finite
  letI:Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C):=base.separable
  let L:=RCN002.CoordinateField E C
  let ev:=SecondJetComponentRoots.coefficientMap phi C
  let H:=ev (polyH K F)
  let sigma:=ev (polyG K F)/H
  let theta:=fun nu:Place_p19 E L=>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag+RCN187.poleOrder nu.val sigma)
  let Hf:FlagDegree:=⟨z,v,r-1⟩
  have hHne:H ≠ 0:=by
    intro hz
    apply hH
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mp hz
  let Pl:=RCN026.placesFor_p19 E L H hHne
  set W' :=W ∪ Pl with hW'
  have hsource:(scale:ℤ)*(∑ nu ∈ W',theta nu)≤(CV:ℤ):=by
    have hh:=hMoving W'
    simpa only [theta,sigma,H,ev,RCN064.KS,RCN204.flagPole_unitAll,
      RCN204.flagPole_unitYZ,SecondJetComponentRoots.coefficientMap,RCN064.movingRatio,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hh
  have htarget:(∑ nu ∈ W',RCN064.KS C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu)= ∑ nu ∈ W',theta nu:=by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta,RCN204.flagPole_unitAll,RCN204.flagPole_unitYZ]
    rfl

  have hHF:=(BoundaryTailAlgebra.boundary_surfaceMap_flags phi F r v z (by omega) (by omega)
    hR hYR hAll).1
  have hpoleH (nu:Place_p19 E L):
      RCN346.poleOrder_p19 E L nu H≤flagPole nu.val (coordinate E C) Hf:=by
    apply ActualFirstCutPole6807.pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h:=RCN204.valuation_eval_le_flag nu.val (algebraMap E L)
      (RCN344.NP E L nu) (coordinate E C) Hf _ hHF
    simpa only [H,ev,SecondJetComponentRoots.coefficientMap,
      RCN002.coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h
  have hzero:(∑ nu ∈ W',RCN026.zeroOrder_p19 E L nu H)≤
      ∑ nu ∈ W',flagPole nu.val (coordinate E C) Hf:=by
    have hout: ∀nu ∈ W'.filter (fun nu=>nu ∉ Pl),RCN026.zeroOrder_p19 E L nu H=0:=by
      intro nu hnu
      have hno:RCN026.order_p19 E L nu H=0:=by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.ALB E L H hHne nu hne)
      simp only [RCN026.zeroOrder_p19,hno,max_self]
    calc
      _=(∑ nu ∈ W'.filter (fun nu=>nu ∈ Pl),RCN026.zeroOrder_p19 E L nu H)+
          ∑ nu ∈ W'.filter (fun nu=>nu ∉ Pl),RCN026.zeroOrder_p19 E L nu H:=
        (Finset.sum_filter_add_sum_filter_not W' _ _).symm
      _= ∑ nu ∈ W'.filter (fun nu=>nu ∈ Pl),RCN026.zeroOrder_p19 E L nu H:=by
        rw [Finset.sum_eq_zero hout,add_zero]
      _≤ ∑ nu ∈ Pl,RCN026.zeroOrder_p19 E L nu H:=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu=>(Finset.mem_filter.mp hnu).2)
          (fun nu _ _=>RCN026.AUU E L nu H)
      _= ∑ nu ∈ Pl,RCN346.poleOrder_p19 E L nu H:=RCN026.AJO E L H hHne
      _≤ ∑ nu ∈ Pl,flagPole nu.val (coordinate E C) Hf:=Finset.sum_le_sum (fun nu _=>hpoleH nu)
      _≤_:=Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun nu _ _=>RCN204.flagPole_nonneg nu.val (coordinate E C) Hf)

  have hcusp:2*(∑ nu ∈ W',flagPole nu.val (coordinate E C) Hf)≤
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlag d r v z))+
        ∑ nu ∈ W',flagPole nu.val (coordinate E C) (HFree6812.infCap d):=by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun nu _=> ?_
    have e1:=congrArg (flagPole nu.val (coordinate E C)) (cusp_add_cap d r v z hr hv)
    rw [RCN204.flagPole_add,RCN204.flagPole_nsmul] at e1
    have e2:=HFreeDir6813.capFlag_pole_le nu.val (coordinate E C) d r hr
    push_cast at e1
    linarith
  have hX:=hXbudget W'
  simp only [hfreeFlagDir,RCN204.flagPole_add,RCN204.flagPole_nsmul,Finset.sum_add_distrib,
    ← Finset.mul_sum] at hX
  have hb:=hbudget.pole_le W'
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hb
  rw [htarget] at hb
  have hWW:(∑ nu ∈ W,RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
      ∑ nu ∈ W',RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)):=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun nu _ _=>le_max_left _ _)
  push_cast at hb hsource hX ⊢
  have hk:(0:ℤ)≤(scale:ℤ):=by positivity
  have hw:(0:ℤ)≤(w:ℤ)+1:=by positivity
  have e0:=mul_le_mul_of_nonneg_left (show
    2*(∑ nu ∈ W',RCN026.zeroOrder_p19 E L nu H)≤
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlag d r v z))+
        ∑ nu ∈ W',flagPole nu.val (coordinate E C) (HFree6812.infCap d) by linarith) hw
  have hb' :3*(∑ nu ∈ W',RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F (w-1))/
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)))≤
      4*((w:ℤ)+1)*(∑ nu ∈ W',theta nu)+(CX:ℤ):=by
    nlinarith
  have e1:=mul_le_mul_of_nonneg_left hb' hk
  have e2:=mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num:(0:ℤ)≤4) hw)
  have e3:=mul_le_mul_of_nonneg_left hWW (mul_nonneg (by norm_num:(0:ℤ)≤3) hk)
  nlinarith
end
end AHX
end MergedPart0
section MergedPart1
namespace ARR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open scoped Classical
open MvPolynomial RCN084 RCN137 RCN264 YE
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
variable {E:Type} [Field E] [IsAlgClosed E]
local notation "Poly" =>MvPolynomial (Fin 3) E
theorem BSI (F G H:Poly) (P:Ideal Poly)
    (hprod:G*H∣F) (hG:G∈P) (hH:H∈P):pderiv (1:Fin 3) F∈P:=by
  obtain ⟨Q,rfl⟩:=hprod
  rw [pderiv_mul,pderiv_mul]
  exact P.add_mem
    (P.mul_mem_right Q (P.add_mem (P.mul_mem_left _ hH) (P.mul_mem_right _ hG)))
    (P.mul_mem_right _ (P.mul_mem_right H hG))
theorem FBW (F N R:Poly) (hFne:F≠0)
    (hR:R∈Ideal.span ({F,pderiv (1:Fin 3) F}:Set Poly)):
    Function.Injective (fun a:ANR F N R=>a.2.1):=by
  classical
  rintro ⟨ga,Ca⟩ ⟨gb,Cb⟩ he
  change Ca.1=Cb.1 at he
  have hga:=RCN084.activeFactors_spec F N ga
  have hgb:=RCN084.activeFactors_spec F N gb
  have hgeq:ga=gb:=by
    apply Subtype.ext
    by_contra hne
    have hsubset:({ga.1,gb.1}:Finset Poly)⊆RCN137.normalizedFactorSet F:=by
      intro P0 hP0
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP0
      rcases hP0 with rfl | rfl
      · exact (Finset.mem_filter.mp ga.2).1
      · exact (Finset.mem_filter.mp gb.2).1
    have hprod:ga.1*gb.1∣F:=by
      have hh:=(Finset.prod_dvd_prod_of_subset {ga.1,gb.1} (RCN137.normalizedFactorSet F) id hsubset).trans
        (RCN137.normalizedFactorSet_product_dvd F hFne)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have ha:ga.1∈Ca.1:=EN E ga.1 N R Ca
    have hb:gb.1∈Ca.1:=by rw [he];exact EN E gb.1 N R Cb
    have hF:F∈Ca.1:=Ca.1.mem_of_dvd hga.2.1 ha
    have hd:=BSI F ga.1 gb.1 Ca.1 hprod ha hb
    have hspan:Ideal.span ({F,pderiv (1:Fin 3) F}:Set Poly)≤Ca.1:=by
      apply Ideal.span_le.mpr
      intro P0 hP0
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP0
      rcases hP0 with rfl | rfl
      · exact hF
      · exact hd
    exact _Q6 E ga.1 N R Ca (hspan hR)
  cases hgeq
  exact congrArg (fun C:RCN264.RegularComponent E ga.1 N R=>(⟨ga,C⟩:ANR F N R)) (Subtype.ext he)
end
end ARR
end MergedPart1
section MergedPart2
namespace AGD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators WithZero
open RCN002 RCN022 RCN064 RCN095 RCN187 RCN207 RCN208 RCN212 RCN264 RCN295 RCN341 RCN344
open RCN095 renaming PolynomialInFlag → BI
open RCN184 RCN133 RCN114 RCN005 RCN006 RCN044 RCN037 RCN042 RCN035
variable {E I:Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" =>MvPolynomial (Fin 3) E
theorem field_eval (P:Ideal Poly) [P.IsPrime] (A:Poly):
    MvPolynomial.eval₂Hom (algebraMap E (RCN002.CoordinateField E P)) (coordinate E P) A=RCN002.coordinateEvaluation E P A:=by
  rw [RCN002.coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
theorem BJG
    (P:I→Ideal Poly) [∀i,(P i).IsPrime]
    (base: ∀i,RCN341.SeparableLiteralCoordinate (P i)) (H G:Poly):
    ∃(Q A:Poly) (projection: ∀i,RCN344.SeparableCoordinate E (RCN002.CoordinateField E (P i))),
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q∧RCN095.PolynomialInFlag unitYZFlag A∧
      ∀i,A∉P i∧
        RCN344.SeparableCoordinate.value E (RCN002.CoordinateField E (P i)) (projection i)=movingValue (P i) H G Q A∧
        ∀nu:RCN026.Place_p19 E (RCN002.CoordinateField E (P i)),
          poleOrder nu.val (RCN344.SeparableCoordinate.value E (RCN002.CoordinateField E (P i)) (projection i))=
            KS (P i) H G nu:=by
  obtain ⟨c,hc⟩:=CQD (K:=E)
    (fun i=>RCN002.CoordinateField E (P i)) (fun i=>coordinate E (P i))
    (fun i=>movingRatio (P i) H G) (fun i=>(base i).index)
    (fun i=>RCN037.base_differential_ne_zero (base i))
    (fun i=>ALT (base i) (movingRatio (P i) H G))
  let Q:=BIK c
  let A:=CKK c
  have hJ (i:I):
      RCN184.coefficientEvaluation (RCN212.movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) MS c=
        movingValue (P i) H G Q A:=by
    rw [DAQ,field_eval,field_eval]
    simp only [movingValue,movingRatio,Q,A,mul_div_assoc]
  have hA (i:I):RCN184.coefficientEvaluation (coordinate E (P i)) RCN212.linearSupport (restrictU_p19 c)=
      RCN002.coordinateEvaluation E (P i) A:=field_eval (P i) A
  have hx (i:I):=hc i
  simp only [hA,hJ] at hx
  have hnot (i:I):A∉P i:=by
    intro hh
    exact (hx i).1 ((SecondJetComponentRoots.evaluation_zero_iff (P i) A).mpr hh)
  have gate (i:I):=RCN064.moving_projection_gate (base i) H G Q A (hx i).2.1
  let projection (i:I):RCN344.SeparableCoordinate E (RCN002.CoordinateField E (P i)):={
    embedding:=RCN022.elementEmbedding E (RCN002.CoordinateField E (P i)) (movingValue (P i) H G Q A) (gate i).choose
    finite:=(gate i).choose_spec.1
    separable:=(gate i).choose_spec.2.1}
  have hv (i:I):RCN344.SeparableCoordinate.value E (RCN002.CoordinateField E (P i)) (projection i)=
      movingValue (P i) H G Q A:=RCN022.elementEmbedding_variable E (RCN002.CoordinateField E (P i)) _ (gate i).choose
  refine ⟨Q,A,projection,CQA c,DHT c,fun i=>⟨hnot i,hv i,?_⟩⟩
  intro nu
  rw [hv]
  by_cases hn:nu∈ALT (base i) (movingRatio (P i) H G)
  · exact RCN184.poleOrder_eq_of_valuation_eq_exp nu.val _ _
      (by dsimp [KS,poleOrder];positivity) ((hx i).2.2 nu hn).1
  · obtain ⟨hcoord,hw⟩:=CAX (base i) (movingRatio (P i) H G) nu hn
    have hz:RCN295.exponentSetPoleWeight nu.val (RCN212.movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) MS=0:=by
      rw [AZV]
      simp [hcoord,hw]
    have hp:=(RCN295.poleOrder_eval_le_support nu.val (algebraMap E (RCN002.CoordinateField E (P i)))
      (NP E (RCN002.CoordinateField E (P i)) nu)
      (RCN212.movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G))
      (RCN133.polynomialOfSupport MS c)).trans
      (RCN295.supportPoleWeight_le_exponentSetPoleWeight _ _ _ MS (RCN133.support_polynomialOfSupport_subset _ _))
    change poleOrder nu.val (RCN184.coefficientEvaluation _ _ c)≤_ at hp
    rw [hJ i,hz] at hp
    have hp0:=le_antisymm hp (le_max_left _ _)
    simpa [KS,hcoord,hw] using hp0
end
end AGD
end MergedPart2
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
theorem CRH
    {I:Type} [Fintype I]
    (F:MvPolynomial (Fin 4) K) (S:MovingFiberThreeSources6811.Source F)
    (G:I→MvPolynomial (Fin 3) Omega) (hGF: ∀i,G i∣BXI eta F)
    (Q A:MvPolynomial (Fin 3) Omega) (scale z u v:ℕ)
    (hbound:AGN eta F S Q A scale z u v)
    (n:ℕ) (coeff:Fin (n+1)→MvPolynomial (Fin 3) Omega)
    (W:FlagDegree) (hcut:RCN095.PolynomialInFlag W (ZN n coeff Q A))
    (old: ∀i,CWU eta F (G i) n coeff)
    (hold:Function.Injective (fun i=>(old i).1))
    (hleading: ∀i,S.leading (codeMap eta)∉(old i).1)
    (hA: ∀i,A∉(old i).1)
    (projection: ∀i,RCN344.SeparableCoordinate Omega (RCN002.CoordinateField Omega (old i).1))
    (hvalue: ∀i,RCN344.SeparableCoordinate.value Omega (RCN002.CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A):
    scale*(∑ i,RCN344.SeparableCoordinate.degree Omega (RCN002.CoordinateField Omega (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v:=by
  classical
  let prime:=fun i=>(old i).1
  letI: ∀i,Algebra (RatFunc Omega) (RCN002.CoordinateField Omega (prime i)):=
    fun i=>(projection i).embedding.toRingHom.toAlgebra
  letI: ∀i,IsScalarTower Omega (RatFunc Omega) (RCN002.CoordinateField Omega (prime i)):=
    fun i=>IsScalarTower.of_algebraMap_eq fun a=>((projection i).embedding.commutes a).symm
  letI: ∀i,FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega (prime i)):=
    fun i=>(projection i).finite
  letI: ∀i,Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega (prime i)):=
    fun i=>(projection i).separable
  let points:=RCN134.genericFiberPoints (B:=RatFunc Omega) (L:=OmegaT) prime
  have hinj:Function.Injective prime:=hold
  have hwhole (i:I):lift (G i)∣OO eta F:=by
    have hh:=map_dvd (MvPolynomial.map (RCN135.coefficientEmbedding Omega)) (hGF i)
    simpa only [BXI,lift_frozen,OO] using hh
  have certificate (i:I) (f:RCN002.CoordinateField Omega (prime i)→ₐ[RatFunc Omega] OmegaT):
      let x:=RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (OO eta F)=0∧
      MvPolynomial.eval x (XC eta F Q A)=0∧
      MvPolynomial.aeval x (ZN n coeff Q A)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0∧
      RCN084.IsolatedPoint (OO eta F) (XC eta F Q A) (ZN n coeff Q A) x:=by
    have hj:algebraMap (RatFunc Omega) (RCN002.CoordinateField Omega (prime i)) (RCN202.rationalVariable Omega)=
        movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A:=hvalue i
    have hc:=VX (G i) (frozenH eta F) (frozenG eta F) Q A n coeff
      (old i) hj (hA i) f
    have hc' :
        MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)) (lift (G i))=0∧
        MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)) (XC eta F Q A)=0∧
        MvPolynomial.aeval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)) (ZN n coeff Q A)=0∧
        MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)) (surfaceMap phi (polyH K F)*lift A)≠0∧
        RCN084.IsolatedPoint (lift (G i)) (XC eta F Q A) (ZN n coeff Q A)
          (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)):=by
      simpa only [EQP,frozenH,frozenG,lift_frozen,FES,XC,ZN] using hc
    have hzero:=map_dvd (MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega))) (hwhole i)
    rw [hc'.1,zero_dvd_iff] at hzero
    have hreg:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega))
        (MvPolynomial.pderiv (1:Fin 3) (OO eta F))≠0:=by
      have hr:=hc'.2.2.2.1
      rw [map_mul,mul_ne_zero_iff] at hr
      simpa only [OO,RCN267.surfaceMap_pderiv_R,polyH] using hr.1
    exact ⟨hzero,hc'.2.1,hc'.2.2.1,hc'.2.2.2.1,
      AIW.DAZ
        (OO eta F) (lift (G i)) (XC eta F Q A) (ZN n coeff Q A)
        (hwhole i) _ hc'.1 hreg hc'.2.2.2.2⟩
  have hc: ∀x ∈ points,
      MvPolynomial.eval x (OO eta F)=0∧MvPolynomial.eval x (XC eta F Q A)=0∧
      MvPolynomial.eval x (AOT eta F A*S.leading phi)≠0∧
      MvPolynomial.aeval x (ZN n coeff Q A)=0∧
      RCN084.IsolatedPoint (OO eta F) (XC eta F Q A) (ZN n coeff Q A) x:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    have hh:=certificate i f
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.2⟩
    have hHA:=hh.2.2.2.1
    rw [map_mul,mul_ne_zero_iff] at hHA
    have hL:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Omega)) (S.leading phi)≠0:=by
      have he:S.leading phi=lift (S.leading (codeMap eta)):=(lift_frozen eta _).symm
      rw [he,FJX]
      intro hz
      exact hleading i ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have h2:(2:OmegaT)≠0:=(CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
    simpa only [RCN134.commonBaseEmbeddingPoint,AOT,map_mul,map_ofNat] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hHA.1) (mul_ne_zero h2 hHA.2)) hL
  have hb:=hbound W (ZN n coeff Q A) hcut points
    (fun x hx=>(hc x hx).1) (fun x hx=>(hc x hx).2.1)
    (fun x hx=>(hc x hx).2.2.1) (fun x hx=>(hc x hx).2.2.2.1)
    (fun x hx=>(hc x hx).2.2.2.2)
  have hcard:=RCN134.genericFiberPoints_card (B:=RatFunc Omega) (L:=OmegaT) prime hinj
  simpa only [points,hcard,RCN344.SeparableCoordinate.degree,prime] using hb
end
end AKN
end MergedPart3
end SubmissionLower
end ProximityPrize
end
