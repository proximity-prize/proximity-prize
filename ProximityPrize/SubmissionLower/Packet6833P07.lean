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
import ProximityPrize.SubmissionLower.Packet6833P06
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace LV
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF
open MovingFiberThreeSources6811 (direction weight)
open HI FF ZGL DR
variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}
theorem GHJ [Fintype I] (nodes:I ↪ K) (hI:Fintype.card I=262144)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (SZ:MovingFiberThreeSources6811.Source P.F) (z:Degrees) (hZ:Fits SZ z)
    (hZFT:z.T<wt RCN156.residualTotalWeights P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (i:Fin 2) (hFT:(CN.profile i).L<wt RCN156.residualTotalWeights P.F)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (a:Box) (m cap:ℕ)
    (h:Contains a (point J)) (hm:0<m)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
    (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
    (hJF:a.thi<wt RCN156.residualTotalWeights P.F) (hcap:3000000000000000≤cap)
    (hgood:GoodPower i a m)
    (hchecks: ∀e,e<(powerBox (CN.profile i) a m).q→
      active (CN.profile i) a m e→
      flagMixed (ownerFlag a) (cofactorFlag (CN.profile i) a e) unitZFlag<2130706433∧
      flagMixed (ownerFlag a) (cofactorFlag (CN.profile i) a e) unitYZFlag<2130706433∧
      pairCost z (min m ((CN.profile i).k+1-e*m))
        (ownerFlag a) (cofactorFlag (CN.profile i) a e) t y r+leading z t y r≤cap):
    P.seeds.card≤max (MG t y r) cap:=by
  let p:=CN.profile i
  have hp:Shape p:=CN.shape i
  have small:p.B≤256∧p.U≤512∧p.L≤4096∧p.s≤64∧p.L+p.s≤8192:=CN.small i
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  have hcovers:DA.Covers (powerBox p a m) J:=
    ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.2.2.2.1,h.2.2.2.2.2.2.1⟩
  rcases BHD p hp (CN.kernel i)
    (CN.dimension i) nodes P.u0 P.u1 hI P.F hFT P.rdegree hchar
    r y t (by have:=P.rlow;omega) (by have:=P.ylow;have:=P.rlow;omega)
    (by have:=P.yt;have:=P.ylow;have:=P.rlow;omega)
    ⟨P.r_weight,P.y_weight,P.total_weight⟩ J hJ a.thi h.2.2.2.2.2.2.2 hJF m hm hroot hJne
    (powerBox p a m) rfl hcovers hgood
      with ⟨Q,hQ⟩ | ⟨e,he,SJ,SQ,hSJ,hcop,hdelta,hSP,hRet,hT,hU,hB,hS⟩
  · exact ((KY.helper_count p nodes P small.1 small.2.1
      small.2.2.1 small.2.2.2.1 Q hQ).le.trans hcap).trans (le_max_right _ _)
  have hb:=Nat.mul_le_mul_left e h.2.2.1
  have hu:=Nat.mul_le_mul_left e h.2.2.2.2.1
  have ht:=Nat.mul_le_mul_left e h.2.2.2.2.2.2.1
  have hs:=Nat.mul_le_mul_left e h.1
  have horder:SQ.d≤order SQ.P:=by
    have hh:=SQ.hdn.trans SQ.hn
    simpa only [MovingFiberThreeSources6811.Source.d,ABW,order] using hh
  have ha:active p a m e:=by unfold active;dsimp only [point] at hb hu ht hs;omega
  obtain ⟨hcgZ,hcgU,hfit⟩:=hchecks e he ha
  have hq:CumulativeLe (ordinaryFlag SQ.P) (cofactorFlag p a e):=
    FBA SQ.P _ _ _ _ (by dsimp only [point] at hb;omega)
      (by dsimp only [point] at hu;omega) (by dsimp only [point] at ht;omega)
      (by dsimp only [point] at hs;omega)
  have hj:=_Q23 J a h
  rw [←hSJ] at hj
  have hdchar:min m (p.k+1-e*m)≤2130706433:=by
    have h1:=hp.retention
    have h2:=hp.degree
    have h3:=hp.characteristic
    have h4:=min_le_right m (p.k+1-e*m)
    omega
  exact (AHM P SZ SJ SQ z hZ hZFT hk hg hcop _ hdelta hdchar hSP
    ((min_le_right _ _).trans hRet) _ _ hj hq hcgZ hcgU P.rlow).trans (max_le_max le_rfl hfit)
end
end LV
end MergedPart1
section MergedPart2
namespace SN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC BD
open SecondJetCoefficients (liftExponent)
open MovingFiberThreeSources6811 (direction weight)
open DU ER EF
open FF HI
open CQG
inductive Choice where
  | native
  | derivative (ownerZ:Bool)
  | auxiliary (ownerZ:Bool) (source:Fin 2)
  deriving DecidableEq
def Common (z:Degrees) (low t y r:ℕ):Prop:=
  z.T<low∧z.k<2130706433∧Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)
instance (z:Degrees) (low t y r:ℕ):Decidable (Common z low t y r):=by
  unfold Common Gates
  infer_instance
end
end SN
end MergedPart2
section MergedPart3
namespace BH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open DR LV HI FF
open SN (Choice Common)
open RCN095 RCN135 RCN136 RCN156 RCN234 CB
open RCN095 renaming PolynomialInFlag → BI
open DC BD
open MovingFiberThreeSources6811 (direction weight)
open DU EF
open CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetCoefficients (liftExponent)
def chosenZ (useOwner:Bool) (fixed:Degrees) (a:Box) (m:ℕ):=
  if useOwner then ownerZ a m else fixed
instance (p:Parameters) (a:Box) (m e:ℕ):Decidable (active p a m e):=by
  unfold active;infer_instance
instance (i:Fin 2) (a:Box) (m:ℕ):Decidable (GoodPower i a m):=by
  unfold GoodPower DA.Impossible;infer_instance
def PairChecks (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r cap:ℕ):Prop:=
  flagMixed p q unitZFlag<2130706433∧flagMixed p q unitYZFlag<2130706433∧
    pairCost z delta p q t y r+leading z t y r≤cap
instance (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r cap:ℕ):
    Decidable (PairChecks z delta p q t y r cap):=by unfold PairChecks;infer_instance
def checkExit (p:Parameters) (a:Box) (z:Degrees) (m t y r cap e:ℕ):Bool:=
  if active p a m e then decide (PairChecks z (min m (p.k+1-e*m))
    (ownerFlag a) (cofactorFlag p a e) t y r cap) else true
def checkExits (p:Parameters) (a:Box) (z:Degrees) (m t y r cap:ℕ):Bool:=
  (List.range (powerBox p a m).q).all (checkExit p a z m t y r cap)
def checkChoice (c:Choice) (fixed:Degrees) (a:Box) (m low t y r cap:ℕ):Bool:=
  match c with
  | .native=>decide (Common (ownerZ a m) low t y r∧
      nativeScalar (ownerZ a m) t y r/(9*(ownerZ a m).d*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap)
  | .derivative useOwner=>
      let z:=chosenZ useOwner fixed a m
      decide (2≤m∧Common z low t y r∧PairChecks z (m-1) (ownerFlag a) (AFD a) t y r cap)
  | .auxiliary useOwner i=>
      let z:=chosenZ useOwner fixed a m
      decide (Common z low t y r∧(CN.profile i).L<low) &&
        decide (GoodPower i a m) && checkExits (CN.profile i) a z m t y r cap
def check (c:Choice) (fixed:Degrees) (a:Box) (m low t y r cap:ℕ):Bool:=
  decide (0<m∧m≤a.slo∧2*a.slo≤a.bhi∧a.thi≤1700∧a.thi<low∧a.shi<2130706433) &&
    checkChoice c fixed a m low t y r cap
theorem exits_spec (p:Parameters) (a:Box) (z:Degrees) (m t y r cap:ℕ)
    (hc:checkExits p a z m t y r cap=true):
    ∀e,e<(powerBox p a m).q→active p a m e→
      PairChecks z (min m (p.k+1-e*m)) (ownerFlag a) (cofactorFlag p a e) t y r cap:=by
  intro e he ha
  have hh:=List.all_eq_true.mp hc e (List.mem_range.mpr he)
  simpa only [checkExit,if_pos ha,decide_eq_true_eq] using hh
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r:ℕ}
theorem BLQ (nodes:I ↪ K) (hI:Fintype.card I=262144)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (fixedS:MovingFiberThreeSources6811.Source P.F) (fixed:Degrees) (hFixed:Fits fixedS fixed)
    (c:Choice) (a:Box) (m low cap:ℕ)
    (hloF:low≤wt RCN156.residualTotalWeights P.F) (hlo:1700<low) (hcap:3000000000000000≤cap)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (h:Contains a (point J))
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
    (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
    (hc:check c fixed a m low t y r cap=true):
    P.seeds.card≤max (MG t y r) cap:=by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hm,hms,h2,hsmall,hJF,hsChar⟩:=hc.1
  have hsrc (useOwner:Bool): ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (chosenZ useOwner fixed a m):=by
    cases useOwner
    · exact ⟨fixedS,hFixed⟩
    · exact owner_source P J a m hm h hms h2 hroot
  cases c with
  | native=>
    have hh:=of_decide_eq_true hc.2
    obtain ⟨S,hS⟩:=owner_source P J a m hm h hms h2 hroot
    exact (BVF P S _ hS (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2 P.rlow).trans
      (max_le_max le_rfl hh.2)
  | derivative useOwner=>
    have hh:=of_decide_eq_true hc.2
    obtain ⟨S,hS⟩:=hsrc useOwner
    exact GBB P S _ hS (hh.2.1.1.trans_le hloF) hh.2.1.2.1 hh.2.1.2.2
      (hlo.trans_le hloF) J hJ a m cap h hh.1 (hms.trans h.1) hsmall hsChar hroot
      ⟨hh.2.2.1,hh.2.2.2.1⟩ hh.2.2.2.2
  | auxiliary useOwner i=>
    have hh:=hc.2
    simp only [checkChoice,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨S,hS⟩:=hsrc useOwner
    exact GHJ nodes hI P S _ hS (hh.1.1.1.1.trans_le hloF)
      hh.1.1.1.2.1 hh.1.1.1.2.2 i (hh.1.1.2.trans_le hloF) J hJ a m cap h hm hroot hJne
      (hJF.trans_le hloF) hcap hh.1.2 (exits_spec _ _ _ _ _ _ _ _ hh.2)
end
end BH
end MergedPart3
section MergedPart6
namespace CQJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF LK
open MovingFiberThreeSources6811 (direction weight)
open HI
open SN (Common)
structure Point where
  b:ℕ
  u:ℕ
  t:ℕ
  deriving DecidableEq
structure Box where
  blo:ℕ
  bhi:ℕ
  ulo:ℕ
  uhi:ℕ
  tlo:ℕ
  thi:ℕ
  deriving DecidableEq
def Empty (a:Box):=a.bhi<a.blo∨a.uhi<a.ulo∨a.thi<a.tlo
instance (a:Box):Decidable (Empty a):=by unfold Empty;infer_instance
structure Choice where
  which:Fin 3
  derivative:Bool
  deriving DecidableEq
end
end CQJ
end MergedPart6
section MergedPart8
namespace AYU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GZ LK
open MovingFiberThreeSources6811 (direction weight)
open ON
open DR LV HI
open AIA BMA
def LinearChecks (B U L t y r cap:ℕ):Prop:=
  Gates t y r (B-2) (U-1) (L-1)∧
  flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433∧
  linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
    (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)≤cap
instance (B U L t y r cap:ℕ):Decidable (LinearChecks B U L t y r cap):=by
  unfold LinearChecks Gates;infer_instance
end
end AYU
end MergedPart8
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ALQ
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
variable {σ:Type*} [DecidableEq σ]
def coeffPoly (e:σ→₀ ℕ) (P:Polynomial (MvPolynomial σ K)):Polynomial K:=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.mapRange
    (fun c:MvPolynomial σ K=>c.coeff e) (by simp) P.toFinsupp.coeff))
@[simp] theorem FEH (e:σ→₀ ℕ) (P:Polynomial (MvPolynomial σ K)) (j:ℕ):
    (coeffPoly e P).coeff j=(P.coeff j).coeff e:=rfl
theorem DZT {ι:Type*} (s:Finset ι) (mu:ι→ℕ)
    (q m n A W G nu:ℕ) (hA:A=W+G) (hcard:s.card=A)
    (hnu:m*W≤nu) (hloss:(∑ i∈s,(mu i-m))≤nu-m*W):
    n*A≤(∑ i∈s,(n-q*mu i))+q*nu+q*m*G:=by
  have hmu:(∑ i∈s,mu i)≤A*m+∑ i∈s,(mu i-m):=by
    calc
      _≤∑ i∈s,(m+(mu i-m)):=Finset.sum_le_sum (fun i _=>by omega)
      _=_:=by simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,hcard]
  have hsub:=Nat.sub_add_cancel hnu
  have hmul:A*m=W*m+G*m:=by rw [hA];ring
  have hmu' :(∑ i∈s,mu i)≤nu+m*G:=by nlinarith
  have hp:n*A≤(∑ i∈s,(n-q*mu i))+q*(∑ i∈s,mu i):=by
    calc
      _=∑ i∈s,n:=by simp [hcard,Nat.mul_comm]
      _≤∑ i∈s,((n-q*mu i)+q*mu i):=Finset.sum_le_sum (fun i _=>by omega)
      _=_:=by simp only [Finset.sum_add_distrib,Finset.mul_sum]
  have hh:=Nat.mul_le_mul_left q hmu'
  nlinarith
section ProductJets
variable {R:Type*} [CommRing R] [IsDomain R]
theorem EXH (J:Polynomial R) (hJ:J≠0) (q:ℕ):
    (J^q).rootMultiplicity 0=q*J.rootMultiplicity 0:=by
  induction q with
  | zero=>simp
  | succ q ih=>
    rw [pow_succ,Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hJ) hJ),ih]
    simp only [Nat.succ_mul]
theorem quotient_jet (J Q:Polynomial R) (hJ:J≠0) (q n:ℕ)
    (h:Polynomial.X^n ∣ J^q*Q):
    Polynomial.X^(n-q*J.rootMultiplicity 0)∣Q:=by
  by_cases hQ:Q=0
  · simp [hQ]
  have hn:n≤(J^q*Q).rootMultiplicity 0:=by
    apply (Polynomial.le_rootMultiplicity_iff (mul_ne_zero (pow_ne_zero _ hJ) hQ)).mpr
    simpa using h
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hJ) hQ),
    EXH J hJ q] at hn
  have hd:n-q*J.rootMultiplicity 0≤Q.rootMultiplicity 0:=by omega
  have hh:=(Polynomial.le_rootMultiplicity_iff hQ).mp hd
  simpa using hh
end ProductJets
end
end ALQ
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ASN
open scoped BigOperators
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {K I:Type*} [Field K]
theorem DIJ (nodes:I ↪ K) (u0 u1:I→K)
    (J:SecondJetSupport.Poly (K:=K)) (f:Polynomial K) (z:K) (A:Finset I)
    (mu:I→ℕ) (m D:ℕ)
    (hag: ∀i∈A,f.eval (nodes i)=u0 i+u1 i*z)
    (hmu: ∀i∈A,MvPolynomial.X 0^mu i ∣
      SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) J))
    (hne:SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤D):
    (∑ i∈A,(mu i-m))≤D:=by
  classical
  let R:=SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)
  have hroot (i:I) (hi:i∈A):(mu i-m)≤R.rootMultiplicity (nodes i):=by
    apply (Polynomial.le_rootMultiplicity_iff hne).mpr
    by_cases hm:m≤mu i
    · apply SecondJetSpecialize.root_contact ((MvPolynomial.pderiv 1)^[m] J) f (nodes i) (u0 i) (u1 i) z (mu i-m) (hag i hi)
      apply SecondJetGlobalDifferentiation.local_derivative_contact (nodes i) (u0 i) (u1 i) J (mu i-m) m
      simpa only [Nat.sub_add_cancel hm] using hmu i hi
    · simp only [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hm)),pow_zero]
      exact one_dvd _
  have hsum:(∑ i∈A,(mu i-m))≤∑ i∈A,R.rootMultiplicity (nodes i):=
    Finset.sum_le_sum (fun i hi=>hroot i hi)
  have hmass:(∑ x∈A.map nodes,R.rootMultiplicity x)≤R.natDegree:=
    RCN355.sum_rootMultiplicity_le_natDegree R (A.map nodes)
  rw [Finset.sum_map] at hmass
  exact hsum.trans (hmass.trans hdegree)
end
end ASN
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AMR
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {K:Type*} [Field K]
theorem BZR (P:SecondJetSupport.Poly (K:=K)) (n:ℕ):
    MvPolynomial.X 0^n∣P ↔ Polynomial.X^n∣(MvPolynomial.finSuccEquiv K 4) P:=by
  constructor
  · intro h
    have hd:=map_dvd (MvPolynomial.finSuccEquiv K 4).toRingHom h
    change (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0^n)∣(MvPolynomial.finSuccEquiv K 4) P at hd
    simpa only [map_pow,MvPolynomial.finSuccEquiv_X_zero] using hd
  · rintro ⟨R,hR⟩
    refine ⟨(MvPolynomial.finSuccEquiv K 4).symm R,?_⟩
    apply (MvPolynomial.finSuccEquiv K 4).injective
    rw [map_mul,map_pow,MvPolynomial.finSuccEquiv_X_zero,AlgEquiv.apply_symm_apply]
    exact hR
end
end AMR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace NS
open scoped BigOperators
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type*} [Field K]
def outer (x u0 u1:K) (J:SecondJetSupport.Poly (K:=K)):=
  (MvPolynomial.finSuccEquiv K 4) (SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize x u0 u1 J))
theorem BXW (J:SecondJetSupport.Poly (K:=K)) (f:Polynomial K)
    (x u0 u1 z:K) (m:ℕ) (hag:f.eval x=u0+u1*z)
    (hne:SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0):
    SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize x u0 u1 J)≠0:=by
  intro hz
  let R:=SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)
  have hd:MvPolynomial.X 0^(R.natDegree+1+m) ∣
      SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize x u0 u1 J):=by simp [hz]
  have hh:=SecondJetGlobalDifferentiation.local_derivative_contact x u0 u1 J
    (R.natDegree+1) m hd
  have hr:=SecondJetSpecialize.root_contact ((MvPolynomial.pderiv 1)^[m] J)
    f x u0 u1 z (R.natDegree+1) hag hh
  have hle:=Polynomial.natDegree_le_of_dvd hr hne
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hle
  change R.natDegree+1≤R.natDegree at hle
  omega
end
end NS
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace SI
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
def lowerA (e:Fin 5→₀ ℕ):=Finsupp.equivFunOnFinite.symm
  (fun i=>if i=2 then e 2-1 else e i)
@[simp] theorem lowerA_apply (e:Fin 5→₀ ℕ) (i:Fin 5):
    lowerA e i=if i=2 then e 2-1 else e i:=by simp [lowerA]
end
end SI
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace LM
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type*} [Field K]
def code (e:Fin 5→₀ ℕ):=e 0+131069*e 1+131071*e 2+131070*e 3
def Bounds (C T B S U:ℕ) (Q:SecondJetSupport.Poly (K:=K)):Prop:= ∀e∈Q.support,
  code e<C∧e 1+e 2+e 3+e 4≤T∧2*e 1+e 3≤B∧e 1≤S∧e 1+e 2+e 3≤U
end
end LM
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace BJM
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open SecondJetHelperWeights renaming cleared_weight → BUF
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K E:Type*} [Field K] [Field E]
theorem DEB
    (J:SecondJetSupport.Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (phi:MvPolynomial (Fin 4) K→+*E) (s m:ℕ)
    (hS: ∀e∈J.support,e 1≤s) (hF:phi F=0)
    (hH:phi (2*RCN313.polyH K F)≠0) (hne:(SecondJetCoefficients.asS J).map phi≠0)
    (hfact:(m.factorial:E)≠0)
    (hm:((SecondJetCoefficients.asS J).map phi).rootMultiplicity (SecondJetCarrierDichotomy.ratio phi F)=m):
    ¬F∣SecondJetClearedHelper.helper J F (s-m) m:=by
  have hder:(((Polynomial.derivative)^[m] ((SecondJetCoefficients.asS J).map phi)).eval (SecondJetCarrierDichotomy.ratio phi F))≠0:=by
    rcases RootMultiplicityDichotomy.derivative_or_high_multiplicity
      ((SecondJetCoefficients.asS J).map phi) hne (SecondJetCarrierDichotomy.ratio phi F) m hfact with h | h
    · obtain ⟨d,hd,hn⟩:=h
      have he:d=m:=by
        by_contra hdm
        have hlt:d<((SecondJetCoefficients.asS J).map phi).rootMultiplicity (SecondJetCarrierDichotomy.ratio phi F):=by omega
        exact hn (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt)
      simpa only [he] using hn
    · have hh:=(Polynomial.le_rootMultiplicity_iff hne).mpr h
      omega
  intro hd
  have hz:=map_dvd phi hd
  rw [hF,zero_dvd_iff,SecondJetCarrierDichotomy.mapped_helper J F phi s m hS hH] at hz
  exact (mul_ne_zero (pow_ne_zero _ hH) hder) hz
section PacketSeed
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
open RCN095 RCN234 RCN156
open RCN095 renaming PolynomialInFlag → BI
open DU ER
open CB EF
open FF HI
theorem CZX {t y r:ℕ} (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (p:Parameters) (hp:Shape p) (J:SecondJetSupport.Poly (K:=K)) (m:ℕ)
    (hm:m≤p.s)
    (hflags: ∀e∈J.support,2*e 1+e 3≤p.B∧e 1+e 2+e 3≤p.U∧
      e 1+e 2+e 3+e 4≤p.L)
    (hslope: ∀e∈J.support,e 1≤p.s)
    (hproper: ¬P.F∣SecondJetClearedHelper.helper J P.F (p.s-m) m)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64):
    P.seeds.card<3000000000000000∨
      ∃gamma∈P.seeds,SecondJetSpecialize.specialize (P.selected gamma) gamma
        ((MvPolynomial.pderiv 1)^[m] J)≠0:=by
  classical
  by_cases hex: ∃gamma∈P.seeds,SecondJetSpecialize.specialize (P.selected gamma) gamma
      ((MvPolynomial.pderiv 1)^[m] J)≠0
  · exact Or.inr hex
  left
  have hzero: ∀gamma∈P.seeds,SecondJetSpecialize.specialize (P.selected gamma) gamma
      ((MvPolynomial.pderiv 1)^[m] J)=0:=by
    simpa only [not_exists,not_and,not_not] using hex
  have hF:=And.intro P.r_weight (And.intro P.y_weight P.total_weight)
  have hweights:=SecondJetHelperWeights.helper_weights J P.F p.B p.U p.L p.s m t y r hp.slope
    (by have:=hp.slope;have:=hp.middle;omega)
    (by have:=hp.slope;have:=hp.middle;have:=hp.total;omega) hm
    (by have:=P.rlow;omega) (by have:=P.rlow;have:=P.ylow;omega)
    (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega) hflags hF
  have hrr:=Nat.mul_le_mul_right (r-1) (Nat.sub_le p.s m)
  have hyy:=Nat.mul_le_mul_right (y-1) (Nat.sub_le p.s m)
  have htt:=Nat.mul_le_mul_right (t-1) (Nat.sub_le p.s m)
  have hweights' :wt RCN156.residualSWeights (SecondJetClearedHelper.helper J P.F (p.s-m) m)≤p.B+p.s*(r-1)∧
      wt RCN156.residualYSWeights (SecondJetClearedHelper.helper J P.F (p.s-m) m)≤p.U+p.s*(y-1)∧
      wt RCN156.residualTotalWeights (SecondJetClearedHelper.helper J P.F (p.s-m) m)≤p.L+p.s*(t-1):=by omega
  obtain ⟨hr,hy,ht⟩:=KY.ESM p P hb hu hl hs
  have hg:=KY.gates_mono t y r _ _ _ 7200 71 14 1088 4992 464832
    P.thigh P.yhigh P.rhigh hr hy ht KY.DZN.1
  have hc:=ER.DHG P (SecondJetClearedHelper.helper J P.F (p.s-m) m)
    _ _ _ (P.irreducible.isRelPrime_iff_not_dvd.mpr hproper) hweights' hg
    (fun gamma hgamma=>SecondJetClearedHelper.helper_vanish J P.F (p.s-m) m
      (SecondJetHelperWeights.asS_derivative_degree J p.s m hslope) (P.selected gamma) gamma
      (P.solution gamma hgamma) (hzero gamma hgamma))
  exact hc.trans_lt ((KY.count_mono t y r _ _ _ 7200 71 14 1088 4992 464832
    P.thigh P.yhigh P.rhigh hr hy ht).trans_lt KY.DZN.2)
def maximumOwner:Parameters:=⟨65,4096,256,64,512,0,1⟩
theorem ENC:Shape maximumOwner:=by constructor<;>decide+kernel
theorem CMA {t y r:ℕ} (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (J:SecondJetSupport.Poly (K:=K)) (m:ℕ) (hms:m≤J.degreeOf 1) (horder:J.degreeOf 1≤64)
    (hflags: ∀e∈J.support,2*e 1+e 3≤256∧e 1+e 2+e 3≤512∧
      e 1+e 2+e 3+e 4≤4096)
    (hne:(SecondJetCoefficients.asS J).map (DC.carrierMap P.F)≠0)
    (hm:((SecondJetCoefficients.asS J).map (DC.carrierMap P.F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (DC.carrierMap P.F) P.F)=m):
    P.seeds.card<3000000000000000∨
      ∃gamma∈P.seeds,SecondJetSpecialize.specialize (P.selected gamma) gamma
        ((MvPolynomial.pderiv 1)^[m] J)≠0:=by
  have hS: ∀e∈J.support,e 1≤64:=fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans horder
  have hchar:=P.IZ.2.1.trans_lt
    (by have:=P.rhigh;omega:r<2130706433)
  have hnot:=DEB J P.F (DC.carrierMap P.F)
    64 m hS (DC.DQY P.F)
    (DC.ALO P.F P.rdegree hchar) hne
    (SecondJetOwnShape.factorial_ne m (by omega)) hm
  exact CZX nodes P maximumOwner ENC J m
    (hms.trans horder) hflags hS hnot (by decide) (by decide) (by decide) (by decide)
end PacketSeed
end
end BJM
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AIP
open MvPolynomial
open SecondJetSupport (Box Poly)
open LM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K:Type*} [Field K]
theorem code_add_S (e:Fin 5→₀ ℕ) (m:ℕ):
    code (e+Finsupp.single 1 m)=code e+131069*m:=by
  simp only [code,Finsupp.add_apply,Finsupp.single_apply]
  norm_num
  ring
theorem ARL
    (J:SecondJetSupport.Poly (K:=K)) (f:Polynomial K) (z:K) (m nu:ℕ)
    (hf:f.natDegree≤131071) (hc: ∀e∈J.support,code e≤nu):
    (SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*131069:=by
  have hh:=SecondJetSpecialize.specialization_degree ((MvPolynomial.pderiv 1)^[m] J)
    f z 131071 (nu-m*131069+1) hf (by omega) (by
      intro e he
      have h:=hc _ (SecondJetGlobalDifferentiation.support_iterate J m e he)
      rw [code_add_S] at h
      change e 0+131071*e 2+131070*e 3+131069*e 1<nu-m*131069+1
      dsimp only [code] at h
      omega)
  omega
end
end AIP
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace TA
open MvPolynomial CW DJ XB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open DA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K I:Type*} [Field K]
theorem BLT (e:Fin 5→₀ ℕ):
    LM.code e=Finsupp.weight codeWeights e:=by
  simp [LM.code,JW,codeWeights,Nat.mul_comm,Nat.add_comm,
    Nat.add_left_comm,Nat.add_assoc]
end
end TA
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace BYG
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K:Type*} [Field K]
theorem EHN (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (m:ℕ)
    (hms:m≤J.degreeOf 1):m*131069≤weightedTotalDegree codeWeights J:=by
  classical
  obtain ⟨e,he,hh⟩:=Finset.exists_mem_eq_sup J.support (MvPolynomial.support_nonempty.mpr hJ)
    (fun e=>e (1:Fin 5))
  have hd:J.degreeOf 1=e 1:=by rw [MvPolynomial.degreeOf_eq_sup];exact hh
  have hc:LM.code e≤weightedTotalDegree codeWeights J:=by
    rw [TA.BLT]
    exact le_weightedTotalDegree codeWeights he
  dsimp only [LM.code] at hc
  rw [hd] at hms
  nlinarith
end
end BYG
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace BSV
open scoped BigOperators
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open LM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type*} [Field K]
theorem DYW
    (nodes:I ↪ K) (u0 u1:I→K) (s:Finset I)
    (J P Q:SecondJetSupport.Poly (K:=K)) (q m n nu D:ℕ)
    (heq:P=J^q*Q)
    (hjet: ∀i∈s,MvPolynomial.X 0^n∣SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (z:K) (hf:f.natDegree≤131071)
    (hag: ∀i∈s,f.eval (nodes i)=u0 i+u1 i*z)
    (hne:SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(SecondJetSpecialize.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*131069)
    (hnu:m*131069≤nu) (hcard:s.card=181059) (hD:D+q*nu=n*181059)
    (hQ:weightedTotalDegree CW.codeWeights Q<D-q*m*49990):
    SecondJetSpecialize.specialize f z Q=0:=by
  classical
  let mu (i:I):=(NS.outer (nodes i) (u0 i) (u1 i) J).rootMultiplicity 0
  let ord (i:I):=n-q*mu i
  have hmu (i:I):MvPolynomial.X 0^mu i∣SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) J):=by
    apply (AMR.BZR _ _).mpr
    simpa only [mu,NS.outer,map_zero,sub_zero] using
      (NS.outer (nodes i) (u0 i) (u1 i) J).pow_rootMultiplicity_dvd 0
  have hloss:=ASN.DIJ nodes u0 u1 J f z s
    mu m (nu-m*131069) hag (fun i _=>hmu i) hne hdegree
  have hmass:=ALQ.DZT s mu q m n 181059 131069 49990 nu
    (by decide) hcard hnu hloss
  let R:=SecondJetSpecialize.specialize f z Q
  by_contra hR
  have hroot (i:I) (hi:i∈s):ord i≤R.rootMultiplicity (nodes i):=by
    have hJ:NS.outer (nodes i) (u0 i) (u1 i) J≠0:=by
      intro hz
      apply NS.BXW J f (nodes i) (u0 i) (u1 i) z m (hag i hi) hne
      exact (MvPolynomial.finSuccEquiv K 4).injective (by simpa only [NS.outer,map_zero] using hz)
    have hp:=(AMR.BZR _ _).mp (hjet i hi)
    have he:NS.outer (nodes i) (u0 i) (u1 i) P=
      (NS.outer (nodes i) (u0 i) (u1 i) J)^q*
        NS.outer (nodes i) (u0 i) (u1 i) Q:=by
      simp only [NS.outer,heq,map_mul,map_pow]
    change Polynomial.X^n∣NS.outer (nodes i) (u0 i) (u1 i) P at hp
    rw [he] at hp
    have hq:=ALQ.quotient_jet _ _ hJ q n hp
    have hcontact:=(AMR.BZR _ _).mpr hq
    have hh:=SecondJetSpecialize.root_contact Q f (nodes i) (u0 i) (u1 i) z (ord i) (hag i hi) hcontact
    exact (Polynomial.le_rootMultiplicity_iff hR).mpr hh
  have hsum:(∑ i∈s,ord i)≤R.natDegree:=by
    have h1:=Finset.sum_le_sum hroot
    have h2:=RCN355.sum_rootMultiplicity_le_natDegree R (s.map nodes)
    rw [Finset.sum_map] at h2
    exact h1.trans h2
  have hdeg:R.natDegree≤weightedTotalDegree CW.codeWeights Q:=by
    have hh:=AIP.ARL Q f z 0
      (weightedTotalDegree CW.codeWeights Q) hf (fun e he=>by
        rw [TA.BLT]
        exact le_weightedTotalDegree CW.codeWeights he)
    simpa only [Function.iterate_zero,id_eq,Nat.zero_mul,Nat.sub_zero] using hh
  change n*181059≤(∑ i∈s,ord i)+q*nu+q*m*49990 at hmass
  omega
end
end BSV
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AMK
open scoped BigOperators
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open BJM
open RCN095 RCN234 DU DC
open RCN095 renaming PolynomialInFlag → BI
open FF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
abbrev Small (Q:SecondJetSupport.Poly (K:=K)):Prop:=Q.degreeOf 1≤64∧
  ∀e∈Q.support,2*e 1+e 3≤256∧e 1+e 2+e 3≤512∧e 1+e 2+e 3+e 4≤4096
theorem FIN {t y r:ℕ}
    (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (J T Q:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (q m n nu D:ℕ)
    (heq:T=J^q*Q)
    (hjet: ∀i,MvPolynomial.X 0^n∣SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (P.u0 i) (P.u1 i) T))
    (hms:m≤J.degreeOf 1) (hJs:Small J) (hQs:Small Q)
    (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
    (hnu:weightedTotalDegree CW.codeWeights J=nu)
    (hD:D+q*nu=n*181059)
    (hQcode:weightedTotalDegree CW.codeWeights Q<D-q*m*49990):
    P.F∣SecondJetClearedHelper.helper Q P.F 64 0∨P.seeds.card<6000000000000000:=by
  classical
  by_cases hproper:P.F∣SecondJetClearedHelper.helper Q P.F 64 0
  · exact Or.inl hproper
  right
  let zeroSeeds:=P.seeds.filter (fun g=>SecondJetSpecialize.specialize (P.selected g) g Q=0)
  let nonzeroSeeds:=P.seeds.filter (fun g=>SecondJetSpecialize.specialize (P.selected g) g Q≠0)
  have hZsub:zeroSeeds⊆P.seeds:=Finset.filter_subset _ _
  have hUsub:nonzeroSeeds⊆P.seeds:=Finset.filter_subset _ _
  let zeroPacket:=P.restrict zeroSeeds hZsub
  let nonzeroPacket:=P.restrict nonzeroSeeds hUsub
  letI:Fact (Irreducible zeroPacket.F):=⟨zeroPacket.irreducible⟩
  letI:Fact (Irreducible nonzeroPacket.F):=⟨nonzeroPacket.irreducible⟩
  have hZsmall:zeroSeeds.card<3000000000000000:=by
    rcases CZX nodes zeroPacket maximumOwner ENC Q 0
        (by decide) hQs.2 (fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans hQs.1)
        hproper (by decide) (by decide) (by decide) (by decide)
        with hs | ⟨g,hg,hn⟩
    · exact hs
    · have hz:=(Finset.mem_filter.mp hg).2
      exact False.elim (hn (by simpa only [zeroPacket,Packet.restrict,Function.iterate_zero,id_eq] using hz))
  have hUsmall:nonzeroSeeds.card<3000000000000000:=by
    rcases CMA nodes nonzeroPacket J m hms hJs.1 hJs.2 hJne hroot
        with hs | ⟨g,hg,hn⟩
    · exact hs
    · have hgP:g∈P.seeds:=hUsub hg
      obtain ⟨Aagree,hAsub,hAcard⟩:=Finset.exists_subset_card_eq (P.agreement g hgP)
      have hag: ∀i∈Aagree,(P.selected g).eval (nodes i)=P.u0 i+P.u1 i*g:=by
        intro i hi
        simpa only [mul_comm] using (Finset.mem_filter.mp (hAsub hi)).2
      have hnuLow:m*131069≤nu:=by
        rw [←hnu]
        exact BYG.EHN J hJ m hms
      have hdeg:=AIP.ARL J (P.selected g) g m nu
        (P.degree g hgP) (fun e he=>by
          rw [TA.BLT]
          exact (le_weightedTotalDegree CW.codeWeights he).trans_eq hnu)
      have hz:=BSV.DYW nodes P.u0 P.u1 Aagree
        J T Q q m n nu D heq (fun i _=>hjet i) (P.selected g) g (P.degree g hgP)
        hag hn hdeg hnuLow hAcard hD hQcode
      exact False.elim ((Finset.mem_filter.mp hg).2 hz)
  have hcover:P.seeds⊆zeroSeeds∪nonzeroSeeds:=by
    intro g hg
    by_cases hz:SecondJetSpecialize.specialize (P.selected g) g Q=0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hg,hz⟩)
  have hc:=(Finset.card_le_card hcover).trans (Finset.card_union_le zeroSeeds nonzeroSeeds)
  omega
end
end AMK
end SubmissionLower
end ProximityPrize
end
namespace ProximityPrize
namespace SubmissionLower
namespace BandPrefixKernel6816
open scoped BigOperators
theorem weighted_prefix (q C M : Nat) :
 (∑ a : Fin M, (q-131071*a.val)*(C-a.val)) =
 SecondJetGlobalCounts.weightedCell q 131071 C (min ((q-1)/131071+1) (min M C)) := by
  let n := min ((q-1)/131071+1) (min M C)
  have hnM : n≤M := by dsimp [n]; omega
  have hs : (∑a ∈ Finset.range M, (q-131071*a)*(C-a)) =
   ∑a ∈ Finset.range n, (q-131071*a)*(C-a) := by
   symm
   apply Finset.sum_subset (Finset.range_mono hnM)
   intro a ha hnot
   simp only [Finset.mem_range] at ha hnot
   have hz : q-131071*a=0 ∨ C-a=0 := by dsimp [n] at hnot; omega
   rcases hz with hz|hz <;> simp only [hz, Nat.zero_mul, Nat.mul_zero]
  calc
   _ = ∑a : Fin n, (q-131071*a.val)*(C-a.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun a : Nat => (q-131071*a)*(C-a)),
        Fin.sum_univ_eq_sum_range (fun a : Nat => (q-131071*a)*(C-a))]
    exact hs
   _ = _ := by
    apply SecondJetGlobalCounts.sum_weighted_cell
    · intro a
      have ha := a.isLt
      dsimp [n] at ha
      omega
    · intro a
      have ha := a.isLt
      dsimp [n] at ha
      omega
theorem sum_fin_cut (f : Nat → Nat) (M n : Nat) (hn : n≤M)
  (hz : ∀ (i : Nat), n ≤ i → i < M → f i = 0) : (∑i : Fin M, f i.val) = ∑i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hi hnot
  simp only [Finset.mem_range] at hi hnot
  exact hz i (by omega) hi
def row (D T B U h : Nat) : Nat :=
  ∑r : Fin (B+1-2*h), ∑a : Fin (U+1-h-r.val),
   (D-131069*h-131070*r.val-131071*a.val)*(T+1-h-r.val-a.val)
def prefixCount (D T B S U : Nat) : Nat := ∑h : Fin (S+1), row D T B U h.val
theorem prefix_eq (D T B S U : Nat) :
 prefixCount D T B S U = SecondJetRelaxedGlobalCounts.coefficientCount (fun _ => D) 131071 T B (min S (B/2)) (min U T) := by
  have hcut : prefixCount D T B S U = ∑h : Fin (min S (B/2)+1), row D T B U h.val := by
   apply sum_fin_cut
   · omega
   · intro h hlo hhi
     have hz : B+1-2*h=0 := by omega
     simp [row, hz]
  rw [hcut]
  unfold SecondJetRelaxedGlobalCounts.coefficientCount
  apply Finset.sum_congr rfl
  intro h hh
  have hm := h.isLt
  have hb : B+1-2*h.val=B-2*h.val+1 := by omega
  unfold row
  rw [hb]
  apply Finset.sum_congr rfl
  intro r hr
  rw [weighted_prefix]
  dsimp only [SecondJetRelaxedGlobalIndex.yCount, SecondJetRelaxedGlobalIndex.budget]
  norm_num only [Nat.reduceSub]
  congr 1 <;> omega
def inner (h r a : Nat) := 131069*h+131070*r+131071*a
def rawCount (D width T B S U : Nat) : Nat :=
 ∑h : Fin (S+1), ∑r : Fin (B+1-2*h.val), ∑a : Fin (U+1-h.val-r.val),
  min width (D-inner h.val r.val a.val)*(T+1-h.val-r.val-a.val)
theorem band_add_prefix (D width T B S U : Nat) :
 rawCount D width T B S U + prefixCount (D-width) T B S U = prefixCount D T B S U := by
  unfold rawCount prefixCount row
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have e1 : D-131069*h.val-131070*r.val-131071*a.val = D-inner h.val r.val a.val := by unfold inner; omega
  have e2 : D-width-131069*h.val-131070*r.val-131071*a.val = D-width-inner h.val r.val a.val := by unfold inner; omega
  rw [e1, e2, ←Nat.add_mul]
  have he : min width (D-inner h.val r.val a.val)+(D-width-inner h.val r.val a.val)=D-inner h.val r.val a.val := by omega
  rw [he]
def closedCount (D width T B S U : Nat) : Nat :=
 SecondJetRelaxedGlobalCounts.coefficientCount (fun _ => D) 131071 T B (min S (B/2)) (min U T) -
 SecondJetRelaxedGlobalCounts.coefficientCount (fun _ => D-width) 131071 T B (min S (B/2)) (min U T)
theorem count_eq (D width T B S U : Nat) : rawCount D width T B S U = closedCount D width T B S U := by
  have h := band_add_prefix D width T B S U
  rw [prefix_eq, prefix_eq] at h
  unfold closedCount
  omega
end BandPrefixKernel6816
end SubmissionLower
end ProximityPrize
section
namespace ProximityPrize
namespace SubmissionLower
namespace BLM
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
def inner (h r a:ℕ):=131069*h+131070*r+131071*a
def start (D width h r a:ℕ):=D-width-inner h r a
def length (D width h r a:ℕ):=min width (D-inner h r a)
def Index (D width T B S U:ℕ):=
 (h:Fin (S+1)) × (r:Fin (B+1-2*h.val)) × (a:Fin (U+1-h.val-r.val)) ×
 (Fin (length D width h.val r.val a.val) × Fin (T+1-h.val-r.val-a.val))
instance (D width T B S U:ℕ):Fintype (Index D width T B S U):=by unfold Index;infer_instance
def exponent (D width T B S U:ℕ) (i:Index D width T B S U):Fin 5→₀ ℕ:=
 Finsupp.equivFunOnFinite.symm ![start D width i.1.val i.2.1.val i.2.2.1.val+i.2.2.2.1.val,
   i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]
def count (D width T B S U:ℕ):=BandPrefixKernel6816.closedCount D width T B S U
theorem count_eq_sum (D width T B S U:ℕ):count D width T B S U=
 ∑ h:Fin (S+1),∑ r:Fin (B+1-2*h.val),∑ a:Fin (U+1-h.val-r.val),
 length D width h.val r.val a.val*(T+1-h.val-r.val-a.val):=by
 exact (BandPrefixKernel6816.count_eq D width T B S U).symm
theorem card_eq (D width T B S U:ℕ):Fintype.card (Index D width T B S U)=count D width T B S U:=by
 simp only [Index,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,count_eq_sum]
theorem count_mono_D (D E width T B S U:ℕ) (hDE:D≤E):
 count D width T B S U≤count E width T B S U:=by
 rw [count_eq_sum,count_eq_sum]
 apply Finset.sum_le_sum
 intro h _
 apply Finset.sum_le_sum
 intro r _
 apply Finset.sum_le_sum
 intro a _
 apply Nat.mul_le_mul_right
 exact min_le_min_left _ (Nat.sub_le_sub_right hDE _)
theorem AKF (D width T B S U:ℕ) (e:Fin 5→₀ ℕ)
 (hc:LM.code e<D) (hl:D-width≤LM.code e)
 (ht:e 1+e 2+e 3+e 4≤T) (hb:2*e 1+e 3≤B) (hs:e 1≤S)
 (hu:e 1+e 2+e 3≤U):e∈Set.range (exponent D width T B S U):=by
 have hh:e 1<S+1:=by omega
 have hr:e 3<B+1-2*e 1:=by omega
 have ha:e 2<U+1-e 1-e 3:=by omega
 have hstart:start D width (e 1) (e 3) (e 2)≤e 0:=by
   dsimp only [start,inner,LM.code] at*
   omega
 have hx:e 0-start D width (e 1) (e 3) (e 2)<length D width (e 1) (e 3) (e 2):=by
   dsimp only [start,length,inner,LM.code] at*
   omega
 have hg:e 4<T+1-e 1-e 3-e 2:=by omega
 refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hr⟩,⟨e 2,ha⟩,⟨e 0-start D width (e 1) (e 3) (e 2),hx⟩,⟨e 4,hg⟩⟩,?_⟩
 ext j
 fin_cases j<;>simp [exponent,Nat.add_sub_of_le hstart]
theorem ECV {K:Type*} [Field K]
 (D width T B S U:ℕ) (Q:SecondJetSupport.Poly (K:=K)) (hQ:Q≠0)
 (hb:LM.Bounds D T B S U Q)
 (hp: ∀i,Q.coeff (exponent D width T B S U i)=0):
 weightedTotalDegree CW.codeWeights Q<D-width:=by
 classical
 have hevery: ∀e∈Q.support,Finsupp.weight CW.codeWeights e<D-width:=by
   intro e he
   obtain ⟨hc,ht,hB,hS,hU⟩:=hb e he
   rw [←TA.BLT]
   by_contra hn
   obtain ⟨i,hi⟩:=AKF D width T B S U e hc (by omega) ht hB hS hU
   exact (MvPolynomial.mem_support_iff.mp he) (by rw [←hi];exact hp i)
 have hpos:0<D-width:=by
   obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr hQ
   exact (Nat.zero_le _).trans_lt (hevery e he)
 have hh:weightedTotalDegree CW.codeWeights Q≤D-width-1:=by
   apply Finset.sup_le
   intro e he
   exact Nat.le_sub_one_of_lt (hevery e he)
 omega
end
end BLM
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace EKS
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open DC CB BD
open MovingFiberThreeSources6811 (direction weight)
open AMK RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [CharP K 2130706433]
theorem FGS
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (cap:ℕ) (hFT:cap<wt RCN156.residualTotalWeights F)
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (Q:SecondJetSupport.Poly (K:=K)) (hQ:Q≠0) (hS:Q.degreeOf 1≤64)
    (hT:total Q≤cap) (hdiv:F∣SecondJetClearedHelper.helper Q F 64 0):
    ∃SQ:MovingFiberThreeSources6811.Source F,SQ.P=Q∧1≤SQ.d:=by
  let phi:=carrierMap F
  have hH:phi (2*RCN313.polyH K F)≠0:=ALO F hpos hchar
  have hz:=map_dvd phi hdiv
  rw [DQY,zero_dvd_iff] at hz
  have hs: ∀e∈Q.support,e 1≤64:=fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans hS
  have hm:=SecondJetCarrierDichotomy.mapped_helper Q F phi 64 0 hs hH
  simp only [Nat.sub_zero,Function.iterate_zero,id_eq] at hm
  have hroot:((SecondJetCoefficients.asS Q).map phi).eval (SecondJetCarrierDichotomy.ratio phi F)=0:=by
    rw [hm] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hH)
  have hp:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^1∣(SecondJetCoefficients.asS Q).map (carrierMap F):=by
    simpa only [pow_one] using (Polynomial.dvd_iff_isRoot.mpr hroot)
  exact ZD.UN F cap hFT hpos hchar Q hQ hT 1 (by decide) hp
end
end EKS
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ZZ
open MvPolynomial CW DJ XB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DA
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K:Type*} [Field K]
def powSpace (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)) (e:ℕ):Submodule K (SecondJetSupport.Poly (K:=K)) where
 carrier:={P | P∈V∧J^e∣P}
 zero_mem' :=⟨V.zero_mem,dvd_zero _⟩
 add_mem' hP hQ:=⟨V.add_mem hP.1 hQ.1,dvd_add hP.2 hQ.2⟩
 smul_mem' c P hP:=by
   refine ⟨V.smul_mem c hP.1,?_⟩
   obtain ⟨Q,hQ⟩:=hP.2
   refine ⟨c • Q,?_⟩
   rw [hQ]
   simp only [MvPolynomial.smul_eq_C_mul]
   ring
theorem powSpace_le (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)) (e:ℕ):
 powSpace V J e≤V:=fun _ h=>h.1
@[simp] theorem GVA (V:Submodule K (SecondJetSupport.Poly (K:=K))) (J:SecondJetSupport.Poly (K:=K)):
 powSpace V J 0=V:=by ext P;simp [powSpace]
def bandCount (p:SourceCaps) (a:OwnerBox) (m e:ℕ):ℕ:=
 BLM.count (p.C-e*(131071*a.loU-a.hiB)) (e*m*49990)
   (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)
theorem EAJ (p:SourceCaps) (a:OwnerBox) (e:ℕ)
 (P J Q:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hQ:Q≠0) (heq:P=J^e*Q)
 (hP:Bounds p P) (ha:Covers a J):
 LM.Bounds (p.C-e*weightedTotalDegree codeWeights J)
   (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU) Q:=by
 let aa:OwnerBox:={a with q:=e}
 have haa:Covers aa J:=ha
 obtain ⟨_,_,ht,hB,hS,hU⟩:=AUL p aa P J Q hJ hQ heq hP haa
 have hc:=hP.1
 rw [heq,weight_mul codeWeights _ _ (pow_ne_zero _ hJ) hQ,weight_pow codeWeights J hJ] at hc
 intro d hd
 have cc:=le_weightedTotalDegree codeWeights hd
 have tt:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights hd).trans ht
 have bb:=(le_weightedTotalDegree slopeWeights hd).trans hB
 have ss:=(MvPolynomial.monomial_le_degreeOf 1 hd).trans hS
 have uu:=(le_weightedTotalDegree HA hd).trans hU
 rw [←TA.BLT] at cc
 simp only [JW,Koala6831Ordinary.totalWeights,slopeWeights,HA] at tt bb uu
 norm_num at tt bb uu
 dsimp only [aa,remT,remB] at tt bb ss uu
 refine ⟨by omega,?_,?_,ss,?_⟩<;>omega
theorem step
 (p:SourceCaps) (a:OwnerBox) (m e:ℕ)
 (V:Submodule K (SecondJetSupport.Poly (K:=K))) [Module.Finite K V]
 (hb: ∀P∈V,Bounds p P) (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hlow: ∀(P Q:SecondJetSupport.Poly (K:=K)),P∈V→P=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*49990→J∣Q):
 Module.finrank K (powSpace V J e)≤bandCount p a m e+Module.finrank K (powSpace V J (e+1)):=by
 classical
 let W:=powSpace V J e
 letI:Module.Finite K W:=Submodule.finiteDimensional_of_le (powSpace_le V J e)
 let hd: ∀v:W,J^e∣v.val:=fun v=>v.property.2
 let Q:=BKC W J e hJ hd
 have heq (v:W):v.val=J^e*Q v:=RV W J e hd v
 let D:=p.C-e*weightedTotalDegree codeWeights J
 let width:=e*m*49990
 let idx:=BLM.Index D width (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)
 let ex:=BLM.exponent D width (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)
 let proj:W→ₗ[K] (idx→K):=LinearMap.pi (fun i=>(MvPolynomial.lcoeff K (ex i)).comp Q)
 have hnext (v:proj.ker):(v.val:W).val∈powSpace V J (e+1):=by
   let w:W:=v.val
   have hp: ∀i,(Q w).coeff (ex i)=0:=by
     intro i
     have hh:=congrFun v.property i
     exact hh
   have hdiv:J∣Q w:=by
     by_cases hz:Q w=0
     · rw [hz];exact dvd_zero _
     apply hlow w.val (Q w) w.property.1 (heq w) hz
     exact BLM.ECV D width _ _ _ _ (Q w) hz
       (EAJ p a e w.val J (Q w) hJ hz (heq w) (hb w.val w.property.1) ha) hp
   refine ⟨w.property.1,?_⟩
   obtain ⟨R,hR⟩:=hdiv
   refine ⟨R,?_⟩
   rw [heq w,hR,pow_succ,mul_assoc]
 let inc:proj.ker→ₗ[K] powSpace V J (e+1):=
   (((powSpace V J e).subtype).comp proj.ker.subtype).codRestrict _ hnext
 have hi:Function.Injective inc:=by
   intro v u h
   apply Subtype.ext
   apply Subtype.ext
   have hh:=congrArg (fun z:powSpace V J (e+1)=>z.val) h
   change v.val.val=u.val.val at hh
   exact hh
 letI:Module.Finite K (powSpace V J (e+1)):=Submodule.finiteDimensional_of_le (powSpace_le V J (e+1))
 have hk:=LinearMap.finrank_le_finrank_of_injective hi
 have hr:Module.finrank K proj.range≤Fintype.card idx:=by
   have hh:=proj.range.finrank_le
   simpa using hh
 have hsum:=proj.finrank_range_add_finrank_ker
 change Module.finrank K proj.range+Module.finrank K proj.ker=Module.finrank K (powSpace V J e) at hsum
 have hactual:Fintype.card idx≤bandCount p a m e:=by
   rw [BLM.card_eq]
   apply BLM.count_mono_D
   apply Nat.sub_le_sub_left
   exact Nat.mul_le_mul_left e (BKI J hJ a.loU a.hiB ha.2.2.2.1 ha.2.1)
 omega
theorem telescope
 (p:SourceCaps) (a:OwnerBox) (m N:ℕ)
 (V:Submodule K (SecondJetSupport.Poly (K:=K))) [Module.Finite K V]
 (hb: ∀P∈V,Bounds p P) (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hlow: ∀e<N,∀(P Q:SecondJetSupport.Poly (K:=K)),P∈V→P=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*49990→J∣Q):
 Module.finrank K V≤(∑ e∈Finset.range N,bandCount p a m e)+Module.finrank K (powSpace V J N):=by
 induction N with
 | zero=>
   rw [GVA V J]
   simp
 | succ N ih=>
   have hprev:=ih (fun e he=>hlow e (by omega))
   have hstep:=step p a m N V hb J hJ ha (hlow N (by omega))
   rw [Finset.sum_range_succ]
   omega
theorem EVH
 (p:SourceCaps) (a:OwnerBox) (N:ℕ)
 (V:Submodule K (SecondJetSupport.Poly (K:=K)))
 (hb: ∀P∈V,Bounds p P) (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hstop:Impossible p {a with q:=N}):powSpace V J N=⊥ :=by
 apply le_antisymm _ bot_le
 intro P hP
 change P=0
 by_contra hPne
 obtain ⟨Q,hQ⟩:=hP.2
 have heq:P=J^N*Q:=hQ
 have hQne:Q≠0:=by intro hz;simp [hz] at heq;exact hPne heq
 exact (AUL p {a with q:=N} P J Q hJ hQne heq (hb P hP.1) ha).1 hstop
end
end ZZ
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace DDV
open MvPolynomial CW DJ XB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open CB DC BD
open MovingFiberThreeSources6811 (direction weight)
open DU EF GF
open SecondJetCoefficients (liftExponent)
open HI LV DR BH
open RCN095 RCN234 RCN156 ER
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem GHY {t y r:ℕ}
 (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (p:DA.SourceCaps) (n:ℕ) (hpC:p.C=n*181059)
 (hpSmall:p.B≤256∧p.U≤512∧p.T≤4096∧p.S≤64)
 (hFT:p.T<wt RCN156.residualTotalWeights P.F)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (a:DR.Box) (ha:Contains a (point J))
 (m:ℕ) (hms:m≤J.degreeOf 1) (hJs:AMK.Small J)
 (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
 (SJ SZ:MovingFiberThreeSources6811.Source P.F) (hSJ:SJ.P=J) (hSJd:1≤SJ.d)
 (z:Degrees) (hZ:Fits SZ z) (hZFT:z.T<wt RCN156.residualTotalWeights P.F)
 (hk:z.k<2130706433) (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
 (cap:ℕ) (hcap:6000000000000000≤cap) (hlarge:cap<P.seeds.card) (T0 Bh Ch qd nh:ℕ) (hT0:T0≤wt RCN156.residualTotalWeights P.F) (hcert:FormalR.H2.Certificate r y T0 Bh Ch qd nh)
 (hidentity:MG t y r≤cap)
 (hgeo:flagMixed (ownerFlag a) (flag p.B p.U p.T p.S) unitZFlag<2130706433∧
   flagMixed (ownerFlag a) (flag p.B p.U p.T p.S) unitYZFlag<2130706433∧
   FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.T p.S) Bh Ch qd t y r+leading z t y r≤cap)
 (e:ℕ) (T Q:SecondJetSupport.Poly (K:=K))
 (heq:T=J^e*Q) (hQ:Q≠0) (hb:DA.Bounds p T)
 (hjet: ∀i,MvPolynomial.X 0^n∣SecondJetDifferentiation.substitute (K:=K) (SecondJetGlobalSupport.localize (nodes i) (P.u0 i) (P.u1 i) T))
 (hcode:weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*49990):
 J∣Q:=by
 classical
 by_contra hnot
 have hn:=ZZ.EAJ p (⟨e,0,weightedTotalDegree slopeWeights J,0,0,0⟩) e
   T J Q hJ.ne_zero hQ heq hb (by exact ⟨Nat.zero_le _,le_rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩)
 have hTQ:total Q≤p.T:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.1
   simpa [total,JW,Koala6831Ordinary.totalWeights] using hh
 have hBQ:slope Q≤p.B:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.2.1
   simpa [CB.slope,JW,slopeWeights,Nat.mul_comm] using hh
 have hSQ:Q.degreeOf 1≤p.S:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   exact fun d hd=>(hn d hd).2.2.2.1
 have hUQ:middle Q≤p.U:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.2.2.2
   simpa [middle,JW,HA] using hh
 have hQs:AMK.Small Q:=by
   refine ⟨hSQ.trans hpSmall.2.2.2,?_⟩
   intro d hd
   have hh:=hn d hd
   exact ⟨hh.2.2.1.trans hpSmall.1,hh.2.2.2.2.trans hpSmall.2.1,hh.2.1.trans hpSmall.2.2.1⟩
 have hc:=hb.1
 rw [heq,weight_mul codeWeights _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow codeWeights J hJ.ne_zero] at hc
 have henu:e*weightedTotalDegree codeWeights J≤p.C:=by omega
 have hD:p.C-e*weightedTotalDegree codeWeights J+e*weightedTotalDegree codeWeights J=n*181059:=by
   rw [Nat.sub_add_cancel henu,hpC]
 rcases AMK.FIN nodes P J T Q hJ.ne_zero e m n
     (weightedTotalDegree codeWeights J) (p.C-e*weightedTotalDegree codeWeights J) heq hjet
     hms hJs hQs hJne hroot rfl hD hcode with hdiv | hsmall
 · have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
   obtain ⟨SQ,hSQP,hSQd⟩:=EKS.FGS P.F p.T hFT P.rdegree hchar Q hQ
     hQs.1 hTQ hdiv
   have hcop:IsRelPrime SJ.P SQ.P:=by
     rw [hSJ,hSQP]
     exact hJ.isRelPrime_iff_not_dvd.mpr hnot
   have hJF:=_Q23 J a ha
   rw [←hSJ] at hJF
   have hQF:=FBA Q p.B p.U p.T p.S hBQ hUQ hTQ hSQ
   rw [←hSQP] at hQF
   have hbnd:=FormalR.H2.pair_count_of_degreesEH P SZ SJ SQ z hZ hZFT hk hg hcop 1
     (by decide) (by decide) hSJd hSQd _ _ hJF hQF hgeo.1 hgeo.2.1 P.rlow T0 Bh Ch qd nh hT0 hcert
   have hh:=hbnd.trans (max_le hidentity hgeo.2.2)
   omega
 · omega
end
end DDV
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace XU
open MvPolynomial CW DJ XB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open CB DC BD
open MovingFiberThreeSources6811 (direction weight)
open DU EF GF
open SecondJetCoefficients (liftExponent)
open HI LV DR BH
open RCN095 RCN234 RCN156 ER
open RCN095 renaming PolynomialInFlag → BI
open FF ZGL
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem packet_count {t y r:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
 (hpSmall:p.B≤256∧p.U≤512∧p.L≤4096∧p.s≤64)
 (hFT:p.L<wt RCN156.residualTotalWeights P.F)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (a:DR.Box) (ha:Contains a (point J))
 (m:ℕ) (hms:m≤J.degreeOf 1) (hJs:AMK.Small J)
 (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
 (SJ SZ:MovingFiberThreeSources6811.Source P.F) (hSJ:SJ.P=J) (hSJd:1≤SJ.d)
 (z:Degrees) (hZ:Fits SZ z) (hZFT:z.T<wt RCN156.residualTotalWeights P.F)
 (hk:z.k<2130706433) (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
 (cap:ℕ) (hcap:6000000000000000≤cap) (T0 Bh Ch qd nh:ℕ) (hT0:T0≤wt RCN156.residualTotalWeights P.F) (hcert:FormalR.H2.Certificate r y T0 Bh Ch qd nh)
 (hidentity:MG t y r≤cap)
 (hgeo:flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
   flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
   FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.L p.s) Bh Ch qd t y r+leading z t y r≤cap)

 (N:ℕ) (hstop:DA.Impossible (caps p) {powerBox p a m with q:=N})
 (hband:(∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<Kdim):
 P.seeds.card≤cap:=by
 classical
 by_contra hnot
 have hlarge:cap<P.seeds.card:=Nat.lt_of_not_ge hnot
 obtain ⟨V,hV,hv,hb,hjet⟩:=DVF p hp Kdim hd nodes P.u0 P.u1 hN
 letI:Module.Finite K V:=hV
 have hbounds:=fun Q hQ=>CTV p hp Q (hb Q hQ)
 have hcover:DA.Covers (powerBox p a m) J:=by
   exact ⟨ha.2.2.1,ha.2.2.2.1,ha.1,ha.2.2.2.2.1,ha.2.2.2.2.2.2.1⟩
 have hlow: ∀e<N,∀(T Q:SecondJetSupport.Poly (K:=K)),T∈V→T=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<(caps p).C-e*weightedTotalDegree codeWeights J-e*m*49990→J∣Q:=by
   intro e he T Q hT heq hQ hcode
   exact DDV.GHY nodes P (caps p) p.m rfl hpSmall hFT J hJ a ha m hms hJs
     hJne hroot SJ SZ hSJ hSJd z hZ hZFT hk hg cap hcap hlarge T0 Bh Ch qd nh hT0 hcert hidentity hgeo
     e T Q heq hQ (hbounds T hT) (hjet T hT) hcode
 have hdim:=ZZ.telescope (caps p) (powerBox p a m) m N V hbounds J hJ.ne_zero hcover hlow
 have hz:=ZZ.EVH (caps p) (powerBox p a m) N V hbounds J hJ.ne_zero hcover hstop
 rw [hz] at hdim
 simp only [finrank_bot,add_zero] at hdim
 omega
end
end XU
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AUA
open FF ZGL
open LV BH HI ZZ
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def p:Parameters:=⟨51,400,23,11,70,0,1⟩
theorem shape:Shape p:=by constructor<;>decide+kernel
theorem middle_p (h:ℕ) (hh:h≤11):70≤(p.cutoff h+23-1)/131071:=by
 interval_cases h<;>decide+kernel
theorem coefficients:SecondJetRelaxedGlobalCounts.coefficientCount p.cutoff 131071 400 23 11 70=13495078984543:=by decide+kernel
theorem rank:SecondJetRelaxedCounts.rankBound 51 400 23 11 70=51397405:=by decide+kernel
theorem dimension:Dimension p 21557648223:=by
 exact AZ p 21557648223 13495078984543 51397405 (by decide) (by decide) (by decide) (by decide) (by decide) middle_p coefficients rank (by decide)
end AUA
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace BWK
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def p600:Parameters:=⟨51,600,23,11,70,0,1⟩
theorem shape600:Shape p600:=by constructor<;>decide+kernel
theorem middle600 (h:ℕ) (hh:h≤11):70≤(p600.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem GIT:SecondJetRelaxedGlobalCounts.coefficientCount p600.cutoff 131071 600 23 11 70=20774814314943:=by decide+kernel
theorem rank600:SecondJetRelaxedCounts.rankBound 51 600 23 11 70=78773405:=by decide+kernel
theorem dimension600:Dimension p600 124838834623:=by
 exact AZ p600 124838834623 20774814314943 78773405 (by decide) (by decide) (by decide) (by decide) (by decide) middle600 GIT rank600 (by decide)
def p1000:Parameters:=⟨51,1000,23,11,70,0,1⟩
theorem shape1000:Shape p1000:=by constructor<;>decide+kernel
theorem middle1000 (h:ℕ) (hh:h≤11):70≤(p1000.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem GDB:SecondJetRelaxedGlobalCounts.coefficientCount p1000.cutoff 131071 1000 23 11 70=35334284975743:=by decide+kernel
theorem rank1000:SecondJetRelaxedCounts.rankBound 51 1000 23 11 70=133525405:=by decide+kernel
theorem GXD:Dimension p1000 331401207423:=by
 exact AZ p1000 331401207423 35334284975743 133525405 (by decide) (by decide) (by decide) (by decide) (by decide) middle1000 GDB rank1000 (by decide)
def profile (i:Fin 3):Parameters:=match i.val with
 | 0=>AUA.p
 | 1=>p600
 | _=>p1000
def kernel (i:Fin 3):ℕ:=match i.val with
 | 0=>21557648223
 | 1=>124838834623
 | _=>331401207423
theorem shape (i:Fin 3):Shape (profile i):=by fin_cases i;exact AUA.shape;exact shape600;exact shape1000
theorem dimension (i:Fin 3):Dimension (profile i) (kernel i):=by fin_cases i;exact AUA.dimension;exact dimension600;exact GXD
end BWK
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ACX
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF
open MovingFiberThreeSources6811 (direction weight)
open HI LV BH DR
open FF ZGL BWK
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance
def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed
def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (N Bh Ch qd:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.L p.s) Bh Ch qd t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (N Bh Ch qd:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N Bh Ch qd):=by
 unfold BandValid SN.Common Gates;infer_instance
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem CPT {t y r low cap m:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (SZ:MovingFiberThreeSources6811.Source P.F) (fixed:Degrees) (hFixed:Fits SZ fixed)
 (hFT:low≤wt RCN156.residualTotalWeights P.F) (hcap:6000000000000000≤cap)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
 (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
 (i:Fin 3) (useOwner:Bool) (N Bh Ch qd nh:ℕ) (hcert:FormalR.H2.Certificate r y low Bh Ch qd nh) (hc:BandValid fixed a m low t y r cap i useOwner N Bh Ch qd):
 P.seeds.card≤cap:=by
 classical
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,haf,hpf,hcommon,hid,hstop,hband,hz,huy,hgeo⟩:=hc
 have hsmall:AMK.Small J:=by
   refine ⟨ha.2.1.trans hs,?_⟩
   intro d hd
   have hB:=(le_weightedTotalDegree slopeWeights hd).trans (ha.2.2.2.1.trans hb)
   have hU:=(le_weightedTotalDegree HA hd).trans (ha.2.2.2.2.2.1.trans hu)
   have hT:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights hd).trans (ha.2.2.2.2.2.2.2.trans ht)
   simp only [JW,slopeWeights,HA,Koala6831Ordinary.totalWeights] at hB hU hT
   norm_num at hB hU hT
   exact ⟨by omega,by omega,by omega⟩
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hpower:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F))^1∣(SecondJetCoefficients.asS J).map (carrierMap P.F):=
   (Polynomial.le_rootMultiplicity_iff hJne).mp (by rw [hroot];omega)
 obtain ⟨SJ,hSJ,hSJd⟩:=ZD.UN P.F a.thi
   (haf.trans_le hFT) P.rdegree hchar J hJ.ne_zero ha.2.2.2.2.2.2.2 1 (by decide) hpower
 have hpricing: ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (pricing fixed a m useOwner):=by
   cases useOwner with
   | false=>exact ⟨SZ,hFixed⟩
   | true=>exact owner_source P J a m hm ha hms h2 hroot
 obtain ⟨S,hS⟩:=hpricing
 have hpSmall:(profile i).B≤256∧(profile i).U≤512∧(profile i).L≤4096∧(profile i).s≤64:=by
   fin_cases i<;>decide
 exact XU.packet_count nodes hN P (profile i) (shape i) (kernel i) (dimension i)
   hpSmall (hpf.trans_le hFT) J hJ a ha m (hms.trans ha.1) hsmall hJne hroot SJ S hSJ hSJd
   (pricing fixed a m useOwner) hS (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
   cap hcap low Bh Ch qd nh hFT hcert hid ⟨hz,huy,hgeo⟩ N hstop hband
end
end ACX
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace PA
open DR (Box Point Contains Empty lower upper EQB)
set_option autoImplicit false
def Admissible (m:ℕ) (p:Point):Prop:=
 m≤p.s∧1≤p.s∧2*p.s≤p.b∧p.s≤p.u∧p.b≤p.u+p.s∧p.u≤p.t
def step (m:ℕ) (a:Box):Box:=
 let sl:=max (max (max a.slo m) 1) (a.blo-a.uhi)
 let sh:=min a.shi (a.bhi/2)
 let bl:=max a.blo (2*sl)
 let bh:=min a.bhi (a.uhi+sh)
 let ul:=max (max a.ulo sl) (bl-sh)
 let uh:=min a.uhi a.thi
 let tl:=max a.tlo ul
 ⟨sl,sh,bl,bh,ul,uh,tl,a.thi⟩
def normalize (m:ℕ):ℕ→Box→Box
 | 0,a=>a
 | n+1,a=>normalize m n (step m a)
theorem DVI (m:ℕ) (a:Box) (p:Point)
 (ha:Admissible m p) (hp:Contains a p):Contains (step m a) p:=by
 unfold Admissible Contains at*
 dsimp only [step]
 omega
theorem ATG (m n:ℕ) (a:Box) (p:Point)
 (ha:Admissible m p) (hp:Contains a p):Contains (normalize m n a) p:=by
 induction n generalizing a with
 | zero=>exact hp
 | succ n ih=>exact ih (step m a) (DVI m a p ha hp)
def Covered (m:ℕ) (valid:Box→Prop) (a:Box):Prop:=
 ∀p,Admissible m p→Contains a p→ ∃b,valid b∧Contains b p
theorem AO (m:ℕ) (valid:Box→Prop) (a b:Box)
 (he:normalize m 8 a=b) (h:Covered m valid b):Covered m valid a:=by
 intro p ha hp
 apply h p ha
 rw [←he]
 exact ATG m 8 a p ha hp
theorem BJ (m:ℕ) (valid:Box→Prop) (a:Box) (axis:Fin 4) (v:ℕ)
 (hl:Covered m valid (lower a axis v)) (hh:Covered m valid (upper a axis v)):Covered m valid a:=by
 intro p ha hp
 rcases EQB a p axis v hp with hp | hp
 · exact hl p ha hp
 · exact hh p ha hp
end PA
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ECZ
open ACX HI LV BH
open BWK EF GF RCN095 RCN234 RCN156
open RCN095 renaming PolynomialInFlag → BI
set_option autoImplicit false
def BandGeometry (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (Bh Ch qd:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 SN.Common z low t y r∧MG t y r≤cap∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.L p.s) Bh Ch qd t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (Bh Ch qd:ℕ):Decidable (BandGeometry fixed a m low t y r cap i useOwner Bh Ch qd):=by
 unfold BandGeometry SN.Common ER.Gates;infer_instance
def CQM (a:DR.Box) (m low t y r cap:ℕ):Prop:=
 SN.Common (ownerZ a m) low t y r∧
 nativeScalar (ownerZ a m) t y r/(9*(ownerZ a m).d*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap
instance (a:DR.Box) (m low t y r cap:ℕ):
 Decidable (CQM a m low t y r cap):=by
 unfold CQM SN.Common ER.Gates;infer_instance
def DHJ (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (Bh Ch qd:ℕ):Prop:=
 a.thi<low∧(profile i).L<low∧BandGeometry fixed a m low t y r cap i useOwner Bh Ch qd
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (Bh Ch qd:ℕ):Decidable (DHJ fixed a m low t y r cap i useOwner Bh Ch qd):=by
 unfold DHJ;infer_instance
def CME (a:DR.Box) (m low t y r cap:ℕ):Prop:=
 a.thi<low∧CQM a m low t y r cap
instance (a:DR.Box) (m low t y r cap:ℕ):
 Decidable (CME a m low t y r cap):=by unfold CME;infer_instance
end ECZ
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace JG
open DR (Box Contains lower upper)
open HI LV BH
open ACX ECZ PA
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
structure Leaf where
 m:ℕ
 a:Box
 kind:Option (Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ)
def leaf:Fin 29→Leaf:= ![⟨1,⟨1,1,2,3,1,35,1,321⟩,none⟩,⟨1,⟨1,1,4,4,3,19,3,321⟩,none⟩,⟨1,⟨1,1,4,4,20,27,20,321⟩,none⟩,⟨1,⟨1,1,4,4,28,35,28,321⟩,some (⟨1,by decide⟩,true,3,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,1,5,7,4,19,4,321⟩,none⟩,⟨1,⟨1,1,5,7,20,35,20,321⟩,some (⟨2,by decide⟩,true,4,484000,198893,10000000,10740000000)⟩,⟨1,⟨2,2,4,5,2,35,2,321⟩,none⟩,⟨1,⟨2,2,6,7,4,19,4,321⟩,none⟩,⟨1,⟨2,2,6,7,20,35,20,321⟩,some (⟨2,by decide⟩,true,4,484000,198893,10000000,10740000000)⟩,⟨1,⟨3,3,6,7,3,35,3,321⟩,none⟩,⟨1,⟨1,6,8,12,2,18,2,321⟩,some (⟨2,by decide⟩,true,3,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,6,8,12,19,35,19,321⟩,some (⟨1,by decide⟩,false,3,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,11,13,23,2,35,2,321⟩,some (⟨0,by decide⟩,false,2,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,6,2,12,36,70,36,178⟩,some (⟨1,by decide⟩,false,2,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,6,2,12,36,70,179,321⟩,some (⟨0,by decide⟩,false,2,484000,198893,10000000,10740000000)⟩,⟨1,⟨1,11,13,23,36,70,36,321⟩,some (⟨0,by decide⟩,false,2,484000,198893,10000000,10740000000)⟩,⟨2,⟨2,6,4,13,2,36,2,321⟩,none⟩,⟨2,⟨2,6,4,13,37,70,37,321⟩,some (⟨1,by decide⟩,true,2,484000,198893,10000000,10740000000)⟩,⟨2,⟨2,11,14,23,3,36,3,321⟩,some (⟨1,by decide⟩,true,2,484000,198893,10000000,10740000000)⟩,⟨2,⟨2,11,14,23,37,70,37,321⟩,some (⟨0,by decide⟩,false,2,484000,198893,10000000,10740000000)⟩,⟨3,⟨3,11,6,23,3,70,3,321⟩,none⟩,⟨4,⟨4,11,8,23,4,70,4,321⟩,none⟩,⟨5,⟨5,11,10,23,5,70,5,321⟩,none⟩,⟨6,⟨6,11,12,23,6,70,6,321⟩,none⟩,⟨7,⟨7,11,14,23,7,70,7,321⟩,none⟩,⟨8,⟨8,11,16,23,8,70,8,321⟩,none⟩,⟨9,⟨9,11,18,23,9,70,9,321⟩,none⟩,⟨10,⟨10,11,20,23,10,70,10,321⟩,none⟩,⟨11,⟨11,11,22,23,11,70,11,321⟩,none⟩]
def Geometry (l:Leaf) (fixedNew:Degrees) (low t y r cap:ℕ):Prop:=match l.kind with
 | none=>CME l.a l.m low t y r cap
 | some c=>FormalR.H2.Certificate r y low c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2∧DHJ fixedNew l.a l.m low t y r cap c.1 c.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1
instance (l:Leaf) (fixedNew:Degrees) (low t y r cap:ℕ):Decidable (Geometry l fixedNew low t y r cap):=by unfold Geometry;split<;>infer_instance
def AllGeometry (fixedNew:Degrees) (low t y r cap:ℕ):Prop:= ∀i:Fin 29,Geometry (leaf i) fixedNew low t y r cap
instance (fixedNew:Degrees) (low t y r cap:ℕ):Decidable (AllGeometry fixedNew low t y r cap):=by unfold AllGeometry;infer_instance
end JG
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace GI
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF GZ
open MovingFiberThreeSources6811 (direction weight)
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def degrees (i:Fin 2):Degrees:=
 let p:=CN.profile i
 ⟨p.B,p.U,p.L,p.k,p.n0⟩
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem AGF {t y r:ℕ} (i:Fin 2) (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) t y r)
 (hFT:(CN.profile i).L<wt RCN156.residualTotalWeights P.F):
 P.seeds.card<3000000000000000∨ ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (degrees i):=by
 let p:=CN.profile i
 rcases VT p (CN.shape i) (CN.kernel i)
   (CN.positive i) (CN.dimension i)
   nodes P.u0 P.u1 hI P.F P.irreducible hFT r y t (by have:=P.rlow;omega)
   (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
   ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · have small:=CN.small i
   exact Or.inl (KY.helper_count p nodes P small.1 small.2.1 small.2.2.1 small.2.2.2.1 Q hQ)
 · exact Or.inr ⟨S,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2⟩
end
end GI
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace CP
open DR (Box Contains Empty lower upper)
open PA
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
inductive Tree where
 | empty:Tree
 | leaf:ℕ→Tree
 | node:Fin 4→ℕ→Tree→Tree→Tree
def decode:ℕ→ℕ→Tree × ℕ
 | 0,code=>(.empty,code)
 | n+1,code=>
  if code%4=0 then (.leaf (code/4%65536),code/262144)
  else if code%4=1 then
   let left:=decode n (code/1048576)
   let right:=decode n left.2
   (.node ⟨code/4%4,Nat.mod_lt _ (by decide)⟩ (code/16%65536) left.1 right.1,right.2)
  else (.empty,code/4)
def subset (a b:Box):Prop:=
 b.slo≤a.slo∧a.shi≤b.shi∧b.blo≤a.blo∧a.bhi≤b.bhi∧
 b.ulo≤a.ulo∧a.uhi≤b.uhi∧b.tlo≤a.tlo∧a.thi≤b.thi
instance (a b:Box):Decidable (subset a b):=by unfold subset;infer_instance
def check (boxes:ℕ→Box) (N m:ℕ):Tree→Box→Bool
 | .empty,a=>decide (Empty (normalize m 8 a))
 | .leaf i,a=>decide (i<N∧subset (normalize m 8 a) (boxes i))
 | .node axis pivot left right,a=>
   let b:=normalize m 8 a
   check boxes N m left (lower b axis pivot) && check boxes N m right (upper b axis pivot)
theorem sound (boxes:ℕ→Box) (N m:ℕ) (valid:Box→Prop)
 (hv: ∀i,i<N→valid (boxes i)) (tree:Tree) (a:Box)
 (h:check boxes N m tree a=true):Covered m valid a:=by
 induction tree generalizing a with
 | empty=>
  simp only [check,decide_eq_true_eq] at h
  intro p hp ha
  have hb:=ATG m 8 a p hp ha
  unfold DR.Empty Contains at*
  omega
 | leaf i=>
  simp only [check,decide_eq_true_eq] at h
  intro p hp ha
  have hb:=ATG m 8 a p hp ha
  refine ⟨boxes i,hv i h.1,?_⟩
  have hs:=h.2
  unfold subset Contains at*
  omega
 | node axis pivot left right ihl ihr=>
  simp only [check,Bool.and_eq_true] at h
  apply AO m valid a (normalize m 8 a) rfl
  exact BJ m valid _ axis pivot (ihl _ h.1) (ihr _ h.2)
def listBox (xs:List Box) (i:ℕ):Box:=(xs[i]?).getD ⟨0,0,0,0,0,0,0,0⟩
theorem listBox_valid (xs:List Box) (valid:Box→Prop)
 (h: ∀a∈xs,valid a) (i:ℕ) (hi:i<xs.length):valid (listBox xs i):=by
 have hh:=h xs[i] (List.getElem_mem hi)
 simpa only [listBox,List.getElem?_eq_getElem hi,Option.getD_some] using hh
end CP
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace ADB
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF GZ
open MovingFiberThreeSources6811 (direction weight)
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def degrees (i:Fin 2):Degrees:=
 let p:=CN.profile i
 ⟨p.B,p.U,p.L,p.k,p.n0⟩
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem AGF {t y r:ℕ} (i:Fin 2) (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) t y r)
 (hFT:(CN.profile i).L<wt RCN156.residualTotalWeights P.F):
 P.seeds.card<3000000000000000∨ ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (degrees i):=by
 let p:=CN.profile i
 rcases VT p (CN.shape i) (CN.kernel i)
   (CN.positive i) (CN.dimension i)
   nodes P.u0 P.u1 hI P.F P.irreducible hFT r y t (by have:=P.rlow;omega)
   (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
   ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · have small:=CN.small i
   exact Or.inl (KY.helper_count p nodes P small.1 small.2.1 small.2.2.1 small.2.2.2.1 Q hQ)
 · exact Or.inr ⟨S,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2⟩
end
end ADB
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace QE
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
theorem small (i:Fin 52):(profile i).B≤256∧(profile i).U≤512∧(profile i).L≤4096∧(profile i).s≤64:=by fin_cases i<;>decide
end QE
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace AED
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ CB
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC FN
open SecondJetCoefficients (liftExponent)
open DU ER EF
open BD GF
open MovingFiberThreeSources6811 (direction weight)
open HI LV BH DR
open FF ZGL QE
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance
def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed
def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 52) (useOwner:Bool) (N Bh Ch qd:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.L p.s) Bh Ch qd t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 52) (useOwner:Bool) (N Bh Ch qd:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N Bh Ch qd):=by
 unfold BandValid SN.Common Gates;infer_instance
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem CPT {t y r low cap m:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (SZ:MovingFiberThreeSources6811.Source P.F) (fixed:Degrees) (hFixed:Fits SZ fixed)
 (hFT:low≤wt RCN156.residualTotalWeights P.F) (hcap:6000000000000000≤cap)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
 (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
 (i:Fin 52) (useOwner:Bool) (N Bh Ch qd nh:ℕ) (hcert:FormalR.H2.Certificate r y low Bh Ch qd nh) (hc:BandValid fixed a m low t y r cap i useOwner N Bh Ch qd):
 P.seeds.card≤cap:=by
 classical
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,haf,hpf,hcommon,hid,hstop,hband,hz,huy,hgeo⟩:=hc
 have hsmall:AMK.Small J:=by
   refine ⟨ha.2.1.trans hs,?_⟩
   intro d hd
   have hB:=(le_weightedTotalDegree slopeWeights hd).trans (ha.2.2.2.1.trans hb)
   have hU:=(le_weightedTotalDegree HA hd).trans (ha.2.2.2.2.2.1.trans hu)
   have hT:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights hd).trans (ha.2.2.2.2.2.2.2.trans ht)
   simp only [JW,slopeWeights,HA,Koala6831Ordinary.totalWeights] at hB hU hT
   norm_num at hB hU hT
   exact ⟨by omega,by omega,by omega⟩
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hpower:(Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F))^1∣(SecondJetCoefficients.asS J).map (carrierMap P.F):=
   (Polynomial.le_rootMultiplicity_iff hJne).mp (by rw [hroot];omega)
 obtain ⟨SJ,hSJ,hSJd⟩:=ZD.UN P.F a.thi
   (haf.trans_le hFT) P.rdegree hchar J hJ.ne_zero ha.2.2.2.2.2.2.2 1 (by decide) hpower
 have hpricing: ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (pricing fixed a m useOwner):=by
   cases useOwner with
   | false=>exact ⟨SZ,hFixed⟩
   | true=>exact owner_source P J a m hm ha hms h2 hroot
 obtain ⟨S,hS⟩:=hpricing
 have hpSmall:=QE.small i
 exact XU.packet_count nodes hN P (profile i) (shape i) (kernel i) (dimension i)
   hpSmall (hpf.trans_le hFT) J hJ a ha m (hms.trans ha.1) hsmall hJne hroot SJ S hSJ hSJd
   (pricing fixed a m useOwner) hS (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
   cap hcap low Bh Ch qd nh hFT hcert hid ⟨hz,huy,hgeo⟩ N hstop hband
def linearU (a:DR.Box):=max a.bhi a.uhi
def linearT (a:DR.Box):=max (linearU a) a.thi
def LinearValid (a:DR.Box) (low t y r cap:ℕ):Prop:=
 a.shi≤1∧2≤a.bhi∧linearT a<low∧
 AYU.LinearChecks a.bhi (linearU a) (linearT a) t y r cap
instance (a:DR.Box) (low t y r cap:ℕ):Decidable (LinearValid a low t y r cap):=by unfold LinearValid;infer_instance
theorem CUP {t y r low cap:ℕ} {x:I→K}
 (P:Packet x t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt RCN156.residualTotalWeights P.F) (hid:MG t y r≤cap)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).eval (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=0)
 (hc:LinearValid a low t y r cap):P.seeds.card≤cap:=by
 obtain ⟨hs,hB,hL,hchecks⟩:=hc
 have hS:J.degreeOf 1=1:=by have hh:=ha.2.1;change order J≤a.shi at hh;change order J=1;omega
 have hshape: ∀e∈J.support,2*e 1+e 3≤a.bhi∧e 1+e 2+e 3≤linearU a∧e 1+e 2+e 3+e 4≤linearT a:=by
   intro e he
   have hb:=(le_weightedTotalDegree slopeWeights he).trans ha.2.2.2.1
   have hu:Finsupp.weight HA e≤linearU a:=(le_weightedTotalDegree HA he).trans (ha.2.2.2.2.2.1.trans (le_max_right a.bhi a.uhi))
   have ht:Finsupp.weight Koala6831Ordinary.totalWeights e≤linearT a:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights he).trans (ha.2.2.2.2.2.2.2.trans (le_max_right (linearU a) a.thi))
   simp only [JW,slopeWeights,HA,Koala6831Ordinary.totalWeights] at hb hu ht
   norm_num at hb hu ht
   exact ⟨by omega,by omega,by omega⟩
 have hh:=AOR.BNL P J hJ hS a.bhi (linearU a) (linearT a)
   hB (le_max_left _ _) (le_max_left _ _) hshape (hL.trans_le hFT) hroot hchecks.1 hchecks.2.1
 exact hh.trans (max_le hid hchecks.2.2)
end
end AED
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace OZ
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open DC
open SecondJetCoefficients (liftExponent)
open BD DU EF
open MovingFiberThreeSources6811 (direction weight)
open CB HI DR LV
open AED ADB
open RCN095 RCN234 RCN156
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
def fallback:Fin 2:=⟨0,by decide⟩
def Valid (m low t y r cap:ℕ) (a:DR.Box):Prop:=
 BH.check .native (degrees fallback) a m low t y r cap=true∨
 LinearValid a low t y r cap∨
 ∃(i:Fin 52) (useOwner:Bool) (j:Fin 2) (N Bh Ch qd nh:ℕ),
   (CN.profile j).L<low∧FormalR.H2.Certificate r y low Bh Ch qd nh∧
   BandValid (degrees j) a m low t y r cap i useOwner N Bh Ch qd
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem BLH {m low t y r cap:ℕ}
 (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt RCN156.residualTotalWeights P.F) (hLow:1700<low)
 (hcap:6000000000000000≤cap) (hid:MG t y r≤cap)
 (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
 (hJne:(SecondJetCoefficients.asS J).map (carrierMap P.F)≠0)
 (hJroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).eval (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=0)
 (hc:Valid m low t y r cap a):P.seeds.card≤cap:=by
 rcases hc with hc | hc | ⟨i,useOwner,j,N,Bh,Ch,qd,nh,hL,hcert,hc⟩
 · have hL:(CN.profile fallback).L<low:=by
     have hh:(CN.profile fallback).L=912:=by decide+kernel
     omega
   rcases AGF fallback nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact (BH.BLQ nodes hI P SZ (degrees fallback) hZ .native a m low cap
     hFT (by omega) (by omega) J hJ ha hroot hJne hc).trans (max_le hid le_rfl)
 · exact CUP P hFT hid J hJ.ne_zero horder a ha hJroot hc
 · rcases AGF j nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact CPT nodes hI P SZ (degrees j) hZ hFT hcap J hJ a ha hroot hJne i useOwner N Bh Ch qd nh hcert hc
end
end OZ
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
