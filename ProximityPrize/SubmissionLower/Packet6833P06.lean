/- Apache-2.0. 68.36 retuning by Bome2017. Packet construction from BitWonka’s PR 623 and the earlier Bome2017, Lucieno and 0xAndoroid proofs. -/
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
import ProximityPrize.SubmissionLower.Packet6833P05
import ProximityPrize.SubmissionLower.P33Profiles3
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace LevelCount
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing LevelComponent.isPrime
variable {N p : ℕ} {g H : MvPolynomial (Fin 3) E} {f : RCN002.CoordinateField E G} {c : E} {A₁ : RCN002.CoordinateField E G}
  {W : FlagDegree}
variable {ι : Type*} {C : ι → Ideal (MvPolynomial (Fin 3) E)} [∀ i, (C i).IsPrime]
theorem component_count (M : Setup G N p g H f c A₁ W) (live : Finset ι)
    (S : ∀ i, Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E (C i)))
    (hS : ∀ i ∈ live, IsCurveOnSurface G (C i) (S i))
    (htr : ∀ i ∈ live, ∃ j, Transcendental E (coordinate E (C i) j))
    (hinj : ∀ i ∈ live, ∀ i' ∈ live, C i = C i' → i = i')
    (hlive : ∀ i ∈ live, (S i).val (f - algebraMap E (RCN002.CoordinateField E G) c) = 1)
    (e : ι → ℕ) (hord : ∀ i ∈ live, (S i).val A₁ ≤ exp (-(e i : ℤ)))
    (hcl : ∀ i ∈ live, ∀ (q : SurfacePoint G) (hq : q.On (S i)), f ∈ q.ring → q.level f c ≠ 0 →
      Module.Finite ((S i).image hq) (integralClosure ((S i).image hq) (RCN002.CoordinateField E (C i)))) :
    ∃ (s : Finset (LevelComponent G f c))
      (T : ∀ B : LevelComponent G f c, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))),
      ((∑ i ∈ live, e i * curveMoving (S i) f c + baseNumber f c A₁ W : ℕ) : ℤ) ≤
        levelFlagSum s T W := by
  classical
  have := M.charP
  have := finite_component M
  have := Fintype.ofFinite (LevelComponent G f c)
  have hfin : ({q : SurfacePoint G | f ∉ q.ring ∧ q.level f c ≠ 0} ∪
      ⋃ i ∈ live, {q : SurfacePoint G | q.On (S i) ∧ q.level f c ≠ 0}).Finite :=
    (finite_basePoints M.noether M.char f c M.needs.ne).union
      (Set.Finite.biUnion live.finite_toSet fun i hi =>
        finite_levelPoints M.noether M.char (S i) f c (hlive i hi))
  have hmov : ∀ i ∈ live, curveMoving (S i) f c =
      ∑ q ∈ hfin.toFinset, if f ∈ q.ring then q.order (S i) f c 1 else 0 := by
    intro i hi
    rw [curveMoving]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine Or.inr (Set.mem_biUnion hi ?_)
    by_cases hf : f ∈ q.ring
    · simp only [hf, ↓reduceIte] at hq
      exact ⟨by_contra fun hOn => hq (by rw [SurfacePoint.order, dite_eq_right hOn]),
        fun hlev => hq (Exch.order_eq_zero q (S i) f c 1 hlev)⟩
    · simp only [hf, ↓reduceIte] at hq
      exact absurd rfl hq
  have hbase : baseNumber f c A₁ W = ∑ q ∈ hfin.toFinset,
      if f ∈ q.ring then 0 else q.levelNumber f c (q.localFunction A₁ W) := by
    rw [baseNumber]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine Or.inl ?_
    by_cases hf : f ∈ q.ring
    · simp only [hf, ↓reduceIte] at hq
      exact absurd rfl hq
    · simp only [hf, ↓reduceIte] at hq
      exact ⟨hf, fun hlev => hq (Exch.levelNumber_eq_zero q f c _ hlev)⟩
  have hpt : ∀ q ∈ hfin.toFinset,
      (∑ i ∈ live, e i * (if f ∈ q.ring then q.order (S i) f c 1 else 0)) +
        (if f ∈ q.ring then 0 else q.levelNumber f c (q.localFunction A₁ W)) ≤
      q.levelNumber f c (q.localFunction A₁ W) := by
    intro q _
    by_cases hf : f ∈ q.ring
    · simp only [hf, ↓reduceIte, add_zero]
      exact sum_order_le_levelNumber M live S hS htr hinj hlive e hord hcl q hf
    · simp only [hf, ↓reduceIte, mul_zero, Finset.sum_const_zero, zero_add, le_refl]
  choose T hT using fun B : LevelComponent G f c => sum_pointSum_le M B hfin.toFinset
  refine ⟨Finset.univ, T, ?_⟩
  have h1 : ∑ i ∈ live, e i * curveMoving (S i) f c + baseNumber f c A₁ W ≤
      ∑ q ∈ hfin.toFinset, q.levelNumber f c (q.localFunction A₁ W) := by
    rw [hbase, Finset.sum_congr rfl fun i hi => by rw [hmov i hi]]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  have h2 : ∑ q ∈ hfin.toFinset, q.levelNumber f c (q.localFunction A₁ W) =
      ∑ B : LevelComponent G f c,
        B.mult * ∑ q ∈ hfin.toFinset, pointSum B q (q.localFunction A₁ W) := by
    rw [Finset.sum_congr rfl fun q _ =>
      levelNumber_eq M q Finset.univ fun B _ => Finset.mem_univ B, Finset.sum_comm]
    exact Finset.sum_congr rfl fun B _ => (Finset.mul_sum _ _ _).symm
  rw [h2] at h1
  calc ((∑ i ∈ live, e i * curveMoving (S i) f c + baseNumber f c A₁ W : ℕ) : ℤ)
      ≤ ((∑ B : LevelComponent G f c,
          B.mult * ∑ q ∈ hfin.toFinset, pointSum B q (q.localFunction A₁ W) : ℕ) : ℤ) :=
        Int.ofNat_le.mpr h1
    _ = ∑ B : LevelComponent G f c, (B.mult : ℤ) *
          ((∑ q ∈ hfin.toFinset, pointSum B q (q.localFunction A₁ W) : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun B _ => Nat.cast_mul _ _
    _ ≤ levelFlagSum Finset.univ T W :=
        Finset.sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hT B) (Int.natCast_nonneg _)
end Surface
end
end LevelCount
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Exch
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] component_isPrime fact_irreducible SurfacePoint.isNoetherianRing
  SurfacePoint.isIntegrallyClosed SurfacePoint.isFractionRing
theorem exchange_count (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1))
    (hS : ∀ a ∈ active P SZ, IsCurveOnSurface (component P a.1) a.2.1 (S a))
    (hneeds : ExchangeNeeds P SZ Q A c S (flag SZ Hf))
    (hc : ∀ j, sliceCoord P.F j ≠ 0)
    (hI : ∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ)
    (N : ℕ) (hN : ∀ g sR sY sZ, SurfaceNoether (component P g) sR sY sZ N)
    (hNp : 3 * N < 2130706433) (htail : TailOrder P hp SZ S)
    (hp1 : ∀ a ∈ active P SZ,
      PlaceSurf.Statement.surfacePoint_leastOrder_le Ω (component P a.1) (RCN002.CoordinateField Ω a.2.1)) :
    ExchangeCount P hp SZ (baseOrder P Q A c S) (lam P SZ Q A c (flag SZ Hf))
      (constant P hp SZ Q A c S (flag SZ Hf)) := by
  intro n
  have hcomp : ∀ g : RCN222.GeometricFactor K P.F,
      ∑ C ∈ Finset.univ.filter (fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ),
        3 * SZ.d * multiplicity P hp ⟨g, C⟩ * curveBase (S ⟨g, C⟩) (moving P Q A g) c n ≤
      n * baseNumber (moving P Q A g) c (function P SZ g) (flag SZ Hf) +
        componentLoss (moving P Q A g) c (function P SZ g) (flag SZ Hf)
          (Finset.univ.filter fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ)
          (fun C : CM (P.stage g) => S ⟨g, C⟩) (fun C => 3 * SZ.d * multiplicity P hp ⟨g, C⟩) := by
    intro g
    have hact : ∀ C ∈ Finset.univ.filter
        (fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ),
        (⟨g, C⟩ : Curve P) ∈ active P SZ := fun C hC => (Finset.mem_filter.mp hC).2
    rcases (Finset.univ.filter
        (fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ)).eq_empty_or_nonempty with
      hempty | ⟨C₀, hC₀⟩
    · rw [hempty, Finset.sum_empty]
      exact Nat.zero_le _
    · refine component_exchange (F := fun C : CM (P.stage g) => RCN002.CoordinateField Ω C.1) (hN g) hNp
        (coordinate_ne_zero P g hc) _ c _ _
        (localFunction_function_mem P SZ Hf hI g)
        (hneeds.disjoint ⟨g, C₀⟩ (hact C₀ hC₀)) _ _ _ ?_ ?_ ?_ ?_ ?_ n
      · intro C hC C' hC' hval
        refine Subtype.ext (Ideal.ext fun B => ?_)
        rw [mem_iff_of_isCurveOnSurface (hS ⟨g, C⟩ (hact C hC)),
          mem_iff_of_isCurveOnSurface (hS ⟨g, C'⟩ (hact C' hC')), hval]
      · intro C hC j
        exact val_le_one_of_isCurveOnSurface (hS ⟨g, C⟩ (hact C hC)) (MvPolynomial.X j)
      · intro C hC q hq
        exact (hS ⟨g, C⟩ (hact C hC)).exists_primeDivisor (coordinate_ne_zero P g hc)
          (RCN002.exists_transcendental_coordinate_of_ne_point_kernel Ω C.1 fun v => RCN264.PU Ω _ _ _ C v) q hq
      · intro C hC
        exact val_function_le P hp SZ ⟨g, C⟩ (S ⟨g, C⟩) (hS ⟨g, C⟩ (hact C hC))
          (htail ⟨g, C⟩ (hact C hC))
      · intro C hC q hq hf hL
        exact hp1 ⟨g, C⟩ (hact C hC) q (S ⟨g, C⟩) hq
          (hneeds.closure ⟨g, C⟩ (hact C hC) q hq hf hL)
  calc 3 * SZ.d * ∑ a ∈ active P SZ, multiplicity P hp a * baseOrder P Q A c S n a
      = ∑ a : Curve P, if a ∈ active P SZ then
          3 * SZ.d * multiplicity P hp a * curveBase (S a) (moving P Q A a.1) c n else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [baseOrder]; ring
    _ = ∑ g : RCN222.GeometricFactor K P.F, ∑ C ∈ Finset.univ.filter
          (fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ),
          3 * SZ.d * multiplicity P hp ⟨g, C⟩ * curveBase (S ⟨g, C⟩) (moving P Q A g) c n := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun g _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ g : RCN222.GeometricFactor K P.F, (n * baseNumber (moving P Q A g) c (function P SZ g) (flag SZ Hf) +
          componentLoss (moving P Q A g) c (function P SZ g) (flag SZ Hf)
            (Finset.univ.filter fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ)
            (fun C : CM (P.stage g) => S ⟨g, C⟩)
            (fun C => 3 * SZ.d * multiplicity P hp ⟨g, C⟩)) :=
        Finset.sum_le_sum fun g _ => hcomp g
    _ = n * lam P SZ Q A c (flag SZ Hf) + constant P hp SZ Q A c S (flag SZ Hf) := by
        rw [lam, constant, Finset.mul_sum, Finset.sum_add_distrib]
end
end Packet
end Exch
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Data
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN187
open RCN095 renaming PolynomialInFlag → BI
section Surface
noncomputable section
open scoped Classical
variable {E : Type} [Field E]
theorem zero_inFlag (W : FlagDegree) : RCN095.PolynomialInFlag W (0 : MvPolynomial (Fin 3) E) := fun d hd => by
  rw [support_zero] at hd
  exact absurd hd (Finset.notMem_empty d)
def pairs (E : Type) [Field E] :
    Submodule E (MvPolynomial (Fin 3) E × MvPolynomial (Fin 3) E) where
  carrier := {p | RCN095.PolynomialInFlag (2 • unitAllFlag) p.1 ∧ RCN095.PolynomialInFlag unitYZFlag p.2}
  add_mem' := fun hp hq =>
    ⟨fun d hd => (Finset.mem_union.mp (support_add hd)).elim (hp.1 d) (hq.1 d),
      fun d hd => (Finset.mem_union.mp (support_add hd)).elim (hp.2 d) (hq.2 d)⟩
  zero_mem' := ⟨zero_inFlag _, zero_inFlag _⟩
  smul_mem' := fun _ _ hp =>
    ⟨fun d hd => hp.1 d (support_smul hd), fun d hd => hp.2 d (support_smul hd)⟩
theorem X_inFlag (W : FlagDegree) (m : Fin 3) (h : InFlag W (Finsupp.single m 1)) :
    RCN095.PolynomialInFlag W (MvPolynomial.X m : MvPolynomial (Fin 3) E) := fun d hd => by
  rw [support_X, Finset.mem_singleton] at hd
  rw [hd]
  exact h
variable {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
def value (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (σ : RCN002.CoordinateField E G) :
    MvPolynomial (Fin 3) E × MvPolynomial (Fin 3) E →ₗ[E] RCN002.CoordinateField E G :=
  (RCN002.coordinateEvaluation E G).toLinearMap.coprod ((LinearMap.mulRight E σ).comp (RCN002.coordinateEvaluation E G).toLinearMap)
theorem value_apply (σ : RCN002.CoordinateField E G) (p : MvPolynomial (Fin 3) E × MvPolynomial (Fin 3) E) :
    value G σ p = RCN002.coordinateEvaluation E G p.1 + RCN002.coordinateEvaluation E G p.2 * σ :=
  rfl
def ball (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (T : ℤ) : Submodule E (RCN002.CoordinateField E G) where
  carrier := {z | ∀ a : E, nu (a • z) < exp T}
  add_mem' := fun hz hz' a => by
    rw [smul_add]
    exact (nu.map_add _ _).trans_lt (max_lt (hz a) (hz' a))
  zero_mem' := fun a => by
    rw [smul_zero, map_zero]
    exact exp_pos
  smul_mem' := fun b z hz a => by
    rw [smul_smul]
    exact hz (a * b)
def badSpace (σ : RCN002.CoordinateField E G) (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) : Submodule E (pairs E) :=
  (ball nu (placeTOn nu (coordinate E G) σ)).comap ((value G σ).comp (pairs E).subtype)
theorem val_eq_exp_poleOrder {L : Type*} [Field L] (nu : Valuation L ℤᵐ⁰) (z : L)
    (h : 0 < poleOrder nu z) : nu z = exp (poleOrder nu z) := by
  have hl : 0 < (nu z).log := by
    by_contra hn
    rw [poleOrder, max_eq_left (not_lt.mp hn)] at h
    exact lt_irrefl _ h
  have h0 : nu z ≠ 0 := fun h0 => by
    rw [h0, log_zero] at hl
    exact lt_irrefl _ hl
  rw [poleOrder, max_eq_right hl.le, exp_log h0]
theorem exists_witness (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (σ : RCN002.CoordinateField E G)
    (hT : 0 < placeTOn nu (coordinate E G) σ) :
    ∃ v ∈ pairs E, exp (placeTOn nu (coordinate E G) σ) ≤ nu (value G σ v) := by
  have hnn : ∀ z : RCN002.CoordinateField E G, 0 ≤ poleOrder nu z := fun z => le_max_left _ _
  have hall : ∀ m : Fin 3, RCN095.PolynomialInFlag unitAllFlag (MvPolynomial.X m : MvPolynomial (Fin 3) E) := fun m =>
    X_inFlag _ m (by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [Finsupp.single_apply, unitAllFlag] <;> split_ifs <;> omega)
  rw [placeTOn] at hT ⊢
  by_cases hcase : max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2)) +
      poleOrder nu σ ≤ 2 * max (poleOrder nu (coordinate E G 1))
        (max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2)))
  · rw [max_eq_left hcase] at hT ⊢
    obtain ⟨m, hm⟩ : ∃ m : Fin 3, poleOrder nu (coordinate E G m) =
        max (poleOrder nu (coordinate E G 1))
          (max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2))) := by
      rcases max_choice (poleOrder nu (coordinate E G 1))
        (max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2))) with h | h
      · exact ⟨1, h.symm⟩
      · rcases max_choice (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2))
          with h' | h'
        · exact ⟨0, by rw [h, h']⟩
        · exact ⟨2, by rw [h, h']⟩
    refine ⟨(MvPolynomial.X m * MvPolynomial.X m, 0), ⟨RCN207.inFlag_mul_poly (hall m) (hall m), zero_inFlag _⟩, ?_⟩
    rw [value_apply, map_zero, zero_mul, add_zero, map_mul, map_mul]
    show _ ≤ nu (coordinate E G m) * nu (coordinate E G m)
    rw [val_eq_exp_poleOrder nu _ (by omega), hm, ← exp_add, two_mul]
  · rw [max_eq_right (not_le.mp hcase).le] at hT ⊢
    have hs : 0 < poleOrder nu σ := by
      have h0 := hnn (coordinate E G 0)
      have h1 := hnn (coordinate E G 1)
      have h2 := hnn (coordinate E G 2)
      have hσ := hnn σ
      omega
    by_cases hβ : 0 < max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2))
    · obtain ⟨b, hb1, hb⟩ : ∃ b : Fin 3, b ≠ 1 ∧ poleOrder nu (coordinate E G b) =
          max (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2)) := by
        rcases max_choice (poleOrder nu (coordinate E G 0)) (poleOrder nu (coordinate E G 2))
          with h | h
        · exact ⟨0, by decide, h.symm⟩
        · exact ⟨2, by decide, h.symm⟩
      refine ⟨(0, MvPolynomial.X b), ⟨zero_inFlag _, X_inFlag _ b (by
        refine ⟨?_, ?_, ?_⟩ <;> simp only [Finsupp.single_apply, unitYZFlag] <;> split_ifs <;>
          omega)⟩, ?_⟩
      rw [value_apply, map_zero, zero_add, map_mul]
      show _ ≤ nu (coordinate E G b) * nu σ
      rw [val_eq_exp_poleOrder nu _ (by omega), val_eq_exp_poleOrder nu σ hs, hb, ← exp_add]
    · refine ⟨(0, 1), ⟨zero_inFlag _, RCN207.inFlag_const _ 1⟩, ?_⟩
      rw [value_apply, map_zero, zero_add, map_one, one_mul, val_eq_exp_poleOrder nu σ hs]
      refine exp_le_exp.mpr ?_
      have h0 := hnn (coordinate E G 0)
      have h2 := hnn (coordinate E G 2)
      omega
variable {N p : ℕ} [CharP E p]
theorem finite_pole (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (hc : ∀ j, coordinate E G j ≠ 0) (σ : RCN002.CoordinateField E G) :
    {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
      0 < placeTOn nu (coordinate E G) σ}.Finite := by
  have hpos : ∀ (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (z : RCN002.CoordinateField E G), 0 < poleOrder nu z →
      z ≠ 0 ∧ nu z ≠ 1 := fun nu z h => by
    have hz := val_eq_exp_poleOrder nu z h
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · rw [h0, map_zero] at hz
      exact exp_ne_zero hz.symm
    · rw [h1, ← exp_zero] at hz
      exact h.ne (exp_injective hz)
  refine ((Set.finite_iUnion fun j =>
    finite_surfaceDivisor_ne_one hN hp (coordinate E G j) (hc j)).union
    (show {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
      σ ≠ 0 ∧ nu σ ≠ 1}.Finite from ?_)).subset ?_
  · by_cases hσ : σ = 0
    · exact Set.finite_empty.subset fun nu h => (h.2.1 hσ).elim
    · exact (finite_surfaceDivisor_ne_one hN hp σ hσ).subset fun nu h => ⟨h.1, h.2.2⟩
  · rintro nu ⟨hsd, hT⟩
    have h4 : (∃ j, 0 < poleOrder nu (coordinate E G j)) ∨ 0 < poleOrder nu σ := by
      by_contra hno
      rw [not_or, not_exists] at hno
      have h0 := hno.1 0
      have h1 := hno.1 1
      have h2 := hno.1 2
      have hσ := hno.2
      rw [placeTOn] at hT
      omega
    rcases h4 with ⟨j, hj⟩ | hσ
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j, hsd, (hpos nu _ hj).2⟩)
    · exact Or.inr ⟨hsd, hpos nu σ hσ⟩
theorem exists_pole_subspaces (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (hc : ∀ j, coordinate E G j ≠ 0) (σ : RCN002.CoordinateField E G) :
    ∃ s : Finset (Submodule E (pairs E)), ⊤ ∉ s ∧ ∀ v : pairs E, (∀ W ∈ s, v ∉ W) →
      ∀ (sR sY sZ : Bool) (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰), SurfaceDivisor G sR sY sZ nu →
        placeTOn nu (coordinate E G) σ ≤ poleOrder nu (value G σ v) := by
  have hfin := finite_pole hN hp hc σ
  refine ⟨hfin.toFinset.image (badSpace σ), fun htop => ?_, fun v hv sR sY sZ nu hnu => ?_⟩
  · obtain ⟨nu, hnu, heq⟩ := Finset.mem_image.mp htop
    obtain ⟨v, hv, hle⟩ := exists_witness nu σ (hfin.mem_toFinset.mp hnu).2
    have hmem : (⟨v, hv⟩ : pairs E) ∈ badSpace σ nu := heq ▸ Submodule.mem_top
    exact absurd (hmem 1) (by rw [one_smul]; exact not_lt.mpr hle)
  · by_cases hT : 0 < placeTOn nu (coordinate E G) σ
    · have hmem := hv _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr ⟨⟨sR, sY, sZ, hnu⟩, hT⟩))
      have htriv : ∀ a : E, nu (algebraMap E (RCN002.CoordinateField E G) a) ≤ 1 := fun a => by
        by_cases ha : a = 0
        · rw [ha, map_zero, map_zero]
          exact zero_le_one
        · exact (Exch.SurfaceDivisor.trivial_on_constants hnu a ha).le
      have hle : exp (placeTOn nu (coordinate E G) σ) ≤ nu (value G σ v) :=
        not_lt.mp fun hlt => hmem fun a => by
          rw [Algebra.smul_def, map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (htriv a)) hlt
      have h0 : nu (value G σ v) ≠ 0 := fun h0 => by
        rw [h0] at hle
        exact absurd hle (not_le.mpr exp_pos)
      exact le_max_of_le_right ((le_log_iff_exp_le h0).mpr hle)
    · exact (not_lt.mp hT).trans (le_max_left _ _)
end
end Surface
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime Exch.fact_irreducible
theorem pair (P : Packet x t y r) (N : ℕ)
    (hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N) (hNp : 3 * N < 2130706433)
    (hc : ∀ j, sliceCoord P.F j ≠ 0) :
    ∃ Q A : MvPolynomial (Fin 3) Ω, RCN095.PolynomialInFlag (2 • unitAllFlag) Q ∧ RCN095.PolynomialInFlag unitYZFlag A ∧
      (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 ∧
      ∀ (g : RCN222.GeometricFactor K P.F) (sR sY sZ : Bool) (nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰),
        SurfaceDivisor (Exch.component P g) sR sY sZ nu →
          placeTOn nu (coordinate Ω (Exch.component P g))
            (RCN002.coordinateEvaluation Ω (Exch.component P g) (baseG P.F) / RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F)) ≤
            poleOrder nu (Exch.moving P Q A g) := by
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  choose s hs hsv using fun g : RCN222.GeometricFactor K P.F =>
    exists_pole_subspaces (hN g) hNp (Exch.coordinate_ne_zero P g hc)
      (RCN002.coordinateEvaluation Ω (Exch.component P g) (baseG P.F) / RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F))
  let A0 : Submodule Ω (pairs Ω) :=
    (LinearMap.ker (LinearMap.snd Ω (MvPolynomial (Fin 3) Ω) (MvPolynomial (Fin 3) Ω))).comap
      (pairs Ω).subtype
  have htop : ⊤ ∉ insert A0 (Finset.univ.biUnion s) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hmem : (⟨(0, 1), ⟨zero_inFlag _, RCN207.inFlag_const _ 1⟩⟩ : pairs Ω) ∈ A0 :=
        h ▸ Submodule.mem_top
      exact one_ne_zero (show (1 : MvPolynomial (Fin 3) Ω) = 0 from hmem)
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp h
      exact hs g hg
  obtain ⟨v, hv⟩ : ∃ v : pairs Ω, ∀ W ∈ insert A0 (Finset.univ.biUnion s), v ∉ W := by
    by_contra hall
    refine Subspace.biUnion_ne_univ_of_top_notMem htop (Set.eq_univ_of_forall fun v => ?_)
    by_contra hv
    exact hall ⟨v, fun W hW hvW => hv (Set.mem_biUnion hW hvW)⟩
  have h2 : (2 : Ω) ≠ 0 := fun h => by
    have h' := (CharP.cast_eq_zero_iff Ω 2130706433 2).mp (by exact_mod_cast h)
    omega
  refine ⟨v.1.1, v.1.2, v.2.1, v.2.2, ?_, fun g sR sY sZ nu hnu => ?_⟩
  · rw [two_mul, ← two_smul Ω]
    exact smul_ne_zero h2 fun h0 => hv A0 (Finset.mem_insert_self _ _) h0
  · have h := hsv g v (fun W hW => hv W (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hW⟩))) sR sY sZ nu hnu
    rwa [value_apply, ← mul_div_assoc] at h
end
end Packet
end Data
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Data
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
theorem finite_level_ne_one {N p : ℕ} [CharP E p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (f x : RCN002.CoordinateField E G) (hx : x ≠ 0) :
    {c : E | ∃ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
      nu (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 ∧ nu x ≠ 1}.Finite :=
  (finite_level_values _ (finite_surfaceDivisor_ne_one hN hp x hx)
    (fun _ hnu a ha => by
      obtain ⟨⟨sR, sY, sZ, hsd⟩, -⟩ := hnu
      exact Exch.SurfaceDivisor.trivial_on_constants hsd a ha) f).subset
    fun _ ⟨nu, h, hlt, hne⟩ => ⟨nu, ⟨h, hne⟩, hlt⟩
end Surface
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN086 RCN135 RCN136 RCN159 RCN222 RCN238 RCN243 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime Exch.fact_irreducible
theorem baseH_mem (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) (J : Ideal (MvPolynomial (Fin 3) Ω))
    (hg : (P.stage g).G ∈ J) (hd : pderiv 1 (P.stage g).G ∈ J) : baseH P.F ∈ J := by
  obtain ⟨h, hh⟩ := (P.stage g).RR
  rw [baseH, polyH, ← RCN267.surfaceMap_pderiv_R, show surfaceMap (RCN135.polynomialEmbedding K) P.F = (P.stage g).G * h from hh,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact J.add_mem (J.mul_mem_right _ hg) (J.mul_mem_left _ hd)
theorem baseH_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F) ≠ 0 := fun h =>
  (P.stage g).BLO (Ideal.mem_span_singleton.mp ((Sec.BR_eq_zero_iff _).mp h))
theorem pderiv_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RCN002.coordinateEvaluation Ω (Exch.component P g) (pderiv 1 (P.stage g).G) ≠ 0 := fun h =>
  baseH_ne_zero P g ((Sec.BR_eq_zero_iff _).mpr (baseH_mem P g _
    (Ideal.mem_span_singleton_self _) ((Sec.BR_eq_zero_iff _).mp h)))
theorem curves (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) :
    ∃ S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1),
      ∀ a : Curve P, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a) := by
  have h : ∀ a : Curve P, ∃ S : Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1),
      IsCurveOnSurface (Exch.component P a.1) a.2.1 S := fun a =>
    Sec.exists_curve (P.stage a.1).G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1)) (P.stage a.1).MW rfl
      (P.stage_proper hp a.1) a.2.1 (AAS Ω _ _ _ a.2) fun hd =>
        _Q6 Ω _ _ _ a.2 (baseH_mem P a.1 a.2.1 (EN Ω _ _ _ a.2) hd)
  exact ⟨fun a => (h a).choose, fun a => (h a).choose_spec⟩
theorem off_level (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1))
    (hS : ∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) :
    {c : Ω | ∃ a ∈ active P SZ, (S a).val (Exch.moving P Q A a.1 -
      algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) ≠ 1}.Finite := by
  refine (Set.Finite.biUnion (active P SZ).finite_toSet fun a ha =>
    (show {c : Ω | (S a).val (Exch.moving P Q A a.1 -
        algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) < 1}.Subsingleton from
      fun c hc c' hc' =>
        level_value_unique (S a).val (hS a ha).trivial_on_constants _ hc hc').finite).subset ?_
  rintro c ⟨a, ha, hne⟩
  refine Set.mem_biUnion ha (lt_of_le_of_ne (((S a).val.map_sub _ _).trans (max_le ?_ ?_)) hne)
  · exact (Valuation.mem_valuationSubring_iff _ _).mp
      ((hS a ha).res_movingValue (baseH P.F) (baseG P.F) Q A (_Q6 Ω _ _ _ a.2)).1
  · rw [← (RCN002.coordinateEvaluation Ω (Exch.component P a.1)).commutes c]
    exact Sec.curve_val_le_one (hS a ha) _
theorem seed (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) :
    {c : Ω | ∃ a ∈ active P SZ, ∃ γ ∈ RCN264.componentSeeds Ω (P.stage a.1).G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
      (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F) (KK K P.F P.selected P.seeds a.1)
      (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2,
      MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected γ)
        (baseH P.F * (Q - MvPolynomial.C c) + A * baseG P.F) = 0}.Finite := by
  refine (Set.Finite.biUnion (active P SZ).finite_toSet fun a _ =>
    Set.Finite.biUnion (Finset.finite_toSet _) fun γ hγ =>
      (show {c : Ω | MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected γ)
          (baseH P.F * (Q - MvPolynomial.C c) + A * baseG P.F) = 0}.Subsingleton from
        fun c hc c' hc' => ?_).finite).subset
    fun c ⟨a, ha, γ, hγ, h⟩ => Set.mem_biUnion ha (Set.mem_biUnion hγ h)
  have hH : MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected γ) (baseH P.F) ≠ 0 := by
    rw [baseH, polyH, WQ]
    exact (P.stage a.1).regular γ (RCN264.componentSeeds_subset Ω _ _ _ _ _ a.2 hγ)
  simp only [Set.mem_ofPred_eq, map_add, map_mul, map_sub, eval_C] at hc hc'
  exact (sub_eq_zero.mp ((mul_eq_zero.mp (show MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected γ)
    (baseH P.F) * (c' - c) = 0 by linear_combination hc - hc')).resolve_left hH)).symm
theorem component_ne (P : Packet x t y r) (Q A : MvPolynomial (Fin 3) Ω) :
    {c : Ω | ∃ g, Exch.moving P Q A g = algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c}.Finite :=
  (Set.finite_iUnion fun g : RCN222.GeometricFactor K P.F =>
    (show {c : Ω | Exch.moving P Q A g =
        algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c}.Subsingleton from
      fun _ hc _ hc' => (algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g))).injective
        (hc.symm.trans hc')).finite).subset fun _ ⟨g, hg⟩ => Set.mem_iUnion.mpr ⟨g, hg⟩
theorem component_unit (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (N : ℕ)
    (hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N) (hNp : 3 * N < 2130706433)
    (hc : ∀ j, sliceCoord P.F j ≠ 0) (htail : tail P.F P.F (dvd_refl P.F) w ≠ 0)
    (hlead : srcLead P.F P.F SZ ≠ 0) (Q A : MvPolynomial (Fin 3) Ω) :
    {c : Ω | ∃ (g : RCN222.GeometricFactor K P.F) (nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰),
      (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
      nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
      ¬((∀ j, nu (coordinate Ω (Exch.component P g) j) = 1) ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (pderiv 1 (P.stage g).G)) = 1 ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F)) = 1 ∧ nu (Exch.function P SZ g) = 1)}.Finite := by
  have hfin : ∀ (g : RCN222.GeometricFactor K P.F) (z : RCN002.CoordinateField Ω (Exch.component P g)), z ≠ 0 →
      {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu z ≠ 1}.Finite := fun g z hz => finite_level_ne_one (hN g) hNp _ z hz
  have hA : ∀ g, Exch.function P SZ g ≠ 0 := fun g =>
    Exch.function_ne_zero P SZ g htail (fun h0 => baseH_ne_zero P g (by
      rw [baseH, ← Exch.embedding_sliceProj, h0, map_zero])) hlead
  refine (Set.finite_iUnion fun g : RCN222.GeometricFactor K P.F =>
    ((Set.finite_iUnion fun j => hfin g _ (Exch.coordinate_ne_zero P g hc j)).union
      (hfin g _ (pderiv_ne_zero P g))).union
      ((hfin g _ (baseH_ne_zero P g)).union (hfin g _ (hA g)))).subset ?_
  rintro c ⟨g, nu, hnu, hlt, hbad⟩
  refine Set.mem_iUnion.mpr ⟨g, ?_⟩
  by_contra hno
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and,
    not_not] at hno
  exact hbad ⟨fun j => hno.1.1 j nu hnu hlt, hno.1.2 nu hnu hlt, hno.2.1 nu hnu hlt,
    hno.2.2 nu hnu hlt⟩
end
end Packet
end Data
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace LevelCount
section Flag
open RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
theorem flagPole_eq_units {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (W : FlagDegree) :
    flagPole v x W = (W.zOnly : ℤ) * flagPole v x unitZFlag + (W.yz : ℤ) * flagPole v x unitYZFlag +
      (W.all : ℤ) * flagPole v x unitAllFlag := by
  simp only [flagPole, unitZFlag, unitYZFlag, unitAllFlag, Nat.cast_one, Nat.cast_zero, one_mul,
    zero_mul, add_zero, zero_add]
theorem levelCut_flag {E : Type*} [Field E] {a b s : ℕ} {H Gs Q A : MvPolynomial (Fin 3) E}
    (hH : RCN095.PolynomialInFlag ⟨a, b + 1, s + 1⟩ H) (hGs : RCN095.PolynomialInFlag ⟨a, b, s + 3⟩ Gs) (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : RCN095.PolynomialInFlag unitYZFlag A) (c : E) : RCN095.PolynomialInFlag ⟨a, b + 1, s + 3⟩ (RCN207.movingEquation H Gs Q A c) := by
  have h1 : RCN095.PolynomialInFlag (⟨a, b + 1, s + 1⟩ + 2 • unitAllFlag) (H * (MvPolynomial.C c - Q)) :=
    RCN207.inFlag_mul_poly hH (RCN207.inFlag_sub_poly (RCN207.inFlag_const _ c) hQ)
  have h2 : RCN095.PolynomialInFlag (⟨a, b, s + 3⟩ + unitYZFlag) (Gs * A) := RCN207.inFlag_mul_poly hGs hA
  rw [RCN207.movingEquation, mul_comm A Gs]
  exact RCN207.inFlag_sub_poly h1 h2
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] LevelComponent.isPrime
theorem levelFlagSum_eq_units {f : RCN002.CoordinateField E G} {c : E} (s : Finset (LevelComponent G f c))
    (T : ∀ B : LevelComponent G f c, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))) (W : FlagDegree) :
    levelFlagSum s T W = (W.zOnly : ℤ) * levelFlagSum s T unitZFlag +
      (W.yz : ℤ) * levelFlagSum s T unitYZFlag + (W.all : ℤ) * levelFlagSum s T unitAllFlag := by
  simp only [levelFlagSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun v _ => ?_
  rw [flagPole_eq_units v.val (coordinate E B.prime) W]
  ring
end Flag
section Packet
noncomputable section
open scoped Classical BigOperators
open WithZero
open RCN002 RCN074 RCN095 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open DU BD AFA RL BOE HFree6812 FA
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime Exch.fact_irreducible
theorem baseH_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F) ≠ 0 := fun h =>
  (P.stage g).BLO (Ideal.mem_span_singleton.mp ((LevelSurf.BR_eq_zero_iff _ _).mp h))
theorem separable (P : Packet x t y r) (Q A : MvPolynomial (Fin 3) Ω) (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : RCN095.PolynomialInFlag unitYZFlag A) (c : Ω) (g : RCN222.GeometricFactor K P.F)
    (hne : Exch.moving P Q A g ≠ algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c)
    (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c) :
    Nonempty (RCN341.SeparableLiteralCoordinate B.prime) := by
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  have hthi := packet_t_le P
  obtain ⟨hHf, hGf⟩ := RCN201.DGW (RCN135.polynomialEmbedding K) (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) P.F P.support.IZ.2.1
    P.support.ys_weight P.support.total_weight
  have hT := levelCut_flag hHf hGf hQ hA c
  refine nonempty_separable_levelComponent (p := 2130706433) rfl (P.stage g).MW
    (Gs := baseG P.F) (Q := Q) (A := A) (baseH_ne_zero P g) hne (surfaceMap (RCN135.polynomialEmbedding K) P.F)
    (RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero) (P.stage g).RR ⟨t - y, y - r, r⟩ _
    (P.parent_flag Ω (RCN135.polynomialEmbedding K)) hT ?_ ?_ B
  · show t - y + (y - r) + r < 2130706433
    omega
  · show 2 * (t - y + (y - r) + r) * (LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3)) < 2130706433
    have h1 : t - y + (y - r) + r = t := by omega
    have h2 : LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3) = t + 1 := by
      simp only [LocatorHybridCells.cellA, LocatorHybridCells.cellB, LocatorHybridCells.cellS]
      omega
    rw [h1, h2]
    nlinarith
theorem level_count_price (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (scale z u v : ℕ) (Hf : FlagDegree) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1))
    (hS : ∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a))
    (hneeds : LevelNeeds P SZ Q A c S) (hsec : SectionBound P scale z u v Q A c)
    (hc : ∀ j, sliceCoord P.F j ≠ 0)
    (hI : ∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ)
    (N : ℕ) (hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (hNp : 3 * N < 2130706433) (htail : Exch.TailOrder P hp SZ S)
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A) :
    3 * SZ.d * scale * (∑ a ∈ active P SZ, multiplicity P hp a *
        curveMoving (S a) (Exch.moving P Q A a.1) c) +
      scale * Exch.lam P SZ Q A c (Exch.flag SZ Hf) ≤ price (Exch.flag SZ Hf) z u v := by
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  let live : ∀ g : RCN222.GeometricFactor K P.F, Finset (CM (P.stage g)) := fun g =>
    Finset.univ.filter fun C => SZ.leading (RCN135.polynomialEmbedding K) ∉ C.1
  have hmem : ∀ (g : RCN222.GeometricFactor K P.F) (C : CM (P.stage g)), C ∈ live g → (⟨g, C⟩ : Curve P) ∈ active P SZ :=
    fun g C hC => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hC).2⟩
  have hcomp : ∀ g : RCN222.GeometricFactor K P.F, ∃ (s : Finset (LevelComponent (Exch.component P g)
      (Exch.moving P Q A g) c)) (T : ∀ B : LevelComponent (Exch.component P g)
        (Exch.moving P Q A g) c, Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω B.prime))),
      ((∑ C ∈ live g, 3 * SZ.d * multiplicity P hp ⟨g, C⟩ *
          curveMoving (S ⟨g, C⟩) (Exch.moving P Q A g) c +
        baseNumber (Exch.moving P Q A g) c (Exch.function P SZ g) (Exch.flag SZ Hf) : ℕ) : ℤ) ≤
        levelFlagSum s T (Exch.flag SZ Hf) := by
    intro g
    have M : Setup (Exch.component P g) N 2130706433 (P.stage g).G (baseH P.F)
        (Exch.moving P Q A g) c (Exch.function P SZ g) (Exch.flag SZ Hf) :=
      { algClosed := inferInstance
        charP := hchar
        noether := hN g
        char := hNp
        coord := Exch.coordinate_ne_zero P g hc
        irreducible := (P.stage g).MW
        span := rfl
        needs := hneeds.component g
        regular := Exch.localFunction_function_mem P SZ Hf hI g
        sep := separable P Q A hQ hA c g (hneeds.component g).ne
        closure := hneeds.levelClosure g }
    exact component_count M (live g) (fun C => S ⟨g, C⟩)
      (fun C hC => hS ⟨g, C⟩ (hmem g C hC))
      (fun C _ => RCN002.exists_transcendental_coordinate_of_ne_point_kernel Ω C.1 fun pt => PU Ω _ _ _ C pt)
      (fun C _ C' _ h => Subtype.ext h)
      (fun C hC => hneeds.live ⟨g, C⟩ (hmem g C hC))
      (fun C => 3 * SZ.d * multiplicity P hp ⟨g, C⟩)
      (fun C hC => Exch.val_function_le P hp SZ ⟨g, C⟩ (S ⟨g, C⟩) (hS ⟨g, C⟩ (hmem g C hC))
        (htail ⟨g, C⟩ (hmem g C hC)))
      (fun C hC => hneeds.closure ⟨g, C⟩ (hmem g C hC))
  choose s T hsT using hcomp
  obtain ⟨hz, hu, hv⟩ := hsec s T
  have hsum : ∑ a ∈ active P SZ, multiplicity P hp a *
      curveMoving (S a) (Exch.moving P Q A a.1) c =
      ∑ g, ∑ C ∈ live g, multiplicity P hp ⟨g, C⟩ *
        curveMoving (S ⟨g, C⟩) (Exch.moving P Q A g) c := by
    simp only [live, active, Finset.sum_filter]
    rw [Fintype.sum_sigma]
  have htotal : ((3 * SZ.d * scale * (∑ a ∈ active P SZ, multiplicity P hp a *
        curveMoving (S a) (Exch.moving P Q A a.1) c) +
      scale * Exch.lam P SZ Q A c (Exch.flag SZ Hf) : ℕ) : ℤ) ≤
      (scale : ℤ) * ∑ g, levelFlagSum (s g) (T g) (Exch.flag SZ Hf) := by
    have h1 : 3 * SZ.d * scale * (∑ a ∈ active P SZ, multiplicity P hp a *
          curveMoving (S a) (Exch.moving P Q A a.1) c) +
        scale * Exch.lam P SZ Q A c (Exch.flag SZ Hf) =
        scale * ∑ g, (∑ C ∈ live g, 3 * SZ.d * multiplicity P hp ⟨g, C⟩ *
            curveMoving (S ⟨g, C⟩) (Exch.moving P Q A g) c +
          baseNumber (Exch.moving P Q A g) c (Exch.function P SZ g) (Exch.flag SZ Hf)) := by
      rw [hsum, Exch.lam, Finset.sum_add_distrib, Nat.mul_add]
      congr 1
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun C _ => ?_
      ring
    rw [h1, Nat.cast_mul, Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hsT g) (Int.natCast_nonneg _)
  have hlin : (scale : ℤ) * ∑ g, levelFlagSum (s g) (T g) (Exch.flag SZ Hf) ≤
      ((price (Exch.flag SZ Hf) z u v : ℕ) : ℤ) := by
    simp only [levelFlagSum_eq_units _ _ (Exch.flag SZ Hf), Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [price]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg (Exch.flag SZ Hf).zOnly),
      mul_le_mul_of_nonneg_left hu (Int.natCast_nonneg (Exch.flag SZ Hf).yz),
      mul_le_mul_of_nonneg_left hv (Int.natCast_nonneg (Exch.flag SZ Hf).all)]
  exact Int.ofNat_le.mp (htotal.trans hlin)
end
end Packet
end LevelCount
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Exch
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] component_isPrime fact_irreducible SurfacePoint.isNoetherianRing
  SurfacePoint.isIntegrallyClosed SurfacePoint.isFractionRing
theorem tail_ne_zero (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) :
    tail P.F P.F (dvd_refl P.F) w ≠ 0 := by
  have hH := Chart.packet_polyH_ne_zero P
  rw [show w = w - 1 + 1 from rfl, tail,
    show sliceCoord P.F 1 = sliceProj P.F (MvPolynomial.X 2) from rfl,
    HFree6812.sliceDerivation_iterate P.F P.F (dvd_refl P.F) hH (w - 1)]
  exact div_ne_zero (fun h => hp (by
    rw [show w + 1 = w - 1 + 2 from rfl, RCN055.numerator_eq_H_cube]
    exact ((HFree6812.sliceProj_eq_zero_iff P.F _).1 h).mul_left _)) (pow_ne_zero _ hH)
end
end Packet
end Exch
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace SecChoice
open WithZero MvPolynomial
open RCN002 RCN095 RCN187
open RCN095 renaming PolynomialInFlag → BI
section Pencil
noncomputable section
open scoped Classical
variable {E : Type} [Field E]
local notation "Poly" => MvPolynomial (Fin 3) E
theorem exists_notMem_of_top_notMem [Infinite E] {V : Type*} [AddCommGroup V] [Module E V]
    (S : Finset (Submodule E V)) (hS : ⊤ ∉ S) : ∃ b : V, ∀ U ∈ S, b ∉ U := by
  by_contra hall
  refine Subspace.biUnion_ne_univ_of_top_notMem hS (Set.eq_univ_of_forall fun b => ?_)
  by_contra hb
  exact hall ⟨b, fun U hU hbU => hb (Set.mem_biUnion hU hbU)⟩
def mask (J : Finset (Fin 3)) : (Fin 3 → E) →ₗ[E] (Fin 3 → E) where
  toFun b m := if m ∈ J then b m else 0
  map_add' b b' := by
    funext m
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · rw [add_zero]
  map_smul' a b := by
    funext m
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs
    · rfl
    · rw [mul_zero]
theorem mask_apply (J : Finset (Fin 3)) (b : Fin 3 → E) (m : Fin 3) :
    mask J b m = if m ∈ J then b m else 0 :=
  rfl
theorem mask_of_mem {J : Finset (Fin 3)} (b : Fin 3 → E) {m : Fin 3} (hm : m ∈ J) :
    mask J b m = b m := by
  simp only [mask_apply, hm, ↓reduceIte]
theorem mem_of_mask_ne_zero {J : Finset (Fin 3)} {b : Fin 3 → E} {m : Fin 3} (h : mask J b m ≠ 0) :
    m ∈ J := by
  by_contra hm
  exact h (by simp only [mask_apply, hm, ↓reduceIte])
theorem mask_single {J : Finset (Fin 3)} {m : Fin 3} (hm : m ∈ J) :
    mask J (Pi.single m (1 : E)) = Pi.single m 1 := by
  funext k
  rw [mask_apply]
  split_ifs with hk
  · rfl
  · rw [Pi.single_eq_of_ne fun h : k = m => hk (h ▸ hm)]
structure FlagCoords (W : FlagDegree) (J : Finset (Fin 3)) : Prop where
  two : 2 ∈ J
  zero : 0 ∈ J → 1 ≤ W.yz + W.all
  one : 1 ∈ J → 1 ≤ W.all
  sum : 1 ≤ W.zOnly + W.yz + W.all
  pole : ∀ z : Fin 3 → ℤ, ∃ m ∈ J, (W.zOnly : ℤ) * z 2 + (W.yz : ℤ) * max (z 0) (z 2) +
    (W.all : ℤ) * max (z 1) (max (z 0) (z 2)) ≤ z m
theorem flagCoords_z : FlagCoords unitZFlag {2} where
  two := by decide
  zero h := absurd h (by decide)
  one h := absurd h (by decide)
  sum := by simp [unitZFlag]
  pole z := ⟨2, by decide, by simp [unitZFlag]⟩
theorem flagCoords_yz : FlagCoords unitYZFlag {0, 2} where
  two := by decide
  zero _ := by simp [unitYZFlag]
  one h := absurd h (by decide)
  sum := by simp [unitYZFlag]
  pole z := by
    rcases le_total (z 0) (z 2) with h | h
    · exact ⟨2, by decide, by simp [unitYZFlag, h]⟩
    · exact ⟨0, by decide, by simp [unitYZFlag, h]⟩
theorem flagCoords_all : FlagCoords unitAllFlag Finset.univ where
  two := Finset.mem_univ _
  zero _ := by simp [unitAllFlag]
  one _ := by simp [unitAllFlag]
  sum := by simp [unitAllFlag]
  pole z := by
    have key : max (z 1) (max (z 0) (z 2)) ≤ z 0 ∨ max (z 1) (max (z 0) (z 2)) ≤ z 1 ∨
        max (z 1) (max (z 0) (z 2)) ≤ z 2 := by omega
    rcases key with h | h | h
    · exact ⟨0, Finset.mem_univ _, by simpa [unitAllFlag] using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [unitAllFlag] using h⟩
    · exact ⟨2, Finset.mem_univ _, by simpa [unitAllFlag] using h⟩
theorem linearForm_mask_inFlag {W : FlagDegree} {J : Finset (Fin 3)} (hWJ : FlagCoords W J)
    (b : Fin 3 → E) (a : E) : RCN095.PolynomialInFlag W (Sec.linearForm (mask J b) - C a) :=
  Sec.linearForm_sub_C_inFlag W _ a (fun h => hWJ.zero (mem_of_mask_ne_zero h))
    (fun h => hWJ.one (mem_of_mask_ne_zero h)) fun _ => hWJ.sum
def minor (g : Poly) : (Fin 3 → E) →ₗ[E] Poly where
  toFun b := Sec.linearMinor b 2 1 g
  map_add' b b' := by
    simp only [Sec.linearMinor, Pi.add_apply, map_add]
    ring
  map_smul' a b := by
    simp only [Sec.linearMinor, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring
def minorSpace (J : Finset (Fin 3)) (g : Poly) : Submodule E (Fin 3 → E) :=
  ((Ideal.span ({g} : Set Poly)).restrictScalars E).comap ((minor g).comp (mask J))
theorem mem_minorSpace (J : Finset (Fin 3)) (g : Poly) (b : Fin 3 → E) :
    b ∈ minorSpace J g ↔ g ∣ Sec.linearMinor (mask J b) 2 1 g := by
  rw [minorSpace, Submodule.mem_comap, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  rfl
theorem minorSpace_ne_top {J : Finset (Fin 3)} (h2 : 2 ∈ J) (g : Poly) (hg : ¬g ∣ pderiv 1 g) :
    minorSpace J g ≠ ⊤ := by
  intro htop
  have hmem : (Pi.single 2 (1 : E) : Fin 3 → E) ∈ minorSpace J g := htop ▸ Submodule.mem_top
  rw [mem_minorSpace, mask_single h2, Sec.linearMinor, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), C_1, C_0, one_mul, zero_mul, sub_zero] at hmem
  exact hg hmem
variable {I : Ideal (MvPolynomial (Fin 3) E)} [I.IsPrime]
omit [I.IsPrime] in
theorem BR_linearForm (b : Fin 3 → E) :
    RCN002.coordinateEvaluation E I (Sec.linearForm b) = Fintype.linearCombination E (coordinate E I) b := by
  rw [Sec.linearForm, map_sum, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, algHom_C, Algebra.smul_def]
  rfl
def poleMax (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) : ℤ :=
  J.fold max 0 fun m => poleOrder v.val (coordinate E I m)
theorem poleOrder_le_poleMax (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) {m : Fin 3}
    (hm : m ∈ J) : poleOrder v.val (coordinate E I m) ≤ poleMax J v :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨m, hm, le_rfl⟩)
theorem exists_poleMax_le (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (h : 0 < poleMax J v) :
    ∃ m ∈ J, poleMax J v ≤ poleOrder v.val (coordinate E I m) := by
  rcases (Finset.le_fold_max _).mp (le_refl (poleMax J v)) with h0 | h1
  · exact absurd h0 (not_le.mpr h)
  · exact h1
def poleSpace (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) : Submodule E (Fin 3 → E) :=
  (Data.ball v.val (poleMax J v)).comap ((Fintype.linearCombination E (coordinate E I)).comp (mask J))
theorem mem_poleSpace (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (b : Fin 3 → E) :
    b ∈ poleSpace J v ↔
      ∀ a : E, v.val (a • RCN002.coordinateEvaluation E I (Sec.linearForm (mask J b))) < exp (poleMax J v) := by
  rw [BR_linearForm]
  exact Iff.rfl
theorem poleSpace_ne_top (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (h : 0 < poleMax J v) :
    poleSpace J v ≠ ⊤ := by
  intro htop
  obtain ⟨m, hm, hle⟩ := exists_poleMax_le J v h
  have hmem : (Pi.single m (1 : E) : Fin 3 → E) ∈ poleSpace J v := htop ▸ Submodule.mem_top
  have h1 := (mem_poleSpace J v _).mp hmem 1
  rw [one_smul, mask_single hm, BR_linearForm, Fintype.linearCombination_apply_single, one_smul,
    Data.val_eq_exp_poleOrder v.val _ (lt_of_lt_of_le h hle)] at h1
  exact absurd (exp_lt_exp.mp h1) (not_lt.mpr hle)
theorem pole_of_notMem (J : Finset (Fin 3)) (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (b : Fin 3 → E)
    (hb : 0 < poleMax J v → b ∉ poleSpace J v) (a : E) {m : Fin 3} (hm : m ∈ J) :
    poleOrder v.val (coordinate E I m) ≤
      poleOrder v.val (RCN002.coordinateEvaluation E I (Sec.linearForm (mask J b) - C a)) := by
  refine (poleOrder_le_poleMax J v hm).trans ?_
  by_cases hT : 0 < poleMax J v
  · have hnot := hb hT
    rw [mem_poleSpace, not_forall] at hnot
    obtain ⟨a', ha'⟩ := hnot
    have hle : exp (poleMax J v) ≤ v.val (RCN002.coordinateEvaluation E I (Sec.linearForm (mask J b))) := by
      refine (not_lt.mp ha').trans ?_
      rw [Algebra.smul_def, map_mul]
      exact mul_le_of_le_one_left' (RCN344.NP E (RCN002.CoordinateField E I) v a')
    have hlt : v.val (RCN002.coordinateEvaluation E I (C a)) < v.val (RCN002.coordinateEvaluation E I (Sec.linearForm (mask J b))) := by
      rw [algHom_C]
      refine lt_of_le_of_lt (RCN344.NP E (RCN002.CoordinateField E I) v a) (lt_of_lt_of_le ?_ hle)
      rw [← exp_zero]
      exact exp_lt_exp.mpr hT
    have h0 : v.val (RCN002.coordinateEvaluation E I (Sec.linearForm (mask J b))) ≠ 0 := fun h0 => by
      rw [h0] at hle
      exact absurd hle (not_le.mpr exp_pos)
    rw [map_sub, poleOrder, Valuation.map_sub_eq_of_lt_left _ hlt]
    exact le_max_of_le_right ((le_log_iff_exp_le h0).mpr hle)
  · exact (not_lt.mp hT).trans (le_max_left _ _)
theorem subsingleton_mem (ℓ : Poly) : {a : E | ℓ - C a ∈ I}.Subsingleton := by
  intro a ha a' ha'
  by_contra hne
  have hmem : (C (a' - a) : Poly) ∈ I := by
    have h := I.sub_mem ha ha'
    rwa [sub_sub_sub_cancel_left, ← map_sub] at h
  exact (‹I.IsPrime›).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map C))
theorem subsingleton_val_lt_one (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (ℓ : Poly) :
    {a : E | v.val (RCN002.coordinateEvaluation E I (ℓ - C a)) < 1}.Subsingleton := by
  intro a ha a' ha'
  by_contra hne
  have h := Valuation.map_sub_lt v.val ha ha'
  rw [← map_sub, sub_sub_sub_cancel_left, ← map_sub, algHom_C,
    v.property.2.eq_one _ (sub_ne_zero.mpr (Ne.symm hne))] at h
  exact lt_irrefl _ h
variable [IsAlgClosed E]
theorem finite_val_ne_one (sep : RCN341.SeparableLiteralCoordinate I) (x : RCN002.CoordinateField E I) (hx : x ≠ 0) :
    {v : RCN026.Place_p19 E (RCN002.CoordinateField E I) | v.val x ≠ 1}.Finite := by
  obtain ⟨V, hV⟩ := Sec.exists_zero_places I sep x
  obtain ⟨V', hV'⟩ := Sec.exists_zero_places I sep x⁻¹
  have key : ∀ (v : RCN026.Place_p19 E (RCN002.CoordinateField E I)) (y : RCN002.CoordinateField E I), y ≠ 0 → v.val y < 1 →
      (RCN026.order_p19 E (RCN002.CoordinateField E I) v y).toNat ≠ 0 := by
    intro v y hy hlt
    have h0 : v.val y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    have hlog : (v.val y).log < 0 := (log_lt_iff_lt_exp h0).mpr (by rwa [exp_zero])
    rw [RCN026.order_p19]
    omega
  refine (V ∪ V').finite_toSet.subset fun v hv => ?_
  rcases lt_or_gt_of_ne hv with h | h
  · exact Finset.mem_coe.mpr (Finset.mem_union_left _ (hV v (key v x hx h)))
  · refine Finset.mem_coe.mpr (Finset.mem_union_right _ (hV' v (key v x⁻¹ (inv_ne_zero hx) ?_)))
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h
theorem finite_pole (sep : RCN341.SeparableLiteralCoordinate I) :
    {v : RCN026.Place_p19 E (RCN002.CoordinateField E I) | ∃ m, 1 < v.val (coordinate E I m)}.Finite := by
  refine (Set.finite_iUnion fun m : Fin 3 =>
    (show {v : RCN026.Place_p19 E (RCN002.CoordinateField E I) | 1 < v.val (coordinate E I m)}.Finite from ?_)).subset
      fun v ⟨m, hm⟩ => Set.mem_iUnion.mpr ⟨m, hm⟩
  by_cases h0 : coordinate E I m = 0
  · refine Set.finite_empty.subset fun v h => ?_
    rw [Set.mem_ofPred_eq, h0, map_zero] at h
    exact absurd h (not_lt.mpr zero_le_one)
  · exact (finite_val_ne_one sep _ h0).subset fun v h => ne_of_gt h
end
end Pencil
section Level
noncomputable section
open scoped Classical
variable {E : Type} [Field E] [IsAlgClosed E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
local notation "Poly" => MvPolynomial (Fin 3) E
attribute [local instance] LevelComponent.isPrime
theorem finite_levelComponent {N p : ℕ} [CharP E p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (hc : ∀ j, coordinate E G j ≠ 0) (f : RCN002.CoordinateField E G) (c : E)
    (hne : f ≠ algebraMap E (RCN002.CoordinateField E G) c) : Finite (LevelComponent G f c) := by
  have hfin := finite_surfaceDivisor_ne_one hN hp (f - algebraMap E (RCN002.CoordinateField E G) c) (sub_ne_zero.mpr hne)
  have := hfin.to_subtype
  have hle : ∀ B : LevelComponent G f c,
      ∀ i, B.curve.val (lmono (coordinate E G) (chartExp false false false i)) ≤ 1 := by
    intro B i
    fin_cases i <;> simp [lmono, chartExp] <;> exact LevelSurf.val_le_one B.isCurve (MvPolynomial.X _)
  refine Finite.of_injective (fun B : LevelComponent G f c =>
    (⟨B.val, ⟨_, _, _, B.curve_val ▸ B.isCurve.surfaceDivisor hc B.exists_transcendental
      false false false (hle B)⟩, B.val_lt_one.ne⟩ :
      {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
        nu (f - algebraMap E (RCN002.CoordinateField E G) c) ≠ 1})) ?_
  intro B B' h
  exact Subtype.ext (Subtype.mk.inj h)
variable (f : RCN002.CoordinateField E G) (c : E) (hfin : Finite (LevelComponent G f c))
  (hsep : ∀ B : LevelComponent G f c, Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
include hfin hsep
theorem exists_pole_subspaces (J : Finset (Fin 3)) :
    ∃ S : Finset (Submodule E (Fin 3 → E)), ⊤ ∉ S ∧ ∀ b : Fin 3 → E, (∀ U ∈ S, b ∉ U) →
      ∀ (B : LevelComponent G f c) (v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)) (a : E), ∀ m ∈ J,
        poleOrder v.val (coordinate E B.prime m) ≤
          poleOrder v.val (RCN002.coordinateEvaluation E B.prime (Sec.linearForm (mask J b) - C a)) := by
  have := Fintype.ofFinite (LevelComponent G f c)
  have hpole : ∀ B : LevelComponent G f c,
      {v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime) | 0 < poleMax J v}.Finite := by
    intro B
    obtain ⟨sep⟩ := hsep B
    refine (finite_pole sep).subset fun v hv => ?_
    obtain ⟨m, -, hle⟩ := exists_poleMax_le J v hv
    have hpos : 0 < poleOrder v.val (coordinate E B.prime m) := lt_of_lt_of_le hv hle
    refine ⟨m, ?_⟩
    rw [Data.val_eq_exp_poleOrder v.val _ hpos, ← exp_zero]
    exact exp_lt_exp.mpr hpos
  refine ⟨Finset.univ.biUnion fun B => (hpole B).toFinset.image (poleSpace J), fun htop => ?_,
    fun b hb B v a m hm => ?_⟩
  · obtain ⟨B, -, hB⟩ := Finset.mem_biUnion.mp htop
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hB
    exact poleSpace_ne_top J v ((hpole B).mem_toFinset.mp hv) heq
  · exact pole_of_notMem J v b (fun hT => hb _ (Finset.mem_biUnion.mpr ⟨B, Finset.mem_univ B,
      Finset.mem_image_of_mem _ ((hpole B).mem_toFinset.mpr hT)⟩)) a hm
theorem finite_constants (H : Poly) (hH : ∀ B : LevelComponent G f c, H ∉ B.prime) (ℓ : Poly) :
    {a : E | ¬∀ B : LevelComponent G f c, RCN002.coordinateEvaluation E B.prime (ℓ - C a) ≠ 0 ∧
      ∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime), v.val (RCN002.coordinateEvaluation E B.prime (ℓ - C a)) < 1 →
        (∀ i, v.val (coordinate E B.prime i) ≤ 1) ∧ v.val (RCN002.coordinateEvaluation E B.prime H) = 1}.Finite := by
  have hbad : ∀ B : LevelComponent G f c, {v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime) |
      ¬((∀ i, v.val (coordinate E B.prime i) ≤ 1) ∧ v.val (RCN002.coordinateEvaluation E B.prime H) = 1)}.Finite := by
    intro B
    obtain ⟨sep⟩ := hsep B
    have hH0 : RCN002.coordinateEvaluation E B.prime H ≠ 0 := fun h => hH B ((Sec.BR_eq_zero_iff _).mp h)
    refine ((finite_pole sep).union (finite_val_ne_one sep _ hH0)).subset fun v hv => ?_
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    exact hv ⟨fun i => not_lt.mp fun hi => hnot.1 ⟨i, hi⟩, not_not.mp hnot.2⟩
  refine (Set.finite_iUnion fun B : LevelComponent G f c => (subsingleton_mem (I := B.prime) ℓ).finite.union
    ((hbad B).biUnion fun v _ => (subsingleton_val_lt_one v ℓ).finite)).subset fun a ha => ?_
  rw [Set.mem_ofPred_eq, not_forall] at ha
  obtain ⟨B, hB⟩ := ha
  refine Set.mem_iUnion.mpr ⟨B, ?_⟩
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  refine hB ⟨fun h0 => hnot.1 ((Sec.BR_eq_zero_iff _).mp h0), fun v hv => ?_⟩
  by_contra hv'
  exact hnot.2 (Set.mem_biUnion hv' hv)
end
end Level
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE HFree6812
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime Exch.fact_irreducible
theorem not_dvd_pderiv (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    ¬(P.stage g).G ∣ pderiv 1 (P.stage g).G := fun h =>
  Data.pderiv_ne_zero P g ((Sec.BR_eq_zero_iff _).mpr (Ideal.mem_span_singleton.mpr h))
theorem not_dvd_leading (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (hlead : srcLead P.F P.F SZ ≠ 0)
    (g : RCN222.GeometricFactor K P.F) : ¬(P.stage g).G ∣ SZ.leading (RCN135.polynomialEmbedding K) := fun h => by
  have h1 : Exch.embedding P g (srcLead P.F P.F SZ) =
      RCN002.coordinateEvaluation Ω (Exch.component P g) (SZ.leading (RCN135.polynomialEmbedding K)) := Exch.embedding_sliceProj P g _
  rw [(Sec.BR_eq_zero_iff _).mpr (Ideal.mem_span_singleton.mpr h)] at h1
  exact hlead ((map_eq_zero _).mp h1)
theorem exists_section (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (N : ℕ)
    (hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N) (hNp : 3 * N < 2130706433)
    (hc : ∀ j, sliceCoord P.F j ≠ 0) (hlead : srcLead P.F P.F SZ ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (hcomp : ∀ g, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
      (Exch.moving P Q A g) c (Exch.function P SZ g))
    (hsep : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
    {W : FlagDegree} {J : Finset (Fin 3)} (hWJ : FlagCoords W J) :
    ∃ s : MvPolynomial (Fin 3) Ω, Sec.Needs P SZ Q A c W s := by
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hfin : ∀ g, Finite (LevelComponent (Exch.component P g) (Exch.moving P Q A g) c) := fun g =>
    finite_levelComponent (hN g) hNp (Exch.coordinate_ne_zero P g hc) _ c (hcomp g).ne
  have hH : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      baseH P.F ∉ B.prime := fun g B h => by
    have h1 := (LevelCount.units_of_needs (Exch.coordinate_ne_zero P g hc) (hcomp g) B).2.1
    have h2 := (LevelSurf.val_lt_one_iff B.isCurve (baseH P.F)).mpr h
    rw [h1] at h2
    exact lt_irrefl _ h2
  choose S hS hSb using fun g => exists_pole_subspaces (Exch.moving P Q A g) c (hfin g) (hsep g) J
  let Z0 : Submodule Ω (Fin 3 → Ω) :=
    LinearMap.ker (LinearMap.proj (R := Ω) (φ := fun _ : Fin 3 => Ω) 2)
  have htop : ⊤ ∉ insert Z0 (Finset.univ.biUnion S ∪
      Finset.univ.image fun g : RCN222.GeometricFactor K P.F => minorSpace J (P.stage g).G) := by
    rw [Finset.mem_insert, Finset.mem_union, not_or, not_or]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hmem : (Pi.single 2 (1 : Ω) : Fin 3 → Ω) ∈ Z0 := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at hmem
      exact one_ne_zero hmem
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp h
      exact hS g hg
    · obtain ⟨g, -, hg⟩ := Finset.mem_image.mp h
      exact minorSpace_ne_top hWJ.two _ (not_dvd_pderiv P g) hg
  obtain ⟨b, hb⟩ := exists_notMem_of_top_notMem _ htop
  have hb2 : mask J b 2 ≠ 0 := by
    rw [mask_of_mem b hWJ.two]
    exact fun h => hb Z0 (Finset.mem_insert_self _ _) (LinearMap.mem_ker.mpr h)
  have hbad := Set.finite_iUnion fun g : RCN222.GeometricFactor K P.F =>
    finite_constants (Exch.moving P Q A g) c (hfin g) (hsep g) (baseH P.F) (hH g)
      (Sec.linearForm (mask J b))
  obtain ⟨a, ha, hgood⟩ := Sec.exists_good_section
    (Finset.univ.image fun g : RCN222.GeometricFactor K P.F => (P.stage g).G) (SZ.leading (RCN135.polynomialEmbedding K)) (mask J b) 2 1 hb2
    (by decide) (fun g' hg' => by
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hg'
      exact ⟨(P.stage g).MW, not_dvd_leading P SZ hlead g, fun h =>
        hb _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_univ g)))) ((mem_minorSpace J _ b).mpr h)⟩)
    _ hbad
  have hconst := fun g => not_not.mp fun h => ha (Set.mem_iUnion.mpr ⟨g, h⟩)
  refine ⟨Sec.linearForm (mask J b) - C a, linearForm_mask_inFlag hWJ b a,
    fun g => hgood _ (Finset.mem_image_of_mem _ (Finset.mem_univ g)), fun g =>
      ⟨fun B => (hconst g B).1, fun B v => ?_, fun B v => (hconst g B).2 v⟩⟩
  obtain ⟨m, hm, hle⟩ := hWJ.pole fun m => poleOrder v.val (coordinate Ω B.prime m)
  exact (show RCN204.flagPole v.val (coordinate Ω B.prime) W ≤ _ from hle).trans
    (hSb g b (fun U hU => hb U (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hU⟩)))) B v a m hm)
theorem sections (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Sec.SectionStatement P SZ := by
  intro N hN hNp hc hlead Q A c hcomp hsep
  obtain ⟨s₀, h₀⟩ := exists_section P SZ N hN hNp hc hlead Q A c hcomp hsep flagCoords_z
  obtain ⟨s₁, h₁⟩ := exists_section P SZ N hN hNp hc hlead Q A c hcomp hsep flagCoords_yz
  obtain ⟨s₂, h₂⟩ := exists_section P SZ N hN hNp hc hlead Q A c hcomp hsep flagCoords_all
  exact ⟨s₀, s₁, s₂, h₀, h₁, h₂⟩
end
end Packet
end SecChoice
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Data
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime Exch.fact_irreducible
theorem disjoint_of_needs (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (N : ℕ) (g : RCN222.GeometricFactor K P.F)
    (hN : ∀ sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N) (hNp : 3 * N < 2130706433)
    (Q A : MvPolynomial (Fin 3) Ω) (c : Ω) (W : FlagDegree)
    (h : LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F) (Exch.moving P Q A g) c
      (Exch.function P SZ g)) :
    Exch.LevelDisjoint (Exch.moving P Q A g) c (Exch.function P SZ g) W :=
  Exch.levelDisjoint_of_unit hN hNp _ c _ W fun nu hnu hlt =>
    ⟨(h.unit nu hnu hlt).1, (h.unit nu hnu hlt).2.2.2⟩
theorem data (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F) :
    Sec.DataStatement P SZ := by
  intro N hN hNp hc htail hlead hbase hsep hclosure
  obtain ⟨S, hS⟩ := curves P hp
  obtain ⟨Q, A, hQ, hA, h2, hpole⟩ := pair P N hN hNp hc
  obtain ⟨c, hbad⟩ := (((off_level P SZ Q A S fun a _ => hS a).union (seed P SZ Q A)).union
    ((component_ne P Q A).union (component_unit P SZ N hN hNp hc htail hlead Q A))).exists_notMem
  have hlive : ∀ a ∈ active P SZ, (S a).val (Exch.moving P Q A a.1 -
      algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) = 1 := fun a ha =>
    by_contra fun h => hbad (Or.inl (Or.inl ⟨a, ha, h⟩))
  have hcomp : ∀ g, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
      (Exch.moving P Q A g) c (Exch.function P SZ g) := fun g =>
    ⟨fun h => hbad (Or.inr (Or.inl ⟨g, h⟩)), fun nu hnu hlt =>
      by_contra fun h => hbad (Or.inr (Or.inr ⟨g, nu, hnu, hlt, h⟩))⟩
  refine ⟨Q, A, c, S, hQ, hA, h2, fun a _ => hS a, ⟨fun a _ => hpole a.1, hlive, fun a ha γ hγ h =>
    hbad (Or.inl (Or.inr ⟨a, ha, γ, hγ, h⟩))⟩, ⟨fun a _ => disjoint_of_needs P SZ N a.1 (hN a.1) hNp
      Q A c _ (hcomp a.1), fun a _ q hq _ _ => hclosure a.1 a.2.1 (S a) (hS a) q hq (hbase a)⟩,
    ⟨hcomp, hlive, fun a _ q hq _ _ => hclosure a.1 a.2.1 (S a) (hS a) q hq (hbase a),
      fun g B q hq => ?_⟩⟩
  obtain ⟨bp⟩ := hsep Q A hQ hA c g (hcomp g).ne B
  exact hclosure g B.prime B.curve B.isCurve q hq bp
end
end Packet
end Data
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Assembly
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 HFree6812 DU BLL AYR BIO BBT _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime Exch.fact_irreducible
theorem srcLead_ne_zero (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (a : Curve P) (ha : a ∈ active P SZ) :
    srcLead P.F P.F SZ ≠ 0 :=
  Curve.sliceProj_ne_zero_of_notMem P.F (Exch.component P a.1) (Exch.ker_sliceMap_component P a.1) a.2.1
    ((Ideal.span_singleton_le_iff_mem _).mpr (RCN072.cutIdeal_le_component Ω (P.stage a.1).G _ a.2.1
      (RCN264.AAS Ω _ _ _ a.2) (Ideal.subset_span (Set.mem_insert _ _)))) _ (Finset.mem_filter.mp ha).2
end
end Packet
end Assembly
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Native
section Budget
noncomputable section
open scoped BigOperators
open RCN095 RCN135 RCN136 RCN207 RCN313
open RCN095 renaming PolynomialInFlag → BI
open BD LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [CharP E 2130706433]
variable (f : GenericField K →+* E)
local notation "OmegaT" => GenericField E
local notation "phi" => RingHom.comp (RCN135.coefficientEmbedding E) (codeMap f)
local notation "lift" => MvPolynomial.map (RCN135.coefficientEmbedding E)
theorem point_budget
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (S : MovingFiberThreeSources6811.Source F) (hk : S.k < 2130706433)
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p (OO f F))
    (hunit : 2 * (p.zOnly + p.yz + p.all) < 2130706433)
    (hmix : 2 * (p.zOnly + p.yz + p.all) * (q.zOnly + q.yz + q.all) < 2130706433)
    (Q A : MvPolynomial (Fin 3) E)
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A)
    (hq : RCN095.PolynomialInFlag q (XC f F Q A)) :
    AGN f F S Q A S.d (flagMixed p unitZFlag S.flag)
      (flagMixed p unitYZFlag S.flag) (flagMixed p unitAllFlag S.flag) := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hGne : OO f F ≠ 0 := fun hh => hF (BMZ f (by simpa only [OO, map_zero] using hh))
  have h2 : (2 : OmegaT) ≠ 0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (S.k.factorial : OmegaT) ≠ 0 := SecondJetOwnShape.factorial_ne S.k hk
  have hHdiv : surfaceMap phi (polyH K F) ∣ AOT f F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have hpoints : ∀ x ∈ points, MvPolynomial.eval x (OO f F) = 0 ∧
      MvPolynomial.eval x (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F))
        (lift Q) (lift A) (RCN135.initialCoordinate E)) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F) * ∏ _j : Fin 3, S.leading phi) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0 := by
    intro x hx
    refine ⟨hG x hx, hM x hx, ?_, hzero x hx⟩
    have hr := hregular x hx
    rw [map_mul] at hr
    obtain ⟨hden, hlead⟩ := mul_ne_zero_iff.mp hr
    have hH : MvPolynomial.eval x (surfaceMap phi (polyH K F)) ≠ 0 := by
      intro hz
      have hdvd := map_dvd (MvPolynomial.eval x) hHdiv
      rw [hz, zero_dvd_iff] at hdvd
      exact hden hdvd
    rw [map_mul, map_prod]
    exact mul_ne_zero hH (Finset.prod_ne_zero_iff.mpr (fun _ _ => hlead))
  have h := DMO phi F (fun _ => S) S.d (fun _ => dvd_rfl)
    (OO f F) p q W hGne dvd_rfl hp 2130706433 hunit hmix h2 (fun _ => hfact)
    (lift Q) (lift A) (RCN135.initialCoordinate E) (inFlag_map _ hQ) (inFlag_map _ hA) hq cut hcut points
    hpoints hisolated
  have hd : 0 < S.d := Nat.succ_pos _
  simpa [Fin.sum_univ_three, MovingFiberThreeSources6811.weight, MovingFiberThreeSources6811.direction, Nat.div_self hd] using h
theorem point_budget_of_weights
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (S : MovingFiberThreeSources6811.Source F) (hk : S.k < 2130706433)
    (p : FlagDegree) (hp : RCN095.PolynomialInFlag p (OO f F))
    (hunit : 2 * (p.zOnly + p.yz + p.all) < 2130706433)
    (ca cb cs : ℕ) (hR : F.degreeOf 2 ≤ cs + 2) (hYR : RCN234.wt ![0, 1, 1, 0] F ≤ cb + cs + 3)
    (hAll : RCN234.wt ![0, 1, 1, 1] F ≤ ca + cb + cs + 3)
    (hmix : 2 * (p.zOnly + p.yz + p.all) * (ca + (cb + 1) + (cs + 3)) < 2130706433)
    (Q A : MvPolynomial (Fin 3) E)
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A) :
    AGN f F S Q A S.d (flagMixed p unitZFlag S.flag)
      (flagMixed p unitYZFlag S.flag) (flagMixed p unitAllFlag S.flag) := by
  obtain ⟨hHflag, hGflag⟩ := RCN201.DGW phi ca cb cs F hR hYR hAll
  exact point_budget f F hF S hk p ⟨ca, cb + 1, cs + 3⟩ hp hunit hmix Q A hQ hA
    (FCY ca cb cs _ _ _ _ _ hHflag hGflag (inFlag_map _ hQ) (inFlag_map _ hA))
end
end Budget
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 DU BLL AYR BIO BBT CAS _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)
theorem exists_frame_of_budget
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ)
    (hraw : ∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN (RingHom.id Ω) P.F SZ Q A scale z u v) :
    ∃ (lam mu : Ω) (geometry : ∀ g, ABN (P.stage g))
      (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)),
      PacketFrame P hp SZ scale z u v lam mu geometry budget := by
  have hrlo := P.rlow
  have hrhi : r ≤ 31 := by have := packet_r_le P; omega
  have hylo := P.ylow
  have hyhi : y ≤ 142 := by have := packet_y_le P; omega
  have hyt := P.yt
  have hthi : t ≤ 9678 := by have := packet_t_le P; omega
  have hflags (g : RCN222.GeometricFactor K P.F) : (CO K g).yz + (CO K g).all < 2130706433 ∧
      (CO K g).all < 2130706433 ∧
      (CO K g).zOnly + (CO K g).yz + (CO K g).all < 2130706433 := by
    have hh := P.stage_flag g
    omega
  have hmixed (g : RCN222.GeometricFactor K P.F) := BoundaryTailGates.reduced_gate
    (CO K g) t y r (by omega) hrhi hyhi (by omega) hyt
    (P.stage_flag g).1 (P.stage_flag g).2.1
  obtain ⟨lam, mu, hlam, hmu, geometry, heq⟩ := DYG
    (KK K P.F P.selected P.seeds) x (CO K) P.stage (P.stage_proper hp) hflags hmixed
  let unit := fun g => suppliedUnit (P.stage g) (P.stage_proper hp g) (geometry g)
  obtain ⟨budget, hcost, hmoving⟩ := CTF P.F SZ
    (fun a : Curve P => a.1.val) (fun a => (P.stage a.1).RR)
    (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) w (by decide)
    P.support.IZ.2.1 P.support.ys_weight P.support.total_weight
    (fun a : Curve P => suppliedBase (P.stage a.1) (geometry a.1))
    (fun a : Curve P => CO K a.1) (LocatorHybridCells.cellFirstTail t y r)
    (fun a : Curve P => unit a.1) (fun a : Curve P => a.2) (P.FDF hp)
    (active P SZ) (fun a ha => (Finset.mem_filter.mp ha).2) scale z u v hraw
  refine ⟨lam, mu, geometry, budget, hlam, hmu, heq, fun j a => ?_, hcost, hmoving, hraw⟩
  fin_cases j
  · exact FKV (unit a.1) a.2
  · exact GDG (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam (heq a.1).1 a.2
  · exact GAA (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam mu (heq a.1).1 (heq a.1).2 a.2
theorem packet_point_budget {E : Type} [Field E] [CharP E 2130706433] (f : Ω →+* E)
    (P : Packet x t y r) (S : MovingFiberThreeSources6811.Source P.F) (hk : S.k < 2130706433)
    (Q A : MvPolynomial (Fin 3) E) (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A) :
    AGN f P.F S Q A S.d (flagMixed ⟨t - y, y - r, r⟩ unitZFlag S.flag)
      (flagMixed ⟨t - y, y - r, r⟩ unitYZFlag S.flag)
      (flagMixed ⟨t - y, y - r, r⟩ unitAllFlag S.flag) := by
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  have hthi : t ≤ 9678 := by have := packet_t_le P; omega
  have hgate : 2 * ((t - y) + (y - r) + r) * (LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3)) <
      2130706433 := by
    have h1 : (t - y) + (y - r) + r = t := by omega
    have h2 : LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3) = t + 1 := by
      dsimp only [LocatorHybridCells.cellA, LocatorHybridCells.cellB, LocatorHybridCells.cellS]
      omega
    rw [h1, h2]
    calc 2 * t * (t + 1) ≤ 2 * 9678 * 9679 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hthi) (by omega)
      _ < 2130706433 := by decide
  exact point_budget_of_weights f P.F P.irreducible.ne_zero S hk ⟨t - y, y - r, r⟩ (P.parent_flag _ _)
    (by dsimp; omega) (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) P.support.IZ.2.1 P.support.ys_weight
    P.support.total_weight hgate Q A hQ hA
theorem exists_packet_frame
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (S : MovingFiberThreeSources6811.Source P.F)
    (hk : S.k < 2130706433) :
    ∃ (lam mu : Ω) (geometry : ∀ g, ABN (P.stage g))
      (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)),
      PacketFrame P hp S S.d (flagMixed ⟨t - y, y - r, r⟩ unitZFlag S.flag)
        (flagMixed ⟨t - y, y - r, r⟩ unitYZFlag S.flag)
        (flagMixed ⟨t - y, y - r, r⟩ unitAllFlag S.flag) lam mu geometry budget :=
  exists_frame_of_budget P hp S _ _ _ _
    (fun Q A _ hQ hA => packet_point_budget (RingHom.id Ω) P S hk Q A hQ hA)
end
end Packet
end Native
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Cut
noncomputable section
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN199 RCN222 RCN238 RCN243 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU BOE AYR AFA TW CB HFreeDir6813 RL
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
def priceNumerator (d scale z u v : ℕ) (C : FlagDegree) (Φ : Fin 3 → FlagDegree) (flag source : FlagDegree) :
    ℕ :=
  d * (scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight C j * flagMixed flag (Φ j) (MovingFiberThreeSources6811.direction j)) +
      8 * (w + 1) * price C z u v) +
    16 * (w + 1) ^ 2 * price source z u v
theorem cutFlag_delay_le_smul (Hf : FlagDegree) (mu delay : ℕ) (hmu : 1 ≤ mu) (hdelay : delay ≤ mu) :
    (cutFlag (w + delay) Hf).zOnly ≤ (mu • cutFlag (w + 1) Hf).zOnly ∧
    (cutFlag (w + delay) Hf).yz ≤ (mu • cutFlag (w + 1) Hf).yz ∧
    (cutFlag (w + delay) Hf).all ≤ (mu • cutFlag (w + 1) Hf).all := by
  have hscale : w + delay ≤ mu * (w + 1) := by nlinarith [Nat.mul_le_mul_right w hmu]
  have ha := Nat.mul_le_mul_right (2 * Hf.all - 5) hscale
  have hv := Nat.mul_le_mul_right (2 * Hf.yz) hscale
  have hz := Nat.mul_le_mul_right (2 * Hf.zOnly) hscale
  simp only [cutFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
def CurveCount (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree)
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (moving : Curve P → ℕ) (o : ℕ → Curve P → ℕ) : Prop :=
  ∀ n : ℕ, ∀ a ∈ active P SZ, ∀ delay : ℕ, 1 ≤ delay →
    RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1 + delay) ∉ a.2.1 →
    3 * n * (RCN264.componentSeeds Ω (P.stage a.1).G
        (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
        (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F)
        (KK K P.F P.selected P.seeds a.1)
        (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2).card ≤
      n * (budget a).weightedCost (cutFlag (w + delay) Hf) +
        4 * (w + delay) * (n * moving a + o n a)
def LevelCount (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (scale z u v : ℕ) (moving : Curve P → ℕ) (Lam : ℕ) : Prop :=
  3 * SZ.d * scale * (∑ a ∈ active P SZ, multiplicity P hp a * moving a) + scale * Lam ≤
    SZ.d * price (cutFlag (w + 1) Hf) z u v + 4 * (w + 1) * price SZ.flag z u v
def XContracts (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (scale z u v : ℕ) : Prop :=
  ∀ (lam mu : Ω) (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)),
    PacketFrame P hp SZ scale z u v lam mu geometry budget →
    ∃ (moving : Curve P → ℕ) (o : ℕ → Curve P → ℕ) (Lam Kc : ℕ),
      CurveCount P SZ Hf budget moving o ∧ LevelCount P hp SZ Hf scale z u v moving Lam ∧
        ExchangeCount P hp SZ o Lam Kc
def SharedCostAt (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (Φ : Fin 3 → FlagDegree) (scale z u v : ℕ) : Prop :=
  ∃ (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)) (loss : ℕ),
    (∀ a, (budget a).zCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2 ∧
      (budget a).yzCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2 ∧
      (budget a).allCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2) ∧
    ∀ bound : ℕ, ∃ (den : ℕ) (mov : Curve P → ℕ), bound < den ∧
    (∀ a ∈ active P SZ, ∀ delay : ℕ, 1 ≤ delay →
      RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1 + delay) ∉ a.2.1 →
      3 * den * (RCN264.componentSeeds Ω (P.stage a.1).G
          (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
          (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F)
          (KK K P.F P.selected P.seeds a.1)
          (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2).card ≤
        den * (budget a).weightedCost (cutFlag (w + delay) Hf) +
          4 * (w + delay) * mov a) ∧
    (3 * SZ.d * scale) * (∑ a ∈ active P SZ, multiplicity P hp a *
        (den * ordinary P hp geometry a (cutFlag (w + 1) Hf) + 4 * (w + 1) * mov a)) ≤
      den * priceNumerator SZ.d scale z u v (cutFlag (w + 1) Hf) Φ ⟨t - y, y - r, r⟩ SZ.flag + loss
def FirstCutLaw (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (Φ : Fin 3 → FlagDegree) (scale z u v : ℕ) (geometry : ∀ g, ABN (P.stage g)) (W : FlagDegree) :
    Prop :=
  3 * scale * (∑ a ∈ active P SZ, multiplicity P hp a * ordinary P hp geometry a W) ≤
    scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * flagMixed ⟨t - y, y - r, r⟩ (Φ j) (MovingFiberThreeSources6811.direction j)) +
      4 * (w + 1) * price W z u v
end
section HFlag
noncomputable section
open WithZero MvPolynomial HFree6812
open RCN095 RCN204 RCN313 RCN187 DU BD
open RCN095 renaming PolynomialInFlag → BI
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
variable {K I : Type} [Field K] {x : I → K} {t y r : ℕ}
def IsHFlag (P : Packet x t y r) (Hf : FlagDegree) : Prop :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  ∀ v : Valuation (SliceField P.F) ℤᵐ⁰, (∀ a : K, a ≠ 0 → v (algebraMap K (SliceField P.F) a) = 1) →
    v (sliceProj P.F (MvPolynomial.X 0)) ≤ 1 →
    v (sliceProj P.F (polyH K P.F)) ≤ exp (flagPole v (sliceCoord P.F) Hf)
theorem IsHFlag.euler (P : Packet x t y r) : IsHFlag P ⟨t - y, y - r + 1, r - 2⟩ :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  fun v hK hX0 => polyH_euler_le P.F P.F (dvd_refl P.F) v hK hX0 (t - y) (y - r) r
    (cell_support t y r (by have := P.rlow; omega) (by have := P.ylow; omega) P.F P.support)
end
end HFlag
end Cut
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Cut
section Provider
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN199 RCN237 RCN238 RCN243 RCN244 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN334 RCN339 FA IB
noncomputable section
local notation "w" => RCN326.w
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
theorem exists_provider_of_budget
    {support : RCN275.ResidualSupportParameters} (S : FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w support)
    (hfirstProper : ¬ S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1))
    (Hf tail1 : FlagDegree)
    (B : FE (G := S.G) (T := RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (H := CR (RCN135.polynomialEmbedding K) S.F) flag tail1)
    (budget : ∀ C : CM S, RD C.1 (CR (RCN135.polynomialEmbedding K) S.F) (surfaceMap (RCN135.polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : CM S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (den : ℕ) (hden : 0 < den) (mov : CM S → ℕ)
    (active : Finset (CM S))
    (hcount : ∀ C ∈ active, ∀ delay : ℕ, 1 ≤ delay →
      RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 →
      3 * den * (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card ≤
        den * (budget C).weightedCost (cutFlag (w + delay) Hf) +
          4 * (w + delay) * mov C)
    (divisorBound : ℕ)
    (hinactive : ∀ C : CM S, C ∉ active →
      (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card = 0)
    (hjoint : (∑ C ∈ active,
      FO (MU S) (DN (MU S) hfirstProper) C *
        (den * B.weightedCost (cutFlag (w + 1) Hf) C + 4 * (w + 1) * mov C) / (3 * den)) ≤
      divisorBound)
    (hgate : 3 * (stageErrorCap + 1) ≤ (cutFlag (w + 1) Hf).yz)
    (htangent : ∀ C : CM S,
      (∀ delay, RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1 + delay) ∈ C.1) →
      (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card ≤ (stageErrorCap + 1) * B.yzCost C) :
    Nonempty (AKI (tailFlag1 := tail1) (tailFlag2 := cutFlag (w + 1) Hf) S divisorBound) := by
  classical
  let S0 := MU S
  let multiplicity : CM S → ℕ := fun C => FO S0 (DN S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C := ADP S hfirstProper
  have hwcEq : ∀ (C : CM S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [RD.weightedCost, FE.weightedCost, hz, hy', ha]
  have hscale : ∀ (m : ℕ) (f : FlagDegree) (C : CM S),
      B.weightedCost (m • f) C = m * B.weightedCost f C := by
    intro m f C
    simp only [FE.weightedCost, nsmul_zOnly, nsmul_yz, nsmul_all]
    ring
  let total : CM S → ℕ := fun C =>
    multiplicity C * (den * B.weightedCost (cutFlag (w + 1) Hf) C + 4 * (w + 1) * mov C)
  have hbound : ∀ C ∈ active,
      3 * den * (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card ≤ total C := by
    intro C hactive
    have dichotomy := AEM S0 (DN S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      have hc := hcount C hactive delay hdelay htail
      rw [hwcEq] at hc
      have hmono := cutFlag_delay_le_smul Hf (multiplicity C) delay (hone C) hdelayMu
      have hcostle := CUY B C hmono.1 hmono.2.1 hmono.2.2
      rw [hscale] at hcostle
      have hfactor : w + delay ≤ multiplicity C * (w + 1) := by
        nlinarith [Nat.mul_le_mul_right w (hone C), hdelayMu]
      have hmove : 4 * (w + delay) * mov C ≤ multiplicity C * (4 * (w + 1) * mov C) := by
        nlinarith [Nat.mul_le_mul_right (4 * mov C) hfactor]
      calc _ ≤ den * B.weightedCost (cutFlag (w + delay) Hf) C +
            4 * (w + delay) * mov C := hc
        _ ≤ den * (multiplicity C * B.weightedCost (cutFlag (w + 1) Hf) C) +
            multiplicity C * (4 * (w + 1) * mov C) :=
          Nat.add_le_add (Nat.mul_le_mul_left den hcostle) hmove
        _ = total C := by simp only [total]; ring
    · have hc := htangent C htangentBranch
      calc _ ≤ 3 * den * ((stageErrorCap + 1) * B.yzCost C) := Nat.mul_le_mul_left _ hc
        _ = den * ((3 * (stageErrorCap + 1)) * B.yzCost C) := by ring
        _ ≤ den * B.weightedCost (cutFlag (w + 1) Hf) C := Nat.mul_le_mul_left den
          (BIB B (cutFlag (w + 1) Hf) C (3 * (stageErrorCap + 1)) hgate)
        _ ≤ multiplicity C * (den * B.weightedCost (cutFlag (w + 1) Hf) C) := by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (den * B.weightedCost (cutFlag (w + 1) Hf) C) (hone C)
        _ ≤ total C := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  let cost : CM S → ℕ := fun C => if C ∈ active then total C / (3 * den) else 0
  have hcostBound : ∀ C,
      (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card ≤ cost C := by
    intro C
    by_cases hC : C ∈ active
    · simp only [cost, hC, ite_true]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 3 * den)).mpr
        ((Nat.mul_comm _ _).trans_le (hbound C hC))
    · simp only [cost, hC, ite_false, hinactive C hC, le_refl]
  have hsum : (∑ C, cost C) ≤ divisorBound := by
    have ha : (∑ C, cost C) = ∑ C ∈ active, total C / (3 * den) := by
      simp only [cost, Finset.sum_ite_mem, Finset.univ_inter]
    rw [ha]
    simpa only [total, multiplicity, S0] using hjoint
  have providerDichotomy := AFC S hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := cost
    one_le_multiplicity := hone
    EHX := le_trans (by omega) hgate
    cost_sum_le := hsum
    CRK := hcostBound
    dichotomy := providerDichotomy }⟩
end
end Provider
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN199 RCN222 RCN238 RCN243 RCN264 RCN312 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open FA IB BD DU BOE AYR AFA TW CB HFreeDir6813 RL
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
theorem packet_count_of_cleared_budget
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (hyz : 1 ≤ Hf.yz) (scale : ℕ) (hscale : 0 < scale)
    (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (den : ℕ) (mov : Curve P → ℕ) (loss : ℕ) (hloss : loss < den)
    (hcost : ∀ a, (budget a).zCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2 ∧
      (budget a).yzCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2 ∧
      (budget a).allCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2)
    (hcount : ∀ a ∈ active P SZ, ∀ delay : ℕ, 1 ≤ delay →
      RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1 + delay) ∉ a.2.1 →
      3 * den * (RCN264.componentSeeds Ω (P.stage a.1).G
          (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
          (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F)
          (KK K P.F P.selected P.seeds a.1)
          (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2).card ≤
        den * (budget a).weightedCost (cutFlag (w + delay) Hf) +
          4 * (w + delay) * mov a)
    (N : ℕ)
    (hjoint : (3 * SZ.d * scale) * (∑ a ∈ active P SZ, multiplicity P hp a *
        (den * ordinary P hp geometry a (cutFlag (w + 1) Hf) + 4 * (w + 1) * mov a)) ≤ den * N + loss)
    (hgood : ∀ gamma ∈ P.seeds,
      MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (SZ.leading (RCN135.polynomialEmbedding K)) ≠ 0) :
    P.seeds.card ≤ N / (9 * SZ.d * scale) := by
  have hden : 0 < den := Nat.zero_lt_of_lt hloss
  let total (a : Curve P) := multiplicity P hp a *
    (den * ordinary P hp geometry a (cutFlag (w + 1) Hf) + 4 * (w + 1) * mov a)
  let live (g : RCN222.GeometricFactor K P.F) : Finset (CM (P.stage g)) :=
    Finset.univ.filter (fun C => SZ.leading (RCN135.polynomialEmbedding K) ∉ C.1)
  have hsingle (g : RCN222.GeometricFactor K P.F) :
      (KK K P.F P.selected P.seeds g).card ≤ ∑ C ∈ live g, total ⟨g, C⟩ / (3 * den) := by
    let S := P.stage g
    let B := BLJ S (P.stage_proper hp g) (geometry g)
    have hinactive : ∀ C : CM S, C ∉ live g →
        (RCN264.componentSeeds Ω S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w + 1)) (CR (RCN135.polynomialEmbedding K) S.F) (KK K P.F P.selected P.seeds g)
          (DK (RCN135.polynomialEmbedding K) S.selected) C).card = 0 := by
      intro C hC
      have hmem : SZ.leading (RCN135.polynomialEmbedding K) ∈ C.1 := by
        simpa only [live, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hC
      exact AEF.BOK _ _ _ (SZ.leading (RCN135.polynomialEmbedding K)) (KK K P.F P.selected P.seeds g)
        (DK (RCN135.polynomialEmbedding K) S.selected) C hmem
        (fun gamma hg => hgood gamma (WK K P.F P.selected P.seeds g hg))
    obtain ⟨provider⟩ := exists_provider_of_budget S (P.stage_proper hp g)
      Hf (LocatorHybridCells.cellFirstTail t y r) B (fun C => budget ⟨g, C⟩) (fun C => hcost ⟨g, C⟩)
      den hden (fun C => mov ⟨g, C⟩) (live g)
      (fun C hC delay hdelay htail => hcount ⟨g, C⟩
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hC).2⟩) delay hdelay htail)
      (∑ C ∈ live g, total ⟨g, C⟩ / (3 * den)) hinactive (le_refl _)
      (by dsimp [cutFlag, RCN326.w]; omega)
      (fun C hall => ALX S C (P.stage_proper hp g) (suppliedBase S (geometry g) C)
        _ P.D t r P.nodeCount (P.CVV g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B (EKM S (P.stage_proper hp g) (geometry g) C) hall
        (FDD S (P.stage_proper hp g) (geometry g) C))
    exact BIF S provider
  have hsum : (∑ g, ∑ C ∈ live g, total ⟨g, C⟩ / (3 * den)) =
      ∑ a ∈ active P SZ, total a / (3 * den) := by
    simp only [live, active, Finset.sum_filter]
    rw [Fintype.sum_sigma]
  have hthird : (∑ a ∈ active P SZ, total a / (3 * den)) * (3 * den) ≤
      ∑ a ∈ active P SZ, total a := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun a _ => Nat.div_mul_le_self (total a) (3 * den))
  have hcard : P.seeds.card ≤ ∑ a ∈ active P SZ, total a / (3 * den) := by
    calc
      P.seeds.card ≤ ∑ g, (KK K P.F P.selected P.seeds g).card := P.seeds_cover
      _ ≤ ∑ g, ∑ C ∈ live g, total ⟨g, C⟩ / (3 * den) := Finset.sum_le_sum (fun g _ => hsingle g)
      _ = ∑ a ∈ active P SZ, total a / (3 * den) := hsum
  have hdZ : 0 < SZ.d := by dsimp [MovingFiberThreeSources6811.Source.d]; omega
  have hmain : den * (P.seeds.card * (9 * SZ.d * scale)) ≤ den * N + loss := by
    calc den * (P.seeds.card * (9 * SZ.d * scale))
        = (3 * SZ.d * scale) * (P.seeds.card * (3 * den)) := by ring
      _ ≤ (3 * SZ.d * scale) * ((∑ a ∈ active P SZ, total a / (3 * den)) * (3 * den)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard)
      _ ≤ (3 * SZ.d * scale) * (∑ a ∈ active P SZ, total a) := Nat.mul_le_mul_left _ hthird
      _ ≤ _ := hjoint
  refine (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (by decide) hdZ) hscale)).mpr ?_
  have hlt : den * (P.seeds.card * (9 * SZ.d * scale)) < den * (N + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.lt_of_le_of_lt hmain (Nat.add_lt_add_left hloss _)
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)
theorem packet_count_at
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (hyz : 1 ≤ Hf.yz) (Φ : Fin 3 → FlagDegree) (scale z u v : ℕ)
    (hscale : 0 < scale) (hR : SharedCostAt P hp SZ Hf Φ scale z u v)
    (hgood : ∀ gamma ∈ P.seeds,
      MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (SZ.leading (RCN135.polynomialEmbedding K)) ≠ 0) :
    P.seeds.card ≤
      priceNumerator SZ.d scale z u v (cutFlag (w + 1) Hf) Φ ⟨t - y, y - r, r⟩ SZ.flag /
        (9 * SZ.d * scale) := by
  obtain ⟨geometry, budget, loss, hcost, hall⟩ := hR
  obtain ⟨den, mov, hden, hcount, hjoint⟩ := hall loss
  exact packet_count_of_cleared_budget P hp SZ Hf hyz scale hscale geometry budget den mov loss hden hcost
    hcount _ hjoint hgood
theorem shared_cost_at_of_counts
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (Φ : Fin 3 → FlagDegree) (scale z u v : ℕ)
    (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (hcost : ∀ a, (budget a).zCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2 ∧
      (budget a).yzCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2 ∧
      (budget a).allCost =
        (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2)
    (hN1 : FirstCutLaw P hp SZ Φ scale z u v geometry (cutFlag (w + 1) Hf))
    (moving : Curve P → ℕ) (o : ℕ → Curve P → ℕ) (Lam Kc : ℕ)
    (hcurve : CurveCount P SZ Hf budget moving o)
    (hlevel : LevelCount P hp SZ Hf scale z u v moving Lam)
    (hexch : ExchangeCount P hp SZ o Lam Kc) :
    SharedCostAt P hp SZ Hf Φ scale z u v := by
  refine ⟨geometry, budget, 4 * (w + 1) * (scale * Kc), hcost, fun bound =>
    ⟨bound + 1, fun a => (bound + 1) * moving a + o (bound + 1) a, Nat.lt_succ_self _,
      hcurve (bound + 1), ?_⟩⟩
  unfold FirstCutLaw at hN1
  unfold LevelCount at hlevel
  set n := bound + 1 with hn
  set pc := price (cutFlag (w + 1) Hf) z u v with hpc
  set ps := price SZ.flag z u v with hps
  set first := ∑ j : Fin 3, MovingFiberThreeSources6811.weight (cutFlag (w + 1) Hf) j *
    flagMixed ⟨t - y, y - r, r⟩ (Φ j) (MovingFiberThreeSources6811.direction j) with hfirst
  set S1 := ∑ a ∈ active P SZ, multiplicity P hp a *
    ordinary P hp geometry a (cutFlag (w + 1) Hf) with hS1
  set S2 := ∑ a ∈ active P SZ, multiplicity P hp a * moving a with hS2
  set S3 := ∑ a ∈ active P SZ, multiplicity P hp a * o n a with hS3
  have hsum : (∑ a ∈ active P SZ, multiplicity P hp a *
      (n * ordinary P hp geometry a (cutFlag (w + 1) Hf) + 4 * (w + 1) * (n * moving a + o n a))) =
      n * S1 + 4 * (w + 1) * (n * S2 + S3) := by
    rw [hS1, hS2, hS3]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hsum]
  have hex := hexch n
  rw [← hS3] at hex
  have h1 := Nat.mul_le_mul_left (SZ.d * n) hN1
  have h2 := Nat.mul_le_mul_left (4 * (w + 1) * n) hlevel
  have h3 := Nat.mul_le_mul_left (4 * (w + 1) * scale) hex
  simp only [priceNumerator]
  rw [← hfirst, ← hpc, ← hps]
  nlinarith [h1, h2, h3]
theorem shared_cost_at_of_contracts
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (Φ : Fin 3 → FlagDegree) (scale z u v : ℕ) (lam mu : Ω)
    (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (hframe : PacketFrame P hp SZ scale z u v lam mu geometry budget)
    (hfirst : FirstCutLaw P hp SZ Φ scale z u v geometry (cutFlag (w + 1) Hf))
    (hX : XContracts P hp SZ Hf scale z u v) :
    SharedCostAt P hp SZ Hf Φ scale z u v := by
  obtain ⟨moving, o, Lam, Kc, hcurve, hlevel, hexch⟩ := hX lam mu geometry budget hframe
  exact shared_cost_at_of_counts P hp SZ Hf Φ scale z u v geometry budget hframe.cost hfirst
    moving o Lam Kc hcurve hlevel hexch
end
end Packet
end Cut
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Cut
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 HFree6812 DU BLL AYR BIO BBT _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime Exch.fact_irreducible
omit [CharP K 2130706433] in
theorem exchFlag_le {F : MvPolynomial (Fin 4) K} (SZ : MovingFiberThreeSources6811.Source F) (Hf : FlagDegree) :
    (Exch.flag SZ Hf).zOnly ≤ SZ.d * (cutFlag (w + 1) Hf).zOnly + 4 * (w + 1) * SZ.flag.zOnly ∧
    (Exch.flag SZ Hf).yz ≤ SZ.d * (cutFlag (w + 1) Hf).yz + 4 * (w + 1) * SZ.flag.yz ∧
    (Exch.flag SZ Hf).all ≤ SZ.d * (cutFlag (w + 1) Hf).all + 4 * (w + 1) * SZ.flag.all := by
  simp only [Exch.flag, cutFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [Nat.zero_le (SZ.d * (2 * Hf.zOnly)),
    Nat.zero_le (SZ.d * (2 * Hf.yz)), Nat.zero_le (SZ.d * (2 * Hf.all - 5)), Nat.zero_le SZ.flag.zOnly,
    Nat.zero_le SZ.flag.yz, Nat.zero_le SZ.flag.all]
theorem xContracts
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : IsHFlag P Hf) (scale z u v : ℕ) :
    XContracts P hp SZ Hf scale z u v := by
  intro lam mu geometry budget hframe
  by_cases hlead : srcLead P.F P.F SZ = 0
  · have hempty : active P SZ = ∅ :=
      Finset.eq_empty_of_forall_notMem fun a ha => Assembly.srcLead_ne_zero P SZ a ha hlead
    refine ⟨fun _ => 0, fun _ _ => 0, 0, 0, ?_, ?_, ?_⟩
    · intro n a ha
      exact absurd (hempty ▸ ha) (Finset.notMem_empty a)
    · simp [LevelCount]
    · intro n
      simp
  have hc := Chart.packet_sliceCoord_ne_zero P hp
  have hI : ∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ := fun sR sY sZ =>
    Chart.common_psiS_integral P.F P.F (dvd_refl P.F) (Chart.packet_polyH_ne_zero P) t P.total_weight
      (by have := packet_t_le P; omega) hc SZ (RCN347.factorial_cast_ne_zero_below_characteristic 2130706433 SZ.k hZd) hlead Hf h5 hHf sR sY sZ
  have hN := Chart.surfaceNoether_component P hp
  have hNp := Chart.packet_three_mul_lt P
  have hsep := LevelCount.separable P
  obtain ⟨Q, A, c, S, s₀, s₁, s₂, hQ, hA, -, hS, hCn, hXn, hLn, h₀, h₁, h₂⟩ :=
    Sec.choice_of_data_of_section P SZ (Data.data P hp SZ) (SecChoice.sections P SZ) t hN hNp hc
      (Exch.tail_ne_zero P hp) hlead
      (fun a => suppliedBase (P.stage a.1) (geometry a.1) a.2) hsep
      (fun g _ _ _ h q hq sep =>
        h.finite_integralClosure (Chart.packet_coordinate_ne_zero P hp g) q hq sep)
  have htail := tail_order P hp SZ S hS
  have hbound : SectionBound P scale z u v Q A c :=
    Sec.section_bound P SZ scale z u v hframe.point_budget t hN hNp
      (Chart.packet_coordinate_ne_zero P hp) Q A hQ hA c
      (fun _ _ _ => PlaceSurf.surfacePoint_length_eq_zeros)
      (fun g B => hsep Q A hQ hA c g (hLn.component g).ne B) s₀ s₁ s₂ h₀ h₁ h₂
  have hXf : Exch.ExchangeNeeds P SZ Q A c S (Exch.flag SZ Hf) :=
    ⟨fun a _ => Exch.levelDisjoint_of_unit (hN a.1) hNp _ c _ _ fun nu hnu hlt =>
      ⟨((hLn.component a.1).unit nu hnu hlt).1, ((hLn.component a.1).unit nu hnu hlt).2.2.2⟩,
      hXn.closure⟩
  refine ⟨fun a => curveMoving (S a) (Exch.moving P Q A a.1) c, Exch.baseOrder P Q A c S,
    Exch.lam P SZ Q A c (Exch.flag SZ Hf), Exch.constant P hp SZ Q A c S (Exch.flag SZ Hf),
    Curve.count_flag P SZ Hf h5 (fun _ _ _ v hv => hHf v hv.trivial_on_K hv.x0_le_one) budget
      (fun a => suppliedBase (P.stage a.1) (geometry a.1) a.2) t hN hNp Q A c S hS hCn,
    ?_,
    Exch.exchange_count P hp SZ Hf Q A c S hS hXf hc hI t hN hNp htail
      (fun _ _ => PlaceSurf.surfacePoint_leastOrder_le)⟩
  refine (LevelCount.level_count_price P hp SZ scale z u v Hf Q A c S hS hLn hbound hc hI t hN hNp
    htail hQ hA).trans ?_
  obtain ⟨hWz, hWu, hWv⟩ := exchFlag_le SZ Hf
  simp only [price]
  nlinarith [Nat.mul_le_mul_right z hWz, Nat.mul_le_mul_right u hWu, Nat.mul_le_mul_right v hWv]
end
end Packet
end Cut
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Euler
section Lemma
open scoped WithZero
open MvPolynomial
open RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
variable {K : Type} {L : Type*} [Field K] [Field L]
theorem euler_inFlag (z v r : ℕ) (F : MvPolynomial (Fin 3) K) (hF : RCN095.PolynomialInFlag ⟨z, v, r⟩ F) :
    RCN095.PolynomialInFlag ⟨z, v + 1, r - 1⟩ (C (r : K) * F - MvPolynomial.X 1 * pderiv 1 F) := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_C_mul, coeff_X_mul_pderiv, ← sub_mul] at hd
  have hne : d 1 ≠ r := fun h => hd (by rw [h, sub_self, zero_mul])
  obtain ⟨h1, h2, h3⟩ := hF d (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hd))
  dsimp only at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
theorem pderiv_R_inFlag (z v r : ℕ) (F : MvPolynomial (Fin 3) K) (hF : RCN095.PolynomialInFlag ⟨z, v, r⟩ F) :
    RCN095.PolynomialInFlag ⟨z, v, r - 1⟩ (pderiv 1 F) := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, coeff_pderiv_succ] at hd
  obtain ⟨h1, h2, h3⟩ := hF _ (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hd))
  simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.isValue, ↓reduceIte, add_zero,
    show ((1 : Fin 3) = 0) = False from by decide, show ((1 : Fin 3) = 2) = False from by decide]
    at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
theorem euler_value_le (V : Valuation L (WithZero (Multiplicative ℤ))) (coeff : K →+* L)
    (hcoeff : ∀ a, V (coeff a) ≤ 1) (x : Fin 3 → L) (z v r : ℕ) (hr : 2 ≤ r)
    (F : MvPolynomial (Fin 3) K) (hF : RCN095.PolynomialInFlag ⟨z, v, r⟩ F)
    (h0 : MvPolynomial.eval₂Hom coeff x F = 0) :
    V (MvPolynomial.eval₂Hom coeff x (pderiv 1 F)) ≤ WithZero.exp (flagPole V x ⟨z, v + 1, r - 2⟩) := by
  have hr1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  have hr2 : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
  by_cases hcase : RCN187.poleOrder V (x 1) ≤
      max (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2))
  · refine (RCN204.valuation_eval_le_flag V coeff hcoeff x ⟨z, v, r - 1⟩ _ (pderiv_R_inFlag z v r F hF)).trans ?_
    rw [WithZero.exp_le_exp]
    simp only [flagPole, max_eq_right hcase, hr1, hr2]
    push_cast
    linarith
  · rw [not_le] at hcase
    have hbeta : 0 ≤ max (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2)) :=
      le_max_of_le_left (le_max_left _ _)
    have hx1ne : V (x 1) ≠ 0 := by
      intro hz
      have : RCN187.poleOrder V (x 1) = 0 := by simp [RCN187.poleOrder, hz]
      omega
    have hx1 : V (x 1) = WithZero.exp (RCN187.poleOrder V (x 1)) := by
      rw [← WithZero.exp_log hx1ne]
      congr 1
      have : RCN187.poleOrder V (x 1) = max 0 (V (x 1)).log := rfl
      omega
    have hE := RCN204.valuation_eval_le_flag V coeff hcoeff x ⟨z, v + 1, r - 1⟩ _ (euler_inFlag z v r F hF)
    have heval : MvPolynomial.eval₂Hom coeff x (C (r : K) * F - MvPolynomial.X 1 * pderiv 1 F) =
        -(x 1 * MvPolynomial.eval₂Hom coeff x (pderiv 1 F)) := by
      rw [map_sub, map_mul, map_mul, h0, mul_zero, zero_sub, eval₂Hom_X']
    rw [heval, Valuation.map_neg, map_mul, hx1] at hE
    have hmul := mul_le_mul_right hE (WithZero.exp (-RCN187.poleOrder V (x 1)))
    rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul,
      ← WithZero.exp_add] at hmul
    refine hmul.trans ?_
    rw [WithZero.exp_le_exp]
    simp only [flagPole, max_eq_left hcase.le, hr1, hr2]
    push_cast
    linarith
end Lemma
section Carrier
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place_p19)
open RCN002 RCN055 RCN095 RCN136 RCN156 RCN208 RCN234 RCN313 RCN341
open RCN095 renaming PolynomialInFlag → BI
variable {K E : Type} [Field K] [Field E]
theorem carrier_H_pole_le (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (r v z : ℕ) (hr : 2 ≤ r)
    (hR : WeightBound RCN156.residualSWeights F (r : ℤ))
    (hYR : WeightBound RCN156.residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound RCN156.residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hF : surfaceMap phi F ∈ C) (nu : Place_p19 E (RCN002.CoordinateField E C)) :
    RCN346.poleOrder_p19 E (RCN002.CoordinateField E C) nu (SecondJetComponentRoots.coefficientMap phi C (polyH K F)) ≤
      flagPole nu.val (coordinate E C) ⟨z, v + 1, r - 2⟩ := by
  have hflag : RCN095.PolynomialInFlag ⟨z, v, r⟩ (surfaceMap phi F) := by
    apply BoundaryTailAlgebra.weightBounds_surfaceMap_flag
    · exact hR
    · convert hYR using 2
      dsimp only
      omega
    · convert hAll using 2
      dsimp only
      omega
  have hzero : MvPolynomial.eval₂Hom (algebraMap E (RCN002.CoordinateField E C)) (coordinate E C)
      (surfaceMap phi F) = 0 := by
    rw [BoundaryTailAlgebra.coordinate_eval₂]
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mpr hF
  have h := euler_value_le nu.val (algebraMap E (RCN002.CoordinateField E C)) (RCN344.NP E (RCN002.CoordinateField E C) nu)
    (coordinate E C) z v r hr (surfaceMap phi F) hflag hzero
  rw [RCN267.surfaceMap_pderiv_R] at h
  apply ActualFirstCutPole6807.pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
  simpa only [SecondJetComponentRoots.coefficientMap, RCN002.coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, polyH] using h
end Carrier
section Flags
open RCN095
open RCN095 renaming PolynomialInFlag → BI
open RCN204 (flagPole)
open HFreeDir6813 (ASY hfreeFlagDir cuspFlag flag_eq_iff)
local notation "w" => RCN326.w
def cuspFlagE (d : Fin 3) (r v z : ℕ) : FlagDegree :=
  ![⟨2 * z, 2 * v + 2 - 3 - (9 - 2 * r), 2 * r - 9⟩, ⟨2 * z, 2 * v + 2 - (9 - 2 * r), 2 * r - 9⟩,
    ⟨2 * z, 2 * v + 2 - 3, 2 * r - 6⟩] d
def capFlagE (d : Fin 3) (r : ℕ) : FlagDegree :=
  ![⟨0, 3 + (9 - 2 * r), 5 - (9 - 2 * r)⟩, ⟨0, 9 - 2 * r, 5 - (9 - 2 * r)⟩, ⟨0, 3, 2⟩] d
theorem cuspE_add_capE (d : Fin 3) (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    cuspFlagE d r v z + capFlagE d r = 2 • (⟨z, v + 1, r - 2⟩ : FlagDegree) := by
  rw [flag_eq_iff]
  fin_cases d <;> simp [cuspFlagE, capFlagE] <;> omega
theorem capFlagE_pole_le {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (d : Fin 3) (r : ℕ) (hr : 3 ≤ r) :
    flagPole V x (capFlagE d r) ≤ flagPole V x (HFree6812.infCap d) := by
  have h1 : 0 ≤ RCN187.poleOrder V (x 0) := le_max_left _ _
  have h2 := le_max_right (RCN187.poleOrder V (x 1))
    (max (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2)))
  have h3 := le_max_left (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2))
  rcases (show r = 3 ∨ r = 4 ∨ 9 - 2 * r = 0 by omega) with rfl | rfl | h0
  · fin_cases d <;> simp [flagPole, capFlagE, HFree6812.infCap] <;> omega
  · fin_cases d <;> simp [flagPole, capFlagE, HFree6812.infCap] <;> omega
  · fin_cases d <;> simp [flagPole, capFlagE, HFree6812.infCap, h0]
def hfreeFlagDirE (d : Fin 3) (r v z : ℕ) (C0 : FlagDegree) : FlagDegree :=
  (w + 1) • cuspFlagE d r v z + 3 • C0
def eulerFirst (t y r : ℕ) (j : Fin 3) : FlagDegree :=
  hfreeFlagDirE j r (y - r) (t - y) unitAllFlag
end Flags
end Euler
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option linter.all false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Euler
section Mass
noncomputable section
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
theorem first_pole_massE
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:RCN341.SeparableLiteralCoordinate C)
    (hF:surfaceMap phi F∈C) (hH:surfaceMap phi (polyH K F)∉C)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound RCN156.residualSWeights F (r:ℤ))
    (hYR:WeightBound RCN156.residualYSWeights F ((r+v:ℕ):ℤ))
    (hAll:WeightBound RCN156.residualTotalWeights F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hbudget:APH phi F C C0 (HFree6812.infCap d))
    (scale CX CV:ℕ)
    (hXbudget: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
      (∑ nu∈W,flagPole nu.val (coordinate E C) (hfreeFlagDirE d r v z C0))≤(CX:ℤ))
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
  let Hf:FlagDegree:=⟨z,v+1,r-2⟩
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

  have hpoleH (nu:Place_p19 E L):
      RCN346.poleOrder_p19 E L nu H≤flagPole nu.val (coordinate E C) Hf:=
    carrier_H_pole_le phi F C r v z (by omega) hR hYR hAll hF nu
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
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlagE d r v z))+
        ∑ nu ∈ W',flagPole nu.val (coordinate E C) (HFree6812.infCap d):=by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun nu _=> ?_
    have e1:=congrArg (flagPole nu.val (coordinate E C)) (cuspE_add_capE d r v z hr hv)
    rw [RCN204.flagPole_add,RCN204.flagPole_nsmul] at e1
    have e2:=capFlagE_pole_le nu.val (coordinate E C) d r hr
    push_cast at e1
    linarith
  have hX:=hXbudget W'
  simp only [hfreeFlagDirE,RCN204.flagPole_add,RCN204.flagPole_nsmul,Finset.sum_add_distrib,
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
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlagE d r v z))+
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
end Mass
end Euler
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option linter.all false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Euler
section AllSlices
noncomputable section
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
theorem first_cut_all_slicesE
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
      scale*flagMixed parent q (hfreeFlagDirE d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap):=by
  classical
  let carrier:=BXI eta F
  let A:=RCN208.scalarPolynomialMap Ω E (RCN086.globalTailCut (RCN135.polynomialEmbedding K) F (w+1))
  let R:=frozenH eta F
  let point:=fun i=>RCN134.embeddingPoint (old i).1 (emb i)
  let mu:=fun i=>FO (S i) (DN (S i) (hproper i)) (old i)
  let first:=hfreeFlagDirE d r v z C0
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
        have hh:=first_pole_massE phiE F a.val.2.1
          (budgets.base a.val.1 a.val.2) hFd hHd d r v z hr hv hR hYR hAll C0
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
end AllSlices
section Channel
noncomputable section
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
theorem first_cut_generic_channelE
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
      scale*flagMixed parent q (hfreeFlagDirE d r v z C0)+
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
  have hmass:=first_cut_all_slicesE (fun i:T=>Gamma i.1) (fun i:T=>flag i.1)
    (fun i:T=>S i.1) F hF (fun i=>hSF i.1) parent hparent (fun i=>hproper i.1)
    oldT embT hpoints N q hNq (fun i=>(hcert i).2.1) (fun i=>(hcert i).2.2.2.2)
    hdeg hmix SZ (fun i=>hleading i.1) d r v z hr hv hR hYR hAll C0
    (fun D _ sep hFD hND hHD=>hfree D sep hFD hND hHD) scale zCap uCap vCap hbound
  have hsum:=GenericSlicePoints6807.weighted_embedding_sum (E:=E) oldPrime
    (fun a=>FO (S a) (DN (S a) (hproper a)) (old a))
  simpa only [oldT,embT,T,RCN344.SeparableCoordinate.degree,oldPrime,hsum] using hmass
theorem first_cut_coordinate_channelE
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
      scale*flagMixed parent q (hfreeFlagDirE d r v z C0)+
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
  have hb:=first_cut_generic_channelE (E:=E)
    (fun a:Alive=>Gamma a.1) (fun a:Alive=>flag a.1) (fun a:Alive=>S a.1)
    F hF (fun a=>hSF a.1) parent hparent (fun a=>hproper a.1) old0 hi0 ell q hell
    sep hv0 hdeg hmix SZ (fun a=>hleading a.1) d r v z hr hv hR hYR hAll C0 hfree
    scale zCap uCap vCap hbound
  change 3*scale*(∑ a,weight a*RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old a).1) (projection a))≤_
  rw [hsum]
  exact hb
end
end Channel
end Euler
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Euler
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
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
theorem flagMixed_swap (p q r : FlagDegree) : flagMixed p q r = flagMixed p r q := by
  unfold flagMixed
  ring
theorem sum_weight_swap {A : Type} [Fintype A]
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
theorem sum_weight_price (W : FlagDegree) (scale coeff z u v : ℕ) (fixed : Fin 3 → ℕ) :
    (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * (scale * fixed j + coeff * price (MovingFiberThreeSources6811.direction j) z u v)) =
      scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * fixed j) + coeff * price W z u v := by
  simp only [Nat.mul_add, Finset.sum_add_distrib, Nat.mul_left_comm, ← Finset.mul_sum]
  rw [GEV]
theorem first_cut_packetE
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F) (ht : t ≤ 9678)
    (scale z u v : ℕ) (lam mu : Ω) (hlam : lam ∈ Set.range (RCN135.polynomialEmbedding K)) (hmu : mu ∈ Set.range (RCN135.polynomialEmbedding K))
    (geometry : ∀ g, ABN (P.stage g))
    (hvalue : ∀ (j : Fin 3) (a : Curve P),
      RCN344.coordinateValue Ω (RCN002.CoordinateField Ω a.2.1)
        (![(suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zProjection a.2,
          (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzProjection a.2,
          (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).NV a.2] j) =
        RCN002.coordinateEvaluation Ω a.2.1 (DSG lam mu j))
    (hbound : ∀ Q U : MvPolynomial (Fin 3) Ext, (2 : MvPolynomial (Fin 3) Ext) * U ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag U →
      AGN (algebraMap Ω Ext) P.F SZ Q U scale z u v)
    (W : FlagDegree) :
    3 * scale * (∑ a ∈ active P SZ, multiplicity P hp a * ordinary P hp geometry a W) ≤
      scale * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j *
          flagMixed ⟨t - y, y - r, r⟩ (eulerFirst t y r j) (MovingFiberThreeSources6811.direction j)) +
        4 * (w + 1) * price W z u v := by
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  let unit := fun g => suppliedUnit (P.stage g) (P.stage_proper hp g) (geometry g)
  let live := active P SZ
  let projection : (j : Fin 3) → (a : Curve P) → Coordinate Ω (RCN002.CoordinateField Ω a.2.1) :=
    fun j a => ![(unit a.1).zProjection a.2, (unit a.1).yzProjection a.2, (unit a.1).NV a.2] j
  have hR : WeightBound RCN156.residualSWeights P.F (r : ℤ) := Or.inr (by exact_mod_cast P.r_weight)
  have hYR : WeightBound RCN156.residualYSWeights P.F ((r + (y - r) : ℕ) : ℤ) :=
    Or.inr (by exact_mod_cast (show wt RCN156.residualYSWeights P.F ≤ r + (y - r) by have := P.y_weight; omega))
  have hAll : MvPolynomial.weightedTotalDegree RCN156.residualTotalWeights P.F ≤ r + (y - r) + (t - y) := by
    have hh : MvPolynomial.weightedTotalDegree RCN156.residualTotalWeights P.F ≤ t := P.total_weight
    omega
  have hnormal (j : Fin 3) :
      3 * scale * (∑ a : live, multiplicity P hp a.val *
          RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω a.val.2.1) (projection j a.val)) ≤
        scale * flagMixed ⟨t - y, y - r, r⟩ (eulerFirst t y r j) (MovingFiberThreeSources6811.direction j) +
          4 * (w + 1) * price (MovingFiberThreeSources6811.direction j) z u v := by
    have hell : RCN095.PolynomialInFlag (MovingFiberThreeSources6811.direction j) (DSG lam mu j) := by
      fin_cases j
      · exact FFR
      · exact FDG lam
      · exact FFE mu lam
    have hq : (MovingFiberThreeSources6811.direction j).zOnly + (MovingFiberThreeSources6811.direction j).yz + (MovingFiberThreeSources6811.direction j).all = 1 := by
      fin_cases j <;> rfl
    have hh := first_cut_coordinate_channelE (E := Ext)
      (fun a : live => KK K P.F P.selected P.seeds a.val.1)
      (fun a : live => CO K a.val.1)
      (fun a : live => MU (P.stage a.val.1))
      P.F P.irreducible.ne_zero (fun _ => rfl) ⟨t - y, y - r, r⟩ (P.parent_flag _ _)
      (fun a => P.stage_proper hp a.val.1) (fun a : live => a.val.2)
      (fun a b hh => Subtype.ext (P.FDF hp hh))
      (DSG lam mu j) (MovingFiberThreeSources6811.direction j) hell (fun a => projection j a.val) (fun a => hvalue j a.val)
      (by dsimp only; omega) (by rw [hq, mul_one]; dsimp only; omega)
      SZ (fun a => (Finset.mem_filter.mp a.property).2) j r (y - r) (t - y) (by omega) (by omega)
      hR hYR (Or.inr (by exact_mod_cast hAll)) unitAllFlag
      (FGQ P.F (r + (y - r) + (t - y)) hAll (by omega) lam mu hlam hmu j) scale z u v hbound
    simpa only [BOE.multiplicity, price, eulerFirst, flagMixed_swap] using hh
  change 3 * scale * (∑ a ∈ live, multiplicity P hp a * ordinary P hp geometry a W) ≤ _
  have hordinary (a : Curve P) : ordinary P hp geometry a W =
      ∑ j : Fin 3, MovingFiberThreeSources6811.weight W j * RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω a.2.1) (projection j a) := by
    simp only [Fin.sum_univ_three, projection, MovingFiberThreeSources6811.weight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, ordinary, BLJ, FE.weightedCost, unit, EE.toFE, QZ.toFE, EE.toQZ]
    rfl
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Nat.mul_le_mul_left (MovingFiberThreeSources6811.weight W j) (hnormal j))
  rw [sum_weight_swap, sum_weight_price] at hh
  rw [← Finset.sum_coe_sort live (fun a => multiplicity P hp a * ordinary P hp geometry a W)]
  simpa only [hordinary] using hh
theorem first_cut_pairE
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F)
    (ht : t ≤ 9678) (hZd : SZ.k < 2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433)
    (lam mu : Ω) (hlam : lam ∈ Set.range (RCN135.polynomialEmbedding K)) (hmu : mu ∈ Set.range (RCN135.polynomialEmbedding K))
    (geometry : ∀ g, ABN (P.stage g))
    (hvalue : ∀ (j : Fin 3) (a : Curve P),
      RCN344.coordinateValue Ω (RCN002.CoordinateField Ω a.2.1)
        (![(suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zProjection a.2,
          (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzProjection a.2,
          (suppliedUnit (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).NV a.2] j) =
        RCN002.coordinateEvaluation Ω a.2.1 (DSG lam mu j))
    (W : FlagDegree) :
    3 * stageScale SZ delta *
        (∑ a ∈ active P SZ, multiplicity P hp a * ordinary P hp geometry a W) ≤
      stageScale SZ delta * (∑ j : Fin 3, MovingFiberThreeSources6811.weight W j *
          flagMixed ⟨t - y, y - r, r⟩ (eulerFirst t y r j) (MovingFiberThreeSources6811.direction j)) +
        4 * (w + 1) * price W
          (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
          (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
          (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag) := by
  have hylo := P.ylow
  have hyt := P.yt
  exact first_cut_packetE P hp SZ ht _ _ _ _ lam mu hlam hmu geometry hvalue
    (fun Q U hden hQf hUf => BSF (algebraMap Ω Ext) P.F P.irreducible.ne_zero P.rdegree
      (P.IZ.2.1.trans_lt (by omega)) SP SQ hcop delta hd hP hQ hdchar SZ hZd ⟨t - y, y - r, r⟩
      (P.parent_flag _ _) (by dsimp only; omega) Q U hden hQf hUf hz hu) W
end
end Packet
end Euler
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Cut
section Euler
noncomputable section
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN156 RCN199 RCN222 RCN234 RCN238 RCN243 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open FA BD DU BOE AYR AFA TW CB HFreeDir6813 RL _Q7
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
def eulerFlag (t y r : ℕ) : FlagDegree :=
  ⟨t - y, y - r + 1, r - 2⟩
def numeratorRE (d scale z u v t y r : ℕ) (flag source : FlagDegree) : ℕ :=
  priceNumerator d scale z u v (cutFlag (w + 1) (eulerFlag t y r)) (Euler.eulerFirst t y r) flag source
def pairStageCostRE {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : MovingFiberThreeSources6811.Source F) (delta t y r : ℕ) (flag : FlagDegree) : ℕ :=
  numeratorRE SZ.d (stageScale SZ delta)
    (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
    (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    t y r flag SZ.flag / (9 * SZ.d * stageScale SZ delta)
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)
theorem xContracts_euler
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433) (hr : 5 ≤ r) (scale z u v : ℕ) :
    XContracts P hp SZ (eulerFlag t y r) scale z u v :=
  xContracts P hp SZ hZd _ (by show 5 ≤ 2 * (r - 2); omega) (IsHFlag.euler P) scale z u v
theorem shared_cost_euler_of_frame
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433) (hr : 5 ≤ r) (scale z u v : ℕ) (lam mu : Ω)
    (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (hframe : PacketFrame P hp SZ scale z u v lam mu geometry budget)
    (hbound : ∀ Q U : MvPolynomial (Fin 3) Ext, (2 : MvPolynomial (Fin 3) Ext) * U ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag U →
      AGN (algebraMap Ω Ext) P.F SZ Q U scale z u v) :
    SharedCostAt P hp SZ (eulerFlag t y r) (Euler.eulerFirst t y r) scale z u v :=
  shared_cost_at_of_contracts P hp SZ _ _ scale z u v lam mu geometry budget hframe
    (Euler.first_cut_packetE P hp SZ (by have := packet_t_le P; omega) scale z u v lam mu
      hframe.lam_mem hframe.mu_mem geometry hframe.value hbound _)
    (xContracts_euler P hp SZ hZd hr scale z u v)
theorem shared_RE_cost
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ SP SQ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433)
    (hr : 5 ≤ r) :
    SharedCostAt P hp SZ (eulerFlag t y r) (Euler.eulerFirst t y r) (stageScale SZ delta)
      (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag) := by
  obtain ⟨lam, mu, geometry, budget, hframe, -⟩ :=
    exists_packet_frame P hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
  exact shared_cost_at_of_contracts P hp SZ _ _ _ _ _ _ lam mu geometry budget hframe
    (Euler.first_cut_pairE P hp SZ SP SQ (by have := packet_t_le P; omega) hZd hcop delta hd hdchar
      hP hQ hz hu lam mu hframe.lam_mem hframe.mu_mem geometry hframe.value _)
    (xContracts_euler P hp SZ hZd hr _ _ _ _)
theorem regular_pair_packet_countRE
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ SP SQ : MovingFiberThreeSources6811.Source P.F) (delta : ℕ) (hd : 0 < delta)
    (hR : SharedCostAt P hp SZ (eulerFlag t y r) (Euler.eulerFirst t y r) (stageScale SZ delta)
      (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag))
    (hgood : ∀ gamma ∈ P.seeds,
      MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (SZ.leading (RCN135.polynomialEmbedding K)) ≠ 0) :
    P.seeds.card ≤ pairStageCostRE SZ SP SQ delta t y r ⟨t - y, y - r, r⟩ :=
  packet_count_at P hp SZ (eulerFlag t y r) (Nat.le_add_left 1 (y - r)) _ _ _ _ _
    (Nat.mul_pos (Nat.succ_pos _) hd) hR hgood
theorem packet_count_of_regular
    (P : Packet x t y r) (S : MovingFiberThreeSources6811.Source P.F) (hFT : S.T < wt RCN156.residualTotalWeights P.F)
    (hgates : ER.Gates t y r (S.B - 2 * S.n0) (S.U - S.n0) (S.T - S.n0)) (N : ℕ)
    (hregular : ∀ (good : Finset K) (hsub : good ⊆ P.seeds), ¬P.F ∣ numerator K P.F (w + 1) →
      (∀ gamma ∈ good, MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (S.leading (RCN135.polynomialEmbedding K)) ≠ 0) →
      (P.restrict good hsub).seeds.card ≤ N) :
    P.seeds.card ≤ max (EF.MG t y r) (N + ER.leadingPrice S t y r) := by
  by_cases hp : P.F ∣ numerator K P.F (w + 1)
  · exact (EF.CNE P hp).trans (le_max_left _ _)
  let good := P.seeds.filter (fun gamma =>
    MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (S.leading (RCN135.polynomialEmbedding K)) ≠ 0)
  let bad := P.seeds.filter (fun gamma =>
    MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (S.leading (RCN135.polynomialEmbedding K)) = 0)
  have hmain : good.card ≤ N :=
    hregular good (Finset.filter_subset _ _) hp (fun gamma hg => (Finset.mem_filter.mp hg).2)
  have hbad : bad.card ≤ ER.leadingPrice S t y r := ER.DOU P S hFT hgates
  have hpartition : P.seeds.card = good.card + bad.card := by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hmain hbad).trans (le_max_right _ _)
theorem pair_packet_countRE
    (P : Packet x t y r) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F)
    (hFT : SZ.T < wt RCN156.residualTotalWeights P.F) (hZd : SZ.k < 2130706433)
    (hgates : ER.Gates t y r (SZ.B - 2 * SZ.n0) (SZ.U - SZ.n0) (SZ.T - SZ.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433)
    (hr : 5 ≤ r) :
    P.seeds.card ≤ max (EF.MG t y r)
      (pairStageCostRE SZ SP SQ delta t y r ⟨t - y, y - r, r⟩ + ER.leadingPrice SZ t y r) :=
  packet_count_of_regular P SZ hFT hgates _ fun good hsub hp hgood =>
    regular_pair_packet_countRE (P.restrict good hsub) hp SZ SP SQ delta hd
      (shared_RE_cost (P.restrict good hsub) hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu hr) hgood
theorem native_regular_countRE
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (S : MovingFiberThreeSources6811.Source P.F)
    (hk : S.k < 2130706433) (hr : 5 ≤ r)
    (hgood : ∀ gamma ∈ P.seeds,
      MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) P.selected gamma) (S.leading (RCN135.polynomialEmbedding K)) ≠ 0) :
    P.seeds.card ≤ numeratorRE S.d S.d (flagMixed ⟨t - y, y - r, r⟩ unitZFlag S.flag)
      (flagMixed ⟨t - y, y - r, r⟩ unitYZFlag S.flag)
      (flagMixed ⟨t - y, y - r, r⟩ unitAllFlag S.flag) t y r ⟨t - y, y - r, r⟩ S.flag /
        (9 * S.d * S.d) := by
  obtain ⟨lam, mu, geometry, budget, hframe⟩ := Native.exists_packet_frame P hp S hk
  exact packet_count_at P hp S (eulerFlag t y r) (Nat.le_add_left 1 (y - r)) _ S.d _ _ _ (Nat.succ_pos _)
    (shared_cost_euler_of_frame P hp S hk hr _ _ _ _ lam mu geometry budget hframe
      (fun Q U _ hQ hU => Native.packet_point_budget (algebraMap Ω Ext) P S hk Q U hQ hU)) hgood
theorem native_packet_countRE
    (P : Packet x t y r) (S : MovingFiberThreeSources6811.Source P.F) (hk : S.k < 2130706433) (hFT : S.T < wt RCN156.residualTotalWeights P.F)
    (hgates : ER.Gates t y r (S.B - 2 * S.n0) (S.U - S.n0) (S.T - S.n0)) (hr : 5 ≤ r) :
    P.seeds.card ≤ max (EF.MG t y r)
      (numeratorRE S.d S.d (flagMixed ⟨t - y, y - r, r⟩ unitZFlag S.flag)
        (flagMixed ⟨t - y, y - r, r⟩ unitYZFlag S.flag)
        (flagMixed ⟨t - y, y - r, r⟩ unitAllFlag S.flag) t y r ⟨t - y, y - r, r⟩ S.flag /
          (9 * S.d * S.d) + ER.leadingPrice S t y r) :=
  packet_count_of_regular P S hFT hgates _ fun good hsub hp hgood =>
    native_regular_countRE (P.restrict good hsub) hp S hk hr hgood
end
end Euler
end Cut
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Cut
section Leaf
noncomputable section
open scoped Classical BigOperators
open RCN074 RCN086 RCN095 RCN135 RCN156 RCN199 RCN222 RCN234 RCN238 RCN243 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open FA BD DU BOE AYR AFA TW CB HFreeDir6813 RL
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
def nativeRE (d : ℕ) (S : FlagDegree) (t y r : ℕ) : ℕ :=
  numeratorRE d d (flagMixed ⟨t - y, y - r, r⟩ unitZFlag S) (flagMixed ⟨t - y, y - r, r⟩ unitYZFlag S)
    (flagMixed ⟨t - y, y - r, r⟩ unitAllFlag S) t y r ⟨t - y, y - r, r⟩ S
def pairCostRE (d : ℕ) (S : FlagDegree) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  numeratorRE d (d * delta) (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag S)
    (d * flagMixed p q unitYZFlag) (d * flagMixed p q unitAllFlag) t y r ⟨t - y, y - r, r⟩ S /
      (9 * d * (d * delta))
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
omit [CharP K 2130706433] in
theorem stageCostRE_le {F : MvPolynomial (Fin 4) K} (SZ SP SQ : MovingFiberThreeSources6811.Source F) (delta : ℕ)
    (p q : FlagDegree) (t y r : ℕ)
    (hp : GF.CumulativeLe (ordinaryFlag SP.P) p) (hq : GF.CumulativeLe (ordinaryFlag SQ.P) q) :
    pairStageCostRE SZ SP SQ delta t y r ⟨t - y, y - r, r⟩ ≤ pairCostRE SZ.d SZ.flag delta p q t y r := by
  unfold pairStageCostRE stageScale pairCostRE
  apply Nat.div_le_div_right
  have hu := GF.CAB _ _ _ _ unitYZFlag hp hq
  have hv := GF.CAB _ _ _ _ unitAllFlag hp hq
  simp only [numeratorRE, priceNumerator, price]
  gcongr
theorem pair_leaf_countRE
    (P : Packet x t y r) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F)
    (hFT : SZ.T < wt RCN156.residualTotalWeights P.F) (hk : SZ.k < 2130706433)
    (hg : ER.Gates t y r (SZ.B - 2 * SZ.n0) (SZ.U - SZ.n0) (SZ.T - SZ.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hchar : delta ≤ 2130706433)
    (hSP : delta ≤ SP.d) (hSQ : delta ≤ SQ.d)
    (p q : FlagDegree) (hp : GF.CumulativeLe (ordinaryFlag SP.P) p)
    (hq : GF.CumulativeLe (ordinaryFlag SQ.P) q)
    (hz : flagMixed p q unitZFlag < 2130706433)
    (hu : flagMixed p q unitYZFlag < 2130706433)
    (hr : 5 ≤ r) :
    P.seeds.card ≤ max (EF.MG t y r)
      (pairCostRE SZ.d SZ.flag delta p q t y r + ER.leadingPrice SZ t y r) :=
  (pair_packet_countRE P SZ SP SQ hFT hk hg hcop delta hd hchar hSP hSQ
    ((GF.CAB _ _ _ _ unitZFlag hp hq).trans_lt hz) ((GF.CAB _ _ _ _ unitYZFlag hp hq).trans_lt hu)
    hr).trans
    (max_le_max le_rfl (Nat.add_le_add_right (stageCostRE_le SZ SP SQ delta p q t y r hp hq) _))
theorem native_leaf_countRE
    (P : Packet x t y r) (S : MovingFiberThreeSources6811.Source P.F) (hk : S.k < 2130706433) (hFT : S.T < wt RCN156.residualTotalWeights P.F)
    (hgates : ER.Gates t y r (S.B - 2 * S.n0) (S.U - S.n0) (S.T - S.n0)) (hr : 5 ≤ r) :
    P.seeds.card ≤ max (EF.MG t y r)
      (nativeRE S.d S.flag t y r / (9 * S.d * S.d) + ER.leadingPrice S t y r) :=
  native_packet_countRE P S hk hFT hgates hr
end
end Leaf
end Cut
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Count
open MvPolynomial
def boxCount (ρ θ : ℕ) : ℕ :=
  (θ + 3).choose 3 - (θ - ρ + 2).choose 3
theorem choose_three (m : ℕ) : (m + 2).choose 3 = m * (m + 1) * (m + 2) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.descFactorial_succ, Nat.descFactorial_zero, show Nat.factorial 3 = 6 from rfl,
    show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega, Nat.sub_zero, mul_one, ← mul_assoc]
theorem boxCount_eq (ρ θ : ℕ) :
    boxCount ρ θ =
      (θ + 1) * (θ + 2) * (θ + 3) / 6 - (θ - ρ) * (θ - ρ + 1) * (θ - ρ + 2) / 6 := by
  rw [boxCount, ← choose_three (θ - ρ)]
  exact congrArg (· - (θ - ρ + 2).choose 3) (choose_three (θ + 1))
def boxExp (ρ θ : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | e 1 ≤ ρ ∧ e 0 + e 1 + e 2 ≤ θ}
def degFin (d : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (Finset.range (d + 1)).biUnion fun n => (Finset.univ : Finset (Fin 3)).finsuppAntidiag n
theorem mem_degFin {d : ℕ} {e : Fin 3 →₀ ℕ} : e ∈ degFin d ↔ e 0 + e 1 + e 2 ≤ d := by
  simp only [degFin, Finset.mem_biUnion, Finset.mem_range, Finset.mem_finsuppAntidiag,
    Finset.subset_univ, and_true, Fin.sum_univ_three]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    exact ⟨_, by omega, rfl⟩
theorem card_degFin (d : ℕ) : (degFin d).card = (d + 3).choose 3 := by
  rw [degFin, Finset.card_biUnion]
  · simp only [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
    calc ∑ n ∈ Finset.range (d + 1), (3 + n - 1).choose n
        = ∑ n ∈ Finset.range (d + 1), (n + 2).choose 2 := Finset.sum_congr rfl fun n _ => by
          rw [show 3 + n - 1 = n + 2 by omega, Nat.choose_symm_add]
      _ = (d + 3).choose 3 := Nat.sum_range_add_choose d 2
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun e ha hb => hab ?_
    rw [Finset.mem_finsuppAntidiag] at ha hb
    exact ha.1.symm.trans hb.1
theorem card_filter_not_le (ρ θ : ℕ) :
    ((degFin θ).filter fun e => ¬e 1 ≤ ρ).card = (θ - ρ + 2).choose 3 := by
  rcases Nat.lt_or_ge ρ θ with h | h
  · have key : ((degFin θ).filter fun e => ¬e 1 ≤ ρ).card = (degFin (θ - (ρ + 1))).card := by
      refine Finset.card_nbij' (fun e => e - Finsupp.single 1 (ρ + 1))
        (fun e => e + Finsupp.single 1 (ρ + 1)) ?_ ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_coe, Finset.mem_filter, mem_degFin] at he
        rw [Finset.mem_coe, mem_degFin]
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, Fin.isValue, one_ne_zero,
          ↓reduceIte, tsub_zero, Fin.reduceEq]
        omega
      · intro e he
        rw [Finset.mem_coe, mem_degFin] at he
        rw [Finset.mem_coe, Finset.mem_filter, mem_degFin]
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Fin.isValue, one_ne_zero,
          ↓reduceIte, add_zero, Fin.reduceEq, not_le]
        omega
      · intro e he
        rw [Finset.mem_coe, Finset.mem_filter] at he
        exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))
      · intro e _
        exact add_tsub_cancel_right _ _
    rw [key, card_degFin]
    congr 1
    omega
  · rw [Finset.filter_eq_empty_iff.mpr, Finset.card_empty, show θ - ρ + 2 = 2 by omega]
    · rfl
    · intro e he
      rw [mem_degFin] at he
      omega
def boxFin (ρ θ : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (degFin θ).filter fun e => e 1 ≤ ρ
theorem coe_boxFin (ρ θ : ℕ) : (boxFin ρ θ : Set (Fin 3 →₀ ℕ)) = boxExp ρ θ := by
  ext e
  rw [Finset.mem_coe, boxFin, Finset.mem_filter, mem_degFin]
  exact and_comm
theorem card_boxFin (ρ θ : ℕ) : (boxFin ρ θ).card = boxCount ρ θ := by
  have h := Finset.card_filter_add_card_filter_not (s := degFin θ) (fun e => e 1 ≤ ρ)
  rw [card_filter_not_le, card_degFin] at h
  rw [boxFin, boxCount]
  omega
theorem finite_boxExp (ρ θ : ℕ) : (boxExp ρ θ).Finite := by
  rw [← coe_boxFin]
  exact Finset.finite_toSet _
theorem ncard_boxExp (ρ θ : ℕ) : (boxExp ρ θ).ncard = boxCount ρ θ := by
  rw [← coe_boxFin, Set.ncard_coe_finset, card_boxFin]
theorem boxCount_mono {ρ₁ ρ₂ θ₁ θ₂ : ℕ} (hρ : ρ₁ ≤ ρ₂) (hθ : θ₁ ≤ θ₂) :
    boxCount ρ₁ θ₁ ≤ boxCount ρ₂ θ₂ := by
  rw [← ncard_boxExp, ← ncard_boxExp]
  exact Set.ncard_le_ncard (fun e he => ⟨he.1.trans hρ, he.2.trans hθ⟩) (finite_boxExp ρ₂ θ₂)
variable (k : Type*) [Field k]
noncomputable def box (ρ θ : ℕ) : Submodule k (MvPolynomial (Fin 3) k) :=
  restrictSupport k (boxExp ρ θ)
variable {k}
theorem mem_box_iff_support {ρ θ : ℕ} {p : MvPolynomial (Fin 3) k} :
    p ∈ box k ρ θ ↔ ∀ e ∈ p.support, e 1 ≤ ρ ∧ e 0 + e 1 + e 2 ≤ θ :=
  Iff.rfl
theorem mem_box_iff {ρ θ : ℕ} {p : MvPolynomial (Fin 3) k} :
    p ∈ box k ρ θ ↔ p.degreeOf 1 ≤ ρ ∧ p.totalDegree ≤ θ := by
  have hsum : ∀ e : Fin 3 →₀ ℕ, (e.sum fun _ n => n) = e 0 + e 1 + e 2 := fun e => by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_three]
  rw [mem_box_iff_support, degreeOf_le_iff, totalDegree, Finset.sup_le_iff]
  refine ⟨fun h => ⟨fun e he => (h e he).1, fun e he => ?_⟩, fun h e he => ⟨h.1 e he, ?_⟩⟩
  · rw [hsum]
    exact (h e he).2
  · rw [← hsum]
    exact h.2 e he
variable (k)
theorem finite_box (ρ θ : ℕ) : Module.Finite k (box k ρ θ) :=
  have := (finite_boxExp ρ θ).to_subtype
  Module.Finite.of_basis (basisRestrictSupport k (boxExp ρ θ))
theorem finrank_box (ρ θ : ℕ) : Module.finrank k (box k ρ θ) = boxCount ρ θ := by
  rw [box, Module.finrank_eq_nat_card_basis (basisRestrictSupport k (boxExp ρ θ)), Nat.card_coe_set_eq,
    ncard_boxExp]
variable {k}
theorem mul_mem_box_iff {F H : MvPolynomial (Fin 3) k} (hF : F ≠ 0) (hH : H ≠ 0) {ρ θ : ℕ} :
    H * F ∈ box k ρ θ ↔
      F.degreeOf 1 ≤ ρ ∧ F.totalDegree ≤ θ ∧ H ∈ box k (ρ - F.degreeOf 1) (θ - F.totalDegree) := by
  rw [mem_box_iff, mem_box_iff, degreeOf_mul_eq hH hF, totalDegree_mul_of_isDomain hH hF]
  omega
theorem finrank_map_box {M : Type*} [AddCommGroup M] [Module k M]
    (φ : MvPolynomial (Fin 3) k →ₗ[k] M) {F : MvPolynomial (Fin 3) k} (hF : F ≠ 0)
    (hφ : ∀ p, φ p = 0 ↔ F ∣ p) (ρ θ : ℕ) :
    Module.finrank k (Submodule.map φ (box k ρ θ)) =
      boxCount ρ θ - if F.degreeOf 1 ≤ ρ ∧ F.totalDegree ≤ θ then
        boxCount (ρ - F.degreeOf 1) (θ - F.totalDegree) else 0 := by
  have := finite_box k ρ θ
  have hsum := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict (box k ρ θ))
  rw [LinearMap.range_domRestrict, finrank_box] at hsum
  split_ifs with hfit
  · let ψ : box k (ρ - F.degreeOf 1) (θ - F.totalDegree) →ₗ[k] box k ρ θ :=
      ((LinearMap.mulRight k F).comp (box k (ρ - F.degreeOf 1) (θ - F.totalDegree)).subtype).codRestrict
        (box k ρ θ) fun H => by
          rcases eq_or_ne (H : MvPolynomial (Fin 3) k) 0 with h0 | h0
          · simp [h0]
          · exact (mul_mem_box_iff hF h0).mpr ⟨hfit.1, hfit.2, H.2⟩
    have hψ : Function.Injective ψ := fun H₁ H₂ h => by
      have h' : (H₁ : MvPolynomial (Fin 3) k) * F = H₂ * F := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hF h')
    have hker : LinearMap.ker (φ.domRestrict (box k ρ θ)) = LinearMap.range ψ := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, hφ, LinearMap.mem_range]
      constructor
      · rintro ⟨H, hH⟩
        rcases eq_or_ne H 0 with h0 | h0
        · exact ⟨0, Subtype.ext (by rw [hH, h0, mul_zero, map_zero]; rfl)⟩
        · have hmem : H * F ∈ box k ρ θ := by
            rw [mul_comm, ← hH]
            exact x.2
          refine ⟨⟨H, ((mul_mem_box_iff hF h0).mp hmem).2.2⟩, Subtype.ext ?_⟩
          change H * F = (x : MvPolynomial (Fin 3) k)
          rw [hH, mul_comm]
      · rintro ⟨H, rfl⟩
        exact ⟨H, mul_comm _ _⟩
    rw [hker, LinearMap.finrank_range_of_inj hψ, finrank_box] at hsum
    omega
  · have hker : LinearMap.ker (φ.domRestrict (box k ρ θ)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      rw [LinearMap.domRestrict_apply, hφ] at hx
      obtain ⟨H, hH⟩ := hx
      by_contra hx0
      have h0 : H ≠ 0 := fun h0 => hx0 (Subtype.ext (by rw [hH, h0, mul_zero]; rfl))
      have hmem : H * F ∈ box k ρ θ := by
        rw [mul_comm, ← hH]
        exact x.2
      exact hfit ⟨((mul_mem_box_iff hF h0).mp hmem).1, ((mul_mem_box_iff hF h0).mp hmem).2.1⟩
    rw [hker, finrank_bot] at hsum
    omega
theorem mkₐ_eq_zero_iff (F p : MvPolynomial (Fin 3) k) :
    (Ideal.Quotient.mkₐ k (Ideal.span {F})).toLinearMap p = 0 ↔ F ∣ p := by
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
theorem boxCount_sub_ite_le_finrank_map_box {M : Type*} [AddCommGroup M] [Module k M]
    (φ : MvPolynomial (Fin 3) k →ₗ[k] M) {F : MvPolynomial (Fin 3) k} (hF : F ≠ 0)
    (hφ : ∀ p, φ p = 0 ↔ F ∣ p) {ρ θ r t : ℕ} (hr : r ≤ F.degreeOf 1) (ht : t ≤ F.totalDegree) :
    (boxCount ρ θ - if r ≤ ρ ∧ t ≤ θ then boxCount (ρ - r) (θ - t) else 0) ≤
      Module.finrank k (Submodule.map φ (box k ρ θ)) := by
  rw [finrank_map_box φ hF hφ]
  split_ifs
  · exact Nat.sub_le_sub_left (boxCount_mono (by omega) (by omega)) _
  · omega
  · omega
  · exact le_rfl
end H2Count
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
namespace Fibre
section Away
variable {k : Type*} [Field k]
theorem isUnit_algebraMap_powers {h : Polynomial k} (hh : h ≠ 0) (y : Submonoid.powers h) :
    IsUnit (algebraMap (Polynomial k) (RatFunc k) y) := by
  obtain ⟨_, j, rfl⟩ := y
  exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr
    (pow_ne_zero j hh))
theorem isUnit_eval_powers {h : Polynomial k} {a : k} (ha : h.eval a ≠ 0) (y : Submonoid.powers h) :
    IsUnit (Polynomial.evalRingHom a y) := by
  obtain ⟨_, j, rfl⟩ := y
  refine IsUnit.mk0 _ ?_
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_pow]
  exact pow_ne_zero j ha
noncomputable def awayToRatFunc (h : Polynomial k) (hh : h ≠ 0) : Localization.Away h →+* RatFunc k :=
  IsLocalization.lift (isUnit_algebraMap_powers hh)
noncomputable def awayEval (h : Polynomial k) (a : k) (ha : h.eval a ≠ 0) : Localization.Away h →+* k :=
  IsLocalization.lift (isUnit_eval_powers ha)
theorem awayToRatFunc_algebraMap (h : Polynomial k) (hh : h ≠ 0) (r : Polynomial k) :
    awayToRatFunc h hh (algebraMap (Polynomial k) (Localization.Away h) r) =
      algebraMap (Polynomial k) (RatFunc k) r :=
  IsLocalization.lift_eq _ r
theorem awayEval_algebraMap (h : Polynomial k) (a : k) (ha : h.eval a ≠ 0) (r : Polynomial k) :
    awayEval h a ha (algebraMap (Polynomial k) (Localization.Away h) r) = r.eval a :=
  IsLocalization.lift_eq _ r
theorem awayToRatFunc_injective (h : Polynomial k) (hh : h ≠ 0) :
    Function.Injective (awayToRatFunc h hh) := by
  refine (IsLocalization.lift_injective_iff (isUnit_algebraMap_powers hh)).mpr fun r s => ?_
  rw [(IsLocalization.injective (Localization.Away h)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh)).eq_iff,
    (IsFractionRing.injective (Polynomial k) (RatFunc k)).eq_iff]
theorem mem_range_awayToRatFunc (h : Polynomial k) (hh : h ≠ 0) {c : RatFunc k}
    (hc : IsLocalization.IsInteger (Polynomial k) (h • c)) : c ∈ Set.range (awayToRatFunc h hh) := by
  obtain ⟨n, hn⟩ := hc
  refine ⟨IsLocalization.mk' (Localization.Away h) n ⟨h, Submonoid.mem_powers h⟩, ?_⟩
  have h1 := congrArg (awayToRatFunc h hh)
    (IsLocalization.mk'_spec (Localization.Away h) n ⟨h, Submonoid.mem_powers h⟩)
  rw [map_mul, awayToRatFunc_algebraMap, awayToRatFunc_algebraMap] at h1
  have h2 : algebraMap (Polynomial k) (RatFunc k) h ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hh
  rw [hn, Algebra.smul_def] at h1
  exact mul_right_cancel₀ h2 (h1.trans (mul_comm _ _))
theorem exists_map_awayToRatFunc_eq (h : Polynomial k) (hh : h ≠ 0) (f : Polynomial (RatFunc k))
    (hf : ∀ c ∈ f.coeffs, IsLocalization.IsInteger (Polynomial k) (h • c)) :
    ∃ g : Polynomial (Localization.Away h), g.map (awayToRatFunc h hh) = f := by
  refine (Polynomial.mem_lifts f).mp ((Polynomial.lifts_iff_coeff_lifts f).mpr fun n => ?_)
  by_cases hc : f.coeff n = 0
  · exact ⟨0, by rw [map_zero, hc]⟩
  · exact mem_range_awayToRatFunc h hh (hf _ (Polynomial.coeff_mem_coeffs hc))
end Away
section Specialize
variable {k : Type*} [Field k] {L : Type*} [Field L] [Algebra (RatFunc k) L] {B : Type*} [CommRing B]
  {σ : Type*}
theorem eval_map_eq_zero_of_aeval_map_eq_zero {ψ : B →+* RatFunc k} (hψ : Function.Injective ψ)
    (ev : B →+* k) {α : L} {μ : Polynomial B} (hμ : μ.Monic)
    (hμα : μ.map ψ = minpoly (RatFunc k) α) {N : Polynomial B}
    (hN : Polynomial.aeval α (N.map ψ) = 0) {t : k} (ht : (μ.map ev).eval t = 0) :
    (N.map ev).eval t = 0 := by
  have h1 : μ.map ψ ∣ N.map ψ := hμα ▸ minpoly.dvd (RatFunc k) α hN
  obtain ⟨Q, rfl⟩ := (Polynomial.map_dvd_map ψ hψ hμ).mp h1
  rw [Polynomial.map_mul, Polynomial.eval_mul, ht, zero_mul]
theorem aeval_map_eval₂Hom [Algebra k L] [IsScalarTower k (RatFunc k) L] (ι : k →+* B)
    (ψ : B →+* RatFunc k) (hι : ψ.comp ι = algebraMap k (RatFunc k)) (α : L) (x : σ → L)
    (G : σ → Polynomial B) (hG : ∀ i, Polynomial.aeval α ((G i).map ψ) = x i)
    (g : MvPolynomial σ k) :
    Polynomial.aeval α ((MvPolynomial.eval₂Hom (Polynomial.C.comp ι) G g).map ψ) =
      MvPolynomial.aeval x g := by
  have h : ((Polynomial.aeval α : Polynomial (RatFunc k) →ₐ[RatFunc k] L).toRingHom.comp
      (Polynomial.mapRingHom ψ)).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp ι) G) =
      (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] L).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C,
        MvPolynomial.aeval_C]
      rw [← RingHom.comp_apply ψ ι, hι, ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_mapRingHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      exact hG i
  exact RingHom.congr_fun h g
theorem eval_map_eval₂Hom (ι : k →+* B) (ev : B →+* k) (hι : ev.comp ι = RingHom.id k)
    (G : σ → Polynomial B) (t : k) (g : MvPolynomial σ k) :
    ((MvPolynomial.eval₂Hom (Polynomial.C.comp ι) G g).map ev).eval t =
      MvPolynomial.eval (fun i => ((G i).map ev).eval t) g := by
  have h : ((Polynomial.evalRingHom t).comp (Polynomial.mapRingHom ev)).comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp ι) G) =
      MvPolynomial.eval (fun i => ((G i).map ev).eval t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C, MvPolynomial.eval_C]
      rw [← RingHom.comp_apply ev ι, hι, RingHom.id_apply]
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_mapRingHom,
        Polynomial.coe_evalRingHom, MvPolynomial.eval_X]
  exact RingHom.congr_fun h g
theorem exists_fibre_of_specialization [IsAlgClosed k] [Algebra k L] [IsScalarTower k (RatFunc k) L]
    (ι : k →+* B) (ψ : B →+* RatFunc k) (hψ : Function.Injective ψ)
    (hψι : ψ.comp ι = algebraMap k (RatFunc k)) (ev : B →+* k) (hevι : ev.comp ι = RingHom.id k)
    (XB : B) (hXB : ψ XB = RatFunc.X) (a : k) (hXa : ev XB = a) (α : L) (μ : Polynomial B)
    (hμ : μ.Monic) (hμα : μ.map ψ = minpoly (RatFunc k) α) (hsep : μ.Separable) (x : σ → L)
    (G : σ → Polynomial B) (hG : ∀ i, Polynomial.aeval α ((G i).map ψ) = x i)
    (p q : MvPolynomial σ k) (hq : MvPolynomial.aeval x q ≠ 0)
    (hpq : α * MvPolynomial.aeval x q = MvPolynomial.aeval x p) (W : Polynomial B)
    (hW : Polynomial.aeval α (W.map ψ) = (MvPolynomial.aeval x q)⁻¹) (F : MvPolynomial σ k)
    (hF : algebraMap (RatFunc k) L RatFunc.X = MvPolynomial.aeval x F) (g : MvPolynomial σ k)
    (hg : MvPolynomial.aeval x g ≠ 0) (V : Polynomial B)
    (hV : Polynomial.aeval α (V.map ψ) = (MvPolynomial.aeval x g)⁻¹) :
    ∃ S : Finset (σ → k), S.card = (minpoly (RatFunc k) α).natDegree ∧
      ∀ pt ∈ S, (∀ r : MvPolynomial σ k, MvPolynomial.aeval x r = 0 → MvPolynomial.eval pt r = 0) ∧
        MvPolynomial.eval pt F = a ∧ MvPolynomial.eval pt g ≠ 0 := by
  classical
  let Φ := MvPolynomial.eval₂Hom (Polynomial.C.comp ι) G
  let pt : k → σ → k := fun t i => ((G i).map ev).eval t
  have key : ∀ N : Polynomial B, Polynomial.aeval α (N.map ψ) = 0 → ∀ t,
      (μ.map ev).eval t = 0 → (N.map ev).eval t = 0 :=
    fun N hN t ht => eval_map_eq_zero_of_aeval_map_eq_zero hψ ev hμ hμα hN ht
  have hΦα : ∀ r, Polynomial.aeval α ((Φ r).map ψ) = MvPolynomial.aeval x r :=
    aeval_map_eval₂Hom ι ψ hψι α x G hG
  have hΦt : ∀ t r, ((Φ r).map ev).eval t = MvPolynomial.eval (pt t) r :=
    fun t r => eval_map_eval₂Hom ι ev hevι G t r
  have hrel : ∀ t, (μ.map ev).eval t = 0 → ∀ r, MvPolynomial.aeval x r = 0 →
      MvPolynomial.eval (pt t) r = 0 := by
    intro t ht r hr
    rw [← hΦt]
    exact key _ (by rw [hΦα, hr]) t ht
  have hval : ∀ t, (μ.map ev).eval t = 0 → MvPolynomial.eval (pt t) F = a := by
    intro t ht
    have h1 := key (Φ F - Polynomial.C XB) (by
      rw [Polynomial.map_sub, map_sub, hΦα, Polynomial.map_C, Polynomial.aeval_C, hXB, hF, sub_self]) t ht
    rw [Polynomial.map_sub, Polynomial.eval_sub, hΦt, Polynomial.map_C, Polynomial.eval_C, hXa,
      sub_eq_zero] at h1
    exact h1
  have hinv : ∀ (r : MvPolynomial σ k) (R : Polynomial B), MvPolynomial.aeval x r ≠ 0 →
      Polynomial.aeval α (R.map ψ) = (MvPolynomial.aeval x r)⁻¹ → ∀ t, (μ.map ev).eval t = 0 →
        MvPolynomial.eval (pt t) r ≠ 0 := by
    intro r R hr hR t ht
    have h1 := key (Φ r * R - 1) (by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, map_sub, map_mul, map_one, hΦα,
        hR, mul_inv_cancel₀ hr, sub_self]) t ht
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_one, hΦt, sub_eq_zero] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hgen : ∀ t, (μ.map ev).eval t = 0 →
      t * MvPolynomial.eval (pt t) q = MvPolynomial.eval (pt t) p := by
    intro t ht
    have h1 := key (Polynomial.X * Φ q - Φ p) (by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, map_sub, map_mul,
        Polynomial.aeval_X, hΦα, hΦα, hpq, sub_self]) t ht
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X, hΦt, hΦt, sub_eq_zero] at h1
    exact h1
  have hinj : ∀ t, (μ.map ev).eval t = 0 → ∀ t', (μ.map ev).eval t' = 0 → pt t = pt t' → t = t' := by
    intro t ht t' ht' htt'
    have h1 := hgen t ht
    have h2 := hgen t' ht'
    rw [← htt'] at h2
    exact mul_right_cancel₀ (hinv q W hq hW t ht) (h1.trans h2.symm)
  have hcard : (μ.map ev).roots.toFinset.card = (minpoly (RatFunc k) α).natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep.map),
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hμ.natDegree_map ev, ← hμα,
      hμ.natDegree_map ψ]
  have hroot : ∀ t ∈ (μ.map ev).roots.toFinset, (μ.map ev).eval t = 0 := fun t ht =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ht)
  refine ⟨(μ.map ev).roots.toFinset.image pt, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn fun t ht t' ht' h => hinj t (hroot t ht) t' (hroot t' ht') h, hcard]
  · intro P hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hrel t (hroot t ht), hval t (hroot t ht), hinv g V hg hV t (hroot t ht)⟩
end Specialize
end Fibre
section Main
variable (k : Type*) [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ]
theorem finite_setOf_not_exists_fibre_off {L : Type*} [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] (x : σ → L)
    (hx : ∀ z : L, ∃ p q : MvPolynomial σ k, MvPolynomial.aeval x q ≠ 0 ∧
      z * MvPolynomial.aeval x q = MvPolynomial.aeval x p)
    (F : MvPolynomial σ k) (hF : algebraMap (RatFunc k) L RatFunc.X = MvPolynomial.aeval x F)
    (g : MvPolynomial σ k) (hg : MvPolynomial.aeval x g ≠ 0) :
    {a : k | ¬∃ S : Finset (σ → k), S.card = Module.finrank (RatFunc k) L ∧
      ∀ p ∈ S, (∀ r : MvPolynomial σ k, MvPolynomial.aeval x r = 0 → MvPolynomial.eval p r = 0) ∧
        MvPolynomial.eval p F = a ∧ MvPolynomial.eval p g ≠ 0}.Finite := by
  classical
  cases nonempty_fintype σ
  let pb := Field.powerBasisOfFiniteOfSeparable (RatFunc k) L
  have hdeg : (minpoly (RatFunc k) pb.gen).natDegree = Module.finrank (RatFunc k) L := by
    rw [pb.natDegree_minpoly, pb.finrank]
  obtain ⟨u, v, huv⟩ := Algebra.IsSeparable.isSeparable (RatFunc k) pb.gen
  choose G hG using fun i => pb.exists_eq_aeval' (x i)
  obtain ⟨p, q, hq, hpq⟩ := hx pb.gen
  obtain ⟨W, hW⟩ := pb.exists_eq_aeval' (MvPolynomial.aeval x q)⁻¹
  obtain ⟨V, hV⟩ := pb.exists_eq_aeval' (MvPolynomial.aeval x g)⁻¹
  obtain ⟨⟨h, hh⟩, hden⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (Polynomial k)) ((minpoly (RatFunc k) pb.gen).coeffs ∪ u.coeffs ∪ v.coeffs ∪
      W.coeffs ∪ V.coeffs ∪ Finset.univ.biUnion fun i => (G i).coeffs)
  have hh0 : h ≠ 0 := nonZeroDivisors.ne_zero hh
  refine h.roots.toFinset.finite_toSet.subset fun a ha => ?_
  by_contra hroot
  have hha : h.eval a ≠ 0 := fun h0 =>
    hroot (Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hh0).mpr h0)))
  obtain ⟨μB, hμB⟩ := Fibre.exists_map_awayToRatFunc_eq h hh0 (minpoly (RatFunc k) pb.gen) fun c hc =>
    hden c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hc)))))
  obtain ⟨uB, huB⟩ := Fibre.exists_map_awayToRatFunc_eq h hh0 u fun c hc =>
    hden c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hc)))))
  obtain ⟨vB, hvB⟩ := Fibre.exists_map_awayToRatFunc_eq h hh0 v fun c hc =>
    hden c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hc))))
  obtain ⟨WB, hWB⟩ := Fibre.exists_map_awayToRatFunc_eq h hh0 W fun c hc =>
    hden c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hc)))
  obtain ⟨VB, hVB⟩ := Fibre.exists_map_awayToRatFunc_eq h hh0 V fun c hc =>
    hden c (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
  choose GB hGB using fun i => Fibre.exists_map_awayToRatFunc_eq h hh0 (G i) fun c hc =>
    hden c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩))
  have hμmon : μB.Monic := Polynomial.monic_of_injective (Fibre.awayToRatFunc_injective h hh0)
    (hμB ▸ minpoly.monic pb.isIntegral_gen)
  have hsep : μB.Separable := by
    refine ⟨uB, vB, Polynomial.map_injective _ (Fibre.awayToRatFunc_injective h hh0) ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, huB,
      hvB, hμB, Polynomial.map_one]
    exact huv
  obtain ⟨S, hS, hSp⟩ := Fibre.exists_fibre_of_specialization
    ((algebraMap (Polynomial k) (Localization.Away h)).comp Polynomial.C) (Fibre.awayToRatFunc h hh0)
    (Fibre.awayToRatFunc_injective h hh0)
    (RingHom.ext fun c => (Fibre.awayToRatFunc_algebraMap h hh0 _).trans
      (IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) c).symm)
    (Fibre.awayEval h a hha)
    (RingHom.ext fun c => (Fibre.awayEval_algebraMap h a hha _).trans Polynomial.eval_C)
    (algebraMap (Polynomial k) (Localization.Away h) Polynomial.X)
    ((Fibre.awayToRatFunc_algebraMap h hh0 _).trans RatFunc.algebraMap_X) a
    ((Fibre.awayEval_algebraMap h a hha _).trans Polynomial.eval_X) pb.gen μB hμmon hμB hsep x GB
    (fun i => by rw [hGB i, ← hG i]) p q hq hpq WB (by rw [hWB, ← hW]) F hF g hg VB
    (by rw [hVB, ← hV])
  exact ha ⟨S, hS.trans hdeg, hSp⟩
theorem finite_setOf_not_exists_zeros_off (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    [Algebra (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P))]
    [IsScalarTower k (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P))]
    [FiniteDimensional (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P))]
    [Algebra.IsSeparable (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P))]
    (F : MvPolynomial σ k)
    (hF : algebraMap (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P)) RatFunc.X =
      algebraMap (MvPolynomial σ k ⧸ P) (FractionRing (MvPolynomial σ k ⧸ P)) (Ideal.Quotient.mk P F))
    (g : MvPolynomial σ k) (hg : g ∉ P) :
    {a : k | ¬∃ S : Finset (σ → k),
      S.card = Module.finrank (RatFunc k) (FractionRing (MvPolynomial σ k ⧸ P)) ∧
        ∀ p ∈ S, (∀ r ∈ P, MvPolynomial.eval p r = 0) ∧ MvPolynomial.eval p F = a ∧
          MvPolynomial.eval p g ≠ 0}.Finite := by
  let φ : MvPolynomial σ k →ₐ[k] FractionRing (MvPolynomial σ k ⧸ P) :=
    (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ P) (FractionRing (MvPolynomial σ k ⧸ P))).comp
      (Ideal.Quotient.mkₐ k P)
  have hφ : ∀ r, MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) r =
      algebraMap (MvPolynomial σ k ⧸ P) (FractionRing (MvPolynomial σ k ⧸ P))
        (Ideal.Quotient.mk P r) := fun r =>
    (AlgHom.congr_fun (MvPolynomial.aeval_unique φ) r).symm
  have hker : ∀ r, MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) r = 0 ↔ r ∈ P := fun r => by
    rw [hφ, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial σ k ⧸ P)
      (FractionRing (MvPolynomial σ k ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]
  have hgen : ∀ z : FractionRing (MvPolynomial σ k ⧸ P), ∃ p q : MvPolynomial σ k,
      MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) q ≠ 0 ∧
        z * MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) q =
          MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) p := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k ⧸ P) z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hq : algebraMap (MvPolynomial σ k ⧸ P) (FractionRing (MvPolynomial σ k ⧸ P))
        (Ideal.Quotient.mk P q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ k ⧸ P)
        (FractionRing (MvPolynomial σ k ⧸ P)))).mpr (nonZeroDivisors.ne_zero hb)
    refine ⟨p, q, by rwa [hφ], ?_⟩
    rw [hφ, hφ, div_mul_cancel₀ _ hq]
  refine (finite_setOf_not_exists_fibre_off k (fun i => φ (MvPolynomial.X i)) hgen F
    (hF.trans (hφ F).symm) g fun h0 => hg ((hker g).mp h0)).subset fun a ha hS => ha ?_
  obtain ⟨S, hS, hSp⟩ := hS
  exact ⟨S, hS, fun p hp => ⟨fun r hr => (hSp p hp).1 r ((hker r).mpr hr), (hSp p hp).2⟩⟩
end Main
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
namespace CurveH2
open RCN135 RCN136
noncomputable section
section Contraction
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K L : Type} [Field K] [Field L]
theorem surfaceMap_comp {M : Type} [Field M] (g : L →+* M) (φ : Polynomial K →+* L)
    (B : MvPolynomial (Fin 4) K) :
    surfaceMap (g.comp φ) B = MvPolynomial.map g (surfaceMap φ B) := by
  simp only [surfaceMap, RingHom.comp_apply, MvPolynomial.map_map]
theorem height_comap_surfaceMap (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (P : Ideal (MvPolynomial (Fin 3) L)) [P.IsPrime] :
    (P.comap (surfaceMap φ)).height ≤ P.height := by
  let _ : Algebra (Polynomial K) L := φ.toAlgebra
  have htf : Module.IsTorsionFree (Polynomial K) L :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  have hflat : Module.Flat (MvPolynomial (Fin 3) (Polynomial K)) (MvPolynomial (Fin 3) L) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv (Polynomial K)
      (MvPolynomial (Fin 3) (Polynomial K)) L (MvPolynomial (Fin 3) L)).symm.toLinearEquiv
  let p : Ideal (MvPolynomial (Fin 3) (Polynomial K)) :=
    P.comap (algebraMap (MvPolynomial (Fin 3) (Polynomial K)) (MvPolynomial (Fin 3) L))
  have hlies : P.LiesOver p := ⟨rfl⟩
  calc (P.comap (surfaceMap φ)).height = p.height :=
        RingEquiv.height_comap (collectX K).toRingEquiv p
    _ ≤ P.height := by
        rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P]
        exact le_self_add
theorem surfaceMap_notMem (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    {F G : MvPolynomial (Fin 4) K} (hF : Irreducible F) (hFG : ¬F ∣ G)
    (q : Ideal (MvPolynomial (Fin 3) L)) [q.IsPrime] (hq : q.height ≤ 1)
    (hFq : surfaceMap φ F ∈ q) : surfaceMap φ G ∉ q := by
  intro hGq
  have hI : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
  have hle : Ideal.span {F} ≤ q.comap (surfaceMap φ) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hFq
  have hlt : Ideal.span {F} < q.comap (surfaceMap φ) :=
    lt_of_le_of_ne hle fun h => hFG (Ideal.mem_span_singleton.mp
      (h ▸ (hGq : G ∈ q.comap (surfaceMap φ))))
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 4) K)) < Ideal.span {F} :=
    bot_lt_iff_ne_bot.mpr fun h => hF.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (Ideal.span {F}).height + 1 ≤ 1 :=
    h2.trans ((height_comap_surfaceMap φ hφ q).trans hq)
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add (le_add_self.trans h1) le_rfl).trans h3
  exact absurd h4 (by decide)
end Contraction
section Point
variable {k : Type} [Field k] [IsAlgClosed k]
theorem height_le_two_of_ne_point (D : Ideal (MvPolynomial (Fin 3) k)) [hD : D.IsPrime]
    (hpt : ∀ w : Fin 3 → k,
      D ≠ RingHom.ker (MvPolynomial.aeval w : MvPolynomial (Fin 3) k →ₐ[k] k).toRingHom) :
    D.height ≤ 2 := by
  have hnmax : ¬D.IsMaximal := fun hmax => by
    obtain ⟨w, hw⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax
    exact hpt w (hw.trans (Ideal.ext fun p =>
      (MvPolynomial.mem_vanishingIdeal_singleton_iff w p).trans RingHom.mem_ker.symm))
  obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal D hD.ne_top
  have hMp := hM.isPrime
  have h4 := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne hDM fun heq => hnmax (heq ▸ hM))
  have h5 : (M.height : WithBot ℕ∞) ≤ 3 := by
    have h6 := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_fin, zero_add] at h6
  by_contra hgt
  have h6 : (2 : ℕ∞) + 1 ≤ D.height := Order.add_one_le_of_lt (not_le.mp hgt)
  have h7 : (((2 : ℕ∞) + 1 + 1 : ℕ∞) : WithBot ℕ∞) ≤ 3 :=
    (WithBot.coe_le_coe.mpr ((add_le_add h6 le_rfl).trans h4)).trans h5
  exact absurd h7 (by decide)
end Point
section Generic
variable {K E : Type} [Field K] [Field E]
def levelEval (E : Type) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) →+* MvPolynomial (Fin 3) (GenericField E) :=
  Polynomial.eval₂RingHom (MvPolynomial.map (RCN135.coefficientEmbedding E)) (MvPolynomial.C (RCN135.initialCoordinate E))
theorem surfaceMap_eq_levelEval (E : Type) [Field E] :
    surfaceMap (RCN135.polynomialEmbedding E) = (levelEval E).comp
      (MvPolynomial.finSuccEquiv E 3 :
        MvPolynomial (Fin 4) E →+* Polynomial (MvPolynomial (Fin 3) E)) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [levelEval, RCN135.coefficientEmbedding, MvPolynomial.finSuccEquiv_apply]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [levelEval, RCN135.initialCoordinate, MvPolynomial.finSuccEquiv_X_zero]
    · simp [levelEval, MvPolynomial.finSuccEquiv_X_succ]
theorem aux_notMem (f : GenericField K →+* E) {F G : MvPolynomial (Fin 4) K} (hF : Irreducible F)
    (hFG : ¬F ∣ G) (Q A : MvPolynomial (Fin 3) E)
    (D : Ideal (MvPolynomial (Fin 3) (GenericField E))) [D.IsPrime]
    (hpt : ∀ w : Fin 3 → GenericField E, D ≠ RingHom.ker (MvPolynomial.aeval w :
      MvPolynomial (Fin 3) (GenericField E) →ₐ[GenericField E] GenericField E).toRingHom)
    (hOO : WC.OO f F ∈ D) (hXC : WC.XC f F Q A ∈ D)
    (hH : surfaceMap ((RCN135.coefficientEmbedding E).comp (LF.codeMap f)) (RCN313.polyH K F) ∉ D) :
    surfaceMap ((RCN135.coefficientEmbedding E).comp (LF.codeMap f)) G ∉ D := by
  intro hG
  have hmap : ∀ B : MvPolynomial (Fin 4) K, surfaceMap ((RCN135.coefficientEmbedding E).comp (LF.codeMap f)) B =
      MvPolynomial.map (RCN135.coefficientEmbedding E) (surfaceMap (LF.codeMap f) B) := surfaceMap_comp (RCN135.coefficientEmbedding E) (LF.codeMap f)
  let D' : Ideal (Polynomial (MvPolynomial (Fin 3) E)) := D.comap (levelEval E)
  have hD' : D'.IsPrime := Ideal.comap_isPrime _ _
  have hD'2 : D'.height ≤ 2 := by
    have h1 : (D'.comap (MvPolynomial.finSuccEquiv E 3).toRingEquiv).height = D'.height :=
      RingEquiv.height_comap _ D'
    have h2 : D'.comap (MvPolynomial.finSuccEquiv E 3).toRingEquiv =
        D.comap (surfaceMap (RCN135.polynomialEmbedding E)) := by
      rw [surfaceMap_eq_levelEval]
      rfl
    rw [← h1, h2]
    exact (height_comap_surfaceMap (RCN135.polynomialEmbedding E) (RCN135.polynomialEmbedding_injective E) D).trans (height_le_two_of_ne_point D hpt)
  let D0 : Ideal (MvPolynomial (Fin 3) E) := D'.comap Polynomial.C
  have hD0 : D0.IsPrime := Ideal.comap_isPrime _ _
  have hmem0 : ∀ a : MvPolynomial (Fin 3) E, a ∈ D0 ↔ MvPolynomial.map (RCN135.coefficientEmbedding E) a ∈ D := fun a => by
    change levelEval E (Polynomial.C a) ∈ D ↔ _
    rw [levelEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  have hF0 : surfaceMap (LF.codeMap f) F ∈ D0 := (hmem0 _).mpr (hmap F ▸ hOO)
  have hG0 : surfaceMap (LF.codeMap f) G ∈ D0 := (hmem0 _).mpr (hmap G ▸ hG)
  have hH0 : surfaceMap (LF.codeMap f) (RCN313.polyH K F) ∉ D0 := fun h =>
    hH (hmap _ ▸ (hmem0 _).mp h)
  have hFne : surfaceMap (LF.codeMap f) F ≠ 0 := RCN136.surfaceMap_ne_zero _ (LF.DTI f) F hF.ne_zero
  obtain ⟨q, hqmin, hqD0⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {surfaceMap (LF.codeMap f) F} ≤ D0 from
      (Ideal.span_singleton_le_iff_mem _).mpr hF0)
  have hq : q.IsPrime := hqmin.1.1
  have hFq : surfaceMap (LF.codeMap f) F ∈ q := hqmin.1.2 (Ideal.mem_span_singleton_self _)
  have hq1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin
  have hGq := surfaceMap_notMem (LF.codeMap f) (LF.DTI f) hF hFG q hq1 hFq
  have hP1 : (q.map Polynomial.C).IsPrime := (Ideal.isPrime_map_C_iff_isPrime q).mpr hq
  have hP2 : (D0.map Polynomial.C).IsPrime := (Ideal.isPrime_map_C_iff_isPrime D0).mpr hD0
  have h01 : (⊥ : Ideal (Polynomial (MvPolynomial (Fin 3) E))) < q.map Polynomial.C :=
    bot_lt_iff_ne_bot.mpr fun h => hFne (Polynomial.C_eq_zero.mp
      (Ideal.mem_bot.mp (h ▸ Ideal.mem_map_of_mem Polynomial.C hFq)))
  have h12 : q.map Polynomial.C < D0.map Polynomial.C :=
    lt_of_le_of_ne (Ideal.map_mono hqD0) fun h => hGq (by
      have h0 := Ideal.mem_map_C_iff.mp (h ▸ Ideal.mem_map_of_mem Polynomial.C hG0) 0
      rwa [Polynomial.coeff_C_zero] at h0)
  have h23 : D0.map Polynomial.C < D' :=
    lt_of_le_of_ne Ideal.map_comap_le fun h => hH0 (by
      have hp : Polynomial.C (surfaceMap (LF.codeMap f) (RCN313.polyH K F)) *
            (Polynomial.X - Polynomial.C Q) -
          Polynomial.C A * Polynomial.C (surfaceMap (LF.codeMap f) (RCN313.polyG K F)) ∈ D' := by
        change levelEval E _ ∈ D
        have h0 : levelEval E (Polynomial.C (surfaceMap (LF.codeMap f) (RCN313.polyH K F)) *
              (Polynomial.X - Polynomial.C Q) -
            Polynomial.C A * Polynomial.C (surfaceMap (LF.codeMap f) (RCN313.polyG K F))) =
            WC.XC f F Q A := by
          simp only [levelEval, map_sub, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
            Polynomial.eval₂_X, WC.XC, RCN207.movingEquation, hmap]
        rw [h0]
        exact hXC
      have h1 := Ideal.mem_map_C_iff.mp (h ▸ hp) 1
      simpa using h1)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h12
  have e3 := Ideal.height_add_one_le_of_lt_of_isPrime h23
  have e4 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    ((add_le_add ((add_le_add (le_add_self.trans e1) le_rfl).trans e2) le_rfl).trans e3).trans hD'2
  exact absurd e4 (by decide)
end Generic
end
end CurveH2
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open MvPolynomial
noncomputable section
section Descent
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {σ : Type*}
def coeffwise (μ : Ω →ₗ[k] k) : MvPolynomial σ Ω →ₗ[k] MvPolynomial σ k :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap μ ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
theorem coeff_coeffwise (μ : Ω →ₗ[k] k) (p : MvPolynomial σ Ω) (d : σ →₀ ℕ) :
    (coeffwise μ p).coeff d = μ (p.coeff d) :=
  rfl
theorem coeffwise_mul_map (μ : Ω →ₗ[k] k) (q : MvPolynomial σ Ω) (f : MvPolynomial σ k) :
    coeffwise μ (q * MvPolynomial.map (algebraMap k Ω) f) = coeffwise μ q * f := by
  classical
  ext d
  rw [coeff_coeffwise, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_coeffwise, coeff_map, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
theorem coeffwise_C_mul_map (μ : Ω →ₗ[k] k) (c : Ω) (f : MvPolynomial σ k) :
    coeffwise μ (C c * MvPolynomial.map (algebraMap k Ω) f) = C (μ c) * f := by
  classical
  rw [coeffwise_mul_map]
  congr 1
  ext d
  rw [coeff_coeffwise, coeff_C, coeff_C]
  split_ifs
  · rfl
  · exact map_zero μ
theorem coeffwise_mem (μ : Ω →ₗ[k] k) (I : Ideal (MvPolynomial σ k)) {x : MvPolynomial σ Ω}
    (hx : x ∈ I.map (MvPolynomial.map (algebraMap k Ω))) : coeffwise μ x ∈ I := by
  have h : ∀ a : MvPolynomial σ Ω, coeffwise μ (a * x) ∈ I := by
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      intro a
      rw [coeffwise_mul_map]
      exact I.mul_mem_left _ hf
    | zero =>
      intro a
      rw [mul_zero, map_zero]
      exact I.zero_mem
    | add y z _ _ hy hz =>
      intro a
      rw [mul_add, map_add]
      exact I.add_mem (hy a) (hz a)
    | smul b y _ hy =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * b)
  simpa only [one_mul] using h 1
theorem eq_zero_of_sum_mem_map (I : Ideal (MvPolynomial σ k)) {ι : Type*}
    (u : ι → MvPolynomial σ k) (h : LinearIndependent k fun i => Ideal.Quotient.mk I (u i))
    (s : Finset ι) (c : ι → Ω)
    (hc : ∑ i ∈ s, C (c i) * MvPolynomial.map (algebraMap k Ω) (u i) ∈
      I.map (MvPolynomial.map (algebraMap k Ω))) : ∀ i ∈ s, c i = 0 := by
  have hμ : ∀ μ : Ω →ₗ[k] k, ∀ i ∈ s, μ (c i) = 0 := by
    intro μ
    have h1 := coeffwise_mem μ I hc
    rw [map_sum] at h1
    simp only [coeffwise_C_mul_map] at h1
    refine linearIndependent_iff'.mp h s (fun i => μ (c i)) ?_
    rw [← (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C_mul']
    rfl
  intro i hi
  exact (Module.forall_dual_apply_eq_zero_iff k (c i)).mp fun μ => hμ μ i hi
end Descent
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Pole
open IsDedekindDomain
noncomputable section
section Field
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
def pointAt (c : K) : RCN349.FiniteNormalization K L →ₐ[K] K :=
  RCN354.chosenPointLift (FaithfulSMul.algebraMap_injective (Polynomial K) (RCN349.FiniteNormalization K L)) (Polynomial.aeval c)
omit [IsScalarTower K (RatFunc K) L] in
theorem pointAt_algebraMap (c : K) (f : Polynomial K) :
    pointAt K L c (algebraMap (Polynomial K) (RCN349.FiniteNormalization K L) f) = f.eval c := by
  have h := DFunLike.congr_fun (RCN354.chosenPointLift_spec
    (FaithfulSMul.algebraMap_injective (Polynomial K) (RCN349.FiniteNormalization K L)) (Polynomial.aeval c)) f
  rw [← Polynomial.coe_aeval_eq_eval, ← h]
  rfl
def primeAt (c : K) : HeightOneSpectrum (RCN349.FiniteNormalization K L) where
  asIdeal := RingHom.ker (pointAt K L c).toRingHom
  isPrime := (RCN354.pointKernel_isMaximal (pointAt K L c)).isPrime
  ne_bot := fun h => by
    have hmem : algebraMap (Polynomial K) (RCN349.FiniteNormalization K L) (Polynomial.X - Polynomial.C c) ∈
        RingHom.ker (pointAt K L c).toRingHom := by
      change pointAt K L c _ = 0
      rw [pointAt_algebraMap, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [h, Ideal.mem_bot] at hmem
    exact Polynomial.X_sub_C_ne_zero c (FaithfulSMul.algebraMap_injective (Polynomial K)
      (RCN349.FiniteNormalization K L) (hmem.trans (map_zero _).symm))
def placeAt (c : K) : RCN026.Place_p19 K L :=
  RCN345.chartMap_p19 K L (Sum.inl (primeAt K L c))
theorem placeAt_parameter_lt_one (c : K) :
    (placeAt K L c).val (algebraMap (Polynomial K) L (Polynomial.X - Polynomial.C c)) < 1 := by
  change (primeAt K L c).valuation L _ < 1
  rw [IsScalarTower.algebraMap_apply (Polynomial K) (RCN349.FiniteNormalization K L) L,
    HeightOneSpectrum.valuation_lt_one_iff_mem]
  change pointAt K L c _ = 0
  rw [pointAt_algebraMap, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
theorem placeAt_injective : Function.Injective (placeAt K L) := by
  intro c c' h
  by_contra hne
  have h1 := placeAt_parameter_lt_one K L c
  have h2 := placeAt_parameter_lt_one K L c'
  rw [← h] at h2
  have h3 : (placeAt K L c).val (algebraMap K L (c' - c)) < 1 := by
    have heq : algebraMap K L (c' - c) =
        algebraMap (Polynomial K) L (Polynomial.X - Polynomial.C c) -
          algebraMap (Polynomial K) L (Polynomial.X - Polynomial.C c') := by
      rw [← map_sub, IsScalarTower.algebraMap_apply K (Polynomial K) L]
      congr 1
      rw [Polynomial.algebraMap_eq, map_sub]
      ring
    rw [heq]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt h1 h2)
  rw [(placeAt K L c).property.2.eq_one _ (sub_ne_zero.mpr (Ne.symm hne))] at h3
  exact lt_irrefl _ h3
theorem exists_residue (c : K) (x : L) (hx : (placeAt K L c).val x ≤ 1) :
    ∃ e : K, (placeAt K L c).val (x - algebraMap K L e) < 1 := by
  change (primeAt K L c).valuation L x ≤ 1 at hx
  obtain ⟨n, d, hnd⟩ := (primeAt K L c).exists_primeCompl_mul_eq_of_integer x hx
  have hd : pointAt K L c d ≠ 0 := fun h => d.2 h
  have hd1 : (primeAt K L c).valuation L (algebraMap (RCN349.FiniteNormalization K L) L d) = 1 :=
    (primeAt K L c).valuation_eq_one_iff_notMem.mpr d.2
  have hmem : n - algebraMap K (RCN349.FiniteNormalization K L) (pointAt K L c n / pointAt K L c d) * d ∈
      (primeAt K L c).asIdeal := by
    change pointAt K L c _ = 0
    rw [map_sub, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply, div_mul_cancel₀ _ hd,
      sub_self]
  refine ⟨pointAt K L c n / pointAt K L c d, ?_⟩
  change (primeAt K L c).valuation L _ < 1
  have hlt : (primeAt K L c).valuation L (algebraMap (RCN349.FiniteNormalization K L) L
      (n - algebraMap K (RCN349.FiniteNormalization K L) (pointAt K L c n / pointAt K L c d) * d)) < 1 :=
    ((primeAt K L c).valuation_lt_one_iff_mem (K := L) _).mpr hmem
  rwa [map_sub, map_mul, ← hnd, ← IsScalarTower.algebraMap_apply K (RCN349.FiniteNormalization K L) L, ← sub_mul,
    map_mul, hd1, mul_one] at hlt
theorem exists_places (T : Finset (RCN026.Place_p19 K L)) (N : ℕ) :
    ∃ U : Finset (RCN026.Place_p19 K L), U.card = N ∧ Disjoint U T ∧
      ∀ v ∈ U, ∀ x : L, v.val x ≤ 1 → ∃ e : K, v.val (x - algebraMap K L e) < 1 := by
  obtain ⟨U, hsub, hcard⟩ := ((Set.infinite_range_of_injective (placeAt_injective K L)).sdiff
    T.finite_toSet).exists_subset_card_eq N
  refine ⟨U, hcard, Finset.disjoint_left.mpr fun v hv hvT => (hsub hv).2 hvT, fun v hv x hx => ?_⟩
  obtain ⟨c, rfl⟩ := (hsub hv).1
  exact exists_residue K L c x hx
variable {K L}
theorem poleOrder_le_iff (v : Valuation L (WithZero (Multiplicative ℤ))) (y : L) (n : ℕ) :
    RCN187.poleOrder v y ≤ (n : ℤ) ↔ v y ≤ WithZero.exp (n : ℤ) := by
  rw [RCN187.poleOrder]
  rcases eq_or_ne (v y) 0 with h0 | h0
  · simp [h0]
  · rw [max_le_iff, ← WithZero.log_le_iff_le_exp h0]
    exact and_iff_right (Int.natCast_nonneg n)
theorem card_le_of_zeros {x : L} (hx : x ≠ 0) (T : Finset (RCN026.Place_p19 K L))
    (D : RCN026.Place_p19 K L → ℕ) (hD : ∀ v ∉ T, D v = 0)
    (hpole : ∀ v : RCN026.Place_p19 K L, RCN187.poleOrder v.val x ≤ (D v : ℤ))
    (U : Finset (RCN026.Place_p19 K L)) (hU : ∀ v ∈ U, v.val x < 1) : U.card ≤ ∑ v ∈ T, D v := by
  have h1 := RCN026.AUN K L x hx U fun v hv => by
    have h0 : v.val x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hlt := hU v hv
    rw [← WithZero.exp_log h0, WithZero.exp_lt_one_iff] at hlt
    rw [RCN026.order_p19]
    omega
  have h2 : ∑ v ∈ RCN026.placesFor_p19 K L x hx, RCN346.poleOrder_p19 K L v x ≤
      ((∑ v ∈ T, D v : ℕ) : ℤ) :=
    (Finset.sum_le_sum fun v _ => hpole v).trans (by
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.sum_le_sum_of_ne_zero fun v _ hv => by
        by_contra hT
        exact hv (hD v hT))
  exact_mod_cast h1.trans h2
theorem sum_smul_eq_zero (T : Finset (RCN026.Place_p19 K L)) (D : RCN026.Place_p19 K L → ℕ)
    (hD : ∀ v ∉ T, D v = 0) (U : Finset (RCN026.Place_p19 K L)) (hcard : ∑ v ∈ T, D v < U.card)
    {ι : Type*} [Fintype ι] (y : ι → L)
    (hpole : ∀ i (v : RCN026.Place_p19 K L), RCN187.poleOrder v.val (y i) ≤ (D v : ℤ))
    (r : RCN026.Place_p19 K L → ι → K)
    (hr : ∀ v ∈ U, ∀ i, v.val (y i - algebraMap K L (r v i)) < 1)
    (l : ι → K) (hl : ∀ v ∈ U, ∑ i, l i * r v i = 0) : ∑ i, l i • y i = 0 := by
  by_contra hx
  have hconst : ∀ (v : RCN026.Place_p19 K L) (c : K), v.val (algebraMap K L c) ≤ 1 := fun v c =>
    haveI := v.property.2
    RCN345.FLO K L v.val c
  refine absurd (card_le_of_zeros hx T D hD (fun v => ?_) U fun v hv => ?_) (not_le.mpr hcard)
  · rw [poleOrder_le_iff]
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_of_le (hconst v (l i)) ((poleOrder_le_iff _ _ _).mp (hpole i v))
  · have hsum : ∑ i, l i • algebraMap K L (r v i) = 0 := by
      simp_rw [Algebra.smul_def, ← map_mul]
      rw [← map_sum, hl v hv, map_zero]
    have hsplit : ∑ i, l i • y i = ∑ i, l i • (y i - algebraMap K L (r v i)) := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, hsum, sub_zero]
    rw [hsplit]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    exact mul_lt_of_le_one_of_lt (hconst v (l i)) (hr v hv i)
end Field
section Curves
open RCN002 RCN005 RCN006 RCN072 RCN341
variable {E : Type} [Field E] [IsAlgClosed E]
theorem curve_exists_places (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (sep : RCN341.SeparableLiteralCoordinate C)
    (T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C))) (N : ℕ) :
    ∃ U : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)), U.card = N ∧ Disjoint U T ∧
      ∀ v ∈ U, ∀ x : RCN002.CoordinateField E C, v.val x ≤ 1 → ∃ e : E, v.val (x - algebraMap E (RCN002.CoordinateField E C) e) < 1 := by
  let _ := RCN006.polynomialBaseAlgebra E C sep.index
  let _ := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  let _ := RCN006.polynomialBaseScalarTower E C sep.index
  let _ := RCN006.polynomialRationalScalarTower E C sep.index sep.transcendental
  let _ := RCN005.rationalBaseScalarTower E C sep.index sep.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  exact exists_places E (RCN002.CoordinateField E C) T N
theorem curve_sum_smul_eq_zero (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (sep : RCN341.SeparableLiteralCoordinate C)
    (T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C))) (D : RCN026.Place_p19 E (RCN002.CoordinateField E C) → ℕ)
    (hD : ∀ v ∉ T, D v = 0) (U : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)))
    (hcard : ∑ v ∈ T, D v < U.card) {ι : Type} [Fintype ι] (y : ι → RCN002.CoordinateField E C)
    (hpole : ∀ i (v : RCN026.Place_p19 E (RCN002.CoordinateField E C)), RCN187.poleOrder v.val (y i) ≤ (D v : ℤ))
    (r : RCN026.Place_p19 E (RCN002.CoordinateField E C) → ι → E)
    (hr : ∀ v ∈ U, ∀ i, v.val (y i - algebraMap E (RCN002.CoordinateField E C) (r v i)) < 1)
    (l : ι → E) (hl : ∀ v ∈ U, ∑ i, l i * r v i = 0) : ∑ i, l i • y i = 0 := by
  let _ := RCN006.polynomialBaseAlgebra E C sep.index
  let _ := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  let _ := RCN006.polynomialBaseScalarTower E C sep.index
  let _ := RCN006.polynomialRationalScalarTower E C sep.index sep.transcendental
  let _ := RCN005.rationalBaseScalarTower E C sep.index sep.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  exact sum_smul_eq_zero T D hD U hcard y hpole r hr l hl
theorem card_le_sum_degree (A : Type) [Fintype A] (C : A → Ideal (MvPolynomial (Fin 3) E))
    [∀ a, (C a).IsPrime] (sep : ∀ a, RCN341.SeparableLiteralCoordinate (C a)) (T : ∀ a, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E (C a))))
    (D : ∀ a, RCN026.Place_p19 E (RCN002.CoordinateField E (C a)) → ℕ) (hD : ∀ a, ∀ v ∉ T a, D a v = 0)
    (ι : Type) [Fintype ι] (f : ι → ∀ a, RCN002.CoordinateField E (C a)) (hf : LinearIndependent E f)
    (hpole : ∀ i a (v : RCN026.Place_p19 E (RCN002.CoordinateField E (C a))),
      RCN187.poleOrder v.val (f i a) ≤ (D a v : ℤ)) :
    Fintype.card ι ≤ ∑ a, ((∑ v ∈ T a, D a v) + 1) := by
  choose U hUcard hUdisj hUres using fun a =>
    curve_exists_places (C a) (sep a) (T a) ((∑ v ∈ T a, D a v) + 1)
  have hres : ∀ a (v : RCN026.Place_p19 E (RCN002.CoordinateField E (C a))) (i : ι), ∃ e : E,
      v ∈ U a → v.val (f i a - algebraMap E (RCN002.CoordinateField E (C a)) e) < 1 := fun a v i => by
    by_cases hv : v ∈ U a
    · have hle : v.val (f i a) ≤ 1 := by
        have h := hpole i a v
        rw [hD a v (Finset.disjoint_left.mp (hUdisj a) hv), poleOrder_le_iff] at h
        simpa using h
      obtain ⟨e, he⟩ := hUres a v hv (f i a) hle
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hres
  let M : Matrix (Σ a, U a) ι E := fun j i => r j.1 j.2.1 i
  have hinj : Function.Injective (Matrix.mulVecLin M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro l hl
    refine funext (Fintype.linearIndependent_iff.mp hf l (funext fun a => ?_))
    rw [Finset.sum_apply]
    refine curve_sum_smul_eq_zero (C a) (sep a) (T a) (D a) (hD a) (U a)
      (by rw [hUcard a]; exact Nat.lt_succ_self _) (fun i => f i a) (fun i v => hpole i a v) (r a)
      (fun v hv i => hr a v i hv) l fun v hv => ?_
    have h : ∑ i, r a v i * l i = 0 := congrFun hl ⟨a, ⟨v, hv⟩⟩
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sigma] at h
  simpa [hUcard] using h
end Curves
end
end H2Pole
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Field
variable {k : Type} [Field k]
def levelForm (c0 : k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 2 - MvPolynomial.C c0
def layer (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    Submodule k
      (MvPolynomial (Fin 3) k ⧸ Ideal.span ({F, levelForm c0} : Set (MvPolynomial (Fin 3) k))) :=
  Submodule.map
    (Ideal.Quotient.mkₐ k
      (Ideal.span ({F, levelForm c0} : Set (MvPolynomial (Fin 3) k)))).toLinearMap
    (Submodule.comap (LinearMap.mulLeft k (levelForm c0 ^ j))
      (H2Count.box k ρ θ ⊔ (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k))).restrictScalars k))
def CountStatement (k : Type) [Field k] : Prop :=
  ∀ (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ n ℓ : ℕ),
    (∀ j < n, Module.rank k (layer F c0 ρ θ j) ≤ (ℓ : Cardinal)) →
    n * ℓ < Module.finrank k
      (Submodule.map
        (Ideal.Quotient.mkₐ k (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)))).toLinearMap
        (H2Count.box k ρ θ)) →
    ∃ G ∈ H2Count.box k ρ θ, ¬F ∣ G ∧
      ∃ A H : MvPolynomial (Fin 3) k, G = A * F + levelForm c0 ^ n * H
def PoleSpaceStatement (E : Type) [Field E] [IsAlgClosed E] : Prop :=
  ∀ (A : Type) [Fintype A] (C : A → Ideal (MvPolynomial (Fin 3) E)) [∀ a, (C a).IsPrime]
    (_sep : ∀ a, RCN341.SeparableLiteralCoordinate (C a)) (T : ∀ a, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E (C a))))
    (D : ∀ a, RCN026.Place_p19 E (RCN002.CoordinateField E (C a)) → ℕ) (_hD : ∀ a, ∀ v ∉ T a, D a v = 0)
    (ι : Type) [Fintype ι] (f : ι → ∀ a, RCN002.CoordinateField E (C a)), LinearIndependent E f →
    (∀ i a (v : RCN026.Place_p19 E (RCN002.CoordinateField E (C a))), RCN187.poleOrder v.val (f i a) ≤ (D a v : ℤ)) →
    Fintype.card ι ≤ ∑ a, ((∑ v ∈ T a, D a v) + 1)
end Field
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
def carrierK (P : Packet x t y r) : MvPolynomial (Fin 3) (RationalBase K) :=
  surfaceMap (algebraMap (Polynomial K) (RationalBase K)) P.F
abbrev levelΩ (c0 : RationalBase K) : MvPolynomial (Fin 3) (GenericField K) :=
  levelForm (algebraMap (RationalBase K) (GenericField K) c0)
structure GoodValue (P : Packet x t y r) (c0 : RationalBase K) : Prop where
  ne_zero : c0 ≠ 0
  good : ∀ g : RCN222.GeometricFactor K P.F, Sec.GoodSection (P.stage g).G (levelΩ c0) (baseH P.F)
  unit : ∀ (g : RCN222.GeometricFactor K P.F) (sR sY sZ : Bool) (ν : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰),
    SurfaceDivisor (Exch.component P g) sR sY sZ ν →
    ν (RCN002.coordinateEvaluation Ω (Exch.component P g) (levelΩ c0)) < 1 →
    ∀ j, ν (coordinate Ω (Exch.component P g) j) = 1
def GoodValueStatement (P : Packet x t y r) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0),
    {c0 : RationalBase K | ¬GoodValue P c0}.Finite
abbrev SectionComponent (P : Packet x t y r) (c0 : RationalBase K) : Type :=
  (g : RCN222.GeometricFactor K P.F) × RCN264.RegularComponent Ω (P.stage g).G (levelΩ c0) (baseH P.F)
def SectionEmbeddingStatement (P : Packet x t y r) : Prop :=
  ∀ (c0 : RationalBase K) (_h0 : GoodValue P c0) (ι : Type) [Fintype ι]
    (H : ι → MvPolynomial (Fin 3) (RationalBase K)),
    LinearIndependent (RationalBase K) (fun i =>
      Ideal.Quotient.mk (Ideal.span ({carrierK P, levelForm c0} :
        Set (MvPolynomial (Fin 3) (RationalBase K)))) (H i)) →
    LinearIndependent Ω (fun i (a : SectionComponent P c0) =>
      RCN002.coordinateEvaluation Ω a.2.1 (MvPolynomial.map (algebraMap (RationalBase K) Ω) (H i)))
def PoleBoundStatement (P : Packet x t y r) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (c0 : RationalBase K) (_h0 : GoodValue P c0) (W : FlagDegree) (j : ℕ)
    (G A H : MvPolynomial (Fin 3) Ω), RCN095.PolynomialInFlag W G →
    G = A * baseCarrier P.F + levelΩ c0 ^ j * H →
    ∀ (a : SectionComponent P c0) (v : RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1)),
      RCN187.poleOrder v.val (RCN002.coordinateEvaluation Ω a.2.1 H) ≤ RCN204.flagPole v.val (coordinate Ω a.2.1) W
def SectionDegreeStatement (P : Packet x t y r) : Prop :=
  ∀ (c0 : RationalBase K) (_h0 : GoodValue P c0) (rhi yhi : ℕ)
    (_hr : (baseCarrier P.F).degreeOf 1 ≤ rhi)
    (_hy : ∀ d ∈ (baseCarrier P.F).support, d 0 + d 1 ≤ yhi),
    Fintype.card (SectionComponent P c0) ≤ rhi ∧
    ∀ (β γ : ℕ) (T : ∀ a : SectionComponent P c0, Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1))),
      ∑ a, ∑ v ∈ T a, RCN204.flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩ ≤
        ((β * rhi + γ * yhi : ℕ) : ℤ)
def LayerBoundStatement (P : Packet x t y r) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (c0 : RationalBase K) (_h0 : GoodValue P c0) (β γ rhi yhi : ℕ)
    (_hr : (baseCarrier P.F).degreeOf 1 ≤ rhi)
    (_hy : ∀ d ∈ (baseCarrier P.F).support, d 0 + d 1 ≤ yhi) (j : ℕ),
    Module.rank (RationalBase K) (layer (carrierK P) c0 γ (β + γ) j) ≤
      ((β * rhi + γ * yhi + rhi : ℕ) : Cardinal)
def ExistsAux (P : Packet x t y r) (n β γ : ℕ) : Prop :=
  ∃ bad : Set (RationalBase K), bad.Finite ∧ ∀ c0 ∉ bad, c0 ≠ 0 ∧
    ∃ G : MvPolynomial (Fin 4) K, ¬P.F ∣ G ∧
      (∀ g : RCN222.GeometricFactor K P.F, RCN002.coordinateEvaluation Ω (Exch.component P g) (surfaceMap (RCN135.polynomialEmbedding K) G) ≠ 0) ∧
      RCN095.PolynomialInFlag ⟨0, β, γ⟩ (surfaceMap (RCN135.polynomialEmbedding K) G) ∧
      ∃ A H : MvPolynomial (Fin 3) Ω,
        surfaceMap (RCN135.polynomialEmbedding K) G = A * baseCarrier P.F + levelΩ c0 ^ n * H
def ExistsStatement (P : Packet x t y r) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (n β γ rlo rhi yhi tlo : ℕ)
    (_hr1 : rlo ≤ (baseCarrier P.F).degreeOf 1) (_hr2 : (baseCarrier P.F).degreeOf 1 ≤ rhi)
    (_hy : ∀ d ∈ (baseCarrier P.F).support, d 0 + d 1 ≤ yhi)
    (_ht : tlo ≤ (baseCarrier P.F).totalDegree)
    (_hcert : n * (β * rhi + γ * yhi + rhi) <
      H2Count.boxCount γ (β + γ) -
        if rlo ≤ γ ∧ tlo ≤ β + γ then H2Count.boxCount (γ - rlo) (β + γ - tlo) else 0),
    ExistsAux P n β γ
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2
def tet (m : ℕ) : ℕ :=
  m * (m + 1) * (m + 2) / 6
def boxN (ρ θ : ℕ) : ℕ :=
  tet (θ + 1) - tet (θ - ρ)
def boxNSub (ρ θ r t : ℕ) : ℕ :=
  if r ≤ ρ ∧ t ≤ θ then boxN (ρ - r) (θ - t) else 0
def quotientDim (ρ θ r t : ℕ) : ℕ :=
  boxN ρ θ - boxNSub ρ θ r t
def layerBound (B C q m r y : ℕ) : ℕ :=
  q * m * (m * (B * r + C * y) + r)
abbrev LayerGap (B C q m r y t : ℕ) : Prop :=
  layerBound B C q m r y < quotientDim (m * C) (m * (B + C)) r t
abbrev Certificate (r y T0 B C q n : ℕ) : Prop :=
  0 < q ∧ q ∣ n ∧ 0 < n ∧ ∀ j : ℕ, j < r → LayerGap B C q (n / q) (j + 1) y T0
theorem boxN_eq (ρ θ : ℕ) : boxN ρ θ = H2Count.boxCount ρ θ :=
  (H2Count.boxCount_eq ρ θ).symm
theorem LayerGap.count {B C q m r y t : ℕ} (h : LayerGap B C q m r y t) :
    q * m * (m * (B * r + C * y) + r) <
      H2Count.boxCount (m * C) (m * (B + C)) -
        if r ≤ m * C ∧ t ≤ m * (B + C) then H2Count.boxCount (m * C - r) (m * (B + C) - t) else 0 := by
  have h' := h
  simp only [LayerGap, layerBound, quotientDim, boxNSub, boxN_eq] at h'
  exact h'
theorem Certificate.count {r y T0 B C q n : ℕ} (h : Certificate r y T0 B C q n) {r' : ℕ}
    (hr1 : 1 ≤ r') (hr : r' ≤ r) :
    n * (n / q * B * r' + n / q * C * y + r') <
      H2Count.boxCount (n / q * C) (n / q * B + n / q * C) -
        if r' ≤ n / q * C ∧ T0 ≤ n / q * B + n / q * C then
          H2Count.boxCount (n / q * C - r') (n / q * B + n / q * C - T0) else 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hr1
  have h1 := (h.2.2.2 j (Nat.lt_of_succ_le hr)).count
  have hn : n = q * (n / q) := (Nat.mul_div_cancel' h.2.1).symm
  have e1 : n * (n / q * B * (j + 1) + n / q * C * y + (j + 1)) =
      q * (n / q) * (n / q * (B * (j + 1) + C * y) + (j + 1)) := by
    rw [← hn]
    ring
  rw [e1, ← Nat.mul_add (n / q) B C]
  exact h1
end H2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Pole
theorem poleSpace (E : Type) [Field E] [IsAlgClosed E] : H2Sec.PoleSpaceStatement E :=
  fun A _ C _ sep T D hD ι _ f hf hpole => card_le_sum_degree A C sep T D hD ι f hf hpole
end H2Pole
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN204 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Restrict
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
theorem BR_eq_zero_of_le (hGC : G ≤ C) (a : MvPolynomial (Fin 3) E)
    (ha : (RCN002.coordinateEvaluation E G).toRingHom a = 0) : (RCN002.coordinateEvaluation E C).toRingHom a = 0 :=
  (Sec.BR_eq_zero_iff (G := C) a).mpr (hGC ((Sec.BR_eq_zero_iff (G := G) a).mp ha))
theorem lmono_neg {L : Type*} [Field L] (x : Fin 3 → L) (a : Fin 3 → ℤ) :
    lmono x (fun j => -a j) = (lmono x a)⁻¹ := by
  simp only [lmono, zpow_neg, mul_inv]
theorem lmono_mem_resGraph (hGC : G ≤ C) (a : Fin 3 → ℤ)
    (ha : ∀ j, a j < 0 → coordinate E C j ≠ 0) :
    (lmono (coordinate E G) a, lmono (coordinate E C) a) ∈
      resGraph (RCN002.coordinateEvaluation E G).toRingHom (RCN002.coordinateEvaluation E C).toRingHom := by
  have hfg : ∀ z, (RCN002.coordinateEvaluation E G).toRingHom z = 0 → (RCN002.coordinateEvaluation E C).toRingHom z = 0 := BR_eq_zero_of_le hGC
  have h : ∀ j : Fin 3, (coordinate E G j ^ a j, coordinate E C j ^ a j) ∈
      resGraph (RCN002.coordinateEvaluation E G).toRingHom (RCN002.coordinateEvaluation E C).toRingHom := fun j =>
    zpow_mem_resGraph hfg (MvPolynomial.X j) (a j) (ha j)
  simpa only [lmono, Prod.mk_mul_mk] using mul_mem (mul_mem (h 0) (h 1)) (h 2)
theorem BR_mem_resGraph (hGC : G ≤ C) (A : MvPolynomial (Fin 3) E) :
    (RCN002.coordinateEvaluation E G A, RCN002.coordinateEvaluation E C A) ∈ resGraph (RCN002.coordinateEvaluation E G).toRingHom (RCN002.coordinateEvaluation E C).toRingHom := by
  have hfg : ∀ z, (RCN002.coordinateEvaluation E G).toRingHom z = 0 → (RCN002.coordinateEvaluation E C).toRingHom z = 0 := BR_eq_zero_of_le hGC
  have h := mem_resGraph hfg A 1 (by rw [map_one]; exact one_ne_zero)
  rw [map_one, map_one, div_one, div_one] at h
  exact h
theorem chart_mem_resGraph (hGC : G ≤ C) (sR sY sZ : Bool)
    (hcoord : ∀ i j, chartExp sR sY sZ i j < 0 → coordinate E C j ≠ 0)
    (nu : Valuation (RCN002.CoordinateField E C) ℤᵐ⁰) (hnuE : ∀ a : E, nu (algebraMap E (RCN002.CoordinateField E C) a) ≤ 1)
    (hnu : ∀ i, nu (lmono (coordinate E C) (chartExp sR sY sZ i)) ≤ 1)
    (a : RCN002.CoordinateField E G) (ha : a ∈ surfaceChartRing G sR sY sZ) :
    ∃ b, (a, b) ∈ resGraph (RCN002.coordinateEvaluation E G).toRingHom (RCN002.coordinateEvaluation E C).toRingHom ∧ nu b ≤ 1 := by
  rw [surfaceChartRing] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, lmono_mem_resGraph hGC _ (hcoord i), hnu i⟩
  | algebraMap e =>
    refine ⟨algebraMap E (RCN002.CoordinateField E C) e, ?_, hnuE e⟩
    have h := BR_mem_resGraph hGC (MvPolynomial.C e)
    rwa [algHom_C, algHom_C] at h
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hb1⟩ := hx
    obtain ⟨c, hc, hc1⟩ := hy
    exact ⟨b + c, add_mem hb hc, nu.map_add_le hb1 hc1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hb1⟩ := hx
    obtain ⟨c, hc, hc1⟩ := hy
    exact ⟨b * c, mul_mem hb hc, by rw [map_mul]; exact mul_le_one' hb1 hc1⟩
theorem BR_le_flagPole (hGC : G ≤ C) (num : MvPolynomial (Fin 3) E) (W : FlagDegree)
    (hint : ∀ sR sY sZ : Bool, IsIntegral (surfaceChartRing G sR sY sZ)
      (RCN002.coordinateEvaluation E G num / lmono (coordinate E G) (vertexExp sR sY sZ W)))
    (nu : Valuation (RCN002.CoordinateField E C) ℤᵐ⁰) (hnuE : ∀ a : E, nu (algebraMap E (RCN002.CoordinateField E C) a) ≤ 1) :
    nu (RCN002.coordinateEvaluation E C num) ≤ exp (flagPole nu (coordinate E C) W) := by
  obtain ⟨sR, sY, sZ, hR, hY, hZ, hchart, hvert⟩ := chart_select nu (coordinate E C)
  have hbit : ∀ j : Fin 3, (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) →
      coordinate E C j ≠ 0 := by
    rintro j (⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩)
    exacts [hY hb, hR hb, hZ hb]
  have hcoord : ∀ i j, chartExp sR sY sZ i j < 0 → coordinate E C j ≠ 0 := fun i j h =>
    hbit j (chartExp_neg sR sY sZ i j h)
  have hneg := lmono_mem_resGraph hGC (fun j => -vertexExp sR sY sZ W j) (fun j hj =>
    hbit j (vertexExp_ne_zero sR sY sZ W j (by omega)))
  rw [lmono_neg, lmono_neg] at hneg
  have hmem := mul_mem (BR_mem_resGraph hGC num) hneg
  rw [Prod.mk_mul_mk, ← div_eq_mul_inv, ← div_eq_mul_inv] at hmem
  have hfg : ∀ z, (RCN002.coordinateEvaluation E G).toRingHom z = 0 → (RCN002.coordinateEvaluation E C).toRingHom z = 0 := BR_eq_zero_of_le hGC
  have h := le_one_of_isIntegral_resGraph hfg nu
    (fun a : surfaceChartRing G sR sY sZ =>
      chart_mem_resGraph hGC sR sY sZ hcoord nu hnuE hchart a.1 a.2) hmem (hint sR sY sZ)
  rw [map_div₀, hvert W] at h
  exact (div_le_one₀ (zero_lt_iff.2 exp_ne_zero)).1 h
omit [G.IsPrime] in
theorem val_BR_le_one (nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (hnuE : ∀ a : E, nu (algebraMap E (RCN002.CoordinateField E G) a) ≤ 1)
    (hnu : ∀ i, nu (coordinate E G i) ≤ 1) (A : MvPolynomial (Fin 3) E) : nu (RCN002.coordinateEvaluation E G A) ≤ 1 := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [algHom_C]
    exact hnuE a
  | add p q hp hq =>
    rw [map_add]
    exact nu.map_add_le hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact mul_le_one' hp (hnu i)
end Restrict
section Krull
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] {sR sY sZ : Bool}
variable {N p : ℕ} [CharP E p]
theorem isIntegral_of_surfaceDivisor (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p) (x : RCN002.CoordinateField E G)
    (h : ∀ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, SurfaceDivisor G sR sY sZ nu → nu x ≤ 1) :
    IsIntegral (surfaceChartRing G sR sY sZ) x := by
  have := normalChart_isFractionRing hN
  have := normalChart_isIntegrallyClosed hN
  have := normalChart_isNoetherianRing hN hp
  obtain ⟨a, rfl⟩ := mem_range_of_valuation_le_one (K := RCN002.CoordinateField E G) (O := normalChart G sR sY sZ) x
    fun P => h _ (PrimeDivisor.surfaceDivisor hN hp P)
  exact a.2
end Krull
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
theorem BR_baseCarrier (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RCN002.coordinateEvaluation Ω (Exch.component P g) (baseCarrier P.F) = 0 := by
  obtain ⟨h, hh⟩ := (P.stage g).RR
  have hh' : baseCarrier P.F = (P.stage g).G * h := hh
  rw [Sec.BR_eq_zero_iff, hh']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
theorem val_quotient_le (P : Packet x t y r) (hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (c0 : RationalBase K) (h0 : GoodValue P c0) (W : FlagDegree) (j : ℕ)
    (G A H : MvPolynomial (Fin 3) Ω) (hG : RCN095.PolynomialInFlag W G)
    (hGA : G = A * baseCarrier P.F + levelΩ c0 ^ j * H) (g : RCN222.GeometricFactor K P.F) (sR sY sZ : Bool)
    (nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰)
    (hnu : SurfaceDivisor (Exch.component P g) sR sY sZ nu) :
    nu (RCN002.coordinateEvaluation Ω (Exch.component P g) H /
      lmono (coordinate Ω (Exch.component P g)) (vertexExp sR sY sZ W)) ≤ 1 := by
  have hchart : ∀ i, nu (lmono (coordinate Ω (Exch.component P g)) (chartExp sR sY sZ i)) ≤ 1 :=
    fun i => hnu.le_one _ (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hconst : ∀ e : Ω, nu (algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) e) ≤ 1 := fun e =>
    hnu.le_one _ (Subalgebra.algebraMap_mem _ e)
  have hM := flagPole_eq_vertex nu _ (hc g) sR sY sZ hchart W
  rw [map_div₀, hM, div_le_one₀ (zero_lt_iff.2 exp_ne_zero)]
  by_cases hlt : nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (levelΩ c0)) < 1
  · have hunit := h0.unit g sR sY sZ nu hnu hlt
    have hpole : flagPole nu (coordinate Ω (Exch.component P g)) W = 0 := by
      simp only [flagPole, RCN187.poleOrder, hunit, log_one, max_self, mul_zero, add_zero]
    rw [hpole, exp_zero]
    exact val_BR_le_one nu hconst (fun i => (hunit i).le) H
  · rw [not_lt] at hlt
    have hprod : RCN002.coordinateEvaluation Ω (Exch.component P g) G =
        RCN002.coordinateEvaluation Ω (Exch.component P g) (levelΩ c0) ^ j * RCN002.coordinateEvaluation Ω (Exch.component P g) H := by
      rw [hGA, map_add, map_mul, map_mul, map_pow, BR_baseCarrier, mul_zero, zero_add]
    have hflag : nu (RCN002.coordinateEvaluation Ω (Exch.component P g) G) ≤
        exp (flagPole nu (coordinate Ω (Exch.component P g)) W) := by
      have h := RCN204.valuation_eval_le_flag nu (algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g))) hconst
        (coordinate Ω (Exch.component P g)) W G hG
      rwa [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def, ← RCN002.coordinateEvaluation_eq_aeval] at h
    refine le_trans ?_ hflag
    rw [hprod, map_mul, map_pow]
    exact le_mul_of_one_le_left' (one_le_pow_of_one_le' hlt j)
theorem poleBound (P : Packet x t y r) : PoleBoundStatement P := by
  intro N hN hNp hc c0 h0 W j G A H hG hGA a v
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hCmem : a.2.1 ∈ RCN072.componentFamily Ω (P.stage a.1).G (levelΩ c0) := AAS Ω _ _ _ a.2
  have hGC : Exch.component P a.1 ≤ a.2.1 :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (RCN072.cutIdeal_le_component Ω _ _ _ hCmem (Ideal.subset_span (Set.mem_insert _ _)))
  have hle := BR_le_flagPole hGC H W (fun sR sY sZ =>
    isIntegral_of_surfaceDivisor (hN a.1 sR sY sZ) hNp _ fun nu hnu =>
      val_quotient_le P hc c0 h0 W j G A H hG hGA a.1 sR sY sZ nu hnu) v.val
    (fun e => RCN344.NP Ω _ v e)
  refine max_le (RCN204.flagPole_nonneg v.val _ W) ?_
  by_cases hz : v.val (RCN002.coordinateEvaluation Ω a.2.1 H) = 0
  · rw [hz, log_zero]
    exact RCN204.flagPole_nonneg v.val _ W
  · exact (log_le_iff_le_exp hz).2 hle
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open MvPolynomial
noncomputable section
section Plane
variable {E : Type} [Field E]
def evZ (c : E) : MvPolynomial (Fin 3) E →ₐ[E] MvPolynomial (Fin 2) E :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, C c]
def incZ : MvPolynomial (Fin 2) E →ₐ[E] MvPolynomial (Fin 3) E :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1]
theorem evZ_incZ (c : E) (q : MvPolynomial (Fin 2) E) : evZ c (incZ q) = q := by
  have h : (evZ c).comp incZ = AlgHom.id E (MvPolynomial (Fin 2) E) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [evZ, incZ]
  exact congrArg (fun f : MvPolynomial (Fin 2) E →ₐ[E] MvPolynomial (Fin 2) E => f q) h
theorem evZ_surjective (c : E) : Function.Surjective (evZ c) := fun q => ⟨incZ q, evZ_incZ c q⟩
theorem evZ_levelForm (c : E) : evZ c (levelForm c) = 0 := by
  simp [evZ, levelForm]
theorem sub_incZ_evZ_mem (c : E) (p : MvPolynomial (Fin 3) E) :
    p - incZ (evZ c p) ∈ Ideal.span ({levelForm c} : Set (MvPolynomial (Fin 3) E)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evZ, incZ]
  | add p q hp hq =>
    have e : p + q - incZ (evZ c (p + q)) = p - incZ (evZ c p) + (q - incZ (evZ c q)) := by
      rw [map_add, map_add]
      ring
    rw [e]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    have hi : MvPolynomial.X i - incZ (evZ c (MvPolynomial.X i)) ∈
        Ideal.span ({levelForm c} : Set (MvPolynomial (Fin 3) E)) := by
      fin_cases i
      · simp [evZ, incZ]
      · simp [evZ, incZ]
      · have e : (MvPolynomial.X 2 : MvPolynomial (Fin 3) E) - incZ (evZ c (MvPolynomial.X 2)) = levelForm c := by
          simp [evZ, incZ, levelForm]
        exact e ▸ Ideal.mem_span_singleton_self _
    have e : p * MvPolynomial.X i - incZ (evZ c (p * MvPolynomial.X i)) =
        (p - incZ (evZ c p)) * MvPolynomial.X i + incZ (evZ c p) * (MvPolynomial.X i - incZ (evZ c (MvPolynomial.X i))) := by
      rw [map_mul, map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hi)
theorem mem_span_levelForm_of_evZ (c : E) (p : MvPolynomial (Fin 3) E) (hp : evZ c p = 0) :
    p ∈ Ideal.span ({levelForm c} : Set (MvPolynomial (Fin 3) E)) := by
  have h := sub_incZ_evZ_mem c p
  rwa [hp, map_zero, sub_zero] at h
theorem evZ_pderiv (c : E) (p : MvPolynomial (Fin 3) E) :
    evZ c (pderiv 1 p) = pderiv 1 (evZ c p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evZ]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    have hi : evZ c (pderiv 1 (MvPolynomial.X i)) = pderiv 1 (evZ c (MvPolynomial.X i)) := by
      fin_cases i <;> simp [evZ, pderiv_X]
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, map_add, map_mul, map_mul, hp, hi]
theorem dvd_of_forall_prime_dvd {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    (f : B) : ∀ y : B, f ≠ 0 → (∀ q : B, Prime q → q ∣ f → q ∣ y) →
      (∀ q : B, Prime q → ¬q * q ∣ f) → f ∣ y := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun y h0 => absurd rfl h0
  | h₂ x hx => exact fun y _ _ _ => hx.dvd
  | h₃ a p ha hp ih =>
    intro y _ hdvd hsq
    obtain ⟨y', rfl⟩ := hdvd p hp (dvd_mul_right p a)
    refine mul_dvd_mul_left p (ih y' ha (fun q hq hqa => ?_) fun q hq hqq =>
      hsq q hq (hqq.trans (dvd_mul_left a p)))
    rcases hq.dvd_or_dvd (hdvd q hq (hqa.trans (dvd_mul_left a p))) with hqp | hqy
    · exact absurd (mul_dvd_mul_left p ((hq.associated_of_dvd hp hqp).symm.dvd.trans hqa)) (hsq p hp)
    · exact hqy
theorem mem_span_of_section (c : E) (Fb x : MvPolynomial (Fin 3) E) (hF : evZ c Fb ≠ 0)
    (h : ∀ q : MvPolynomial (Fin 2) E, Prime q → q ∣ evZ c Fb →
      ¬q ∣ evZ c (pderiv 1 Fb) ∧ q ∣ evZ c x) :
    x ∈ Ideal.span ({Fb, levelForm c} : Set (MvPolynomial (Fin 3) E)) := by
  have hsq : ∀ q : MvPolynomial (Fin 2) E, Prime q → ¬q * q ∣ evZ c Fb := by
    rintro q hq ⟨w, hw⟩
    refine (h q hq ⟨q * w, by rw [hw]; ring⟩).1 ?_
    rw [evZ_pderiv, hw, Derivation.leibniz, Derivation.leibniz]
    exact ⟨q * pderiv 1 w + w * (pderiv 1 q + pderiv 1 q), by
      simp only [smul_eq_mul]
      ring⟩
  obtain ⟨w, hw⟩ := dvd_of_forall_prime_dvd (evZ c Fb) (evZ c x) hF
    (fun q hq hqF => (h q hq hqF).2) hsq
  have h0 : evZ c (x - Fb * incZ w) = 0 := by
    rw [map_sub, map_mul, evZ_incZ, hw, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_span_levelForm_of_evZ c _ h0)
  exact Ideal.mem_span_pair.mpr ⟨incZ w, b, by rw [hb]; ring⟩
theorem comap_mem_minimalPrimes (c : E) (g : MvPolynomial (Fin 3) E) (hg : evZ c g ≠ 0)
    (q : MvPolynomial (Fin 2) E) (hq : Prime q) (hqg : q ∣ evZ c g) :
    Ideal.comap (evZ c) (Ideal.span {q}) ∈
      (Ideal.span ({g, levelForm c} : Set (MvPolynomial (Fin 3) E))).minimalPrimes := by
  have hqp : (Ideal.span ({q} : Set (MvPolynomial (Fin 2) E))).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span ({g, levelForm c} : Set (MvPolynomial (Fin 3) E)) ≤
      Ideal.comap (evZ c) (Ideal.span {q}) := by
    rw [Ideal.span_le]
    intro z hz
    rcases hz with h1 | h1
    · rw [h1]
      exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr hqg)
    · rw [Set.mem_singleton_iff.mp h1]
      refine Ideal.mem_comap.mpr ?_
      rw [evZ_levelForm]
      exact Ideal.zero_mem _
  refine ⟨⟨Ideal.comap_isPrime _ _, hle⟩, fun P hP hPle => ?_⟩
  obtain ⟨hPp, hPI⟩ := hP
  have hsub : ({levelForm c} : Set (MvPolynomial (Fin 3) E)) ⊆ {g, levelForm c} :=
    Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem g (Set.mem_singleton (levelForm c)))
  have hker : RingHom.ker (evZ c) ≤ P := fun z hz =>
    hPI (Ideal.span_mono hsub (mem_span_levelForm_of_evZ c z (RingHom.mem_ker.mp hz)))
  have hP'p : (Ideal.map (evZ c) P).IsPrime :=
    Ideal.map_isPrime_of_surjective (evZ_surjective c) hker
  have hP'ne : Ideal.map (evZ c) P ≠ ⊥ := by
    intro h0
    have h1 : evZ c g ∈ Ideal.map (evZ c) P :=
      Ideal.mem_map_of_mem (evZ c) (hPI (Ideal.subset_span (Set.mem_insert g _)))
    rw [h0, Ideal.mem_bot] at h1
    exact hg h1
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hP'p hP'ne
  have hP'le : Ideal.map (evZ c) P ≤ Ideal.span {q} := Ideal.map_le_iff_le_comap.mpr hPle
  obtain ⟨u, hu⟩ := (hq.associated_of_dvd hπ (Ideal.mem_span_singleton.mp (hP'le hπP))).symm.dvd
  have hqP : q ∈ Ideal.map (evZ c) P := by
    rw [hu]
    exact Ideal.mul_mem_right _ _ hπP
  calc Ideal.comap (evZ c) (Ideal.span {q})
      ≤ Ideal.comap (evZ c) (Ideal.map (evZ c) P) :=
        Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hqP)
    _ = P ⊔ Ideal.comap (evZ c) ⊥ := Ideal.comap_map_of_surjective _ (evZ_surjective c) P
    _ ≤ P := sup_le le_rfl hker
end Plane
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open MvPolynomial
noncomputable section
section Field
variable {k : Type} [Field k]
theorem finrank_map_mk_add (V : Submodule k (MvPolynomial (Fin 3) k)) [Module.Finite k V]
    (J : Ideal (MvPolynomial (Fin 3) k)) :
    Module.finrank k (V.map (Ideal.Quotient.mkₐ k J).toLinearMap) +
      Module.finrank k ↥(V ⊓ J.restrictScalars k) = Module.finrank k V := by
  let φ : V →ₗ[k] (MvPolynomial (Fin 3) k ⧸ J) :=
    (Ideal.Quotient.mkₐ k J).toLinearMap.domRestrict V
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have hr : LinearMap.range φ = V.map (Ideal.Quotient.mkₐ k J).toLinearMap := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hk : LinearMap.ker φ = (V ⊓ J.restrictScalars k).comap V.subtype := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    show Ideal.Quotient.mk J x = 0 ↔ x ∈ V ⊓ J.restrictScalars k
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [hr, hk] at h
  rw [← h, (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : V ⊓ J.restrictScalars k ≤ V)).finrank_eq]
def filt (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    Submodule k (MvPolynomial (Fin 3) k) :=
  H2Count.box k ρ θ ⊓
    (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
      Ideal.span {levelForm c0 ^ j}).restrictScalars k
theorem filt_le (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    filt F c0 ρ θ j ≤ H2Count.box k ρ θ :=
  inf_le_left
theorem filt_finite (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    Module.Finite k ↥(filt F c0 ρ θ j) :=
  have := H2Count.finite_box k ρ θ
  Submodule.finiteDimensional_of_le (filt_le F c0 ρ θ j)
theorem filt_zero (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ : ℕ) :
    filt F c0 ρ θ 0 = H2Count.box k ρ θ := by
  rw [filt, pow_zero, Ideal.span_singleton_one, sup_top_eq, Submodule.restrictScalars_top,
    inf_top_eq]
theorem filt_inf (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    filt F c0 ρ θ j ⊓
      (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
        Ideal.span {levelForm c0 ^ (j + 1)}).restrictScalars k = filt F c0 ρ θ (j + 1) := by
  have hle : Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
      Ideal.span {levelForm c0 ^ (j + 1)} ≤
      Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔ Ideal.span {levelForm c0 ^ j} :=
    sup_le_sup_left ((Ideal.span_singleton_le_span_singleton).mpr (pow_dvd_pow _ j.le_succ)) _
  ext x
  simp only [filt, Submodule.mem_inf, Submodule.restrictScalars_mem]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hle h.2⟩, h.2⟩⟩
def shift (F : MvPolynomial (Fin 3) k) (c0 : k) (j : ℕ) :
    (MvPolynomial (Fin 3) k ⧸ Ideal.span ({F, levelForm c0} : Set (MvPolynomial (Fin 3) k)))
      →ₗ[k] MvPolynomial (Fin 3) k ⧸
        (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔ Ideal.span {levelForm c0 ^ (j + 1)}) :=
  (Submodule.liftQ
    ((Ideal.span ({F, levelForm c0} : Set (MvPolynomial (Fin 3) k))).restrictScalars k)
    ((Ideal.Quotient.mkₐ k (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
        Ideal.span {levelForm c0 ^ (j + 1)})).toLinearMap ∘ₗ
      LinearMap.mulLeft k (levelForm c0 ^ j)) (fun x hx => by
        obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
        rw [LinearMap.mem_ker]
        show Ideal.Quotient.mk _ (levelForm c0 ^ j * (a * F + b * levelForm c0)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have he : levelForm c0 ^ j * (a * F + b * levelForm c0) =
            levelForm c0 ^ j * a * F + b * levelForm c0 ^ (j + 1) := by ring
        rw [he]
        exact Ideal.add_mem _
          (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self F)))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))))).comp
    (Submodule.Quotient.restrictScalarsEquiv k
      (Ideal.span ({F, levelForm c0} : Set (MvPolynomial (Fin 3) k)))).symm.toLinearMap
theorem shift_mk (F : MvPolynomial (Fin 3) k) (c0 : k) (j : ℕ) (H : MvPolynomial (Fin 3) k) :
    shift F c0 j (Ideal.Quotient.mk _ H) = Ideal.Quotient.mk _ (levelForm c0 ^ j * H) :=
  rfl
theorem map_filt_le (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j : ℕ) :
    (filt F c0 ρ θ j).map (Ideal.Quotient.mkₐ k
        (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
          Ideal.span {levelForm c0 ^ (j + 1)})).toLinearMap ≤
      (layer F c0 ρ θ j).map (shift F c0 j) := by
  rintro _ ⟨G, hG, rfl⟩
  obtain ⟨hGbox, hGI⟩ := hG
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hGI
  obtain ⟨A, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  refine ⟨Ideal.Quotient.mk _ H, ⟨H, ?_, rfl⟩, ?_⟩
  · show levelForm c0 ^ j * H ∈ H2Count.box k ρ θ ⊔ _
    have he : levelForm c0 ^ j * H = G + (-A) * F := by rw [← huw]; ring
    rw [he]
    exact Submodule.add_mem_sup hGbox
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self F))
  · rw [shift_mk]
    show Ideal.Quotient.mk _ (levelForm c0 ^ j * H) = Ideal.Quotient.mk _ G
    rw [Ideal.Quotient.eq, ← huw]
    have he : levelForm c0 ^ j * H - (A * F + H * levelForm c0 ^ j) = (-A) * F := by ring
    rw [he]
    exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self F))
theorem finrank_filt_le (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ j ℓ : ℕ)
    (hl : Module.rank k (layer F c0 ρ θ j) ≤ (ℓ : Cardinal)) :
    Module.finrank k ↥(filt F c0 ρ θ j) ≤ Module.finrank k ↥(filt F c0 ρ θ (j + 1)) + ℓ := by
  have := filt_finite F c0 ρ θ j
  have h := finrank_map_mk_add (filt F c0 ρ θ j)
    (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔ Ideal.span {levelForm c0 ^ (j + 1)})
  rw [filt_inf] at h
  have hr : Module.rank k ((filt F c0 ρ θ j).map (Ideal.Quotient.mkₐ k
      (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) ⊔
        Ideal.span {levelForm c0 ^ (j + 1)})).toLinearMap) ≤ (ℓ : Cardinal) :=
    ((Submodule.rank_mono (map_filt_le F c0 ρ θ j)).trans (rank_map_le _ _)).trans hl
  have := Module.finrank_le_of_rank_le hr
  omega
theorem finrank_box_le (F : MvPolynomial (Fin 3) k) (c0 : k) (ρ θ ℓ : ℕ) :
    ∀ n : ℕ, (∀ j < n, Module.rank k (layer F c0 ρ θ j) ≤ (ℓ : Cardinal)) →
      Module.finrank k (H2Count.box k ρ θ) ≤ Module.finrank k ↥(filt F c0 ρ θ n) + n * ℓ
  | 0, _ => by rw [filt_zero, Nat.zero_mul, Nat.add_zero]
  | n + 1, h => by
      have h1 := finrank_box_le F c0 ρ θ ℓ n fun j hj => h j (Nat.lt_succ_of_lt hj)
      have h2 := finrank_filt_le F c0 ρ θ n ℓ (h n n.lt_succ_self)
      rw [Nat.succ_mul]
      omega
theorem count (k : Type) [Field k] : CountStatement k := by
  intro F c0 ρ θ n ℓ hlayer hcert
  have hV := H2Count.finite_box k ρ θ
  have h1 := finrank_box_le F c0 ρ θ ℓ n hlayer
  have h2 := finrank_map_mk_add (H2Count.box k ρ θ) (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)))
  have hfin := filt_finite F c0 ρ θ n
  have hex : ∃ G ∈ filt F c0 ρ θ n, G ∉ Ideal.span ({F} : Set (MvPolynomial (Fin 3) k)) := by
    by_contra hcon
    have hle : filt F c0 ρ θ n ≤ H2Count.box k ρ θ ⊓
        (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k))).restrictScalars k := fun G hG =>
      ⟨hG.1, by
        by_contra hGF
        exact hcon ⟨G, hG, hGF⟩⟩
    have := Submodule.finiteDimensional_of_le (inf_le_left : H2Count.box k ρ θ ⊓
      (Ideal.span ({F} : Set (MvPolynomial (Fin 3) k))).restrictScalars k ≤ H2Count.box k ρ θ)
    have h3 := Submodule.finrank_mono hle
    omega
  obtain ⟨G, hG, hGF⟩ := hex
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hG.2
  obtain ⟨A, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  exact ⟨G, hG.1, fun hdvd => hGF (Ideal.mem_span_singleton.mpr hdvd), A, H, by rw [← huw]; ring⟩
end Field
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
theorem levelForm_eq_linearForm {E : Type} [Field E] (c : E) :
    levelForm c = Sec.linearForm (fun m : Fin 3 => if m = 2 then (1 : E) else 0) - C c := by
  simp [levelForm, Sec.linearForm]
theorem BR_levelForm {E : Type} [Field E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (c : E) :
    RCN002.coordinateEvaluation E G (levelForm c) = coordinate E G 2 - algebraMap E (RCN002.CoordinateField E G) c := by
  rw [levelForm, map_sub, algHom_C]
  rfl
theorem goodValue_finite (P : Packet x t y r) : GoodValueStatement P := by
  intro N hN hNp hc
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hgood := Sec.finite_not_good
    (Finset.univ.image fun g : RCN222.GeometricFactor K P.F => (P.stage g).G) (baseH P.F)
    (fun m : Fin 3 => if m = 2 then (1 : Ω) else 0) 2 1 (by simp) (by decide) (fun g hg => by
      obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hg
      exact ⟨(P.stage g').MW, (P.stage g').BLO,
        Sec.not_dvd_linearMinor_noR _ 2 (by simp) (by simp) _
          (Sec.not_dvd_pderiv_self 1 _ (Sec.pderiv_stage_ne_zero P g'))⟩)
  have hunit : ∀ (g : RCN222.GeometricFactor K P.F) (j : Fin 3),
      {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (coordinate Ω (Exch.component P g) 2 - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (coordinate Ω (Exch.component P g) j) ≠ 1}.Finite :=
    fun g j => Data.finite_level_ne_one (hN g) hNp _ _ (hc g j)
  have hinj : Function.Injective (algebraMap (RationalBase K) Ω) :=
    (algebraMap (RationalBase K) Ω).injective
  refine (((Set.finite_singleton (0 : RationalBase K)).union (hgood.preimage hinj.injOn)).union
    (Set.finite_iUnion fun g => Set.finite_iUnion fun j =>
      (hunit g j).preimage hinj.injOn)).subset ?_
  intro c0 hc0
  by_contra hnot
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hnot
  obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
  refine hc0 ⟨fun h => h1 (Set.mem_singleton_iff.mpr h), fun g => ?_,
    fun g sR sY sZ nu hnu hlt j => ?_⟩
  · by_contra hbad
    refine h2 ⟨(P.stage g).G, Finset.mem_image_of_mem _ (Finset.mem_univ g), ?_⟩
    rwa [← levelForm_eq_linearForm]
  · by_contra hne
    refine h3 (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨j, nu, ⟨sR, sY, sZ, hnu⟩, ?_, hne⟩⟩)
    rwa [← BR_levelForm]
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Lev
open WithZero MvPolynomial
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Curve
def CurveStatement (E : Type) [Field E] [IsAlgClosed E] : Prop :=
  ∀ (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (_sep : RCN341.SeparableLiteralCoordinate D) (c0 : E) (n β γ : ℕ)
    (Ga H : MvPolynomial (Fin 3) E), RCN095.PolynomialInFlag ⟨0, β, γ⟩ Ga → Ga ∉ D →
    Ga - (MvPolynomial.X 2 - MvPolynomial.C c0) ^ n * H ∈ D →
    (∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E D), v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) < 1 →
      ∀ j, v.val (coordinate E D j) ≤ 1) →
    ∀ T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D)), ∃ T' : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D)),
      (n : ℤ) * ∑ v ∈ T, RCN204.flagPole v.val (coordinate E D) unitZFlag ≤
        (β : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E D) unitYZFlag +
          (γ : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E D) unitAllFlag
end Curve
section Packet
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE HFree6812 _Q7
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime
def LevelH2 (P : Packet x t y r) (n β γ : ℕ) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω) : Prop :=
  ∀ (s : ∀ g, Finset (LevelComponent (Exch.component P g) (Exch.moving P Q A g) c))
    (T : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω B.prime))),
    ∃ T' : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
        Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω B.prime)),
      (n : ℤ) * (∑ g, levelFlagSum (s g) (T g) unitZFlag) ≤
        (β : ℤ) * (∑ g, levelFlagSum (s g) (T' g) unitYZFlag) +
          (γ : ℤ) * (∑ g, levelFlagSum (s g) (T' g) unitAllFlag)
def LevelStatement (P : Packet x t y r) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (n β γ : ℕ) (_haux : H2Sec.ExistsAux P n β γ)
    (Q A : MvPolynomial (Fin 3) Ω) (_hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (_hA : RCN095.PolynomialInFlag unitYZFlag A),
    ∃ bad : Set Ω, bad.Finite ∧ ∀ c ∉ bad, LevelH2 P n β γ Q A c
def SectionBoundStatement (P : Packet x t y r) : Prop :=
  ∀ (n β γ : ℕ) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω), LevelH2 P n β γ Q A c →
    ∀ scale z u v : ℕ, SectionBound P scale z u v Q A c →
      SectionBound P (n * scale) (min (n * z) (β * u + γ * v)) (n * u) (n * v) Q A c
def PointBudgetStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (n β γ : ℕ) (_haux : H2Sec.ExistsAux P n β γ)
    (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (scale z u v : ℕ)
    (_hold : ∀ Q A : MvPolynomial (Fin 3) E, (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN f P.F SZ Q A scale z u v)
    (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
      AGN f P.F SZ Q A (n * scale) (min (n * z) (β * u + γ * v)) (n * u) (n * v)
end Packet
end
end H2Lev
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Deg
open scoped Classical BigOperators
open WithZero MvPolynomial
open RCN002 RCN013 RCN072 RCN084 RCN095 RCN114 RCN135 RCN136 RCN137 RCN222 RCN237 RCN264 RCN313 RCN340 RCN341
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT AVZ H2Sec
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Field
variable {E : Type} [Field E]
theorem levelForm_support (c : E) (d : Fin 3 →₀ ℕ) (hd : d ∈ (levelForm c).support) :
    d = Finsupp.single 2 1 ∨ d = 0 := by
  by_contra h
  rw [not_or] at h
  refine MvPolynomial.mem_support_iff.1 hd ?_
  simp [levelForm, MvPolynomial.coeff_X, MvPolynomial.coeff_C, Ne.symm h.1, Ne.symm h.2]
theorem levelForm_flag (c : E) : RCN095.PolynomialInFlag ⟨1, 0, 0⟩ (levelForm c) := by
  intro d hd
  rcases levelForm_support c d hd with rfl | rfl <;> simp [InFlag]
theorem levelForm_degreeOf_one (c : E) : (levelForm c).degreeOf 1 = 0 := by
  refine Nat.le_zero.1 ((MvPolynomial.degreeOf_le_iff).2 fun d hd => ?_)
  rcases levelForm_support c d hd with rfl | rfl <;> simp
theorem levelForm_degreeOf_two (c : E) : (levelForm c).degreeOf 2 ≤ 1 := by
  refine (MvPolynomial.degreeOf_le_iff).2 fun d hd => ?_
  rcases levelForm_support c d hd with rfl | rfl <;> simp
def lineEval (y c : E) : MvPolynomial (Fin 3) E →ₐ[E] Polynomial E :=
  MvPolynomial.aeval ![Polynomial.C y, Polynomial.X, Polynomial.C c]
theorem derivative_lineEval (y c : E) (A : MvPolynomial (Fin 3) E) :
    Polynomial.derivative (lineEval y c A) = lineEval y c (MvPolynomial.pderiv 1 A) := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [lineEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
      MvPolynomial.pderiv_X]
    fin_cases i <;> simp [lineEval]
theorem BR_eq_zero_iff (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (A : MvPolynomial (Fin 3) E) : RCN002.coordinateEvaluation E C A = 0 ↔ A ∈ C := by
  conv_rhs => rw [← RCN002.coordinateEvaluation_ker E C]
  rfl
theorem transcendental_coordinate_zero [IsAlgClosed E] (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (D : RCN341.SeparableLiteralCoordinate C) (g : MvPolynomial (Fin 3) E) (c : E) (hg : g ∈ C) (hc : levelForm c ∈ C)
    (hd : MvPolynomial.pderiv 1 g ∉ C) : Transcendental E (coordinate E C 0) := by
  intro hY
  have hZ : coordinate E C 2 = algebraMap E (RCN002.CoordinateField E C) c := by
    have h := (BR_eq_zero_iff C _).2 hc
    rw [levelForm, map_sub, MvPolynomial.algHom_C] at h
    exact sub_eq_zero.1 h
  obtain ⟨y, hy⟩ : ∃ y : E, algebraMap E (RCN002.CoordinateField E C) y = coordinate E C 0 :=
    minpoly.mem_range_of_degree_eq_one E _
      (IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hY.isIntegral))
  have hfac : ∀ A, RCN002.coordinateEvaluation E C A = Polynomial.aeval (coordinate E C 1) (lineEval y c A) := by
    have hy' : RCN002.coordinateEvaluation E C (MvPolynomial.X 0) = algebraMap E (RCN002.CoordinateField E C) y := hy.symm
    have hZ' : RCN002.coordinateEvaluation E C (MvPolynomial.X 2) = algebraMap E (RCN002.CoordinateField E C) c := hZ
    have h : (Polynomial.aeval (coordinate E C 1)).comp (lineEval y c) = RCN002.coordinateEvaluation E C := by
      refine MvPolynomial.algHom_ext fun i => ?_
      fin_cases i
      · simp [lineEval, hy']
      · simp [lineEval, coordinate]
      · simp [lineEval, hZ']
    intro A
    rw [← h]
    rfl
  have htr : Transcendental E (coordinate E C 1) := by
    have h := D.transcendental
    rcases (by omega : D.index = 0 ∨ D.index = 1 ∨ D.index = 2) with h0 | h1 | h2
    · rw [h0] at h
      exact absurd hY h
    · rwa [h1] at h
    · rw [h2, hZ] at h
      exact absurd (isAlgebraic_algebraMap c) h
  have h0 : lineEval y c g = 0 := by
    by_contra hne
    exact htr ⟨_, hne, by rw [← hfac, (BR_eq_zero_iff C g).2 hg]⟩
  exact hd ((BR_eq_zero_iff C _).1
    (by rw [hfac, ← derivative_lineEval, h0, Polynomial.derivative_zero, map_zero]))
theorem flagPole_le_cost [IsAlgClosed E] {G T H : MvPolynomial (Fin 3) E}
    {base : ∀ C : RCN264.RegularComponent E G T H, RCN341.SeparableLiteralCoordinate C.1} {p q : FlagDegree} (U : QZ base p q) (r : FlagDegree)
    (C : RCN264.RegularComponent E G T H) (W : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C.1))) :
    ∑ v ∈ W, RCN204.flagPole v.val (coordinate E C.1) r ≤ (U.toFE.weightedCost r C : ℤ) := by
  have hz : (∑ v ∈ W, RCN295.exponentSetPoleWeight v.val (coordinate E C.1) (flagSupport unitZFlag)) ≤ (U.zCost C : ℤ) :=
    U.zPole C W
  have hy : (∑ v ∈ W, RCN295.exponentSetPoleWeight v.val (coordinate E C.1) (flagSupport unitYZFlag)) ≤ (U.yzCost C : ℤ) :=
    U.yzPole C W
  have ha : (∑ v ∈ W, RCN295.exponentSetPoleWeight v.val (coordinate E C.1) (flagSupport unitAllFlag)) ≤ (U.allCost C : ℤ) :=
    U.allPole C W
  simp only [UC] at hz
  simp only [QD] at hy
  simp only [SF] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [RCN204.flagPole, Finset.sum_add_distrib, ← Finset.mul_sum, FE.weightedCost, QZ.toFE,
    Nat.cast_add, Nat.cast_mul] using h
end Field
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
theorem stage_pderiv_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    MvPolynomial.pderiv 1 (P.stage g).G ≠ 0 := by
  intro h
  obtain ⟨Q, hQ⟩ := (P.stage g).RR
  apply (P.stage g).BLO
  rw [← RCN267.surfaceMap_pderiv_R, hQ, MvPolynomial.pderiv_mul, h, zero_mul, zero_add]
  exact dvd_mul_right _ _
theorem stage_pderiv_notMem (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) (s : MvPolynomial (Fin 3) Ω)
    (C : RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F)) : MvPolynomial.pderiv 1 (P.stage g).G ∉ C.1 := by
  intro hd
  obtain ⟨Q, hQ⟩ := (P.stage g).RR
  apply _Q6 Ω _ _ _ C
  show surfaceMap (RCN135.polynomialEmbedding K) (MvPolynomial.pderiv 2 P.F) ∈ C.1
  rw [← RCN267.surfaceMap_pderiv_R, show surfaceMap (RCN135.polynomialEmbedding K) P.F = (P.stage g).G * Q from hQ, MvPolynomial.pderiv_mul]
  exact C.1.add_mem (C.1.mul_mem_right Q hd) (C.1.mul_mem_right _ (EN Ω _ _ _ C))
theorem section_degree (P : Packet x t y r) : H2Sec.SectionDegreeStatement P := by
  intro c0 h0 rhi yhi hr hy
  have hF : baseCarrier P.F ≠ 0 := RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero
  have ht := packet_t_le P
  have htot : (exactFlag (baseCarrier P.F)).zOnly + (exactFlag (baseCarrier P.F)).yz +
      (exactFlag (baseCarrier P.F)).all ≤ t := by
    have h1 : MvPolynomial.weightedTotalDegree RCN095.flagTotalWeights (baseCarrier P.F) ≤ t - y + (y - r) + r :=
      (RCN084.inFlag_weight_caps _ _ (P.parent_flag Ω (RCN135.polynomialEmbedding K))).2.2
    have h2 := P.ylow
    have h3 := P.yt
    rw [(RCN084.exactFlag_cumulative _).2.2]
    omega
  have hdeg : ∀ (g : RCN222.GeometricFactor K P.F) (j : Fin 3), g.1.degreeOf j < 2130706433 := fun g j =>
    lt_of_le_of_lt ((RCN137.coordinate_degree_le_of_dvd j g.1 _ (RCN137.surfaceFactors_spec (RCN135.polynomialEmbedding K) P.F g.1 g.2).2 hF).trans
      ((RCN084.degreeOf_le_flag_total _ _ (RCN084.polynomialIn_exactFlag (baseCarrier P.F)) j).trans htot)) (by omega)
  obtain ⟨B⟩ := EFX (baseCarrier P.F) (levelΩ c0) (baseH P.F) (exactFlag (baseCarrier P.F)) ⟨1, 0, 0⟩ hF
    (RCN084.polynomialIn_exactFlag _) (levelForm_flag _) 2130706433 (by omega)
    (by show 2 * (_ + _ + _) * (1 + 0 + 0) < 2130706433; omega)
  have hmem : ∀ g : RCN222.GeometricFactor K P.F, g.1 ∈ RCN084.activeFactors (baseCarrier P.F) (levelΩ c0) := fun g =>
    Finset.mem_filter.2 ⟨g.2, (h0.good g).1, stage_pderiv_ne_zero P g⟩
  have hinj : Function.Injective fun g : RCN222.GeometricFactor K P.F =>
      (⟨g.1, hmem g⟩ : ↥(RCN084.activeFactors (baseCarrier P.F) (levelΩ c0))) := fun g g' h =>
    Subtype.ext (Subtype.mk.inj h)
  have hall : (exactFlag (baseCarrier P.F)).all ≤ rhi := by
    rw [(RCN084.exactFlag_cumulative _).1]
    refine Finset.sup_le fun d hd => ?_
    rw [RCN095.flag_weight_fin3]
    simpa [flagSWeights] using (MvPolynomial.monomial_le_degreeOf 1 hd).trans hr
  have hyz : (exactFlag (baseCarrier P.F)).yz + (exactFlag (baseCarrier P.F)).all ≤ yhi := by
    rw [(RCN084.exactFlag_cumulative _).2.1]
    refine Finset.sup_le fun d hd => ?_
    rw [RCN095.flag_weight_fin3]
    simpa [RCN095.flagYSWeights] using hy d hd
  constructor
  · have hcard : ∀ g : RCN222.GeometricFactor K P.F,
        Fintype.card (RCN264.RegularComponent Ω (P.stage g).G (levelΩ c0) (baseH P.F)) ≤ g.1.degreeOf 1 := by
      intro g
      have ht0 : ∀ C : RCN264.RegularComponent Ω (P.stage g).G (levelΩ c0) (baseH P.F),
          Transcendental Ω (coordinate Ω C.1 ((Equiv.swap (1 : Fin 3) 2) 0)) := fun C => by
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact transcendental_coordinate_zero C.1 (B.base ⟨g.1, hmem g⟩ C) _ _ (EN Ω _ _ _ C)
          (GV Ω _ _ _ C) (stage_pderiv_notMem P g _ C)
      have hMD : RCN013.originalMixedDegree Ω (Equiv.swap (1 : Fin 3) 2) g.1 (levelΩ c0) ≤ g.1.degreeOf 1 := by
        unfold RCN013.originalMixedDegree
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right, levelForm_degreeOf_one, mul_zero, add_zero]
        exact (Nat.mul_le_mul_right _ (levelForm_degreeOf_two _)).trans (one_mul _).le
      obtain ⟨hfin, hsum⟩ := RCN004.BQE Ω (Equiv.swap (1 : Fin 3) 2)
        (fun C : RCN264.RegularComponent Ω (P.stage g).G (levelΩ c0) (baseH P.F) => C.1) ht0 (fun _ _ h => Subtype.ext h)
        2130706433 g.1 (levelΩ c0) (RCN137.surfaceFactors_spec (RCN135.polynomialEmbedding K) P.F g.1 g.2).1 (fun C => EN Ω _ _ _ C)
        (fun C => GV Ω _ _ _ C) (h0.good g).1 (hdeg g _) (hdeg g _)
        (lt_of_le_of_lt hMD (hdeg g 1))
      refine le_trans ?_ (hsum.trans hMD)
      rw [Fintype.card_eq_sum_ones]
      refine Finset.sum_le_sum fun C _ => ?_
      let _ : Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1) := RCN005.rationalBaseAlgebra Ω C.1 _ (ht0 C)
      have : FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1) := (hfin C).1
      exact Module.finrank_pos
    calc Fintype.card (SectionComponent P c0)
        = ∑ g : RCN222.GeometricFactor K P.F, Fintype.card (RCN264.RegularComponent Ω (P.stage g).G (levelΩ c0) (baseH P.F)) :=
          Fintype.card_sigma
      _ ≤ ∑ g : RCN222.GeometricFactor K P.F, g.1.degreeOf 1 := Finset.sum_le_sum fun g _ => hcard g
      _ = ∑ g ∈ RCN137.normalizedFactorSet (baseCarrier P.F), g.degreeOf 1 :=
          Finset.sum_coe_sort (RCN137.normalizedFactorSet (baseCarrier P.F)) fun g => g.degreeOf 1
      _ ≤ (baseCarrier P.F).degreeOf 1 := RCN137.sum_coordinate_degrees_le_of_prod_dvd (RCN137.normalizedFactorSet (baseCarrier P.F)) id _ hF (RCN137.normalizedFactorSet_product_dvd _ hF) 1
      _ ≤ rhi := hr
  · intro β γ T
    have hsum : (∑ a : SectionComponent P c0,
        (B.unit ⟨a.1.1, hmem a.1⟩).toFE.weightedCost ⟨0, β, γ⟩ a.2) ≤ β * rhi + γ * yhi := by
      rw [Fintype.sum_sigma]
      calc _ = ∑ g' ∈ Finset.univ.image fun g : RCN222.GeometricFactor K P.F =>
              (⟨g.1, hmem g⟩ : ↥(RCN084.activeFactors (baseCarrier P.F) (levelΩ c0))),
            ∑ C : RCN264.RegularComponent Ω g'.1 (levelΩ c0) (baseH P.F), (B.unit g').toFE.weightedCost ⟨0, β, γ⟩ C :=
            (Finset.sum_image fun _ _ _ _ h => hinj h).symm
        _ ≤ ∑ g' : ↥(RCN084.activeFactors (baseCarrier P.F) (levelΩ c0)),
            ∑ C : RCN264.RegularComponent Ω g'.1 (levelΩ c0) (baseH P.F), (B.unit g').toFE.weightedCost ⟨0, β, γ⟩ C :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ ≤ flagMixed (exactFlag (baseCarrier P.F)) ⟨1, 0, 0⟩ ⟨0, β, γ⟩ :=
            sum_cost_le _ _ _ _ _ _ hF (RCN084.polynomialIn_exactFlag _) B
        _ = β * (exactFlag (baseCarrier P.F)).all +
              γ * ((exactFlag (baseCarrier P.F)).yz + (exactFlag (baseCarrier P.F)).all) := by
            simp only [flagMixed]
            ring
        _ ≤ β * rhi + γ * yhi :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hall) (Nat.mul_le_mul_left _ hyz)
    calc ∑ a, ∑ v ∈ T a, RCN204.flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩
        ≤ ∑ a : SectionComponent P c0,
            (((B.unit ⟨a.1.1, hmem a.1⟩).toFE.weightedCost ⟨0, β, γ⟩ a.2 : ℕ) : ℤ) :=
          Finset.sum_le_sum fun a _ => flagPole_le_cost (B.unit ⟨a.1.1, hmem a.1⟩) ⟨0, β, γ⟩ a.2 (T a)
      _ ≤ ((β * rhi + γ * yhi : ℕ) : ℤ) := by exact_mod_cast hsum
end Packet
end
end H2Deg
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
omit [CharP K 2130706433] in
theorem map_carrierK (P : Packet x t y r) :
    MvPolynomial.map (algebraMap (RationalBase K) Ω) (carrierK P) = baseCarrier P.F := by
  show MvPolynomial.map _ (MvPolynomial.map _ (collectX K P.F)) =
    MvPolynomial.map (RCN135.polynomialEmbedding K) (collectX K P.F)
  rw [MvPolynomial.map_map]
  rfl
omit [CharP K 2130706433] in
theorem map_levelForm (c0 : RationalBase K) :
    MvPolynomial.map (algebraMap (RationalBase K) Ω) (levelForm c0) = levelΩ c0 := by
  simp [levelForm]
theorem evZ_stage_ne_zero (P : Packet x t y r) (c0 : RationalBase K) (h0 : GoodValue P c0)
    (g : RCN222.GeometricFactor K P.F) : evZ (algebraMap (RationalBase K) Ω c0) (P.stage g).G ≠ 0 := by
  intro hz
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp (mem_span_levelForm_of_evZ _ _ hz)
  rcases (P.stage g).MW.isUnit_or_isUnit hu with hs | hu'
  · have h1 := hs.map (evZ (algebraMap (RationalBase K) Ω c0))
    rw [evZ_levelForm] at h1
    exact not_isUnit_zero h1
  · obtain ⟨v, hv⟩ := hu'.exists_right_inv
    exact (h0.good g).1 ⟨v, by rw [hu, mul_assoc, hv, mul_one]⟩
theorem mem_span_of_forall_component (P : Packet x t y r) (c0 : RationalBase K) (h0 : GoodValue P c0)
    (z : MvPolynomial (Fin 3) Ω) (hz : ∀ a : SectionComponent P c0, z ∈ a.2.1) :
    z ∈ Ideal.span ({baseCarrier P.F, levelΩ c0} : Set (MvPolynomial (Fin 3) Ω)) := by
  have hne : baseCarrier P.F ≠ 0 := RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero
  refine mem_span_of_section _ _ z ?_ ?_
  · intro hF0
    obtain ⟨F, hF, hF0'⟩ := RCN137.exists_normalizedFactorSet_zero (evZ (algebraMap (RationalBase K) Ω c0)).toRingHom
      (baseCarrier P.F) hne hF0
    exact evZ_stage_ne_zero P c0 h0 ⟨F, hF⟩ hF0'
  · intro q hq hqF
    have hqp : (Ideal.span ({q} : Set (MvPolynomial (Fin 2) Ω))).IsPrime :=
      (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    obtain ⟨F, hF, hF0⟩ := RCN137.exists_normalizedFactorSet_zero
      ((Ideal.Quotient.mk (Ideal.span ({q} : Set (MvPolynomial (Fin 2) Ω)))).comp
        (evZ (algebraMap (RationalBase K) Ω c0)).toRingHom) (baseCarrier P.F) hne
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hqF))
    have hqg : q ∣ evZ (algebraMap (RationalBase K) Ω c0) F :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hF0)
    have hmin := comap_mem_minimalPrimes _ (P.stage ⟨F, hF⟩).G
      (evZ_stage_ne_zero P c0 h0 ⟨F, hF⟩) q hq hqg
    have hAUR : Ideal.comap (evZ (algebraMap (RationalBase K) Ω c0)) (Ideal.span {q}) ∈
        RCN072.componentFamily Ω (P.stage ⟨F, hF⟩).G (levelΩ c0) := (RCN072.mem_componentFamily Ω _ _ _).mpr hmin
    have hgood := (h0.good ⟨F, hF⟩).2 _ hAUR
    refine ⟨fun hd => hgood.1 (Ideal.mem_comap.mpr ?_), ?_⟩
    · rw [show baseH P.F = pderiv 1 (baseCarrier P.F) from (RCN267.surfaceMap_pderiv_R (RCN135.polynomialEmbedding K) P.F).symm]
      exact Ideal.mem_span_singleton.mpr hd
    · exact Ideal.mem_span_singleton.mp
        (Ideal.mem_comap.mp (hz ⟨⟨F, hF⟩, ⟨_, (AJF Ω).mpr ⟨hAUR, hgood.1⟩⟩⟩))
theorem sectionEmbedding (P : Packet x t y r) : SectionEmbeddingStatement P := by
  intro c0 h0 ι _ H hH
  rw [Fintype.linearIndependent_iff]
  intro cc hcc i
  have hmem : ∀ a : SectionComponent P c0,
      (∑ i, MvPolynomial.C (cc i) * MvPolynomial.map (algebraMap (RationalBase K) Ω) (H i)) ∈
        a.2.1 := by
    intro a
    have h1 := congrFun hcc a
    rw [Finset.sum_apply, Pi.zero_apply] at h1
    rw [← Sec.BR_eq_zero_iff, map_sum, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, algHom_C, Pi.smul_apply, Algebra.smul_def]
  have h1 := mem_span_of_forall_component P c0 h0 _ hmem
  have hmap : (Ideal.span ({carrierK P, levelForm c0} :
      Set (MvPolynomial (Fin 3) (RationalBase K)))).map
        (MvPolynomial.map (algebraMap (RationalBase K) Ω)) =
      Ideal.span {baseCarrier P.F, levelΩ c0} := by
    rw [Ideal.map_span, Set.image_pair, map_carrierK, map_levelForm]
  rw [← hmap] at h1
  exact eq_zero_of_sum_mem_map _ H hH Finset.univ cc h1 i (Finset.mem_univ i)
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Lev
open WithZero MvPolynomial
open RCN002 RCN095 RCN187
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Curve
theorem poleOrder_eq_zero {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) {y : L} (h : v y ≤ 1) :
    poleOrder v y = 0 := by
  rw [poleOrder]
  by_cases h0 : v y = 0
  · rw [h0, log_zero, max_self]
  · exact max_eq_left ((log_le_iff_le_exp h0).mpr (by rwa [exp_zero]))
variable {E : Type} [Field E] {D : Ideal (MvPolynomial (Fin 3) E)} [D.IsPrime]
omit [D.IsPrime] in
theorem BR_levelForm (c0 : E) :
    RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0) =
      coordinate E D 2 - algebraMap E (RCN002.CoordinateField E D) c0 := by
  rw [map_sub, algHom_C]
  rfl
theorem val_coordinate_le_one (v : RCN026.Place_p19 E (RCN002.CoordinateField E D)) (c0 : E)
    (h : v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) ≤ 1) :
    v.val (coordinate E D 2) ≤ 1 := by
  by_contra hlt
  rw [BR_levelForm, Valuation.map_sub_eq_of_lt_left _
    (lt_of_le_of_lt (RCN344.NP E (RCN002.CoordinateField E D) v c0) (not_le.mp hlt))] at h
  exact hlt h
theorem order_levelForm_add (v : RCN026.Place_p19 E (RCN002.CoordinateField E D)) (c0 : E)
    (h : 1 ≤ v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0))) :
    RCN026.order_p19 E (RCN002.CoordinateField E D) v (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) +
      poleOrder v.val (coordinate E D 2) = 0 := by
  rw [RCN026.order_p19]
  by_cases hlt : 1 < v.val (coordinate E D 2)
  · have h0 : v.val (coordinate E D 2) ≠ 0 := ne_of_gt (zero_lt_one.trans hlt)
    have hlog : 0 < (v.val (coordinate E D 2)).log := (lt_log_iff_exp_lt h0).mpr (by rwa [exp_zero])
    rw [BR_levelForm, Valuation.map_sub_eq_of_lt_left _
      (lt_of_le_of_lt (RCN344.NP E (RCN002.CoordinateField E D) v c0) hlt), poleOrder, max_eq_right hlog.le]
    exact neg_add_cancel _
  · have h1 : v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) = 1 := by
      refine le_antisymm ?_ h
      rw [BR_levelForm]
      exact (Valuation.map_sub _ _ _).trans (max_le (not_lt.mp hlt) (RCN344.NP E (RCN002.CoordinateField E D) v c0))
    rw [h1, log_one, neg_zero, zero_add, poleOrder_eq_zero _ (not_lt.mp hlt)]
theorem order_aux_ge (v : RCN026.Place_p19 E (RCN002.CoordinateField E D)) (c0 : E) (n β γ : ℕ)
    (Ga H : MvPolynomial (Fin 3) E) (hflag : RCN095.PolynomialInFlag ⟨0, β, γ⟩ Ga) (hγ0 : RCN002.coordinateEvaluation E D Ga ≠ 0)
    (hprod : RCN002.coordinateEvaluation E D Ga = RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0) ^ n * RCN002.coordinateEvaluation E D H)
    (hη : v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) < 1 →
      v.val (RCN002.coordinateEvaluation E D H) ≤ exp ((β : ℤ) * RCN204.flagPole v.val (coordinate E D) unitYZFlag +
        (γ : ℤ) * RCN204.flagPole v.val (coordinate E D) unitAllFlag)) :
    (n : ℤ) * (RCN026.order_p19 E (RCN002.CoordinateField E D) v (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) +
        poleOrder v.val (coordinate E D 2)) ≤
      RCN026.order_p19 E (RCN002.CoordinateField E D) v (RCN002.coordinateEvaluation E D Ga) +
        ((β : ℤ) * RCN204.flagPole v.val (coordinate E D) unitYZFlag +
          (γ : ℤ) * RCN204.flagPole v.val (coordinate E D) unitAllFlag) := by
  have hv0 : v.val (RCN002.coordinateEvaluation E D Ga) ≠ 0 := (Valuation.ne_zero_iff _).mpr hγ0
  have hYZ := RCN204.flagPole_nonneg v.val (coordinate E D) unitYZFlag
  have hAll := RCN204.flagPole_nonneg v.val (coordinate E D) unitAllFlag
  have hβ := mul_nonneg (Nat.cast_nonneg (α := ℤ) β) hYZ
  have hγ := mul_nonneg (Nat.cast_nonneg (α := ℤ) γ) hAll
  by_cases h : v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) < 1
  · have hprod0 := hv0
    rw [hprod, map_mul, map_pow] at hprod0
    have hpow0 := left_ne_zero_of_mul hprod0
    have hle : v.val (RCN002.coordinateEvaluation E D Ga) ≤
        v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) ^ n *
          exp ((β : ℤ) * RCN204.flagPole v.val (coordinate E D) unitYZFlag +
            (γ : ℤ) * RCN204.flagPole v.val (coordinate E D) unitAllFlag) := by
      rw [hprod, map_mul, map_pow]
      exact mul_le_mul' le_rfl (hη h)
    have hlog := (log_le_log hv0 (mul_ne_zero hpow0 exp_ne_zero)).mpr hle
    rw [log_mul hpow0 exp_ne_zero, log_pow, nsmul_eq_mul, log_exp] at hlog
    rw [poleOrder_eq_zero _ (val_coordinate_le_one v c0 h.le), add_zero, RCN026.order_p19, RCN026.order_p19]
    linarith
  · have hpole : (v.val (RCN002.coordinateEvaluation E D Ga)).log ≤
        (β : ℤ) * RCN204.flagPole v.val (coordinate E D) unitYZFlag +
          (γ : ℤ) * RCN204.flagPole v.val (coordinate E D) unitAllFlag := by
      have hA := RCN204.valuation_eval_le_flag v.val (algebraMap E (RCN002.CoordinateField E D)) (RCN344.NP E (RCN002.CoordinateField E D) v)
        (coordinate E D) ⟨0, β, γ⟩ Ga hflag
      rw [show MvPolynomial.eval₂Hom (algebraMap E (RCN002.CoordinateField E D)) (coordinate E D) Ga = RCN002.coordinateEvaluation E D Ga from by
        rw [RCN002.coordinateEvaluation_eq_aeval]
        exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm] at hA
      have hlog := (log_le_iff_le_exp hv0).mpr hA
      rw [RCN204.flagPole_unitYZ, RCN204.flagPole_unitAll]
      simpa only [RCN204.flagPole, Nat.cast_zero, zero_mul, zero_add] using hlog
    rw [order_levelForm_add v c0 (not_lt.mp h), mul_zero, RCN026.order_p19]
    linarith
end Curve
section Statement
variable {E : Type} [Field E] [IsAlgClosed E] {D : Ideal (MvPolynomial (Fin 3) E)} [D.IsPrime]
theorem curve_of_pole (sep : RCN341.SeparableLiteralCoordinate D) (c0 : E) (n β γ : ℕ) (Ga H : MvPolynomial (Fin 3) E)
    (hflag : RCN095.PolynomialInFlag ⟨0, β, γ⟩ Ga) (hGa : Ga ∉ D)
    (hmem : Ga - (MvPolynomial.X 2 - MvPolynomial.C c0) ^ n * H ∈ D)
    (hη : ∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E D),
      v.val (RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0)) < 1 →
      v.val (RCN002.coordinateEvaluation E D H) ≤ exp ((β : ℤ) * RCN204.flagPole v.val (coordinate E D) unitYZFlag +
        (γ : ℤ) * RCN204.flagPole v.val (coordinate E D) unitAllFlag))
    (T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D))) :
    ∃ T' : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D)),
      (n : ℤ) * ∑ v ∈ T, RCN204.flagPole v.val (coordinate E D) unitZFlag ≤
        (β : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E D) unitYZFlag +
          (γ : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E D) unitAllFlag := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, by simp⟩
  have hγ0 : RCN002.coordinateEvaluation E D Ga ≠ 0 := fun h => hGa ((Sec.BR_eq_zero_iff (G := D) Ga).mp h)
  have hprod : RCN002.coordinateEvaluation E D Ga = RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0) ^ n * RCN002.coordinateEvaluation E D H := by
    have h := (Sec.BR_eq_zero_iff (G := D) _).mpr hmem
    rwa [map_sub, map_mul, map_pow, sub_eq_zero] at h
  have hζ0 : RCN002.coordinateEvaluation E D (MvPolynomial.X 2 - MvPolynomial.C c0) ≠ 0 := fun h =>
    hγ0 (by rw [hprod, h, zero_pow hn.ne', zero_mul])
  obtain ⟨T1, hT1⟩ := LevelCount.exists_sum_order_eq_zero sep _ hγ0
  obtain ⟨T2, hT2⟩ := LevelCount.exists_sum_order_eq_zero sep _ hζ0
  refine ⟨T ∪ (T1 ∪ T2), ?_⟩
  have h1 := hT1 (T ∪ (T1 ∪ T2))
    (fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ hv))
  have h2 := hT2 (T ∪ (T1 ∪ T2))
    (fun v hv => Finset.mem_union_right _ (Finset.mem_union_right _ hv))
  have hkey := Finset.sum_le_sum fun v (_ : v ∈ T ∪ (T1 ∪ T2)) =>
    order_aux_ge v c0 n β γ Ga H hflag hγ0 hprod (hη v)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, h2, zero_add, Finset.sum_add_distrib, h1, zero_add,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hkey
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)) hkey
  have hZ : ∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E D),
      RCN204.flagPole v.val (coordinate E D) unitZFlag = poleOrder v.val (coordinate E D 2) :=
    fun v => by simp [RCN204.flagPole, unitZFlag]
  simp only [hZ]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun v _ _ => le_max_left 0 _
end Statement
theorem curve (E : Type) [Field E] [IsAlgClosed E] : CurveStatement E := by
  intro D _ sep c0 n β γ Ga H hflag hGa hmem hfin T
  refine curve_of_pole sep c0 n β γ Ga H hflag hGa hmem (fun v hv => ?_) T
  refine (Sec.place_BR_le_one v (hfin v hv) H).trans ?_
  rw [← exp_zero, exp_le_exp]
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg β) (RCN204.flagPole_nonneg v.val (coordinate E D) unitYZFlag))
    (mul_nonneg (Nat.cast_nonneg γ) (RCN204.flagPole_nonneg v.val (coordinate E D) unitAllFlag))
end
end H2Lev
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
open scoped Classical
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
abbrev LevelCurve (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) {E : Type} [Field E]
    (f : GenericField K →+* E) (Q A : MvPolynomial (Fin 3) E) : Type :=
  RCN264.RegularComponent (GenericField E) (OO f P.F) (XC f P.F Q A) (AOT f P.F A * SZ.leading ((RCN135.coefficientEmbedding E).comp (codeMap f)))
def GoodCurve (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) {E : Type} [Field E]
    (f : GenericField K →+* E) (Q A : MvPolynomial (Fin 3) E) (V : LevelCurve P SZ f Q A) : Prop :=
  Nonempty (RCN341.SeparableLiteralCoordinate V.1) ∧ V.1.height = 2 ∧
    ∃ g : MvPolynomial (Fin 3) (GenericField E),
      Irreducible g ∧ g ∣ OO f P.F ∧ g ∈ V.1 ∧ ¬g ∣ XC f P.F Q A
def CountedStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    ∀ (cut : MvPolynomial (Fin 3) (GenericField E)) (points : Finset (Fin 3 → GenericField E)),
      (∀ w ∈ points, MvPolynomial.eval w (OO f P.F) = 0) →
      (∀ w ∈ points, MvPolynomial.eval w (XC f P.F Q A) = 0) →
      (∀ w ∈ points,
        MvPolynomial.eval w (AOT f P.F A * SZ.leading ((RCN135.coefficientEmbedding E).comp (codeMap f))) ≠ 0) →
      (∀ w ∈ points, MvPolynomial.aeval w cut = 0) →
      (∀ w ∈ points, RCN084.IsolatedPoint (OO f P.F) (XC f P.F Q A) cut w) →
      ∃ (S : Finset (LevelCurve P SZ f Q A))
        (T : ∀ V : LevelCurve P SZ f Q A,
          Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1))),
        (∀ V ∈ S, GoodCurve P SZ f Q A V ∧ cut ∉ V.1 ∧
          ∀ μ ∈ T V, μ.val (RCN002.coordinateEvaluation (GenericField E) V.1 cut) < 1) ∧
        points.card ≤ ∑ V ∈ S, (T V).card
def CurveH2Statement (P : Packet x t y r) : Prop :=
  ∀ (n β γ : ℕ), H2Sec.ExistsAux P n β γ →
  ∀ (E : Type) [Field E] [IsAlgClosed E] (f : GenericField K →+* E) (Q A : MvPolynomial (Fin 3) E)
    (D : Ideal (MvPolynomial (Fin 3) (GenericField E))) [D.IsPrime] (_sep : RCN341.SeparableLiteralCoordinate D),
    OO f P.F ∈ D → XC f P.F Q A ∈ D →
    surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) (RCN313.polyH K P.F) ∉ D →
    (∀ w : Fin 3 → GenericField E, D ≠ RingHom.ker (MvPolynomial.aeval w).toRingHom) →
    ∀ T : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) D)),
      ∃ T' : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) D)),
        (n : ℤ) * ∑ v ∈ T, RCN204.flagPole v.val (coordinate (GenericField E) D) unitZFlag ≤
          (β : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate (GenericField E) D) unitYZFlag +
            (γ : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate (GenericField E) D) unitAllFlag
def SeparableFormStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    ∀ V : LevelCurve P SZ f Q A, GoodCurve P SZ f Q A V →
    ∀ ℓ : MvPolynomial (Fin 3) (GenericField E), RCN095.PolynomialInFlag unitAllFlag ℓ →
    ∀ [Algebra (RatFunc (GenericField E)) (RCN002.CoordinateField (GenericField E) V.1)]
      [IsScalarTower (GenericField E) (RatFunc (GenericField E)) (RCN002.CoordinateField (GenericField E) V.1)],
      algebraMap (RatFunc (GenericField E)) (RCN002.CoordinateField (GenericField E) V.1) RatFunc.X =
          RCN002.coordinateEvaluation (GenericField E) V.1 ℓ →
        FiniteDimensional (RatFunc (GenericField E)) (RCN002.CoordinateField (GenericField E) V.1) ∧
          Algebra.IsSeparable (RatFunc (GenericField E)) (RCN002.CoordinateField (GenericField E) V.1)
def IsolatedStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    ∀ V : LevelCurve P SZ f Q A, GoodCurve P SZ f Q A V →
    ∃ h : MvPolynomial (Fin 3) (GenericField E), h ∉ V.1 ∧
      ∀ w : Fin 3 → GenericField E, V.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom →
        MvPolynomial.eval w h ≠ 0 →
        MvPolynomial.eval w (AOT f P.F A * SZ.leading ((RCN135.coefficientEmbedding E).comp (codeMap f))) ≠ 0 ∧
        (∀ V' : LevelCurve P SZ f Q A,
          V'.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom → V' = V) ∧
        ∀ cut : MvPolynomial (Fin 3) (GenericField E), cut ∉ V.1 →
          RCN084.IsolatedPoint (OO f P.F) (XC f P.F Q A) cut w
def FibreBoundStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    ∀ V : LevelCurve P SZ f Q A, GoodCurve P SZ f Q A V →
    ∀ ℓ g : MvPolynomial (Fin 3) (GenericField E), RCN095.PolynomialInFlag unitAllFlag ℓ →
      (∀ a : GenericField E, ℓ - MvPolynomial.C a ∉ V.1) → g ∉ V.1 →
      {a : GenericField E | ¬∃ pts : Finset (Fin 3 → GenericField E),
        (∀ w ∈ pts, V.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom ∧
          MvPolynomial.eval w ℓ = a ∧ MvPolynomial.eval w g ≠ 0) ∧
        ∀ U : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1)),
          ∑ v ∈ U, RCN187.poleOrder v.val (RCN002.coordinateEvaluation (GenericField E) V.1 ℓ) ≤ (pts.card : ℤ)}.Finite
def UnitBoundStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  ∀ (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (scale z u v : ℕ) (Q A : MvPolynomial (Fin 3) E), (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN f P.F SZ Q A scale z u v →
    ∀ S : Finset (LevelCurve P SZ f Q A), (∀ V ∈ S, GoodCurve P SZ f Q A V) →
    ∀ U : ∀ V : LevelCurve P SZ f Q A,
        Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1)),
      (scale : ℤ) * ∑ V ∈ S, ∑ μ ∈ U V,
          RCN204.flagPole μ.val (coordinate (GenericField E) V.1) unitYZFlag ≤ u ∧
        (scale : ℤ) * ∑ V ∈ S, ∑ μ ∈ U V,
          RCN204.flagPole μ.val (coordinate (GenericField E) V.1) unitAllFlag ≤ v
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN204 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT AVZ
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
theorem section_sep (P : Packet x t y r) (c0 : RationalBase K) (h0 : GoodValue P c0)
    (a : SectionComponent P c0) : Nonempty (RCN341.SeparableLiteralCoordinate a.2.1) := by
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hthi := packet_t_le P
  have hylo := P.ylow
  have hyt := P.yt
  have hflag : RCN095.PolynomialInFlag ⟨1, 0, 0⟩ (levelΩ c0) := by
    rw [levelΩ, levelForm_eq_linearForm]
    exact Sec.linearForm_sub_C_inFlag _ _ _ (by simp) (by simp) (by simp)
  obtain ⟨B⟩ := EFX (baseCarrier P.F) (levelΩ c0) (baseH P.F) ⟨t - y, y - r, r⟩ ⟨1, 0, 0⟩
    (RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero) (P.parent_flag Ω (RCN135.polynomialEmbedding K)) hflag
    2130706433
    (by show t - y + (y - r) + r < 2130706433; omega)
    (by show 2 * (t - y + (y - r) + r) * (1 + 0 + 0) < 2130706433; omega)
  exact ⟨B.base ⟨(P.stage a.1).G, Finset.mem_filter.mpr
    ⟨a.1.2, (h0.good a.1).1, Sec.pderiv_stage_ne_zero P a.1⟩⟩ a.2⟩
theorem finite_flagPole_pos (P : Packet x t y r) (c0 : RationalBase K) (W : FlagDegree) (b : ℕ)
    (hsum : ∀ T : ∀ a : SectionComponent P c0, Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1)),
      ∑ a, ∑ v ∈ T a, flagPole v.val (coordinate Ω a.2.1) W ≤ (b : ℤ))
    (a : SectionComponent P c0) :
    {v : RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1) | 0 < flagPole v.val (coordinate Ω a.2.1) W}.Finite := by
  by_contra hinf
  obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (b + 1)
  have h1 := hsum (Function.update (fun _ => ∅) a T)
  have h2 : ∑ v ∈ T, flagPole v.val (coordinate Ω a.2.1) W ≤
      ∑ a', ∑ v ∈ Function.update
        (fun a' : SectionComponent P c0 => (∅ : Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a'.2.1)))) a T a',
          flagPole v.val (coordinate Ω a'.2.1) W := by
    have h3 := Finset.single_le_sum (f := fun a' : SectionComponent P c0 =>
      ∑ v ∈ Function.update
        (fun a' : SectionComponent P c0 => (∅ : Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a'.2.1)))) a T a',
          flagPole v.val (coordinate Ω a'.2.1) W)
      (fun a' _ => Finset.sum_nonneg fun v _ => RCN204.flagPole_nonneg _ _ _) (Finset.mem_univ a)
    simpa only [Function.update_self] using h3
  have h4 : ((b + 1 : ℕ) : ℤ) ≤ ∑ v ∈ T, flagPole v.val (coordinate Ω a.2.1) W := by
    rw [← hTcard, Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun v hv => by
      have h5 : 0 < flagPole v.val (coordinate Ω a.2.1) W := hTsub hv
      rw [Nat.cast_one]
      omega
  have h6 := h4.trans (h2.trans h1)
  push_cast at h6
  omega
theorem layerBound_of (P : Packet x t y r) (hdeg : SectionDegreeStatement P)
    (hpole : PoleSpaceStatement (GenericField K)) : LayerBoundStatement P := by
  intro N hN hNp hc c0 h0 β γ rhi yhi hr hy j
  obtain ⟨hcard, hsum⟩ := hdeg c0 h0 rhi yhi hr hy
  refine rank_le fun s hs => ?_
  have hrep : ∀ i : s, ∃ H G A : MvPolynomial (Fin 3) (RationalBase K),
      Ideal.Quotient.mk (Ideal.span ({carrierK P, levelForm c0} :
        Set (MvPolynomial (Fin 3) (RationalBase K)))) H =
          ((i : layer (carrierK P) c0 γ (β + γ) j) : MvPolynomial (Fin 3) (RationalBase K) ⧸ _) ∧
      G ∈ H2Count.box (RationalBase K) γ (β + γ) ∧
      G = A * carrierK P + levelForm c0 ^ j * H := by
    intro i
    obtain ⟨H, hH, hHi⟩ := Submodule.mem_map.mp (i : layer (carrierK P) c0 γ (β + γ) j).2
    obtain ⟨G, hG, u, hu, hGu⟩ := Submodule.mem_sup.mp hH
    obtain ⟨A, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    have hGu' : G + A * carrierK P = levelForm c0 ^ j * H := hGu
    exact ⟨H, G, -A, hHi, hG, by rw [← hGu']; ring⟩
  choose H G A hH hG hGA using hrep
  have hli : LinearIndependent (RationalBase K) fun i : s =>
      Ideal.Quotient.mk (Ideal.span ({carrierK P, levelForm c0} :
        Set (MvPolynomial (Fin 3) (RationalBase K)))) (H i) := by
    have h1 := hs.map' (layer (carrierK P) c0 γ (β + γ) j).subtype (Submodule.ker_subtype _)
    have h2 : (fun i : s => Ideal.Quotient.mk (Ideal.span ({carrierK P, levelForm c0} :
        Set (MvPolynomial (Fin 3) (RationalBase K)))) (H i)) =
        (layer (carrierK P) c0 γ (β + γ) j).subtype ∘
          fun i : s => (i : layer (carrierK P) c0 γ (β + γ) j) := funext fun i => hH i
    rw [h2]
    exact h1
  have hemb := sectionEmbedding P c0 h0 s H hli
  have hBI : ∀ i : s, RCN095.PolynomialInFlag ⟨0, β, γ⟩
      (MvPolynomial.map (algebraMap (RationalBase K) Ω) (G i)) := by
    intro i d hd
    have h1 := H2Count.mem_box_iff_support.mp (hG i) d (MvPolynomial.support_map_subset _ _ hd)
    show d 1 ≤ γ ∧ d 0 + d 1 ≤ β + γ ∧ d 0 + d 1 + d 2 ≤ 0 + β + γ
    omega
  have hEq : ∀ i : s, MvPolynomial.map (algebraMap (RationalBase K) Ω) (G i) =
      MvPolynomial.map (algebraMap (RationalBase K) Ω) (A i) * baseCarrier P.F +
        levelΩ c0 ^ j * MvPolynomial.map (algebraMap (RationalBase K) Ω) (H i) := by
    intro i
    rw [hGA i, map_add, map_mul, map_mul, map_pow, map_carrierK, map_levelForm]
  have hfin := finite_flagPole_pos P c0 ⟨0, β, γ⟩ (β * rhi + γ * yhi) (hsum β γ)
  have hDcast : ∀ (a : SectionComponent P c0) (v : RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1)),
      (((flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat : ℕ) : ℤ) =
        flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩ := fun a v =>
    Int.toNat_of_nonneg (RCN204.flagPole_nonneg _ _ _)
  have hcount := hpole (SectionComponent P c0) (fun a => a.2.1)
    (fun a => (section_sep P c0 h0 a).some) (fun a => (hfin a).toFinset)
    (fun a v => (flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat)
    (fun a v hv => Int.toNat_eq_zero.mpr (not_lt.mp fun h => hv ((hfin a).mem_toFinset.mpr h)))
    s (fun i a => RCN002.coordinateEvaluation Ω a.2.1 (MvPolynomial.map (algebraMap (RationalBase K) Ω) (H i))) hemb
    (fun i a v => by
      rw [hDcast]
      exact poleBound P N hN hNp hc c0 h0 ⟨0, β, γ⟩ j _ _ _ (hBI i) (hEq i) a v)
  rw [Fintype.card_coe] at hcount
  have hsumD : (∑ a : SectionComponent P c0, ∑ v ∈ (hfin a).toFinset,
      (flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat) ≤ β * rhi + γ * yhi := by
    have h1 := hsum β γ fun a => (hfin a).toFinset
    have h2 : ((∑ a : SectionComponent P c0, ∑ v ∈ (hfin a).toFinset,
        (flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat : ℕ) : ℤ) =
        ∑ a : SectionComponent P c0, ∑ v ∈ (hfin a).toFinset,
          flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩ := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun v _ => hDcast a v
    rw [← h2] at h1
    exact_mod_cast h1
  calc s.card ≤ ∑ a : SectionComponent P c0, ((∑ v ∈ (hfin a).toFinset,
        (flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat) + 1) := hcount
    _ = (∑ a : SectionComponent P c0, ∑ v ∈ (hfin a).toFinset,
          (flagPole v.val (coordinate Ω a.2.1) ⟨0, β, γ⟩).toNat) +
        Fintype.card (SectionComponent P c0) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    _ ≤ β * rhi + γ * yhi + rhi := Nat.add_le_add hsumD hcard
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Lev
open WithZero MvPolynomial
open RCN002 RCN095 RCN187
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing LevelComponent.isPrime
omit [G.IsPrime] in
theorem val_BR_le_one (v : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (hE : ∀ a : E, v (algebraMap E (RCN002.CoordinateField E G) a) ≤ 1)
    (hv : ∀ i, v (coordinate E G i) ≤ 1) (A : MvPolynomial (Fin 3) E) : v (RCN002.coordinateEvaluation E G A) ≤ 1 := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [algHom_C]
    exact hE a
  | add p q hp hq =>
    rw [map_add]
    exact (v.map_add _ _).trans (max_le hp hq)
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact mul_le_one' hp (hv i)
theorem val_vertex (hc : ∀ j, coordinate E G j ≠ 0) (q : SurfacePoint G) (P : PrimeDivisor q.ring)
    (W : FlagDegree) :
    P.valuation (RCN002.CoordinateField E G)
        (lmono (coordinate E G) (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 W)) =
      exp (RCN204.flagPole (P.valuation (RCN002.CoordinateField E G)) (coordinate E G) W) :=
  flagPole_eq_vertex _ _ hc _ _ _
    (fun i => P.valuation_le_one (RCN002.CoordinateField E G) ⟨_, LevelCount.chartCoord_mem q i⟩) W
theorem val_constant_le_one (q : SurfacePoint G) (P : PrimeDivisor q.ring) (a : E) :
    P.valuation (RCN002.CoordinateField E G) (algebraMap E (RCN002.CoordinateField E G) a) ≤ 1 :=
  P.valuation_le_one (RCN002.CoordinateField E G) (algebraMap E q.ring a)
theorem localFunction_BR_mem (hc : ∀ j, coordinate E G j ≠ 0) (q : SurfacePoint G) (W : FlagDegree)
    (A : MvPolynomial (Fin 3) E) (hA : RCN095.PolynomialInFlag W A) : q.localFunction (RCN002.coordinateEvaluation E G A) W ∈ q.ring := by
  obtain ⟨a, ha⟩ := mem_range_of_valuation_le_one (O := q.ring) (RCN002.CoordinateField E G)
      (q.localFunction (RCN002.coordinateEvaluation E G A) W) fun P => by
    have hB := RCN204.valuation_eval_le_flag (P.valuation (RCN002.CoordinateField E G)) (algebraMap E (RCN002.CoordinateField E G)) (val_constant_le_one q P)
      (coordinate E G) W A hA
    rw [show MvPolynomial.eval₂Hom (algebraMap E (RCN002.CoordinateField E G)) (coordinate E G) A = RCN002.coordinateEvaluation E G A from by
      rw [RCN002.coordinateEvaluation_eq_aeval]
      exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm] at hB
    rw [SurfacePoint.localFunction, map_div₀, val_vertex hc q P W]
    exact (div_le_one₀ exp_pos).mpr hB
  rw [← ha]
  exact a.2
variable {N p : ℕ}
theorem localFunction_cofactor_mem [CharP E p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p)
    (hc : ∀ j, coordinate E G j ≠ 0) (q : SurfacePoint G) (W : FlagDegree)
    (Ga H Zc : MvPolynomial (Fin 3) E) (n : ℕ) (hflag : RCN095.PolynomialInFlag W Ga)
    (hprod : RCN002.coordinateEvaluation E G Ga = RCN002.coordinateEvaluation E G Zc ^ n * RCN002.coordinateEvaluation E G H)
    (hc0 : ∀ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) →
      nu (RCN002.coordinateEvaluation E G Zc) < 1 → ∀ j, nu (coordinate E G j) ≤ 1) :
    q.localFunction (RCN002.coordinateEvaluation E G H) W ∈ q.ring := by
  have hGa := localFunction_BR_mem hc q W Ga hflag
  obtain ⟨a, ha⟩ := mem_range_of_valuation_le_one (O := q.ring) (RCN002.CoordinateField E G)
      (q.localFunction (RCN002.coordinateEvaluation E G H) W) fun P => by
    by_cases h : P.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G Zc) < 1
    · have hcoord := hc0 _ ⟨_, _, _, q.surfaceDivisor hN hp P⟩ h
      rw [SurfacePoint.localFunction, map_div₀, val_vertex hc q P W, RCN204.flagPole,
        poleOrder_eq_zero _ (hcoord 0), poleOrder_eq_zero _ (hcoord 1),
        poleOrder_eq_zero _ (hcoord 2)]
      simp only [max_self, mul_zero, add_zero, exp_zero, div_one]
      exact val_BR_le_one _ (val_constant_le_one q P) hcoord H
    · have h1 := P.valuation_le_one (RCN002.CoordinateField E G) ⟨_, hGa⟩
      rw [show algebraMap q.ring (RCN002.CoordinateField E G) ⟨_, hGa⟩ = q.localFunction (RCN002.coordinateEvaluation E G Ga) W from rfl,
        SurfacePoint.localFunction, hprod, map_div₀, map_mul, map_pow, mul_div_assoc] at h1
      rw [SurfacePoint.localFunction, map_div₀]
      exact (le_mul_of_one_le_left' (one_le_pow_of_one_le' (not_lt.mp h) n)).trans h1
  rw [← ha]
  exact a.2
variable {g Hp : MvPolynomial (Fin 3) E} {f : RCN002.CoordinateField E G} {c : E}
theorem component_h2 {β γ : ℕ} {H : MvPolynomial (Fin 3) E}
    (M : LevelCount.Setup G N p g Hp f c (RCN002.coordinateEvaluation E G H) ⟨0, β, γ⟩) (Ga : MvPolynomial (Fin 3) E)
    (c0 : E) (n : ℕ) (hflag : RCN095.PolynomialInFlag ⟨0, β, γ⟩ Ga)
    (hmem : Ga - (MvPolynomial.X 2 - MvPolynomial.C c0) ^ n * H ∈ G)
    (hGa : ∀ B : LevelComponent G f c, Ga ∉ B.prime) (s : Finset (LevelComponent G f c))
    (T : ∀ B : LevelComponent G f c, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))) :
    ∃ T' : ∀ B : LevelComponent G f c, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
      (n : ℤ) * levelFlagSum s T unitZFlag ≤
        (β : ℤ) * levelFlagSum s T' unitYZFlag + (γ : ℤ) * levelFlagSum s T' unitAllFlag := by
  have := M.algClosed
  have key : ∀ B : LevelComponent G f c, ∃ T' : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
      (n : ℤ) * ∑ v ∈ T B, RCN204.flagPole v.val (coordinate E B.prime) unitZFlag ≤
        (β : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E B.prime) unitYZFlag +
          (γ : ℤ) * ∑ v ∈ T', RCN204.flagPole v.val (coordinate E B.prime) unitAllFlag := by
    intro B
    obtain ⟨sep⟩ := M.sep B
    refine curve_of_pole sep c0 n β γ Ga H hflag (hGa B) (B.isCurve.le hmem) (fun v _ => ?_) (T B)
    have h := LevelCount.order_add_flagPole_nonneg M B v
    rw [LevelCount.resOf_BR B.isCurve H, RCN026.order_p19, RCN204.flagPole] at h
    rw [RCN204.flagPole_unitYZ, RCN204.flagPole_unitAll]
    by_cases h0 : v.val (RCN002.coordinateEvaluation E B.prime H) = 0
    · rw [h0]
      exact zero_le
    · rw [← log_le_iff_le_exp h0]
      simp only [Nat.cast_zero, zero_mul, zero_add] at h
      linarith
  choose T' hT' using key
  refine ⟨T', ?_⟩
  simp only [levelFlagSum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun B _ => ?_
  have h := mul_le_mul_of_nonneg_left (hT' B) (Nat.cast_nonneg (α := ℤ) B.mult)
  linarith
end Surface
section Packet
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE HFree6812
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime Exch.fact_irreducible
theorem carrier_mem (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) : baseCarrier P.F ∈ Exch.component P g :=
  Ideal.mem_span_singleton.mpr (P.stage g).RR
theorem level (P : Packet x t y r) : LevelStatement P := by
  intro N hN hNp hc n β γ haux Q A hQ hA
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  obtain ⟨bad0, hbad0, haux⟩ := haux
  have hB0 : ∀ g : RCN222.GeometricFactor K P.F, {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
      (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
      nu (coordinate Ω (Exch.component P g) 2 - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
      (nu 1 ≠ 1 ∨ ∃ j, 1 < nu (coordinate Ω (Exch.component P g) j))}.Finite := fun g =>
    finite_level_exclusion (hN g) hNp (hc g) 1 one_ne_zero _
  have hinj : Function.Injective (algebraMap (RationalBase K) Ω) :=
    (algebraMap (RationalBase K) Ω).injective
  have : Infinite (RationalBase K) :=
    Infinite.of_injective (algebraMap (Polynomial K) (RationalBase K)) (IsFractionRing.injective _ _)
  obtain ⟨c0, hc0⟩ :=
    (hbad0.union ((Set.finite_iUnion hB0).preimage hinj.injOn)).exists_notMem
  obtain ⟨-, Gk, -, hGne, hflag, Ap, Hc, heq⟩ := haux c0 fun h => hc0 (Or.inl h)
  have hmem : ∀ g : RCN222.GeometricFactor K P.F, surfaceMap (RCN135.polynomialEmbedding K) Gk -
      (MvPolynomial.X 2 - MvPolynomial.C (algebraMap (RationalBase K) Ω c0)) ^ n * Hc ∈
        Exch.component P g := fun g => by
    rw [heq, show H2Sec.levelΩ c0 =
      MvPolynomial.X 2 - MvPolynomial.C (algebraMap (RationalBase K) Ω c0) from rfl,
      add_sub_cancel_right]
    exact Ideal.mul_mem_left _ _ (carrier_mem P g)
  have hprod : ∀ g : RCN222.GeometricFactor K P.F, RCN002.coordinateEvaluation Ω (Exch.component P g) (surfaceMap (RCN135.polynomialEmbedding K) Gk) =
      RCN002.coordinateEvaluation Ω (Exch.component P g)
        (MvPolynomial.X 2 - MvPolynomial.C (algebraMap (RationalBase K) Ω c0)) ^ n *
        RCN002.coordinateEvaluation Ω (Exch.component P g) Hc := fun g => by
    have h := (Sec.BR_eq_zero_iff (G := Exch.component P g) _).mpr (hmem g)
    rwa [map_sub, map_mul, map_pow, sub_eq_zero] at h
  have hHne : ∀ g : RCN222.GeometricFactor K P.F, RCN002.coordinateEvaluation Ω (Exch.component P g) Hc ≠ 0 := fun g h =>
    hGne g (by rw [hprod g, h, mul_zero])
  have hc0g : ∀ (g : RCN222.GeometricFactor K P.F) (nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰),
      (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) →
      nu (RCN002.coordinateEvaluation Ω (Exch.component P g)
        (MvPolynomial.X 2 - MvPolynomial.C (algebraMap (RationalBase K) Ω c0))) < 1 →
      ∀ j, nu (coordinate Ω (Exch.component P g) j) ≤ 1 := by
    intro g nu hnu hlt j
    by_contra hj
    rw [BR_levelForm] at hlt
    exact hc0 (Or.inr (Set.mem_iUnion.mpr ⟨g, nu, hnu, hlt, Or.inr ⟨j, not_le.mp hj⟩⟩))
  have hfin : ∀ (g : RCN222.GeometricFactor K P.F) (z : RCN002.CoordinateField Ω (Exch.component P g)), z ≠ 0 →
      {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu z ≠ 1}.Finite := fun g z hz => Data.finite_level_ne_one (hN g) hNp _ z hz
  refine ⟨{c : Ω | ∃ g, Exch.moving P Q A g = algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c} ∪
    ⋃ g : RCN222.GeometricFactor K P.F, (((⋃ j, {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (coordinate Ω (Exch.component P g) j) ≠ 1}) ∪
      {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (pderiv 1 (P.stage g).G)) ≠ 1}) ∪
      ({c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F)) ≠ 1} ∪
      ({c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) Hc) ≠ 1} ∪
      {c : Ω | ∃ nu : Valuation (RCN002.CoordinateField Ω (Exch.component P g)) ℤᵐ⁰,
        (∃ sR sY sZ, SurfaceDivisor (Exch.component P g) sR sY sZ nu) ∧
        nu (Exch.moving P Q A g - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c) < 1 ∧
        nu (RCN002.coordinateEvaluation Ω (Exch.component P g) (surfaceMap (RCN135.polynomialEmbedding K) Gk)) ≠ 1}))),
    (Data.component_ne P Q A).union (Set.finite_iUnion fun g =>
      ((Set.finite_iUnion fun j => hfin g _ (hc g j)).union
        (hfin g _ (Data.pderiv_ne_zero P g))).union
        ((hfin g _ (LevelCount.baseH_ne_zero P g)).union
          ((hfin g _ (hHne g)).union (hfin g _ (hGne g))))), fun c hcbad => ?_⟩
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and,
    not_not] at hcbad
  obtain ⟨hne, hunit⟩ := hcbad
  have hneeds : ∀ g : RCN222.GeometricFactor K P.F, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
      (Exch.moving P Q A g) c (RCN002.coordinateEvaluation Ω (Exch.component P g) Hc) := fun g =>
    ⟨hne g, fun nu hnu hlt => ⟨fun j => (hunit g).1.1 j nu hnu hlt, (hunit g).1.2 nu hnu hlt,
      (hunit g).2.1 nu hnu hlt, (hunit g).2.2.1 nu hnu hlt⟩⟩
  have M : ∀ g : RCN222.GeometricFactor K P.F, LevelCount.Setup (Exch.component P g) N 2130706433 (P.stage g).G
      (baseH P.F) (Exch.moving P Q A g) c (RCN002.coordinateEvaluation Ω (Exch.component P g) Hc) ⟨0, β, γ⟩ := fun g =>
    { algClosed := inferInstance
      charP := hchar
      noether := hN g
      char := hNp
      coord := hc g
      irreducible := (P.stage g).MW
      span := rfl
      needs := hneeds g
      regular := fun q => localFunction_cofactor_mem (hN g) hNp (hc g) q ⟨0, β, γ⟩ _ Hc _ n hflag
        (hprod g) (hc0g g)
      sep := LevelCount.separable P Q A hQ hA c g (hne g)
      closure := fun B q hq => B.isCurve.finite_integralClosure (hc g) q hq
        (LevelCount.separable P Q A hQ hA c g (hne g) B).some }
  have hGa : ∀ (g : RCN222.GeometricFactor K P.F) (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      surfaceMap (RCN135.polynomialEmbedding K) Gk ∉ B.prime := by
    intro g B hB
    have hle : ∀ i, B.curve.val
        (lmono (coordinate Ω (Exch.component P g)) (chartExp false false false i)) ≤ 1 := by
      intro i
      fin_cases i <;> simp [lmono, chartExp] <;>
        exact LevelSurf.val_le_one B.isCurve (MvPolynomial.X _)
    have hsd := B.isCurve.surfaceDivisor (hc g) B.exists_transcendental false false false hle
    have h1 := (hunit g).2.2.2 B.curve.val ⟨_, _, _, hsd⟩ (by rw [B.curve_val]; exact B.val_lt_one)
    exact absurd ((LevelSurf.val_lt_one_iff B.isCurve _).mpr hB) (by rw [h1]; exact lt_irrefl _)
  intro s T
  choose T' hT' using fun g =>
    component_h2 (M g) (surfaceMap (RCN135.polynomialEmbedding K) Gk) _ n hflag (hmem g) (hGa g) (s g) (T g)
  refine ⟨T', ?_⟩
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun g _ => hT' g
theorem section_bound (P : Packet x t y r) : SectionBoundStatement P := by
  intro n β γ Q A c hH2 scale z u v hsec s T
  obtain ⟨T', hT'⟩ := hH2 s T
  obtain ⟨hz, hu, hv⟩ := hsec s T
  obtain ⟨-, hu', hv'⟩ := hsec s T'
  have hn : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
  have hs : (0 : ℤ) ≤ (scale : ℤ) := Nat.cast_nonneg scale
  have hβ : (0 : ℤ) ≤ (β : ℤ) := Nat.cast_nonneg β
  have hγ : (0 : ℤ) ≤ (γ : ℤ) := Nat.cast_nonneg γ
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.cast_min, le_min_iff]
    push_cast
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hz hn]
    · nlinarith [mul_le_mul_of_nonneg_left hT' hs, mul_le_mul_of_nonneg_left hu' hβ,
        mul_le_mul_of_nonneg_left hv' hγ]
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hu hn]
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hv hn]
end Packet
end
end H2Lev
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open scoped Classical BigOperators
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN187 RCN204 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
variable {K I : Type} [Field K]
variable {x : I → K} {t y r : ℕ}
structure GoodFibre (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) {E : Type} [Field E]
    (f : GenericField K →+* E) (Q A : MvPolynomial (Fin 3) E) (V : LevelCurve P SZ f Q A)
    (ℓ : MvPolynomial (Fin 3) (GenericField E)) (a : GenericField E)
    (pts : Finset (Fin 3 → GenericField E)) : Prop where
  point : ∀ w ∈ pts, V.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom ∧
    MvPolynomial.eval w ℓ = a ∧
    MvPolynomial.eval w (AOT f P.F A * SZ.leading ((RCN135.coefficientEmbedding E).comp (codeMap f))) ≠ 0 ∧
    (∀ V' : LevelCurve P SZ f Q A,
      V'.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom → V' = V) ∧
    ∀ cut : MvPolynomial (Fin 3) (GenericField E), cut ∉ V.1 → RCN084.IsolatedPoint (OO f P.F) (XC f P.F Q A) cut w
  poles : ∀ U' : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1)),
    ∑ μ ∈ U', poleOrder μ.val (RCN002.coordinateEvaluation (GenericField E) V.1 ℓ) ≤ (pts.card : ℤ)
theorem flag_sum_le (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (hI : IsolatedStatement P SZ)
    (hF : FibreBoundStatement P SZ) {W : FlagDegree} {J : Finset (Fin 3)}
    (hWJ : SecChoice.FlagCoords W J) (E : Type) [Field E] [IsAlgClosed E] [CharP E 2130706433]
    (f : GenericField K →+* E) (scale z u v : ℕ) (Q A : MvPolynomial (Fin 3) E)
    (hA2 : (2 : MvPolynomial (Fin 3) E) * A ≠ 0) (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : RCN095.PolynomialInFlag unitYZFlag A) (hagn : AGN f P.F SZ Q A scale z u v)
    (S : Finset (LevelCurve P SZ f Q A)) (hS : ∀ V ∈ S, GoodCurve P SZ f Q A V)
    (U : ∀ V : LevelCurve P SZ f Q A,
      Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1))) :
    (scale : ℤ) * ∑ V ∈ S, ∑ μ ∈ U V, flagPole μ.val (coordinate (GenericField E) V.1) W ≤
      ((W.zOnly * z + W.yz * u + W.all * v : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := SecChoice.exists_notMem_of_top_notMem
    (S.biUnion fun V =>
      ((U V).filter fun μ => 0 < SecChoice.poleMax J μ).image (SecChoice.poleSpace J))
    (fun htop => by
      obtain ⟨V, -, hV⟩ := Finset.mem_biUnion.mp htop
      obtain ⟨μ, hμ, heq⟩ := Finset.mem_image.mp hV
      exact SecChoice.poleSpace_ne_top J μ (Finset.mem_filter.mp hμ).2 heq)
  let ℓ : MvPolynomial (Fin 3) (GenericField E) := Sec.linearForm (SecChoice.mask J b)
  have hℓ : RCN095.PolynomialInFlag unitAllFlag ℓ := by
    have h := Sec.linearForm_sub_C_inFlag unitAllFlag (SecChoice.mask J b) 0
      (fun _ => by simp [unitAllFlag]) (fun _ => by simp [unitAllFlag])
      fun _ => by simp [unitAllFlag]
    rwa [map_zero, sub_zero] at h
  have hpole : ∀ V ∈ S, ∀ μ ∈ U V, ∀ a : GenericField E,
      flagPole μ.val (coordinate (GenericField E) V.1) W ≤
        poleOrder μ.val (RCN002.coordinateEvaluation (GenericField E) V.1 (ℓ - C a)) := by
    intro V hV μ hμ a
    obtain ⟨m, hm, hle⟩ := hWJ.pole fun i => poleOrder μ.val (coordinate (GenericField E) V.1 i)
    exact hle.trans (SecChoice.pole_of_notMem J μ b (fun hT => hb _ (Finset.mem_biUnion.mpr
      ⟨V, hV, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hμ, hT⟩)⟩)) a hm)
  have hfib : ∀ V ∈ S, (∀ a, ℓ - C a ∉ V.1) →
      {a : GenericField E | ¬∃ pts, GoodFibre P SZ f Q A V ℓ a pts}.Finite := by
    intro V hV hnc
    obtain ⟨h, hhV, hh⟩ := hI E f Q A hA2 hQ hA V (hS V hV)
    refine (hF E f Q A hA2 hQ hA V (hS V hV) ℓ h hℓ hnc hhV).subset fun a ha hex => ha ?_
    obtain ⟨pts, hpts, hU⟩ := hex
    exact ⟨pts, fun w hw =>
      ⟨(hpts w hw).1, (hpts w hw).2.1, hh w (hpts w hw).1 (hpts w hw).2.2⟩, hU⟩
  obtain ⟨Snc, hSnc⟩ : ∃ Snc : Finset (LevelCurve P SZ f Q A),
      Snc = S.filter fun V => ∀ a, ℓ - C a ∉ V.1 := ⟨_, rfl⟩
  have hmem : ∀ V, V ∈ Snc ↔ V ∈ S ∧ ∀ a, ℓ - C a ∉ V.1 := fun V => by
    rw [hSnc, Finset.mem_filter]
  have hfin : (⋃ V ∈ (Snc : Set (LevelCurve P SZ f Q A)),
      {a : GenericField E | ¬∃ pts, GoodFibre P SZ f Q A V ℓ a pts}).Finite :=
    Snc.finite_toSet.biUnion fun V hV =>
      hfib V ((hmem V).mp (Finset.mem_coe.mp hV)).1 ((hmem V).mp (Finset.mem_coe.mp hV)).2
  obtain ⟨a, ha⟩ := hfin.infinite_compl.nonempty
  have hex : ∀ V : LevelCurve P SZ f Q A, ∃ pts : Finset (Fin 3 → GenericField E),
      V ∈ Snc → GoodFibre P SZ f Q A V ℓ a pts := by
    intro V
    by_cases hV : V ∈ Snc
    · by_contra hn
      exact ha (Set.mem_biUnion (Finset.mem_coe.mpr hV) fun ⟨pts, hpts⟩ => hn ⟨pts, fun _ => hpts⟩)
    · exact ⟨∅, fun h => absurd h hV⟩
  choose pts hpts using hex
  have hdisj : ∀ V ∈ Snc, ∀ V' ∈ Snc, V ≠ V' → Disjoint (pts V) (pts V') := by
    intro V hV V' hV' hne
    refine Finset.disjoint_left.mpr fun w hw hw' => hne ?_
    exact ((hpts V' hV').point w hw').2.2.2.1 V ((hpts V hV).point w hw).1
  have hbud := hagn W (ℓ - C a) (SecChoice.linearForm_mask_inFlag hWJ b a) (Snc.biUnion pts)
    (fun w hw => by
      obtain ⟨V, hV, hwV⟩ := Finset.mem_biUnion.mp hw
      exact ((hpts V hV).point w hwV).1 (EN (GenericField E) _ _ _ V))
    (fun w hw => by
      obtain ⟨V, hV, hwV⟩ := Finset.mem_biUnion.mp hw
      exact ((hpts V hV).point w hwV).1 (GV (GenericField E) _ _ _ V))
    (fun w hw => by
      obtain ⟨V, hV, hwV⟩ := Finset.mem_biUnion.mp hw
      exact ((hpts V hV).point w hwV).2.2.1)
    (fun w hw => by
      obtain ⟨V, hV, hwV⟩ := Finset.mem_biUnion.mp hw
      show MvPolynomial.eval w (ℓ - C a) = 0
      rw [map_sub, eval_C, ((hpts V hV).point w hwV).2.1, sub_self])
    (fun w hw => by
      obtain ⟨V, hV, hwV⟩ := Finset.mem_biUnion.mp hw
      exact ((hpts V hV).point w hwV).2.2.2.2 _ (((hmem V).mp hV).2 a))
  rw [Finset.card_biUnion hdisj] at hbud
  have hterm : ∀ V ∈ S, ∑ μ ∈ U V, flagPole μ.val (coordinate (GenericField E) V.1) W ≤
      ((if ∀ a, ℓ - C a ∉ V.1 then (pts V).card else 0 : ℕ) : ℤ) := by
    intro V hV
    split_ifs with hnc
    · refine le_trans (Finset.sum_le_sum fun μ hμ => ?_)
        ((hpts V ((hmem V).mpr ⟨hV, hnc⟩)).poles (U V))
      have h := hpole V hV μ hμ 0
      rwa [map_zero, sub_zero] at h
    · rw [Nat.cast_zero]
      obtain ⟨a0, ha0⟩ := not_forall.mp hnc
      have h0 : RCN002.coordinateEvaluation (GenericField E) V.1 (ℓ - C a0) = 0 := by
        have hmem0 : ℓ - C a0 ∈ V.1 := not_not.mp ha0
        rw [← RCN002.coordinateEvaluation_ker (GenericField E) V.1] at hmem0
        exact hmem0
      refine Finset.sum_nonpos fun μ hμ => ?_
      have h := hpole V hV μ hμ a0
      rwa [h0, poleOrder, map_zero, log_zero, max_self] at h
  have hsum : ∑ V ∈ S, ∑ μ ∈ U V, flagPole μ.val (coordinate (GenericField E) V.1) W ≤
      ((∑ V ∈ Snc, (pts V).card : ℕ) : ℤ) := by
    rw [hSnc, Finset.sum_filter, Nat.cast_sum]
    exact Finset.sum_le_sum hterm
  calc (scale : ℤ) * ∑ V ∈ S, ∑ μ ∈ U V, flagPole μ.val (coordinate (GenericField E) V.1) W
      ≤ (scale : ℤ) * ((∑ V ∈ Snc, (pts V).card : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hsum (Int.natCast_nonneg scale)
    _ ≤ ((W.zOnly * z + W.yz * u + W.all * v : ℕ) : ℤ) := by exact_mod_cast hbud
theorem unit_bound_of_parts (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (hI : IsolatedStatement P SZ)
    (hF : FibreBoundStatement P SZ) : UnitBoundStatement P SZ := by
  intro E _ _ _ f scale z u v Q A hA2 hQ hA hagn S hS U
  have h1 := flag_sum_le P SZ hI hF SecChoice.flagCoords_yz E f scale z u v Q A hA2 hQ hA hagn S hS U
  have h2 := flag_sum_le P SZ hI hF SecChoice.flagCoords_all E f scale z u v Q A hA2 hQ hA hagn S hS U
  simp only [unitYZFlag, zero_mul, one_mul, zero_add, add_zero] at h1
  simp only [unitAllFlag, zero_mul, one_mul, zero_add] at h2
  exact ⟨h1, h2⟩
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7 FA
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Affine
variable {k : Type} [Field k]
theorem totalDegree_aeval_le {σ τ : Type*} (g : σ → MvPolynomial τ k)
    (hg : ∀ j, (g j).totalDegree ≤ 1) (q : MvPolynomial σ k) :
    (MvPolynomial.aeval g q).totalDegree ≤ q.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun d hd => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun j _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg j))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hd
theorem totalDegree_le_of_flag {p : FlagDegree} {F : MvPolynomial (Fin 3) k} (hF : RCN095.PolynomialInFlag p F) :
    F.totalDegree ≤ p.zOnly + p.yz + p.all := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun d hd => ?_
  rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_three]
  exact (hF d hd).2.2
theorem eq_zero_or_single (d : Fin 3 →₀ ℕ) (h : d 0 + d 1 + d 2 ≤ 1) :
    d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  by_cases h0 : d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0
  · left
    ext j
    fin_cases j <;> simp [h0.1, h0.2.1, h0.2.2]
  · right
    have h1 : d 0 = 1 ∨ d 1 = 1 ∨ d 2 = 1 := by omega
    rcases h1 with h1 | h1 | h1
    · refine ⟨0, Finsupp.ext fun j => ?_⟩
      fin_cases j <;> simp <;> omega
    · refine ⟨1, Finsupp.ext fun j => ?_⟩
      fin_cases j <;> simp <;> omega
    · refine ⟨2, Finsupp.ext fun j => ?_⟩
      fin_cases j <;> simp <;> omega
theorem eq_affine_of_flag (ℓ : MvPolynomial (Fin 3) k) (h : RCN095.PolynomialInFlag unitAllFlag ℓ) :
    ℓ = MvPolynomial.C (ℓ.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C (ℓ.coeff (Finsupp.single j 1)) * MvPolynomial.X j := by
  classical
  ext d
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum]
  simp only [coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one, mul_zero]
  by_cases hd0 : d = 0
  · subst hd0
    simp
  by_cases hds : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hds
    rw [ite_eq_right (Ne.symm hd0), zero_add, Finset.sum_eq_single i
      (fun j _ hji => ite_eq_right fun hj => hji (Finsupp.single_left_injective one_ne_zero hj))
      (fun hi => absurd (Finset.mem_univ i) hi), ite_eq_left rfl]
  · have hns : d ∉ ℓ.support := fun hd =>
      (eq_zero_or_single d (h d hd).2.2).elim hd0 hds
    rw [MvPolynomial.notMem_support_iff.mp hns, ite_eq_right (Ne.symm hd0), zero_add]
    exact (Finset.sum_eq_zero fun j _ => ite_eq_right fun hj => hds ⟨j, hj.symm⟩).symm
def substVar (i : Fin 3) (u : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.aeval (Function.update MvPolynomial.X i u)
theorem substVar_X_self (i : Fin 3) (u : MvPolynomial (Fin 3) k) :
    substVar i u (MvPolynomial.X i) = u := by
  rw [substVar, MvPolynomial.aeval_X, Function.update_self]
theorem substVar_C (i : Fin 3) (u : MvPolynomial (Fin 3) k) (c : k) :
    substVar i u (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [substVar, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
theorem substVar_comp (i : Fin 3) (u v : MvPolynomial (Fin 3) k) :
    (substVar i u).comp (substVar i v) = substVar i (substVar i u v) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  by_cases hj : j = i
  · rw [hj, AlgHom.comp_apply, substVar_X_self, substVar_X_self]
  · rw [AlgHom.comp_apply]
    simp only [substVar, MvPolynomial.aeval_X, Function.update_of_ne hj]
theorem substVar_X_id (i : Fin 3) :
    substVar i (MvPolynomial.X i : MvPolynomial (Fin 3) k) = AlgHom.id k _ := by
  rw [substVar, Function.update_eq_self, MvPolynomial.aeval_X_left]
theorem substVar_affine (i : Fin 3) (c : k) (a : Fin 3 → k) (v : MvPolynomial (Fin 3) k) :
    substVar i v (MvPolynomial.C c + ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) =
      (MvPolynomial.C c + ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) -
        MvPolynomial.C (a i) * MvPolynomial.X i + MvPolynomial.C (a i) * v := by
  have hX : ∀ j, substVar i v (MvPolynomial.X j) =
      MvPolynomial.X j + if j = i then v - MvPolynomial.X i else 0 := fun j => by
    by_cases hj : j = i
    · rw [ite_eq_left hj, hj, substVar_X_self]
      ring
    · rw [ite_eq_right hj, add_zero, substVar, MvPolynomial.aeval_X, Function.update_of_ne hj]
  simp only [map_add, map_sum, map_mul, substVar_C, hX, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring
theorem exists_affine_equiv (i : Fin 3) (c : k) (a : Fin 3 → k) (ha : a i ≠ 0) :
    ∃ σ : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k,
      σ (MvPolynomial.X i) = MvPolynomial.C c + ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j ∧
        ∀ q : MvPolynomial (Fin 3) k, (σ.symm q).totalDegree ≤ q.totalDegree := by
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : MvPolynomial (Fin 3) k,
      ℓ₀ = MvPolynomial.C c + ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : MvPolynomial (Fin 3) k,
      w = MvPolynomial.X i + MvPolynomial.C (a i)⁻¹ * (MvPolynomial.X i - ℓ₀) := ⟨_, rfl⟩
  have hsub : ∀ v, substVar i v ℓ₀ =
      ℓ₀ - MvPolynomial.C (a i) * MvPolynomial.X i + MvPolynomial.C (a i) * v := fun v => by
    rw [hℓ₀]
    exact substVar_affine i c a v
  have hinv : (MvPolynomial.C (a i)⁻¹ : MvPolynomial (Fin 3) k) * MvPolynomial.C (a i) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, MvPolynomial.C_1]
  have h1 : substVar i ℓ₀ w = MvPolynomial.X i := by
    rw [hw, map_add, map_mul, map_sub, substVar_X_self, substVar_C, hsub]
    linear_combination (MvPolynomial.X i - ℓ₀) * hinv
  have h2 : substVar i w ℓ₀ = MvPolynomial.X i := by
    rw [hsub, hw]
    linear_combination (MvPolynomial.X i - ℓ₀) * hinv
  have hℓdeg : ℓ₀.totalDegree ≤ 1 := by
    rw [hℓ₀]
    refine (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1) ?_)
    refine MvPolynomial.totalDegree_finsetSum_le fun j _ =>
      (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]
  have hwdeg : w.totalDegree ≤ 1 := by
    rw [hw]
    refine (MvPolynomial.totalDegree_add _ _).trans
      (max_le (MvPolynomial.totalDegree_X i).le ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (MvPolynomial.totalDegree_X i).le hℓdeg)
  refine ⟨AlgEquiv.ofAlgHom (substVar i ℓ₀) (substVar i w)
    (by rw [substVar_comp, h1, substVar_X_id]) (by rw [substVar_comp, h2, substVar_X_id]),
    ?_, fun q => ?_⟩
  · show substVar i ℓ₀ (MvPolynomial.X i) = _
    rw [substVar_X_self, hℓ₀]
  · show (substVar i w q).totalDegree ≤ _
    refine totalDegree_aeval_le _ (fun j => ?_) q
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact hwdeg
    · rw [Function.update_of_ne hj]
      exact (MvPolynomial.totalDegree_X j).le
end Affine
section Transport
variable {k : Type} [Field k] (D : Ideal (MvPolynomial (Fin 3) k))
  (σ : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
local notation "σD" => Ideal.comap (σ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) D
def fieldEquiv : RCN002.CoordinateField k σD ≃+* RCN002.CoordinateField k D :=
  IsFractionRing.ringEquivOfRingEquiv
    (Ideal.quotientEquivAlg σD D σ
      (Ideal.map_comap_of_surjective (σ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)
        σ.surjective D).symm).toRingEquiv
theorem fieldEquiv_BR (q : MvPolynomial (Fin 3) k) :
    fieldEquiv D σ (RCN002.coordinateEvaluation k σD q) = RCN002.coordinateEvaluation k D (σ q) := by
  show fieldEquiv D σ (algebraMap (RCN002.CoordinateRing k σD) (RCN002.CoordinateField k σD) (Ideal.Quotient.mk σD q)) = _
  rw [fieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl
theorem fieldEquiv_algebraMap (c : k) :
    fieldEquiv D σ (algebraMap k (RCN002.CoordinateField k σD) c) = algebraMap k (RCN002.CoordinateField k D) c := by
  rw [← (RCN002.coordinateEvaluation k σD).commutes c, fieldEquiv_BR, σ.commutes, (RCN002.coordinateEvaluation k D).commutes]
theorem transcendental_coordinate_comap (i : Fin 3)
    (h : Transcendental k (RCN002.coordinateEvaluation k D (σ (MvPolynomial.X i)))) :
    Transcendental k (coordinate k σD i) := fun halg =>
  h (fieldEquiv_BR D σ (MvPolynomial.X i) ▸
    halg.algHom (AlgEquiv.ofRingEquiv (f := fieldEquiv D σ) (fieldEquiv_algebraMap D σ)).toAlgHom)
variable [D.IsPrime] [Algebra (RatFunc k) (RCN002.CoordinateField k D)] [IsScalarTower k (RatFunc k) (RCN002.CoordinateField k D)]
theorem fieldEquiv_algebraMap_ratFunc (i : Fin 3)
    (hX : algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D (σ (MvPolynomial.X i)))
    (hi : Transcendental k (coordinate k σD i)) (z : RatFunc k) :
    fieldEquiv D σ (RCN005.rationalBaseEmbedding k σD i hi z) = algebraMap (RatFunc k) (RCN002.CoordinateField k D) z := by
  have h : ((fieldEquiv D σ : RCN002.CoordinateField k σD →+* RCN002.CoordinateField k D).comp (RCN005.rationalBaseEmbedding k σD i hi).toRingHom) =
      algebraMap (RatFunc k) (RCN002.CoordinateField k D) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
      (Polynomial.ringHom_ext (fun c => ?_) ?_)
    · show fieldEquiv D σ (RCN005.rationalBaseEmbedding k σD i hi
          (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c))) =
        algebraMap (RatFunc k) (RCN002.CoordinateField k D) (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c))
      rw [RCN005.rationalBaseEmbedding_polynomial, Polynomial.aeval_C, fieldEquiv_algebraMap, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
    · show fieldEquiv D σ (RCN005.rationalBaseEmbedding k σD i hi
          (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)) =
        algebraMap (RatFunc k) (RCN002.CoordinateField k D) (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)
      rw [RCN005.rationalBaseEmbedding_polynomial, Polynomial.aeval_X, RatFunc.algebraMap_X, hX]
      exact fieldEquiv_BR D σ (MvPolynomial.X i)
  exact RingHom.congr_fun h z
theorem finite_separable_of_comap (i : Fin 3)
    (hX : algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D (σ (MvPolynomial.X i)))
    (hi : Transcendental k (coordinate k σD i))
    (h : letI : Algebra (RatFunc k) (RCN002.CoordinateField k σD) := RCN005.rationalBaseAlgebra k σD i hi
      FiniteDimensional (RatFunc k) (RCN002.CoordinateField k σD) ∧ Algebra.IsSeparable (RatFunc k) (RCN002.CoordinateField k σD)) :
    FiniteDimensional (RatFunc k) (RCN002.CoordinateField k D) ∧ Algebra.IsSeparable (RatFunc k) (RCN002.CoordinateField k D) := by
  let _ : Algebra (RatFunc k) (RCN002.CoordinateField k σD) := RCN005.rationalBaseAlgebra k σD i hi
  obtain ⟨hfd, hsep⟩ := h
  let ψ : RCN002.CoordinateField k σD ≃ₐ[RatFunc k] RCN002.CoordinateField k D :=
    AlgEquiv.ofRingEquiv (f := fieldEquiv D σ) (fieldEquiv_algebraMap_ratFunc D σ i hX hi)
  exact ⟨ψ.toLinearEquiv.finiteDimensional, AlgEquiv.Algebra.isSeparable ψ⟩
theorem transcendental_of_algebraMap_X (ℓ : MvPolynomial (Fin 3) k)
    (hX : algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D ℓ) : Transcendental k (RCN002.coordinateEvaluation k D ℓ) := by
  rw [← hX, transcendental_algebraMap_iff (algebraMap (RatFunc k) (RCN002.CoordinateField k D)).injective,
    ← RatFunc.algebraMap_X,
    transcendental_algebraMap_iff (IsFractionRing.injective (Polynomial k) (RatFunc k))]
  exact Polynomial.transcendental_X k
end Transport
section Degree
variable {k : Type} [Field k]
theorem finite_separable_of_degree {p : ℕ} [CharP k p] (D : Ideal (MvPolynomial (Fin 3) k))
    [D.IsPrime] (ℓ : MvPolynomial (Fin 3) k) (hℓ : RCN095.PolynomialInFlag unitAllFlag ℓ)
    [Algebra (RatFunc k) (RCN002.CoordinateField k D)] [IsScalarTower k (RatFunc k) (RCN002.CoordinateField k D)]
    (hX : algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D ℓ)
    (g T : MvPolynomial (Fin 3) k) (hg : Irreducible g) (hgD : g ∈ D) (hTD : T ∈ D) (hgT : ¬g ∣ T)
    (m n : ℕ) (hgm : g.totalDegree ≤ m) (hTn : T.totalDegree ≤ n) (hm : m < p)
    (hmn : 2 * m * n < p) :
    FiniteDimensional (RatFunc k) (RCN002.CoordinateField k D) ∧ Algebra.IsSeparable (RatFunc k) (RCN002.CoordinateField k D) := by
  have hXt : Transcendental k (RCN002.coordinateEvaluation k D ℓ) := transcendental_of_algebraMap_X D ℓ hX
  have haff := eq_affine_of_flag ℓ hℓ
  obtain ⟨i, hi⟩ : ∃ i, ℓ.coeff (Finsupp.single i 1) ≠ 0 := by
    by_contra hall
    have hall' : ∀ i, ℓ.coeff (Finsupp.single i 1) = 0 := fun i =>
      by_contra fun hne => hall ⟨i, hne⟩
    refine hXt ?_
    rw [haff]
    simp only [hall', map_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact isAlgebraic_algebraMap _
  obtain ⟨σ, hσ, hdeg⟩ :=
    exists_affine_equiv i (ℓ.coeff 0) (fun j => ℓ.coeff (Finsupp.single j 1)) hi
  have hσ' : σ (MvPolynomial.X i) = ℓ := by
    rw [haff]
    exact hσ
  have hi' : Transcendental k (coordinate k
      (Ideal.comap (σ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) D) i) :=
    transcendental_coordinate_comap D σ i (by rw [hσ']; exact hXt)
  refine finite_separable_of_comap D σ i (by rw [hσ']; exact hX) hi' ?_
  have hdegG : ∀ j : Fin 3, (σ.symm g).degreeOf j ≤ m := fun j =>
    (MvPolynomial.degreeOf_le_totalDegree _ j).trans ((hdeg g).trans hgm)
  have hdegT : ∀ j : Fin 3, (σ.symm T).degreeOf j ≤ n := fun j =>
    (MvPolynomial.degreeOf_le_totalDegree _ j).trans ((hdeg T).trans hTn)
  have hprod : ∀ u v : Fin 3, (σ.symm T).degreeOf u * (σ.symm g).degreeOf v +
      (σ.symm g).degreeOf u * (σ.symm T).degreeOf v ≤ 2 * m * n := fun u v =>
    calc (σ.symm T).degreeOf u * (σ.symm g).degreeOf v +
          (σ.symm g).degreeOf u * (σ.symm T).degreeOf v
        ≤ n * m + m * n :=
          Nat.add_le_add (Nat.mul_le_mul (hdegT u) (hdegG v)) (Nat.mul_le_mul (hdegG u) (hdegT v))
      _ = 2 * m * n := by ring
  have hmixed : RCN001.coordinateMixedDegree k (σ.symm g) (σ.symm T) i < p := by
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [RCN001.coordinateMixedDegree_zero]
      exact (hprod 1 2).trans_lt hmn
    · rw [RCN001.coordinateMixedDegree_one]
      exact (hprod 0 2).trans_lt hmn
    · rw [RCN001.coordinateMixedDegree_two]
      exact (hprod 0 1).trans_lt hmn
  have hgD' : σ.symm g ∈ Ideal.comap (σ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) D := by
    show σ (σ.symm g) ∈ D
    rw [AlgEquiv.apply_symm_apply]
    exact hgD
  have hTD' : σ.symm T ∈ Ideal.comap (σ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) D := by
    show σ (σ.symm T) ∈ D
    rw [AlgEquiv.apply_symm_apply]
    exact hTD
  exact RCN003.RH k _ i hi' p (σ.symm g) (σ.symm T) ((MulEquiv.irreducible_iff σ.symm).mpr hg)
    hgD' hTD' (fun h => hgT ((map_dvd_iff σ.symm).mp h)) (fun j => (hdegG j).trans_lt hm) hmixed
end Degree
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem separable_form (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : SeparableFormStatement P SZ := by
  intro E _ _ _ f Q A _ hQ hA V hV ℓ hℓ _ _ hX
  have hchar : CharP (GenericField E) 2130706433 := RCN135.genericField_charP E 2130706433
  obtain ⟨-, -, g, hg, hgF, hgV, hgT⟩ := hV
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  have hthi := packet_t_le P
  have hF0 : OO f P.F ≠ 0 :=
    RCN136.surfaceMap_ne_zero ((RCN135.coefficientEmbedding E).comp (codeMap f)) ((RCN135.coefficientEmbedding E).injective.comp (DTI f)) P.F P.irreducible.ne_zero
  have hFdeg : (OO f P.F).totalDegree ≤ t :=
    (totalDegree_le_of_flag (P.parent_flag (GenericField E) ((RCN135.coefficientEmbedding E).comp (codeMap f)))).trans
      (by show t - y + (y - r) + r ≤ t; omega)
  obtain ⟨hHf, hGf⟩ := RCN201.DGW ((RCN135.coefficientEmbedding E).comp (codeMap f)) (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) P.F
    P.support.IZ.2.1 P.support.ys_weight P.support.total_weight
  have hTdeg : (XC f P.F Q A).totalDegree ≤ t + 1 :=
    (totalDegree_le_of_flag (LevelCount.levelCut_flag hHf hGf (RCN207.inFlag_map (RCN135.coefficientEmbedding E) hQ)
      (RCN207.inFlag_map (RCN135.coefficientEmbedding E) hA) (RCN135.initialCoordinate E))).trans (by
        simp only [LocatorHybridCells.cellA, LocatorHybridCells.cellB, LocatorHybridCells.cellS]
        omega)
  have hmix : 2 * t * (t + 1) < 2130706433 :=
    calc 2 * t * (t + 1) ≤ 2 * 9352 * (9352 + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hthi) (Nat.add_le_add_right hthi 1)
      _ < 2130706433 := by norm_num
  exact finite_separable_of_degree (p := 2130706433) V.1 ℓ hℓ hX g (XC f P.F Q A) hg hgV
    (GV (GenericField E) _ _ _ V) hgT t (t + 1)
    ((MvPolynomial.totalDegree_le_of_dvd_of_isDomain hgF hF0).trans hFdeg) hTdeg
    (lt_of_le_of_lt hthi (by norm_num)) hmix
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open RCN072 RCN084 RCN264
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
namespace Isolated
section Curve
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G M R : MvPolynomial (Fin 3) Ω}
theorem exists_polynomial (V : RCN264.RegularComponent Ω G M R) (hV : V.1.height = 2) :
    ∃ h : MvPolynomial (Fin 3) Ω, h ∉ V.1 ∧
      ∀ w : Fin 3 → Ω, V.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom →
        MvPolynomial.eval w h ≠ 0 →
        MvPolynomial.eval w R ≠ 0 ∧
        (∀ V' : RCN264.RegularComponent Ω G M R, V'.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom → V' = V) ∧
        ∀ cut : MvPolynomial (Fin 3) Ω, cut ∉ V.1 → RCN084.IsolatedPoint G M cut w := by
  classical
  have hmin : V.1 ∈ (cutIdeal Ω G M).minimalPrimes := (RCN072.mem_componentFamily Ω G M V.1).mp (AAS Ω G M R V)
  have key : ∀ V' : RCN264.RegularComponent Ω G M R, ∃ a : MvPolynomial (Fin 3) Ω, a ∉ V.1 ∧ (V' ≠ V → a ∈ V'.1) := by
    intro V'
    by_cases hV' : V' = V
    · exact ⟨1, V.1.one_notMem, fun h => absurd hV' h⟩
    · have hnle : ¬V'.1 ≤ V.1 := fun hle => hV' (Subtype.ext (le_antisymm hle
        (hmin.2 ⟨inferInstance, RCN072.cutIdeal_le_component Ω G M V'.1 (AAS Ω G M R V')⟩ hle)))
      obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨a, ha, fun _ => ha'⟩
  choose a ha ha' using key
  refine ⟨R * ∏ V' : RCN264.RegularComponent Ω G M R, a V', fun hmem => ?_, fun w hw hh => ?_⟩
  · rcases (inferInstance : V.1.IsPrime).mem_or_mem hmem with h | h
    · exact _Q6 Ω G M R V h
    · obtain ⟨V', -, hV'⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact ha V' hV'
  · rw [map_mul, map_prod] at hh
    obtain ⟨hR, hprod⟩ := mul_ne_zero_iff.mp hh
    have hone : ∀ V' : RCN264.RegularComponent Ω G M R,
        V'.1 ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom → V' = V := by
      intro V' hV'w
      by_contra hne
      exact Finset.prod_ne_zero_iff.mp hprod V' (Finset.mem_univ _) (hV'w (ha' V' hne))
    refine ⟨hR, hone, fun cut hcut D hD hpt hDw hGD hMD hcutD => ?_⟩
    have hle : cutIdeal Ω G M ≤ D := Ideal.span_le.mpr fun b hb => by
      rcases hb with rfl | rfl
      exacts [hGD, hMD]
    obtain ⟨D', hD', hD'D⟩ := Ideal.exists_minimalPrimes_le hle
    have hVV : (⟨D', (AJF Ω).mpr ⟨(RCN072.mem_componentFamily Ω G M D').mpr hD', fun h => hR (hDw (hD'D h))⟩⟩ :
        RCN264.RegularComponent Ω G M R) = V := hone _ (hD'D.trans hDw)
    have hVD : V.1 ≤ D := hVV ▸ hD'D
    rcases eq_or_lt_of_le hVD with heq | hlt
    · exact hcut (heq ▸ hcutD)
    · have h1 := Ideal.height_strict_mono_of_isPrime hlt
      rw [hV] at h1
      exact absurd (h1.trans_le (CurveH2.height_le_two_of_ne_point D hpt)) (lt_irrefl _)
end Curve
end Isolated
section Packet
open BD DU
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K]
variable {x : I → K} {t y r : ℕ}
theorem isolated (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : IsolatedStatement P SZ :=
  fun _ _ _ _ _ _ _ _ _ _ V hV => Isolated.exists_polynomial V hV.2.1
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open scoped Classical BigOperators
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN187 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Curve
variable {k : Type} [Field k] [IsAlgClosed k]
theorem transcendental_of_not_const (D : Ideal (MvPolynomial (Fin 3) k)) [D.IsPrime]
    (ℓ : MvPolynomial (Fin 3) k) (hnc : ∀ a : k, ℓ - C a ∉ D) : Transcendental k (RCN002.coordinateEvaluation k D ℓ) := by
  intro halg
  obtain ⟨a, ha⟩ : ∃ a : k, algebraMap k (RCN002.CoordinateField k D) a = RCN002.coordinateEvaluation k D ℓ :=
    minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))
  refine hnc a ?_
  rw [← RCN002.coordinateEvaluation_ker k D]
  show RCN002.coordinateEvaluation k D (ℓ - C a) = 0
  rw [map_sub, algHom_C, ha, sub_self]
theorem fibre_of_separable (D : Ideal (MvPolynomial (Fin 3) k)) [D.IsPrime]
    (ℓ g : MvPolynomial (Fin 3) k) (hnc : ∀ a : k, ℓ - C a ∉ D) (hg : g ∉ D)
    (hsep : ∀ [Algebra (RatFunc k) (RCN002.CoordinateField k D)] [IsScalarTower k (RatFunc k) (RCN002.CoordinateField k D)],
      algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D ℓ →
        FiniteDimensional (RatFunc k) (RCN002.CoordinateField k D) ∧ Algebra.IsSeparable (RatFunc k) (RCN002.CoordinateField k D)) :
    {a : k | ¬∃ pts : Finset (Fin 3 → k),
      (∀ w ∈ pts, D ≤ RingHom.ker (MvPolynomial.aeval w).toRingHom ∧ MvPolynomial.eval w ℓ = a ∧
        MvPolynomial.eval w g ≠ 0) ∧
      ∀ U : Finset (RCN026.Place_p19 k (RCN002.CoordinateField k D)),
        ∑ v ∈ U, poleOrder v.val (RCN002.coordinateEvaluation k D ℓ) ≤ (pts.card : ℤ)}.Finite := by
  have htr := transcendental_of_not_const D ℓ hnc
  let φ : RatFunc k →ₐ[k] RCN002.CoordinateField k D := RatFunc.liftAlgHom (Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ)).toRingHom
      (transcendental_iff_injective.mp htr))
  have hφ : ∀ p : Polynomial k,
      φ (algebraMap (Polynomial k) (RatFunc k) p) = Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ) p := fun p =>
    RatFunc.liftRingHom_algebraMap _ _ p
  let _a1 : Algebra (Polynomial k) (RCN002.CoordinateField k D) := (Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ)).toRingHom.toAlgebra
  let _a2 : Algebra (RatFunc k) (RCN002.CoordinateField k D) := φ.toRingHom.toAlgebra
  have _t1 : IsScalarTower k (Polynomial k) (RCN002.CoordinateField k D) :=
    IsScalarTower.of_algebraMap_eq fun c => ((Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ)).commutes c).symm
  have _t2 : IsScalarTower k (RatFunc k) (RCN002.CoordinateField k D) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have _t3 : IsScalarTower (Polynomial k) (RatFunc k) (RCN002.CoordinateField k D) :=
    IsScalarTower.of_algebraMap_eq fun p => (hφ p).symm
  have hX : algebraMap (RatFunc k) (RCN002.CoordinateField k D) RatFunc.X = RCN002.coordinateEvaluation k D ℓ := by
    rw [← RatFunc.algebraMap_X]
    exact (hφ Polynomial.X).trans (Polynomial.aeval_X _)
  obtain ⟨_t4, _t5⟩ := hsep hX
  have hegm : ∀ U : Finset (RCN026.Place_p19 k (RCN002.CoordinateField k D)),
      ∑ v ∈ U, poleOrder v.val (RCN002.coordinateEvaluation k D ℓ) ≤ (Module.finrank (RatFunc k) (RCN002.CoordinateField k D) : ℤ) := by
    intro U
    have h := RCN346.EGM k (RCN002.CoordinateField k D) U
    have hpar : RCN345.parameter_p19 k (RCN002.CoordinateField k D) = RCN002.coordinateEvaluation k D ℓ := by
      show Polynomial.aeval (RCN002.coordinateEvaluation k D ℓ) Polynomial.X = RCN002.coordinateEvaluation k D ℓ
      exact Polynomial.aeval_X _
    rw [hpar] at h
    exact h
  refine (finite_setOf_not_exists_zeros_off k D ℓ hX g hg).subset fun a ha hS => ha ?_
  obtain ⟨S, hcard, hS⟩ := hS
  refine ⟨S, fun w hw => ⟨fun r hr => (hS w hw).1 r hr, (hS w hw).2.1, (hS w hw).2.2⟩, fun U => ?_⟩
  rw [hcard]
  exact hegm U
end Curve
section Packet
variable {K I : Type} [Field K]
variable {x : I → K} {t y r : ℕ}
theorem fibre_bound_of_separable (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F)
    (hsep : SeparableFormStatement P SZ) : FibreBoundStatement P SZ := by
  intro E _ _ _ f Q A hA2 hQ hA V hV ℓ g hℓ hnc hg
  exact fibre_of_separable V.1 ℓ g hnc hg fun hX => hsep E f Q A hA2 hQ hA V hV ℓ hℓ hX
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
namespace CurveH2
section Curve
variable {k : Type} [Field k] [IsAlgClosed k] {D : Ideal (MvPolynomial (Fin 3) k)} [D.IsPrime]
theorem finite_pole_values (sep : RCN341.SeparableLiteralCoordinate D) :
    {c : k | ∃ v : RCN026.Place_p19 k (RCN002.CoordinateField k D), (∃ j, 1 < v.val (coordinate k D j)) ∧
      v.val (coordinate k D 2 - algebraMap k (RCN002.CoordinateField k D) c) < 1}.Finite := by
  have hpole : ∀ j : Fin 3,
      {v : RCN026.Place_p19 k (RCN002.CoordinateField k D) | 1 < v.val (coordinate k D j)}.Finite := by
    intro j
    by_cases hx : coordinate k D j = 0
    · refine Set.finite_empty.subset fun v (hv : 1 < v.val (coordinate k D j)) => ?_
      rw [hx, map_zero] at hv
      exact absurd hv (not_lt.mpr zero_le_one)
    · refine (Curve.finite_order_ne_zero D sep _ hx).subset
        fun v (hv : 1 < v.val (coordinate k D j)) => ?_
      have h0 : v.val (coordinate k D j) ≠ 0 := ne_of_gt (zero_lt_one.trans hv)
      have hlog : 0 < (v.val (coordinate k D j)).log :=
        (lt_log_iff_exp_lt h0).mpr (by rwa [exp_zero])
      change -(v.val (coordinate k D j)).log ≠ 0
      omega
  have hS : {v : RCN026.Place_p19 k (RCN002.CoordinateField k D) | ∃ j, 1 < v.val (coordinate k D j)}.Finite :=
    (Set.finite_iUnion hpole).subset fun v ⟨j, hj⟩ => Set.mem_iUnion.mpr ⟨j, hj⟩
  refine (finite_level_values ((fun v : RCN026.Place_p19 k (RCN002.CoordinateField k D) => v.val) '' _) (hS.image _)
    (fun ν hν => ?_) (coordinate k D 2)).subset fun c ⟨v, hv, hc⟩ => ⟨v.val, ⟨v, hv, rfl⟩, hc⟩
  obtain ⟨v, -, rfl⟩ := hν
  exact v.property.2.eq_one
end Curve
end CurveH2
section Packet
open scoped Classical
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem curve_h2 (P : Packet x t y r) : CurveH2Statement P := by
  intro n β γ haux E _ _ f Q A D _ sep hOO hXC hH hpt T
  obtain ⟨bad, hbad, haux⟩ := haux
  let ι : GenericField K →+* GenericField E := (RCN135.coefficientEmbedding E).comp f
  let g : RationalBase K →+* GenericField E :=
    ι.comp (algebraMap (RationalBase K) (GenericField K))
  have hinf : Infinite (RationalBase K) := Infinite.of_injective _
    (IsFractionRing.injective (Polynomial K) (RationalBase K))
  obtain ⟨c0, hc0⟩ := (hbad.union ((CurveH2.finite_pole_values sep).preimage
    (Set.injOn_of_injective g.injective))).exists_notMem
  obtain ⟨-, G, hdiv, -, hflag, A0, H0, hid⟩ := haux c0 fun h => hc0 (Or.inl h)
  have hGa : surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) G =
      MvPolynomial.map ι (surfaceMap (RCN135.polynomialEmbedding K) G) := CurveH2.surfaceMap_comp ι (RCN135.polynomialEmbedding K) G
  refine H2Lev.curve (GenericField E) D sep (g c0) n β γ
    (surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) G) (MvPolynomial.map ι H0) ?_ ?_ ?_ ?_ T
  · rw [hGa]
    exact RCN207.inFlag_map ι hflag
  · exact CurveH2.aux_notMem f P.irreducible hdiv Q A D hpt hOO hXC hH
  · have hF : MvPolynomial.map ι (AFA.baseCarrier P.F) = OO f P.F :=
      (CurveH2.surfaceMap_comp ι (RCN135.polynomialEmbedding K) P.F).symm
    have hL : MvPolynomial.map ι (H2Sec.levelΩ c0) =
        MvPolynomial.X 2 - MvPolynomial.C (g c0) := by
      simp only [H2Sec.levelForm, map_sub, MvPolynomial.map_X, MvPolynomial.map_C]
      rfl
    have h1 : surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) G -
        (MvPolynomial.X 2 - MvPolynomial.C (g c0)) ^ n * MvPolynomial.map ι H0 =
        MvPolynomial.map ι A0 * OO f P.F := by
      rw [hGa, hid, map_add, map_mul, map_mul, map_pow, hF, hL]
      ring
    rw [h1]
    exact D.mul_mem_left _ hOO
  · intro v hv j
    by_contra hj
    rw [H2Lev.BR_levelForm] at hv
    exact hc0 (Or.inr ⟨v, ⟨j, not_le.mp hj⟩, hv⟩)
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open MvPolynomial RCN002 RCN095 RCN072 RCN264 RCN084
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
namespace Counted
section Curve
variable {Ω : Type} [Field Ω] {G M R A : MvPolynomial (Fin 3) Ω} {v : Fin 3 → Ω}
theorem not_mem_of_isolated (V : RCN264.RegularComponent Ω G M R) (hV : V.1 ≤ RingHom.ker (aeval v).toRingHom)
    (hi : RCN084.IsolatedPoint G M A v) : A ∉ V.1 :=
  hi V.1 inferInstance (PU Ω G M R V) hV (EN Ω G M R V) (GV Ω G M R V)
theorem exists_factor (hG0 : G ≠ 0) (V : RCN264.RegularComponent Ω G M R)
    (hV : V.1 ≤ RingHom.ker (aeval v).toRingHom) (hA : aeval v A = 0) (hi : RCN084.IsolatedPoint G M A v) :
    ∃ g, Irreducible g ∧ g ∣ G ∧ g ∈ V.1 ∧ ¬g ∣ M := by
  obtain ⟨g, hg, hgV⟩ := RCN137.exists_normalizedFactorSet_zero (Ideal.Quotient.mk V.1) G hG0
    (Ideal.Quotient.eq_zero_iff_mem.mpr (EN Ω G M R V))
  have hgV' : g ∈ V.1 := Ideal.Quotient.eq_zero_iff_mem.mp hgV
  obtain ⟨hgi, hgG⟩ := RCN137.normalizedFactorSet_spec G g hg
  refine ⟨g, hgi, hgG, hgV', fun hgM => ?_⟩
  obtain ⟨D, hD, hDv⟩ := RCN072.exists_component_of_common_point Ω g A v (hV hgV') hA
  have hgD : g ∈ D := RCN072.cutIdeal_le_component Ω g A D hD (Ideal.subset_span (Set.mem_insert g {A}))
  exact hi D (RCN072.component_isPrime Ω g A D hD) (fun w => RCN072.component_ne_pointKernel Ω g A D hD w) hDv (D.mem_of_dvd hgG hgD)
    (D.mem_of_dvd hgM hgD)
    (RCN072.cutIdeal_le_component Ω g A D hD (Ideal.subset_span (Set.mem_insert_of_mem g (Set.mem_singleton A))))
theorem height_eq_two (V : RCN264.RegularComponent Ω G M R) {g : MvPolynomial (Fin 3) Ω} (hg : Irreducible g)
    (hgV : g ∈ V.1) (hgM : ¬g ∣ M) : V.1.height = 2 := by
  have hprime : (Ideal.span {g}).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 3) Ω)) < Ideal.span {g} :=
    bot_lt_iff_ne_bot.mpr fun h => hg.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hlt : Ideal.span {g} < V.1 :=
    lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr hgV) fun h =>
      hgM (Ideal.mem_span_singleton.mp (h.symm ▸ GV Ω G M R V))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  refine le_antisymm (RCN072.component_height_le_two Ω G M V.1 (AAS Ω G M R V)) ?_
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ (⊥ : Ideal (MvPolynomial (Fin 3) Ω)).height + 1 + 1 := by gcongr; exact zero_le
    _ ≤ (Ideal.span {g}).height + 1 := by gcongr
    _ ≤ V.1.height := h2
theorem nonempty_separable [IsAlgClosed Ω] {p : ℕ} [CharP Ω p] (hG0 : G ≠ 0) (a b : FlagDegree)
    (hGa : RCN095.PolynomialInFlag a G) (hMb : RCN095.PolynomialInFlag b M) (hdeg : a.zOnly + a.yz + a.all < p)
    (hmix : 2 * (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) < p) (V : RCN264.RegularComponent Ω G M R)
    {g : MvPolynomial (Fin 3) Ω} (hg : Irreducible g) (hgG : g ∣ G) (hgV : g ∈ V.1)
    (hgM : ¬g ∣ M) : Nonempty (RCN341.SeparableLiteralCoordinate V.1) := by
  obtain ⟨i, htr⟩ := RCN002.exists_transcendental_coordinate_of_ne_point_kernel Ω V.1 (PU Ω G M R V)
  exact LevelCount.nonempty_separable i htr G g M hG0 hg hgG hgV (GV Ω G M R V) hgM a b hGa hMb
    hdeg hmix
end Curve
section Packet
open scoped Classical
open RCN135 RCN136 RCN313
open BD DU LF WC _Q7 FA
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem good (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) {E : Type} [Field E] [IsAlgClosed E]
    [CharP E 2130706433] (f : GenericField K →+* E) {Q A : MvPolynomial (Fin 3) E}
    (hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA : RCN095.PolynomialInFlag unitYZFlag A)
    {cut : MvPolynomial (Fin 3) (GenericField E)} {v : Fin 3 → GenericField E}
    (V : LevelCurve P SZ f Q A) (hV : V.1 ≤ RingHom.ker (aeval v).toRingHom)
    (hzero : aeval v cut = 0) (hi : RCN084.IsolatedPoint (OO f P.F) (XC f P.F Q A) cut v) :
    GoodCurve P SZ f Q A V ∧ cut ∉ V.1 := by
  have hchar : CharP (GenericField E) 2130706433 := RCN135.genericField_charP E 2130706433
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  have hthi := packet_t_le P
  obtain ⟨hHf, hGf⟩ := RCN201.DGW ((RCN135.coefficientEmbedding E).comp (codeMap f)) (LocatorHybridCells.cellA t y) (LocatorHybridCells.cellB y r) (LocatorHybridCells.cellS r) P.F
    P.support.IZ.2.1 P.support.ys_weight P.support.total_weight
  have hT := LevelCount.levelCut_flag hHf hGf (RCN207.inFlag_map (RCN135.coefficientEmbedding E) hQ)
    (RCN207.inFlag_map (RCN135.coefficientEmbedding E) hA) (RCN135.initialCoordinate E)
  have hG0 : OO f P.F ≠ 0 := fun h0 =>
    P.irreducible.ne_zero (BMZ f (by simpa only [OO, map_zero] using h0))
  have hdeg : t - y + (y - r) + r < 2130706433 := by omega
  have hmix : 2 * (t - y + (y - r) + r) * (LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3)) <
      2130706433 := by
    have h1 : t - y + (y - r) + r = t := by omega
    have h2 : LocatorHybridCells.cellA t y + (LocatorHybridCells.cellB y r + 1) + (LocatorHybridCells.cellS r + 3) = t + 1 := by
      simp only [LocatorHybridCells.cellA, LocatorHybridCells.cellB, LocatorHybridCells.cellS]
      omega
    rw [h1, h2]
    nlinarith
  obtain ⟨g, hg, hgG, hgV, hgM⟩ := exists_factor hG0 V hV hzero hi
  have hsep := nonempty_separable (p := 2130706433) hG0 ⟨t - y, y - r, r⟩ _ (P.parent_flag _ _) hT
    hdeg hmix V hg hgG hgV hgM
  exact ⟨⟨hsep, height_eq_two V hg hgV hgM, g, hg, hgG, hgV, hgM⟩, not_mem_of_isolated V hV hi⟩
end Packet
end Counted
section Packet
open scoped Classical
open RCN135 RCN136 RCN313
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem counted (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : CountedStatement P SZ := by
  intro E _ _ _ f Q A _ hQ hA cut points hG hM hR hzero hi
  have hgood : ∀ (V : LevelCurve P SZ f Q A), ∀ w ∈ RCN264.componentSeeds (GenericField E) _ _ _ points id V,
      GoodCurve P SZ f Q A V ∧ cut ∉ V.1 := fun V w hw =>
    Counted.good P SZ f hQ hA V (RCN264.componentSeeds_on_prime (GenericField E) _ _ _ points id V w hw)
      (hzero w (RCN264.componentSeeds_subset (GenericField E) _ _ _ points id V hw))
      (hi w (RCN264.componentSeeds_subset (GenericField E) _ _ _ points id V hw))
  have hplaces : ∀ V : LevelCurve P SZ f Q A,
      ∃ TV : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1)),
        (∀ μ ∈ TV, μ.val (RCN002.coordinateEvaluation (GenericField E) V.1 cut) < 1) ∧
          (RCN264.componentSeeds (GenericField E) _ _ _ points id V).card ≤ TV.card := by
    intro V
    rcases (RCN264.componentSeeds (GenericField E) _ _ _ points id V).eq_empty_or_nonempty with hempty | ⟨w₀, hw₀⟩
    · exact ⟨∅, fun μ hμ => absurd hμ (Finset.notMem_empty μ), by
        rw [hempty, Finset.card_empty]
        exact Nat.zero_le _⟩
    · obtain ⟨base⟩ := (hgood V w₀ hw₀).1.1
      choose place hplace using
        fun pt : {w : Fin 3 → GenericField E // w ∈ RCN264.componentSeeds (GenericField E) _ _ _ points id V} =>
          exists_placeOver base (RCN264.componentSeeds_on_prime (GenericField E) _ _ _ points id V pt.1 pt.2)
      have hinj : Function.Injective place := fun pt pt' hpt =>
        Subtype.ext ((hplace pt).point_eq (by rw [hpt]; exact hplace pt'))
      refine ⟨(RCN264.componentSeeds (GenericField E) _ _ _ points id V).attach.image place, fun μ hμ => ?_, ?_⟩
      · obtain ⟨pt, -, rfl⟩ := Finset.mem_image.mp hμ
        exact hplace pt cut (hzero pt.1 (RCN264.componentSeeds_subset (GenericField E) _ _ _ points id V pt.2))
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  choose T hT hcard using hplaces
  refine ⟨Finset.univ.filter fun V => (RCN264.componentSeeds (GenericField E) _ _ _ points id V).Nonempty, T,
    fun V hV => ?_, ?_⟩
  · obtain ⟨w₀, hw₀⟩ := (Finset.mem_filter.mp hV).2
    exact ⟨(hgood V w₀ hw₀).1, (hgood V w₀ hw₀).2, hT V⟩
  · calc points.card
        ≤ ∑ V : LevelCurve P SZ f Q A, (RCN264.componentSeeds (GenericField E) _ _ _ points id V).card :=
          WX (GenericField E) _ _ _ points id hG hM hR
      _ = ∑ V ∈ Finset.univ.filter fun V => (RCN264.componentSeeds (GenericField E) _ _ _ points id V).Nonempty,
            (RCN264.componentSeeds (GenericField E) _ _ _ points id V).card :=
          (Finset.sum_filter_of_ne fun V _ h => Finset.card_ne_zero.mp h).symm
      _ ≤ _ := Finset.sum_le_sum fun V _ => hcard V
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open scoped Classical BigOperators
open WithZero MvPolynomial
open RCN002 RCN084 RCN095 RCN135 RCN136 RCN204 RCN264 RCN313
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open BD DU LF WC _Q7
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Curve
variable {k : Type} [Field k] [IsAlgClosed k]
theorem card_le_sum_flagPole (D : Ideal (MvPolynomial (Fin 3) k)) [D.IsPrime] (base : RCN341.SeparableLiteralCoordinate D)
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) k) (hW : RCN095.PolynomialInFlag W cut) (hcut : cut ∉ D)
    (T : Finset (RCN026.Place_p19 k (RCN002.CoordinateField k D))) (hT : ∀ μ ∈ T, μ.val (RCN002.coordinateEvaluation k D cut) < 1) :
    ∃ T' : Finset (RCN026.Place_p19 k (RCN002.CoordinateField k D)),
      (T.card : ℤ) ≤ ∑ μ ∈ T', flagPole μ.val (coordinate k D) W := by
  have hpsi : RCN002.coordinateEvaluation k D cut ≠ 0 := fun h => hcut (by rw [← RCN002.coordinateEvaluation_ker k D]; exact h)
  obtain ⟨T₁, hT₁⟩ := LevelCount.exists_sum_order_eq_zero base (RCN002.coordinateEvaluation k D cut) hpsi
  refine ⟨T₁ ∪ T, ?_⟩
  have h0 := hT₁ (T₁ ∪ T) Finset.subset_union_left
  have hmain : ∀ μ ∈ T₁ ∪ T,
      (if μ ∈ T then (1 : ℤ) else 0) - flagPole μ.val (coordinate k D) W ≤
        RCN026.order_p19 k (RCN002.CoordinateField k D) μ (RCN002.coordinateEvaluation k D cut) := by
    intro μ _
    have hne : μ.val (RCN002.coordinateEvaluation k D cut) ≠ 0 := (Valuation.ne_zero_iff _).mpr hpsi
    have hpole : (μ.val (RCN002.coordinateEvaluation k D cut)).log ≤ flagPole μ.val (coordinate k D) W := by
      have h := RCN204.valuation_eval_le_flag μ.val (algebraMap k (RCN002.CoordinateField k D)) (RCN344.NP k (RCN002.CoordinateField k D) μ) (coordinate k D) W cut hW
      rw [← MvPolynomial.aeval_eq_eval₂Hom, ← RCN002.coordinateEvaluation_eq_aeval] at h
      exact (log_le_iff_le_exp hne).mpr h
    by_cases hμ : μ ∈ T
    · have hlog : (μ.val (RCN002.coordinateEvaluation k D cut)).log < 0 :=
        (log_lt_iff_lt_exp hne).mpr (by rw [exp_zero]; exact hT μ hμ)
      have h2 := RCN204.flagPole_nonneg μ.val (coordinate k D) W
      simp only [hμ, ↓reduceIte, RCN026.order_p19]
      omega
    · simp only [hμ, ↓reduceIte, RCN026.order_p19]
      omega
  have hsum := Finset.sum_le_sum hmain
  rw [h0, Finset.sum_sub_distrib, sub_nonpos, Finset.sum_ite_mem, Finset.union_inter_cancel_right,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact hsum
end Curve
theorem curve_arith (n β γ w0 w1 w2 : ℕ) (N a b1 c1 b2 c2 b c : ℤ)
    (hN : N ≤ w0 * a + w1 * b1 + w2 * c1) (h2 : n * a ≤ β * b2 + γ * c2) (hb1 : b1 ≤ b)
    (hc1 : c1 ≤ c) (hb2 : b2 ≤ b) (hc2 : c2 ≤ c) :
    n * N ≤ w0 * (β * b + γ * c) + w1 * (n * b) + w2 * (n * c) := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have e1 := mul_le_mul_of_nonneg_left hN hn
  have e2 : (β : ℤ) * b2 + γ * c2 ≤ β * b + γ * c :=
    add_le_add (mul_le_mul_of_nonneg_left hb2 (Int.natCast_nonneg β))
      (mul_le_mul_of_nonneg_left hc2 (Int.natCast_nonneg γ))
  have e3 := mul_le_mul_of_nonneg_left (h2.trans e2) (Int.natCast_nonneg w0)
  have e4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hn) (Int.natCast_nonneg w1)
  have e5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc1 hn) (Int.natCast_nonneg w2)
  linarith
theorem budget_arith (n β γ w0 w1 w2 scale u v N : ℕ) (Ts bS cS : ℤ) (hN : (N : ℤ) ≤ Ts)
    (hsum : (n : ℤ) * Ts ≤ w0 * (β * bS + γ * cS) + w1 * (n * bS) + w2 * (n * cS))
    (hu : (scale : ℤ) * bS ≤ u) (hv : (scale : ℤ) * cS ≤ v) :
    n * scale * N ≤ w0 * (β * u + γ * v) + w1 * (n * u) + w2 * (n * v) := by
  have key : ((n * scale * N : ℕ) : ℤ) ≤
      ((w0 * (β * u + γ * v) + w1 * (n * u) + w2 * (n * v) : ℕ) : ℤ) := by
    push_cast
    have hs : (0 : ℤ) ≤ scale := Int.natCast_nonneg scale
    have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have e1 := mul_le_mul_of_nonneg_left hN (mul_nonneg hn hs)
    have e2 := mul_le_mul_of_nonneg_left hsum hs
    have e3 := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hu (Int.natCast_nonneg β))
      (mul_le_mul_of_nonneg_left hv (Int.natCast_nonneg γ))) (Int.natCast_nonneg w0)
    have e4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hn) (Int.natCast_nonneg w1)
    have e5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hn) (Int.natCast_nonneg w2)
    linarith
  exact_mod_cast key
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem point_budget_of_parts (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (h1 : CountedStatement P SZ)
    (h3 : CurveH2Statement P) (h4 : UnitBoundStatement P SZ) : H2Lev.PointBudgetStatement P SZ := by
  intro N _ _ _ n β γ haux E _ _ _ f scale z u v hold Q A hA2 hQ hA W cut hcut points hG hM hreg hzero
    hiso
  have hold' : scale * points.card ≤ W.zOnly * z + W.yz * u + W.all * v :=
    hold Q A hA2 hQ hA W cut hcut points hG hM hreg hzero hiso
  rcases le_total (n * z) (β * u + γ * v) with hmin | hmin
  · rw [min_eq_left hmin]
    calc n * scale * points.card = n * (scale * points.card) := by ring
      _ ≤ n * (W.zOnly * z + W.yz * u + W.all * v) := Nat.mul_le_mul_left _ hold'
      _ = W.zOnly * (n * z) + W.yz * (n * u) + W.all * (n * v) := by ring
  rw [min_eq_right hmin]
  obtain ⟨S, T, hST, hcard⟩ := h1 E f Q A hA2 hQ hA cut points hG hM hreg hzero hiso
  have hcurve : ∀ V : LevelCurve P SZ f Q A,
      ∃ U : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1)), V ∈ S →
        (n : ℤ) * ((T V).card : ℤ) ≤
          (W.zOnly : ℤ) *
              ((β : ℤ) * ∑ μ ∈ U, flagPole μ.val (coordinate (GenericField E) V.1) unitYZFlag +
                (γ : ℤ) * ∑ μ ∈ U, flagPole μ.val (coordinate (GenericField E) V.1) unitAllFlag) +
            (W.yz : ℤ) *
              ((n : ℤ) * ∑ μ ∈ U, flagPole μ.val (coordinate (GenericField E) V.1) unitYZFlag) +
            (W.all : ℤ) *
              ((n : ℤ) * ∑ μ ∈ U, flagPole μ.val (coordinate (GenericField E) V.1) unitAllFlag) := by
    intro V
    by_cases hV : V ∈ S
    swap
    · exact ⟨∅, fun h => absurd h hV⟩
    obtain ⟨⟨⟨base⟩, -, -⟩, hcutV, hTV⟩ := hST V hV
    obtain ⟨T1, hT1⟩ := card_le_sum_flagPole V.1 base W cut hcut hcutV (T V) hTV
    have hH : surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) (polyH K P.F) ∉ V.1 := fun h =>
      _Q6 (GenericField E) _ _ _ V (by
        show surfaceMap ((RCN135.coefficientEmbedding E).comp (codeMap f)) (2 * polyH K P.F) * MvPolynomial.map (RCN135.coefficientEmbedding E) (2 * A) *
          SZ.leading ((RCN135.coefficientEmbedding E).comp (codeMap f)) ∈ V.1
        rw [map_mul]
        exact V.1.mul_mem_right _ (V.1.mul_mem_right _ (V.1.mul_mem_left _ h)))
    obtain ⟨T2, hT2⟩ := h3 n β γ haux E f Q A V.1 base (EN (GenericField E) _ _ _ V)
      (GV (GenericField E) _ _ _ V) hH (PU (GenericField E) _ _ _ V) T1
    refine ⟨T1 ∪ T2, fun _ => ?_⟩
    have hmono : ∀ (F : FlagDegree) (T0 : Finset (RCN026.Place_p19 (GenericField E) (RCN002.CoordinateField (GenericField E) V.1))),
        T0 ⊆ T1 ∪ T2 → ∑ μ ∈ T0, flagPole μ.val (coordinate (GenericField E) V.1) F ≤
          ∑ μ ∈ T1 ∪ T2, flagPole μ.val (coordinate (GenericField E) V.1) F := fun F T0 h =>
      Finset.sum_le_sum_of_subset_of_nonneg h fun μ _ _ => RCN204.flagPole_nonneg _ _ _
    have hsplit : ∑ μ ∈ T1, flagPole μ.val (coordinate (GenericField E) V.1) W =
        (W.zOnly : ℤ) * ∑ μ ∈ T1, flagPole μ.val (coordinate (GenericField E) V.1) unitZFlag +
          (W.yz : ℤ) * ∑ μ ∈ T1, flagPole μ.val (coordinate (GenericField E) V.1) unitYZFlag +
          (W.all : ℤ) * ∑ μ ∈ T1, flagPole μ.val (coordinate (GenericField E) V.1) unitAllFlag := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun μ _ => LevelCount.flagPole_eq_units _ _ _
    rw [hsplit] at hT1
    exact curve_arith n β γ W.zOnly W.yz W.all _ _ _ _ _ _ _ _ hT1 hT2
      (hmono unitYZFlag T1 Finset.subset_union_left) (hmono unitAllFlag T1 Finset.subset_union_left)
      (hmono unitYZFlag T2 Finset.subset_union_right) (hmono unitAllFlag T2 Finset.subset_union_right)
  choose U hU using hcurve
  obtain ⟨hu, hv⟩ := h4 E f scale z u v Q A hA2 hQ hA (hold Q A hA2 hQ hA) S
    (fun V hV => (hST V hV).1) U
  have hsum := Finset.sum_le_sum fun V hV => hU V hV
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact budget_arith n β γ W.zOnly W.yz W.all scale u v points.card _ _ _ (by exact_mod_cast hcard)
    hsum hu hv
end Packet
end
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open scoped Classical
open MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN222 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
noncomputable section
section Packet
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
omit [CharP K 2130706433] in
theorem surfaceMap_collect_symm {L : Type} [Field L] (φ : Polynomial K →+* L)
    (G' : MvPolynomial (Fin 3) (Polynomial K)) :
    surfaceMap φ ((collectX K).symm G') = MvPolynomial.map φ G' := by
  show MvPolynomial.map φ (collectX K ((collectX K).symm G')) = _
  rw [AlgEquiv.apply_symm_apply]
omit [CharP K 2130706433] in
theorem exists_cleared (Gk : MvPolynomial (Fin 3) (RationalBase K)) :
    ∃ (G : MvPolynomial (Fin 4) K) (d : RationalBase K), d ≠ 0 ∧
      surfaceMap (algebraMap (Polynomial K) (RationalBase K)) G = C d * Gk ∧
      surfaceMap (RCN135.polynomialEmbedding K) G = C (algebraMap (RationalBase K) Ω d) *
        MvPolynomial.map (algebraMap (RationalBase K) Ω) Gk := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (Polynomial K)) Gk.coeffs
  have hd : algebraMap (Polynomial K) (RationalBase K) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RationalBase K))).mpr
      (nonZeroDivisors.coe_ne_zero b)
  obtain ⟨G', hG'⟩ : ∃ G' : MvPolynomial (Fin 3) (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RationalBase K)) G' =
        C (algebraMap (Polynomial K) (RationalBase K) b) * Gk := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc => ?_
    obtain ⟨m, hm, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    rw [coeff_C_mul]
    have hcm : Gk.coeff m ≠ 0 := fun h0 => by
      rw [MvPolynomial.mem_support_iff, coeff_C_mul, h0, mul_zero] at hm
      exact hm rfl
    obtain ⟨z, hz⟩ := RingHom.mem_rangeS.mp (hb _ (MvPolynomial.coeff_mem_coeffs m hcm))
    exact ⟨z, by rw [hz, Algebra.smul_def]⟩
  refine ⟨(collectX K).symm G', _, hd, ?_, ?_⟩
  · rw [surfaceMap_collect_symm, hG']
  · have h1 : MvPolynomial.map (RCN135.polynomialEmbedding K) G' = MvPolynomial.map (algebraMap (RationalBase K) Ω)
        (MvPolynomial.map (algebraMap (Polynomial K) (RationalBase K)) G') := by
      rw [MvPolynomial.map_map]
      rfl
    rw [surfaceMap_collect_symm, h1, hG', map_mul, MvPolynomial.map_C]
theorem exists_of (P : Packet x t y r) (hdeg : SectionDegreeStatement P)
    (hpole : PoleSpaceStatement (GenericField K)) : ExistsStatement P := by
  intro N hN hNp hc n β γ rlo rhi yhi tlo hr1 hr2 hy ht hcert
  refine ⟨{c0 | ¬GoodValue P c0}, goodValue_finite P N hN hNp hc, fun c0 hc0 => ?_⟩
  have h0 : GoodValue P c0 := not_not.mp hc0
  refine ⟨h0.ne_zero, ?_⟩
  have hinj : Function.Injective (algebraMap (RationalBase K) Ω) :=
    (algebraMap (RationalBase K) Ω).injective
  have hne : baseCarrier P.F ≠ 0 := RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero
  have hFk : carrierK P ≠ 0 := fun h => hne (by rw [← map_carrierK, h, map_zero])
  have hdegR : (carrierK P).degreeOf 1 = (baseCarrier P.F).degreeOf 1 := by
    rw [← map_carrierK, degreeOf_eq_sup, degreeOf_eq_sup, support_map_of_injective _ hinj]
  have htot : (carrierK P).totalDegree = (baseCarrier P.F).totalDegree := by
    rw [← map_carrierK, totalDegree, totalDegree, support_map_of_injective _ hinj]
  have hbox := H2Count.boxCount_sub_ite_le_finrank_map_box
    (Ideal.Quotient.mkₐ (RationalBase K) (Ideal.span {carrierK P})).toLinearMap hFk
    (H2Count.mkₐ_eq_zero_iff (carrierK P)) (ρ := γ) (θ := β + γ) (r := rlo) (t := tlo)
    (by rw [hdegR]; exact hr1) (by rw [htot]; exact ht)
  obtain ⟨Gk, hGbox, hGdvd, Ak, Hk, hGk⟩ := count (RationalBase K) (carrierK P) c0 γ (β + γ) n
    (β * rhi + γ * yhi + rhi)
    (fun j _ => layerBound_of P hdeg hpole N hN hNp hc c0 h0 β γ rhi yhi hr2 hy j)
    (lt_of_lt_of_le hcert hbox)
  obtain ⟨G, d, hd, hGsmall, hGΩ⟩ := exists_cleared Gk
  have hndvd : ¬P.F ∣ G := by
    rintro ⟨Q, hQ⟩
    have h1 := congrArg (surfaceMap (algebraMap (Polynomial K) (RationalBase K))) hQ
    rw [hGsmall, map_mul] at h1
    exact hGdvd (((isUnit_iff_ne_zero.mpr hd).map
      (C : RationalBase K →+* MvPolynomial (Fin 3) (RationalBase K))).dvd_mul_left.mp ⟨_, h1⟩)
  refine ⟨G, hndvd, fun g hg0 => ?_, ?_, ?_⟩
  · have hk : G ∈ Ideal.span ({P.F} : Set (MvPolynomial (Fin 4) K)) := by
      rw [← Exch.ker_sliceMap_component P g, RingHom.mem_ker, Exch.sliceMap_component]
      exact hg0
    exact hndvd (Ideal.mem_span_singleton.mp hk)
  · rw [hGΩ]
    intro e he
    have h1 : e ∈ Gk.support := by
      rw [MvPolynomial.mem_support_iff] at he ⊢
      intro h2
      apply he
      rw [coeff_C_mul, coeff_map, h2, map_zero, mul_zero]
    have h2 := H2Count.mem_box_iff_support.mp hGbox e h1
    show e 1 ≤ γ ∧ e 0 + e 1 ≤ β + γ ∧ e 0 + e 1 + e 2 ≤ 0 + β + γ
    omega
  · refine ⟨C (algebraMap (RationalBase K) Ω d) * MvPolynomial.map (algebraMap (RationalBase K) Ω) Ak,
      C (algebraMap (RationalBase K) Ω d) * MvPolynomial.map (algebraMap (RationalBase K) Ω) Hk, ?_⟩
    rw [hGΩ, hGk, map_add, map_mul, map_mul, map_pow, map_carrierK, map_levelForm]
    ring
end Packet
end
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Lev
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Packet
noncomputable section
open scoped Classical
open RCN074 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime Exch.fact_irreducible
def ChoiceH2Statement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ j, sliceCoord P.F j ≠ 0)
    (_htail : tail P.F P.F (dvd_refl P.F) w ≠ 0) (_hlead : srcLead P.F P.F SZ ≠ 0)
    (_hbase : ∀ a : Curve P, RCN341.SeparableLiteralCoordinate a.2.1)
    (_hsep : ∀ Q A : MvPolynomial (Fin 3) Ω, RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
      ∀ (c : Ω) (g : RCN222.GeometricFactor K P.F),
        Exch.moving P Q A g ≠ algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P g)) c →
        ∀ B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c,
          Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
    (_hclosure : ∀ (g : RCN222.GeometricFactor K P.F) (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime]
      (S : Specialization (RCN002.CoordinateField Ω (Exch.component P g)) (RCN002.CoordinateField Ω C)),
      IsCurveOnSurface (Exch.component P g) C S →
      ∀ (q : SurfacePoint (Exch.component P g)) (hq : q.On S), RCN341.SeparableLiteralCoordinate C →
        Module.Finite (S.image hq) (integralClosure (S.image hq) (RCN002.CoordinateField Ω C)))
    (n β γ : ℕ) (_haux : H2Sec.ExistsAux P n β γ),
    ∃ (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
      (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1))
      (s₀ s₁ s₂ : MvPolynomial (Fin 3) Ω),
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q ∧ RCN095.PolynomialInFlag unitYZFlag A ∧ (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 ∧
      (∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) ∧
      CurveNeeds P SZ Q A c S ∧
      Exch.ExchangeNeeds P SZ Q A c S (Exch.flag SZ ⟨t - y, y - r, r - 1⟩) ∧
      LevelNeeds P SZ Q A c S ∧
      Sec.Needs P SZ Q A c unitZFlag s₀ ∧ Sec.Needs P SZ Q A c unitYZFlag s₁ ∧
      Sec.Needs P SZ Q A c unitAllFlag s₂ ∧ LevelH2 P n β γ Q A c
theorem choice (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F) :
    ChoiceH2Statement P SZ := by
  intro N hN hNp hc htail hlead hbase hsep hclosure n β γ haux
  obtain ⟨S, hS⟩ := Data.curves P hp
  obtain ⟨Q, A, hQ, hA, h2, hpole⟩ := Data.pair P N hN hNp hc
  obtain ⟨bad, hbadfin, hH2⟩ :=
    level P N hN hNp (fun g => Exch.coordinate_ne_zero P g hc) n β γ haux Q A hQ hA
  obtain ⟨c, hbad⟩ := ((((Data.off_level P SZ Q A S fun a _ => hS a).union
    (Data.seed P SZ Q A)).union ((Data.component_ne P Q A).union
      (Data.component_unit P SZ N hN hNp hc htail hlead Q A))).union hbadfin).exists_notMem
  have hlive : ∀ a ∈ active P SZ, (S a).val (Exch.moving P Q A a.1 -
      algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) = 1 := fun a ha =>
    by_contra fun h => hbad (Or.inl (Or.inl (Or.inl ⟨a, ha, h⟩)))
  have hcomp : ∀ g, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
      (Exch.moving P Q A g) c (Exch.function P SZ g) := fun g =>
    ⟨fun h => hbad (Or.inl (Or.inr (Or.inl ⟨g, h⟩))), fun nu hnu hlt =>
      by_contra fun h => hbad (Or.inl (Or.inr (Or.inr ⟨g, nu, hnu, hlt, h⟩)))⟩
  obtain ⟨s₀, s₁, s₂, h₀, h₁, h₂⟩ := SecChoice.sections P SZ N hN hNp hc hlead Q A c hcomp
    fun g B => hsep Q A hQ hA c g (hcomp g).ne B
  refine ⟨Q, A, c, S, s₀, s₁, s₂, hQ, hA, h2, fun a _ => hS a,
    ⟨fun a _ => hpole a.1, hlive, fun a ha δ hδ h =>
      hbad (Or.inl (Or.inl (Or.inr ⟨a, ha, δ, hδ, h⟩)))⟩,
    ⟨fun a _ => Data.disjoint_of_needs P SZ N a.1 (hN a.1) hNp Q A c _ (hcomp a.1),
      fun a _ q hq _ _ => hclosure a.1 a.2.1 (S a) (hS a) q hq (hbase a)⟩,
    ⟨hcomp, hlive, fun a _ q hq _ _ => hclosure a.1 a.2.1 (S a) (hS a) q hq (hbase a),
      fun g B q hq => ?_⟩, h₀, h₁, h₂, hH2 c fun h => hbad (Or.inr h)⟩
  obtain ⟨bp⟩ := hsep Q A hQ hA c g (hcomp g).ne B
  exact hclosure g B.prime B.curve B.isCurve q hq bp
end
end Packet
end H2Lev
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Bud
open BD DU
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem unit_bound (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : UnitBoundStatement P SZ :=
  unit_bound_of_parts P SZ (isolated P SZ) (fibre_bound_of_separable P SZ (separable_form P SZ))
theorem point_budget (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : H2Lev.PointBudgetStatement P SZ :=
  point_budget_of_parts P SZ (counted P SZ) (curve_h2 P) (unit_bound P SZ)
end H2Bud
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2Sec
open RCN135 RCN222 DU
open RCN222 renaming GeometricFactor → EX
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
theorem exists_aux (P : Packet x t y r) : ExistsStatement P :=
  exists_of P (H2Deg.section_degree P) (H2Pole.poleSpace (GenericField K))
end H2Sec
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2
open scoped Classical
open MvPolynomial
open RCN002 RCN072 RCN095 RCN135 RCN136 RCN156 RCN222 RCN234 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT
open MovingFiberThreeSources6811 (direction weight)
section Surface
variable {K L : Type*} [Field K] [Field L]
theorem tail_mem_support_surfaceMap (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) {d : Fin 4 →₀ ℕ} (hd : d ∈ Q.support) :
    d.tail ∈ (surfaceMap φ Q).support := by
  rw [MvPolynomial.mem_support_iff]
  have hsum : surfaceMap φ Q = ∑ e ∈ Q.support,
      MvPolynomial.monomial e.tail (φ (Polynomial.C (Q.coeff e)) * φ Polynomial.X ^ e 0) := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff Q, map_sum]
    exact Finset.sum_congr rfl fun e _ => RCN136.surfaceMap_monomial φ e _
  have hmap : ∑ e ∈ Q.support.filter (fun e => e.tail = d.tail),
        φ (Polynomial.C (Q.coeff e)) * φ Polynomial.X ^ e 0 =
      φ (∑ e ∈ Q.support.filter (fun e => e.tail = d.tail),
        Polynomial.C (Q.coeff e) * Polynomial.X ^ e 0) := by
    simp only [map_sum, map_mul, map_pow]
  rw [hsum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [← Finset.sum_filter, hmap]
  refine (map_ne_zero_iff φ hφ).2 fun h0 => ?_
  have hc := congrArg (fun p => Polynomial.coeff p (d 0)) h0
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single_of_mem d
    (show d ∈ Q.support.filter (fun e => e.tail = d.tail) from Finset.mem_filter.2 ⟨hd, rfl⟩)] at hc
  · simp only [↓reduceIte, mul_one] at hc
    exact MvPolynomial.mem_support_iff.1 hd hc
  · intro e he hne
    have ht := (Finset.mem_filter.1 he).2
    have h0' : d 0 ≠ e 0 := fun h => hne (by rw [← Finsupp.cons_tail e, ← Finsupp.cons_tail d, ht, h])
    simp only [h0', ↓reduceIte, mul_zero]
end Surface
section Packet
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
theorem baseCarrier_degreeOf_le (P : Packet x t y r) : (baseCarrier P.F).degreeOf 1 ≤ r :=
  MvPolynomial.degreeOf_le_iff.2 fun d hd => (P.parent_flag Ω (RCN135.polynomialEmbedding K) d hd).1
omit [CharP K 2130706433] in
theorem one_le_baseCarrier_degreeOf (P : Packet x t y r) : 1 ≤ (baseCarrier P.F).degreeOf 1 := by
  have hpos := P.rdegree
  rw [MvPolynomial.degreeOf_eq_sup] at hpos
  obtain ⟨d, hd, hd2⟩ := Finset.lt_sup_iff.1 hpos
  exact (Nat.succ_le_of_lt hd2).trans
    (MvPolynomial.monomial_le_degreeOf 1 (tail_mem_support_surfaceMap (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F hd))
theorem baseCarrier_middle_le (P : Packet x t y r) :
    ∀ d ∈ (baseCarrier P.F).support, d 0 + d 1 ≤ y := fun d hd => by
  have h := (P.parent_flag Ω (RCN135.polynomialEmbedding K) d hd).2.1
  have hy := P.ylow
  dsimp only at h
  omega
omit [CharP K 2130706433] in
theorem le_baseCarrier_totalDegree (P : Packet x t y r) {T0 : ℕ} (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) :
    T0 ≤ (baseCarrier P.F).totalDegree := by
  rcases Nat.eq_zero_or_pos T0 with rfl | hpos
  · exact Nat.zero_le _
  obtain ⟨d, hd, hdw⟩ := (Finset.le_sup_iff (by exact hpos)).1 hT0
  have hmem := tail_mem_support_surfaceMap (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F hd
  have hle := MvPolynomial.le_totalDegree hmem
  rw [RCN081.weight_fin4] at hdw
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three] at hle
  simp only [Finsupp.tail_apply] at hle
  rw [show Fin.succ (0 : Fin 3) = 1 from rfl, show Fin.succ (1 : Fin 3) = 2 from rfl,
    show Fin.succ (2 : Fin 3) = 3 from rfl] at hle
  simp only [RCN156.residualTotalWeights, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hdw
  exact le_trans (by omega) hle
theorem existsAux_of_certificate (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (T0 B C qd n : ℕ) (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n) :
    H2Sec.ExistsAux P n (n / qd * B) (n / qd * C) :=
  H2Sec.exists_aux P t (Chart.surfaceNoether_component P hp) (Chart.packet_three_mul_lt P)
    (Chart.packet_coordinate_ne_zero P hp) n (n / qd * B) (n / qd * C) _ _ y T0 le_rfl le_rfl
    (baseCarrier_middle_le P) (le_baseCarrier_totalDegree P hT0)
    (hcert.count (one_le_baseCarrier_degreeOf P) (baseCarrier_degreeOf_le P))
end Packet
end H2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2
def heightH2 (B C qd z u v : ℕ) : ℕ :=
  min (qd * z) (B * u + C * v)
theorem heightH2_mono (B C qd z : ℕ) {u u' v v' : ℕ} (hu : u ≤ u') (hv : v ≤ v') :
    heightH2 B C qd z u v ≤ heightH2 B C qd z u' v' :=
  min_le_min le_rfl (Nat.add_le_add (Nat.mul_le_mul_left B hu) (Nat.mul_le_mul_left C hv))
section Level
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 HFree6812 DU BLL AYR BIO BBT _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime Exch.fact_irreducible
theorem counts_h2
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : Cut.IsHFlag P Hf) (scale z u v T0 B C qd n : ℕ)
    (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n)
    (lam mu : Ω) (geometry : ∀ g, ABN (P.stage g))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F))
    (hframe : PacketFrame P hp SZ scale z u v lam mu geometry budget) :
    ∃ (moving : Curve P → ℕ) (o : ℕ → Curve P → ℕ) (Lam Kc : ℕ),
      Cut.CurveCount P SZ Hf budget moving o ∧
        Cut.LevelCount P hp SZ Hf (qd * scale) (heightH2 B C qd z u v) (qd * u) (qd * v) moving Lam ∧
        ExchangeCount P hp SZ o Lam Kc := by
  by_cases hlead : srcLead P.F P.F SZ = 0
  · have hempty : active P SZ = ∅ :=
      Finset.eq_empty_of_forall_notMem fun a ha => Assembly.srcLead_ne_zero P SZ a ha hlead
    refine ⟨fun _ => 0, fun _ _ => 0, 0, 0, ?_, ?_, ?_⟩
    · intro k a ha
      exact absurd (hempty ▸ ha) (Finset.notMem_empty a)
    · simp [Cut.LevelCount]
    · intro k
      simp
  have haux := existsAux_of_certificate P hp T0 B C qd n hT0 hcert
  have hqd := hcert.1
  have hn := hcert.2.2.1
  obtain ⟨m, rfl⟩ := hcert.2.1
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left m hqd] at haux
  have hc := Chart.packet_sliceCoord_ne_zero P hp
  have hI : ∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ := fun sR sY sZ =>
    Chart.common_psiS_integral P.F P.F (dvd_refl P.F) (Chart.packet_polyH_ne_zero P) t P.total_weight
      (by have := packet_t_le P; omega) hc SZ (RCN347.factorial_cast_ne_zero_below_characteristic 2130706433 SZ.k hZd) hlead Hf h5 hHf sR sY sZ
  have hN := Chart.surfaceNoether_component P hp
  have hNp := Chart.packet_three_mul_lt P
  have hsep := LevelCount.separable P
  obtain ⟨Q, A, c, S, s₀, s₁, s₂, hQ, hA, -, hS, hCn, hXn, hLn, h₀, h₁, h₂, hH2⟩ :=
    H2Lev.choice P hp SZ t hN hNp hc (Exch.tail_ne_zero P hp) hlead
      (fun a => suppliedBase (P.stage a.1) (geometry a.1) a.2) hsep
      (fun g _ _ _ h q hq sep =>
        h.finite_integralClosure (Chart.packet_coordinate_ne_zero P hp g) q hq sep)
      (qd * m) (m * B) (m * C) haux
  have htail := tail_order P hp SZ S hS
  have hbound := H2Lev.section_bound P (qd * m) (m * B) (m * C) Q A c hH2 scale z u v
    (Sec.section_bound P SZ scale z u v hframe.point_budget t hN hNp
      (Chart.packet_coordinate_ne_zero P hp) Q A hQ hA c
      (fun _ _ _ => PlaceSurf.surfacePoint_length_eq_zeros)
      (fun g Bc => hsep Q A hQ hA c g (hLn.component g).ne Bc) s₀ s₁ s₂ h₀ h₁ h₂)
  have hXf : Exch.ExchangeNeeds P SZ Q A c S (Exch.flag SZ Hf) :=
    ⟨fun a _ => Exch.levelDisjoint_of_unit (hN a.1) hNp _ c _ _ fun nu hnu hlt =>
      ⟨((hLn.component a.1).unit nu hnu hlt).1, ((hLn.component a.1).unit nu hnu hlt).2.2.2⟩,
      hXn.closure⟩
  have hlevel := LevelCount.level_count_price P hp SZ (qd * m * scale)
    (min (qd * m * z) (m * B * u + m * C * v)) (qd * m * u) (qd * m * v) Hf Q A c S hS hLn hbound hc hI
    t hN hNp htail hQ hA
  rw [show qd * m * z = m * (qd * z) by ring, show m * B * u + m * C * v = m * (B * u + C * v) by ring,
    Nat.mul_min_mul_left] at hlevel
  refine ⟨fun a => curveMoving (S a) (Exch.moving P Q A a.1) c, Exch.baseOrder P Q A c S,
    Exch.lam P SZ Q A c (Exch.flag SZ Hf), Exch.constant P hp SZ Q A c S (Exch.flag SZ Hf),
    Curve.count_flag P SZ Hf h5 (fun _ _ _ val hval => hHf val hval.trivial_on_K hval.x0_le_one) budget
      (fun a => suppliedBase (P.stage a.1) (geometry a.1) a.2) t hN hNp Q A c S hS hCn,
    ?_,
    Exch.exchange_count P hp SZ Hf Q A c S hS hXf hc hI t hN hNp htail
      (fun _ _ => PlaceSurf.surfacePoint_leastOrder_le)⟩
  obtain ⟨hWz, hWu, hWv⟩ := Cut.exchFlag_le SZ Hf
  unfold Cut.LevelCount heightH2
  simp only [price] at hlevel ⊢
  refine Nat.le_of_mul_le_mul_left ?_ hm
  nlinarith [hlevel, Nat.mul_le_mul_right (m * min (qd * z) (B * u + C * v)) hWz,
    Nat.mul_le_mul_right (m * (qd * u)) hWu, Nat.mul_le_mul_right (m * (qd * v)) hWv]
end
end Level
end H2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2
section Price
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN046 RCN074 RCN086 RCN095 RCN130 RCN135 RCN156 RCN199 RCN222 RCN234 RCN237 RCN238 RCN243
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN264 RCN313 RCN334 RCN340 RCN344
open FA PR BD HK HFreeDir6813 DU BLL AYR BIO BBT _Q7 AFA RL TW CB BOE
open CommonLinearChannels6807 (linearA linearU linearZ)
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
def pairStageCostREH {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : MovingFiberThreeSources6811.Source F) (delta B C qd t y r : ℕ) (flag : FlagDegree) : ℕ :=
  Cut.numeratorRE SZ.d (qd * stageScale SZ delta)
    (heightH2 B C qd (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
      (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag))
    (qd * (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag))
    (qd * (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag))
    t y r flag SZ.flag / (9 * SZ.d * (qd * stageScale SZ delta))
def pairCostREH (d : ℕ) (S : FlagDegree) (delta : ℕ) (p q : FlagDegree) (B C qd t y r : ℕ) : ℕ :=
  Cut.numeratorRE d (qd * (d * delta))
    (heightH2 B C qd (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag S)
      (d * flagMixed p q unitYZFlag) (d * flagMixed p q unitAllFlag))
    (qd * (d * flagMixed p q unitYZFlag)) (qd * (d * flagMixed p q unitAllFlag))
    t y r ⟨t - y, y - r, r⟩ S / (9 * d * (qd * (d * delta)))
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)
theorem point_budget_h2
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v T0 B C qd n : ℕ)
    (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n)
    {E : Type} [Field E] [IsAlgClosed E] [CharP E 2130706433] (f : GenericField K →+* E)
    (hold : ∀ Q A : MvPolynomial (Fin 3) E, (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN f P.F SZ Q A scale z u v) :
    ∀ Q A : MvPolynomial (Fin 3) E, (2 : MvPolynomial (Fin 3) E) * A ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
      AGN f P.F SZ Q A (qd * scale) (heightH2 B C qd z u v) (qd * u) (qd * v) := by
  intro Q A hden hQ hA W cut hcut points hG hM hreg hzero hiso
  have haux := existsAux_of_certificate P hp T0 B C qd n hT0 hcert
  have hq := hcert.1
  have hn := hcert.2.2.1
  obtain ⟨m, rfl⟩ := hcert.2.1
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left m hq] at haux
  have h := H2Bud.point_budget P SZ t (Chart.surfaceNoether_component P hp)
    (Chart.packet_three_mul_lt P) (Chart.packet_coordinate_ne_zero P hp) (qd * m) (m * B) (m * C) haux
    E f scale z u v hold Q A hden hQ hA W cut hcut points hG hM hreg hzero hiso
  rw [show qd * m * z = m * (qd * z) by ring, show m * B * u + m * C * v = m * (B * u + C * v) by ring,
    Nat.mul_min_mul_left] at h
  refine Nat.le_of_mul_le_mul_left ?_ hm
  calc m * (qd * scale * points.card) = qd * m * scale * points.card := by ring
    _ ≤ _ := h
    _ = m * (W.zOnly * heightH2 B C qd z u v + W.yz * (qd * u) + W.all * (qd * v)) := by
      unfold heightH2
      ring
theorem shared_REH_cost
    (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ SP SQ : MovingFiberThreeSources6811.Source P.F) (hZd : SZ.k < 2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433)
    (hr : 5 ≤ r)
    (T0 B C qd n : ℕ) (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n) :
    Cut.SharedCostAt P hp SZ (Cut.eulerFlag t y r) (Euler.eulerFirst t y r) (qd * stageScale SZ delta)
      (heightH2 B C qd (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag))
      (qd * (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag))
      (qd * (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)) := by
  have hrhi := packet_r_le P
  have hyhi := packet_y_le P
  have hyt := P.yt
  have hthi := packet_t_le P
  have hylo := P.ylow
  obtain ⟨lam, mu, geometry, budget, hframe, -⟩ :=
    exists_packet_frame P hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
  obtain ⟨moving, o, Lam, Kc, hcurve, hlevel, hexch⟩ :=
    counts_h2 P hp SZ hZd (Cut.eulerFlag t y r) (by show 5 ≤ 2 * (r - 2); omega) (Cut.IsHFlag.euler P)
      _ _ _ _ T0 B C qd n hT0 hcert lam mu geometry budget hframe
  have hFchar : P.F.degreeOf 2 < 2130706433 := P.IZ.2.1.trans_lt (by omega : r < 2130706433)
  have hold : ∀ Q U : MvPolynomial (Fin 3) Ext, (2 : MvPolynomial (Fin 3) Ext) * U ≠ 0 →
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag U →
      AGN (algebraMap Ω Ext) P.F SZ Q U (stageScale SZ delta)
        (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
        (SZ.d * flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag) := by
    intro Q U hden hQf hUf
    exact BSF (algebraMap Ω Ext) P.F P.irreducible.ne_zero P.rdegree hFchar
      SP SQ hcop delta hd hP hQ (by omega) SZ hZd ⟨t - y, y - r, r⟩ (P.parent_flag _ _) (by dsimp; omega)
      Q U hden hQf hUf (by omega) (by omega)
  exact Cut.shared_cost_at_of_counts P hp SZ _ _ _ _ _ _ geometry budget hframe.cost
    (Euler.first_cut_packetE P hp SZ (by omega) _ _ _ _ lam mu hframe.lam_mem hframe.mu_mem geometry
      hframe.value (point_budget_h2 P hp SZ _ _ _ _ T0 B C qd n hT0 hcert (algebraMap Ω Ext) hold) _)
    moving o Lam Kc hcurve hlevel hexch
theorem pair_packet_countREH
    (P : Packet x t y r) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F)
    (hFT : SZ.T < wt RCN156.residualTotalWeights P.F) (hZd : SZ.k < 2130706433)
    (hgates : ER.Gates t y r (SZ.B - 2 * SZ.n0) (SZ.U - SZ.n0) (SZ.T - SZ.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hdchar : delta ≤ 2130706433)
    (hP : delta ≤ SP.d) (hQ : delta ≤ SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag < 2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag < 2130706433)
    (hr : 5 ≤ r)
    (T0 B C qd n : ℕ) (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n) :
    P.seeds.card ≤ max (EF.MG t y r)
      (pairStageCostREH SZ SP SQ delta B C qd t y r ⟨t - y, y - r, r⟩ + ER.leadingPrice SZ t y r) :=
  Cut.packet_count_of_regular P SZ hFT hgates _ fun good hsub hp hgood =>
    Cut.packet_count_at (P.restrict good hsub) hp SZ (Cut.eulerFlag t y r) (Nat.le_add_left 1 (y - r))
      _ _ _ _ _ (Nat.mul_pos hcert.1 (Nat.mul_pos (Nat.succ_pos _) hd))
      (shared_REH_cost (P.restrict good hsub) hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu hr
        T0 B C qd n hT0 hcert) hgood
omit [CharP K 2130706433] in
theorem stageCostREH_le {F : MvPolynomial (Fin 4) K} (SZ SP SQ : MovingFiberThreeSources6811.Source F) (delta : ℕ)
    (p q : FlagDegree) (B C qd t y r : ℕ)
    (hp : GF.CumulativeLe (ordinaryFlag SP.P) p) (hq : GF.CumulativeLe (ordinaryFlag SQ.P) q) :
    pairStageCostREH SZ SP SQ delta B C qd t y r ⟨t - y, y - r, r⟩ ≤
      pairCostREH SZ.d SZ.flag delta p q B C qd t y r := by
  unfold pairStageCostREH stageScale pairCostREH
  apply Nat.div_le_div_right
  have hu := GF.CAB _ _ _ _ unitYZFlag hp hq
  have hv := GF.CAB _ _ _ _ unitAllFlag hp hq
  have hH := heightH2_mono B C qd (delta * flagMixed ⟨t - y, y - r, r⟩ unitZFlag SZ.flag)
    (Nat.mul_le_mul_left SZ.d hu) (Nat.mul_le_mul_left SZ.d hv)
  simp only [Cut.numeratorRE, Cut.priceNumerator, price]
  gcongr
theorem pair_leaf_countREH
    (P : Packet x t y r) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F)
    (hFT : SZ.T < wt RCN156.residualTotalWeights P.F) (hk : SZ.k < 2130706433)
    (hg : ER.Gates t y r (SZ.B - 2 * SZ.n0) (SZ.U - SZ.n0) (SZ.T - SZ.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hchar : delta ≤ 2130706433)
    (hSP : delta ≤ SP.d) (hSQ : delta ≤ SQ.d)
    (p q : FlagDegree) (hp : GF.CumulativeLe (ordinaryFlag SP.P) p)
    (hq : GF.CumulativeLe (ordinaryFlag SQ.P) q)
    (hz : flagMixed p q unitZFlag < 2130706433)
    (hu : flagMixed p q unitYZFlag < 2130706433)
    (hr : 5 ≤ r)
    (T0 B C qd n : ℕ) (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n) :
    P.seeds.card ≤ max (EF.MG t y r)
      (pairCostREH SZ.d SZ.flag delta p q B C qd t y r + ER.leadingPrice SZ t y r) :=
  (pair_packet_countREH P SZ SP SQ hFT hk hg hcop delta hd hchar hSP hSQ
    ((GF.CAB _ _ _ _ unitZFlag hp hq).trans_lt hz) ((GF.CAB _ _ _ _ unitYZFlag hp hq).trans_lt hu)
    hr T0 B C qd n hT0 hcert).trans
    (max_le_max le_rfl
      (Nat.add_le_add_right (stageCostREH_le SZ SP SQ delta p q B C qd t y r hp hq) _))
end
end Price
end H2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart5
namespace ON
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open BD GZ DC
open MovingFiberThreeSources6811 (direction weight)
open LK CB FN
open NX
open RCN234 RCN156
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
variable {K:Type} [Field K] [CharP K 2130706433]
def multiplicity (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J:SecondJetSupport.Poly (K:=K)):ℕ:=
  ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)
theorem DDZ (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (J:SecondJetSupport.Poly (K:=K)) (m s b u t k n0:ℕ)
    (hkm:k+1≤m) (hkn:k+1≤n0) (hn:n0≤J.degreeOf 1) (hs:J.degreeOf 1≤s)
    (h2n:2*n0≤b) (hbu:b≤u) (hut:u≤t)
    (hshape: ∀e∈J.support,2*e 1+e 3≤b∧e 1+e 2+e 3≤u∧e 1+e 2+e 3+e 4≤t)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=m):
    ∃S:MovingFiberThreeSources6811.Source F,S.P=J∧Profile S b u t s k n0:=by
  have hS: ∀e∈J.support,e 1≤s:=MvPolynomial.degreeOf_le_iff.mp hs
  have hH:=ALO F hpos hchar
  let source:MovingFiberThreeSources6811.Source F:={
    P:=J,B:=b,U:=u,T:=t,s:=s,k:=k,n0:=n0
    hS:=hS,hshape:=hshape,hBU:=hbu,hUT:=hut,hdn:=hkn,hB:=by omega
    hn:=by simpa only [ABW] using hn
    hdiv:=by
      intro d hd
      apply (TY F _).mp
      rw [SecondJetCarrierDichotomy.mapped_helper J F (carrierMap F) s d hS hH]
      have hz:((Polynomial.derivative)^[d] ((SecondJetCoefficients.asS J).map (carrierMap F))).eval (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0:=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot];omega)
      rw [hz,mul_zero]}
  exact ⟨source,rfl,by repeat' constructor⟩
end
end ON
end MergedPart5
section MergedPart6
namespace YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 25000
open MvPolynomial CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open BD GZ DC
open MovingFiberThreeSources6811 (direction weight)
open LK FN CB
open RCN234 RCN156
open SecondJetCoefficients (liftExponent)
variable {K:Type} [Field K] [CharP K 2130706433]
theorem AVL (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S:MovingFiberThreeSources6811.Source F) (hFT:S.T<wt RCN156.residualTotalWeights F)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (hJS:J∣S.P)
    (hroot:NT (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J=0):
    (SecondJetCoefficients.asS J).map (carrierMap F)≠0∧
    0<ON.multiplicity F J∧ON.multiplicity F J≤order J∧
    slope J≤S.B∧middle J≤S.U∧total J≤S.T∧order J≤S.s:=by
  have hP:=AHY F S
  have hne:=AKB F S.P hP S.T (fun e he=>(S.hshape e he).2.2) hFT
  have hJne:QC (carrierMap F) J≠0:=by
    intro hz
    have hd:=map_dvd (QC (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hne hd
  have hm:0<ON.multiplicity F J:=(Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms:ON.multiplicity F J≤order J:=by
    have hh:=Polynomial.natDegree_le_of_dvd
      ((QC (carrierMap F) J).pow_rootMultiplicity_dvd (SecondJetCarrierDichotomy.ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (ABW J))
  obtain ⟨Q,hEq⟩:=hJS
  have hQ:Q≠0:=by intro hz;exact hP (by rw [hEq,hz,mul_zero])
  obtain ⟨hb,hu,ht,hs⟩:=AZX.source_caps F S
  rw [hEq,weight_mul _ _ _ hJ.ne_zero hQ] at hb hu ht
  rw [hEq,degreeOf_mul_eq hJ.ne_zero hQ] at hs
  refine ⟨hJne,hm,hms,?_,?_,?_,?_⟩
  all_goals
    dsimp only [CB.slope,middle,total,order]
    omega
end
end YY
end MergedPart6
section MergedPart7
namespace BMA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334
open RCN222 renaming GeometricFactor → EX
open DU EF ER
open MI DC BHE
open GF WW
open AIA CUT BTA
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
def linearPrice (first delay:FlagDegree) (t y r b u l:ℕ):ℕ:=
  r*GB.FU (pair t y r b u l)+
    flagMixed ⟨t-y,y-r,r⟩ first delay+
    81107*flagMixed ⟨t-y,y-r,r⟩ first unitYZFlag+
    flagMixed ⟨t-y,y-r,r⟩ first unitAllFlag
theorem packet_count
    (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:SecondJetSupport.Poly (K:=K)) (first delay:FlagDegree)
    (hroute:Route P.F J first delay) (b u l:ℕ)
    (hH:wt RCN156.residualSWeights (linearH J)≤b∧wt RCN156.residualYSWeights (linearH J)≤u∧
      wt RCN156.residualTotalWeights (linearH J)≤l)
    (hgates:Gates t y r b u l)
    (hsmall:flagMixed ⟨t-y,y-r,r⟩ first unitZFlag<2130706433):
    P.seeds.card≤max (MG t y r) (linearPrice first delay t y r b u l):=by
  by_cases hp:P.F∣numerator K P.F (RCN326.w+1)
  · exact (CNE P hp).trans (le_max_left _ _)
  let cap:=GB.FU (pair t y r b u l)
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval
    (DK (RCN135.polynomialEmbedding K) P.selected gamma)
    (surfaceMap (RCN135.polynomialEmbedding K) (linearH J))=0)
  let PB:=P.restrict bad (Finset.filter_subset _ _)
  have hrel:IsRelPrime P.F (linearH J):=P.irreducible.isRelPrime_iff_not_dvd.mpr
    (fun hd=>hroute.denominator ((TY P.F _).mpr hd))
  have hbad:bad.card≤cap:=by
    apply DHG PB (linearH J) b u l hrel hH hgates
    intro gamma hg
    have hh:=(Finset.mem_filter.mp hg).2
    rw [RCN170.XH] at hh
    change RCN319.specialization K (P.selected gamma) gamma (linearH J)=0
    exact RCN135.polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  have hb:=VD P.F P.irreducible.ne_zero
  have hc:=RCN130.originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hry:r≤y:=by have:=P.ylow;omega
  have hyt:=P.yt
  have hsum (W:FlagDegree):(∑ g:RCN222.GeometricFactor K P.F,
      flagMixed (CO K g) first W)≤flagMixed ⟨t-y,y-r,r⟩ first W:=by
    apply RCN084.sum_flagMixed_le_of_cumulative
    · exact hb.1.trans P.r_weight
    · simpa only [Nat.sub_add_cancel hry] using hb.2.1.trans P.y_weight
    · have ht:=hb.2.2.trans P.total_weight
      exact ht.trans_eq (by change t=(t-y)+(y-r)+r;omega)
  have hcard:Fintype.card (RCN222.GeometricFactor K P.F)≤r:=by
    have hone (g:RCN222.GeometricFactor K P.F):1≤(CO K g).all:=by
      have hd:=(P.stage g).y_dependent
      have hle:(P.stage g).G.degreeOf 1≤(CO K g).all:=
        MvPolynomial.degreeOf_le_iff.mpr (fun e he=>((P.stage g).flag_support e he).1)
      omega
    have hh:=(Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hone g)).trans (hb.1.trans P.r_weight)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hh
  let cost (fl:FlagDegree):=flagMixed fl first delay+
    (flagMixed fl first unitYZFlag+flagMixed fl first unitAllFlag)+81106*flagMixed fl first unitYZFlag
  have hsingle (g:RCN222.GeometricFactor K P.F):
      (KK K P.F P.selected P.seeds g).card≤cap+cost (CO K g):=by
    let S:=P.stage g
    letI:Fact (Irreducible S.F):=⟨P.irreducible⟩
    have hfirst:=P.stage_proper hp g
    have hsmall' :flagMixed (CO K g) first unitZFlag<2130706433:=
      (ELU _ ⟨t-y,y-r,r⟩ first unitZFlag (by
        have h:=P.stage_flag g
        change _≤r∧_≤y-r+r∧_≤t-y+(y-r)+r
        omega)).trans_lt hsmall
    have hproper:=FLD S J hroute
    have hden:(BPG S J).card≤cap:=by
      apply (Finset.card_le_card (show BPG S J⊆bad from ?_)).trans hbad
      intro gamma hg
      exact Finset.mem_filter.mpr
        ⟨WK K P.F P.selected P.seeds g (Finset.mem_filter.mp hg).1,
          (Finset.mem_filter.mp hg).2⟩
    have hd:=ENS S hfirst J hroute (CO K g) S.flag_support hsmall'
    have hz:=EJI S hfirst J hroute hproper (CO K g) S.flag_support
    have ht:=EEB S hfirst J hroute hproper (CO K g)
      S.flag_support hsmall' 181039 P.D t r P.nodeCount (P.CVV g) (by decide) P.Dlow P.Dchar P.box
    have hh:=(FPI S hfirst J).trans (Nat.add_le_add hden (Nat.add_le_add hd (Nat.add_le_add hz ht)))
    exact hh.trans_eq (by dsimp only [cost];ring)
  have hcost:(∑ g:RCN222.GeometricFactor K P.F,cost (CO K g))≤cost ⟨t-y,y-r,r⟩:=by
    unfold cost
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add (hsum delay) (Nat.add_le_add (hsum unitYZFlag) (hsum unitAllFlag)))
      (Nat.mul_le_mul_left 81106 (hsum unitYZFlag))
  have htotal:P.seeds.card≤r*cap+cost ⟨t-y,y-r,r⟩:=by
    have hh:=P.seeds_cover.trans (Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hsingle g))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
    exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hcard) hcost)
  apply (htotal.trans_eq ?_).trans (le_max_right _ _)
  dsimp [linearPrice,cap,cost]
  ring
end
end BMA
end MergedPart7
section MergedPart8
namespace AOR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW MI NA
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open ANU AIA BMA
open DU ER EF
open DC
open SecondJetCoefficients (liftExponent)
variable {K:Type} [Field K]
theorem tail_weights (J:SecondJetSupport.Poly (K:=K)) (B U L:ℕ) (hB:2≤B) (hBU:B≤U) (hUL:U≤L)
    (hshape: ∀e∈J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤L)
    (n:ℕ):
    wt RCN156.residualSWeights (numerators (linearH J) (linearG J) n)≤(2*B-3)*n∧
    wt RCN156.residualYSWeights (numerators (linearH J) (linearG J) n)≤1+(2*U-2)*n∧
    wt RCN156.residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+(2*L-2)*n:=by
  have hh:=CQC J B U L hshape
  have hR:=EAZ RCN156.residualSWeights (linearH J) (linearG J) (B-2) (B-1)
    hh.1.1 (by change _≤B-1+1;omega) (by change B-2≤B-1+0;omega)
    (by change 1+(B-2)≤B-1+0;omega) n
  have hY:=EAZ RCN156.residualYSWeights (linearH J) (linearG J) (U-1) (U-1)
    hh.1.2.1 (by change _≤U-1+1;omega) (by change U-1≤U-1+0;omega)
    (by change 1+(U-1)≤U-1+1;omega) n
  have hT:=EAZ RCN156.residualTotalWeights (linearH J) (linearG J) (L-1) (L-1)
    hh.1.2.2 (by change _≤L-1+1;omega) (by change L-1≤L-1+0;omega)
    (by change 1+(L-1)≤L-1+1;omega) n
  have hr:(B-2)+(B-1)=2*B-3:=by omega
  have hy:(U-1)+(U-1)=2*U-2:=by omega
  have ht:(L-1)+(L-1)=2*L-2:=by omega
  exact ⟨by simpa only [show RCN156.residualSWeights 1=0 from rfl,zero_add,hr,Nat.mul_comm] using hR,
    by simpa only [show RCN156.residualYSWeights 1=1 from rfl,hy,Nat.mul_comm] using hY,
    by simpa only [show RCN156.residualTotalWeights 1=1 from rfl,ht,Nat.mul_comm] using hT⟩
variable [CharP K 2130706433] {I:Type} {x:I→K} {t y r:ℕ}
theorem BNL
    (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:SecondJetSupport.Poly (K:=K)) (hJ:J≠0) (hs:J.degreeOf 1=1)
    (B U L:ℕ) (hB:2≤B) (hBU:B≤U) (hUL:U≤L)
    (hshape: ∀e∈J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤L)
    (hFT:L<wt RCN156.residualTotalWeights P.F)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).eval (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=0)
    (hgates:Gates t y r (B-2) (U-1) (L-1))
    (hsmall:flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433):
    P.seeds.card≤max (MG t y r)
      (linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
        (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)):=by
  have hchar:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega:r<2130706433)
  have route:=GCI P.F J hJ hs P.rdegree hchar L
    (fun e he=>(hshape e he).2.2) hFT hroot (2*B-3) (2*U-2) (2*L-2)
    (by omega) (by omega) (tail_weights J B U L hB hBU hUL hshape)
  exact packet_count P J _ _ route (B-2) (U-1) (L-1)
    (CQC J B U L hshape).1 hgates hsmall
end
end AOR
end MergedPart8
section MergedPart9
namespace AJR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open DU ER
open GF CB
open FF
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
theorem helper_count {t y r:ℕ} (p:Parameters) (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) (Q:MvPolynomial (Fin 4) K)
    (hh:ProperHelper p P.F Q r y t nodes P.u0 P.u1)
    (hg:Gates t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))):
    P.seeds.card≤GB.FU
      (pair t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))):=by
  classical
  apply DHG P Q _ _ _ hh.1 hh.2.1 hg
  intro gamma hgamma
  exact hh.2.2 (P.selected gamma) (P.degree gamma hgamma) gamma
    (P.nodes.filter (fun i=>(P.selected gamma).eval (nodes i)=P.u0 i+gamma*P.u1 i))
    (P.agreement gamma hgamma)
    (fun i hi=>by simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
    (P.solution gamma hgamma)
end
end AJR
end MergedPart9
section MergedPart10
namespace HI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped BigOperators
open RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open BD CB
open MovingFiberThreeSources6811 (direction weight)
open DU ER EF
open TW RL
open GF
structure Degrees where
  B:ℕ
  U:ℕ
  T:ℕ
  k:ℕ
  n0:ℕ
  deriving DecidableEq
def Degrees.d (z:Degrees):=z.k+1
def Degrees.flag (z:Degrees):=SecondJetRelaxedFlag.budgetFlag z.B z.U z.T z.d z.n0
def leading (z:Degrees) (t y r:ℕ):ℕ:=
  GB.FU (pair t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
def pairCost (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r:ℕ):ℕ:=
  FormalR.Cut.pairCostRE z.d z.flag delta p q t y r
variable {K I:Type} [Field K] [CharP K 2130706433]
variable {F:MvPolynomial (Fin 4) K}
def Fits (S:MovingFiberThreeSources6811.Source F) (z:Degrees):Prop:=
  S.B=z.B∧S.U=z.U∧S.T=z.T∧S.k=z.k∧S.n0=z.n0
theorem fits_degree (S:MovingFiberThreeSources6811.Source F) (z:Degrees) (h:Fits S z):S.d=z.d:=by
  simp only [MovingFiberThreeSources6811.Source.d,Degrees.d,h.2.2.2.1]
theorem fits_flag (S:MovingFiberThreeSources6811.Source F) (z:Degrees) (h:Fits S z):S.flag=z.flag:=by
  simp only [MovingFiberThreeSources6811.Source.flag,Degrees.flag,h.1,h.2.1,h.2.2.1,h.2.2.2.2,fits_degree S z h]
theorem fits_leading (S:MovingFiberThreeSources6811.Source F) (z:Degrees) (h:Fits S z) (t y r:ℕ):
    leadingPrice S t y r=leading z t y r:=by
  simp only [leadingPrice,leading,h.1,h.2.1,h.2.2.1,h.2.2.2.2]
variable {x:I→K} {t y r:ℕ}
theorem AHM
    (P:Packet x t y r) (SZ SP SQ:MovingFiberThreeSources6811.Source P.F)
    (z:Degrees) (hZ:Fits SZ z) (hFT:z.T<wt RCN156.residualTotalWeights P.F)
    (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta) (hchar:delta≤2130706433)
    (hSP:delta≤SP.d) (hSQ:delta≤SQ.d)
    (p q:FlagDegree) (hp:CumulativeLe (ordinaryFlag SP.P) p)
    (hq:CumulativeLe (ordinaryFlag SQ.P) q)
    (hz:flagMixed p q unitZFlag<2130706433)
    (hu:flagMixed p q unitYZFlag<2130706433) (hr:5≤r):
    P.seeds.card≤max (MG t y r) (pairCost z delta p q t y r+leading z t y r):=by
  have hg' :Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0):=by
    simpa only [hZ.1,hZ.2.1,hZ.2.2.1,hZ.2.2.2.2] using hg
  have hc:=FormalR.Cut.pair_leaf_countRE P SZ SP SQ (by simpa only [hZ.2.2.1] using hFT)
    (by simpa only [hZ.2.2.2.1] using hk) hg' hcop delta hd hchar hSP hSQ p q hp hq hz hu hr
  rw [fits_degree SZ z hZ,fits_flag SZ z hZ,fits_leading SZ z hZ t y r] at hc
  exact hc
def nativeScalar (z:Degrees) (t y r:ℕ):ℕ:=
  FormalR.Cut.nativeRE z.d z.flag t y r
theorem GEE (S:MovingFiberThreeSources6811.Source F) (z:Degrees) (h:Fits S z) (t y r:ℕ):
    FormalR.Cut.nativeRE S.d S.flag t y r=nativeScalar z t y r:=by
  simp only [nativeScalar,fits_degree S z h,fits_flag S z h]
theorem BVF
    (P:Packet x t y r) (S:MovingFiberThreeSources6811.Source P.F) (z:Degrees) (h:Fits S z)
    (hFT:z.T<wt RCN156.residualTotalWeights P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)) (hr:5≤r):
    P.seeds.card≤max (MG t y r) (nativeScalar z t y r/(9*z.d*z.d)+leading z t y r):=by
  have hg' :Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0):=by
    simpa only [h.1,h.2.1,h.2.2.1,h.2.2.2.2] using hg
  have hc:=FormalR.Cut.native_leaf_countRE P S (by simpa only [h.2.2.2.1] using hk)
    (by simpa only [h.2.2.1] using hFT) hg' hr
  rw [GEE S z h t y r,fits_degree S z h,fits_leading S z h t y r] at hc
  exact hc
end
end HI
end MergedPart10
section MergedPart13
namespace KY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN260 RCN294 RCN234 RCN156
open ER DU FF
theorem count_mono (t y r b u l capT capY capR capB capU capL:ℕ)
    (ht:t≤capT) (hy:y≤capY) (hr:r≤capR) (hb:b≤capB) (hu:u≤capU) (hl:l≤capL):
    GB.FU (pair t y r b u l)≤
      GB.FU (pair capT capY capR capB capU capL):=by
  unfold GB.FU
  apply Nat.div_le_div_right
  simp only [GB.KP,pair,DG.errors,
    DG.gap,DG.KO,DG.mixedCost,dot]
  gcongr
theorem gates_mono (t y r b u l capT capY capR capB capU capL:ℕ)
    (ht:t≤capT) (hy:y≤capY) (hr:r≤capR) (hb:b≤capB) (hu:u≤capU) (hl:l≤capL)
    (h:Gates capT capY capR capB capU capL):Gates t y r b u l:=by
  rcases h with ⟨hY,hR,hZ⟩
  unfold Gates pair DG.mixedCost at*
  constructor
  · apply lt_of_le_of_lt _ hY
    dsimp only
    gcongr
  constructor
  · apply lt_of_le_of_lt _ hR
    dsimp only
    gcongr
  · apply lt_of_le_of_lt _ hZ
    dsimp only
    gcongr
theorem DZN:Gates 9352 76 18 1344 5312 602560∧
    GB.FU (pair 9352 76 18 1344 5312 602560)<4000000000000000:=by
  unfold Gates
  decide+kernel
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x:I→K} {t y r:ℕ}
theorem ESM (p:Parameters) (P:Packet x t y r)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64):
    p.B+p.s*(r-1)≤1344∧p.U+p.s*(y-1)≤5312∧p.L+p.s*(t-1)≤602560:=by
  have hr:=P.rhigh
  have hy:=P.yhigh
  have ht:=P.thigh
  have hrr:p.s*(r-1)≤64*17:=Nat.mul_le_mul hs (by omega)
  have hyy:p.s*(y-1)≤64*75:=Nat.mul_le_mul hs (by omega)
  have htt:p.s*(t-1)≤64*9351:=Nat.mul_le_mul hs (by omega)
  omega
theorem helper_count (p:Parameters) (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64)
    (Q:MvPolynomial (Fin 4) K) (hQ:ProperHelper p P.F Q r y t nodes P.u0 P.u1):
    P.seeds.card<4000000000000000:=by
  obtain ⟨hr,hy,ht⟩:=ESM p P hb hu hl hs
  have hg:=gates_mono t y r _ _ _ 9352 76 18 1344 5312 602560
    P.thigh P.yhigh P.rhigh hr hy ht DZN.1
  exact (AJR.helper_count p nodes P Q hQ hg).trans_lt
    ((count_mono t y r _ _ _ 9352 76 18 1344 5312 602560
      P.thigh P.yhigh P.rhigh hr hy ht).trans_lt DZN.2)
end
end KY
end MergedPart13
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace H2
section Degrees
noncomputable section
open scoped Classical BigOperators
open RCN095 RCN135 RCN156 RCN234 RCN313
open RCN095 renaming PolynomialInFlag → BI
open BD DU CB HI
open MovingFiberThreeSources6811 (direction weight)
def pairCostEH (z : Degrees) (delta : ℕ) (p q : FlagDegree) (B C qd t y r : ℕ) : ℕ :=
  pairCostREH z.d z.flag delta p q B C qd t y r
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
theorem pair_count_of_degreesEH
    (P : Packet x t y r) (SZ SP SQ : MovingFiberThreeSources6811.Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hFT : z.T < wt RCN156.residualTotalWeights P.F) (hk : z.k < 2130706433)
    (hg : ER.Gates t y r (z.B - 2 * z.n0) (z.U - z.n0) (z.T - z.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0 < delta) (hchar : delta ≤ 2130706433)
    (hSP : delta ≤ SP.d) (hSQ : delta ≤ SQ.d)
    (p q : FlagDegree) (hp : GF.CumulativeLe (ordinaryFlag SP.P) p)
    (hq : GF.CumulativeLe (ordinaryFlag SQ.P) q)
    (hz : flagMixed p q unitZFlag < 2130706433)
    (hu : flagMixed p q unitYZFlag < 2130706433) (hr : 5 ≤ r)
    (T0 B C qd n : ℕ) (hT0 : T0 ≤ wt RCN156.residualTotalWeights P.F) (hcert : Certificate r y T0 B C qd n) :
    P.seeds.card ≤ max (EF.MG t y r) (pairCostEH z delta p q B C qd t y r + leading z t y r) := by
  have hg' : ER.Gates t y r (SZ.B - 2 * SZ.n0) (SZ.U - SZ.n0) (SZ.T - SZ.n0) := by
    simpa only [hZ.1, hZ.2.1, hZ.2.2.1, hZ.2.2.2.2] using hg
  have hc := pair_leaf_countREH P SZ SP SQ (by simpa only [hZ.2.2.1] using hFT)
    (by simpa only [hZ.2.2.2.1] using hk) hg' hcop delta hd hchar hSP hSQ p q hp hq hz hu hr
    T0 B C qd n hT0 hcert
  rw [fits_degree SZ z hZ, fits_flag SZ z hZ, fits_leading SZ z hZ t y r] at hc
  exact hc
end
end Degrees
end H2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart2
namespace BGT
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open RCN095 RCN135 RCN136 RCN156 RCN234
open RCN095 renaming PolynomialInFlag → BI
open CW DJ
open Koala6831Ordinary (totalWeights)
open SecondJetSupport (Poly)
open FF ZGL HI
open CB BD
open MovingFiberThreeSources6811 (direction weight)
open DU ER EF
open DC FN
open SecondJetCoefficients (liftExponent)
def active (p:Parameters) (m s b u e:ℕ):Prop:=
  e*b≤p.B∧e*u≤p.U∧e*s≤p.s∧p.k+1-e*m≤p.s-e*s
def box (p:Parameters) (m s b u lo:ℕ):DA.OwnerBox:=
  ⟨(p.k+1+m-1)/m,b,b,s,u,lo⟩
end
end BGT
end MergedPart2
section MergedPart3
namespace CQG
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 50000
open FF HI BGT
instance (p:Parameters) (m s b u e:ℕ):Decidable (active p m s b u e):=by
  unfold active
  infer_instance
def GoodPower (i:Fin 2) (m s b u lo:ℕ):Prop:=
  let p:=CN.profile i
  (DA.Impossible (ZGL.caps p) (box p m s b u lo)∧
    0<CN.kernel i)∨
  ZGL.strongCount p (box p m s b u lo)<
    CN.kernel i
instance (i:Fin 2) (m s b u lo:ℕ):Decidable (GoodPower i m s b u lo):=by
  unfold GoodPower DA.Impossible
  infer_instance
end CQG
end MergedPart3
end SubmissionLower
end ProximityPrize
end
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
def flag (B U T S:ℕ):FlagDegree:=
  let M:=max B (U+S)
  ⟨max M (T+S)-M,M-B,B⟩
def ownerFlag (a:Box):=flag a.bhi a.uhi a.thi a.shi
def AFD (a:Box):FlagDegree:=
  let p:=ownerFlag a
  ⟨p.zOnly,p.yz,p.all-2⟩
def ownerZ (a:Box) (m:ℕ):Degrees:=
  ⟨a.bhi,max a.bhi a.uhi,max (max a.bhi a.uhi) a.thi,m-1,a.slo⟩
def point {K:Type} [Field K] (J:SecondJetSupport.Poly (K:=K)):Point:=
  ⟨order J,slope J,middle J,total J⟩
def powerBox (p:Parameters) (a:Box) (m:ℕ):DA.OwnerBox:=
  ⟨(p.k+1+m-1)/m,a.blo,a.bhi,a.slo,a.ulo,a.tlo⟩
def cofactorFlag (p:Parameters) (a:Box) (e:ℕ):=
  flag (p.B-e*a.blo) (p.U-e*a.ulo) (p.L-e*a.tlo) (p.s-e*a.slo)
def active (p:Parameters) (a:Box) (m e:ℕ):Prop:=
  e*a.blo≤p.B∧e*a.ulo≤p.U∧e*a.tlo≤p.L∧e*a.slo≤p.s∧p.k+1-e*m≤p.s-e*a.slo
def GoodPower (i:Fin 2) (a:Box) (m:ℕ):Prop:=
  let p:=CN.profile i
  (DA.Impossible (caps p) (powerBox p a m)∧
    0<CN.kernel i)∨
  strongCount p (powerBox p a m)<CN.kernel i
variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}
theorem FBA (J:SecondJetSupport.Poly (K:=K)) (B U T S:ℕ)
    (hb:slope J≤B) (hu:middle J≤U) (ht:total J≤T) (hs:order J≤S):
    CumulativeLe (ordinaryFlag J) (flag B U T S):=by
  have h:=RJ J
  dsimp only [flag]
  change _≤B∧_≤max B (U+S)-B+B∧
    _≤max (max B (U+S)) (T+S)-max B (U+S)+(max B (U+S)-B)+B
  omega
theorem _Q23 (J:SecondJetSupport.Poly (K:=K)) (a:Box) (h:Contains a (point J)):
    CumulativeLe (ordinaryFlag J) (ownerFlag a):=by
  exact FBA J a.bhi a.uhi a.thi a.shi h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.1
theorem DEA (J:SecondJetSupport.Poly (K:=K)) (a:Box) (h:Contains a (point J))
    (hs:2≤order J):CumulativeLe (ordinaryFlag (pderiv 1 J)) (AFD a):=by
  have hdB:=LL.AWV J slopeWeights
  have hdU:=LL.AWV J HA
  have hdT:=LL.AWV J Koala6831Ordinary.totalWeights
  have hdS:=LL.pderiv_order J
  change slope (pderiv 1 J)≤slope J-2 at hdB
  change middle (pderiv 1 J)≤middle J-1 at hdU
  change total (pderiv 1 J)≤total J-1 at hdT
  change order (pderiv 1 J)≤order J-1 at hdS
  have hn:=_Q15 J
  have hd:=RJ (pderiv 1 J)
  dsimp only [Contains,point] at h
  dsimp only [CumulativeLe,AFD,ownerFlag,flag]
  omega
theorem owner_source (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:SecondJetSupport.Poly (K:=K)) (a:Box) (m:ℕ) (hm:0<m)
    (h:Contains a (point J)) (hms:m≤a.slo) (h2:2*a.slo≤a.bhi)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m):
    ∃S:MovingFiberThreeSources6811.Source P.F,Fits S (ownerZ a m):=by
  have hshape: ∀e∈J.support,2*e 1+e 3≤a.bhi∧
      e 1+e 2+e 3≤max a.bhi a.uhi∧e 1+e 2+e 3+e 4≤max (max a.bhi a.uhi) a.thi:=by
    intro e he
    have h1:=(le_weightedTotalDegree slopeWeights he).trans h.2.2.2.1
    have h2:=(le_weightedTotalDegree HA he).trans h.2.2.2.2.2.1
    have h3:=(le_weightedTotalDegree Koala6831Ordinary.totalWeights he).trans h.2.2.2.2.2.2.2
    simp [JW,slopeWeights,HA,Koala6831Ordinary.totalWeights] at h1 h2 h3
    exact ⟨by simpa only [Nat.mul_comm] using h1,h2.trans (le_max_right _ _),h3.trans (le_max_right _ _)⟩
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  obtain ⟨S,_,hp⟩:=ON.DDZ P.F P.rdegree hchar J m a.shi
    a.bhi (max a.bhi a.uhi) (max (max a.bhi a.uhi) a.thi) (m-1) a.slo
    (by omega) (by omega) h.1 h.2.1 h2 (le_max_left _ _) (le_max_left _ _) hshape hroot
  exact ⟨S,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2⟩
theorem GBB (P:Packet x t y r) [Fact (Irreducible P.F)]
    (SZ:MovingFiberThreeSources6811.Source P.F) (z:Degrees) (hZ:Fits SZ z)
    (hZFT:z.T<wt RCN156.residualTotalWeights P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hFT:1700<wt RCN156.residualTotalWeights P.F)
    (J:SecondJetSupport.Poly (K:=K)) (hJ:Irreducible J) (a:Box) (m cap:ℕ)
    (h:Contains a (point J)) (hm:2≤m) (hms:m≤order J)
    (hsmall:a.thi≤1700) (hsChar:a.shi<2130706433)
    (hroot:((SecondJetCoefficients.asS J).map (carrierMap P.F)).rootMultiplicity (SecondJetCarrierDichotomy.ratio (carrierMap P.F) P.F)=m)
    (hcg:flagMixed (ownerFlag a) (AFD a) unitZFlag<2130706433∧
      flagMixed (ownerFlag a) (AFD a) unitYZFlag<2130706433)
    (hfit:pairCost z (m-1) (ownerFlag a) (AFD a) t y r+leading z t y r≤cap):
    P.seeds.card≤max (MG t y r) cap:=by
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  obtain ⟨SJ,SQ,hSJ,hSQ,hcop,hJd,hQd,_⟩:=LL.AWG
    P.F hFT P.rdegree hchar J hJ (h.2.2.2.2.2.2.2.trans hsmall)
    (by rw [ABW];change 0<order J;omega)
    (by rw [ABW];exact h.2.1.trans_lt hsChar) m hm hroot
  have hp:=_Q23 J a h
  have hq:=DEA J a h (by omega)
  rw [←hSJ] at hp
  rw [←hSQ] at hq
  have hms' :m<2130706433:=hms.trans_lt (h.2.1.trans_lt hsChar)
  exact (AHM P SZ SJ SQ z hZ hZFT hk hg hcop (m-1) (by omega)
    (by omega) (by omega) hQd _ _ hp hq hcg.1 hcg.2 P.rlow).trans (max_le_max le_rfl hfit)
end
end LV
end MergedPart1
end SubmissionLower
end ProximityPrize
end
