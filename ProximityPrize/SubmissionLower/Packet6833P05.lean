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
import ProximityPrize.SubmissionLower.Packet6833P04
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial HFree6812
section Residue
variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Valuation L ℤᵐ⁰)
variable (hk : ∀ a : k, a ≠ 0 → w (algebraMap k L a) = 1)
include hk
theorem algebraMap_le_one_of_trivial (a : k) : w (algebraMap k L a) ≤ 1 := by
  by_cases h0 : a = 0
  · rw [h0, map_zero, w.map_zero]; exact zero_le
  · exact (hk a h0).le
theorem resAlg_algebraMap (a : k) : ResAlg k w (algebraMap k L a) :=
  ⟨algebraMap_le_one_of_trivial w hk a, Polynomial.X - Polynomial.C a, Polynomial.monic_X_sub_C a, by simp⟩
theorem resAlg_adjoin (S : Set L) (hS : ∀ s ∈ S, ResAlg k w s) :
    ∀ x ∈ Algebra.adjoin k S, ResAlg k w x := by
  obtain ⟨hadd, hmul, -, -⟩ := resAlg_closure w (algebraMap_le_one_of_trivial w hk)
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap a => exact resAlg_algebraMap w hk a
  | add x y _ _ hx hy => exact hadd x y hx hy
  | mul x y _ _ hx hy => exact hmul x y hx hy
theorem resAlg_zpow (x : L) (hx : ResAlg k w x) (n : ℤ) (hn : 0 ≤ n ∨ w x = 1) :
    ResAlg k w (x ^ n) := by
  obtain ⟨-, hmul, hinv, -⟩ := resAlg_closure w (algebraMap_le_one_of_trivial w hk)
  have hpow : ∀ (y : L), ResAlg k w y → ∀ m : ℕ, ResAlg k w (y ^ m) := by
    intro y hy m
    induction m with
    | zero => rw [pow_zero, ← map_one (algebraMap k L)]; exact resAlg_algebraMap w hk 1
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih hy
  by_cases h0 : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [zpow_natCast]; exact hpow x hx m
  · have h1 : w x = 1 := hn.resolve_left h0
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hpow _ (hinv x hx h1) m
theorem resAlg_lmono (x : Fin 3 → L) (a : Fin 3 → ℤ)
    (h : ∀ j, ResAlg k w (x j) ∧ (0 ≤ a j ∨ w (x j) = 1)) : ResAlg k w (lmono x a) := by
  obtain ⟨-, hmul, -, -⟩ := resAlg_closure w (algebraMap_le_one_of_trivial w hk)
  exact hmul _ _ (hmul _ _ (resAlg_zpow w hk _ (h 0).1 _ (h 0).2)
    (resAlg_zpow w hk _ (h 1).1 _ (h 1).2)) (resAlg_zpow w hk _ (h 2).1 _ (h 2).2)
omit hk in
theorem not_resAlg_of_trivial (x : L)
    (h : ∀ p : Polynomial k, p ≠ 0 → w (Polynomial.aeval x p) = 1) : ¬ ResAlg k w x := by
  rintro ⟨-, p, hp, hlt⟩
  rw [h p hp.ne_zero] at hlt
  exact lt_irrefl _ hlt
theorem trivial_of_not_resAlg (x : L) (hx : w x ≤ 1) (h : ¬ ResAlg k w x) :
    ∀ p : Polynomial k, p ≠ 0 → w (Polynomial.aeval x p) = 1 := by
  obtain ⟨-, -, -, hle⟩ := resAlg_closure w (algebraMap_le_one_of_trivial w hk)
  intro p hp
  have hmon := Polynomial.monic_mul_leadingCoeff_inv hp
  have h1 : w (Polynomial.aeval x (p * Polynomial.C p.leadingCoeff⁻¹)) = 1 :=
    le_antisymm (hle x hx _) (not_lt.1 fun hlt => h ⟨hx, _, hmon, hlt⟩)
  rwa [map_mul, map_mul, Polynomial.aeval_C,
    hk _ (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hp)), mul_one] at h1
end Residue
theorem optionElim_comp_finSucc {A : Type*} {n : ℕ} (a : A) (x : Fin n → A) :
    (Fin.cons a x : Fin (n + 1) → A) ∘ (finSuccEquiv n).symm = fun o : Option (Fin n) => o.elim a x := by
  funext o
  rcases o with _ | j
  · rfl
  · simp
section Slice
variable {K : Type} [Field K] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
theorem xField_le_unitField (t : SliceField F₀) : xField F₀ ≤ unitField F₀ t :=
  IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))
theorem xField_trivial (w : Valuation (SliceField F₀) ℤᵐ⁰) (t : SliceField F₀)
    (htv : ∀ a ∈ unitField F₀ t, a ≠ 0 → w a = 1) (a : xField F₀) (ha : a ≠ 0) :
    w (algebraMap (xField F₀) (SliceField F₀) a) = 1 :=
  htv (a : SliceField F₀) (xField_le_unitField F₀ t a.2) fun h => ha (Subtype.ext h)
theorem aeval_trivial_of_unitField (w : Valuation (SliceField F₀) ℤᵐ⁰) (t : SliceField F₀)
    (hind : AlgebraicIndependent K ![t, sliceProj F₀ (MvPolynomial.X 0)])
    (htv : ∀ a ∈ unitField F₀ t, a ≠ 0 → w a = 1) :
    ∀ p : Polynomial (xField F₀), p ≠ 0 → w (Polynomial.aeval t p) = 1 := by
  have htr : Transcendental (xField F₀) t := by
    have h1 : AlgebraicIndependent K (fun o : Option (Fin 1) =>
        o.elim t ![sliceProj F₀ (MvPolynomial.X 0)]) :=
      (algebraicIndependent_equiv' (finSuccEquiv 1).symm (optionElim_comp_finSucc _ _)).2 hind
    have h2 := (AlgebraicIndependent.option_iff.1 h1).2
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty] at h2
    exact IntermediateField.transcendental_adjoin_iff.2 h2
  have hxle := xField_le_unitField F₀ t
  have htm : t ∈ unitField F₀ t := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  intro p hp
  refine htv _ ?_ fun h0 => hp ((transcendental_iff.1 htr) p h0)
  rw [Polynomial.aeval_eq_sum_range]
  refine sum_mem fun n _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hxle (p.coeff n).2) (pow_mem htm n)
theorem unitField_trivial_of_aeval (w : Valuation (SliceField F₀) ℤᵐ⁰) (c : SliceField F₀)
    (hX : AlgebraicIndependent K ![sliceProj F₀ (MvPolynomial.X 0)])
    (h : ∀ p : Polynomial (xField F₀), p ≠ 0 → w (Polynomial.aeval c p) = 1) :
    AlgebraicIndependent K ![c, sliceProj F₀ (MvPolynomial.X 0)] ∧
      ∀ a ∈ unitField F₀ c, a ≠ 0 → w a = 1 := by
  have h0 : ∀ p : Polynomial (xField F₀), p ≠ 0 → Polynomial.aeval c p ≠ 0 := fun p hp h0 => by
    have h1 := h p hp
    rw [h0, w.map_zero] at h1
    exact zero_ne_one h1
  have htr : Transcendental (xField F₀) c :=
    transcendental_iff.2 fun p hp => by_contra fun hne => h0 p hne hp
  constructor
  · have h2 : Transcendental (Algebra.adjoin K (Set.range ![sliceProj F₀ (MvPolynomial.X 0)])) c := by
      rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
      exact IntermediateField.transcendental_adjoin_iff.1 htr
    exact (algebraicIndependent_equiv' (finSuccEquiv 1).symm (optionElim_comp_finSucc _ _)).1
      (AlgebraicIndependent.option_iff.2 ⟨hX, h2⟩)
  · have hle : unitField F₀ c ≤ (IntermediateField.adjoin (xField F₀) {c}).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      · exact IntermediateField.mem_adjoin_simple_self (xField F₀) _
      · exact (IntermediateField.adjoin (xField F₀) {c}).algebraMap_mem
          ⟨_, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
    intro a ha ha0
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (xField F₀) a).1 (hle ha)
    have hr : r ≠ 0 := by rintro rfl; simp at ha0
    have hs : s ≠ 0 := by rintro rfl; simp at ha0
    rw [map_div₀, h r hr, h s hs, div_one]
theorem ChartDivisor.exists_unit_coord (sR sY sZ : Bool) : ChartUnitCoord F₀ sR sY sZ := by
  intro w hw
  obtain ⟨t, ht, hind, htv⟩ := hw.nonconst
  have hk := xField_trivial F₀ w t htv
  have hX : AlgebraicIndependent K ![sliceProj F₀ (MvPolynomial.X 0)] := by
    have h := hind.comp (Fin.succ : Fin 1 → Fin 2) (Fin.succ_injective _)
    have he : ![t, sliceProj F₀ (MvPolynomial.X 0)] ∘ (Fin.succ : Fin 1 → Fin 2) =
        ![sliceProj F₀ (MvPolynomial.X 0)] := by funext j; fin_cases j; rfl
    rwa [he] at h
  have ht' : t ∈ Algebra.adjoin (xField F₀) (Set.range (chartCoord F₀ sR sY sZ)) := ht
  by_contra hno
  have hall : ∀ s ∈ Set.range (chartCoord F₀ sR sY sZ), ResAlg (xField F₀) w s := by
    rintro _ ⟨i, rfl⟩
    by_contra hi
    have hle : w (chartCoord F₀ sR sY sZ i) ≤ 1 := hw.le_one _ (Algebra.subset_adjoin ⟨i, rfl⟩)
    have htriv := trivial_of_not_resAlg w hk (chartCoord F₀ sR sY sZ i) hle hi
    exact hno ⟨i, unitField_trivial_of_aeval F₀ w _ hX htriv⟩
  exact not_resAlg_of_trivial w t (aeval_trivial_of_unitField F₀ w t hind htv)
    (resAlg_adjoin w hk _ hall t ht')
end Slice
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
open RCN002 RCN136
noncomputable section
section Residue
variable {E : Type*} [Field E] {L : Type*} [Field L] [Algebra E L]
theorem exists_trivial_on_generator {ι : Type*} (nu : Valuation L ℤᵐ⁰) (T : ι → L)
    (h1 : ∀ a ∈ Algebra.adjoin E (Set.range T), nu a ≤ 1) (t : L)
    (ht : t ∈ Algebra.adjoin E (Set.range T)) (htr : Transcendental E t)
    (h2 : ∀ a ∈ IntermediateField.adjoin E {t}, a ≠ 0 → nu a = 1) :
    ∃ i, Transcendental E (T i) ∧ ∀ a ∈ IntermediateField.adjoin E {T i}, a ≠ 0 → nu a = 1 := by
  have hE : ∀ a : E, nu (algebraMap E L a) ≤ 1 := fun a => h1 _ (Subalgebra.algebraMap_mem _ a)
  let V := nu.valuationSubring
  let ιE : E →+* V := (algebraMap E L).codRestrict V fun a =>
    (Valuation.mem_valuationSubring_iff nu _).mpr (hE a)
  let ρ : V →+* IsLocalRing.ResidueField V := IsLocalRing.residue V
  let _ : Algebra E (IsLocalRing.ResidueField V) := (ρ.comp ιE).toAlgebra
  have key1 : ∀ (x : V) (P : Polynomial E), Polynomial.aeval (ρ x) P = ρ (P.eval₂ ιE x) :=
    fun x P => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl
  have key2 : ∀ (x : V) (P : Polynomial E),
      ((P.eval₂ ιE x : V) : L) = Polynomial.aeval (x : L) P := fun x P => by
    rw [Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ P ιE V.subtype x
  have hres : ∀ x : V, ρ x = 0 ↔ nu (x : L) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (Valuation.isEquiv_valuation_valuationSubring nu).lt_one_iff_lt_one.symm
  have hmem : ∀ a ∈ Algebra.adjoin E (Set.range T), a ∈ V := fun a ha =>
    (Valuation.mem_valuationSubring_iff nu a).mpr (h1 a ha)
  have hTV : ∀ i, T i ∈ V := fun i => hmem _ (Algebra.subset_adjoin ⟨i, rfl⟩)
                                                                                               
  have key3 : ∀ (x : V) (P : Polynomial E),
      Polynomial.aeval (ρ x) P = 0 ↔ nu (Polynomial.aeval (x : L) P) < 1 := fun x P => by
    rw [key1, hres, key2]
  obtain ⟨i, hi⟩ : ∃ i, Transcendental E (ρ ⟨T i, hTV i⟩) := by
    by_contra hall
    have halg : ∀ a (ha : a ∈ Algebra.adjoin E (Set.range T)), IsAlgebraic E (ρ ⟨a, hmem a ha⟩) := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact not_not.mp (not_exists.mp hall i)
      | algebraMap r => exact isAlgebraic_algebraMap (R := E) r
      | add x y hx hy ihx ihy => exact ihx.add ihy
      | mul x y hx hy ihx ihy => exact ihx.mul ihy
    obtain ⟨P, hP0, hP⟩ := halg t ht
    have h3 := (key3 ⟨t, hmem t ht⟩ P).mp hP
    have h4 : Polynomial.aeval t P ≠ 0 := fun h => hP0 ((transcendental_iff.mp htr) P h)
    have h5 := h2 _ (IntermediateField.algebra_adjoin_le_adjoin E _
      (Polynomial.aeval_mem_adjoin_singleton E t)) h4
    exact absurd h3 (by rw [h5]; exact lt_irrefl _)
  have hone : ∀ P : Polynomial E, P ≠ 0 → nu (Polynomial.aeval (T i) P) = 1 := by
    intro P hP0
    have hle : nu (Polynomial.aeval (T i) P) ≤ 1 :=
      h1 _ (Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
        (Polynomial.aeval_mem_adjoin_singleton E (T i)))
    refine le_antisymm hle (not_lt.mp fun hlt => hP0 ?_)
    exact (transcendental_iff.mp hi) P ((key3 ⟨T i, hTV i⟩ P).mpr hlt)
  refine ⟨i, fun ⟨P, hP0, hP⟩ => ?_, fun a ha ha0 => ?_⟩
  · have := hone P hP0
    rw [hP, map_zero] at this
    exact zero_ne_one this
  · obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff E a).mp ha
    have hr : r ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at ha0
      exact ha0 rfl
    have hs : s ≠ 0 := by
      rintro rfl
      rw [map_zero, div_zero] at ha0
      exact ha0 rfl
    rw [map_div₀, hone r hr, hone s hs, div_one]
end Residue
section Independence
variable {K E : Type*} [Field K] [Field E] {L₀ L : Type*} [Field L₀] [Algebra K L₀] [Field L]
  [Algebra E L]
theorem algebraicIndependent_pair_of_map (phi : Polynomial K →+* E) (hphi : Function.Injective phi)
    (ψ : L₀ →+* L) (hK : ∀ a : K, ψ (algebraMap K L₀ a) = algebraMap E L (phi (Polynomial.C a)))
    (t x : L₀) (hx : ψ x = algebraMap E L (phi Polynomial.X)) (ht : Transcendental E (ψ t)) :
    AlgebraicIndependent K ![t, x] := by
  let φ₁ : MvPolynomial (Fin 1) K →+* E :=
    phi.comp (MvPolynomial.aeval fun _ : Fin 1 => (Polynomial.X : Polynomial K)).toRingHom
  have hφ₁ : Function.Injective φ₁ := by
    refine hphi.comp ?_
    have : AlgebraicIndependent K fun _ : Fin 1 => (Polynomial.X : Polynomial K) :=
      algebraicIndependent_unique_type_iff.mpr (Polynomial.transcendental_X K)
    exact this
  let Θ : MvPolynomial (Fin 2) K →+* Polynomial E :=
    (Polynomial.mapRingHom φ₁).comp (MvPolynomial.finSuccEquiv K 1).toRingEquiv.toRingHom
  have hΘ : Function.Injective Θ :=
    (Polynomial.map_injective φ₁ hφ₁).comp (MvPolynomial.finSuccEquiv K 1).injective
  have hcomp : ψ.comp (MvPolynomial.aeval ![t, x]).toRingHom =
      (Polynomial.aeval (ψ t)).toRingHom.comp Θ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_
    · have h1 : (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.C a) =
          Polynomial.C (MvPolynomial.C a) := (MvPolynomial.finSuccEquiv K 1).commutes a
      simp [Θ, φ₁, h1, hK]
    · fin_cases j
      · simp [Θ, MvPolynomial.finSuccEquiv_X_zero]
      · have h1 : (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (1 : Fin 2)) =
            Polynomial.C (MvPolynomial.X 0) :=
          MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 1))
        simp [Θ, φ₁, h1, hx]
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have h1 : ψ.comp (MvPolynomial.aeval ![t, x]).toRingHom P = 0 := by
    change ψ (MvPolynomial.aeval ![t, x] P) = 0
    rw [hP, map_zero]
  rw [hcomp] at h1
  exact (injective_iff_map_eq_zero Θ).mp hΘ P ((transcendental_iff.mp ht) (Θ P) h1)
end Independence
section Bridge
variable {K E : Type} [Field K] [Field E]
theorem surface_divisor_restrict (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (sR sY sZ : Bool) (phi : Polynomial K →+* E) (hphi : Function.Injective phi)
    (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (ψ : SliceField F₀ →+* RCN002.CoordinateField E G)
    (hψ : ∀ A, ψ (sliceProj F₀ A) = SecondJetComponentRoots.coefficientMap phi G A) :
    SurfaceDivisorRestrict F₀ sR sY sZ G ψ := by
  have hC : ∀ a : E, RCN002.coordinateEvaluation E G (MvPolynomial.C a) = algebraMap E (RCN002.CoordinateField E G) a := fun a =>
    (RCN002.coordinateEvaluation E G).commutes a
  have hcoord : ∀ j, ψ (sliceCoord F₀ j) = coordinate E G j := fun j => by
    rw [sliceCoord, hψ, SecondJetComponentRoots.coefficientMap, RingHom.comp_apply, RCN136.surfaceMap_X_succ]
    rfl
  have hx0 : ψ (sliceProj F₀ (MvPolynomial.X 0)) = algebraMap E (RCN002.CoordinateField E G) (phi Polynomial.X) := by
    rw [hψ, SecondJetComponentRoots.coefficientMap, RingHom.comp_apply, RCN136.surfaceMap_X_zero]
    exact hC _
  have hK : ∀ a : K, ψ (algebraMap K (SliceField F₀) a) =
      algebraMap E (RCN002.CoordinateField E G) (phi (Polynomial.C a)) := fun a => by
    have h : algebraMap K (SliceField F₀) a = sliceProj F₀ (MvPolynomial.C a) := rfl
    rw [h, hψ, SecondJetComponentRoots.coefficientMap, RingHom.comp_apply, surfaceMap_C]
    exact hC _
  have hmono : ∀ i, ψ (chartCoord F₀ sR sY sZ i) =
      lmono (coordinate E G) (chartExp sR sY sZ i) := fun i => by
    simp only [chartCoord, lmono, map_mul, map_zpow₀, hcoord]
  intro nu h1 h2
  obtain ⟨t, ht, htr, htriv⟩ := h2
  by_cases hall : ∀ a, a ≠ 0 → nu (ψ a) = 1
  · exact Or.inl hall
  right
  obtain ⟨a₀, ha₀, hne⟩ : ∃ a, a ≠ 0 ∧ nu (ψ a) ≠ 1 := by
    by_contra h
    exact hall fun a ha => by_contra fun hn => h ⟨a, ha, hn⟩
  obtain ⟨e, w, he, hnorm, hw⟩ := HFree6812.exists_normalization (nu.comap ψ)
    ⟨a₀, (Valuation.ne_zero_iff _).mpr ha₀, hne⟩
  have hw' : ∀ a, nu (ψ a) = w a ^ e := hw
  have he0 : e ≠ 0 := by omega
  have hxE : ∀ r ∈ xField F₀, ∃ a : E, ψ r = algebraMap E (RCN002.CoordinateField E G) a := by
    intro r hr
    induction hr using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, hx0⟩
    | algebraMap a => exact ⟨_, hK a⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | inv x _ ihx =>
      obtain ⟨a, ha⟩ := ihx
      exact ⟨a⁻¹, by rw [map_inv₀, ha, map_inv₀]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩
  have hle : ∀ a ∈ chartRing F₀ sR sY sZ, nu (ψ a) ≤ 1 := by
    intro a ha
    rw [chartRing] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hmono]
      exact h1 _ (Algebra.subset_adjoin ⟨i, rfl⟩)
    | algebraMap r =>
      obtain ⟨a, ha⟩ := hxE r r.2
      change nu (ψ (r : SliceField F₀)) ≤ 1
      rw [ha]
      exact h1 _ (Subalgebra.algebraMap_mem _ a)
    | add x y _ _ ihx ihy =>
      rw [map_add]
      exact (nu.map_add _ _).trans (max_le ihx ihy)
    | mul x y _ _ ihx ihy =>
      rw [map_mul, map_mul]
      exact mul_le_one' ihx ihy
  obtain ⟨i, hi, hitriv⟩ := exists_trivial_on_generator nu
    (fun i => lmono (coordinate E G) (chartExp sR sY sZ i)) h1 t ht htr htriv
  have hmem : ∀ a ∈ unitField F₀ (chartCoord F₀ sR sY sZ i), ψ a ∈
      IntermediateField.adjoin E {lmono (coordinate E G) (chartExp sR sY sZ i)} := by
    intro a ha
    induction ha using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · rw [hmono]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hx0]
        exact IntermediateField.algebraMap_mem _ _
    | algebraMap a =>
      rw [hK]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
    | inv x _ ihx =>
      rw [map_inv₀]
      exact inv_mem ihx
    | mul x y _ _ ihx ihy =>
      rw [map_mul]
      exact mul_mem ihx ihy
  refine ⟨e, w, he, ⟨hnorm, fun a ha => ?_, chartCoord F₀ sR sY sZ i,
    Algebra.subset_adjoin ⟨i, rfl⟩, ?_, fun a ha ha0 => ?_⟩, hw'⟩
  · have h3 := hle a ha
    rw [hw'] at h3
    exact (pow_le_one_iff_of_nonneg zero_le he0).mp h3
  · exact algebraicIndependent_pair_of_map phi hphi ψ hK _ _ hx0 (by rw [hmono]; exact hi)
  · have h3 := hitriv _ (hmem a ha) ((map_ne_zero ψ).mpr ha0)
    rw [hw'] at h3
    exact (pow_eq_one_iff_of_nonneg zero_le he0).mp h3
theorem surface_divisor_restrict_sliceEmbedding [Algebra (RCN135.GenericField K) E]
    (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K)
    [Fact (Irreducible F₀)] (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
    (sR sY sZ : Bool) : SurfaceDivisorRestrict F₀ sR sY sZ D (HFree6812.sliceEmbedding D F₀ hker) :=
  surface_divisor_restrict F₀ sR sY sZ
    ((algebraMap (RCN135.GenericField K) E).comp (RCN135.polynomialEmbedding K))
    ((algebraMap (RCN135.GenericField K) E).injective.comp (RCN135.polynomialEmbedding_injective K)) D _
    fun A => HFree6812.sliceEmbedding_proj D F₀ hker A
end Bridge
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
open MvPolynomial HFree6812
open RCN313
theorem Chart.algebraicIndependent_of_isFractionRing {A k L ι : Type*} [CommRing A] [IsDomain A] [Field k]
    [Algebra A k] [IsFractionRing A k] [CommRing L] [Algebra A L] [Algebra k L] [IsScalarTower A k L]
    (y : ι → L) (hy : AlgebraicIndependent A y) : AlgebraicIndependent k y := by
  let _ := MvPolynomial.algebraMvPolynomial (R := A) (S := k) (σ := ι)
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro Q hQ
  obtain ⟨⟨Q', m⟩, h⟩ :=
    IsLocalization.surj ((nonZeroDivisors A).map (MvPolynomial.C (σ := ι))) Q
  obtain ⟨a, ha, hm⟩ := Submonoid.mem_map.1 m.2
  dsimp only at h
  rw [MvPolynomial.algebraMap_def, ← hm, map_C] at h
  have h1 : aeval y Q' = 0 := by
    have h3 := congrArg (aeval y) h
    rw [map_mul, hQ, zero_mul, aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def] at h3
    exact h3.symm
  rw [(injective_iff_map_eq_zero _).1 hy Q' h1, map_zero] at h
  refine (mul_eq_zero.1 h).resolve_right fun h0 => nonZeroDivisors.ne_zero ha ?_
  exact IsFractionRing.injective A k ((C_eq_zero.1 h0).trans (map_zero _).symm)
section Slots
def Chart.coreSlot (i j : Fin 3) : Fin 4 → Option (Fin 3) :=
  Fin.cases (some 2) fun m => if m = i then some 0 else if m = j then some 1 else none
theorem Chart.coreSlot_injective : ∀ i j : Fin 3, i ≠ j → Function.Injective (coreSlot i j) := by decide
theorem Chart.coreSlot_succ : ∀ i j k : Fin 3, i ≠ k → j ≠ k → coreSlot i j k.succ = none := by decide
theorem Chart.chartSlot_eq_third {i j k m : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmi : m ≠ i) (hmj : m ≠ j) : m = k := by
  rw [ne_eq, Fin.ext_iff] at hij hik hjk hmi hmj
  have := i.isLt
  have := j.isLt
  have := k.isLt
  have := m.isLt
  ext
  omega
theorem Chart.coreSlot_elim {α : Type*} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x0 : α)
    (t : Fin 3 → α) (s : Fin 4) :
    (coreSlot i j s).elim (t k) ![t i, t j, x0] = (Fin.cons x0 t : Fin 4 → α) s := by
  refine Fin.cases rfl (fun m => ?_) s
  rw [Fin.cons_succ]
  show (if m = i then some 0 else if m = j then some 1 else none : Option (Fin 3)).elim (t k)
    ![t i, t j, x0] = t m
  by_cases hmi : m = i
  · simp [hmi]
  by_cases hmj : m = j
  · simp [hmj, hij.symm]
  · obtain rfl := chartSlot_eq_third hij hik hjk hmi hmj
    simp [hmi, hmj]
def Chart.twoSlot (i j k : Fin 3) : Fin 2 ⊕ Fin 2 → Fin 4 :=
  Sum.elim ![k.succ, j.succ] ![i.succ, 0]
theorem Chart.twoSlot_bijective :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → Function.Bijective (twoSlot i j k) := by decide
def Chart.xSlot : Fin 3 ⊕ Unit → Fin 4 :=
  Sum.elim Fin.succ fun _ => 0
theorem Chart.xSlot_bijective : Function.Bijective xSlot := by decide
end Slots
variable {K : Type} [Field K] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
section Coordinates
variable (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool)
include hc
theorem Chart.chart_gen (E : Subfield (SliceField F₀)) (hK : ∀ a : K, algebraMap K (SliceField F₀) a ∈ E)
    (hX : sliceProj F₀ (MvPolynomial.X 0) ∈ E) (ht : ∀ i, chartCoord F₀ sR sY sZ i ∈ E) :
    ∀ z, z ∈ E :=
  slice_gen F₀ E hK hX (coord_mem_of_chart_mem _ hc sR sY sZ E ht)
end Coordinates
theorem Chart.exists_sliceChartPoly (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N)
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) :
    ∃ P : MvPolynomial (Fin 4) K, P ≠ 0 ∧
      aeval (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (chartCoord F₀ sR sY sZ) :
        Fin 4 → SliceField F₀) P = 0 ∧
      ∀ e ∈ P.support, ∀ i : Fin 3, e i.succ ≤ N :=
  exists_chartPoly₄ (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀) hc F₀
    (Fact.out : Irreducible F₀).ne_zero (by rw [aeval_slice]; exact (HFree6812.sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl) N
    (HFree6812.support_bound_of_weighted F₀ N hN) sR sY sZ
open Chart in
theorem chart_core_poly (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N)
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) : ChartCorePoly F₀ N sR sY sZ := by
  intro i j k hij hik hjk hind
  obtain ⟨P, hP0, hPt, hPs⟩ := exists_sliceChartPoly F₀ N hN hc sR sY sZ
  obtain ⟨Q, hQ0, hQy, hQd, hQc⟩ := exists_corePoly P hP0 (coreSlot i j)
    (coreSlot_injective i j hij) _ hind (chartCoord F₀ sR sY sZ k)
    (by
      rw [← hPt]
      exact congrArg (fun f : Fin 4 → SliceField F₀ => aeval f P)
        (funext (coreSlot_elim hij hik hjk _ _)))
    k.succ (coreSlot_succ i j k hik hjk) N (degreeOf_le_iff.2 fun e he => hPs e he k)
  refine ⟨Q, hQ0, hQy, hQd, fun n => Algebra.adjoin_mono ?_ (hQc n)⟩
  rintro _ ⟨o, rfl⟩
  fin_cases o <;> simp
open Chart in
theorem chart_two_coord (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N)
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) : ChartTwoCoord F₀ N sR sY sZ := by
  intro i j k hij hik hjk hind
  obtain ⟨P, hP0, hPt, hPs⟩ := exists_sliceChartPoly F₀ N hN hc sR sY sZ
  obtain ⟨e, he⟩ : ∃ e : Fin 4 ≃ Fin 2 ⊕ Fin 2, ∀ x, e.symm x = twoSlot i j k x :=
    ⟨(Equiv.ofBijective _ (twoSlot_bijective i j k hij hik hjk)).symm, fun _ => rfl⟩
  obtain ⟨w, hw0, hw1⟩ : ∃ w : Fin 2 → unitField F₀ (chartCoord F₀ sR sY sZ i),
      (w 0 : SliceField F₀) = chartCoord F₀ sR sY sZ i ∧
      (w 1 : SliceField F₀) = sliceProj F₀ (MvPolynomial.X 0) :=
    ⟨![⟨_, IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)⟩,
      ⟨_, IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)⟩], rfl, rfl⟩
  have hw : AlgebraicIndependent K w := by
    refine AlgebraicIndependent.of_comp (unitField F₀ (chartCoord F₀ sR sY sZ i)).val ?_
    have hcomp : (unitField F₀ (chartCoord F₀ sR sY sZ i)).val ∘ w =
        ![chartCoord F₀ sR sY sZ i, sliceProj F₀ (MvPolynomial.X 0)] := by
      funext o
      fin_cases o
      · exact hw0
      · exact hw1
    rw [hcomp]
    exact hind
  have : Infinite (unitField F₀ (chartCoord F₀ sR sY sZ i)) := Infinite.of_injective _ hw
  have hP₂ : specialize e w P ≠ 0 := fun h =>
    hP0 (specialize_injective e w hw (h.trans (map_zero _).symm))
  have hP₂v : aeval ![chartCoord F₀ sR sY sZ k, chartCoord F₀ sR sY sZ j] (specialize e w P) = 0 := by
    rw [aeval_specialize, ← hPt]
    refine congrArg (fun f : Fin 4 → SliceField F₀ => aeval f P) (funext fun s => ?_)
    obtain ⟨x, rfl⟩ := e.symm.surjective s
    rw [Equiv.apply_symm_apply, he]
    rcases x with o | o <;> fin_cases o
    · show chartCoord F₀ sR sY sZ k = (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (chartCoord F₀ sR sY sZ) : Fin 4 → SliceField F₀) k.succ
      rw [Fin.cons_succ]
    · show chartCoord F₀ sR sY sZ j = (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (chartCoord F₀ sR sY sZ) : Fin 4 → SliceField F₀) j.succ
      rw [Fin.cons_succ]
    · show (w 0 : SliceField F₀) = (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (chartCoord F₀ sR sY sZ) : Fin 4 → SliceField F₀) i.succ
      rw [Fin.cons_succ, hw0]
    · exact hw1
  have hdeg : (specialize e w P).totalDegree ≤ 2 * N := by
    rw [totalDegree_eq]
    refine Finset.sup_le fun m hm => ?_
    obtain ⟨d, hd, hmd⟩ := support_specialize e w P m hm
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, hmd 0,
      hmd 1, he, he]
    have h0 : d k.succ ≤ N := hPs d hd k
    have h1 : d j.succ ≤ N := hPs d hd j
    simp only [id]
    exact (Nat.add_le_add h0 h1).trans (two_mul N).ge
  obtain ⟨a, c, hc1, hc2⟩ := exists_twoCoord (specialize e w P) hP₂ (chartCoord F₀ sR sY sZ k)
    (chartCoord F₀ sR sY sZ j) hP₂v
  rw [Algebra.smul_def] at hc2
  exact ⟨a, _, c, hdeg, hc1, hc2⟩
theorem Chart.algebraicIndependent_YZ_X (hH : sliceProj F₀ (polyH K F₀) ≠ 0) :
    AlgebraicIndependent K (Sum.elim ![sliceCoord F₀ 0, sliceCoord F₀ 2]
      fun _ : Unit => sliceProj F₀ (MvPolynomial.X 0)) := by
  have h2 : (2 : Fin 4) ∈ F₀.vars := by
    by_contra h
    refine hH ?_
    rw [polyH, pderiv_eq_zero_of_notMem_vars h, map_zero]
  have hYZX := algInd_of_Y'_free F₀ ![1, 0, 0] 0 2 (by decide) (by decide) (by decide) rfl rfl h2
  have hL : sliceLinearL F₀ ![1, 0, 0] = sliceCoord F₀ 0 := by
    simp [sliceLinearL, Fin.sum_univ_three]
  rw [hL] at hYZX
  have h := hYZX.comp (Sum.elim ![some 0, none] fun _ : Unit => some 1) (by decide)
  have hfun : (fun o : Option (Fin 2) => o.elim (sliceCoord F₀ 2)
      ![sliceCoord F₀ 0, sliceProj F₀ (MvPolynomial.X 0)]) ∘
      (Sum.elim ![some 0, none] fun _ : Unit => some 1) =
      Sum.elim ![sliceCoord F₀ 0, sliceCoord F₀ 2]
        fun _ : Unit => sliceProj F₀ (MvPolynomial.X 0) := by
    funext s
    rcases s with o | u
    · fin_cases o <;> rfl
    · rfl
  rwa [hfun] at h
open Chart in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem chart_noether (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N)
    (hH : sliceProj F₀ (polyH K F₀) ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) :
    ChartNoether F₀ N sR sY sZ := by
  obtain ⟨hX1, hy1⟩ := AlgebraicIndependent.sumElim_iff.1 (algebraicIndependent_YZ_X F₀ hH)
  rw [Set.range_const] at hy1
  have hy : AlgebraicIndependent (xField F₀) ![sliceCoord F₀ 0, sliceCoord F₀ 2] :=
    algebraicIndependent_of_isFractionRing _ hy1
  obtain ⟨x0, hx0⟩ : ∃ x0 : xField F₀, (x0 : SliceField F₀) = sliceProj F₀ (MvPolynomial.X 0) :=
    ⟨⟨_, IntermediateField.mem_adjoin_simple_self K _⟩, rfl⟩
  have hX : AlgebraicIndependent K fun _ : Unit => x0 := by
    refine AlgebraicIndependent.of_comp (xField F₀).val ?_
    have hcomp : ((xField F₀).val ∘ fun _ : Unit => x0) =
        fun _ : Unit => sliceProj F₀ (MvPolynomial.X 0) := funext fun _ => hx0
    rw [hcomp]
    exact hX1
  have : Infinite (xField F₀) := Infinite.of_injective _ hX
  obtain ⟨e, he⟩ : ∃ e : Fin 4 ≃ Fin 3 ⊕ Unit, ∀ x, e.symm x = xSlot x :=
    ⟨(Equiv.ofBijective _ xSlot_bijective).symm, fun _ => rfl⟩
  have hF₃ : specialize e (fun _ : Unit => x0) F₀ ≠ 0 := fun h =>
    (Fact.out : Irreducible F₀).ne_zero
      (specialize_injective e _ hX (h.trans (map_zero _).symm))
  have hF₃x : aeval (sliceCoord F₀) (specialize e (fun _ : Unit => x0) F₀) = 0 := by
    rw [aeval_specialize, ← (HFree6812.sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl, ← aeval_slice]
    refine congrArg (fun f : Fin 4 → SliceField F₀ => aeval f F₀) (funext fun s => ?_)
    obtain ⟨x, rfl⟩ := e.symm.surjective s
    rw [Equiv.apply_symm_apply, he]
    rcases x with o | u
    · show sliceCoord F₀ o =
        (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀) : Fin 4 → SliceField F₀) o.succ
      rw [Fin.cons_succ]
    · exact hx0
  have hF₃N : ∀ d ∈ (specialize e (fun _ : Unit => x0) F₀).support, d 0 + d 1 + d 2 ≤ N := by
    intro m hm
    obtain ⟨d, hd, hmd⟩ := support_specialize e _ F₀ m hm
    rw [hmd 0, hmd 1, hmd 2, he, he, he]
    exact HFree6812.support_bound_of_weighted F₀ N hN d hd
  exact exists_chart_noether (sliceCoord F₀) hc _ hF₃ hF₃x N hF₃N
    (fun E hk hx => slice_gen F₀ E (fun a => hk (algebraMap K (xField F₀) a))
      (hx0 ▸ hk x0) hx) _ hy sR sY sZ
end FormalR
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
namespace Exch
variable {O : Type*} [CommRing O] (K : Type*) [Field K] [Algebra O K]
def lossSet (g : O) : Set ℕ :=
  {K' | ∀ L : Divisor O, (∀ P ∈ L.support, g ∉ P.ideal) → ∀ n : ℕ,
    ((div K g).sum fun P e =>
      (e : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ divisorIdeal K (n • L)))) ≤
    n * (L.sum fun P m => (m : ℕ∞) * Module.length O (O ⧸ (P.ideal ⊔ Ideal.span {g}))) + K'}
noncomputable def loss (g : O) : ℕ := sInf (lossSet K g)
variable [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O K]
theorem loss_mem (hO : DivisorChain O) {g : O} (hg : g ≠ 0) : loss K g ∈ lossSet K g :=
  Nat.sInf_mem (exists_bound_sum_length_quotient_nsmul K hO hg)
theorem sum_mul_le (hO : DivisorChain O) {g : O} (hg : g ≠ 0) (D : Divisor O)
    (hD : ∀ P ∈ D.support, g ∉ P.ideal) {ι : Type*} (s : Finset ι) (P : ι → PrimeDivisor O)
    (hP : Set.InjOn P s) (m : ι → ℕ) (hm : ∀ a ∈ s, m a ≤ div K g (P a)) (ord δ : ι → ℕ) (n : ℕ)
    (hord : ∀ a ∈ s, (ord a : ℕ∞) ≤
      Module.length O (O ⧸ ((P a).ideal ⊔ divisorIdeal K (n • D))) + δ a) :
    ((∑ a ∈ s, m a * ord a : ℕ) : ℕ∞) ≤
      n * (D.sum fun Q k => (k : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {g}))) +
        loss K g + (∑ a ∈ s, m a * δ a : ℕ) := by
  classical
  set len : PrimeDivisor O → ℕ∞ := fun Q =>
    Module.length O (O ⧸ (Q.ideal ⊔ divisorIdeal K (n • D))) with hlen
  have h1 : ((∑ a ∈ s, m a * ord a : ℕ) : ℕ∞) ≤
      ∑ a ∈ s, (div K g (P a) : ℕ∞) * len (P a) + (∑ a ∈ s, m a * δ a : ℕ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    calc (m a : ℕ∞) * ord a ≤ m a * (len (P a) + δ a) := mul_le_mul' le_rfl (hord a ha)
      _ = m a * len (P a) + m a * δ a := mul_add _ _ _
      _ ≤ _ := add_le_add (mul_le_mul' (Nat.cast_le.mpr (hm a ha)) le_rfl) le_rfl
  have h2 : ∑ a ∈ s, (div K g (P a) : ℕ∞) * len (P a) ≤
      (div K g).sum fun Q e => (e : ℕ∞) * len Q := by
    rw [← Finset.sum_image (f := fun Q => (div K g Q : ℕ∞) * len Q) hP]
    refine Finset.sum_le_sum_of_ne_zero fun Q _ hne => Finsupp.mem_support_iff.mpr fun h0 => hne ?_
    rw [h0, Nat.cast_zero, zero_mul]
  calc ((∑ a ∈ s, m a * ord a : ℕ) : ℕ∞)
      ≤ ∑ a ∈ s, (div K g (P a) : ℕ∞) * len (P a) + (∑ a ∈ s, m a * δ a : ℕ) := h1
    _ ≤ _ := add_le_add (h2.trans (loss_mem K hO hg D hD n)) le_rfl
omit [IsDomain O] [IsIntegrallyClosed O] in
theorem sum_length_ne_top (hO : DivisorChain O) (g : O) (D : Divisor O)
    (hD : ∀ P ∈ D.support, g ∉ P.ideal) :
    (D.sum fun Q k => (k : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {g}))) ≠ ⊤ := by
  rw [Finsupp.sum]
  exact Finset.sum_induction _ (· ≠ ⊤) (fun _ _ ha hb => WithTop.add_ne_top.mpr ⟨ha, hb⟩)
    ENat.zero_ne_top fun Q hQ =>
      WithTop.mul_ne_top (ENat.natCast_ne_top _) (length_quotient_sup_span_ne_top hO Q (hD Q hQ))
theorem sum_mul_le_toNat (hO : DivisorChain O) {g : O} (hg : g ≠ 0) (D : Divisor O)
    (hD : ∀ P ∈ D.support, g ∉ P.ideal) {ι : Type*} (s : Finset ι) (P : ι → PrimeDivisor O)
    (hP : Set.InjOn P s) (m : ι → ℕ) (hm : ∀ a ∈ s, m a ≤ div K g (P a)) (ord δ : ι → ℕ) (n : ℕ)
    (hord : ∀ a ∈ s, (ord a : ℕ∞) ≤
      Module.length O (O ⧸ ((P a).ideal ⊔ divisorIdeal K (n • D))) + δ a) :
    ∑ a ∈ s, m a * ord a ≤
      n * (D.sum fun Q k => (k : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {g}))).toNat +
        loss K g + ∑ a ∈ s, m a * δ a := by
  have h := sum_mul_le K hO hg D hD s P hP m hm ord δ n hord
  rw [← ENat.natCast_toNat (sum_length_ne_top hO g D hD)] at h
  exact_mod_cast h
end Exch
end FormalR
end SubmissionLower
end ProximityPrize
end
section
open WithZero
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
variable {O : Type*} [CommRing O] (K : Type*) [Field K] [Algebra O K]
namespace Statement
variable (O) [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O K]
def valuation_le_one_iff : Prop :=
  ∀ (P : PrimeDivisor O) (x : K), P.valuation K x ≤ 1 ↔
    ∃ a s : O, s ∉ P.ideal ∧ x * algebraMap O K s = algebraMap O K a
end Statement
namespace Proved
variable (O) [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O K]
theorem valuation_le_one_iff : Statement.valuation_le_one_iff O K := fun P x => P.valuation_le_one_iff K x
end Proved
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
namespace Surf
section Chain
theorem primeChain_of_ringKrullDim_le {A : Type*} [CommRing A] [IsDomain A]
    (h : ringKrullDim A ≤ 2) : PrimeChain A := by
  intro p p' hp hp' hp0 hlt
  by_contra hmax
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal p' hp'.ne_top
  have hm' := hm.isPrime
  have hlt' : p' < m := lt_of_le_of_ne hle fun h => hmax (h ▸ hm)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp0)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
  have h4 : (m.height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    Ideal.height_le_ringKrullDim_of_isPrime.trans h
  have h5 : m.height ≤ 2 := WithBot.coe_le_coe.mp h4
  rw [Ideal.height_bot, zero_add] at h1
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ m.height :=
    (add_le_add_left ((add_le_add_left h1 1).trans h2) 1).trans h3
  exact absurd (h6.trans h5) (by decide)
theorem primeChain_of_isIntegral {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] (h : PrimeChain A) : PrimeChain B := by
  intro p p' hp hp' hp0 hlt
  have h3 : p.under A ≠ ⊥ := fun h0 => hp0 (Ideal.eq_bot_of_under_eq_bot h0)
  obtain ⟨x, hx', hx⟩ := SetLike.exists_of_lt hlt
  have h4 : p.under A < p'.under A :=
    Ideal.under_lt_under_of_integral_mem_sdiff hlt.le ⟨hx', hx⟩ (Algebra.IsIntegral.isIntegral x)
  have h5 := h _ _ (hp.under A) (hp'.under A) h3 h4
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A B)
    (algebraMap_isIntegral_iff.mpr inferInstance) p' h5
end Chain
section Plane
variable {E L : Type*} [Field E] [Field L] [Algebra E L] {s : Fin 2 → L}
  (hs : AlgebraicIndependent E s)
include hs
theorem plane_isNoetherianRing : IsNoetherianRing (Algebra.adjoin E (Set.range s)) :=
  isNoetherianRing_of_ringEquiv _ hs.aevalEquiv.toRingEquiv
theorem plane_isIntegrallyClosed : IsIntegrallyClosed (Algebra.adjoin E (Set.range s)) := by
  have : UniqueFactorizationMonoid (Algebra.adjoin E (Set.range s)) :=
    hs.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance
theorem plane_primeChain : PrimeChain (Algebra.adjoin E (Set.range s)) := by
  apply primeChain_of_ringKrullDim_le
  rw [← ringKrullDim_eq_of_ringEquiv hs.aevalEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  rfl
end Plane
section Closure
open scoped IntermediateField.algebraAdjoinAdjoin
variable {E L : Type*} [Field E] [Field L] [Algebra E L] {s : Fin 2 → L}
theorem mem_integralClosure_iff {R : Subalgebra E L} (hsR : ∀ j, s j ∈ R)
    (hint : ∀ a ∈ R, IsIntegral (Algebra.adjoin E (Set.range s)) a) (x : L) :
    x ∈ (integralClosure R L).restrictScalars E ↔ IsIntegral (Algebra.adjoin E (Set.range s)) x := by
  have hle : Algebra.adjoin E (Set.range s) ≤ R :=
    Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hsR j)
  let _ : Algebra (Algebra.adjoin E (Set.range s)) R := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) R L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.IsIntegral (Algebra.adjoin E (Set.range s)) R :=
    ⟨fun a => (isIntegral_algebraMap_iff (B := L)).mp (hint a a.2)⟩
  exact ⟨fun hx => isIntegral_trans x hx, fun hx => hx.tower_top⟩
variable {C : Subalgebra E L}
  (hC : ∀ x : L, x ∈ C ↔ IsIntegral (Algebra.adjoin E (Set.range s)) x)
include hC
theorem adjoin_le_closure : Algebra.adjoin E (Set.range s) ≤ C := fun x hx =>
  (hC x).mpr (isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin E (Set.range s))))
theorem closure_isFractionRing
    (halg : ∀ a : L, IsAlgebraic (IntermediateField.adjoin E (Set.range s)) a) :
    IsFractionRing C L := by
  let _ : Algebra (Algebra.adjoin E (Set.range s)) C :=
    (Subalgebra.inclusion (adjoin_le_closure hC)).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) C L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsIntegralClosure C (Algebra.adjoin E (Set.range s)) L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, (hC x).mpr h⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (hC y).mp y.2⟩⟩
  have _ : Algebra.IsAlgebraic (Algebra.adjoin E (Set.range s)) L :=
    ⟨fun a => (IsFractionRing.isAlgebraic_iff (Algebra.adjoin E (Set.range s))
      (IntermediateField.adjoin E (Set.range s)) L).mpr (halg a)⟩
  exact IsIntegralClosure.isFractionRing_of_algebraic (Algebra.adjoin E (Set.range s)) C
    fun x hx => Subtype.ext hx
theorem closure_isIntegrallyClosed
    (halg : ∀ a : L, IsAlgebraic (IntermediateField.adjoin E (Set.range s)) a) :
    IsIntegrallyClosed C := by
  have := closure_isFractionRing hC halg
  let _ : Algebra (Algebra.adjoin E (Set.range s)) C :=
    (Subalgebra.inclusion (adjoin_le_closure hC)).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) C L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.IsIntegral (Algebra.adjoin E (Set.range s)) C :=
    ⟨fun a => (isIntegral_algebraMap_iff (B := L)).mp ((hC a).mp a.2)⟩
  exact (isIntegrallyClosed_iff L).mpr fun {x} hx => ⟨⟨x, (hC x).mpr (isIntegral_trans x hx)⟩, rfl⟩
theorem closure_primeChain (hs : AlgebraicIndependent E s) : PrimeChain C := by
  let _ : Algebra (Algebra.adjoin E (Set.range s)) C :=
    (Subalgebra.inclusion (adjoin_le_closure hC)).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) C L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.IsIntegral (Algebra.adjoin E (Set.range s)) C :=
    ⟨fun a => (isIntegral_algebraMap_iff (B := L)).mp ((hC a).mp a.2)⟩
  exact primeChain_of_isIntegral (plane_primeChain hs)
theorem closure_finiteType (hs : AlgebraicIndependent E s)
    [FiniteDimensional (IntermediateField.adjoin E (Set.range s)) L]
    [Algebra.IsSeparable (IntermediateField.adjoin E (Set.range s)) L] :
    Algebra.FiniteType E C := by
  let _ : Algebra (Algebra.adjoin E (Set.range s)) C :=
    (Subalgebra.inclusion (adjoin_le_closure hC)).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) C L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower E (Algebra.adjoin E (Set.range s)) C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsIntegralClosure C (Algebra.adjoin E (Set.range s)) L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, (hC x).mpr h⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (hC y).mp y.2⟩⟩
  have _ := plane_isNoetherianRing hs
  have _ := plane_isIntegrallyClosed hs
  have _ : Module.Finite (Algebra.adjoin E (Set.range s)) C :=
    IsIntegralClosure.finite (Algebra.adjoin E (Set.range s))
      (IntermediateField.adjoin E (Set.range s)) L C
  have h1 : Algebra.FiniteType E (Algebra.adjoin E (Set.range s)) :=
    Algebra.FiniteType.equiv inferInstance hs.aevalEquiv
  exact h1.trans inferInstance
theorem closure_exists_disjoint (hs : AlgebraicIndependent E s) [IsNoetherianRing C] (Q : Ideal C)
    [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ j, ∀ a : C, a ∈ Q → (a : L) ∈ Algebra.adjoin E {s j} → a = 0 := by
  let _ : Algebra (Algebra.adjoin E (Set.range s)) C :=
    (Subalgebra.inclusion (adjoin_le_closure hC)).toRingHom.toAlgebra
  have _ : IsScalarTower (Algebra.adjoin E (Set.range s)) C L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.IsIntegral (Algebra.adjoin E (Set.range s)) C :=
    ⟨fun a => (isIntegral_algebraMap_iff (B := L)).mp ((hC a).mp a.2)⟩
  have _ := plane_isNoetherianRing hs
  have _ := plane_isIntegrallyClosed hs
  have _ : FaithfulSMul (Algebra.adjoin E (Set.range s)) C :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Subalgebra.inclusion_injective (adjoin_le_closure hC))
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (Q.under (Algebra.adjoin E (Set.range s))) Q
  have h2 : (Q.under (Algebra.adjoin E (Set.range s))).height ≤ 1 := by
    rw [← hQ, h1]
    exact le_self_add
  have h3 : Q.under (Algebra.adjoin E (Set.range s)) ≠ ⊥ := fun h0 =>
    Ideal.ne_bot_of_height_eq_one hQ (Ideal.eq_bot_of_under_eq_bot h0)
  have h4 : (Q.under (Algebra.adjoin E (Set.range s))).height = 1 := by
    refine le_antisymm h2 ?_
    have h5 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h3)
    rwa [Ideal.height_bot, zero_add] at h5
  have _ : IsDiscreteValuationRing
      (Localization.AtPrime (Q.under (Algebra.adjoin E (Set.range s)))) :=
    isDiscreteValuationRing_of_height_eq_one _ h4 _
  obtain ⟨j, hj⟩ := Chart.exists_adjoin_singleton_disjoint s hs
    (Q.under (Algebra.adjoin E (Set.range s)))
  refine ⟨j, fun a haQ ha => ?_⟩
  have haP : (a : L) ∈ Algebra.adjoin E (Set.range s) :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self j)) ha
  have h6 := hj ⟨a, haP⟩ (show algebraMap (Algebra.adjoin E (Set.range s)) C ⟨a, haP⟩ ∈ Q from haQ) ha
  have h7 : ((⟨a, haP⟩ : Algebra.adjoin E (Set.range s)) : L) =
      ((0 : Algebra.adjoin E (Set.range s)) : L) := congrArg _ h6
  exact Subtype.ext h7
end Closure
section Residue
variable {E : Type*} [Field E] {A : Type*} [CommRing A] [Algebra E A] [Algebra.FiniteType E A]
theorem isIntegral_quotient (m : Ideal A) [m.IsMaximal] : Algebra.IsIntegral E (A ⧸ m) := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have _ : Algebra.FiniteType E (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ E m) (Ideal.Quotient.mkₐ_surjective E m)
  have _ : Module.Finite E (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing E (A ⧸ m)
  exact Algebra.IsIntegral.of_finite E (A ⧸ m)
theorem residue_bijective [IsAlgClosed E] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap E (A ⧸ m)) := by
  have := isIntegral_quotient (E := E) m
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral
variable {L : Type*} [Field L] [Algebra E L] [Algebra A L] [IsScalarTower E A L]
theorem not_isMaximal_centre (ν : Valuation L ℤᵐ⁰) (h : ∀ a : A, ν (algebraMap A L a) ≤ 1) (t : A)
    (htr : Transcendental E (algebraMap A L t))
    (h1 : ∀ a ∈ IntermediateField.adjoin E {algebraMap A L t}, a ≠ 0 → ν a = 1) :
    ¬(centre L ν h).IsMaximal := by
  intro hmax
  have hint := isIntegral_quotient (E := E) (centre L ν h)
  obtain ⟨f, hf, hf0⟩ := Algebra.IsIntegral.isIntegral (R := E)
    (Ideal.Quotient.mk (centre L ν h) t)
  have h2 : Polynomial.aeval t f ∈ centre L ν h := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ E (centre L ν h)) t f).symm.trans hf0
  have h3 : ν (algebraMap A L (Polynomial.aeval t f)) < 1 := h2
  rw [← Polynomial.aeval_algebraMap_apply] at h3
  have h4 : Polynomial.aeval (algebraMap A L t) f ≠ 0 := fun h0 => htr ⟨f, hf.ne_zero, h0⟩
  have h5 : Polynomial.aeval (algebraMap A L t) f ∈ IntermediateField.adjoin E {algebraMap A L t} :=
    IntermediateField.algebra_adjoin_le_adjoin E _ (Polynomial.aeval_mem_adjoin_singleton E _)
  exact absurd (h1 _ h5 h4) h3.ne
end Residue
section Trivial
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
theorem trivial_on_adjoin_singleton (ν : Valuation L ℤᵐ⁰) (t : L)
    (hle : ∀ a ∈ Algebra.adjoin E {t}, ν a ≤ 1) (hdisj : ∀ a ∈ Algebra.adjoin E {t}, ν a < 1 → a = 0) :
    ∀ a ∈ IntermediateField.adjoin E {t}, a ≠ 0 → ν a = 1 := by
  have hunit : ∀ a ∈ Algebra.adjoin E {t}, a ≠ 0 → ν a = 1 := fun a ha ha0 =>
    le_antisymm (hle a ha) (not_lt.mp fun hlt => ha0 (hdisj a ha hlt))
  intro a ha ha0
  obtain ⟨r, hr, q, hq, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp ha
  have hq0 : q ≠ 0 := fun h => ha0 (by rw [h, div_zero])
  have hr0 : r ≠ 0 := fun h => ha0 (by rw [h, zero_div])
  rw [map_div₀, hunit r hr hr0, hunit q hq hq0, div_one]
theorem valuation_le_one_of_isIntegral {A : Type*} [CommRing A] [Algebra A L] (ν : Valuation L ℤᵐ⁰)
    (hA : ∀ a : A, ν (algebraMap A L a) ≤ 1) {x : L} (hx : IsIntegral A x) : ν x ≤ 1 := by
  obtain ⟨f, hf, hfx⟩ := hx
  let φ : A →+* ν.valuationSubring := (algebraMap A L).codRestrict ν.valuationSubring hA
  refine (Valuation.valuationSubring.integers ν).isIntegral_iff_v_le_one.mp
    ⟨f.map φ, hf.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hfx
end Trivial
section Fractions
variable {E L : Type*} [Field E] [Field L] [Algebra E L] {C O : Subalgebra E L}
theorem exists_under_of_fractions (hle : C ≤ O)
    (hfrac : ∀ x ∈ O, ∃ s ∈ C, s ≠ 0 ∧ s⁻¹ ∈ O ∧ x * s ∈ C) (Q : Ideal O) [Q.IsPrime] :
    ∃ Q' : Ideal C, Q'.IsPrime ∧ Q'.height = Q.height ∧
      ∀ a : C, a ∈ Q' ↔ Subalgebra.inclusion hle a ∈ Q := by
  let _ : Algebra C O := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  let S : Submonoid C := (IsUnit.submonoid O).comap (algebraMap C O)
  have hloc : IsLocalization S O := by
    refine (isLocalization_iff S O).mpr ⟨fun y => y.2, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, hs0, hsinv, hzs⟩ := hfrac z z.2
      have hu : IsUnit (algebraMap C O ⟨s, hs⟩) :=
        isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hsinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
      exact ⟨(⟨z * s, hzs⟩, ⟨⟨s, hs⟩, hu⟩), Subtype.ext rfl⟩
    · rw [Subalgebra.inclusion_injective hle hxy]
  exact ⟨Q.under C, inferInstance, IsLocalization.height_under S Q, fun a => Iff.rfl⟩
end Fractions
end Surf
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
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
namespace Surf
theorem not_dvd_of_degreeOf {g q : MvPolynomial (Fin 3) E} {k : Fin 3} (hk : 0 < g.degreeOf k)
    (hq0 : q ≠ 0) (hq : q.degreeOf k = 0) : ¬g ∣ q := by
  rintro ⟨h, rfl⟩
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hq0) (right_ne_zero_of_mul hq0)] at hq
  omega
theorem coordinate_ne_zero (g : MvPolynomial (Fin 3) E) (hG : G = Ideal.span {g}) {j k : Fin 3}
    (hjk : j ≠ k) (hk : 0 < g.degreeOf k) : coordinate E G j ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X j : MvPolynomial (Fin 3) E) ∈ G :=
    (SecondJetComponentRoots.evaluation_zero_iff G (MvPolynomial.X j)).mp h0
  rw [hG, Ideal.mem_span_singleton] at hmem
  refine not_dvd_of_degreeOf hk (MvPolynomial.X_ne_zero j) ?_ hmem
  rw [degreeOf_X]
  exact ite_eq_right_iff.mpr fun h => absurd h hjk.symm
theorem algebraicIndependent_coordinate (g : MvPolynomial (Fin 3) E) (hG : G = Ideal.span {g})
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : 0 < g.degreeOf k) :
    AlgebraicIndependent E ![coordinate E G i, coordinate E G j] := by
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro q hq
  have hfun : ![coordinate E G i, coordinate E G j] = coordinate E G ∘ ![i, j] := by
    funext m
    fin_cases m <;> rfl
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hij
    · exact absurd hab.symm hij
    · rfl
  rw [hfun, ← aeval_rename, ← RCN002.coordinateEvaluation_eq_aeval] at hq
  have hmem : rename ![i, j] q ∈ G := (SecondJetComponentRoots.evaluation_zero_iff G _).mp hq
  rw [hG, Ideal.mem_span_singleton] at hmem
  by_contra hq0
  refine not_dvd_of_degreeOf hk
    (fun h0 => hq0 (rename_injective _ hinj (h0.trans (map_zero _).symm))) ?_ hmem
  by_contra h
  obtain ⟨m, -, hm⟩ :=
    Finset.mem_image.mp (vars_rename ![i, j] q (mem_vars_iff_degreeOf_ne_zero.mpr h))
  fin_cases m
  · exact hik hm
  · exact hjk hm
end Surf
theorem SurfaceNoether.mono {sR sY sZ : Bool} {N N' : ℕ} (h : SurfaceNoether G sR sY sZ N)
    (hN : N ≤ N') : SurfaceNoether G sR sY sZ N' := by
  obtain ⟨s₁, hs₁, s₂, hs₂, hind, hint, hdeg⟩ := h
  refine ⟨s₁, hs₁, s₂, hs₂, hind, hint, fun a => ?_⟩
  obtain ⟨Q, hQ0, hQN, hQa⟩ := hdeg a
  exact ⟨Q, hQ0, hQN.trans (Nat.mul_le_mul_left 3 hN), hQa⟩
theorem surfaceNoether_of_span [Infinite E] (g : MvPolynomial (Fin 3) E) (hG : G = Ideal.span {g})
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : 0 < g.degreeOf k)
    (hck : coordinate E G k ≠ 0) (N : ℕ) (hN : ∀ d ∈ g.support, d 0 + d 1 + d 2 ≤ N)
    (sR sY sZ : Bool) : SurfaceNoether G sR sY sZ N := by
  have hg0 : g ≠ 0 := fun h => by
    rw [h, degreeOf_zero] at hk
    exact lt_irrefl _ hk
  have hc : ∀ m, coordinate E G m ≠ 0 := fun m => by
    by_cases hm : m = k
    · rw [hm]
      exact hck
    · exact Surf.coordinate_ne_zero g hG hm hk
  have hgx : aeval (coordinate E G) g = 0 := by
    rw [← RCN002.coordinateEvaluation_eq_aeval]
    refine (SecondJetComponentRoots.evaluation_zero_iff G g).mpr ?_
    rw [hG]
    exact Ideal.mem_span_singleton_self g
  exact Chart.exists_chart_noether (coordinate E G) hc g hg0 hgx N hN
    (fun E' hE ht z => by
      have hle : IntermediateField.adjoin E (Set.range (coordinate E G)) ≤
          E'.toIntermediateField hE :=
        IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨m, rfl⟩; exact ht m)
      exact hle (RCN002.adjoin_coordinates_eq_top E G ▸ IntermediateField.mem_top))
    ![coordinate E G i, coordinate E G j]
    (Surf.algebraicIndependent_coordinate g hG hij hik hjk hk) sR sY sZ
end Surface
theorem surfaceNoether_stage {K Omega Iota : Type} [Field K] [Field Omega] [Infinite Omega]
    {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K} {p e : ℕ} [CharP Omega p]
    {flag : FlagDegree} {d : ℕ} {support : RCN275.ResidualSupportParameters}
    (S : RCN159.FH phi Gamma x p e flag d support) (G : Ideal (MvPolynomial (Fin 3) Omega))
    [G.IsPrime] (hG : G = Ideal.span {S.G}) (hR : coordinate Omega G 1 ≠ 0) (sR sY sZ : Bool) :
    SurfaceNoether G sR sY sZ (flag.zOnly + flag.yz + flag.all) :=
  surfaceNoether_of_span S.G hG (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
    S.y_dependent hR _ (fun m hm => (S.flag_support m hm).2.2) sR sY sZ
theorem surfaceNoether_packet {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}
    (P : DU.Packet x t y r) (g : _) (G : Ideal (MvPolynomial (Fin 3) (RCN135.GenericField K)))
    [G.IsPrime] (hG : G = Ideal.span {(P.stage g).G})
    (hR : coordinate (RCN135.GenericField K) G 1 ≠ 0) (sR sY sZ : Bool) :
    SurfaceNoether G sR sY sZ t :=
  (surfaceNoether_stage (P.stage g) G hG hR sR sY sZ).mono (P.stage_flag g).2.2
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open WithZero MvPolynomial
open RCN002 RCN095 RCN135 RCN136 RCN244 RCN313
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
namespace Surf
theorem val_eq_exp_addVal {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {L : Type*} [Field L] (g : R →+* L) (ν : Valuation L ℤᵐ⁰) (hle : ∀ z, ν (g z) ≤ 1)
    (hlt : ∀ z, ¬IsUnit z → ν (g z) < 1) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ z, g z ≠ 0 →
      ν (g z) = exp (-((e * (IsDiscreteValuationRing.addVal R z).toNat : ℕ) : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hunit : ∀ u : Rˣ, ν (g u) = 1 := fun u => by
    have h1 : ν (g u) * ν (g ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    rw [not_le] at hlt'
    exact (lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt').ne h1
  have hc := hlt ϖ hϖ.not_isUnit
  have hval : ∀ z, g z ≠ 0 →
      ν (g z) = ν (g ϖ) ^ (IsDiscreteValuationRing.addVal R z).toNat := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => hz (by rw [h, map_zero])
    obtain ⟨n, u, hzu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hϖ
    rw [IsDiscreteValuationRing.addVal_def z u hϖ n hzu, ENat.toNat_natCast]
    rw [hzu, map_mul, map_mul, map_pow, map_pow, hunit u, one_mul]
  by_cases hc0 : ν (g ϖ) = 0
  · refine ⟨1, le_rfl, fun z hz => ?_⟩
    have h1 := hval z hz
    have hn : (IsDiscreteValuationRing.addVal R z).toNat = 0 := by
      by_contra hn
      rw [hc0, zero_pow hn] at h1
      exact hz ((Valuation.zero_iff _).mp h1)
    rw [h1, hn, pow_zero, mul_zero, Nat.cast_zero, neg_zero, exp_zero]
  · have hlog : log (ν (g ϖ)) < 0 := by
      have h1 := hc
      rwa [← exp_log hc0, exp_lt_one_iff] at h1
    have h2 : ((-log (ν (g ϖ))).toNat : ℤ) = -log (ν (g ϖ)) := Int.toNat_of_nonneg (by omega)
    refine ⟨(-log (ν (g ϖ))).toNat, by omega, fun z hz => ?_⟩
    rw [hval z hz]
    conv_lhs => rw [← exp_log hc0]
    rw [← exp_nsmul, exp_inj, Nat.cast_mul, h2, nsmul_eq_mul]
    ring
theorem exists_lift_localization {P : Type*} [CommRing P] (I p : Ideal P) (Q : Ideal (P ⧸ I))
    [Q.IsPrime] (hQ : ∀ a, Ideal.Quotient.mk I a ∈ Q ↔ a ∈ p) {L : Type*} [Field L] (g : P →+* L)
    (hI : ∀ a ∈ I, g a = 0) (ν : Valuation L ℤᵐ⁰) (hle : ∀ a, ν (g a) ≤ 1)
    (hlt : ∀ a, ν (g a) < 1 ↔ a ∈ p) :
    ∃ g' : Localization.AtPrime Q →+* L,
      (∀ a, g' (algebraMap (P ⧸ I) (Localization.AtPrime Q) (Ideal.Quotient.mk I a)) = g a) ∧
      (∀ z, ν (g' z) ≤ 1) ∧ ∀ z, ¬IsUnit z → ν (g' z) < 1 := by
  have hone : ∀ a, a ∉ p → ν (g a) = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp fun h => ha ((hlt a).mp h))
  have hunit : ∀ y : Q.primeCompl, IsUnit (Ideal.Quotient.lift I g hI y) := fun y => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : P ⧸ I)
    have hap : a ∉ p := fun h => y.2 (ha ▸ (hQ a).mpr h)
    rw [← ha, Ideal.Quotient.lift_mk]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := hone a hap
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have key : ∀ z : Localization.AtPrime Q, ∃ a, (a ∉ p → IsUnit z) ∧
      ν (IsLocalization.lift hunit z) = ν (g a) := by
    intro z
    obtain ⟨xy, hxy⟩ := IsLocalization.surj Q.primeCompl z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective xy.1
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (xy.2 : P ⧸ I)
    have hsp : s ∉ p := fun h => xy.2.2 (hs ▸ (hQ s).mpr h)
    refine ⟨a, fun hap => ?_, ?_⟩
    · have hu : IsUnit (algebraMap (P ⧸ I) (Localization.AtPrime Q) xy.1) :=
        IsLocalization.map_units _ (⟨xy.1, fun h => hap ((hQ a).mp (ha ▸ h))⟩ : Q.primeCompl)
      rw [← hxy] at hu
      exact isUnit_of_mul_isUnit_left hu
    · have h1 := congrArg (IsLocalization.lift hunit) hxy
      rw [map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq, ← ha, ← hs,
        Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at h1
      rw [← h1, map_mul, hone s hsp, mul_one]
  refine ⟨IsLocalization.lift hunit, fun a => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [IsLocalization.lift_eq, Ideal.Quotient.lift_mk]
  · obtain ⟨a, -, h⟩ := key z
    rw [h]
    exact hle a
  · obtain ⟨a, hu, h⟩ := key z
    rw [h]
    exact (hlt a).mpr (not_not.mp fun hap => hz (hu hap))
end Surf
variable {K I : Type} [Field K] {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
theorem liveCurve_val_eq (S : Stage_p19 K I Gamma x p flag errorCap stageSupport) (C : RCN074.CM S)
    (Lf : ERB S) (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hG : surfaceMap (RCN135.polynomialEmbedding K) (originalData_p19 S C).factor ∈ G)
    (Sa : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) C.1))
    (hSa : IsCurveOnSurface G C.1 Sa) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ A : MvPolynomial (Fin 4) K, SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A ≠ 0 →
      Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A) =
        exp (-((e * (@IsDiscreteValuationRing.addVal (LocalRing_p19 S C) _ (Lf.domain C) (Lf.dvr C)
          (localImage_p19 S C A)).toNat : ℕ) : ℤ)) := by
  have hdom := Lf.domain C
  have hdvr := Lf.dvr C
  have hQV : (RCN186.quotientPrime (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C)).IsPrime :=
    RCN186.quotientPrime_isPrime _ _ (factorLe_p19 S C)
  have hle : ∀ A, Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A) ≤ 1 := fun A =>
    (Valuation.mem_valuationSubring_iff _ _).mp (hSa (surfaceMap (RCN135.polynomialEmbedding K) A)).1
  have hlt : ∀ A, Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A) < 1 ↔ A ∈ QP S C := fun A => by
    obtain ⟨h, hres⟩ := hSa (surfaceMap (RCN135.polynomialEmbedding K) A)
    have h1 := Sa.res_eq_zero_iff ⟨_, h⟩
    rw [hres] at h1
    exact h1.symm.trans (SecondJetComponentRoots.evaluation_zero_iff C.1 _)
  have hI : ∀ a ∈ RCN218.factorIdeal (originalData_p19 S C).factor, SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hF : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (originalData_p19 S C).factor = 0 := (SecondJetComponentRoots.evaluation_zero_iff G _).mpr hG
    rw [map_mul, hF, mul_zero]
  obtain ⟨g', hg', hg'le, hg'lt⟩ := Surf.exists_lift_localization _ (QP S C)
    (RCN186.quotientPrime (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C))
    (fun a => by rw [← Ideal.mem_comap, RCN186.quotientPrime_comap_quotientMk _ _ (factorLe_p19 S C)]) (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G) hI
    Sa.val hle hlt
  obtain ⟨e, he, h⟩ := Surf.val_eq_exp_addVal (R := LocalRing_p19 S C) g' Sa.val hg'le hg'lt
  refine ⟨e, he, fun A hA => ?_⟩
  have h2 : g' (localImage_p19 S C A) = SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A := hg' A
  have h1 := h (localImage_p19 S C A) (by rw [h2]; exact hA)
  rwa [h2] at h1
theorem liveCurve_val_tail (S : Stage_p19 K I Gamma x p flag errorCap stageSupport) (C : RCN074.CM S)
    (Lf : ERB S) (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hG : surfaceMap (RCN135.polynomialEmbedding K) (originalData_p19 S C).factor ∈ G)
    (Sa : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) C.1))
    (hSa : IsCurveOnSurface G C.1 Sa)
    (hN : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K (originalData_p19 S C).factor (RCN326.w + 1)) ≠ 0) :
    ∃ e : ℕ, 1 ≤ e ∧
      Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K (originalData_p19 S C).factor (RCN326.w + 1))) =
        exp (-((e * FO S Lf C : ℕ) : ℤ)) := by
  obtain ⟨e, he, h⟩ := liveCurve_val_eq S C Lf G hG Sa hSa
  exact ⟨e, he, h _ hN⟩
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
namespace Exch
section
noncomputable section
open scoped Classical
open WithZero
open RCN002 RCN074 RCN095 RCN135 RCN136 RCN159 RCN222 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open DU BD AFA BOE HFree6812
open MovingFiberThreeSources6811 (direction weight)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
abbrev component (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) : Ideal (MvPolynomial (Fin 3) Ω) :=
  Ideal.span {(P.stage g).G}
theorem component_isPrime (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) : (component P g).IsPrime :=
  (Ideal.span_singleton_prime (P.stage g).MW.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (P.stage g).MW)
attribute [local instance] component_isPrime
omit [CharP K 2130706433] in
theorem fact_irreducible (P : Packet x t y r) : Fact (Irreducible P.F) :=
  ⟨P.irreducible⟩
theorem sliceMap_component (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) (A : MvPolynomial (Fin 4) K) :
    sliceMap (K := K) (component P g) A = RCN002.coordinateEvaluation Ω (component P g) (surfaceMap (RCN135.polynomialEmbedding K) A) :=
  rfl
theorem ker_sliceMap_component (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RingHom.ker (sliceMap (K := K) (component P g)) = Ideal.span {P.F} := by
  have hG : Irreducible (P.stage g).G := (P.stage g).MW
  have hF : Irreducible P.F := P.irreducible
  have hker : RingHom.ker (sliceMap (K := K) (component P g)) = RCN219.originalPrime (component P g) := by
    ext A
    rw [RingHom.mem_ker, RCN219.mem_originalPrime_iff, sliceMap_component]
    exact HFree6812.coordEval_eq_zero_iff (component P g) _
  have hGheight : (component P g).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hG.ne_zero) hG.not_isUnit
  have hQprime : (RingHom.ker (sliceMap (K := K) (component P g))).IsPrime := RingHom.ker_isPrime _
  have hQheight : (RingHom.ker (sliceMap (K := K) (component P g))).height ≤ 1 := by
    rw [hker, ← hGheight]
    exact RCN219.originalPrime_height_le _
  have hFprime : (Ideal.span {P.F}).IsPrime :=
    (Ideal.span_singleton_prime hF.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF)
  have hFheight : (Ideal.span {P.F}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hF.ne_zero) hF.not_isUnit
  have hle : Ideal.span {P.F} ≤ RingHom.ker (sliceMap (K := K) (component P g)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hker, RCN219.mem_originalPrime_iff]
    exact Ideal.mem_span_singleton.mpr (P.stage g).RR
  by_contra hne
  have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle (Ne.symm hne))
  rw [hFheight] at hlt
  exact absurd (hlt.trans hQheight) (by decide)
def embedding (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
    SliceField P.F →+* RCN002.CoordinateField Ω (component P g) :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  HFree6812.sliceEmbedding (component P g) P.F (ker_sliceMap_component P g)
def TailOrder (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1)) : Prop :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  ∀ a ∈ active P SZ, (S a).val (embedding P a.1 (tail P.F P.F (dvd_refl P.F) w)) ≤
    exp (-(multiplicity P hp a : ℤ))
def moving (P : Packet x t y r) (Q A : MvPolynomial (Fin 3) Ω) (g : RCN222.GeometricFactor K P.F) :
    RCN002.CoordinateField Ω (component P g) :=
  RCN208.movingValue (component P g) (baseH P.F) (baseG P.F) Q A
def function (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (g : RCN222.GeometricFactor K P.F) : RCN002.CoordinateField Ω (component P g) :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  embedding P g (psiS P.F P.F (dvd_refl P.F) SZ w)
def flag {F : MvPolynomial (Fin 4) K} (SZ : MovingFiberThreeSources6811.Source F) (Hf : FlagDegree) : FlagDegree :=
  SZ.d • cutFlag w Hf + (4 * w) • SZ.flag
def baseOrder (P : Packet x t y r) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1)) (n : ℕ)
    (a : Curve P) : ℕ :=
  curveBase (S a) (moving P Q A a.1) c n
def lam (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (W : FlagDegree) : ℕ :=
  ∑ g : RCN222.GeometricFactor K P.F, baseNumber (moving P Q A g) c (function P SZ g) W
end
end
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
open WithZero MvPolynomial
open RCN002 RCN095 RCN136
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Restricts
variable {L F : Type*} [Field L] [Field F]
def Specialization.Restricts (S : Specialization L F) (y : L) (z : F) : Prop :=
  ∃ h : y ∈ S.val.valuationSubring, S.res ⟨y, h⟩ = z
namespace Specialization
namespace Restricts
variable {S : Specialization L F} {y y' : L} {z z' : F}
theorem val_le_one (h : S.Restricts y z) : S.val y ≤ 1 :=
  (Valuation.mem_valuationSubring_iff S.val y).mp h.1
theorem eq_zero_iff (h : S.Restricts y z) : z = 0 ↔ S.val y < 1 := by
  obtain ⟨hy, rfl⟩ := h
  exact S.res_eq_zero_iff ⟨y, hy⟩
theorem val_eq_one (h : S.Restricts y z) (hz : z ≠ 0) : S.val y = 1 :=
  le_antisymm h.val_le_one (not_lt.mp fun hlt => hz (h.eq_zero_iff.mpr hlt))
theorem ne_zero (h : S.Restricts y z) (hy : S.val y = 1) : z ≠ 0 := fun hz =>
  absurd (h.eq_zero_iff.mp hz) (by rw [hy]; exact lt_irrefl _)
theorem unique (h : S.Restricts y z) (h' : S.Restricts y z') : z = z' := by
  obtain ⟨hy, rfl⟩ := h
  obtain ⟨hy', rfl⟩ := h'
  rfl
theorem one : S.Restricts 1 1 := ⟨S.val.valuationSubring.one_mem, map_one S.res⟩
theorem add (h : S.Restricts y z) (h' : S.Restricts y' z') : S.Restricts (y + y') (z + z') := by
  obtain ⟨hy, rfl⟩ := h
  obtain ⟨hy', rfl⟩ := h'
  exact ⟨S.val.valuationSubring.add_mem _ _ hy hy', map_add S.res ⟨y, hy⟩ ⟨y', hy'⟩⟩
theorem neg (h : S.Restricts y z) : S.Restricts (-y) (-z) := by
  obtain ⟨hy, rfl⟩ := h
  exact ⟨S.val.valuationSubring.neg_mem _ hy, map_neg S.res ⟨y, hy⟩⟩
theorem sub (h : S.Restricts y z) (h' : S.Restricts y' z') : S.Restricts (y - y') (z - z') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg
theorem mul (h : S.Restricts y z) (h' : S.Restricts y' z') : S.Restricts (y * y') (z * z') := by
  obtain ⟨hy, rfl⟩ := h
  obtain ⟨hy', rfl⟩ := h'
  exact ⟨S.val.valuationSubring.mul_mem _ _ hy hy', map_mul S.res ⟨y, hy⟩ ⟨y', hy'⟩⟩
theorem pow (h : S.Restricts y z) (n : ℕ) : S.Restricts (y ^ n) (z ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (one : S.Restricts 1 1)
  | succ n ih => simpa only [pow_succ] using ih.mul h
theorem inv (h : S.Restricts y z) (hz : z ≠ 0) : S.Restricts y⁻¹ z⁻¹ := by
  have h1 := h.val_eq_one hz
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hinv : y⁻¹ ∈ S.val.valuationSubring :=
    (Valuation.mem_valuationSubring_iff S.val _).mpr (by rw [map_inv₀, h1, inv_one])
  obtain ⟨hy, rfl⟩ := h
  refine ⟨hinv, eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_mul, show (⟨y⁻¹, hinv⟩ : S.val.valuationSubring) * ⟨y, hy⟩ = 1 from
    Subtype.ext (inv_mul_cancel₀ hy0), map_one]
theorem div (h : S.Restricts y z) (h' : S.Restricts y' z') (hz' : z' ≠ 0) :
    S.Restricts (y / y') (z / z') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul (h'.inv hz')
theorem zpow (h : S.Restricts y z) (n : ℤ) (hz : n < 0 → z ≠ 0) : S.Restricts (y ^ n) (z ^ n) := by
  cases n with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow k
  | negSucc k =>
    simpa only [zpow_negSucc] using (h.pow (k + 1)).inv (pow_ne_zero _ (hz (Int.negSucc_lt_zero k)))
end Restricts
end Specialization
theorem Specialization.restricts_resOn {O : Type*} [CommRing O] [Algebra O L] (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (a : O) :
    S.Restricts (algebraMap O L a) (S.resOn hO a) :=
  ⟨(Valuation.mem_valuationSubring_iff S.val _).mpr (hO a), rfl⟩
end Restricts
section Curve
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
  {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem IsCurveOnSurface.restricts_BR (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    S.Restricts (RCN002.coordinateEvaluation E G A) (RCN002.coordinateEvaluation E C A) :=
  h A
theorem IsCurveOnSurface.restricts_algebraMap (h : IsCurveOnSurface G C S) (c : E) :
    S.Restricts (algebraMap E (RCN002.CoordinateField E G) c) (algebraMap E (RCN002.CoordinateField E C) c) := by
  have h1 := h.restricts_BR (MvPolynomial.C c)
  rwa [show RCN002.coordinateEvaluation E G (MvPolynomial.C c) = algebraMap E (RCN002.CoordinateField E G) c from (RCN002.coordinateEvaluation E G).commutes c,
    show RCN002.coordinateEvaluation E C (MvPolynomial.C c) = algebraMap E (RCN002.CoordinateField E C) c from (RCN002.coordinateEvaluation E C).commutes c] at h1
theorem IsCurveOnSurface.ideal_le (h : IsCurveOnSurface G C S) : G ≤ C := fun A hA => by
  have h1 := h.restricts_BR A
  rw [(SecondJetComponentRoots.evaluation_zero_iff G A).mpr hA] at h1
  exact (SecondJetComponentRoots.evaluation_zero_iff C A).mp (h1.eq_zero_iff.mpr (by rw [map_zero]; exact zero_lt_one))
theorem IsCurveOnSurface.restricts_coordinate (h : IsCurveOnSurface G C S) (j : Fin 3) :
    S.Restricts (coordinate E G j) (coordinate E C j) :=
  h (MvPolynomial.X j)
theorem IsCurveOnSurface.restricts_lmono (h : IsCurveOnSurface G C S) (a : Fin 3 → ℤ)
    (ha : ∀ j, a j < 0 → coordinate E C j ≠ 0) :
    S.Restricts (lmono (coordinate E G) a) (lmono (coordinate E C) a) :=
  (((h.restricts_coordinate 0).zpow (a 0) (ha 0)).mul ((h.restricts_coordinate 1).zpow (a 1) (ha 1))).mul
    ((h.restricts_coordinate 2).zpow (a 2) (ha 2))
theorem IsCurveOnSurface.restricts_GP {K : Type} [Field K] (h : IsCurveOnSurface G C S)
    (phi : Polynomial K →+* E) (A : MvPolynomial (Fin 4) K) :
    S.Restricts (SecondJetComponentRoots.coefficientMap phi G A) (SecondJetComponentRoots.coefficientMap phi C A) :=
  h (surfaceMap phi A)
theorem IsCurveOnSurface.restricts_movingValue (h : IsCurveOnSurface G C S)
    (H Gs Q U : MvPolynomial (Fin 3) E) (hH : H ∉ C) :
    S.Restricts (RCN208.movingValue G H Gs Q U) (RCN208.movingValue C H Gs Q U) :=
  (h.restricts_BR Q).add (((h.restricts_BR U).mul (h.restricts_BR Gs)).div (h.restricts_BR H)
    fun h0 => hH ((SecondJetComponentRoots.evaluation_zero_iff C H).mp h0))
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
section Vertex
variable {L : Type*} [Field L]
theorem chart_rows (sR sY sZ z0 z1 z2 : Bool) (l0 l1 l2 : ℤ) (hl0 : z0 = true → l0 = 0)
    (hl1 : z1 = true → l1 = 0) (hl2 : z2 = true → l2 = 0) (hY : sY = true → z0 = false)
    (hR : sR = true → z1 = false) (hZ : sZ = true → z2 = false)
    (h : ∀ i, (∀ j, chartExp sR sY sZ i j ≠ 0 → ![z0, z1, z2] j = false) →
      chartExp sR sY sZ i 0 * l0 + chartExp sR sY sZ i 1 * l1 + chartExp sR sY sZ i 2 * l2 ≤ 0)
    (i : Fin 3) :
    chartExp sR sY sZ i 0 * l0 + chartExp sR sY sZ i 1 * l1 + chartExp sR sY sZ i 2 * l2 ≤ 0 := by
  have r0 := h 0
  have r1 := h 1
  have r2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    rcases z0 with _ | _ <;> rcases z1 with _ | _ <;> rcases z2 with _ | _ <;>
    simp [chartExp, Fin.forall_fin_succ] at r0 r1 r2 hl0 hl1 hl2 hY hR hZ <;>
    fin_cases i <;> simp [chartExp] <;> omega
theorem vertex_of_centred (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (sR sY sZ : Bool)
    (hR : sR = true → x 1 ≠ 0) (hY : sY = true → x 0 ≠ 0) (hZ : sZ = true → x 2 ≠ 0)
    (hchart : ∀ i, v (lmono x (chartExp sR sY sZ i)) ≤ 1) (W : FlagDegree) :
    v (lmono x (vertexExp sR sY sZ W)) = exp (flagPole v x W) := by
  classical
  let x' : Fin 3 → L := fun j => if x j = 0 then 1 else x j
  have hx'0 : ∀ j, x j = 0 → x' j = 1 := fun j h => ite_eq_left_iff.2 fun hn => absurd h hn
  have hx'1 : ∀ j, x j ≠ 0 → x' j = x j := fun j h => ite_eq_right_iff.2 fun hp => absurd hp h
  have hx' : ∀ j, x' j ≠ 0 := fun j => by
    by_cases h : x j = 0
    · rw [hx'0 j h]
      exact one_ne_zero
    · rw [hx'1 j h]
      exact h
  have hlog : ∀ j, (v (x' j)).log = (v (x j)).log := fun j => by
    by_cases h : x j = 0
    · rw [hx'0 j h, h, map_one, map_zero, log_one, log_zero]
    · rw [hx'1 j h]
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
  have hbit : ∀ j : Fin 3, (j = 0 ∧ sY = true) ∨ (j = 1 ∧ sR = true) ∨ (j = 2 ∧ sZ = true) →
      x j ≠ 0 := by
    rintro j (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    exacts [hY h, hR h, hZ h]
  have hz : ∀ j, decide (x j = 0) = false → x j ≠ 0 := fun j h => of_decide_eq_false h
  have h' : ∀ i, v (lmono x' (chartExp sR sY sZ i)) ≤ 1 := fun i => by
    rw [lmono_le_one_iff v x' hx', hlog, hlog, hlog]
    refine chart_rows sR sY sZ (decide (x 0 = 0)) (decide (x 1 = 0)) (decide (x 2 = 0)) _ _ _
      (fun h => by rw [of_decide_eq_true h, map_zero, log_zero])
      (fun h => by rw [of_decide_eq_true h, map_zero, log_zero])
      (fun h => by rw [of_decide_eq_true h, map_zero, log_zero])
      (fun h => decide_eq_false (hY h)) (fun h => decide_eq_false (hR h))
      (fun h => decide_eq_false (hZ h)) (fun i hi => ?_) i
    have hne : ∀ j, chartExp sR sY sZ i j ≠ 0 → x j ≠ 0 := fun j hj => by
      have h := hi j hj
      fin_cases j
      exacts [hz 0 h, hz 1 h, hz 2 h]
    have h := hchart i
    rwa [hmono_eq _ hne, lmono_le_one_iff v x' hx', hlog, hlog, hlog] at h
  rw [hmono_eq _ fun j hj => hbit j (vertexExp_ne_zero sR sY sZ W j hj),
    flagPole_eq_vertex v x' hx' sR sY sZ h' W]
  simp only [flagPole, RCN187.poleOrder, hlog]
end Vertex
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
def placeTOn {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (σ : L) : ℤ :=
  max (2 * max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
    (max (poleOrder v (x 0)) (poleOrder v (x 2)) + poleOrder v σ)
theorem placeTOn_nonneg {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) (x : Fin 3 → L) (σ : L) :
    0 ≤ placeTOn v x σ :=
  le_max_of_le_left (mul_nonneg zero_le_two (le_max_of_le_left (le_max_left _ _)))
section Ramified
variable {L L' : Type*} [Field L] [Field L'] (ψ : L →+* L') (w : Valuation L ℤᵐ⁰)
  (nu : Valuation L' ℤᵐ⁰) (e : ℕ) (hnu : ∀ a, nu (ψ a) = w a ^ e)
include hnu
theorem poleOrder_ramified (a : L) : poleOrder nu (ψ a) = e * poleOrder w a := by
  rw [poleOrder, poleOrder, hnu, log_pow, nsmul_eq_mul, mul_max_of_nonneg _ _ (Nat.cast_nonneg e),
    mul_zero]
theorem flagPole_ramified (x : Fin 3 → L) (W : FlagDegree) :
    flagPole nu (fun j => ψ (x j)) W = e * flagPole w x W := by
  have he : (0 : ℤ) ≤ e := Nat.cast_nonneg e
  simp only [flagPole, poleOrder_ramified ψ w nu e hnu, ← mul_max_of_nonneg _ _ he]
  ring
theorem placeTOn_ramified (x : Fin 3 → L) (σ : L) :
    placeTOn nu (fun j => ψ (x j)) (ψ σ) = e * placeTOn w x σ := by
  have he : (0 : ℤ) ≤ e := Nat.cast_nonneg e
  simp only [placeTOn, poleOrder_ramified ψ w nu e hnu, ← mul_max_of_nonneg _ _ he]
  rw [mul_left_comm, ← mul_add, ← mul_max_of_nonneg _ _ he]
end Ramified
theorem le_one_of_trivial {L L' : Type*} [Field L] [Field L'] (ψ : L →+* L') (nu : Valuation L' ℤᵐ⁰)
    (h : ∀ a, a ≠ 0 → nu (ψ a) = 1) (a : L) : nu (ψ a) ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero]
    exact zero_le
  · exact (h a ha).le
variable {K : Type} [Field K]
theorem placeTOn_slice (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (v : Valuation (SliceField F₀) ℤᵐ⁰) :
    placeTOn v (sliceCoord F₀) (sliceSigma F F₀) = placeT F F₀ v :=
  rfl
theorem tail_cube_bound_surface (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (sR sY sZ : Bool)
    (hHf : ∀ w, ChartDivisor F₀ sR sY sZ w →
      w (sliceProj F₀ (polyH K F)) ≤ exp (flagPole w (sliceCoord F₀) Hf))
    (hPL : ChartPlaceLaw F F₀ hdvd sR sY sZ) {L : Type*} [Field L] (ψ : SliceField F₀ →+* L)
    (nu : Valuation L ℤᵐ⁰)
    (hb : (∀ a, a ≠ 0 → nu (ψ a) = 1) ∨ ∃ (e : ℕ) (w : Valuation (SliceField F₀) ℤᵐ⁰),
      1 ≤ e ∧ ChartDivisor F₀ sR sY sZ w ∧ ∀ a, nu (ψ a) = w a ^ e) (m : ℕ) :
    nu (ψ (tail F F₀ hdvd m)) ^ 3 * nu (ψ (sliceProj F₀ (polyH K F))) ^ (2 * m) ≤
      exp (4 * m * placeTOn nu (fun j => ψ (sliceCoord F₀ j)) (ψ (sliceSigma F F₀)) +
        flagPole nu (fun j => ψ (sliceCoord F₀ j)) (cutFlag m Hf)) := by
  rcases hb with htriv | ⟨e, w, -, hw, hnu⟩
  · calc nu (ψ (tail F F₀ hdvd m)) ^ 3 * nu (ψ (sliceProj F₀ (polyH K F))) ^ (2 * m)
        ≤ (1 : ℤᵐ⁰) := mul_le_one' (pow_le_one' (le_one_of_trivial ψ nu htriv _) 3)
          (pow_le_one' (le_one_of_trivial ψ nu htriv _) _)
      _ = exp (0 : ℤ) := exp_zero.symm
      _ ≤ _ := exp_le_exp.2 (add_nonneg (mul_nonneg (by positivity) (placeTOn_nonneg _ _ _))
          (RCN204.flagPole_nonneg _ _ _))
  · have h := tail_cube_bound F F₀ hdvd hH w m (hPL w hw m) Hf h5 (hHf w hw)
    rw [hnu, hnu, placeTOn_ramified ψ w nu e hnu, flagPole_ramified ψ w nu e hnu, placeTOn_slice]
    calc (w (tail F F₀ hdvd m) ^ e) ^ 3 * (w (sliceProj F₀ (polyH K F)) ^ e) ^ (2 * m)
        = (w (tail F F₀ hdvd m) ^ 3 * w (sliceProj F₀ (polyH K F)) ^ (2 * m)) ^ e := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm e 3,
            mul_comm e (2 * m)]
      _ ≤ exp (4 * m * placeT F F₀ w + flagPole w (sliceCoord F₀) (cutFlag m Hf)) ^ e :=
          pow_le_pow_left' h e
      _ = _ := by
          rw [← exp_nsmul, nsmul_eq_mul]
          congr 1
          ring
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
theorem chart_units_arith (sR sY sZ : Bool) (l0 l1 l2 : ℤ)
    (h : ∀ j, chartExp sR sY sZ j 0 * l0 + chartExp sR sY sZ j 1 * l1 +
      chartExp sR sY sZ j 2 * l2 = 0) : l0 = 0 ∧ l1 = 0 ∧ l2 = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    simp [chartExp] at h0 h1 h2 <;> omega
theorem chartExp_R_eq_zero (sR sY sZ : Bool) (j : Fin 3) (hj : j ≠ 0) : chartExp sR sY sZ j 1 = 0 := by
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases j <;>
    simp [chartExp] at hj ⊢
variable {K : Type} [Field K]
theorem coordR_root (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    ∃ P : Polynomial (SliceField F₀), P ≠ 0 ∧ P.eval (sliceCoord F₀ 1) = 0 ∧
      ∀ n, P.coeff n ∈ Algebra.adjoin K
        {sliceProj F₀ (MvPolynomial.X 0), sliceCoord F₀ 2, sliceCoord F₀ 0} := by
  classical
  have h2vars : (2 : Fin 4) ∈ F₀.vars := by
    obtain ⟨F₁, hF₁⟩ := HFree6812.sliceProj_H_eq F F₀ hdvd
    by_contra h
    rw [pderiv_eq_zero_of_notMem_vars h, map_zero, mul_zero] at hF₁
    exact hH hF₁
  let q : Fin 3 → Polynomial K := ![0, 0, 1]
  have hind := algInd_of_Y'_free F₀ q 2 0 (by decide) (by decide) (by decide) rfl rfl h2vars
  have hFx : aeval (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀) :
      Fin 4 → SliceField F₀) F₀ = 0 := by
    rw [aeval_slice]; exact (HFree6812.sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl
  obtain ⟨P, hP0, hPb, -, hPc⟩ := core_poly_p19 F₀ (Fact.out : Irreducible F₀).ne_zero
    (F₀.support.sup fun d => d 1 + d 2 + d 3)
    (fun d hd => Finset.le_sup (f := fun d : Fin 4 →₀ ℕ => d 1 + d 2 + d 3) hd)
    (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀) hFx q 2 0 1 (by decide) (by decide)
    (by decide) rfl hind
  have hℓ : ∑ m, Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) (q m) * sliceCoord F₀ m =
      sliceCoord F₀ 2 := by
    simp [q, Fin.sum_univ_three]
  rw [hℓ] at hPc
  exact ⟨P, hP0, hPb, hPc⟩
theorem exists_transcendental_coord (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0)
    (sR sY sZ : Bool) (w : Valuation (SliceField F₀) ℤᵐ⁰) (hvn : ∃ x, w x = exp (-1)) (i : Fin 3)
    (hkv : ∀ a ∈ unitField F₀ (chartCoord F₀ sR sY sZ i), a ≠ 0 → w a = 1) :
    ∃ j, j ≠ i ∧ j ≠ 0 ∧
      Transcendental (unitField F₀ (chartCoord F₀ sR sY sZ i)) (chartCoord F₀ sR sY sZ j) := by
  classical
  set k := unitField F₀ (chartCoord F₀ sR sY sZ i) with hk
  by_contra hno
  set A := algebraicClosure k (SliceField F₀) with hA
  have hkA : ∀ x ∈ k, x ∈ A := fun x hx => A.algebraMap_mem ⟨x, hx⟩
  have hX0 : sliceProj F₀ (MvPolynomial.X 0) ∈ A :=
    hkA _ (IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have ht : ∀ j, j ≠ 0 → chartCoord F₀ sR sY sZ j ∈ A := by
    intro j hj0
    by_cases hji : j = i
    · rw [hji]; exact hkA _ (IntermediateField.subset_adjoin K _ (Set.mem_insert _ _))
    · exact mem_algebraicClosure_iff.2 (by_contra fun h => hno ⟨j, hji, hj0, h⟩)
  have hYZ : ∀ l, l ≠ 1 → sliceCoord F₀ l ∈ A := by
    intro l hl
    rw [coord_eq_lmono_chart (sliceCoord F₀) hc sR sY sZ l]
    refine lmono_mem_subfield A.toSubfield _ _ fun m hm => ht m fun hm0 => hm ?_
    rw [hm0]; simp [chartLam, hl]
  obtain ⟨P, hP0, hPb, hPc⟩ := coordR_root F F₀ hdvd hH
  have hR : sliceCoord F₀ 1 ∈ A := by
    have hle : Algebra.adjoin K {sliceProj F₀ (MvPolynomial.X 0), sliceCoord F₀ 2, sliceCoord F₀ 0} ≤
        (A.restrictScalars K).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro y (rfl | rfl | rfl)
      · exact hX0
      · exact hYZ 2 (by decide)
      · exact hYZ 0 (by decide)
    have hlift : P ∈ Polynomial.lifts (algebraMap A (SliceField F₀)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨P.coeff n, hle (hPc n)⟩, rfl⟩
    obtain ⟨P', hP'⟩ := (Polynomial.mem_lifts P).1 hlift
    have hP'0 : P' ≠ 0 := by rintro rfl; exact hP0 (by rw [← hP', Polynomial.map_zero])
    have hP'b : Polynomial.aeval (sliceCoord F₀ 1) P' = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hP']; exact hPb
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.restrictScalars k ⟨P', hP'0, hP'b⟩)
  have hall : ∀ x, x ∈ A.toSubfield :=
    slice_gen F₀ A.toSubfield (fun a => hkA _ (k.algebraMap_mem a)) hX0 fun l => by
      by_cases hl : l = 1
      · rw [hl]; exact hR
      · exact hYZ l hl
  obtain ⟨π, hπ⟩ := hvn
  have hπ0 : π ≠ 0 := by rintro rfl; rw [w.map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hkle : ∀ a : k, w (algebraMap k (SliceField F₀) a) ≤ 1 := fun a => by
    by_cases h0 : (a : SliceField F₀) = 0
    · rw [show algebraMap k (SliceField F₀) a = (a : SliceField F₀) from rfl, h0, w.map_zero]
      exact zero_le
    · exact (hkv _ a.2 h0).le
  have h1 := DJT w hkle hπ0 (mem_algebraicClosure_iff.1 (hall π))
  rw [hπ, ← exp_zero, exp_inj] at h1
  omega
theorem place_law_of_presentation [CharP K 2130706433] (F F₀ : MvPolynomial (Fin 4) K)
    [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ)
    (hNp : 4 * N ^ 2 < 2130706433) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool)
    (hcore : ChartCorePoly F₀ N sR sY sZ) (w : Valuation (SliceField F₀) ℤᵐ⁰)
    (hw : ChartDivisor F₀ sR sY sZ w)
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ w) (placeH F F₀ w) → (n : K) ≠ 0)
    (hgen2 : placeP F₀ w = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      w (sliceProj F₀ a) < 1 ∧ w (sliceProj F₀ b) < 1 ∧
      ∀ g, w (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        w (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hind : AlgebraicIndependent K ![chartCoord F₀ sR sY sZ i, sliceProj F₀ (MvPolynomial.X 0)])
    (hkv : ∀ a ∈ unitField F₀ (chartCoord F₀ sR sY sZ i), a ≠ 0 → w a = 1)
    (hst : Transcendental (unitField F₀ (chartCoord F₀ sR sY sZ i)) (chartCoord F₀ sR sY sZ j))
    (s₀ : SliceField F₀)
    (hs₀ : Tame w (HFree6812.sliceDerivation F F₀ hdvd)
      (exp (vpole w (HFree6812.sliceDerivation F F₀ hdvd (chartCoord F₀ sR sY sZ i)))) s₀)
    (hss₀ : w (chartCoord F₀ sR sY sZ j - s₀) < 1) (m : ℕ) : PlaceLaw F F₀ hdvd w m := by
  classical
  set t := chartCoord F₀ sR sY sZ with ht
  set X0 := sliceProj F₀ (MvPolynomial.X 0) with hX0
  set k₁ := unitField F₀ (t i) with hk₁
  have hzk : t i ∈ k₁ := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have hX0k : X0 ∈ k₁ :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hle : ∀ l, w (t l) ≤ 1 := fun l => hw.coord_le_one l
  have ht0 : ∀ l, t l ≠ 0 := fun l => lmono_ne_zero (sliceCoord F₀) hc _
  have hu : w (t i) = 1 := hkv _ hzk (ht0 i)
  obtain ⟨d, hz, hdir, hcap⟩ :=
    chart_row F F₀ hdvd hH hc sR sY sZ w hw.trivial_on_K hle i hu
  have hind3 : AlgebraicIndependent K ![t j, t i, X0] := by
    have h2 : Transcendental (Algebra.adjoin K (Set.range ![t i, X0])) (t j) := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
      exact IntermediateField.transcendental_adjoin_iff.1 hst
    exact (algebraicIndependent_equiv' (finSuccEquiv 2).symm (optionElim_comp_finSucc _ _)).1
      (AlgebraicIndependent.option_iff.2 ⟨hind, h2⟩)
  obtain ⟨P, hP0, hPb, hPN, hPc⟩ := hcore j i k hij.symm hjk hik hind3
  have hPc' : ∀ n, P.coeff n ∈ IntermediateField.adjoin k₁ {t j} := by
    intro n
    have hsub : Algebra.adjoin K {X0, t j, t i} ≤
        ((IntermediateField.adjoin k₁ {t j}).restrictScalars K).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro y (rfl | rfl | rfl)
      · exact (IntermediateField.adjoin k₁ {t j}).algebraMap_mem ⟨_, hX0k⟩
      · exact IntermediateField.mem_adjoin_simple_self k₁ _
      · exact (IntermediateField.adjoin k₁ {t j}).algebraMap_mem ⟨_, hzk⟩
    exact hsub (hPc n)
  have hgen : ∀ E : Subfield (SliceField F₀), (∀ x ∈ k₁, x ∈ E) → t j ∈ E → t k ∈ E →
      ∀ x, x ∈ E := by
    intro E hkE hsE hbE
    have htE : ∀ l, t l ∈ E := fun l => by
      by_cases hlj : l = j
      · rw [hlj]; exact hsE
      by_cases hlk : l = k
      · rw [hlk]; exact hbE
      rw [HFree6812.eq_of_ne_of_ne hij hik hjk hlj hlk]; exact hkE _ hzk
    exact slice_gen F₀ E (fun a => hkE _ (k₁.algebraMap_mem a)) (hkE _ hX0k)
      (coord_mem_of_chart_mem (sliceCoord F₀) hc sR sY sZ E htE)
  have hNlt : N < 2130706433 := lt_of_le_of_lt
    ((Nat.le_self_pow (by norm_num) N).trans (Nat.le_mul_of_pos_left _ (by norm_num))) hNp
  have h2 : (2 : K) ≠ 0 := by
    have := natCast_ne_zero_of_lt (K := K) 2 (by norm_num) (by norm_num)
    exact_mod_cast this
  have h := place_law_of_tame_unit d F F₀ hdvd hH w hw.norm hw.trivial_on_K hw.x0_le_one (t i) hz
    hdir hkv (t j) (t k) s₀ (hle j) hst hs₀ hss₀ hgen P hP0 hPb hPc' N hPN
    (fun n hn hnN => natCast_ne_zero_of_lt n hn (lt_of_le_of_lt hnN hNlt)) h2 hchar hgen2 m
  have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  have h5 := mul_le_mul_of_nonneg_left hcap hm
  show 3 * vpole w ((⇑(HFree6812.sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1)) + m * (5 * placeP F₀ w) ≤ _
  linarith
theorem chartPlaceLaw_of_contracts [CharP K 2130706433] (F F₀ : MvPolynomial (Fin 4) K)
    [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ)
    (hNp : 4 * N ^ 2 < 2130706433) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool)
    (hcore : ChartCorePoly F₀ N sR sY sZ) (hchar : ChartHchar F F₀ sR sY sZ)
    (hgen : ChartHgen F₀ sR sY sZ) : ChartPlaceLaw F F₀ hdvd sR sY sZ := by
  classical
  intro w hw m
  obtain ⟨i, hind, hkv⟩ := ChartDivisor.exists_unit_coord F₀ sR sY sZ w hw
  set t := chartCoord F₀ sR sY sZ with ht
  set Dd := HFree6812.sliceDerivation F F₀ hdvd with hDd
  have hle : ∀ l, w (t l) ≤ 1 := fun l => hw.coord_le_one l
  have ht0 : ∀ l, t l ≠ 0 := fun l => lmono_ne_zero (sliceCoord F₀) hc _
  have hkle : ∀ a : unitField F₀ (t i), w (algebraMap _ (SliceField F₀) a) ≤ 1 := fun a => by
    by_cases h0 : (a : SliceField F₀) = 0
    · rw [show algebraMap (unitField F₀ (t i)) (SliceField F₀) a = (a : SliceField F₀) from rfl, h0,
        w.map_zero]
      exact zero_le
    · exact (hkv _ a.2 h0).le
  by_cases hA : ∃ j, j ≠ i ∧ w (t j) < 1
  · obtain ⟨j, hji, hlt⟩ := hA
    obtain ⟨k, hki, hkj⟩ := exists_third i j hji
    have hst : Transcendental (unitField F₀ (t i)) (t j) := fun halg =>
      ne_of_lt hlt (DJT w hkle (ht0 j) halg)
    exact place_law_of_presentation F F₀ hdvd hH N hNp hc sR sY sZ hcore w hw (hchar w hw)
      (hgen w hw) i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj) hind hkv hst 0
      (tameSubring w Dd _).zero_mem (by rwa [sub_zero]) m
  · have hall : ∀ l, w (t l) = 1 := fun l =>
      le_antisymm (hle l) (not_lt.1 fun hlt => hA ⟨l, fun hli => by
        rw [hli, hkv _ (IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)) (ht0 i)] at hlt
        exact lt_irrefl _ hlt, hlt⟩)
    obtain ⟨hl0, hl1, -⟩ := chart_units_arith sR sY sZ (w (sliceCoord F₀ 0)).log
      (w (sliceCoord F₀ 1)).log (w (sliceCoord F₀ 2)).log fun l => by
        have h := hall l
        rw [ht, chartCoord, lmono_val w (sliceCoord F₀) hc, ← exp_zero, exp_inj] at h
        exact h
    have hwY : w (sliceCoord F₀ 0) = 1 := by
      rw [← exp_log ((Valuation.ne_zero_iff w).2 (hc 0)), hl0, exp_zero]
    have hwR : w (sliceCoord F₀ 1) = 1 := by
      rw [← exp_log ((Valuation.ne_zero_iff w).2 (hc 1)), hl1, exp_zero]
    obtain ⟨j, hji, hj0, hst⟩ :=
      exists_transcendental_coord F F₀ hdvd hH hc sR sY sZ w hw.norm i hkv
    obtain ⟨k, hki, hkj⟩ := exists_third i j hji
    have hDj : w (Dd (t j)) ≤ 1 := by
      rw [ht, chartCoord, hDd, D_lmono F F₀ hdvd hH hc, chartExp_R_eq_zero sR sY sZ j hj0,
        Int.cast_zero, zero_mul, add_zero, map_mul, map_mul, map_div₀, hwY, hwR, div_one, mul_one]
      exact mul_le_one' (hle j) (intCast_le_one F₀ w hw.trivial_on_K _)
    have htame : Tame w Dd (exp (vpole w (Dd (t i)))) (t j) :=
      ⟨hle j, hDj.trans (by rw [← exp_zero, exp_le_exp]; exact vpole_nonneg _ _)⟩
    exact place_law_of_presentation F F₀ hdvd hH N hNp hc sR sY sZ hcore w hw (hchar w hw)
      (hgen w hw) i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj) hind hkv hst (t j) htame
      (by rw [sub_self, w.map_zero]; exact zero_lt_one) m
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
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem height_le_of_rename {K : Type*} [Field K] {σ τ : Type*} [Finite σ] (ι : τ → σ)
    (hι : Function.Injective ι) (𝔓 : Ideal (MvPolynomial σ K)) [𝔓.IsPrime]
    (h : ∀ r : MvPolynomial τ K, rename ι r ∈ 𝔓 → r = 0) :
    ∃ n : ℕ, 𝔓.height ≤ n ∧ n + Nat.card τ = Nat.card σ := by
  classical
  have : Finite τ := Finite.of_injective ι hι
  let S₁ := ↥(Set.range ι)ᶜ
  let eqv : S₁ ⊕ τ ≃ σ := (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range ι)))
  let R₂ := MvPolynomial τ K
  let e : MvPolynomial σ K ≃ₐ[K] MvPolynomial S₁ R₂ :=
    (renameEquiv K eqv.symm).trans (sumAlgEquiv K S₁ τ)
  have he : ∀ r : R₂, e (rename ι r) = C r := by
    intro r
    have h1 : rename ι r = rename eqv (rename Sum.inr r) := by
      rw [rename_rename]; rfl
    rw [h1]
    show sumAlgEquiv K S₁ τ (rename eqv.symm (rename eqv (rename Sum.inr r))) = C r
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
    exact AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr (R := K) (S₁ := S₁) (S₂ := τ)) r
  let e' : MvPolynomial S₁ R₂ ≃+* MvPolynomial σ K := e.symm.toRingEquiv
  let 𝔓' : Ideal (MvPolynomial S₁ R₂) := 𝔓.comap e'
  have hh : 𝔓'.height = 𝔓.height := RingEquiv.height_comap e' 𝔓
  let M := nonZeroDivisors R₂
  let B := MvPolynomial S₁ (FractionRing R₂)
  have hdisj : Disjoint ((M.map (C (σ := S₁)) : Submonoid (MvPolynomial S₁ R₂)) :
      Set (MvPolynomial S₁ R₂)) (𝔓' : Set (MvPolynomial S₁ R₂)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hmem
    have h2 : e' (C r) = rename ι r := by rw [← he r]; exact e.symm_apply_apply _
    have hmem' : e' (C r) ∈ 𝔓 := hmem
    rw [h2] at hmem'
    exact nonZeroDivisors.ne_zero hr (h r hmem')
  have hmap := IsLocalization.height_map_of_disjoint (S := B) (M.map C) 𝔓' hdisj
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint (M.map C) B 𝔓' inferInstance hdisj
  have hle := Ideal.height_le_ringKrullDim_of_ne_top hprime.ne_top
  rw [hmap, hh, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add] at hle
  refine ⟨Nat.card S₁, ?_, ?_⟩
  · have h3 := WithBot.coe_le_coe.mp hle
    rwa [ENat.card_eq_coe_natCard] at h3
  · rw [← Nat.card_congr eqv, Nat.card_sum]
theorem chart_affine_arith (sR sY sZ : Bool) (l0 l1 l2 : ℤ)
    (h : ∀ j, chartExp sR sY sZ j 0 * l0 + chartExp sR sY sZ j 1 * l1 +
      chartExp sR sY sZ j 2 * l2 ≤ 0)
    (h0 : l0 ≤ 0) (h1 : l1 ≤ 0) (h2 : l2 ≤ 0) (i : Fin 3) :
    (0 ≤ chartExp sR sY sZ i 0 ∨ l0 = 0) ∧ (0 ≤ chartExp sR sY sZ i 1 ∨ l1 = 0) ∧
      (0 ≤ chartExp sR sY sZ i 2 ∨ l2 = 0) := by
  have c0 := h 0
  have c1 := h 1
  have c2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;> fin_cases i <;>
    simp [chartExp] at c0 c1 c2 ⊢ <;> omega
variable {K : Type} [Field K]
theorem chartDivisor_hgen (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) : ChartHgen F₀ sR sY sZ := by
  classical
  intro w hw hP0
  set X0 := sliceProj F₀ (MvPolynomial.X 0) with hX0def
  have hint := place_hint F₀ w hw.trivial_on_K hw.x0_le_one hP0
  have hcle : ∀ l, w (sliceCoord F₀ l) ≤ 1 := fun l => hint _
  obtain ⟨i, hind, hkv⟩ := ChartDivisor.exists_unit_coord F₀ sR sY sZ w hw
  have hk := xField_trivial F₀ w _ hkv
  have hX : AlgebraicIndependent K ![X0] := by
    have h := hind.comp (Fin.succ : Fin 1 → Fin 2) (Fin.succ_injective _)
    have he : ![chartCoord F₀ sR sY sZ i, X0] ∘ (Fin.succ : Fin 1 → Fin 2) = ![X0] := by
      funext j; fin_cases j; rfl
    rwa [he] at h
  have hlog : ∀ l, (w (sliceCoord F₀ l)).log ≤ 0 := fun l => by
    rw [← log_exp (0 : ℤ)]
    exact (log_le_log ((Valuation.ne_zero_iff w).2 (hc l)) (by simp)).2 (by simpa using hcle l)
  have hex : ∃ j, ¬ ResAlg (xField F₀) w (sliceCoord F₀ j) := by
    by_contra hno
    have hall : ∀ j, ResAlg (xField F₀) w (sliceCoord F₀ j) := fun j =>
      by_contra fun h => hno ⟨j, h⟩
    have harith := chart_affine_arith sR sY sZ _ _ _
      (fun j => (lmono_le_one_iff w (sliceCoord F₀) hc _).1 (hw.coord_le_one j))
      (hlog 0) (hlog 1) (hlog 2) i
    have hunit : ∀ l, (w (sliceCoord F₀ l)).log = 0 → w (sliceCoord F₀ l) = 1 := fun l h => by
      rw [← exp_log ((Valuation.ne_zero_iff w).2 (hc l)), h, exp_zero]
    have hres : ResAlg (xField F₀) w (chartCoord F₀ sR sY sZ i) :=
      resAlg_lmono w hk (sliceCoord F₀) _ fun l => ⟨hall l, by
        fin_cases l
        · exact harith.1.imp id (hunit 0)
        · exact harith.2.1.imp id (hunit 1)
        · exact harith.2.2.imp id (hunit 2)⟩
    exact not_resAlg_of_trivial w _ (aeval_trivial_of_unitField F₀ w _ hind hkv) hres
  obtain ⟨j, hj⟩ := hex
  obtain ⟨hindj, hkvj⟩ := unitField_trivial_of_aeval F₀ w _ hX
    (trivial_of_not_resAlg w hk _ (hcle j) hj)
  set 𝔓 := valCentre (sliceProj F₀) w hint with h𝔓
  have hheight : 𝔓.height ≤ 2 := by
    let ι : Fin 2 → Fin 4 := ![j.succ, 0]
    have hι : Function.Injective ι := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [ι, Fin.succ_ne_zero, (Fin.succ_ne_zero j).symm] at hab ⊢
    have hval : ∀ r : MvPolynomial (Fin 2) K,
        sliceProj F₀ (rename ι r) = aeval ![sliceCoord F₀ j, X0] r := by
      intro r
      have hfun : (Fin.cons X0 (sliceCoord F₀) : Fin 4 → SliceField F₀) ∘ ι =
          ![sliceCoord F₀ j, X0] := by
        funext a; fin_cases a <;> rfl
      rw [← aeval_slice, aeval_rename, hfun]
    have hmem : ∀ r : MvPolynomial (Fin 2) K, aeval ![sliceCoord F₀ j, X0] r ∈
        unitField F₀ (sliceCoord F₀ j) := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact (unitField F₀ (sliceCoord F₀ j)).algebraMap_mem a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p a hp =>
        rw [map_mul, aeval_X]
        refine mul_mem hp ?_
        fin_cases a
        · exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
        · exact IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨n, hn, hcard⟩ := height_le_of_rename ι hι 𝔓 fun r hr => by
      by_contra hr0
      have h1 : w (sliceProj F₀ (rename ι r)) < 1 := hr
      rw [hval r, hkvj _ (hmem r) fun h0 => hr0
        ((injective_iff_map_eq_zero _).1 (algebraicIndependent_iff_injective_aeval.1 hindj) r h0)]
        at h1
      exact lt_irrefl _ h1
    have hn2 : n = 2 := by simpa using hcard
    rw [hn2] at hn
    exact_mod_cast hn
  have := RCN230.mvPolynomial_atPrime_isRegularLocalRing 𝔓
  obtain ⟨a, ha, b, hb, hgen'⟩ := HFree6812.exists_two_local_generators 𝔓 hheight
  refine ⟨a, b, ha, hb, fun g hg => ?_⟩
  obtain ⟨s, hs, x, y, hsg⟩ := hgen' g hg
  exact ⟨s, x, y, le_antisymm (hint s) (not_lt.1 hs), hsg⟩
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
section MonoSpan
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
theorem left_mem_monoSpan (u v : L) : u ∈ monoSpan k u v 1 :=
  Submodule.subset_span ⟨1, 0, le_rfl, by simp⟩
theorem right_mem_monoSpan (u v : L) : v ∈ monoSpan k u v 1 :=
  Submodule.subset_span ⟨0, 1, le_rfl, by simp⟩
theorem algebraMap_mul_mem_monoSpan (u v : L) {d : ℕ} (a : k) {x : L} (hx : x ∈ monoSpan k u v d) :
    algebraMap k L a * x ∈ monoSpan k u v d := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hx
theorem pow_mem_monoSpan (u v : L) {d : ℕ} {x : L} (hx : x ∈ monoSpan k u v d) (j : ℕ) :
    x ^ j ∈ monoSpan k u v (d * j) := by
  induction j with
  | zero => simpa using one_mem_monoSpan (k := k) u v
  | succ j ih => rw [pow_succ, Nat.mul_succ]; exact mul_mem_monoSpan u v ih hx
theorem exists_monoSpan_of_mem_adjoin (u v : L) :
    ∀ x ∈ Algebra.adjoin k {u, v}, ∃ d, x ∈ monoSpan k u v d := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, left_mem_monoSpan _ _⟩
    · exact ⟨1, right_mem_monoSpan _ _⟩
  | algebraMap a =>
    exact ⟨0, by simpa using algebraMap_mul_mem_monoSpan u v a (one_mem_monoSpan (k := k) u v)⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', Submodule.add_mem _ (monoSpan_mono u v (le_max_left _ _) hd)
      (monoSpan_mono u v (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mul_mem_monoSpan u v hd hd'⟩
theorem neg_log_le_of_ord (w : Valuation L ℤᵐ⁰) (B : ℕ) (h : L) (h0 : h ≠ 0)
    (hB : ∀ e : ℕ, w h = exp (-(e : ℤ)) → e ≤ B) : -(w h).log ≤ B := by
  by_cases hpos : 0 ≤ (w h).log
  · have : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    omega
  · have he : w h = exp (-(((-(w h).log).toNat : ℕ) : ℤ)) := by
      rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log ((Valuation.ne_zero_iff w).2 h0)]
    have h1 := hB _ he
    omega
end MonoSpan
variable {K : Type} [Field K]
theorem chartDivisor_hchar [CharP K 2130706433] (F F₀ : MvPolynomial (Fin 4) K)
    [Fact (Irreducible F₀)] (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ)
    (hN : MvPolynomial.weightedTotalDegree ![0, 1, 1, 1] F ≤ N) (hNp : 4 * N ^ 2 < 2130706433)
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) (htwo : ChartTwoCoord F₀ N sR sY sZ) :
    ChartHchar F F₀ sR sY sZ := by
  classical
  intro w hw
  obtain ⟨i, hind, hkv⟩ := ChartDivisor.exists_unit_coord F₀ sR sY sZ w hw
  obtain ⟨j, k, hij, hik, hjk⟩ := HFree6812.exists_two_others i
  set x := sliceCoord F₀ with hx
  set t := chartCoord F₀ sR sY sZ with ht
  set X0 := sliceProj F₀ (MvPolynomial.X 0) with hX0
  set k₁ := unitField F₀ (t i) with hk₁
  obtain ⟨a, n, cf, hn, hcdeg, hrel⟩ := htwo i j k hij hik hjk hind
  set u := t j + (a : SliceField F₀) * t k with hu
  set v := t k with hv
  have hzk : t i ∈ k₁ := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have hX0k : X0 ∈ k₁ :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hk : ∀ b : k₁, b ≠ 0 → w (algebraMap k₁ (SliceField F₀) b) = 1 := fun b hb =>
    hkv (b : SliceField F₀) b.2 fun h => hb (Subtype.ext h)
  have hle : ∀ l, w (t l) ≤ 1 := fun l => hw.coord_le_one l
  have ht0 : ∀ l, t l ≠ 0 := fun l => lmono_ne_zero (sliceCoord F₀) hc _
  have htj : t j = u - (a : SliceField F₀) * v := by rw [hu]; ring
  have hmulk : ∀ (y : SliceField F₀), y ∈ k₁ → ∀ {d : ℕ} {g : SliceField F₀},
      g ∈ monoSpan k₁ u v d → y * g ∈ monoSpan k₁ u v d := fun y hy _ _ hg =>
    algebraMap_mul_mem_monoSpan u v (⟨y, hy⟩ : k₁) hg
  have htV : ∀ l, t l ∈ monoSpan k₁ u v (if l = i then 0 else 1) := by
    intro l
    by_cases hli : l = i
    · subst hli
      simpa using hmulk _ hzk (one_mem_monoSpan (k := k₁) u v)
    simp only [hli, ↓reduceIte]
    by_cases hlj : l = j
    · rw [hlj, htj]
      exact Submodule.sub_mem _ (left_mem_monoSpan u v) (hmulk _ a.2 (right_mem_monoSpan u v))
    · by_cases hlk : l = k
      · rw [hlk]; exact right_mem_monoSpan u v
      · exact absurd (HFree6812.eq_of_ne_of_ne hij hik hjk hlj hlk) hli
  have htV1 : ∀ l, t l ∈ monoSpan k₁ u v 1 := fun l =>
    monoSpan_mono u v (by split_ifs <;> simp) (htV l)
  obtain ⟨π, hπ⟩ := hw.norm
  have hgenE : ∀ y, y ∈ (IntermediateField.adjoin k₁ {u, v}).toSubfield := by
    set E := IntermediateField.adjoin k₁ {u, v} with hE
    have hkE : ∀ y ∈ k₁, y ∈ E := fun y hy => E.algebraMap_mem ⟨y, hy⟩
    have huE : u ∈ E := IntermediateField.subset_adjoin k₁ _ (Set.mem_insert _ _)
    have hvE : v ∈ E := IntermediateField.subset_adjoin k₁ _ (Set.mem_insert_of_mem _ rfl)
    have htE : ∀ l, t l ∈ E := fun l => by
      by_cases hlj : l = j
      · rw [hlj, htj]; exact E.sub_mem huE (E.mul_mem (hkE _ a.2) hvE)
      by_cases hlk : l = k
      · rw [hlk]; exact hvE
      rw [HFree6812.eq_of_ne_of_ne hij hik hjk hlj hlk]; exact hkE _ hzk
    exact slice_gen F₀ E.toSubfield (fun b => hkE _ (k₁.algebraMap_mem b)) (hkE _ hX0k)
      (coord_mem_of_chart_mem (sliceCoord F₀) hc sR sY sZ E.toSubfield htE)
  obtain ⟨r, hr, s, hs, hπrs⟩ := IntermediateField.mem_adjoin_iff_div.1 (hgenE π)
  obtain ⟨d₁, hd₁⟩ := exists_monoSpan_of_mem_adjoin u v r hr
  obtain ⟨d₂, hd₂⟩ := exists_monoSpan_of_mem_adjoin u v s hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hπrs, div_zero, w.map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hπ' : w r = exp (-1) * w s := by
    rw [← hπ, hπrs, map_div₀, div_mul_cancel₀ _ ((Valuation.ne_zero_iff w).2 hs0)]
  have key : ∀ (m : ℕ) (g : SliceField F₀), g ∈ monoSpan k₁ u v m → g ≠ 0 →
      -(w g).log ≤ ((n * m : ℕ) : ℤ) := fun m g hg hg0 =>
    neg_log_le_of_ord w (n * m) g hg0 fun e he =>
      ord_le_degree_mul w hk u v n cf hcdeg hrel m g hg (max d₁ d₂) r s
        (monoSpan_mono u v (le_max_left _ _) hd₁) (monoSpan_mono u v (le_max_right _ _) hd₂) hs0
        hπ' e he
  have hnN : (n : ℤ) ≤ 2 * N := by exact_mod_cast hn
  have hP : placeP F₀ w ≤ 4 * N := by
    have hlog : ∀ l, (w (t l)).log = chartExp sR sY sZ l 0 * (w (x 0)).log +
        chartExp sR sY sZ l 1 * (w (x 1)).log + chartExp sR sY sZ l 2 * (w (x 2)).log := fun l => by
      rw [ht, chartCoord, lmono_val w (sliceCoord F₀) hc, log_exp]
    have h := chart_pole_arith sR sY sZ i (w (x 0)).log (w (x 1)).log (w (x 2)).log (2 * N)
      (fun l => by
        rw [← hlog l]
        refine ⟨?_, (lmono_le_one_iff w (sliceCoord F₀) hc _).1 (hle l) |> fun h => by
          rw [hlog l]; exact h⟩
        have h1 := key 1 (t l) (htV1 l) (ht0 l)
        rw [Nat.mul_one] at h1
        omega)
      (by rw [← hlog i, hkv _ hzk (ht0 i), log_one])
    show max (max 0 (w (x 1)).log) (max (max 0 (w (x 0)).log) (max 0 (w (x 2)).log)) ≤ 4 * N
    omega
  have hHb : placeH F F₀ w ≤ 4 * N ^ 2 := by
    set Hp := polyH K F with hHp
    have hsupp : ∀ d ∈ Hp.support, d 1 + d 2 + d 3 ≤ N :=
      HFree6812.support_bound_of_weighted Hp N ((RCN234.wt_polyH_le _ F N hN).trans (Nat.sub_le _ _))
    set M := t 0 ^ (if sR then N else 0) * t 1 ^ (if sY then N else 0) *
      t 2 ^ (if sZ then N else 0) with hM
    have hmono : ∀ a b c : ℕ, a + b + c ≤ N → M * (x 0 ^ a * x 1 ^ b * x 2 ^ c) =
        t 0 ^ chartNu sR sY sZ N a b c 0 * t 1 ^ chartNu sR sY sZ N a b c 1 *
          t 2 ^ chartNu sR sY sZ N a b c 2 := fun a b c h =>
      (chartNu_mono x hc sR sY sZ N a b c h).symm
    have hclear : M * sliceProj F₀ Hp ∈ monoSpan k₁ u v (2 * N) := by
      rw [← aeval_slice, aeval_def, eval₂_eq', Finset.mul_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hd' := hsupp d hd
      have hprod : ∏ l : Fin 4, (Fin.cons X0 x : Fin 4 → SliceField F₀) l ^ d l =
          X0 ^ d 0 * (x 0 ^ d 1 * x 1 ^ d 2 * x 2 ^ d 3) := by
        rw [Fin.prod_univ_four]
        simp only [mul_assoc]
        rfl
      rw [hprod, show M * (algebraMap K (SliceField F₀) (Hp.coeff d) *
          (X0 ^ d 0 * (x 0 ^ d 1 * x 1 ^ d 2 * x 2 ^ d 3))) =
          (algebraMap K (SliceField F₀) (Hp.coeff d) * X0 ^ d 0) *
            (M * (x 0 ^ d 1 * x 1 ^ d 2 * x 2 ^ d 3)) by ring, hmono _ _ _ hd']
      refine hmulk _ (mul_mem (k₁.algebraMap_mem _) (pow_mem hX0k _)) ?_
      have h0 := chartNu_le sR sY sZ N (d 1) (d 2) (d 3) hd' 0
      have h1 := chartNu_le sR sY sZ N (d 1) (d 2) (d 3) hd' 1
      have h2 := chartNu_le sR sY sZ N (d 1) (d 2) (d 3) hd' 2
      refine monoSpan_mono u v ?_ (mul_mem_monoSpan u v (mul_mem_monoSpan u v
        (pow_mem_monoSpan u v (htV 0) _) (pow_mem_monoSpan u v (htV 1) _))
        (pow_mem_monoSpan u v (htV 2) _))
      fin_cases i <;> simp <;> omega
    have hM0 : M ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ht0 0)) (pow_ne_zero _ (ht0 1)))
        (pow_ne_zero _ (ht0 2))
    have hM1 : w M ≤ 1 := by
      rw [hM, map_mul, map_mul, map_pow, map_pow, map_pow]
      exact mul_le_one' (mul_le_one' (pow_le_one' (hle 0) _) (pow_le_one' (hle 1) _))
        (pow_le_one' (hle 2) _)
    have h5 := key (2 * N) _ hclear (mul_ne_zero hM0 hH)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff w).2 hM0) ((Valuation.ne_zero_iff w).2 hH)] at h5
    have h6 : (w M).log ≤ 0 := by
      rw [← log_exp (0 : ℤ)]
      exact (log_le_log ((Valuation.ne_zero_iff w).2 hM0) (by simp)).2 (by simpa using hM1)
    have h7 : ((n * (2 * N) : ℕ) : ℤ) ≤ 4 * N ^ 2 := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℤ) N]
    show max 0 (-(w (sliceProj F₀ Hp)).log) ≤ 4 * N ^ 2
    have h8 : (0 : ℤ) ≤ 4 * N ^ 2 := by positivity
    omega
  intro m hm hmle
  refine natCast_ne_zero_of_lt m hm ?_
  have h9 : (N : ℤ) ≤ N ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) N
  have h10 : (m : ℤ) ≤ 4 * N ^ 2 := hmle.trans (max_le (hP.trans (by omega)) hHb)
  have h11 : ((4 * N ^ 2 : ℕ) : ℤ) < 2130706433 := by exact_mod_cast hNp
  push_cast at h11
  have h12 : (m : ℤ) < 2130706433 := lt_of_le_of_lt h10 h11
  exact_mod_cast h12
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial WithZero HFree6812
open RCN313
variable {K : Type} [Field K] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
theorem Chart.chartKrull_of_chartNoether [CharP K 2130706433] (N : ℕ) (hN9 : N ≤ 9678)
    (hX : AlgebraicIndependent K fun _ : Unit => sliceProj F₀ (MvPolynomial.X 0))
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) (hno : ChartNoether F₀ N sR sY sZ) :
    ChartKrull F₀ sR sY sZ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, hind, hint, hdeg⟩ := hno
  intro x hx
  have hset : Set.range ![s₁, s₂] = {s₁, s₂} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hset] at hint hdeg
  obtain ⟨x0, hx0⟩ : ∃ x0 : xField F₀, (x0 : SliceField F₀) = sliceProj F₀ (MvPolynomial.X 0) :=
    ⟨⟨_, IntermediateField.mem_adjoin_simple_self K _⟩, rfl⟩
  have hsmem : ∀ j, ![s₁, s₂] j ∈ chartRing F₀ sR sY sZ := Fin.forall_fin_two.2 ⟨hs₁, hs₂⟩
  have hchar : CharP (IntermediateField.adjoin (xField F₀) (Set.range ![s₁, s₂])) 2130706433 :=
    charP_of_injective_algebraMap (algebraMap K _).injective _
  obtain ⟨hfin, hsep⟩ := finite_separable_of_natDegree_le 2130706433 (3 * N) (by omega) hdeg
    (chartCoord F₀ sR sY sZ) (fun E hE ht => by
      have hk : ∀ c : xField F₀, algebraMap (xField F₀) (SliceField F₀) c ∈ E := fun c => by
        rw [IsScalarTower.algebraMap_apply (xField F₀)
          (IntermediateField.adjoin (xField F₀) (Set.range ![s₁, s₂])) (SliceField F₀)]
        exact hE _
      exact chart_gen F₀ hc sR sY sZ E (fun a => hk (algebraMap K (xField F₀) a)) (hx0 ▸ hk x0) ht)
  have hxint := isIntegral_of_noether ![s₁, s₂] hind x fun w hnorm hle hunit => by
    obtain ⟨j, hj⟩ := hunit
    refine hx w ⟨hnorm, fun a ha => hle a (hint a ha), ![s₁, s₂] j, hsmem j, ?_,
      fun a ha => hj a ?_⟩
    · have h1 := hX.sumElim_of_tower (S := xField F₀) (y := fun _ : Unit => ![s₁, s₂] j)
        (by rintro _ ⟨u, rfl⟩; exact ⟨x0, hx0⟩)
        (hind.comp (fun _ : Unit => j) (Function.injective_of_subsingleton _))
      have h2 := h1.comp ![Sum.inl (), Sum.inr ()] (by decide)
      have hfun : (Sum.elim (fun _ : Unit => ![s₁, s₂] j)
          fun _ : Unit => sliceProj F₀ (MvPolynomial.X 0)) ∘ ![Sum.inl (), Sum.inr ()] =
          ![![s₁, s₂] j, sliceProj F₀ (MvPolynomial.X 0)] := by
        funext i
        fin_cases i <;> rfl
      rwa [hfun] at h2
    · have hle' : unitField F₀ (![s₁, s₂] j) ≤
          (IntermediateField.adjoin (xField F₀) {![s₁, s₂] j}).restrictScalars K :=
        IntermediateField.adjoin_le_iff.2 (by
          rintro _ (rfl | rfl)
          · exact IntermediateField.subset_adjoin (xField F₀) _ (Set.mem_singleton _)
          · exact hx0 ▸ (IntermediateField.adjoin (xField F₀) {![s₁, s₂] j}).algebraMap_mem x0)
      exact hle' ha
  have hPle : Algebra.adjoin (xField F₀) (Set.range ![s₁, s₂]) ≤ chartRing F₀ sR sY sZ :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hsmem i)
  obtain ⟨q, hqm, hq0⟩ := hxint
  refine ⟨q.map (Subalgebra.inclusion hPle).toRingHom, hqm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hq0
theorem chart_krull [CharP K 2130706433] (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N)
    (hN9 : N ≤ 9678) (hH : sliceProj F₀ (polyH K F₀) ≠ 0) (hc : ∀ j, sliceCoord F₀ j ≠ 0)
    (sR sY sZ : Bool) : ChartKrull F₀ sR sY sZ :=
  Chart.chartKrull_of_chartNoether F₀ N hN9
    (AlgebraicIndependent.sumElim_iff.1 (Chart.algebraicIndependent_YZ_X F₀ hH)).1 hc sR sY sZ
    (chart_noether F₀ N hN hH hc sR sY sZ)
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
section Ring
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L]
theorem local_sum_le (hO : DivisorChain O) {s φ : O} (hs : s ≠ 0) (hφ : φ ≠ 0)
    (hdisj : ∀ P : PrimeDivisor O, φ ∈ P.ideal → s ∉ P.ideal)
    {ι : Type*} (sB : Finset ι) (P : ι → PrimeDivisor O) (hP : Set.InjOn P sB) (m n : ι → ℕ)
    (hm : ∀ i ∈ sB, m i ≤ div L φ (P i))
    (hn : ∀ i ∈ sB, (n i : ℕ∞) ≤ Module.length O (O ⧸ ((P i).ideal ⊔ Ideal.span {s})))
    {κ : Type*} (tD : Finset κ) (z : κ → ℕ) (R : PrimeDivisor O → κ → Prop)
    (hR : ∀ Q Q' j, R Q j → R Q' j → Q = Q')
    (hz : ∀ Q : PrimeDivisor O, s ∈ Q.ideal → div L s Q = 1 ∧ ∃ j ∈ tD, R Q j ∧
      Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {φ})) ≤ (z j : ℕ∞)) :
    ∑ i ∈ sB, m i * n i ≤ ∑ j ∈ tD, z j := by
  classical
  have h1 : ((∑ i ∈ sB, m i * n i : ℕ) : ℕ∞) ≤
      (div L φ).sum fun Q e => (e : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {s})) := by
    rw [Nat.cast_sum]
    calc ∑ i ∈ sB, ((m i * n i : ℕ) : ℕ∞)
        ≤ ∑ i ∈ sB, (div L φ (P i) : ℕ∞) *
            Module.length O (O ⧸ ((P i).ideal ⊔ Ideal.span {s})) :=
          Finset.sum_le_sum fun i hi => by
            rw [Nat.cast_mul]
            exact mul_le_mul' (Nat.cast_le.mpr (hm i hi)) (hn i hi)
      _ = ∑ Q ∈ sB.image P, (div L φ Q : ℕ∞) *
            Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {s})) :=
          (Finset.sum_image (f := fun Q => (div L φ Q : ℕ∞) *
            Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {s}))) hP).symm
      _ ≤ ∑ Q ∈ sB.image P ∪ (div L φ).support, (div L φ Q : ℕ∞) *
            Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {s})) :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = ∑ Q ∈ (div L φ).support, (div L φ Q : ℕ∞) *
            Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {s})) := by
          refine (Finset.sum_subset Finset.subset_union_right fun Q _ hQ => ?_).symm
          rw [Finsupp.notMem_support_iff.mp hQ, Nat.cast_zero, zero_mul]
      _ = _ := rfl
  rw [sum_div_length_quotient_comm L hO hs hφ hdisj] at h1
  have hmem : ∀ Q ∈ (div L s).support, s ∈ Q.ideal := fun Q hQ => (mem_support_div L hs Q).mp hQ
  have hk : ∀ Q : {Q // Q ∈ (div L s).support}, ∃ j ∈ tD, R Q.1 j ∧
      Module.length O (O ⧸ (Q.1.ideal ⊔ Ideal.span {φ})) ≤ (z j : ℕ∞) := fun Q =>
    (hz Q.1 (hmem Q.1 Q.2)).2
  choose k hk1 hk2 hk3 using hk
  have h2 : ((div L s).sum fun Q e =>
      (e : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {φ}))) ≤
      ((∑ j ∈ tD, z j : ℕ) : ℕ∞) := by
    calc ((div L s).sum fun Q e => (e : ℕ∞) * Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {φ})))
        = ∑ Q ∈ (div L s).support.attach, (div L s Q.1 : ℕ∞) *
            Module.length O (O ⧸ (Q.1.ideal ⊔ Ideal.span {φ})) :=
          (Finset.sum_attach (div L s).support fun Q => (div L s Q : ℕ∞) *
            Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {φ}))).symm
      _ ≤ ∑ Q ∈ (div L s).support.attach, (z (k Q) : ℕ∞) := Finset.sum_le_sum fun Q _ => by
          rw [(hz Q.1 (hmem Q.1 Q.2)).1, Nat.cast_one, one_mul]
          exact hk3 Q
      _ = ∑ j ∈ (div L s).support.attach.image k, (z j : ℕ∞) :=
          (Finset.sum_image (f := fun j => (z j : ℕ∞)) (g := k) fun Q _ Q' _ hQQ' => by
            have h' : R Q'.1 (k Q) := by
              rw [hQQ']
              exact hk2 Q'
            exact Subtype.ext (hR Q.1 Q'.1 (k Q) (hk2 Q) h')).symm
      _ ≤ ∑ j ∈ tD, (z j : ℕ∞) := Finset.sum_le_sum_of_subset fun j hj => by
          obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hj
          exact hk1 Q
      _ = ((∑ j ∈ tD, z j : ℕ) : ℕ∞) := (Nat.cast_sum _ _).symm
  exact Nat.cast_le.mp (h1.trans h2)
end Ring
section Sums
variable {α : Type*}
theorem sum_le_finsum_mem (t : Finset α) (A : Set α) (n : α → ℕ) (ht : ∀ a ∈ t, a ∈ A)
    (hfin : (A ∩ Function.support n).Finite) : ∑ a ∈ t, n a ≤ ∑ᶠ a ∈ A, n a := by
  classical
  calc ∑ a ∈ t, n a = ∑ a ∈ t.filter (fun a => n a ≠ 0), n a :=
        (Finset.sum_filter_ne_zero t).symm
    _ ≤ ∑ a ∈ hfin.toFinset, n a := Finset.sum_le_sum_of_subset fun a ha => by
        rw [Finset.mem_filter] at ha
        exact hfin.mem_toFinset.mpr ⟨ht a ha.1, ha.2⟩
    _ = ∑ᶠ a ∈ A, n a :=
        (finsum_mem_eq_finite_toFinset_sum n hfin).symm.trans (finsum_mem_inter_support n A)
theorem finsum_mem_eq_sum_ite (A : Set α) (n : α → ℕ) (V : Finset α) (hV : ∀ a, n a ≠ 0 → a ∈ V) :
    ∑ᶠ a ∈ A, n a = ∑ a ∈ V, (open Classical in if a ∈ A then n a else 0) := by
  classical
  rw [← Finset.sum_filter]
  refine finsum_mem_eq_sum_of_inter_support_eq n ?_
  ext a
  simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨hV a h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
theorem sum_finsum_mem_le {β : Type*} (Q : Finset β) (A : β → Set α) (n : α → ℕ) (V : Finset α)
    (hV : ∀ a, n a ≠ 0 → a ∈ V)
    (hdisj : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ a, a ∈ A q → a ∈ A q' → q = q') :
    ∑ q ∈ Q, ∑ᶠ a ∈ A q, n a ≤ ∑ a ∈ V, n a := by
  classical
  calc ∑ q ∈ Q, ∑ᶠ a ∈ A q, n a = ∑ q ∈ Q, ∑ a ∈ V, (if a ∈ A q then n a else 0) :=
        Finset.sum_congr rfl fun q _ => finsum_mem_eq_sum_ite (A q) n V hV
    _ = ∑ a ∈ V, ∑ q ∈ Q, (if a ∈ A q then n a else 0) := Finset.sum_comm
    _ ≤ ∑ a ∈ V, n a := Finset.sum_le_sum fun a _ => by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        calc (Q.filter fun q => a ∈ A q).card * n a ≤ 1 * n a :=
              Nat.mul_le_mul_right _ (Finset.card_le_one.mpr fun q hq q' hq' =>
                hdisj q (Finset.mem_filter.mp hq).1 q' (Finset.mem_filter.mp hq').1 a
                  (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hq').2)
          _ = n a := one_mul _
end Sums
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
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Local
theorem divisorChain_of_primeChain {O : Type*} [CommRing O] [IsDomain O] (h : PrimeChain O) :
    DivisorChain O := fun P Q hQ hPQ =>
  h P.ideal Q P.isPrime hQ (Ideal.ne_bot_of_height_eq_one P.height_eq_one) hPQ
variable {A : Type*} [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  [IsFractionRing A L]
theorem mem_pointRing_iff (q : Ideal A) [q.IsPrime] (x : L) :
    x ∈ pointRing L q ↔ ∃ a s : A, s ∉ q ∧ x * algebraMap A L s = algebraMap A L a := by
  have hs0 : ∀ s : A, s ∉ q → algebraMap A L s ≠ 0 := fun s hs h0 =>
    hs (by rw [(map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h0]; exact q.zero_mem)
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨a, s, hs, inv_mul_cancel_right₀ (hs0 s hs) _⟩
  · rintro ⟨a, s, hs, h⟩
    exact ⟨a, s, hs, by rw [← h, mul_inv_cancel_right₀ (hs0 s hs)]⟩
theorem pointRing_isNoetherianRing [IsNoetherianRing A] (q : Ideal A) [q.IsPrime] :
    IsNoetherianRing (pointRing L q) :=
  IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
theorem pointRing_isIntegrallyClosed [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] :
    IsIntegrallyClosed (pointRing L q) :=
  isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
theorem pointRing_primeChain (h : PrimeChain A) (q : Ideal A) [q.IsPrime] :
    PrimeChain (pointRing L q) := by
  intro p p' hp hp' hp0 hlt
  have hmap : ∀ J : Ideal (pointRing L q), (J.under A).map (algebraMap A (pointRing L q)) = J :=
    IsLocalization.map_under q.primeCompl _
  have h3 : p.under A ≠ ⊥ := fun h0 => hp0 (by rw [← hmap p, h0, Ideal.map_bot])
  have h4 : p.under A < p'.under A :=
    lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => hlt.ne (by rw [← hmap p, ← hmap p', heq])
  have := h _ _ (hp.under A) (hp'.under A) h3 h4
  exact IsLocalization.isMaximal_of_isMaximal_under q.primeCompl (pointRing L q) p'
theorem pointRing_residue {E : Type*} [Field E] [Algebra E A] [Algebra E L] [IsScalarTower E A L]
    (q : Ideal A) [q.IsMaximal] (hq : Function.Bijective (algebraMap E (A ⧸ q))) :
    ∃ φ : pointRing L q →ₐ[E] E, Function.Surjective φ ∧ ∀ x, φ x = 0 ↔ ¬IsUnit x := by
  let e : E ≃+* A ⧸ q := RingEquiv.ofBijective (algebraMap E (A ⧸ q)) hq
  let g : A →+* E := (e.symm : A ⧸ q →+* E).comp (Ideal.Quotient.mk q)
  have hg0 : ∀ a, g a = 0 ↔ a ∈ q := fun a => by
    change e.symm (Ideal.Quotient.mk q a) = 0 ↔ a ∈ q
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hgu : ∀ s : q.primeCompl, IsUnit (g s) := fun s =>
    isUnit_iff_ne_zero.mpr fun h => s.2 ((hg0 _).mp h)
  let φ₀ : pointRing L q →+* E := IsLocalization.lift hgu
  have hφ₀ : ∀ a : A, φ₀ (algebraMap A (pointRing L q) a) = g a := IsLocalization.lift_eq hgu
  have hgE : ∀ c : E, g (algebraMap E A c) = c := fun c => by
    change e.symm (Ideal.Quotient.mk q (algebraMap E A c)) = c
    exact e.symm_apply_apply c
  have hcomm : ∀ c : E, φ₀ (algebraMap E (pointRing L q) c) = c := fun c => by
    have h1 : algebraMap E (pointRing L q) c = algebraMap A (pointRing L q) (algebraMap E A c) :=
      Subtype.ext (IsScalarTower.algebraMap_apply E A L c)
    rw [h1, hφ₀, hgE]
  let φ : pointRing L q →ₐ[E] E := { φ₀ with commutes' := hcomm }
  refine ⟨φ, fun c => ⟨algebraMap E _ c, hcomm c⟩, fun x => ⟨fun h hu => ?_, fun hnu => ?_⟩⟩
  · have h1 := hu.map φ
    rw [h] at h1
    exact not_isUnit_zero h1
  · obtain ⟨a, s, hs, hxs⟩ := (mem_pointRing_iff L q x).mp x.2
    have hxs' : x * algebraMap A (pointRing L q) s = algebraMap A (pointRing L q) a :=
      Subtype.ext hxs
    have ha : a ∈ q := by
      by_contra ha
      have hu : IsUnit (algebraMap A (pointRing L q) a) :=
        IsLocalization.map_units _ (⟨a, ha⟩ : q.primeCompl)
      rw [← hxs'] at hu
      exact hnu (isUnit_of_mul_isUnit_left hu)
    have h1 : φ₀ x * g s = g a := by rw [← hφ₀ s, ← map_mul, hxs', hφ₀]
    rw [(hg0 a).mpr ha] at h1
    exact (mul_eq_zero.mp h1).resolve_right fun h => hs ((hg0 s).mp h)
omit [IsDomain A] [IsFractionRing A L] in
theorem Surf.mem_centre (v : Valuation L ℤᵐ⁰) (h : ∀ a : A, v (algebraMap A L a) ≤ 1) (a : A) :
    a ∈ centre L v h ↔ v (algebraMap A L a) < 1 :=
  Iff.rfl
omit [IsDomain A] [IsFractionRing A L] in
theorem Surf.centre_isPrime (v : Valuation L ℤᵐ⁰) (h : ∀ a : A, v (algebraMap A L a) ≤ 1) :
    (centre L v h).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : A) ∈ centre L v h := htop ▸ Submodule.mem_top
    rw [Surf.mem_centre, map_one, map_one] at h1
    exact lt_irrefl _ h1
  · rw [Surf.mem_centre, map_mul, map_mul] at hxy
    by_contra hne
    rw [not_or, Surf.mem_centre, Surf.mem_centre, not_lt, not_lt] at hne
    have hx : v (algebraMap A L x) = 1 := le_antisymm (h x) hne.1
    have hy : v (algebraMap A L y) = 1 := le_antisymm (h y) hne.2
    rw [hx, hy, mul_one] at hxy
    exact lt_irrefl _ hxy
theorem Surf.centre_ne_bot (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v)
    (h : ∀ a : A, v (algebraMap A L a) ≤ 1) : centre L v h ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hv (exp (-1))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : v (algebraMap A L b) ≠ 0 := (Valuation.ne_zero_iff _).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.ne_zero hb))
  rw [map_div₀, div_eq_iff hb0] at hx
  have ha : a ∈ centre L v h := by
    rw [Surf.mem_centre, hx]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (h b)) (exp_lt_one_iff.mpr (by norm_num))
  intro hbot
  rw [hbot, Ideal.mem_bot] at ha
  rw [ha, map_zero, map_zero] at hx
  exact exp_ne_zero ((mul_eq_zero.mp hx.symm).resolve_right hb0)
theorem exists_primeDivisor_of_centre [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : PrimeChain A) (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v)
    (h : ∀ a : A, v (algebraMap A L a) ≤ 1) (hmax : ¬(centre L v h).IsMaximal) :
    ∃ P : PrimeDivisor A, P.ideal = centre L v h ∧ P.valuation L = v := by
  have hprime := Surf.centre_isPrime L v h
  have hne := Surf.centre_ne_bot L v hv h
  have hheight : (centre L v h).height = 1 := by
    refine le_antisymm ?_ ?_
    · change (centre L v h).height ≤ ((1 : ℕ) : ℕ∞)
      rw [Ideal.height_le_iff]
      intro p hp hlt
      have hp0 : p = ⊥ := by
        by_contra hp0
        exact hmax (hA p _ hp hprime hp0 hlt)
      rw [hp0, Ideal.height_bot, Nat.cast_one]
      exact zero_lt_one
    · have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
      rwa [Ideal.height_bot, zero_add] at h1
  refine ⟨⟨_, hprime, hheight⟩, rfl, ?_⟩
  exact (PrimeDivisor.valuation_unique L ⟨_, hprime, hheight⟩ v ⟨hv, h, fun a => Iff.rfl⟩).symm
end Local
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] {sR sY sZ : Bool}
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
variable {N p : ℕ} [CharP E p]
theorem Surf.chart_le_normalChart :
    surfaceChartRing G sR sY sZ ≤ normalChart G sR sY sZ := fun a ha =>
  isIntegral_algebraMap (x := (⟨a, ha⟩ : surfaceChartRing G sR sY sZ))
theorem Surf.exists_normalization (hN : SurfaceNoether G sR sY sZ N) :
    ∃ s : Fin 2 → RCN002.CoordinateField E G, AlgebraicIndependent E s ∧ (∀ j, s j ∈ surfaceChartRing G sR sY sZ) ∧
      (∀ x, x ∈ normalChart G sR sY sZ ↔ IsIntegral (Algebra.adjoin E (Set.range s)) x) ∧
      ∀ a : RCN002.CoordinateField E G, ∃ Q : Polynomial (IntermediateField.adjoin E (Set.range s)),
        Q ≠ 0 ∧ Q.natDegree ≤ 3 * N ∧ Polynomial.aeval a Q = 0 := by
  obtain ⟨s₁, hs₁, s₂, hs₂, hind, hint, hdeg⟩ := hN
  have hset : Set.range ![s₁, s₂] = {s₁, s₂} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hset] at hint hdeg
  have hsR : ∀ j, ![s₁, s₂] j ∈ surfaceChartRing G sR sY sZ := Fin.forall_fin_two.mpr ⟨hs₁, hs₂⟩
  exact ⟨![s₁, s₂], hind, hsR, Surf.mem_integralClosure_iff hsR hint, hdeg⟩
theorem Surf.finite_separable (hp : 3 * N < p) {s : Fin 2 → RCN002.CoordinateField E G}
    (hdeg : ∀ a : RCN002.CoordinateField E G, ∃ Q : Polynomial (IntermediateField.adjoin E (Set.range s)),
      Q ≠ 0 ∧ Q.natDegree ≤ 3 * N ∧ Polynomial.aeval a Q = 0) :
    FiniteDimensional (IntermediateField.adjoin E (Set.range s)) (RCN002.CoordinateField E G) ∧
      Algebra.IsSeparable (IntermediateField.adjoin E (Set.range s)) (RCN002.CoordinateField E G) := by
  have hchar : CharP (IntermediateField.adjoin E (Set.range s)) p :=
    charP_of_injective_algebraMap (algebraMap E _).injective p
  refine Chart.finite_separable_of_natDegree_le p (3 * N) hp hdeg (coordinate E G)
    fun E' hE' ht z => ?_
  have hE : ∀ a : E, algebraMap E (RCN002.CoordinateField E G) a ∈ E' := fun a => by
    rw [IsScalarTower.algebraMap_apply E (IntermediateField.adjoin E (Set.range s)) (RCN002.CoordinateField E G)]
    exact hE' _
  have hle : IntermediateField.adjoin E (Set.range (coordinate E G)) ≤
      E'.toIntermediateField hE :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact ht i)
  exact hle (RCN002.adjoin_coordinates_eq_top E G ▸ IntermediateField.mem_top)
theorem normalChart_isFractionRing (hN : SurfaceNoether G sR sY sZ N) :
    IsFractionRing (normalChart G sR sY sZ) (RCN002.CoordinateField E G) := by
  obtain ⟨s, -, -, hC, hdeg⟩ := Surf.exists_normalization hN
  exact Surf.closure_isFractionRing hC fun a => by
    obtain ⟨Q, hQ0, -, hQa⟩ := hdeg a
    exact ⟨Q, hQ0, hQa⟩
theorem normalChart_isIntegrallyClosed (hN : SurfaceNoether G sR sY sZ N) :
    IsIntegrallyClosed (normalChart G sR sY sZ) := by
  obtain ⟨s, -, -, hC, hdeg⟩ := Surf.exists_normalization hN
  exact Surf.closure_isIntegrallyClosed hC fun a => by
    obtain ⟨Q, hQ0, -, hQa⟩ := hdeg a
    exact ⟨Q, hQ0, hQa⟩
theorem normalChart_finiteType (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p) :
    Algebra.FiniteType E (normalChart G sR sY sZ) := by
  obtain ⟨s, hs, -, hC, hdeg⟩ := Surf.exists_normalization hN
  obtain ⟨_, _⟩ := Surf.finite_separable hp hdeg
  exact Surf.closure_finiteType hC hs
theorem normalChart_isNoetherianRing (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p) :
    IsNoetherianRing (normalChart G sR sY sZ) := by
  have := normalChart_finiteType hN hp
  exact Algebra.FiniteType.isNoetherianRing E _
theorem normalChart_primeChain (hN : SurfaceNoether G sR sY sZ N) :
    PrimeChain (normalChart G sR sY sZ) := by
  obtain ⟨s, hs, -, hC, -⟩ := Surf.exists_normalization hN
  exact Surf.closure_primeChain hC hs
theorem normalChart_residue [IsAlgClosed E] (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (q : Ideal (normalChart G sR sY sZ)) [q.IsMaximal] :
    Function.Bijective (algebraMap E (normalChart G sR sY sZ ⧸ q)) := by
  have := normalChart_finiteType hN hp
  exact Surf.residue_bijective q
theorem PrimeDivisor.surfaceDivisor (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (P : PrimeDivisor (normalChart G sR sY sZ)) :
    SurfaceDivisor G sR sY sZ (P.valuation (RCN002.CoordinateField E G)) := by
  have := normalChart_isFractionRing hN
  have := normalChart_isIntegrallyClosed hN
  have := normalChart_isNoetherianRing hN hp
  obtain ⟨s, hs, hsR, hC, -⟩ := Surf.exists_normalization hN
  have hPp := P.isPrime
  obtain ⟨j, hj⟩ := Surf.closure_exists_disjoint hC hs P.ideal P.height_eq_one
  have hsC : Algebra.adjoin E {s j} ≤ normalChart G sR sY sZ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Surf.chart_le_normalChart (hsR j)))
  refine ⟨P.valuation_surjective _,
    fun a ha => P.valuation_le_one _ ⟨a, Surf.chart_le_normalChart ha⟩, s j, hsR j,
    hs.transcendental j, ?_⟩
  exact Surf.trivial_on_adjoin_singleton _ (s j) (fun a ha => P.valuation_le_one _ ⟨a, hsC ha⟩)
    fun a ha hlt => congrArg Subtype.val
      (hj ⟨a, hsC ha⟩ ((P.valuation_lt_one_iff _ ⟨a, hsC ha⟩).mp hlt) ha)
theorem SurfaceDivisor.exists_primeDivisor (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰} (h : SurfaceDivisor G sR sY sZ nu) :
    ∃ P : PrimeDivisor (normalChart G sR sY sZ), P.valuation (RCN002.CoordinateField E G) = nu ∧
      ∀ x : normalChart G sR sY sZ, x ∈ P.ideal ↔ nu (x : RCN002.CoordinateField E G) < 1 := by
  have := normalChart_isFractionRing hN
  have := normalChart_isIntegrallyClosed hN
  have := normalChart_isNoetherianRing hN hp
  have := normalChart_finiteType hN hp
  have hle : ∀ a : normalChart G sR sY sZ,
      nu (algebraMap (normalChart G sR sY sZ) (RCN002.CoordinateField E G) a) ≤ 1 := fun a =>
    Surf.valuation_le_one_of_isIntegral (A := surfaceChartRing G sR sY sZ) nu
      (fun b => h.le_one b b.2) a.2
  obtain ⟨t, ht, htr, ht1⟩ := h.nonconst
  have hmax := Surf.not_isMaximal_centre nu hle ⟨t, Surf.chart_le_normalChart ht⟩ htr ht1
  obtain ⟨P, hP, hPv⟩ := exists_primeDivisor_of_centre (RCN002.CoordinateField E G) (normalChart_primeChain hN) nu
    h.surjective hle hmax
  exact ⟨P, hPv, fun x => by rw [hP]; exact Iff.rfl⟩
theorem exists_surfacePoint [IsAlgClosed E] (hN : SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (q : Ideal (normalChart G sR sY sZ)) [q.IsMaximal] :
    ∃ pt : SurfacePoint G, ∀ x : RCN002.CoordinateField E G, x ∈ pt.ring ↔
      ∃ a s : normalChart G sR sY sZ, s ∉ q ∧ x * (s : RCN002.CoordinateField E G) = a := by
  have := normalChart_isFractionRing hN
  have := normalChart_isIntegrallyClosed hN
  have := normalChart_isNoetherianRing hN hp
  have hmem := mem_pointRing_iff (RCN002.CoordinateField E G) q
  obtain ⟨φ, -, hφ⟩ := pointRing_residue (RCN002.CoordinateField E G) q (normalChart_residue hN hp q)
  refine ⟨{ ring := (pointRing (RCN002.CoordinateField E G) q).restrictScalars E
            isNoetherianRing := pointRing_isNoetherianRing (RCN002.CoordinateField E G) q
            isIntegrallyClosed := pointRing_isIntegrallyClosed (RCN002.CoordinateField E G) q
            isFractionRing := (inferInstance : IsFractionRing (pointRing (RCN002.CoordinateField E G) q) (RCN002.CoordinateField E G))
            primeChain := pointRing_primeChain (RCN002.CoordinateField E G) (normalChart_primeChain hN) q
            residue := ⟨φ, hφ⟩
            chart := ⟨sR, sY, sZ, fun a ha => (hmem a).mpr ⟨⟨a, ha⟩, 1, q.one_notMem, mul_one a⟩,
              fun x hx => ?_⟩ }, hmem⟩
  obtain ⟨a, s, hs, hxs⟩ := (hmem x).mp hx
  have hs0 : (s : RCN002.CoordinateField E G) ≠ 0 := fun h0 => hs (by
    rw [show s = 0 from Subtype.ext h0]
    exact q.zero_mem)
  refine ⟨s, s.2, hs0, (hmem _).mpr ⟨1, s, hs, inv_mul_cancel₀ hs0⟩, ?_⟩
  have h2 : x * (s : RCN002.CoordinateField E G) = a := hxs
  rw [h2]
  exact a.2
namespace SurfacePoint
variable (q : SurfacePoint G)
theorem isLocalRing : IsLocalRing q.ring := by
  obtain ⟨φ, hφ⟩ := q.residue
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, ← hφ] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]
theorem divisorChain : DivisorChain q.ring :=
  divisorChain_of_primeChain q.primeChain
theorem surfaceDivisor (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (P : PrimeDivisor q.ring) :
    SurfaceDivisor G q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 (P.valuation (RCN002.CoordinateField E G)) := by
  obtain ⟨hle, hfrac⟩ := q.chartOf_spec
  have hN' := hN q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2
  have := normalChart_isFractionRing hN'
  have := normalChart_isIntegrallyClosed hN'
  have := normalChart_isNoetherianRing hN' hp
  have hPp := P.isPrime
  obtain ⟨Q', hQ'p, hQ'h, hQ'⟩ := Surf.exists_under_of_fractions hle hfrac P.ideal
  have hval : P.valuation (RCN002.CoordinateField E G) =
      PrimeDivisor.valuation (RCN002.CoordinateField E G) ⟨Q', hQ'p, hQ'h.trans P.height_eq_one⟩ :=
    PrimeDivisor.valuation_unique (RCN002.CoordinateField E G) ⟨Q', hQ'p, hQ'h.trans P.height_eq_one⟩
      (P.valuation (RCN002.CoordinateField E G))
      ⟨P.valuation_surjective _, fun a => P.valuation_le_one _ (Subalgebra.inclusion hle a),
        fun a => ((P.valuation_lt_one_iff _ (Subalgebra.inclusion hle a)).trans (hQ' a).symm)⟩
  rw [hval]
  exact PrimeDivisor.surfaceDivisor hN' hp _
end SurfacePoint
end Surface
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
section Component
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {E : Type} [Field E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime]
def LevelComponent (f : RCN002.CoordinateField E G) (c : E) : Type :=
  {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ // nu (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 ∧
    ∃ (C : Ideal (MvPolynomial (Fin 3) E)) (_ : C.IsPrime) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)),
      IsCurveOnSurface G C S ∧ S.val = nu ∧ C.height = 2}
namespace LevelComponent
variable {G} {f : RCN002.CoordinateField E G} {c : E} (B : LevelComponent G f c)
def val : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ := B.1
theorem val_lt_one : B.val (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 := B.2.1
def prime : Ideal (MvPolynomial (Fin 3) E) := B.2.2.choose
theorem isPrime : B.prime.IsPrime := B.2.2.choose_spec.choose
attribute [local instance] isPrime
def curve : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E B.prime) := B.2.2.choose_spec.choose_spec.choose
theorem isCurve : IsCurveOnSurface G B.prime B.curve := B.2.2.choose_spec.choose_spec.choose_spec.1
theorem curve_val : B.curve.val = B.val := B.2.2.choose_spec.choose_spec.choose_spec.2.1
theorem height : B.prime.height = 2 := B.2.2.choose_spec.choose_spec.choose_spec.2.2
theorem exists_transcendental [IsAlgClosed E] : ∃ j, Transcendental E (coordinate E B.prime j) :=
  RCN002.exists_transcendental_coordinate_of_ne_point_kernel E B.prime fun v heq => by
    have h := RCN072.pointKernel_height_ge_three E v
    rw [show RCN072.pointKernel E v = B.prime from heq.symm, B.height] at h
    exact absurd h (by norm_num)
def mult : ℕ := (-(B.val (f - algebraMap E (RCN002.CoordinateField E G) c)).log).toNat
end LevelComponent
attribute [local instance] LevelComponent.isPrime
variable {G}
def levelFlagSum {f : RCN002.CoordinateField E G} {c : E} (s : Finset (LevelComponent G f c))
    (T : ∀ B : LevelComponent G f c, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))) (W : FlagDegree) : ℤ :=
  ∑ B ∈ s, (B.mult : ℤ) * ∑ v ∈ T B, RCN204.flagPole v.val (coordinate E B.prime) W
variable (G)
structure LevelCount.Needs (g H : MvPolynomial (Fin 3) E) (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) : Prop where
  ne : f ≠ algebraMap E (RCN002.CoordinateField E G) c
  unit : ∀ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) →
    nu (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 →
      (∀ j, nu (coordinate E G j) = 1) ∧ nu (RCN002.coordinateEvaluation E G (pderiv 1 g)) = 1 ∧ nu (RCN002.coordinateEvaluation E G H) = 1 ∧ nu A₁ = 1
end
end Component
section Packet
noncomputable section
open scoped Classical BigOperators
open WithZero
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
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime
structure LevelNeeds (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1)) : Prop where
  component : ∀ g, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
    (Exch.moving P Q A g) c (Exch.function P SZ g)
  live : ∀ a ∈ active P SZ, (S a).val (Exch.moving P Q A a.1 -
    algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) = 1
  closure : ∀ a ∈ active P SZ, ∀ (q : SurfacePoint (Exch.component P a.1)) (hq : q.On (S a)),
    Exch.moving P Q A a.1 ∈ q.ring → q.level (Exch.moving P Q A a.1) c ≠ 0 →
      Module.Finite ((S a).image hq) (integralClosure ((S a).image hq) (RCN002.CoordinateField Ω a.2.1))
  levelClosure : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c)
    (q : SurfacePoint (Exch.component P g)) (hq : q.On B.curve),
    Module.Finite (B.curve.image hq) (integralClosure (B.curve.image hq) (RCN002.CoordinateField Ω B.prime))
def SectionBound (P : Packet x t y r) (scale z u v : ℕ) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω) : Prop :=
  ∀ (s : ∀ g, Finset (LevelComponent (Exch.component P g) (Exch.moving P Q A g) c))
    (T : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω B.prime))),
    (scale : ℤ) * (∑ g, levelFlagSum (s g) (T g) unitZFlag) ≤ (z : ℤ) ∧
      (scale : ℤ) * (∑ g, levelFlagSum (s g) (T g) unitYZFlag) ≤ (u : ℤ) ∧
      (scale : ℤ) * (∑ g, levelFlagSum (s g) (T g) unitAllFlag) ≤ (v : ℤ)
def LevelCount.Statement (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) : Prop :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  ∀ (Hf : FlagDegree) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1)),
    (∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) →
    ((Exch.flag SZ Hf).zOnly ≤ SZ.d * (cellCutR t y r).zOnly + 4 * (w + 1) * SZ.flag.zOnly ∧
      (Exch.flag SZ Hf).yz ≤ SZ.d * (cellCutR t y r).yz + 4 * (w + 1) * SZ.flag.yz ∧
      (Exch.flag SZ Hf).all ≤ SZ.d * (cellCutR t y r).all + 4 * (w + 1) * SZ.flag.all) →
    LevelNeeds P SZ Q A c S →
    SectionBound P scale z u v Q A c →
    (∀ j, sliceCoord P.F j ≠ 0) →
    (∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ) →
    ∀ N : ℕ, (∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N) → 3 * N < 2130706433 →
    Exch.TailOrder P hp SZ S →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A →
    LevelCount P hp SZ scale z u v (fun a => curveMoving (S a) (Exch.moving P Q A a.1) c)
      (Exch.lam P SZ Q A c (Exch.flag SZ Hf))
end
end Packet
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
open RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
section Embedding
variable {K : Type} [Field K] {E : Type} [Field E] [Algebra (RCN135.GenericField K) E]
  (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
theorem embedding_lmono (e : Fin 3 → ℤ) :
    HFree6812.sliceEmbedding D F₀ hker (lmono (sliceCoord F₀) e) = lmono (coordinate E D) e := by
  rw [lmono, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, psi_coord, psi_coord, psi_coord]
  rfl
theorem embedding_xField {a : SliceField F₀} (ha : a ∈ xField F₀) :
    HFree6812.sliceEmbedding D F₀ hker a ∈ (algebraMap E (RCN002.CoordinateField E D)).fieldRange := by
  induction ha using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx, psi_X0]
    exact ⟨_, rfl⟩
  | algebraMap a =>
    rw [psi_const]
    exact ⟨_, rfl⟩
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | inv x _ ihx =>
    rw [map_inv₀]
    exact inv_mem ihx
  | mul x y _ _ ihx ihy =>
    rw [map_mul]
    exact mul_mem ihx ihy
theorem embedding_chartRing (sR sY sZ : Bool) {a : SliceField F₀}
    (ha : a ∈ chartRing F₀ sR sY sZ) : HFree6812.sliceEmbedding D F₀ hker a ∈ surfaceChartRing D sR sY sZ := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [chartCoord, embedding_lmono]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    obtain ⟨b, hb⟩ := embedding_xField D F₀ hker r.2
    rw [show algebraMap (xField F₀) (SliceField F₀) r = (r : SliceField F₀) from rfl, ← hb]
    exact Subalgebra.algebraMap_mem _ b
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mul x y _ _ ihx ihy =>
    rw [map_mul]
    exact mul_mem ihx ihy
theorem isIntegral_embedding (sR sY sZ : Bool) {a : SliceField F₀}
    (ha : IsIntegral (chartRing F₀ sR sY sZ) a) :
    IsIntegral (surfaceChartRing D sR sY sZ) (HFree6812.sliceEmbedding D F₀ hker a) :=
  ha.map_of_comp_eq
    (((HFree6812.sliceEmbedding D F₀ hker).comp (algebraMap (chartRing F₀ sR sY sZ) (SliceField F₀))).codRestrict
      (surfaceChartRing D sR sY sZ) fun a => embedding_chartRing D F₀ hker sR sY sZ a.2)
    (HFree6812.sliceEmbedding D F₀ hker) rfl
theorem localFunction_mem (F : MvPolynomial (Fin 4) K) (hdvd : F₀ ∣ F) (S : MovingFiberThreeSources6811.Source F)
    (Hf : FlagDegree) (hI : ∀ sR sY sZ, PsiSIntegral F F₀ hdvd S Hf sR sY sZ)
    (q : SurfacePoint D) (m : ℕ) :
    q.localFunction (HFree6812.sliceEmbedding D F₀ hker (psiS F F₀ hdvd S m))
      (S.d • cutFlag m Hf + (4 * m) • S.flag) ∈ q.ring := by
  have h := isIntegral_embedding D F₀ hker _ _ _ (hI q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 m)
  rw [map_div₀, embedding_lmono] at h
  exact q.chartOf_spec.1 h
end Embedding
section Curve
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
theorem val_vertex_eq_one {F : Type*} [Field F] (hc : ∀ j, coordinate E G j ≠ 0)
    (q : SurfacePoint G) (S : Specialization (RCN002.CoordinateField E G) F) (hq : q.On S)
    (hcoord : ∀ j, S.val (coordinate E G j) ≤ 1) (W : FlagDegree) :
    S.val (lmono (coordinate E G) (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 W)) = 1 := by
  have hchart : ∀ i, S.val (lmono (coordinate E G)
      (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i)) ≤ 1 := fun i =>
    hq ⟨_, q.chartOf_spec.1 (isIntegral_algebraMap (R := surfaceChartRing G _ _ _)
      (x := ⟨_, Algebra.subset_adjoin ⟨i, rfl⟩⟩))⟩
  have h0 : ∀ j, RCN187.poleOrder S.val (coordinate E G j) = 0 := fun j =>
    max_eq_left ((log_le_iff_le_exp ((Valuation.ne_zero_iff _).mpr (hc j))).mpr
      (by rw [exp_zero]; exact hcoord j))
  rw [flagPole_eq_vertex S.val _ hc _ _ _ hchart W]
  simp only [flagPole, h0, max_self, mul_zero, add_zero, exp_zero]
theorem val_pow_mul_le {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰) (a b c : L) (m d e f : ℕ)
    (ha : v a ≤ exp (-(m : ℤ))) (hb : v b ≤ 1) (hc : v c ≤ 1) :
    v (a ^ (3 * d) * b ^ e * c ^ f) ≤ exp (-((3 * d * m : ℕ) : ℤ)) := by
  rw [map_mul, map_mul, map_pow, map_pow, map_pow]
  calc v a ^ (3 * d) * v b ^ e * v c ^ f
      ≤ exp (-(m : ℤ)) ^ (3 * d) * 1 ^ e * 1 ^ f :=
        mul_le_mul' (mul_le_mul' (pow_le_pow_left' ha _) (pow_le_pow_left' hb _))
          (pow_le_pow_left' hc _)
    _ = exp (-((3 * d * m : ℕ) : ℤ)) := by
        rw [one_pow, one_pow, mul_one, mul_one, ← exp_nsmul]
        congr 1
        push_cast
        simp only [nsmul_eq_mul]
        push_cast
        ring
variable {C : Ideal (MvPolynomial (Fin 3) E)} [C.IsPrime] {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem val_le_one_of_isCurveOnSurface (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    S.val (RCN002.coordinateEvaluation E G A) ≤ 1 :=
  (Valuation.mem_valuationSubring_iff _ _).mp (h A).1
theorem mem_iff_of_isCurveOnSurface (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    A ∈ C ↔ S.val (RCN002.coordinateEvaluation E G A) < 1 := by
  obtain ⟨hmem, hres⟩ := h A
  rw [← HFree6812.coordEval_eq_zero_iff C A, ← hres, S.res_eq_zero_iff]
end Curve
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
attribute [local instance] component_isPrime fact_irreducible
theorem embedding_sliceProj (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) (A : MvPolynomial (Fin 4) K) :
    embedding P g (sliceProj P.F A) = RCN002.coordinateEvaluation Ω (component P g) (surfaceMap (RCN135.polynomialEmbedding K) A) := by
  rw [embedding, HFree6812.sliceEmbedding_proj, sliceMap_component]
theorem coordinate_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) (hc : ∀ j, sliceCoord P.F j ≠ 0)
    (j : Fin 3) : coordinate Ω (component P g) j ≠ 0 := by
  rw [← psi_coord (component P g) P.F (ker_sliceMap_component P g) j]
  exact (map_ne_zero _).mpr (hc j)
theorem localFunction_function_mem (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree)
    (hI : ∀ sR sY sZ, PsiSIntegral P.F P.F (dvd_refl P.F) SZ Hf sR sY sZ) (g : RCN222.GeometricFactor K P.F)
    (q : SurfacePoint (component P g)) :
    q.localFunction (function P SZ g) (flag SZ Hf) ∈ q.ring :=
  localFunction_mem (component P g) P.F (ker_sliceMap_component P g) P.F (dvd_refl P.F) SZ Hf hI q w
theorem function_eq (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (g : RCN222.GeometricFactor K P.F) :
    function P SZ g = embedding P g (tail P.F P.F (dvd_refl P.F) w) ^ (3 * SZ.d) *
      embedding P g (sliceProj P.F (polyH K P.F)) ^ (2 * w * SZ.d) *
      embedding P g (srcLead P.F P.F SZ) ^ (4 * w) := by
  rw [function, psiS, map_mul, map_mul, map_pow, map_pow, map_pow]
theorem function_ne_zero (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (g : RCN222.GeometricFactor K P.F)
    (htail : tail P.F P.F (dvd_refl P.F) w ≠ 0) (hH : sliceProj P.F (polyH K P.F) ≠ 0)
    (hlead : srcLead P.F P.F SZ ≠ 0) : function P SZ g ≠ 0 := by
  rw [function_eq]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).mpr htail))
    (pow_ne_zero _ ((map_ne_zero _).mpr hH))) (pow_ne_zero _ ((map_ne_zero _).mpr hlead))
theorem val_function_le (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (SZ : MovingFiberThreeSources6811.Source P.F) (a : Curve P)
    (S : Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1))
    (hS : IsCurveOnSurface (component P a.1) a.2.1 S)
    (htail : S.val (embedding P a.1 (tail P.F P.F (dvd_refl P.F) w)) ≤
      exp (-(multiplicity P hp a : ℤ))) :
    S.val (function P SZ a.1) ≤ exp (-((3 * SZ.d * multiplicity P hp a : ℕ) : ℤ)) := by
  rw [function_eq]
  refine val_pow_mul_le S.val _ _ _ _ _ _ _ htail ?_ ?_
  · rw [embedding_sliceProj]
    exact val_le_one_of_isCurveOnSurface hS _
  · rw [srcLead, embedding_sliceProj]
    exact val_le_one_of_isCurveOnSurface hS _
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
open WithZero MvPolynomial HFree6812
open RCN002 RCN055 RCN086 RCN095 RCN136 RCN204 RCN313
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
theorem le_exp_neg_one_of_lt_one {a : ℤᵐ⁰} (h : a < 1) : a ≤ exp (-1) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · have hlog : log a < 0 := (log_lt_iff_lt_exp ha).2 (by rwa [exp_zero])
    exact (log_le_iff_le_exp ha).1 (by omega)
variable {K E : Type} [Field K] [Field E]
theorem cell_support (t y r : ℕ) (hr : 2 ≤ r) (hy : r + 1 ≤ y) (F : MvPolynomial (Fin 4) K)
    (hF : RCN275.ResidualSupportData (LocatorHybridCells.cellSupport t y r) F) :
    ∀ e ∈ F.support, e 2 ≤ r ∧ e 1 + e 2 ≤ r + (y - r) ∧ e 1 + e 2 + e 3 ≤ r + (y - r) + (t - y) := by
  intro e he
  have h1 := (MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights he).trans hF.s_weight
  have h2 := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights he).trans hF.ys_weight
  have h3 := (MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights he).trans hF.total_weight
  rw [RCN081.weight_fin4] at h1 h2 h3
  change e 0 * 0 + e 1 * 0 + e 2 * 1 + e 3 * 0 ≤ r - 2 + 2 at h1
  change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ y - r - 1 + (r - 2) + 3 at h2
  change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ t - y + (y - r - 1) + (r - 2) + 3 at h3
  omega
theorem tailCut_eq (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    RCN086.globalTailCut phi F (n + 2) = surfaceMap phi (polyH K F) ^ 3 * surfaceMap phi (RCN055.baseNumerator F n) *
      MvPolynomial.C ((-phi Polynomial.X) ^ (n + 2)) := by
  rw [RCN086.globalTailCut_eq, RCN055.numerator_eq_H_cube, map_mul, map_pow]
theorem sliceCoord_ne_zero (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (n : ℕ) (hn : sliceProj F₀ (RCN055.baseNumerator F n) ≠ 0) (j : Fin 3) :
    sliceCoord F₀ j ≠ 0 := by
  have hR : sliceCoord F₀ 1 ≠ 0 := fun h0 => by
    have h := HFree6812.sliceDerivation_iterate F F₀ hdvd hH n
    rw [show sliceProj F₀ (MvPolynomial.X 2) = sliceCoord F₀ 1 from rfl, h0,
      Function.iterate_fixed (map_zero _) (n + 1)] at h
    exact hn ((div_eq_zero_iff.1 h.symm).resolve_right (pow_ne_zero _ hH))
  have hY : sliceCoord F₀ 0 ≠ 0 := fun h0 => by
    have h := HFree6812.sliceDerivation_coord0 F F₀ hdvd hH
    rw [h0, map_zero] at h
    exact hR h.symm
  have hZ : sliceCoord F₀ 2 ≠ 0 := fun h0 => by
    obtain ⟨c, hc⟩ := (HFree6812.sliceProj_eq_zero_iff F₀ (MvPolynomial.X 3)).1 h0
    have hX : Irreducible (MvPolynomial.X 3 : MvPolynomial (Fin 4) K) := MvPolynomial.X_prime.irreducible
    have hcu : IsUnit c := (hX.isUnit_or_isUnit hc).resolve_left (Fact.out : Irreducible F₀).not_isUnit
    obtain ⟨G₁, hG⟩ : (MvPolynomial.X 3 : MvPolynomial (Fin 4) K) ∣ F := by
      rw [hc]
      exact hcu.mul_right_dvd.2 hdvd
    refine hH ((HFree6812.sliceProj_eq_zero_iff F₀ _).2 (dvd_trans ⟨c, hc⟩ ?_))
    rw [polyH, hG, Derivation.leibniz, pderiv_X_of_ne (by decide), smul_zero, add_zero]
    exact ⟨_, rfl⟩
  fin_cases j
  exacts [hY, hR, hZ]
theorem tail_cube_eq (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (n : ℕ) :
    tail F F₀ hdvd (n + 1) ^ 3 * sliceProj F₀ (polyH K F) ^ (2 * (n + 1)) =
      sliceProj F₀ (RCN055.baseNumerator F n ^ 3) / sliceProj F₀ (polyH K F ^ (4 * n + 1)) := by
  rw [tail, show sliceCoord F₀ 1 = sliceProj F₀ (MvPolynomial.X 2) from rfl, HFree6812.sliceDerivation_iterate F F₀ hdvd hH n,
    map_pow, map_pow, div_pow, ← pow_mul, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero _ hH) (pow_ne_zero _ hH)]
  ring
def tailCubeOn (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (n : ℕ) : RCN002.CoordinateField E C :=
  SecondJetComponentRoots.coefficientMap phi C (RCN055.baseNumerator F n ^ 3) / SecondJetComponentRoots.coefficientMap phi C (polyH K F ^ (4 * n + 1))
section Stage
open RCN074 RCN135 RCN159 RCN238 RCN243 RCN264 RCN330
variable {K I : Type} [Field K] {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageErrorCap d : ℕ} {sup : RCN275.ResidualSupportParameters}
theorem seed_place (S : FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag d sup) (C : CM S) (γ : K)
    (hγ : γ ∈ RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (d + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
      (DK (RCN135.polynomialEmbedding K) S.selected) C)
    (mu : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1))
    (hmu : PlaceOver C.1 (DK (RCN135.polynomialEmbedding K) S.selected γ) mu) :
    mu.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) C.1 (polyH K S.F)) = 1 ∧
      ∀ n, d ≤ n + 1 → mu.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) C.1 (RCN055.baseNumerator S.F n)) < 1 := by
  have hΓ : γ ∈ Gamma := RCN264.componentSeeds_subset (GenericField K) S.G _ _ Gamma (DK (RCN135.polynomialEmbedding K) S.selected) C hγ
  have hHv : MvPolynomial.aeval (DK (RCN135.polynomialEmbedding K) S.selected γ) (surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F)) ≠ 0 := by
    change MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) S.selected γ)
      (surfaceMap (RCN135.polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) S.F)) ≠ 0
    rw [WQ (RCN135.polynomialEmbedding K) S.selected γ]
    exact S.regular γ hΓ
  have h1 : mu.val (RCN002.coordinateEvaluation (GenericField K) C.1 (surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F))) = 1 :=
    hmu.eq_one _ hHv
  refine ⟨h1, fun n hn => hmu (surfaceMap (RCN135.polynomialEmbedding K) (RCN055.baseNumerator S.F n)) ?_⟩
  have hz := VZ (RCN135.polynomialEmbedding K) S.F S.selected γ d (n + 2) (S.degree_le γ hΓ) (S.solution γ hΓ) (by omega)
  rw [tailCut_eq, map_mul, map_mul, map_pow, MvPolynomial.aeval_C] at hz
  rcases mul_eq_zero.1 hz with h2 | h2
  · exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hHv)
  · exact absurd h2 (RCN086.tail_scalar_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) (n + 2))
theorem seed_tailCube (S : FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag d sup) (C : CM S) (γ : K)
    (hγ : γ ∈ RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (d + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
      (DK (RCN135.polynomialEmbedding K) S.selected) C)
    (mu : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1))
    (hmu : PlaceOver C.1 (DK (RCN135.polynomialEmbedding K) S.selected γ) mu) (n : ℕ) (hn : d ≤ n + 1) :
    mu.val (tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 n) ≤ exp (-3) := by
  obtain ⟨h1, h2⟩ := seed_place S C γ hγ mu hmu
  simp only [tailCubeOn, map_div₀, map_pow, h1, one_pow, div_one]
  calc mu.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) C.1 (RCN055.baseNumerator S.F n)) ^ 3 ≤ exp (-1) ^ 3 :=
        pow_le_pow_left' (le_exp_neg_one_of_lt_one (h2 n hn)) 3
    _ = exp (-3) := by
        rw [← exp_nsmul]
        norm_num
theorem Curve.tail_curve_count_of_bound (S : FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag d sup)
    (C : CM S) (base : RCN341.SeparableLiteralCoordinate C.1) {Hb Gb : MvPolynomial (Fin 3) (GenericField K)}
    (budget : RCN199.RD C.1 Hb Gb) (m n : ℕ) (hm : d ≤ m + 1) (u : RCN002.CoordinateField (GenericField K) C.1)
    (hu : ∀ γ ∈ RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (d + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C,
      ∀ mu : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1),
        PlaceOver C.1 (DK (RCN135.polynomialEmbedding K) S.selected γ) mu → mu.val u = 1)
    (hpsi : tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 m ^ n * u ≠ 0) (W : FlagDegree)
    (e : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1) → ℕ) (B : ℕ)
    (hB : ∀ T : Finset (RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1)),
      ∑ mu ∈ T, e mu ≤ B)
    (hpole : ∀ mu : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1),
      -flagPole mu.val (coordinate (GenericField K) C.1) W - e mu ≤
        RCN026.order_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C.1) mu
          (tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 m ^ n * u)) :
    3 * n * (RCN264.componentSeeds (GenericField K) S.G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (d + 1)) (CR (RCN135.polynomialEmbedding K) S.F) Gamma
        (DK (RCN135.polynomialEmbedding K) S.selected) C).card ≤ budget.weightedCost W + B := by
  refine Curve.curve_count_of_bound S.G _ _ C base budget Gamma (DK (RCN135.polynomialEmbedding K) S.selected)
    (ABD (RCN135.polynomialEmbedding K) S.selected) _ hpsi (3 * n) (fun γ hγ mu hmu => ?_) W e B hB hpole
  have h1 := seed_tailCube S C γ hγ mu hmu m hm
  have h2 : mu.val (tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 m ^ n * u) ≤ exp (-((3 * n : ℕ) : ℤ)) := by
    rw [map_mul, map_pow, hu γ hγ mu hmu, mul_one]
    calc mu.val (tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 m) ^ n ≤ exp (-3) ^ n := pow_le_pow_left' h1 n
      _ = exp (-((3 * n : ℕ) : ℤ)) := by
          rw [← exp_nsmul, nsmul_eq_mul]
          congr 1
          push_cast
          ring
  have h3 := (log_le_iff_le_exp ((Valuation.ne_zero_iff _).2 hpsi)).2 h2
  change ((3 * n : ℕ) : ℤ) ≤ -(mu.val (tailCubeOn (RCN135.polynomialEmbedding K) S.F C.1 m ^ n * u)).log
  omega
end Stage
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
open MvPolynomial HFree6812
open RCN313
variable {K : Type} [Field K]
theorem chartDivisor_place_law [CharP K 2130706433] (F F₀ : MvPolynomial (Fin 4) K)
    [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ)
    (hN : MvPolynomial.weightedTotalDegree ![0, 1, 1, 1] F ≤ N) (hNp : 4 * N ^ 2 < 2130706433)
    (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) (hcore : ChartCorePoly F₀ N sR sY sZ)
    (htwo : ChartTwoCoord F₀ N sR sY sZ) : ChartPlaceLaw F F₀ hdvd sR sY sZ :=
  chartPlaceLaw_of_contracts F F₀ hdvd hH N hNp hc sR sY sZ hcore
    (chartDivisor_hchar F F₀ hH N hN hNp hc sR sY sZ htwo) (chartDivisor_hgen F₀ hc sR sY sZ)
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial HFree6812
open RCN313
namespace Chart
theorem weight_le_of_dvd {K : Type*} [Field K] (F F₀ : MvPolynomial (Fin 4) K) (hdvd : F₀ ∣ F)
    (hF : F ≠ 0) (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N) :
    weightedTotalDegree ![0, 1, 1, 1] F₀ ≤ N := by
  obtain ⟨G, rfl⟩ := hdvd
  rw [RCN081.weightedTotalDegree_mul _ F₀ G (left_ne_zero_of_mul hF) (right_ne_zero_of_mul hF)] at hN
  exact (Nat.le_add_right _ _).trans hN
theorem ne_zero_of_polyH_ne_zero {K : Type} [Field K] (F F₀ : MvPolynomial (Fin 4) K)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) : F ≠ 0 := by
  rintro rfl
  exact hH (by rw [polyH, map_zero, map_zero])
variable {K : Type} [Field K] (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]
theorem polyH_ne_zero_of_dvd (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    sliceProj F₀ (polyH K F₀) ≠ 0 := by
  obtain ⟨F₁, hF₁⟩ := HFree6812.sliceProj_H_eq F F₀ hdvd
  intro h
  rw [polyH] at h
  exact hH (by rw [hF₁, h, mul_zero])
theorem chart_core_poly_of_dvd (hdvd : F₀ ∣ F) (hF : F ≠ 0) (N : ℕ)
    (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) :
    ChartCorePoly F₀ N sR sY sZ :=
  chart_core_poly F₀ N (weight_le_of_dvd F F₀ hdvd hF N hN) hc sR sY sZ
theorem chart_two_coord_of_dvd (hdvd : F₀ ∣ F) (hF : F ≠ 0) (N : ℕ)
    (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) :
    ChartTwoCoord F₀ N sR sY sZ :=
  chart_two_coord F₀ N (weight_le_of_dvd F F₀ hdvd hF N hN) hc sR sY sZ
theorem chart_krull_of_dvd [CharP K 2130706433] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N)
    (hN9 : N ≤ 9678) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) : ChartKrull F₀ sR sY sZ :=
  chart_krull F₀ N (weight_le_of_dvd F F₀ hdvd (ne_zero_of_polyH_ne_zero F F₀ hH) N hN) hN9
    (polyH_ne_zero_of_dvd F F₀ hdvd hH) hc sR sY sZ
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
open WithZero
open RCN002
section
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
theorem Surf.lmono_affine_mem {L : Type*} [Field L] (x : Fin 3 → L) (W : Set L) :
    (∀ i, lmono x (chartExp false false false i) ∈ W) ↔ ∀ j, x j ∈ W := by
  have h0 : lmono x (chartExp false false false 0) = x 1 := by
    rw [PlaceSurf.lmono_chartExp_zero]
    simp [PlaceSurf.flip, PlaceSurf.denR, PlaceSurf.denY]
  have h1 : lmono x (chartExp false false false 1) = x 0 := by
    rw [PlaceSurf.lmono_chartExp_one]
    simp [PlaceSurf.flip, PlaceSurf.denY]
  have h2 : lmono x (chartExp false false false 2) = x 2 := by
    rw [PlaceSurf.lmono_chartExp_two]
    simp [PlaceSurf.flip]
  constructor
  · intro hall
    have a0 := hall 0
    have a1 := hall 1
    have a2 := hall 2
    rw [h0] at a0
    rw [h1] at a1
    rw [h2] at a2
    intro j
    fin_cases j
    · exact a1
    · exact a0
    · exact a2
  · intro hall i
    fin_cases i
    · exact h0 ▸ hall 1
    · exact h1 ▸ hall 0
    · exact h2 ▸ hall 2
theorem IsCurveOnSurface.not_isMaximal_centre {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (hc : ∀ j, coordinate E G j ≠ 0)
    (htr : ∃ j, Transcendental E (coordinate E C j)) (q : SurfacePoint G) (hq : q.On S) :
    ¬(centre (RCN002.CoordinateField E G) S.val hq).IsMaximal := by
  intro hmax
  have hloc := q.isLocalRing
  obtain ⟨φ, hφ⟩ := q.residue
  have hlt : ∀ a : q.ring, ¬IsUnit a → S.val (a : RCN002.CoordinateField E G) < 1 := fun a ha => by
    have h1 : a ∈ centre (RCN002.CoordinateField E G) S.val hq := by
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact ha
    exact h1
  have hU : ∀ a ∈ (q.ring : Set (RCN002.CoordinateField E G)), a⁻¹ ∈ {y : RCN002.CoordinateField E G | S.val y ≤ 1} →
      a⁻¹ ∈ (q.ring : Set (RCN002.CoordinateField E G)) := by
    intro a ha hinv
    by_cases ha0 : a = 0
    · rw [ha0, inv_zero]
      exact q.ring.zero_mem
    · have hva : S.val a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
      have h1 : S.val a⁻¹ ≤ 1 := hinv
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hva)] at h1
      have hunit : IsUnit (⟨a, ha⟩ : q.ring) := by
        by_contra hnu
        exact absurd (hlt ⟨a, ha⟩ hnu) (not_lt.mpr h1)
      obtain ⟨u, hu⟩ := hunit
      have h2 : ((↑u⁻¹ : q.ring) : RCN002.CoordinateField E G) * a = 1 := by
        have h3 := congrArg (Subtype.val : q.ring → RCN002.CoordinateField E G) (Units.inv_mul u)
        rwa [hu] at h3
      rw [← eq_inv_of_mul_eq_one_left h2]
      exact (↑u⁻¹ : q.ring).2
  have hx : ∀ j, coordinate E G j ∈ {y : RCN002.CoordinateField E G | S.val y ≤ 1} := fun j =>
    (Valuation.mem_valuationSubring_iff _ _).mp (h (MvPolynomial.X j)).1
  have hO : ∀ i, lmono (coordinate E G)
      (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i) ∈ (q.ring : Set (RCN002.CoordinateField E G)) := fun i =>
    q.chartOf_spec.1 (Surf.chart_le_normalChart (Algebra.subset_adjoin ⟨i, rfl⟩))
  have hmem : ∀ j, coordinate E G j ∈ (q.ring : Set (RCN002.CoordinateField E G)) :=
    (Surf.lmono_affine_mem _ _).mp fun i =>
      PlaceSurf.chart_overlap (coordinate E G) hc q.ring.one_mem
        (fun a ha b hb => q.ring.mul_mem ha hb) hU _ _ _ false false false hO
        ((Surf.lmono_affine_mem _ _).mpr hx) i
  obtain ⟨j, hj⟩ := htr
  have hb : ¬IsUnit ((⟨coordinate E G j, hmem j⟩ : q.ring) -
      algebraMap E q.ring (φ ⟨coordinate E G j, hmem j⟩)) :=
    (hφ _).mp (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self])
  have h2 := hlt _ hb
  have h3 : S.val (RCN002.coordinateEvaluation E G (MvPolynomial.X j -
      MvPolynomial.C (φ ⟨coordinate E G j, hmem j⟩))) < 1 := by
    rw [map_sub, show RCN002.coordinateEvaluation E G (MvPolynomial.X j) = coordinate E G j from rfl,
      show RCN002.coordinateEvaluation E G (MvPolynomial.C (φ ⟨coordinate E G j, hmem j⟩)) =
        algebraMap E (RCN002.CoordinateField E G) (φ ⟨coordinate E G j, hmem j⟩) from (RCN002.coordinateEvaluation E G).commutes _]
    exact h2
  obtain ⟨hm, hres⟩ := h (MvPolynomial.X j - MvPolynomial.C (φ ⟨coordinate E G j, hmem j⟩))
  rw [(S.res_eq_zero_iff ⟨_, hm⟩).mpr h3, map_sub,
    show RCN002.coordinateEvaluation E C (MvPolynomial.X j) = coordinate E C j from rfl,
    show RCN002.coordinateEvaluation E C (MvPolynomial.C (φ ⟨coordinate E G j, hmem j⟩)) =
      algebraMap E (RCN002.CoordinateField E C) (φ ⟨coordinate E G j, hmem j⟩) from (RCN002.coordinateEvaluation E C).commutes _] at hres
  exact hj ((sub_eq_zero.mp hres.symm) ▸ isAlgebraic_algebraMap _)
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
namespace LevelSurf
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Level
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L]
theorem zeroDivisor_apply {x : L} (hx : x ≠ 0) (P : PrimeDivisor O) :
    zeroDivisor (O := O) L x P = (-(P.valuation L x).log).toNat := by
  have hfin : (Function.support fun P : PrimeDivisor O => (-(P.valuation L x).log).toNat).Finite :=
    (finite_setOf_valuation_ne_one L hx).subset fun P hP h1 =>
      hP (by simp only [h1, log_one, neg_zero, Int.toNat_zero])
  rw [zeroDivisor]
  split_ifs with h
  · rfl
  · exact absurd hfin h
theorem zeroDivisor_algebraMap {g : O} (hg : g ≠ 0) :
    zeroDivisor (O := O) L (algebraMap O L g) = div L g :=
  Finsupp.ext fun P =>
    (zeroDivisor_apply L ((map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hg) P).trans
      (div_apply L g P).symm
theorem nsmul_div {g : O} (hg : g ≠ 0) (n : ℕ) : n • div L g = div L (g ^ n) := by
  ext P
  have h1 := valuation_eq_exp_neg_div L (pow_ne_zero n hg) P
  rw [map_pow, map_pow, valuation_eq_exp_neg_div L hg P, ← exp_nsmul, exp_inj, nsmul_eq_mul] at h1
  have h2 : ((n * div L g P : ℕ) : ℤ) = (div L (g ^ n) P : ℕ) := by
    push_cast
    linarith
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact_mod_cast h2
theorem exists_valuation_lt_one_of_zeroDivisor_ne_zero {x : L} (hx : x ≠ 0)
    (h : zeroDivisor (O := O) L x ≠ 0) : ∃ P : PrimeDivisor O, P.valuation L x < 1 := by
  obtain ⟨P, hP⟩ := DFunLike.ne_iff.mp h
  rw [zeroDivisor_apply L hx, Finsupp.zero_apply] at hP
  have h0 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hlog : (P.valuation L x).log < 0 := by
    by_contra hge
    exact hP (Int.toNat_eq_zero.mpr (by omega))
  have h1 := (log_lt_iff_lt_exp h0).mp hlog
  rw [exp_zero] at h1
  exact ⟨P, h1⟩
end Level
section MinimalPrimes
variable {A : Type*} [CommRing A] [IsDomain A]
theorem mem_minimalPrimes_sup (hA : PrimeChain A) (P : PrimeDivisor A) (J M : Ideal A) [hM : M.IsPrime]
    (hPM : P.ideal ≤ M) (hJM : J ≤ M) (hJ : ¬J ≤ P.ideal) : M ∈ (P.ideal ⊔ J).minimalPrimes := by
  obtain ⟨r, hr, hrM⟩ := Ideal.exists_minimalPrimes_le (sup_le hPM hJM)
  have hPr : P.ideal < r := lt_of_le_of_ne (le_sup_left.trans hr.1.2) fun h =>
    hJ (h ▸ le_sup_right.trans hr.1.2)
  have hmax := hA P.ideal r P.isPrime hr.1.1 (Ideal.ne_bot_of_height_eq_one P.height_eq_one) hPr
  rwa [← hmax.eq_of_le hM.ne_top hrM]
end MinimalPrimes
section Under
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
def underIdeal {A O : Subalgebra E L} (h : A ≤ O) (φ : O →ₐ[E] E) : Ideal A :=
  RingHom.ker (φ.toRingHom.comp (Subalgebra.inclusion h).toRingHom)
variable {A O O' : Subalgebra E L} (h : A ≤ O) (φ : O →ₐ[E] E)
theorem underIdeal_isPrime : (underIdeal h φ).IsPrime :=
  RingHom.ker_isPrime _
theorem mem_underIdeal (hφ : ∀ x, φ x = 0 ↔ ¬IsUnit x) (a : A) :
    a ∈ underIdeal h φ ↔ ¬IsUnit (Subalgebra.inclusion h a) :=
  hφ _
theorem le_of_underIdeal_le (h' : A ≤ O') (φ' : O' →ₐ[E] E) (hφ : ∀ x, φ x = 0 ↔ ¬IsUnit x)
    (hφ' : ∀ x, φ' x = 0 ↔ ¬IsUnit x)
    (hloc : ∀ x ∈ O, ∃ s ∈ A, s ≠ 0 ∧ s⁻¹ ∈ O ∧ x * s ∈ A)
    (hle : underIdeal h' φ' ≤ underIdeal h φ) : O ≤ O' := by
  intro x hx
  obtain ⟨s, hsA, hs0, hsinv, hxs⟩ := hloc x hx
  have hu : IsUnit (Subalgebra.inclusion h ⟨s, hsA⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hsinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
  have hu' : IsUnit (Subalgebra.inclusion h' ⟨s, hsA⟩) := by
    by_contra hnu
    exact (mem_underIdeal h φ hφ _).mp (hle ((mem_underIdeal h' φ' hφ' _).mpr hnu)) hu
  obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hu'
  have ht' : s * (t : L) = 1 := congrArg Subtype.val ht
  have hs' : s⁻¹ ∈ O' := by
    rw [← eq_inv_of_mul_eq_one_right ht']
    exact t.2
  have hx' := O'.mul_mem (h' hxs) hs'
  rwa [mul_inv_cancel_right₀ hs0] at hx'
end Under
section Points
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
def InChart (q : SurfacePoint G) (sR sY sZ : Bool) : Prop :=
  ∀ x ∈ q.ring, ∃ s ∈ normalChart G sR sY sZ, s ≠ 0 ∧ s⁻¹ ∈ q.ring ∧ x * s ∈ normalChart G sR sY sZ
theorem subsingleton_points (sR sY sZ : Bool) (M : Ideal (normalChart G sR sY sZ)) :
    {q : SurfacePoint G | ∃ h : normalChart G sR sY sZ ≤ q.ring, InChart q sR sY sZ ∧
      underIdeal h q.residue.choose = M}.Subsingleton := by
  rintro q ⟨h, hloc, hM⟩ q' ⟨h', hloc', hM'⟩
  exact SurfacePoint.ext_ring (le_antisymm
    (le_of_underIdeal_le h _ h' _ q.residue.choose_spec q'.residue.choose_spec hloc
      (hM'.le.trans hM.ge))
    (le_of_underIdeal_le h' _ h _ q'.residue.choose_spec q.residue.choose_spec hloc'
      (hM.le.trans hM'.ge)))
theorem finite_points_of_minimalPrimes (sR sY sZ : Bool) [IsNoetherianRing (normalChart G sR sY sZ)]
    (I : Set (Ideal (normalChart G sR sY sZ))) (hI : I.Finite) :
    {q : SurfacePoint G | ∃ h : normalChart G sR sY sZ ≤ q.ring, InChart q sR sY sZ ∧
      ∃ J ∈ I, underIdeal h q.residue.choose ∈ J.minimalPrimes}.Finite := by
  refine (hI.biUnion fun J _ => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).biUnion
    fun M _ => (subsingleton_points sR sY sZ M).finite).subset ?_
  rintro q ⟨h, hloc, J, hJ, hM⟩
  exact Set.mem_biUnion hJ (Set.mem_biUnion hM ⟨h, hloc, rfl⟩)
variable {N p : ℕ} [CharP E p]
theorem chart_facts (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (q : SurfacePoint G) {sR sY sZ : Bool} (hq : q.chartOf = (sR, sY, sZ)) :
    ∃ h : normalChart G sR sY sZ ≤ q.ring, InChart q sR sY sZ ∧
      ∀ P : PrimeDivisor q.ring, ∃ P₀ : PrimeDivisor (normalChart G sR sY sZ),
        P₀.valuation (RCN002.CoordinateField E G) = P.valuation (RCN002.CoordinateField E G) ∧ P₀.ideal ≤ underIdeal h q.residue.choose := by
  have h1 := q.chartOf_spec
  rw [hq] at h1
  refine ⟨h1.1, h1.2, fun P => ?_⟩
  have h3 := q.surfaceDivisor hN hp P
  rw [hq] at h3
  obtain ⟨P₀, hval, hmem⟩ := h3.exists_primeDivisor (hN sR sY sZ) hp
  refine ⟨P₀, hval, fun a ha => ?_⟩
  rw [mem_underIdeal h1.1 _ q.residue.choose_spec]
  intro hu
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    ((P.valuation_lt_one_iff (RCN002.CoordinateField E G) (Subalgebra.inclusion h1.1 a)).mp ((hmem a).mp ha)) hu)
theorem finite_basePoints_chart (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (sR sY sZ : Bool) (x : RCN002.CoordinateField E G) (hx : x ≠ 0) :
    {q : SurfacePoint G | q.chartOf = (sR, sY, sZ) ∧
      (∃ P : PrimeDivisor q.ring, P.valuation (RCN002.CoordinateField E G) x < 1) ∧
      ∃ P : PrimeDivisor q.ring, 1 < P.valuation (RCN002.CoordinateField E G) x}.Finite := by
  have := normalChart_isNoetherianRing (hN sR sY sZ) hp
  have := normalChart_isIntegrallyClosed (hN sR sY sZ)
  have := normalChart_isFractionRing (hN sR sY sZ)
  have hA := normalChart_primeChain (hN sR sY sZ)
  have hT := finite_setOf_valuation_ne_one (O := normalChart G sR sY sZ) (RCN002.CoordinateField E G) hx
  refine (finite_points_of_minimalPrimes sR sY sZ _ (Set.Finite.image2
    (fun P₀ P₀' : PrimeDivisor (normalChart G sR sY sZ) => P₀.ideal ⊔ P₀'.ideal) hT hT)).subset ?_
  rintro q ⟨hq, ⟨P, hP⟩, ⟨P', hP'⟩⟩
  obtain ⟨h, hloc, hdiv⟩ := chart_facts hN hp q hq
  obtain ⟨P₀, hv, hle⟩ := hdiv P
  obtain ⟨P₀', hv', hle'⟩ := hdiv P'
  have := underIdeal_isPrime h q.residue.choose
  refine ⟨h, hloc, _, Set.mem_image2_of_mem (a := P₀) (b := P₀') ?_ ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, hv]
    exact hP.ne
  · rw [Set.mem_ofPred_eq, hv']
    exact hP'.ne'
  · refine mem_minimalPrimes_sup hA P₀ P₀'.ideal _ hle hle' fun hcle => ?_
    rw [← hv', PrimeDivisor.eq_of_le hcle, hv] at hP'
    exact lt_asymm hP hP'
theorem finite_levelPoints_chart (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (sR sY sZ : Bool) {F : Type*} [Field F] (S : Specialization (RCN002.CoordinateField E G) F) (x : RCN002.CoordinateField E G)
    (hS : S.val x = 1) :
    {q : SurfacePoint G | q.chartOf = (sR, sY, sZ) ∧ q.On S ∧
      ∃ P : PrimeDivisor q.ring, P.valuation (RCN002.CoordinateField E G) x < 1}.Finite := by
  have := normalChart_isNoetherianRing (hN sR sY sZ) hp
  have := normalChart_isIntegrallyClosed (hN sR sY sZ)
  have := normalChart_isFractionRing (hN sR sY sZ)
  have hA := normalChart_primeChain (hN sR sY sZ)
  have hx : x ≠ 0 := fun h => by
    rw [h, map_zero] at hS
    exact zero_ne_one hS
  have hT := finite_setOf_valuation_ne_one (O := normalChart G sR sY sZ) (RCN002.CoordinateField E G) hx
  by_cases hw : ∀ a : normalChart G sR sY sZ,
      S.val (algebraMap (normalChart G sR sY sZ) (RCN002.CoordinateField E G) a) ≤ 1
  · have hpr := Surf.centre_isPrime (RCN002.CoordinateField E G) S.val hw
    have hne := Surf.centre_ne_bot (RCN002.CoordinateField E G) S.val S.surjective hw
    refine (finite_points_of_minimalPrimes sR sY sZ _ (hT.image fun P₀ =>
      P₀.ideal ⊔ centre (RCN002.CoordinateField E G) S.val hw)).subset ?_
    rintro q ⟨hq, hOn, P, hP⟩
    obtain ⟨h, hloc, hdiv⟩ := chart_facts hN hp q hq
    obtain ⟨P₀, hv, hle⟩ := hdiv P
    have := underIdeal_isPrime h q.residue.choose
    have hP₀ := P₀.isPrime
    refine ⟨h, hloc, _, Set.mem_image_of_mem _ (x := P₀) ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, hv]
      exact hP.ne
    · refine mem_minimalPrimes_sup hA P₀ _ _ hle (fun a ha => ?_) fun hcle => ?_
      · rw [mem_underIdeal h _ q.residue.choose_spec]
        intro hu
        obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
        have h1 : S.val (a : RCN002.CoordinateField E G) * S.val (b : RCN002.CoordinateField E G) = 1 := by
          rw [← map_mul, ← map_one S.val]
          exact congrArg S.val (congrArg Subtype.val hb)
        have h2 : S.val (a : RCN002.CoordinateField E G) < 1 := (Surf.mem_centre (RCN002.CoordinateField E G) S.val hw a).mp ha
        exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' (hOn b)) h2))
      · have heq : centre (RCN002.CoordinateField E G) S.val hw = P₀.ideal := by
          by_contra hne'
          have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hcle hne')
          rw [P₀.height_eq_one] at h1
          refine hne (Ideal.height_eq_zero_iff_eq_bot.mp ?_)
          by_contra h0
          have h2 : (1 : ℕ∞) + 1 ≤ 1 :=
            (add_le_add_left (Order.one_le_iff_ne_zero.mpr h0) 1).trans h1
          norm_num at h2
        have hval : S.val = P₀.valuation (RCN002.CoordinateField E G) :=
          PrimeDivisor.valuation_unique (RCN002.CoordinateField E G) P₀ S.val
            ⟨S.surjective, hw, fun a => by rw [← heq]; exact Iff.rfl⟩
        rw [← hv, ← hval, hS] at hP
        exact lt_irrefl _ hP
  · refine Set.finite_empty.subset ?_
    rintro q ⟨hq, hOn, -⟩
    obtain ⟨h, -, -⟩ := chart_facts hN hp q hq
    exact hw fun a => hOn ⟨a, h a.2⟩
theorem finite_surfaceDivisor_chart {sR sY sZ : Bool} (hN : SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (x : RCN002.CoordinateField E G) (hx : x ≠ 0) :
    {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | SurfaceDivisor G sR sY sZ nu ∧ nu x ≠ 1}.Finite := by
  have := normalChart_isNoetherianRing hN hp
  have := normalChart_isIntegrallyClosed hN
  have := normalChart_isFractionRing hN
  refine ((finite_setOf_valuation_ne_one (O := normalChart G sR sY sZ) (RCN002.CoordinateField E G) hx).image
    fun P => P.valuation (RCN002.CoordinateField E G)).subset ?_
  rintro nu ⟨h, hne⟩
  obtain ⟨P, hP, -⟩ := h.exists_primeDivisor hN hp
  exact ⟨P, by rw [Set.mem_ofPred_eq, hP]; exact hne, hP⟩
end Points
end
end LevelSurf
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
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Spec
variable {A : Type*} [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  [IsFractionRing A L]
theorem exists_valuation_of_dvr (P : Ideal A) [P.IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime P)) :
    ∃ v : Valuation L ℤᵐ⁰, Function.Surjective v ∧ (∀ a : A, v (algebraMap A L a) ≤ 1) ∧
      (∀ a : A, v (algebraMap A L a) < 1 ↔ a ∈ P) ∧
      ∀ x : L, v x ≤ 1 → ∃ a s : A, s ∉ P ∧ x * algebraMap A L s = algebraMap A L a := by
  let B := Localization.subalgebra.ofField L P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hB : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) B)
  exact exists_valuation_of_isDiscreteValuationRing L P B
theorem valuation_eq_of_dvr (P : Ideal A) [hP : P.IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime P)) {v w : Valuation L ℤᵐ⁰}
    (hv : Function.Surjective v) (hv1 : ∀ a : A, v (algebraMap A L a) ≤ 1)
    (hv2 : ∀ a : A, v (algebraMap A L a) < 1 ↔ a ∈ P) (hw : Function.Surjective w)
    (hw1 : ∀ a : A, w (algebraMap A L a) ≤ 1) (hw2 : ∀ a : A, w (algebraMap A L a) < 1 ↔ a ∈ P) :
    v = w := by
  obtain ⟨v₀, h1, h2, h3, h4⟩ := exists_valuation_of_dvr L P hdvr
  have h0 : PrimeDivisor.IsValuation L ⟨P, hP, height_eq_one_of_isDiscreteValuationRing P hdvr⟩ v₀ :=
    ⟨h1, h2, h3⟩
  exact (h0.eq_of_forall h4 ⟨hv, hv1, hv2⟩).trans (h0.eq_of_forall h4 ⟨hw, hw1, hw2⟩).symm
theorem exists_specialization (P : Ideal A) [P.IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime P)) {F : Type*} [Field F] (φ : A →+* F)
    (hker : RingHom.ker φ = P) (hsurj : ∀ y : F, ∃ a s : A, s ∉ P ∧ y * φ s = φ a) :
    ∃ S : Specialization L F, ∀ a : A, ∃ h : algebraMap A L a ∈ S.val.valuationSubring,
      S.res ⟨algebraMap A L a, h⟩ = φ a := by
  let B := Localization.subalgebra.ofField L P.primeCompl P.primeCompl_le_nonZeroDivisors
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_valuation_of_dvr L P hdvr
  have hvs : ∀ s : A, s ∉ P → v (algebraMap A L s) = 1 := fun s hs =>
    le_antisymm (hv2 s) (not_lt.mp fun h => hs ((hv3 s).mp h))
  have hs0 : ∀ s : A, s ∉ P → algebraMap A L s ≠ 0 := fun s hs h0 => by
    have h1 := hvs s hs
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hφs : ∀ s : A, s ∉ P → φ s ≠ 0 := fun s hs h => hs (hker ▸ RingHom.mem_ker.mpr h)
  have hu : ∀ s : P.primeCompl, IsUnit (φ s) := fun s => isUnit_iff_ne_zero.mpr (hφs s s.2)
  let ρ : B →+* F := IsLocalization.lift hu
  have hρ : ∀ a : A, ρ (algebraMap A B a) = φ a := IsLocalization.lift_eq hu
  have hmem : ∀ x : L, v x ≤ 1 → x ∈ B := by
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := hv4 x hx
    exact ⟨a, s, hs, by rw [← hxs, mul_inv_cancel_right₀ (hs0 s hs)]⟩
  let ι : v.valuationSubring →+* B :=
    { toFun := fun x => ⟨x.1, hmem x.1 ((Valuation.mem_valuationSubring_iff v _).mp x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have key : ∀ (x : v.valuationSubring) (a s : A),
      (x : L) * algebraMap A L s = algebraMap A L a → ρ (ι x) * φ s = φ a := by
    intro x a s hxs
    rw [← hρ s, ← map_mul, ← hρ a]
    exact congrArg ρ (Subtype.ext hxs)
  refine ⟨⟨v, hv1, ρ.comp ι, fun y => ?_, fun x => ?_⟩, fun a => ?_⟩
  · obtain ⟨a, s, hs, hy⟩ := hsurj y
    have hx : v (algebraMap A L a / algebraMap A L s) ≤ 1 := by
      rw [map_div₀, hvs s hs, div_one]
      exact hv2 a
    refine ⟨⟨_, (Valuation.mem_valuationSubring_iff v _).mpr hx⟩, ?_⟩
    exact mul_right_cancel₀ (hφs s hs)
      ((key ⟨_, (Valuation.mem_valuationSubring_iff v _).mpr hx⟩ a s
        (div_mul_cancel₀ _ (hs0 s hs))).trans hy.symm)
  · obtain ⟨a, s, hs, hxs⟩ := hv4 x.1 ((Valuation.mem_valuationSubring_iff v _).mp x.2)
    have h1 := key x a s hxs
    have h2 : v (x : L) = v (algebraMap A L a) := by rw [← hxs, map_mul, hvs s hs, mul_one]
    change ρ (ι x) = 0 ↔ _
    rw [h2, hv3, ← hker, RingHom.mem_ker, ← h1, mul_eq_zero, or_iff_left (hφs s hs)]
  · exact ⟨(Valuation.mem_valuationSubring_iff v _).mpr (hv2 a), hρ a⟩
end Spec
section ResTrans
variable (E : Type*) [Field E] {L : Type*} [Field L] [Algebra E L]
def ResTrans (nu : Valuation L ℤᵐ⁰) (y : L) : Prop :=
  Transcendental E y ∧ ∀ a ∈ IntermediateField.adjoin E {y}, a ≠ 0 → nu a = 1
variable {E} {nu : Valuation L ℤᵐ⁰}
theorem ResTrans.le_one_algebraMap {y : L} (h : ResTrans E nu y) (a : E) :
    nu (algebraMap E L a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
    exact zero_le_one
  · exact (h.2 _ (IntermediateField.algebraMap_mem _ a)
      ((map_ne_zero_iff _ (algebraMap E L).injective).mpr ha)).le
theorem resTrans_of_forall {y : L}
    (h : ∀ p : Polynomial E, p ≠ 0 → nu (Polynomial.aeval y p) = 1) : ResTrans E nu y := by
  refine ⟨fun ⟨p, hp0, hp⟩ => ?_, fun a ha ha0 => ?_⟩
  · have h1 := h p hp0
    rw [hp, map_zero] at h1
    exact zero_ne_one h1
  · obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff E a).mp ha
    have hr : r ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at ha0
      exact ha0 rfl
    have hs : s ≠ 0 := by
      rintro rfl
      rw [map_zero, div_zero] at ha0
      exact ha0 rfl
    rw [map_div₀, h r hr, h s hs, div_one]
theorem ResTrans.inv {y : L} (h : ResTrans E nu y) : ResTrans E nu y⁻¹ :=
  ⟨fun halg => h.1 (inv_inv y ▸ halg.inv), fun a ha => h.2 a
    (IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self E y)) ha)⟩
theorem not_resTrans_one : ¬ResTrans E nu (1 : L) := fun h => h.1 isAlgebraic_one
theorem ResTrans.of_mul {u w : L} (hu : nu u ≤ 1) (hw : nu w ≤ 1) (h : ResTrans E nu (u * w)) :
    ResTrans E nu u ∨ ResTrans E nu w := by
  have h1 : ∀ a ∈ Algebra.adjoin E (Set.range ![u, w]), nu a ≤ 1 := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      exacts [hu, hw]
    | algebraMap r => exact h.le_one_algebraMap r
    | add x y _ _ ihx ihy => exact (nu.map_add _ _).trans (max_le ihx ihy)
    | mul x y _ _ ihx ihy =>
      rw [map_mul]
      exact mul_le_one' ihx ihy
  obtain ⟨i, hi⟩ := exists_trivial_on_generator nu ![u, w] h1 (u * w)
    (mul_mem (Algebra.subset_adjoin ⟨0, rfl⟩) (Algebra.subset_adjoin ⟨1, rfl⟩)) h.1 h.2
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi
theorem ResTrans.layer {y b : L} (hy : nu y ≤ 1) (hy0 : y ≠ 0) (hb : nu b = 1) (s : Bool)
    (ht : nu (if s then b / y else y / b) ≤ 1) :
    (s = true → nu y = 1) ∧
      (ResTrans E nu y → ResTrans E nu (if s then b / y else y / b) ∨ ResTrans E nu b) ∧
      (ResTrans E nu (if s then b / y else y / b) → ResTrans E nu y ∨ ResTrans E nu b) := by
  have hb0 : b ≠ 0 := fun h => by
    rw [h, map_zero] at hb
    exact zero_ne_one hb
  have hbi : nu b⁻¹ ≤ 1 := by rw [map_inv₀, hb, inv_one]
  have hinv : ∀ z : L, ResTrans E nu z⁻¹ → ResTrans E nu z := fun z h => inv_inv z ▸ h.inv
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
    refine ⟨fun h => absurd h (by decide), fun h => ?_, fun h => ?_⟩
    · exact ResTrans.of_mul ht hb.le (by rwa [div_mul_cancel₀ _ hb0])
    · exact (ResTrans.of_mul hy hbi (by rwa [← div_eq_mul_inv])).imp_right (hinv b)
  · simp only [↓reduceIte] at ht ⊢
    have hy1 : nu y = 1 := by
      refine le_antisymm hy ?_
      rwa [map_div₀, hb, one_div,
        inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff nu).mpr hy0))] at ht
    have hyi : nu y⁻¹ ≤ 1 := by rw [map_inv₀, hy1, inv_one]
    refine ⟨fun _ => hy1, fun h => ?_, fun h => ?_⟩
    · have h' := h.inv
      rw [show y⁻¹ = b / y * b⁻¹ by field_simp] at h'
      exact (ResTrans.of_mul ht hbi h').imp_right (hinv b)
    · exact ((ResTrans.of_mul hb.le hyi (by rwa [← div_eq_mul_inv])).imp_right (hinv y)).symm
theorem chartCoord_eq (x : Fin 3 → L) (sR sY sZ : Bool) :
    lmono x (chartExp sR sY sZ 2) = (if sZ then 1 / x 2 else x 2 / 1) ∧
    lmono x (chartExp sR sY sZ 1) =
      (if sY then (if sZ then x 2 else 1) / x 0 else x 0 / (if sZ then x 2 else 1)) ∧
    lmono x (chartExp sR sY sZ 0) =
      (if sR then (if sY then x 0 else if sZ then x 2 else 1) / x 1
        else x 1 / (if sY then x 0 else if sZ then x 2 else 1)) := by
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    simp [lmono, chartExp, div_eq_mul_inv, mul_comm]
theorem chart_resTrans (x : Fin 3 → L) (hx0 : ∀ j, x j ≠ 0) (hx : ∀ j, nu (x j) ≤ 1)
    (sR sY sZ : Bool) (ht : ∀ i, nu (lmono x (chartExp sR sY sZ i)) ≤ 1) :
    (∃ j, ResTrans E nu (x j)) ↔ ∃ i, ResTrans E nu (lmono x (chartExp sR sY sZ i)) := by
  obtain ⟨e2, e1, e0⟩ := chartCoord_eq x sR sY sZ
  have ht2 := ht 2
  have ht1 := ht 1
  have ht0 := ht 0
  rw [e2] at ht2
  rw [e1] at ht1
  rw [e0] at ht0
  obtain ⟨uZ, fZ, gZ⟩ := ResTrans.layer (E := E) (hx 2) (hx0 2) nu.map_one sZ ht2
  have hb1 : nu (if sZ then x 2 else 1) = 1 := by
    cases sZ
    · exact nu.map_one
    · exact uZ rfl
  obtain ⟨uY, fY, gY⟩ := ResTrans.layer (E := E) (hx 0) (hx0 0) hb1 sY ht1
  have hb0 : nu (if sY then x 0 else if sZ then x 2 else 1) = 1 := by
    cases sY
    · exact hb1
    · exact uY rfl
  obtain ⟨-, fR, gR⟩ := ResTrans.layer (E := E) (hx 1) (hx0 1) hb0 sR ht0
  have k1 : ResTrans E nu (if sZ then x 2 else 1) → ResTrans E nu (x 2) := by
    cases sZ
    · exact fun h => absurd h not_resTrans_one
    · exact id
  have k0 : ResTrans E nu (if sY then x 0 else if sZ then x 2 else 1) →
      ResTrans E nu (x 0) ∨ ResTrans E nu (x 2) := by
    cases sY
    · exact fun h => Or.inr (k1 h)
    · exact Or.inl
  rw [← e2] at fZ gZ
  rw [← e1] at fY gY
  rw [← e0] at fR gR
  have hZ : ResTrans E nu (x 2) → ∃ i, ResTrans E nu (lmono x (chartExp sR sY sZ i)) := fun h =>
    (fZ h).elim (fun h' => ⟨2, h'⟩) fun h' => absurd h' not_resTrans_one
  have hY : ResTrans E nu (x 0) → ∃ i, ResTrans E nu (lmono x (chartExp sR sY sZ i)) := fun h =>
    (fY h).elim (fun h' => ⟨1, h'⟩) fun h' => hZ (k1 h')
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · exact hY hj
    · exact (fR hj).elim (fun h' => ⟨0, h'⟩) fun h' => (k0 h').elim hY hZ
    · exact hZ hj
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact (gR hi).elim (fun h' => ⟨1, h'⟩) fun h' => (k0 h').elim (fun h'' => ⟨0, h''⟩)
        fun h'' => ⟨2, h''⟩
    · exact (gY hi).elim (fun h' => ⟨0, h'⟩) fun h' => ⟨2, k1 h'⟩
    · exact (gZ hi).elim (fun h' => ⟨2, h'⟩) fun h' => absurd h' not_resTrans_one
end ResTrans
section Curve
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
theorem BR_eq_zero_iff (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (A : MvPolynomial (Fin 3) E) : RCN002.coordinateEvaluation E P A = 0 ↔ A ∈ P := by
  rw [← RingHom.mem_ker]
  exact (RCN002.coordinateEvaluation_ker E P).symm ▸ Iff.rfl
omit [G.IsPrime] in
theorem mem_map_mk_iff (hGC : G ≤ C) (A : MvPolynomial (Fin 3) E) :
    Ideal.Quotient.mk G A ∈ C.map (Ideal.Quotient.mk G) ↔ A ∈ C := by
  have h := RCN186.quotientPrime_comap_quotientMk G C hGC
  rw [RCN186.quotientPrime] at h
  exact ⟨fun hA => h ▸ Ideal.mem_comap.mpr hA, fun hA => Ideal.mem_map_of_mem _ hA⟩
variable {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem val_le_one (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    S.val (RCN002.coordinateEvaluation E G A) ≤ 1 := by
  obtain ⟨hmem, -⟩ := h A
  exact (Valuation.mem_valuationSubring_iff _ _).mp hmem
theorem val_lt_one_iff (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    S.val (RCN002.coordinateEvaluation E G A) < 1 ↔ A ∈ C := by
  obtain ⟨hmem, hres⟩ := h A
  rw [← S.res_eq_zero_iff ⟨_, hmem⟩, hres, BR_eq_zero_iff]
theorem val_eq_one (h : IsCurveOnSurface G C S) {A : MvPolynomial (Fin 3) E} (hA : A ∉ C) :
    S.val (RCN002.coordinateEvaluation E G A) = 1 :=
  le_antisymm (val_le_one h A) (not_lt.mp fun hlt => hA ((val_lt_one_iff h A).mp hlt))
theorem resTrans_coordinate (h : IsCurveOnSurface G C S) {j : Fin 3}
    (hj : Transcendental E (coordinate E C j)) : ResTrans E S.val (coordinate E G j) := by
  refine resTrans_of_forall fun p hp => ?_
  rw [coordinate, Polynomial.aeval_algHom_apply]
  refine val_eq_one h fun hmem => hp (transcendental_iff.mp hj p ?_)
  rw [coordinate, Polynomial.aeval_algHom_apply]
  exact (BR_eq_zero_iff C _).mpr hmem
theorem val_eq (hGC : G ≤ C) [(C.map (Ideal.Quotient.mk G)).IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime (C.map (Ideal.Quotient.mk G))))
    (h : IsCurveOnSurface G C S) {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰} (hnu : Function.Surjective nu)
    (hle : ∀ A : MvPolynomial (Fin 3) E, nu (RCN002.coordinateEvaluation E G A) ≤ 1)
    (hmem : ∀ A : MvPolynomial (Fin 3) E, A ∈ C ↔ nu (RCN002.coordinateEvaluation E G A) < 1) : S.val = nu := by
  refine valuation_eq_of_dvr (RCN002.CoordinateField E G) (C.map (Ideal.Quotient.mk G)) hdvr S.surjective
    (fun a => ?_) (fun a => ?_) hnu (fun a => ?_) fun a => ?_ <;>
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
  · exact val_le_one h A
  · exact (val_lt_one_iff h A).trans (mem_map_mk_iff hGC A).symm
  · exact hle A
  · exact (hmem A).symm.trans (mem_map_mk_iff hGC A).symm
theorem exists_centre {sR sY sZ : Bool} {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰}
    (h : SurfaceDivisor G sR sY sZ nu) (hc : ∀ j, coordinate E G j ≠ 0)
    (hx : ∀ j, nu (coordinate E G j) ≤ 1) (g : MvPolynomial (Fin 3) E) (hg : Irreducible g)
    (hG : G = Ideal.span {g}) :
    ∃ C : Ideal (MvPolynomial (Fin 3) E), C.IsPrime ∧ G ≤ C ∧ C.height = 2 ∧
      (∀ A : MvPolynomial (Fin 3) E, nu (RCN002.coordinateEvaluation E G A) ≤ 1) ∧
      ∀ A : MvPolynomial (Fin 3) E, A ∈ C ↔ nu (RCN002.coordinateEvaluation E G A) < 1 := by
  obtain ⟨t, htA, htr, ht1⟩ := h.nonconst
  have hRT : ResTrans E nu t := ⟨htr, ht1⟩
  have hpoly : ∀ A : MvPolynomial (Fin 3) E, nu (RCN002.coordinateEvaluation E G A) ≤ 1 := by
    intro A
    induction A using MvPolynomial.induction_on with
    | C a => exact ((RCN002.coordinateEvaluation E G).commutes a).symm ▸ hRT.le_one_algebraMap a
    | add p q hp hq =>
      rw [map_add]
      exact (nu.map_add _ _).trans (max_le hp hq)
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      exact mul_le_one' hp (hx i)
  have hIT : ∀ a : RCN002.CoordinateRing E G, nu (algebraMap (RCN002.CoordinateRing E G) (RCN002.CoordinateField E G) a) ≤ 1 := fun a => by
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hpoly A
  have hcp := Surf.centre_isPrime (RCN002.CoordinateField E G) nu hIT
  let C : Ideal (MvPolynomial (Fin 3) E) := (centre (RCN002.CoordinateField E G) nu hIT).comap (Ideal.Quotient.mk G)
  have hC : C.IsPrime := Ideal.comap_isPrime _ _
  have hmemC : ∀ A : MvPolynomial (Fin 3) E, A ∈ C ↔ nu (RCN002.coordinateEvaluation E G A) < 1 := fun A => Iff.rfl
  have hGC : G ≤ C := fun A hA => (hmemC A).mpr (by
    rw [(BR_eq_zero_iff G A).mpr hA, map_zero]
    exact zero_lt_one)
  have hlt : G < C := lt_of_le_of_ne hGC fun heq =>
    Surf.centre_ne_bot (RCN002.CoordinateField E G) nu h.surjective hIT (by
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective (centre (RCN002.CoordinateField E G) nu hIT)]
      change C.map (Ideal.Quotient.mk G) = ⊥
      rw [← heq, Ideal.map_quotient_self])
  have hG1 : G.height = 1 := hG ▸ Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hg.ne_zero) hg.not_isUnit
  have h2 : 2 ≤ C.height := by
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rwa [hG1, one_add_one_eq_two] at h3
  have hnmax : ¬C.IsMaximal := by
    intro hmax
    obtain ⟨k, hk⟩ := (chart_resTrans (E := E) (coordinate E G) hc hx sR sY sZ fun i =>
      h.le_one _ (Algebra.subset_adjoin ⟨i, rfl⟩)).mpr
      (exists_trivial_on_generator nu _ h.le_one t htA htr ht1)
    obtain ⟨q, hqm, hq⟩ := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing C
      (Ideal.Quotient.mk C (MvPolynomial.X k))
    have hqC : Polynomial.aeval (MvPolynomial.X k : MvPolynomial (Fin 3) E) q ∈ C := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.aeval_def, Polynomial.hom_eval₂]
      exact hq
    have h3 := (hmemC _).mp hqC
    rw [← Polynomial.aeval_algHom_apply] at h3
    have h4 := hk.2 _ (IntermediateField.algebra_adjoin_le_adjoin E _
      (Polynomial.aeval_mem_adjoin_singleton E _))
      fun h0 => hqm.ne_zero (transcendental_iff.mp hk.1 q h0)
    exact absurd h3 (by rw [coordinate] at h4; rw [h4]; exact lt_irrefl _)
  have h3 : C.height ≤ 2 := by
    obtain ⟨M, hM, hCM⟩ := Ideal.exists_le_maximal C hC.ne_top
    have hMp := hM.isPrime
    have h4 := Ideal.height_add_one_le_of_lt_of_isPrime
      (lt_of_le_of_ne hCM fun heq => hnmax (heq ▸ hM))
    have h5 : (M.height : WithBot ℕ∞) ≤ 3 := by
      have h6 := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
      rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
        Nat.card_fin, zero_add] at h6
    by_contra hgt
    have h6 : (2 : ℕ∞) + 1 ≤ C.height := Order.add_one_le_of_lt (not_le.mp hgt)
    have h7 : (((2 : ℕ∞) + 1 + 1 : ℕ∞) : WithBot ℕ∞) ≤ 3 :=
      (WithBot.coe_le_coe.mpr ((add_le_add_left h6 1).trans h4)).trans h5
    exact absurd h7 (by decide)
  exact ⟨C, hC, hGC, le_antisymm h3 h2, hpoly, hmemC⟩
end Curve
end LevelSurf
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
open RCN002 RCN055 RCN086 RCN095 RCN135 RCN136 RCN204 RCN313
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Component
variable {K : Type} [Field K] (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
  (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
  (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {F})
theorem Curve.sliceEmbedding_sliceProj (A : MvPolynomial (Fin 4) K) :
    HFree6812.sliceEmbedding G F hker (sliceProj F A) = SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A :=
  HFree6812.sliceEmbedding_proj G F hker A
theorem Curve.sliceEmbedding_coord (j : Fin 3) :
    HFree6812.sliceEmbedding G F hker (sliceCoord F j) = coordinate (GenericField K) G j := by
  rw [show sliceCoord F j = sliceProj F (MvPolynomial.X j.succ) from rfl,
    Curve.sliceEmbedding_sliceProj, GP_X_succ]
theorem Curve.sliceEmbedding_sigma :
    HFree6812.sliceEmbedding G F hker (sliceSigma F F) = SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyG K F) / SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyH K F) := by
  rw [sliceSigma, map_div₀, Curve.sliceEmbedding_sliceProj, Curve.sliceEmbedding_sliceProj]
omit [Fact (Irreducible F)] in
include hker in
theorem Curve.surfaceMap_mem_of_ker : surfaceMap (RCN135.polynomialEmbedding K) F ∈ G := by
  have h : F ∈ RingHom.ker (sliceMap (K := K) G) := by
    rw [hker]
    exact Ideal.mem_span_singleton_self F
  exact (SecondJetComponentRoots.evaluation_zero_iff G _).mp (RingHom.mem_ker.mp h)
include hker in
theorem Curve.sliceProj_ne_zero_of_notMem (C : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (hGC : G ≤ C) (A : MvPolynomial (Fin 4) K) (hA : surfaceMap (RCN135.polynomialEmbedding K) A ∉ C) : sliceProj F A ≠ 0 := fun h0 =>
  hA (hGC ((SecondJetComponentRoots.evaluation_zero_iff G _).mp (show SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G A = 0 by
    rw [← Curve.sliceEmbedding_sliceProj F G hker, h0, map_zero])))
theorem sliceEmbedding_tail (hH : sliceProj F (polyH K F) ≠ 0) (n : ℕ) :
    HFree6812.sliceEmbedding G F hker (tail F F (dvd_refl F) (n + 1)) =
      SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (RCN055.baseNumerator F n) / SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyH K F) ^ (2 * n + 1) := by
  rw [tail, show sliceCoord F 1 = sliceProj F (MvPolynomial.X 2) from rfl, HFree6812.sliceDerivation_iterate F F (dvd_refl F) hH n,
    map_div₀, map_pow, Curve.sliceEmbedding_sliceProj, Curve.sliceEmbedding_sliceProj]
end Component
section Stage
open RCN074 RCN159 RCN238 RCN243 RCN244 RCN264
variable {K I : Type} [Field K] {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
theorem tail_val_le_multiplicity (S : Stage_p19 K I Gamma x p flag errorCap stageSupport)
    [Fact (Irreducible S.F)] (C : CM S) (Lf : ERB S)
    (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {S.F})
    (Sa : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) C.1))
    (hSa : IsCurveOnSurface G C.1 Sa) :
    Sa.val (HFree6812.sliceEmbedding G S.F hker (tail S.F S.F (dvd_refl S.F) RCN326.w)) ≤ exp (-(FO S Lf C : ℤ)) := by
  have hirr : Irreducible S.F := Fact.out
  have hHC : surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F) ∉ C.1 := _Q6 (GenericField K) _ _ _ C
  have hvH : Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyH K S.F)) = 1 :=
    (hSa.restricts_GP (RCN135.polynomialEmbedding K) _).val_eq_one fun h => hHC ((SecondJetComponentRoots.evaluation_zero_iff C.1 _).1 h)
  have hu : IsUnit (originalData_p19 S C).cofactor :=
    (hirr.isUnit_or_isUnit (originalData_p19 S C).product).resolve_left
      (originalData_p19 S C).irreducible.not_isUnit
  have hfac : surfaceMap (RCN135.polynomialEmbedding K) (originalData_p19 S C).factor ∈ G := by
    have h1 := Curve.surfaceMap_mem_of_ker S.F G hker
    rw [(originalData_p19 S C).product, map_mul] at h1
    exact (Ideal.mul_unit_mem_iff_mem G (hu.map (surfaceMap (RCN135.polynomialEmbedding K)))).mp h1
  have hvc : Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (originalData_p19 S C).cofactor) = 1 :=
    (hSa.restricts_GP (RCN135.polynomialEmbedding K) _).val_eq_one fun h =>
      (originalData_p19 S C).EYH ((SecondJetComponentRoots.evaluation_zero_iff C.1 _).1 h)
  have hrel : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K S.F (RCN326.w + 1)) =
      SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (originalData_p19 S C).cofactor ^ (2 * (RCN326.w + 1)) *
        SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K (originalData_p19 S C).factor (RCN326.w + 1)) := by
    obtain ⟨q, hq⟩ := RCN217.AKR (originalData_p19 S C).factor (originalData_p19 S C).cofactor S.F
      (originalData_p19 S C).product (RCN326.w + 1)
    have h0 : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (originalData_p19 S C).factor = 0 := (SecondJetComponentRoots.evaluation_zero_iff G _).mpr hfac
    have h1 := congrArg (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G) hq
    rwa [map_sub, map_mul, map_mul, map_pow, h0, zero_mul, sub_eq_zero] at h1
  have htail : Sa.val (HFree6812.sliceEmbedding G S.F hker (tail S.F S.F (dvd_refl S.F) RCN326.w)) =
      Sa.val (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K (originalData_p19 S C).factor (RCN326.w + 1))) := by
    have h1 : HFree6812.sliceEmbedding G S.F hker (tail S.F S.F (dvd_refl S.F) RCN326.w) = _ := sliceEmbedding_tail S.F G hker
      (Curve.sliceProj_ne_zero_of_notMem S.F G hker C.1 hSa.ideal_le _ hHC) 131070
    have h2 : numerator K S.F (RCN326.w + 1) = polyH K S.F ^ 3 * RCN055.baseNumerator S.F 131070 := RCN055.numerator_eq_H_cube S.F 131070
    rw [h1, map_div₀, map_pow, hvH, one_pow, div_one]
    rw [h2, map_mul, map_pow] at hrel
    have h3 := congrArg Sa.val hrel
    rwa [map_mul, map_pow, hvH, one_pow, one_mul, map_mul, map_pow, hvc, one_pow, one_mul] at h3
  rw [htail]
  by_cases hN : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (numerator K (originalData_p19 S C).factor (RCN326.w + 1)) = 0
  · rw [hN, map_zero]
    exact zero_le
  · obtain ⟨e, he, hval⟩ := liveCurve_val_tail S C Lf G hfac Sa hSa hN
    rw [hval, exp_le_exp, neg_le_neg_iff]
    exact_mod_cast Nat.le_mul_of_pos_left _ he
end Stage
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
open MvPolynomial WithZero HFree6812
open RCN313 RCN095 RCN204 BD
open RCN095 renaming PolynomialInFlag → BI
open MovingFiberThreeSources6811 (direction weight)
namespace Chart
variable {K : Type} [Field K] [CharP K 2130706433]
theorem common_place_law (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N)
    (hN9 : N ≤ 9678) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) :
    ChartPlaceLaw F F₀ hdvd sR sY sZ := by
  have hF := ne_zero_of_polyH_ne_zero F F₀ hH
  have hNp : 4 * N ^ 2 < 2130706433 := by
    have h := Nat.mul_le_mul hN9 hN9
    rw [pow_two]
    omega
  exact chartDivisor_place_law F F₀ hdvd hH N hN hNp hc sR sY sZ
    (chart_core_poly_of_dvd F F₀ hdvd hF N hN hc sR sY sZ)
    (chart_two_coord_of_dvd F F₀ hdvd hF N hN hc sR sY sZ)
theorem common_krull (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N)
    (hN9 : N ≤ 9678) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (sR sY sZ : Bool) : ChartKrull F₀ sR sY sZ :=
  chart_krull_of_dvd F F₀ hdvd hH N hN hN9 hc sR sY sZ
theorem common_psiS_integral (F F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hH : sliceProj F₀ (polyH K F) ≠ 0) (N : ℕ) (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N)
    (hN9 : N ≤ 9678) (hc : ∀ j, sliceCoord F₀ j ≠ 0) (S : MovingFiberThreeSources6811.Source F)
    (hfact : (S.k.factorial : K) ≠ 0) (hlead : srcLead F F₀ S ≠ 0) (Hf : FlagDegree)
    (h5 : 5 ≤ 2 * Hf.all)
    (hHf : ∀ w : Valuation (SliceField F₀) ℤᵐ⁰,
      (∀ a : K, a ≠ 0 → w (algebraMap K (SliceField F₀) a) = 1) →
      w (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 →
      w (sliceProj F₀ (polyH K F)) ≤ exp (flagPole w (sliceCoord F₀) Hf))
    (sR sY sZ : Bool) : PsiSIntegral F F₀ hdvd S Hf sR sY sZ :=
  psiS_integral F F₀ hdvd hH (Ring.two_ne_zero (by rw [ringChar.eq K 2130706433]; norm_num)) S hfact
    hlead hc Hf h5 hHf sR sY sZ (common_krull F F₀ hdvd hH N hN hN9 hc sR sY sZ)
    (common_place_law F F₀ hdvd hH N hN hN9 hc sR sY sZ)
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
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Level
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L]
theorem zeroDivisor_apply {x : L} (hx : x ≠ 0) (P : PrimeDivisor O) :
    zeroDivisor (O := O) L x P = (-(P.valuation L x).log).toNat :=
  LevelSurf.zeroDivisor_apply L hx P
variable {E : Type*} [Field E] [Algebra E L]
theorem levelIdeal_eq_span (f : L) (c : E) (g : O) (hg : algebraMap O L g = f - algebraMap E L c)
    (hg0 : g ≠ 0) (n : ℕ) : levelIdeal L f c n = Ideal.span {g ^ n} := by
  rw [levelIdeal, levelDivisor, ← hg, LevelSurf.zeroDivisor_algebraMap L hg0,
    LevelSurf.nsmul_div L hg0, divisorIdeal_div L (pow_ne_zero n hg0)]
end Level
section LevelValue
variable {L : Type*} [Field L] {E : Type*} [Field E] [Algebra E L]
theorem level_value_unique (v : Valuation L ℤᵐ⁰)
    (hv : ∀ a : E, a ≠ 0 → v (algebraMap E L a) = 1) (f : L) {c c' : E}
    (h : v (f - algebraMap E L c) < 1) (h' : v (f - algebraMap E L c') < 1) : c = c' := by
  by_contra hne
  have h1 := hv _ (sub_ne_zero.mpr hne)
  rw [map_sub, ← sub_sub_sub_cancel_left _ _ f] at h1
  exact absurd h1 (ne_of_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h' h)))
theorem finite_level_values (S : Set (Valuation L ℤᵐ⁰)) (hS : S.Finite)
    (hv : ∀ v ∈ S, ∀ a : E, a ≠ 0 → v (algebraMap E L a) = 1) (f : L) :
    {c : E | ∃ v ∈ S, v (f - algebraMap E L c) < 1}.Finite := by
  refine (hS.biUnion fun v hvS => (show {c : E | v (f - algebraMap E L c) < 1}.Subsingleton from
    fun c hc c' hc' => level_value_unique v (hv v hvS) f hc hc').finite).subset ?_
  rintro c ⟨v, hvS, hc⟩
  exact Set.mem_biUnion hvS hc
end LevelValue
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
variable {N p : ℕ} [CharP E p]
theorem finite_surfaceDivisor_ne_one (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (x : RCN002.CoordinateField E G) (hx : x ≠ 0) :
    {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧ nu x ≠ 1}.Finite := by
  refine (Set.finite_iUnion fun u : Bool × Bool × Bool =>
    LevelSurf.finite_surfaceDivisor_chart (hN u.1 u.2.1 u.2.2) hp x hx).subset ?_
  rintro nu ⟨⟨sR, sY, sZ, h⟩, hne⟩
  exact Set.mem_iUnion.mpr ⟨(sR, sY, sZ), h, hne⟩
theorem finite_level_exclusion (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (hc : ∀ j, coordinate E G j ≠ 0) (H : RCN002.CoordinateField E G) (hH : H ≠ 0) (f : RCN002.CoordinateField E G) :
    {c : E | ∃ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
      nu (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 ∧
      (nu H ≠ 1 ∨ ∃ j, 1 < nu (coordinate E G j))}.Finite := by
  have hfin : {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
      (nu H ≠ 1 ∨ ∃ j, 1 < nu (coordinate E G j))}.Finite := by
    refine ((finite_surfaceDivisor_ne_one hN hp H hH).union (Set.finite_iUnion fun j =>
      finite_surfaceDivisor_ne_one hN hp (coordinate E G j) (hc j))).subset ?_
    rintro nu ⟨h, h1 | ⟨j, hj⟩⟩
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, h, hj.ne'⟩)
  refine (finite_level_values _ hfin (fun nu hnu a ha => ?_) f).subset ?_
  · obtain ⟨⟨sR, sY, sZ, h⟩, -⟩ := hnu
    obtain ⟨t, -, -, ht⟩ := h.nonconst
    exact ht _ (IntermediateField.algebraMap_mem _ a)
      ((map_ne_zero_iff _ (algebraMap E (RCN002.CoordinateField E G)).injective).mpr ha)
  · rintro c ⟨nu, h, hlt, hbad⟩
    exact ⟨nu, ⟨h, hbad⟩, hlt⟩
variable {F : Type*} [Field F] [Algebra E F]
theorem finite_basePoints (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (f : RCN002.CoordinateField E G) (c : E) (hf : f ≠ algebraMap E (RCN002.CoordinateField E G) c) :
    {q : SurfacePoint G | f ∉ q.ring ∧ q.level f c ≠ 0}.Finite := by
  have hx : f - algebraMap E (RCN002.CoordinateField E G) c ≠ 0 := sub_ne_zero.mpr hf
  refine (Set.finite_iUnion fun u : Bool × Bool × Bool =>
    LevelSurf.finite_basePoints_chart hN hp u.1 u.2.1 u.2.2 _ hx).subset ?_
  rintro q ⟨hfq, hl⟩
  refine Set.mem_iUnion.mpr ⟨q.chartOf, rfl,
    LevelSurf.exists_valuation_lt_one_of_zeroDivisor_ne_zero _ hx hl, ?_⟩
  by_contra hno
  obtain ⟨a, ha⟩ := mem_range_of_valuation_le_one (RCN002.CoordinateField E G) (f - algebraMap E (RCN002.CoordinateField E G) c)
    fun P => not_lt.mp fun hP => hno ⟨P, hP⟩
  have h1 := q.ring.add_mem a.2 (q.ring.algebraMap_mem c)
  rw [show (a : RCN002.CoordinateField E G) = f - algebraMap E (RCN002.CoordinateField E G) c from ha, sub_add_cancel] at h1
  exact hfq h1
omit [Algebra E F] in
theorem finite_levelPoints (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (S : Specialization (RCN002.CoordinateField E G) F) (f : RCN002.CoordinateField E G) (c : E)
    (hS : S.val (f - algebraMap E (RCN002.CoordinateField E G) c) = 1) :
    {q : SurfacePoint G | q.On S ∧ q.level f c ≠ 0}.Finite := by
  have hx : f - algebraMap E (RCN002.CoordinateField E G) c ≠ 0 := fun h => by
    rw [h, map_zero] at hS
    exact zero_ne_one hS
  refine (Set.finite_iUnion fun u : Bool × Bool × Bool =>
    LevelSurf.finite_levelPoints_chart hN hp u.1 u.2.1 u.2.2 S _ hS).subset ?_
  rintro q ⟨hOn, hl⟩
  exact Set.mem_iUnion.mpr ⟨q.chartOf, rfl, hOn,
    LevelSurf.exists_valuation_lt_one_of_zeroDivisor_ne_zero _ hx hl⟩
end Surface
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
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Curve
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
theorem exists_isCurveOnSurface (hGC : G ≤ C) [hC : (C.map (Ideal.Quotient.mk G)).IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime (C.map (Ideal.Quotient.mk G)))) :
    ∃ S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C), IsCurveOnSurface G C S := by
  let φ : RCN002.CoordinateRing E G →+* RCN002.CoordinateField E C := Ideal.Quotient.lift G (RCN002.coordinateEvaluation E C).toRingHom fun a ha =>
    (LevelSurf.BR_eq_zero_iff C a).mpr (hGC ha)
  have hφ : ∀ A : MvPolynomial (Fin 3) E, φ (Ideal.Quotient.mk G A) = RCN002.coordinateEvaluation E C A := fun A =>
    Ideal.Quotient.lift_mk G _ _
  have hker : RingHom.ker φ = C.map (Ideal.Quotient.mk G) := by
    ext a
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, hφ, LevelSurf.mem_map_mk_iff hGC, LevelSurf.BR_eq_zero_iff]
  have hsurj : ∀ y : RCN002.CoordinateField E C, ∃ a s : RCN002.CoordinateRing E G, s ∉ C.map (Ideal.Quotient.mk G) ∧ y * φ s = φ a := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RCN002.CoordinateRing E C) y
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hB0 : algebraMap (RCN002.CoordinateRing E C) (RCN002.CoordinateField E C) (Ideal.Quotient.mk C B) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RCN002.CoordinateRing E C) (RCN002.CoordinateField E C))).mpr
        (nonZeroDivisors.ne_zero hb)
    refine ⟨Ideal.Quotient.mk G A, Ideal.Quotient.mk G B, fun hB => ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero hb
        (Ideal.Quotient.eq_zero_iff_mem.mpr ((LevelSurf.mem_map_mk_iff hGC B).mp hB))
    · rw [hφ, hφ]
      exact div_mul_cancel₀ _ hB0
  obtain ⟨S, hS⟩ := LevelSurf.exists_specialization (RCN002.CoordinateField E G) (C.map (Ideal.Quotient.mk G)) hdvr φ
    hker hsurj
  exact ⟨S, fun A => (hS (Ideal.Quotient.mk G A)).imp fun _ h => h.trans (hφ A)⟩
theorem isDiscreteValuationRing_of_pderiv_notMem (g : MvPolynomial (Fin 3) E) (hg : Irreducible g)
    (hG : G = Ideal.span {g}) (hgC : g ∈ C) (hC2 : C.height = 2) (j : Fin 3)
    (hj : MvPolynomial.pderiv j g ∉ C) [hC : (C.map (Ideal.Quotient.mk G)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (C.map (Ideal.Quotient.mk G))) :=
  LevelSurf.isDiscreteValuationRing_quotient_of_pderiv_notMem g hg.ne_zero G C hG
    (hG ▸ (Ideal.span_singleton_le_iff_mem _).mpr hgC) hC2 j hj
theorem IsCurveOnSurface.le {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)} (h : IsCurveOnSurface G C S) :
    G ≤ C := fun A hA =>
  (LevelSurf.val_lt_one_iff h A).mp (by
    rw [(LevelSurf.BR_eq_zero_iff G A).mpr hA, map_zero]
    exact zero_lt_one)
theorem IsCurveOnSurface.trivial_on_constants {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (a : E) (ha : a ≠ 0) : S.val (algebraMap E (RCN002.CoordinateField E G) a) = 1 := by
  rw [← (RCN002.coordinateEvaluation E G).commutes a]
  exact LevelSurf.val_eq_one h fun hmem => ‹C.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem C hmem
    ((IsUnit.mk0 a ha).map (algebraMap E (MvPolynomial (Fin 3) E))))
theorem IsCurveOnSurface.surfaceDivisor {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (hc : ∀ j, coordinate E G j ≠ 0)
    (htr : ∃ j, Transcendental E (coordinate E C j)) (sR sY sZ : Bool)
    (hle : ∀ i, S.val (lmono (coordinate E G) (chartExp sR sY sZ i)) ≤ 1) :
    SurfaceDivisor G sR sY sZ S.val := by
  obtain ⟨j, hj⟩ := htr
  obtain ⟨i, hi⟩ := (LevelSurf.chart_resTrans (E := E) (coordinate E G) hc
    (fun j => LevelSurf.val_le_one h (MvPolynomial.X j)) sR sY sZ hle).mp
    ⟨j, LevelSurf.resTrans_coordinate h hj⟩
  refine ⟨S.surjective, fun a ha => ?_, ⟨_, Algebra.subset_adjoin ⟨i, rfl⟩, hi.1, hi.2⟩⟩
  rw [surfaceChartRing] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hle i
  | algebraMap r => exact hi.le_one_algebraMap r
  | add x y _ _ ihx ihy => exact (S.val.map_add _ _).trans (max_le ihx ihy)
  | mul x y _ _ ihx ihy =>
    rw [map_mul]
    exact mul_le_one' ihx ihy
theorem SurfaceDivisor.exists_isCurveOnSurface {sR sY sZ : Bool} {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰}
    (h : SurfaceDivisor G sR sY sZ nu) (hc : ∀ j, coordinate E G j ≠ 0)
    (hx : ∀ j, nu (coordinate E G j) ≤ 1)
    (g : MvPolynomial (Fin 3) E) (hg : Irreducible g) (hG : G = Ideal.span {g}) (j : Fin 3)
    (hj : nu (RCN002.coordinateEvaluation E G (MvPolynomial.pderiv j g)) = 1) :
    ∃ (C : Ideal (MvPolynomial (Fin 3) E)) (_ : C.IsPrime) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)),
      IsCurveOnSurface G C S ∧ S.val = nu ∧ C.height = 2 ∧ MvPolynomial.pderiv j g ∉ C := by
  obtain ⟨C, hC, hGC, hC2, hpoly, hmemC⟩ := LevelSurf.exists_centre h hc hx g hg hG
  have hCq : (C.map (Ideal.Quotient.mk G)).IsPrime := RCN186.quotientPrime_isPrime G C hGC
  have hjC : MvPolynomial.pderiv j g ∉ C := fun hm =>
    absurd ((hmemC _).mp hm) (by rw [hj]; exact lt_irrefl _)
  have hdvr := isDiscreteValuationRing_of_pderiv_notMem g hg hG
    (hGC (hG ▸ Ideal.mem_span_singleton_self g)) hC2 j hjC
  obtain ⟨S, hS⟩ := FormalR.exists_isCurveOnSurface hGC hdvr
  exact ⟨C, hC, S, hS, LevelSurf.val_eq hGC hdvr hS h.surjective hpoly hmemC, hC2, hjC⟩
theorem IsCurveOnSurface.res_movingValue {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (H Gs Q U : MvPolynomial (Fin 3) E) (hH : H ∉ C) :
    ∃ hf : RCN208.movingValue G H Gs Q U ∈ S.val.valuationSubring,
      S.res ⟨RCN208.movingValue G H Gs Q U, hf⟩ = RCN208.movingValue C H Gs Q U := by
  obtain ⟨hQ, hQr⟩ := h Q
  obtain ⟨hU, hUr⟩ := h U
  obtain ⟨hGs, hGr⟩ := h Gs
  obtain ⟨hHm, hHr⟩ := h H
  have hH1 := LevelSurf.val_eq_one h hH
  have hH0 : RCN002.coordinateEvaluation E G H ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hH1
    exact zero_ne_one hH1
  have hHi : (RCN002.coordinateEvaluation E G H)⁻¹ ∈ S.val.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hH1, inv_one]
  have hinv : S.res ⟨(RCN002.coordinateEvaluation E G H)⁻¹, hHi⟩ = (RCN002.coordinateEvaluation E C H)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hHr, ← map_mul, ← map_one S.res]
    exact congrArg S.res (Subtype.ext (mul_inv_cancel₀ hH0))
  have hx : RCN208.movingValue G H Gs Q U = ((⟨_, hQ⟩ + ⟨_, hU⟩ * ⟨_, hGs⟩ * ⟨_, hHi⟩ :
      S.val.valuationSubring) : RCN002.CoordinateField E G) := by
    rw [RCN208.movingValue, div_eq_mul_inv]
    rfl
  refine ⟨hx ▸ SetLike.coe_mem _, ?_⟩
  rw [show (⟨RCN208.movingValue G H Gs Q U, hx ▸ SetLike.coe_mem _⟩ : S.val.valuationSubring) =
    ⟨_, hQ⟩ + ⟨_, hU⟩ * ⟨_, hGs⟩ * ⟨_, hHi⟩ from Subtype.ext hx, map_add, map_mul, map_mul, hQr,
    hUr, hGr, hinv, RCN208.movingValue, div_eq_mul_inv]
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
section Packet
noncomputable section
open scoped Classical
open WithZero HFree6812
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN222 RCN238 RCN243 RCN244 RCN264 RCN313 RCN334
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open DU BOE BD
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
attribute [local instance] Exch.component_isPrime
variable (P : Packet x t y r) [Fact (Irreducible P.F)] (a : Curve P)
  (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
  (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {P.F})
  {Sa : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) a.2.1)}
theorem packet_tail_val_le_multiplicity (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (hSa : IsCurveOnSurface G a.2.1 Sa) :
    Sa.val (HFree6812.sliceEmbedding G P.F hker (tail P.F P.F (dvd_refl P.F) w)) ≤ exp (-(multiplicity P hp a : ℤ)) := by
  have hF : Fact (Irreducible (MU (P.stage a.1)).F) := ‹Fact (Irreducible P.F)›
  exact tail_val_le_multiplicity (MU (P.stage a.1)) a.2
    (DN (MU (P.stage a.1)) (P.stage_proper hp a.1)) G hker Sa hSa
omit [Fact (Irreducible P.F)] in
theorem tail_order (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField (GenericField K) (Exch.component P a.1))
      (RCN002.CoordinateField (GenericField K) a.2.1))
    (hS : ∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) :
    Exch.TailOrder P hp SZ S := by
  intro a ha
  have h := @packet_tail_val_le_multiplicity K I _ _ x t y r P ⟨P.irreducible⟩ a
    (Exch.component P a.1) _ (Exch.ker_sliceMap_component P a.1) (S a) hp (hS a ha)
  unfold Exch.embedding
  exact h
end
end Packet
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
section Component
noncomputable section
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN135 RCN136 RCN187 RCN204 RCN313
open RCN095 renaming PolynomialInFlag → BI
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
variable {K : Type} [Field K]
namespace Curve
def psiC (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {F}) (f : RCN002.CoordinateField (GenericField K) G)
    (c : GenericField K) (m : ℕ) : RCN002.CoordinateField (GenericField K) G :=
  HFree6812.sliceEmbedding G F hker (tail F F (dvd_refl F) m ^ 3 * sliceProj F (polyH K F) ^ (2 * m)) /
    (f - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) G) c) ^ (4 * m)
def StepOne (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {F}) (Hf : FlagDegree)
    (f : RCN002.CoordinateField (GenericField K) G) (c : GenericField K) : Prop :=
  ∀ (q : SurfacePoint G) (B : PrimeDivisor q.ring) (m : ℕ),
    B.valuation (RCN002.CoordinateField (GenericField K) G) (psiC F G hker f c m /
        lmono (coordinate (GenericField K) G)
          (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 (cutFlag m Hf))) ≤
      exp (4 * m * (q.level f c B : ℤ))
def psiCOn (F : MvPolynomial (Fin 4) K) (C : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    [C.IsPrime] (fC : RCN002.CoordinateField (GenericField K) C) (c : GenericField K) (m : ℕ) : RCN002.CoordinateField (GenericField K) C :=
  tailCubeOn (RCN135.polynomialEmbedding K) F C m / (fC - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) C) c) ^ (4 * (m + 1))
def LevelRestrict (F : MvPolynomial (Fin 4) K) (G C : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    [G.IsPrime] [C.IsPrime] (S : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) C))
    (Hf : FlagDegree) (f : RCN002.CoordinateField (GenericField K) G) (fC : RCN002.CoordinateField (GenericField K) C) (c : GenericField K)
    (m : ℕ) : Prop :=
  ∀ (q : SurfacePoint G) (hq : q.On S) (μ : RCN026.Place_p19 (GenericField K) (RCN002.CoordinateField (GenericField K) C)),
    μ ∈ S.placesOn (GenericField K) hq → ∀ n : ℕ,
      μ.val (psiCOn F C fC c m) ^ n ≤
        exp (n * flagPole μ.val (coordinate (GenericField K) C) (cutFlag (m + 1) Hf) +
          4 * (m + 1) * (S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ))
end Curve
end
end Component
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN156 RCN187 RCN199 RCN222 RCN238 RCN243 RCN264 RCN313
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open DU AFA BOE BD
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime
structure CurveNeeds (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1)) : Prop where
  pole : ∀ a ∈ active P SZ, ∀ (sR sY sZ : Bool)
    (nu : Valuation (RCN002.CoordinateField Ω (Exch.component P a.1)) (WithZero (Multiplicative ℤ))),
    SurfaceDivisor (Exch.component P a.1) sR sY sZ nu →
      placeTOn nu (coordinate Ω (Exch.component P a.1))
        (RCN002.coordinateEvaluation Ω (Exch.component P a.1) (baseG P.F) / RCN002.coordinateEvaluation Ω (Exch.component P a.1) (baseH P.F)) ≤
        poleOrder nu (Exch.moving P Q A a.1)
  off_level : ∀ a ∈ active P SZ,
    (S a).val (Exch.moving P Q A a.1 - algebraMap Ω (RCN002.CoordinateField Ω (Exch.component P a.1)) c) = 1
  seed : ∀ a ∈ active P SZ, ∀ γ ∈ RCN264.componentSeeds Ω (P.stage a.1).G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1))
      (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F) (KK K P.F P.selected P.seeds a.1)
      (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2,
    MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected γ)
      (baseH P.F * (Q - MvPolynomial.C c) + A * baseG P.F) ≠ 0
end
end Packet
end FormalR
end SubmissionLower
end ProximityPrize
end
section
set_option autoImplicit false
namespace ProximityPrize
namespace SubmissionLower
namespace FormalR
open MvPolynomial WithZero HFree6812
open RCN002 RCN095 RCN135 RCN204 RCN222 RCN313 DU BD
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open MovingFiberThreeSources6811 (direction weight)
namespace Chart
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}
attribute [local instance] Exch.component_isPrime
local instance packetFact (P : Packet x t y r) : Fact (Irreducible P.F) := ⟨P.irreducible⟩
theorem packet_polyH_ne_zero (P : Packet x t y r) : sliceProj P.F (polyH K P.F) ≠ 0 := fun h =>
  RCN267.equation_not_dvd_R_derivative P.F 2130706433 P.rdegree (P.IZ.2.1.trans_lt (by have := packet_r_le P; omega))
    ((HFree6812.sliceProj_eq_zero_iff P.F _).1 h)
theorem packet_sliceCoord_ne_zero (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (j : Fin 3) : sliceCoord P.F j ≠ 0 :=
  sliceCoord_ne_zero P.F P.F (dvd_refl P.F) (packet_polyH_ne_zero P) (w - 1)
    (fun h => hp (by
      rw [show w + 1 = w - 1 + 2 from rfl, RCN055.numerator_eq_H_cube]
      exact ((HFree6812.sliceProj_eq_zero_iff P.F _).1 h).mul_left _)) j
theorem packet_coordinate_ne_zero (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (g : RCN222.GeometricFactor K P.F) (j : Fin 3) : coordinate (GenericField K) (Exch.component P g) j ≠ 0 := by
  rw [← psi_coord (Exch.component P g) P.F (Exch.ker_sliceMap_component P g) j]
  exact (map_ne_zero _).2 (packet_sliceCoord_ne_zero P hp j)
theorem surfaceNoether_component (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1))
    (g : RCN222.GeometricFactor K P.F) (sR sY sZ : Bool) : SurfaceNoether (Exch.component P g) sR sY sZ t :=
  surfaceNoether_packet P g (Exch.component P g) rfl (packet_coordinate_ne_zero P hp g 1) sR sY sZ
omit [CharP K 2130706433] in
theorem packet_three_mul_lt (P : Packet x t y r) : 3 * t < 2130706433 := by
  have := packet_t_le P
  omega
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
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Specialization
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
theorem Specialization.resOn_eq_zero_iff (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (a : O) :
    S.resOn hO a = 0 ↔ S.val (algebraMap O L a) < 1 := S.res_eq_zero_iff _
theorem Specialization.image_isNoetherianRing [IsNoetherianRing O] (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) : IsNoetherianRing (S.image hO) :=
  isNoetherianRing_range _
theorem Specialization.image_isLocalRing [IsLocalRing O] (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) : IsLocalRing (S.image hO) :=
  IsLocalRing.of_surjective' (S.resOn hO).rangeRestrict (S.resOn hO).rangeRestrict_surjective
theorem Specialization.image_dimensionLEOne [IsDomain O] [IsFractionRing O L] (hO' : PrimeChain O)
    (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) :
    Ring.DimensionLEOne (S.image hO) := by
  let f : O →+* S.image hO := (S.resOn hO).rangeRestrict
  have hsurj : Function.Surjective f := (S.resOn hO).rangeRestrict_surjective
  have hker : RingHom.ker f = centre L S.val hO := by
    ext a
    rw [RingHom.mem_ker, ← Subtype.coe_inj]
    exact S.resOn_eq_zero_iff hO a
  refine ⟨fun {p} hp0 hp => ?_⟩
  have hlt : centre L S.val hO < p.comap f := by
    rw [← hker]
    refine lt_of_le_of_ne (Ideal.ker_le_comap f) fun heq => hp0 ?_
    rw [← Ideal.map_comap_of_surjective f hsurj p, ← heq, Ideal.map_eq_bot_iff_le_ker]
  have hmax := hO' _ _ (Surf.centre_isPrime L S.val hO) (Ideal.comap_isPrime f p)
    (Surf.centre_ne_bot L S.val S.surjective hO) hlt
  have h2 := Ideal.map_eq_top_or_isMaximal_of_surjective f hsurj hmax
  rw [Ideal.map_comap_of_surjective f hsurj p] at h2
  exact h2.resolve_left hp.ne_top
theorem Specialization.image_isFractionRing [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [IsFractionRing O L] (hO' : PrimeChain O) (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (hmax : ¬(centre L S.val hO).IsMaximal) :
    IsFractionRing (S.image hO) F := by
  obtain ⟨P, hP, hPv⟩ := exists_primeDivisor_of_centre L hO' S.val S.surjective hO hmax
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨x, rfl⟩ := S.res_surjective z
  have hx : P.valuation L (x : L) ≤ 1 := by
    rw [hPv]
    exact (S.val.mem_valuationSubring_iff _).mp x.2
  obtain ⟨a, s, hs, hxs⟩ := (P.valuation_le_one_iff L x).mp hx
  have hs0 : S.resOn hO s ≠ 0 := fun h0 => hs (hP ▸ (S.resOn_eq_zero_iff hO s).mp h0)
  refine ⟨⟨S.resOn hO a, a, rfl⟩, ⟨S.resOn hO s, s, rfl⟩, ?_⟩
  change S.res x = S.resOn hO a / S.resOn hO s
  rw [eq_div_iff hs0]
  change S.res x * S.res _ = S.res _
  rw [← map_mul]
  exact congrArg S.res (Subtype.ext hxs)
theorem finite_integralClosure_of_dedekind (R₁ K₁ : Type*) [CommRing R₁] [IsDedekindDomain R₁]
    [Field K₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁] {B : Type*} [CommRing B] (F : Type*) [Field F]
    [Algebra B F] [Algebra R₁ F] [Algebra K₁ F] [IsScalarTower R₁ K₁ F] [FiniteDimensional K₁ F]
    [Algebra.IsSeparable K₁ F] (h : ∀ r : R₁, ∃ b : B, algebraMap B F b = algebraMap R₁ F r) :
    Module.Finite B (integralClosure B F) := by
  let D := integralClosure R₁ F
  have : IsDedekindDomain D := integralClosure.isDedekindDomain R₁ K₁ F
  have : IsFractionRing D F := integralClosure.isFractionRing_of_finite_extension K₁ F
  have : Module.Finite R₁ D := IsIntegralClosure.finite R₁ K₁ F D
  obtain ⟨T, hT⟩ : (Subalgebra.toSubmodule D).FG := Module.Finite.iff_fg.mp ‹Module.Finite R₁ D›
  have hDint : ∀ d ∈ D, IsIntegral B d := by
    intro d hd
    obtain ⟨p, hp, hpd⟩ := hd
    have hlift : p.map (algebraMap R₁ F) ∈ Polynomial.lifts (algebraMap B F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact h (p.coeff n)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hp.map _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
    exact hpd
  have hDN : ∀ d ∈ D, d ∈ Submodule.span B (T : Set F) := by
    intro d hd
    have hd' : d ∈ Submodule.span R₁ (T : Set F) := hT ▸ hd
    refine Submodule.span_induction (fun x hx => Submodule.subset_span hx) (Submodule.zero_mem _)
      (fun x y _ _ hx hy => Submodule.add_mem _ hx hy) (fun r x _ hx => ?_) hd'
    obtain ⟨b, hb⟩ := h r
    rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
    exact Submodule.smul_mem _ b hx
  have hTD : ∀ t ∈ T, t ∈ D := fun t ht => by
    have : t ∈ Subalgebra.toSubmodule D := hT ▸ Submodule.subset_span ht
    exact this
  let M : Subalgebra B F := Algebra.adjoin B (D : Set F)
  have hMN : Subalgebra.toSubmodule M ≤ Submodule.span B (T : Set F) := by
    change Subalgebra.toSubmodule (Algebra.adjoin B (D : Set F)) ≤ _
    rw [Algebra.adjoin_eq_span,
      show (D : Set F) = ((D.toSubsemiring.toSubmonoid : Submonoid F) : Set F) from rfl,
      Submonoid.closure_eq]
    exact Submodule.span_le.mpr hDN
  suffices hmain : ∀ x : F, IsIntegral B x → x ∈ M by
    have heq : Subalgebra.toSubmodule (integralClosure B F) = Submodule.span B (T : Set F) :=
      le_antisymm (fun x hx => hMN (hmain x hx))
        (Submodule.span_le.mpr fun t ht => hDint t (hTD t ht))
    exact (Module.Finite.iff_fg (N := Subalgebra.toSubmodule (integralClosure B F))).mpr
      (by rw [heq]; exact ⟨T, rfl⟩)
  intro x hx
  let 𝔞 : Ideal D :=
    { carrier := {d | (d : F) * x ∈ D}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : D) : F) * x ∈ D
        rw [Subalgebra.coe_add, add_mul]
        exact D.add_mem ha hb
      zero_mem' := by
        change ((0 : D) : F) * x ∈ D
        rw [Subalgebra.coe_zero, zero_mul]
        exact D.zero_mem
      smul_mem' := fun c a ha => by
        change ((c * a : D) : F) * x ∈ D
        rw [Subalgebra.coe_mul, mul_assoc]
        exact D.mul_mem c.2 ha }
  let ι : D →+* M := (D.val : D →+* F).codRestrict M fun d => Algebra.subset_adjoin d.2
  by_cases hJ : Ideal.map ι 𝔞 = ⊤
  · have key : ∀ j ∈ Ideal.map ι 𝔞, (j : F) * x ∈ M := by
      intro j hj
      have hj' : j ∈ Ideal.span (ι '' (𝔞 : Set D)) := hj
      refine Submodule.span_induction (p := fun (j : M) _ => (j : F) * x ∈ M) ?_ ?_ ?_ ?_ hj'
      · rintro _ ⟨a, ha, rfl⟩
        exact Algebra.subset_adjoin ha
      · rw [Subalgebra.coe_zero, zero_mul]
        exact M.zero_mem
      · intro a b _ _ ha hb
        rw [Subalgebra.coe_add, add_mul]
        exact M.add_mem ha hb
      · intro c a _ ha
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
        exact M.mul_mem c.2 ha
    have h1 := key 1 (hJ ▸ Submodule.mem_top)
    rwa [Subalgebra.coe_one, one_mul] at h1
  · exfalso
    obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJ
    have h𝔞n : 𝔞 ≤ n.comap ι := Ideal.map_le_iff_le_comap.mp hJn
    obtain ⟨a, s, hs, hxa⟩ := IsFractionRing.div_surjective (A := D) x
    have hs0 : (s : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hs𝔞 : s ∈ 𝔞 := by
      change (s : F) * x ∈ D
      rw [← hxa]
      change (s : F) * ((a : F) / (s : F)) ∈ D
      rw [mul_div_cancel₀ _ hs0]
      exact a.2
    have hne : n.comap ι ≠ ⊥ := fun hbot => by
      have h0 : s ∈ (⊥ : Ideal D) := hbot ▸ h𝔞n hs𝔞
      exact nonZeroDivisors.ne_zero hs ((Ideal.mem_bot).mp h0)
    have := hn.isPrime
    let V : IsDedekindDomain.HeightOneSpectrum D := ⟨n.comap ι, Ideal.comap_isPrime ι n, hne⟩
    have hM : ∀ m : M, V.valuation F (m : F) ≤ 1 := by
      intro m
      by_contra hcon
      rw [not_le] at hcon
      have hm0 : (m : F) ≠ 0 := by
        rintro h0
        rw [h0, map_zero] at hcon
        exact not_lt_zero hcon
      have hinv : V.valuation F (m : F)⁻¹ < 1 := by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hcon
      obtain ⟨n₀, d, hnd⟩ := V.exists_primeCompl_mul_eq_of_integer _ hinv.le
      have hn₀ : n₀ ∈ V.asIdeal := (V.valuation_lt_one_iff_mem (K := F) n₀).mp (by
        change V.valuation F (algebraMap D F n₀) < 1
        rw [← hnd, map_mul, V.valuation_eq_one_iff_notMem.mpr d.2, mul_one]
        exact hinv)
      have hd : ι d = ι n₀ * m := by
        apply Subtype.ext
        change ((d : D) : F) = (n₀ : F) * (m : F)
        have h2 : (m : F)⁻¹ * ((d : D) : F) = (n₀ : F) := hnd
        rw [← h2, mul_comm, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
      exact d.2 (show (d : D) ∈ n.comap ι from by
        rw [Ideal.mem_comap, hd]
        exact n.mul_mem_right _ hn₀)
    have hxv : V.valuation F x ≤ 1 :=
      Surf.valuation_le_one_of_isIntegral _ (fun b => hM (algebraMap B M b)) hx
    obtain ⟨n₁, d, hnd⟩ := V.exists_primeCompl_mul_eq_of_integer x hxv
    exact d.2 (h𝔞n (show (d : D) ∈ 𝔞 from by
      change ((d : D) : F) * x ∈ D
      rw [mul_comm, show x * ((d : D) : F) = (n₁ : F) from hnd]
      exact n₁.2))
theorem Specialization.finite_integralClosure (R₁ K₁ : Type*) [CommRing R₁] [IsDedekindDomain R₁]
    [Field K₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁] [Algebra R₁ F] [Algebra K₁ F]
    [IsScalarTower R₁ K₁ F] [FiniteDimensional K₁ F] [Algebra.IsSeparable K₁ F]
    (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
    (h : ∀ r : R₁, algebraMap R₁ F r ∈ S.image hO) :
    Module.Finite (S.image hO) (integralClosure (S.image hO) F) :=
  finite_integralClosure_of_dedekind R₁ K₁ F fun r => ⟨⟨_, h r⟩, rfl⟩
variable {E : Type*} [Field E] [Algebra E F]
theorem Specialization.exists_leastOrder (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (I : Ideal O) (μ : RCN026.Place_p19 E F)
    (hμ : μ ∈ S.placesOn E hO) (hI : ∃ x ∈ I, S.val (algebraMap O L x) = 1) :
    ∃ x ∈ I, S.val (algebraMap O L x) = 1 ∧
      μ.val (S.resOn hO x) = exp (-(S.leastOrder hO I μ.val : ℤ)) := by
  obtain ⟨x, hxI, hx1⟩ := hI
  have hres0 : S.resOn hO x ≠ 0 := fun h0 =>
    absurd ((S.resOn_eq_zero_iff hO x).mp h0) (by rw [hx1]; exact lt_irrefl _)
  exact Nat.sInf_mem (s := {k : ℕ | ∃ x ∈ I, S.val (algebraMap O L x) = 1 ∧
    μ.val (S.resOn hO x) = exp (-(k : ℤ))}) ⟨_, x, hxI, hx1,
      PlaceSurf.eq_exp_neg_toNat ((Valuation.ne_zero_iff _).mpr hres0) (hμ _ ⟨x, rfl⟩)⟩
theorem Specialization.leastOrder_levelIdeal [IsDomain O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [IsFractionRing O L] [Algebra E L] (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (f : L) (c : E) (g : O)
    (hg : algebraMap O L g = f - algebraMap E L c) (hgS : S.val (algebraMap O L g) = 1)
    (μ : RCN026.Place_p19 E F) (hμ : μ ∈ S.placesOn E hO) (n : ℕ) :
    (S.leastOrder hO (levelIdeal L f c n) μ.val : ℤ) = n * RCN026.order_p19 E F μ (S.resOn hO g) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hgS
    exact zero_ne_one hgS
  have hres0 : S.resOn hO g ≠ 0 := fun h0 =>
    absurd ((S.resOn_eq_zero_iff hO g).mp h0) (by rw [hgS]; exact lt_irrefl _)
  have hkval := PlaceSurf.eq_exp_neg_toNat ((Valuation.ne_zero_iff μ.val).mpr hres0) (hμ _ ⟨g, rfl⟩)
  generalize (-(μ.val (S.resOn hO g)).log).toNat = k at hkval
  have hord : RCN026.order_p19 E F μ (S.resOn hO g) = k := by
    rw [RCN026.order_p19, hkval, log_exp, neg_neg]
  have hpow : μ.val (S.resOn hO (g ^ n)) = exp (-((n * k : ℕ) : ℤ)) := by
    rw [map_pow, map_pow, hkval, ← exp_nsmul]
    congr 1
    push_cast
    simp
  rw [levelIdeal_eq_span L f c g hg hg0 n, hord]
  have hmem : n * k ∈ {j : ℕ | ∃ x ∈ Ideal.span {g ^ n}, S.val (algebraMap O L x) = 1 ∧
      μ.val (S.resOn hO x) = exp (-(j : ℤ))} :=
    ⟨g ^ n, Ideal.mem_span_singleton_self _, by rw [map_pow, map_pow, hgS, one_pow], hpow⟩
  have hge : n * k ≤ S.leastOrder hO (Ideal.span {g ^ n}) μ.val := by
    refine le_csInf ⟨_, hmem⟩ ?_
    rintro j ⟨x, hx, -, hxj⟩
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have h1 : exp (-(j : ℤ)) ≤ exp (-((n * k : ℕ) : ℤ)) := by
      rw [← hxj, map_mul, map_mul, hpow]
      exact mul_le_of_le_one_right' (hμ _ ⟨y, rfl⟩)
    rw [exp_le_exp] at h1
    exact_mod_cast neg_le_neg_iff.mp h1
  exact_mod_cast le_antisymm (Nat.sInf_le hmem) hge
end Specialization
namespace PlaceSurf
section Composite
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
def comp (S : Specialization L F) (μ : Valuation F ℤᵐ⁰) : ValuationSubring L where
  toSubring := (μ.valuationSubring.toSubring.comap S.res).map S.val.valuationSubring.subtype
  mem_or_inv_mem' x := by
    have key : ∀ (y : L) (z : F), S.Restricts y z → μ z ≤ 1 → y ∈
        ((μ.valuationSubring.toSubring.comap S.res).map S.val.valuationSubring.subtype).carrier := by
      rintro y z ⟨h, rfl⟩ hμ
      exact ⟨⟨y, h⟩, hμ, rfl⟩
    have hlt : ∀ y : L, S.val y < 1 → S.Restricts y 0 := fun y hy =>
      ⟨(S.val.mem_valuationSubring_iff y).mpr hy.le, (S.res_eq_zero_iff _).mpr hy⟩
    rcases lt_trichotomy (S.val x) 1 with h | h | h
    · exact Or.inl (key x 0 (hlt x h) (by rw [map_zero]; exact zero_le_one))
    · have hx : S.Restricts x (S.res ⟨x, (S.val.mem_valuationSubring_iff x).mpr h.le⟩) := ⟨_, rfl⟩
      rcases le_total (μ (S.res ⟨x, (S.val.mem_valuationSubring_iff x).mpr h.le⟩)) 1 with h2 | h2
      · exact Or.inl (key x _ hx h2)
      · exact Or.inr (key x⁻¹ _ (hx.inv (hx.ne_zero h))
          (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h2))
    · exact Or.inr (key x⁻¹ 0 (hlt x⁻¹ (by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h))
        (by rw [map_zero]; exact zero_le_one))
theorem mem_comp {S : Specialization L F} {μ : Valuation F ℤᵐ⁰} {x : L} :
    x ∈ comp S μ ↔ ∃ z, S.Restricts x z ∧ μ z ≤ 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨S.res y, ⟨y.2, rfl⟩, hy⟩
  · rintro ⟨z, ⟨h, rfl⟩, hμ⟩
    exact ⟨⟨x, h⟩, hμ, rfl⟩
theorem algebraMap_mem_comp (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
    (μ : Valuation F ℤᵐ⁰) (a : O) : algebraMap O L a ∈ comp S μ ↔ μ (S.resOn hO a) ≤ 1 := by
  refine mem_comp.trans ⟨fun ⟨z, hz, hμ⟩ => ?_, fun h => ⟨_, S.restricts_resOn hO a, h⟩⟩
  rwa [(S.restricts_resOn hO a).unique hz]
variable [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O L]
  [IsLocalRing O]
theorem val_resOn_lt_one (hO' : PrimeChain O) (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) {μ : Valuation F ℤᵐ⁰}
    (hμs : Function.Surjective μ) (hμ : ∀ b ∈ S.image hO, μ b ≤ 1) {a : O} (ha : ¬IsUnit a) :
    μ (S.resOn hO a) < 1 := by
  by_cases hmax : (centre L S.val hO).IsMaximal
  · have h1 : a ∈ centre L S.val hO :=
      IsLocalRing.eq_maximalIdeal hmax ▸ (IsLocalRing.mem_maximalIdeal a).mpr ha
    rw [(S.resOn_eq_zero_iff hO a).mpr h1, map_zero]
    exact zero_lt_one
  · have hfr := S.image_isFractionRing hO' hO hmax
    have hdim := S.image_dimensionLEOne hO' hO
    have hloc := S.image_isLocalRing hO
    have hμB : ∀ b : S.image hO, μ (algebraMap (S.image hO) F b) ≤ 1 := fun b => hμ b b.2
    have hmaxB : (centre F μ hμB).IsMaximal :=
      (Surf.centre_isPrime F μ hμB).isMaximal (Surf.centre_ne_bot F μ hμs hμB)
    let f : O →+* S.image hO := (S.resOn hO).rangeRestrict
    have hhom := IsLocalHom.of_surjective f (S.resOn hO).rangeRestrict_surjective
    have h2 : f a ∈ centre F μ hμB := by
      rw [IsLocalRing.eq_maximalIdeal hmaxB, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => ha (isUnit_of_map_unit f a hu)
    exact h2
theorem inv_mem_of_mem_comp (hO' : PrimeChain O) (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) {μ : Valuation F ℤᵐ⁰}
    (hμs : Function.Surjective μ) (hμ : ∀ b ∈ S.image hO, μ b ≤ 1) (a : O)
    (h : (algebraMap O L a)⁻¹ ∈ comp S μ) : ∃ b : O, algebraMap O L b = (algebraMap O L a)⁻¹ := by
  by_cases ha0 : a = 0
  · exact ⟨0, by rw [ha0, map_zero, inv_zero]⟩
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    exact ⟨((u⁻¹ : Oˣ) : O), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · exfalso
    have h1 := val_resOn_lt_one hO' S hO hμs hμ hu
    obtain ⟨z, hz, hμz⟩ := mem_comp.mp h
    have h2 := ((S.restricts_resOn hO a).mul hz).unique
      (show S.Restricts (algebraMap O L a * (algebraMap O L a)⁻¹) 1 by
        rw [mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr ha0)]
        exact Specialization.Restricts.one)
    have h3 : μ (S.resOn hO a) * μ z = 1 := by rw [← map_mul, h2, map_one]
    exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hμz) h1))
end Composite
section Separating
open IntermediateField IntermediateField.algebraAdjoinAdjoin
variable {E F : Type*} [Field E] [Field F] [Algebra E F]
theorem finite_integralClosure_of_separating {B : Type*} [CommRing B] [Algebra B F] {t : F}
    [FiniteDimensional E⟮t⟯ F] [Algebra.IsSeparable E⟮t⟯ F]
    (hE : ∀ a : E, ∃ b : B, algebraMap B F b = algebraMap E F a)
    (ht : ∃ b : B, algebraMap B F b = t) : Module.Finite B (integralClosure B F) := by
  have hsurj : Function.Surjective ((Polynomial.aeval t : Polynomial E →ₐ[E] F).codRestrict
      (Algebra.adjoin E {t}) fun _ => Polynomial.aeval_mem_adjoin_singleton E t) := by
    rintro ⟨x, hx⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, rfl⟩
  have : IsPrincipalIdealRing (Algebra.adjoin E {t}) := IsPrincipalIdealRing.of_surjective _ hsurj
  refine finite_integralClosure_of_dedekind (Algebra.adjoin E {t}) E⟮t⟯ F fun r => ?_
  refine Algebra.adjoin_induction (p := fun x _ => ∃ b : B, algebraMap B F b = x) ?_ hE ?_ ?_ r.2
  · rintro x rfl
    exact ht
  · rintro x y _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', map_add _ _ _⟩
  · rintro x y _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b * b', map_mul _ _ _⟩
end Separating
section CurvePoint
open IntermediateField
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
  {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem bp_finite_separable (sep : RCN341.SeparableLiteralCoordinate C) :
    FiniteDimensional E⟮coordinate E C sep.index⟯ (RCN002.CoordinateField E C) ∧
      Algebra.IsSeparable E⟮coordinate E C sep.index⟯ (RCN002.CoordinateField E C) := by
  let _ : Algebra (RatFunc E) (RCN002.CoordinateField E C) := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  have h1 : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  have h2 : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  refine finite_separable_of_range_le (K := RatFunc E) E⟮coordinate E C sep.index⟯ fun r => ?_
  change RCN005.rationalBaseEmbedding E C sep.index sep.transcendental r ∈ _
  induction r using RatFunc.induction_on with
  | f p q hq =>
    rw [map_div₀, RCN005.rationalBaseEmbedding_polynomial, RCN005.rationalBaseEmbedding_polynomial]
    exact div_mem (algebra_adjoin_le_adjoin E _ (Polynomial.aeval_mem_adjoin_singleton E _))
      (algebra_adjoin_le_adjoin E _ (Polynomial.aeval_mem_adjoin_singleton E _))
theorem chart_mem_ring (q : SurfacePoint G) (i : Fin 3) :
    lmono (coordinate E G) (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i) ∈ q.ring :=
  q.chartOf_spec.1 (Surf.chart_le_normalChart (Algebra.subset_adjoin ⟨i, rfl⟩))
theorem resOn_algebraMap (h : IsCurveOnSurface G C S) (q : SurfacePoint G) (hq : q.On S) (a : E) :
    S.resOn hq (algebraMap E q.ring a) = algebraMap E (RCN002.CoordinateField E C) a :=
  (S.restricts_resOn hq (algebraMap E q.ring a)).unique (h.restricts_algebraMap a)
end CurvePoint
section Overlap
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] {F : Type*} [Field F]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem ring_le_of_place (hc : ∀ j, coordinate E G j ≠ 0) (S : Specialization (RCN002.CoordinateField E G) F)
    (q q' : SurfacePoint G) (hq : q.On S) (hq' : q'.On S) (μ : Valuation F ℤᵐ⁰)
    (hμs : Function.Surjective μ) (h : ∀ b ∈ S.image hq, μ b ≤ 1)
    (h' : ∀ b ∈ S.image hq', μ b ≤ 1) : q'.ring ≤ q.ring := by
  have hloc := q.isLocalRing
  have hU : ∀ a ∈ (q.ring : Set (RCN002.CoordinateField E G)), a⁻¹ ∈ (comp S μ : Set (RCN002.CoordinateField E G)) →
      a⁻¹ ∈ (q.ring : Set (RCN002.CoordinateField E G)) := by
    intro a ha ha'
    obtain ⟨b, hb⟩ := inv_mem_of_mem_comp q.primeChain S hq hμs h ⟨a, ha⟩ ha'
    exact hb ▸ b.2
  have hW : ∀ x (hx : x ∈ q'.ring), x ∈ comp S μ := fun x hx =>
    (algebraMap_mem_comp S hq' μ ⟨x, hx⟩).mpr (h' _ ⟨⟨x, hx⟩, rfl⟩)
  have hA : surfaceChartRing G q'.chartOf.1 q'.chartOf.2.1 q'.chartOf.2.2 ≤ q.ring :=
    Algebra.adjoin_le (by
      rintro _ ⟨i, rfl⟩
      exact chart_overlap (O := (q.ring : Set (RCN002.CoordinateField E G))) (W := (comp S μ : Set (RCN002.CoordinateField E G)))
        (coordinate E G) hc (one_mem _) (fun a ha b hb => mul_mem ha hb) hU _ _ _ _ _ _
        (chart_mem_ring q) (fun i => hW _ (chart_mem_ring q' i)) i)
  have hN : normalChart G q'.chartOf.1 q'.chartOf.2.1 q'.chartOf.2.2 ≤ q.ring := by
    rintro x ⟨f, hf, hfx⟩
    have hint : IsIntegral q.ring x :=
      ⟨f.map (Subalgebra.inclusion hA).toRingHom, hf.map _, by rw [Polynomial.eval₂_map]; exact hfx⟩
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact y.2
  intro x hx
  obtain ⟨s, hs, hs0, hsinv, hxs⟩ := q'.chartOf_spec.2 x hx
  have hsq : s⁻¹ ∈ q.ring := hU s (hN hs) (hW _ hsinv)
  rw [show x = x * s * s⁻¹ by rw [mul_assoc, mul_inv_cancel₀ hs0, mul_one]]
  exact mul_mem (hN hxs) hsq
end Overlap
end PlaceSurf
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
variable {F : Type*} [Field F] [Algebra E F]
theorem SurfacePoint.eq_of_place (hc : ∀ j, coordinate E G j ≠ 0) (S : Specialization (RCN002.CoordinateField E G) F)
    (q q' : SurfacePoint G) (hq : q.On S) (hq' : q'.On S) (μ : RCN026.Place_p19 E F)
    (h : μ ∈ S.placesOn E hq) (h' : μ ∈ S.placesOn E hq') : q = q' :=
  SurfacePoint.ext_ring (le_antisymm
    (PlaceSurf.ring_le_of_place hc S q' q hq' hq μ.val μ.2.1 h' h)
    (PlaceSurf.ring_le_of_place hc S q q' hq hq' μ.val μ.2.1 h h'))
end Surface
section Curve
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem IsCurveOnSurface.exists_point {N p : ℕ} [CharP E p] [IsAlgClosed E]
    (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)} (h : IsCurveOnSurface G C S)
    (hc : ∀ j, coordinate E G j ≠ 0) (htr : ∃ j, Transcendental E (coordinate E C j))
    (μ : RCN026.Place_p19 E (RCN002.CoordinateField E C)) :
    ∃ (q : SurfacePoint G) (hq : q.On S), μ ∈ S.placesOn E hq := by
  obtain ⟨sR, sY, sZ, hW⟩ := PlaceSurf.chart_cover_of_dichotomy
    (W := (PlaceSurf.comp S μ.val : Set (RCN002.CoordinateField E G))) (coordinate E G) hc
    fun t _ => (PlaceSurf.comp S μ.val).mem_or_inv_mem t
  have hfr := normalChart_isFractionRing (hN sR sY sZ)
  have hic := normalChart_isIntegrallyClosed (hN sR sY sZ)
  have hnoe := normalChart_isNoetherianRing (hN sR sY sZ) hp
  have hft := normalChart_finiteType (hN sR sY sZ) hp
  have hA : ∀ a ∈ surfaceChartRing G sR sY sZ, a ∈ PlaceSurf.comp S μ.val := by
    intro a ha
    rw [surfaceChartRing] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hW i
    | algebraMap r =>
      refine PlaceSurf.mem_comp.mpr ⟨_, h.restricts_algebraMap r, ?_⟩
      by_cases hr : r = 0
      · rw [hr, map_zero, map_zero]
        exact zero_le_one
      · exact (PlaceSurf.valuation_eq_one_of_isAlgClosed μ.val hr).le
    | add x y _ _ ihx ihy => exact add_mem ihx ihy
    | mul x y _ _ ihx ihy => exact mul_mem ihx ihy
  have hNW : ∀ a ∈ normalChart G sR sY sZ, a ∈ PlaceSurf.comp S μ.val := by
    rintro a ⟨f, hf, hfa⟩
    have hint : IsIntegral (PlaceSurf.comp S μ.val) a :=
      ⟨f.map ((algebraMap (surfaceChartRing G sR sY sZ) (RCN002.CoordinateField E G)).codRestrict
        (PlaceSurf.comp S μ.val) fun x => hA x x.2), hf.map _,
        by rw [Polynomial.eval₂_map]; exact hfa⟩
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact y.2
  have hN' : ∀ a : normalChart G sR sY sZ,
      S.val (algebraMap (normalChart G sR sY sZ) (RCN002.CoordinateField E G) a) ≤ 1 := fun a => by
    obtain ⟨z, hz, -⟩ := PlaceSurf.mem_comp.mp (hNW a a.2)
    exact hz.val_le_one
  have hμN : ∀ a : normalChart G sR sY sZ, μ.val (S.resOn hN' a) ≤ 1 := fun a =>
    (PlaceSurf.algebraMap_mem_comp S hN' μ.val a).mp (hNW a a.2)
  have hnm : ¬(centre (RCN002.CoordinateField E G) S.val hN').IsMaximal := by
    obtain ⟨j, hj⟩ := htr
    obtain ⟨i, hi⟩ := (LevelSurf.chart_resTrans (E := E) (coordinate E G) hc
      (fun j => (h.restricts_coordinate j).val_le_one) sR sY sZ fun i =>
        hN' ⟨_, Surf.chart_le_normalChart (Algebra.subset_adjoin ⟨i, rfl⟩)⟩).mp
      ⟨j, LevelSurf.resTrans_coordinate h hj⟩
    exact Surf.not_isMaximal_centre S.val hN'
      ⟨_, Surf.chart_le_normalChart (Algebra.subset_adjoin ⟨i, rfl⟩)⟩ hi.1 hi.2
  have hfrB := S.image_isFractionRing (normalChart_primeChain (hN sR sY sZ)) hN' hnm
  have hμB : ∀ b : S.image hN', μ.val (algebraMap (S.image hN') (RCN002.CoordinateField E C) b) ≤ 1 := by
    rintro ⟨_, a, rfl⟩
    exact hμN a
  have hcp := Surf.centre_isPrime (RCN002.CoordinateField E C) μ.val hμB
  let m : Ideal (normalChart G sR sY sZ) :=
    (centre (RCN002.CoordinateField E C) μ.val hμB).comap (S.resOn hN').rangeRestrict
  have hmem : ∀ a, a ∈ m ↔ μ.val (S.resOn hN' a) < 1 := fun a => Iff.rfl
  have hlt : centre (RCN002.CoordinateField E G) S.val hN' < m := by
    refine lt_of_le_of_ne (fun a ha => (hmem a).mpr ?_) fun heq => ?_
    · rw [(S.resOn_eq_zero_iff hN' a).mpr ha, map_zero]
      exact zero_lt_one
    · obtain ⟨⟨_, a, rfl⟩, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (Surf.centre_ne_bot (RCN002.CoordinateField E C) μ.val μ.2.1 hμB)
      have ham : a ∈ centre (RCN002.CoordinateField E G) S.val hN' := heq ▸ (hmem a).mpr hb
      exact hb0 (Subtype.ext ((S.resOn_eq_zero_iff hN' a).mpr ham))
  have hmmax : m.IsMaximal := normalChart_primeChain (hN sR sY sZ) _ m
    (Surf.centre_isPrime (RCN002.CoordinateField E G) S.val hN') (Ideal.comap_isPrime _ _)
    (Surf.centre_ne_bot (RCN002.CoordinateField E G) S.val S.surjective hN') hlt
  obtain ⟨pt, hpt⟩ := exists_surfacePoint (hN sR sY sZ) hp m
  have hptW : ∀ x ∈ pt.ring, x ∈ PlaceSurf.comp S μ.val := by
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := (hpt x).mp hx
    have hs1 : μ.val (S.resOn hN' s) = 1 := le_antisymm (hμN s) (not_lt.mp fun hlt => hs hlt)
    have hs0 : S.resOn hN' s ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hs1
      exact zero_ne_one hs1
    have hsL : (s : RCN002.CoordinateField E G) ≠ 0 := fun h0 => by
      have h1 := (S.restricts_resOn hN' s).val_eq_one hs0
      rw [show algebraMap (normalChart G sR sY sZ) (RCN002.CoordinateField E G) s = 0 from h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (s : RCN002.CoordinateField E G)⁻¹ ∈ PlaceSurf.comp S μ.val :=
      PlaceSurf.mem_comp.mpr ⟨_, (S.restricts_resOn hN' s).inv hs0, by rw [map_inv₀, hs1, inv_one]⟩
    rw [show x = (a : RCN002.CoordinateField E G) * (s : RCN002.CoordinateField E G)⁻¹ by rw [← hxs, mul_assoc, mul_inv_cancel₀ hsL, mul_one]]
    exact mul_mem (hNW a a.2) hinv
  have hq : pt.On S := fun a => by
    obtain ⟨z, hz, -⟩ := PlaceSurf.mem_comp.mp (hptW a a.2)
    exact hz.val_le_one
  refine ⟨pt, hq, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (PlaceSurf.algebraMap_mem_comp S hq μ.val a).mp (hptW a a.2)
theorem IsCurveOnSurface.exists_primeDivisor {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (hc : ∀ j, coordinate E G j ≠ 0)
    (htr : ∃ j, Transcendental E (coordinate E C j)) (q : SurfacePoint G) (hq : q.On S) :
    ∃ P : PrimeDivisor q.ring, (∀ x : q.ring, x ∈ P.ideal ↔ S.val (x : RCN002.CoordinateField E G) < 1) ∧
      P.valuation (RCN002.CoordinateField E G) = S.val := by
  obtain ⟨P, hP, hPv⟩ := exists_primeDivisor_of_centre (RCN002.CoordinateField E G) q.primeChain S.val S.surjective hq
    (h.not_isMaximal_centre hc htr q hq)
  exact ⟨P, fun x => by rw [hP]; exact Iff.rfl, hPv⟩
theorem IsCurveOnSurface.finite_integralClosure [IsAlgClosed E]
    {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)} (h : IsCurveOnSurface G C S)
    (hc : ∀ j, coordinate E G j ≠ 0) (q : SurfacePoint G) (hq : q.On S) (sep : RCN341.SeparableLiteralCoordinate C) :
    Module.Finite (S.image hq) (integralClosure (S.image hq) (RCN002.CoordinateField E C)) := by
  have hmax := h.not_isMaximal_centre hc ⟨sep.index, sep.transcendental⟩ q hq
  have hfr : IsFractionRing (S.image hq) (RCN002.CoordinateField E C) := S.image_isFractionRing q.primeChain hq hmax
  obtain ⟨hfin, hsepb⟩ := PlaceSurf.bp_finite_separable sep
  obtain ⟨b, s, -, hbs⟩ :=
    IsFractionRing.div_surjective (A := S.image hq) (coordinate E C sep.index)
  obtain ⟨t, ht, hfin', hsep'⟩ := PlaceSurf.exists_separating_of_div sep.transcendental hbs.symm
  refine PlaceSurf.finite_integralClosure_of_separating (t := t)
    (fun a => ⟨⟨_, algebraMap E q.ring a, rfl⟩, PlaceSurf.resOn_algebraMap h q hq a⟩) ?_
  rcases ht with rfl | rfl
  · exact ⟨b, rfl⟩
  · exact ⟨s, rfl⟩
theorem IsCurveOnSurface.val_coordinate_eq_one {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (hc : ∀ j, coordinate E G j ≠ 0) {sR sY sZ : Bool}
    (hu : ∀ i, S.val (lmono (coordinate E G) (chartExp sR sY sZ i)) ≤ 1) {i j : Fin 3}
    (hneg : chartExp sR sY sZ i j < 0) : S.val (coordinate E G j) = 1 :=
  PlaceSurf.val_eq_one_of_chartExp_neg S.val _ hc (fun j => (h.restricts_coordinate j).val_le_one)
    hu hneg
theorem IsCurveOnSurface.val_chart_le_one {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
    (h : IsCurveOnSurface G C S) (hc : ∀ j, coordinate E G j ≠ 0) (q : SurfacePoint G)
    (hq : q.On S) (μ : RCN026.Place_p19 E (RCN002.CoordinateField E C)) (hμ : μ ∈ S.placesOn E hq) (i : Fin 3) :
    μ.val (lmono (coordinate E C) (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i)) ≤ 1 := by
  have h1 := h.restricts_lmono (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i) fun j hj =>
    (h.restricts_coordinate j).ne_zero
      (h.val_coordinate_eq_one hc (fun i => hq ⟨_, PlaceSurf.chart_mem_ring q i⟩) hj)
  rw [h1.unique (S.restricts_resOn hq ⟨_, PlaceSurf.chart_mem_ring q i⟩)]
  exact hμ _ ⟨_, rfl⟩
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
namespace Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN005 RCN006 RCN072 RCN341
noncomputable section
variable {E : Type} [Field E]
local notation "Poly" => MvPolynomial (Fin 3) E
theorem val_eq_of_localGen {L : Type} [Field L] (g s : Poly) (P : Ideal Poly) (hgen : LocalGen g s P)
    (hsP : s ∈ P) (ev : Poly →+* L) (hg : ev g = 0)
    (hfrac : ∀ y : L, ∃ a b : Poly, ev b ≠ 0 ∧ y * ev b = ev a)
    (v v' : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) (hv' : Function.Surjective v')
    (hle : ∀ A : Poly, v (ev A) ≤ 1) (hP : ∀ A : Poly, v (ev A) < 1 ↔ A ∈ P)
    (hle' : ∀ A : Poly, v' (ev A) ≤ 1) (hP' : ∀ A : Poly, v' (ev A) < 1 ↔ A ∈ P) : v = v' := by
  have hs := val_section_of_localGen g s P hgen hsP ev hg hfrac v hv hle hP
  have hs' := val_section_of_localGen g s P hgen hsP ev hg hfrac v' hv' hle' hP'
  obtain ⟨h, hh, hgen⟩ := hgen
  have hvh : v (ev h) = 1 := le_antisymm (hle h) (not_lt.mp fun hlt => hh ((hP h).mp hlt))
  have hvh' : v' (ev h) = 1 := le_antisymm (hle' h) (not_lt.mp fun hlt => hh ((hP' h).mp hlt))
  have hevh : ev h ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvh
    exact zero_ne_one hvh
  have hout : ∀ A : Poly, A ∉ P → v (ev A) = v' (ev A) := fun A hAP => by
    rw [le_antisymm (hle A) (not_lt.mp fun hlt => hAP ((hP A).mp hlt)),
      le_antisymm (hle' A) (not_lt.mp fun hlt => hAP ((hP' A).mp hlt))]
  have key : ∀ n : ℕ, ∀ A : Poly, ev A ≠ 0 → -(n : ℤ) ≤ (v (ev A)).log → v (ev A) = v' (ev A) := by
    intro n
    induction n with
    | zero =>
      intro A hA hn
      refine hout A fun hAP => ?_
      have h1 : WithZero.exp (v (ev A)).log < WithZero.exp 0 := by
        rw [WithZero.exp_log (v.ne_zero_iff.mpr hA), WithZero.exp_zero]
        exact (hP A).mpr hAP
      have h2 := WithZero.exp_lt_exp.mp h1
      rw [Nat.cast_zero, neg_zero] at hn
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
        have h1 : v (ev β) * v (ev s) = v (ev A) := by
          rw [← map_mul, he, map_mul, hvh, one_mul]
        have h1' : v' (ev β) * v' (ev s) = v' (ev A) := by
          rw [← map_mul, he, map_mul, hvh', one_mul]
        have hl := congrArg WithZero.log h1
        rw [WithZero.log_mul (v.ne_zero_iff.mpr hβ) (by rw [hs]; exact WithZero.exp_ne_zero), hs,
          WithZero.log_exp] at hl
        rw [← h1, ← h1', ih β hβ (by push_cast at hn; omega), hs, hs']
      · exact hout A hAP
  have hall : ∀ A : Poly, v (ev A) = v' (ev A) := fun A => by
    by_cases hA : ev A = 0
    · rw [hA, map_zero, map_zero]
    · exact key (-(v (ev A)).log).toNat A hA (by omega)
  refine Valuation.ext fun y => ?_
  obtain ⟨a, b, hb, hab⟩ := hfrac y
  have h1 : v y * v (ev b) = v' y * v (ev b) := by
    rw [← map_mul, hab, hall a, ← hab, map_mul, hall b]
  exact mul_right_cancel₀ (v.ne_zero_iff.mpr hb) h1
section Surface
variable {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
theorem BR_eq_zero_iff (A : Poly) : RCN002.coordinateEvaluation E G A = 0 ↔ A ∈ G := by
  rw [← RingHom.mem_ker]
  exact (RCN002.coordinateEvaluation_ker E G).symm ▸ Iff.rfl
theorem exists_fraction (y : RCN002.CoordinateField E G) : ∃ a b : Poly, RCN002.coordinateEvaluation E G b ≠ 0 ∧ y * RCN002.coordinateEvaluation E G b = RCN002.coordinateEvaluation E G a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RCN002.CoordinateRing E G) y
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hB0 : algebraMap (RCN002.CoordinateRing E G) (RCN002.CoordinateField E G) (Ideal.Quotient.mk G B) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RCN002.CoordinateRing E G) (RCN002.CoordinateField E G))).mpr (nonZeroDivisors.ne_zero hb)
  exact ⟨A, B, hB0, div_mul_cancel₀ _ hB0⟩
variable {C : Ideal (MvPolynomial (Fin 3) E)} [C.IsPrime] {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem curve_val_le_one (h : IsCurveOnSurface G C S) (A : Poly) : S.val (RCN002.coordinateEvaluation E G A) ≤ 1 := by
  obtain ⟨hA, -⟩ := h A
  exact (Valuation.mem_valuationSubring_iff _ _).mp hA
theorem curve_val_lt_one_iff (h : IsCurveOnSurface G C S) (A : Poly) :
    S.val (RCN002.coordinateEvaluation E G A) < 1 ↔ A ∈ C := by
  obtain ⟨hA, hres⟩ := h A
  exact (S.res_eq_zero_iff ⟨_, hA⟩).symm.trans (by rw [hres]; exact BR_eq_zero_iff A)
theorem curve_val_section (h : IsCurveOnSurface G C S) (g s : Poly) (hgG : g ∈ G)
    (hgen : LocalGen g s C) (hsC : s ∈ C) : S.val (RCN002.coordinateEvaluation E G s) = exp (-1) :=
  val_section_of_localGen g s C hgen hsC (RCN002.coordinateEvaluation E G).toRingHom ((BR_eq_zero_iff g).mpr hgG)
    exists_fraction S.val S.surjective (curve_val_le_one h) (curve_val_lt_one_iff h)
theorem val_eq_curve_val (h : IsCurveOnSurface G C S) (g s : Poly) (hgG : g ∈ G)
    (hgen : LocalGen g s C) (hsC : s ∈ C) (v : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰) (hv : Function.Surjective v)
    (hle : ∀ A : Poly, v (RCN002.coordinateEvaluation E G A) ≤ 1) (hP : ∀ A : Poly, v (RCN002.coordinateEvaluation E G A) < 1 ↔ A ∈ C) : v = S.val :=
  val_eq_of_localGen g s C hgen hsC (RCN002.coordinateEvaluation E G).toRingHom ((BR_eq_zero_iff g).mpr hgG) exists_fraction
    v S.val hv S.surjective hle hP (curve_val_le_one h) (curve_val_lt_one_iff h)
end Surface
theorem height_eq_two_of_mem (g s : Poly) (hg : Irreducible g) (hs : ¬g ∣ s) (C : Ideal Poly)
    (hC : C ∈ RCN072.componentFamily E g s) : C.height = 2 := by
  have hCp : C.IsPrime := RCN072.component_isPrime E g s C hC
  have hgp : (Ideal.span ({g} : Set Poly)).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have h1 : (1 : ℕ∞) ≤ (Ideal.span ({g} : Set Poly)).height := by
    have hbot : (⊥ : Ideal Poly) < Ideal.span {g} :=
      bot_lt_iff_ne_bot.mpr (fun h => hg.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at h
  have hlt : Ideal.span ({g} : Set Poly) < C := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr
      (RCN072.cutIdeal_le_component E g s C hC (Ideal.subset_span (Set.mem_insert g _)))) fun heq => hs ?_
    exact Ideal.mem_span_singleton.mp
      (heq ▸ RCN072.cutIdeal_le_component E g s C hC (Ideal.subset_span (Set.mem_insert_of_mem g rfl)))
  refine le_antisymm (RCN072.component_height_le_two E g s C hC) ?_
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (Ideal.span ({g} : Set Poly)).height + 1 := by gcongr
    _ ≤ C.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
theorem mem_of_height_eq_two (g s : Poly) (hg : Irreducible g) (hs : ¬g ∣ s) (C : Ideal Poly)
    [C.IsPrime] (hgC : g ∈ C) (hsC : s ∈ C) (hC2 : C.height = 2) : C ∈ RCN072.componentFamily E g s := by
  have hgp : (Ideal.span ({g} : Set Poly)).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have h1 : (1 : ℕ∞) ≤ (Ideal.span ({g} : Set Poly)).height := by
    have hbot : (⊥ : Ideal Poly) < Ideal.span {g} :=
      bot_lt_iff_ne_bot.mpr (fun h => hg.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at h
  have hle : Ideal.span ({g, s} : Set Poly) ≤ C := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    exacts [hgC, hsC]
  refine (RCN072.mem_componentFamily E g s C).mpr ⟨⟨inferInstance, hle⟩, fun C' hC' hC'C => ?_⟩
  by_contra hne
  have hC'p : C'.IsPrime := hC'.1
  have hlt : C' < C := lt_of_le_of_ne hC'C fun heq => hne (heq ▸ le_rfl)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hgC' : Ideal.span ({g} : Set Poly) ≤ C' :=
    (Ideal.span_singleton_le_iff_mem _).mpr (hC'.2 (Ideal.subset_span (Set.mem_insert g _)))
  have hlt' : Ideal.span ({g} : Set Poly) < C' := lt_of_le_of_ne hgC' fun heq => hs
    (Ideal.mem_span_singleton.mp (heq ▸ hC'.2 (Ideal.subset_span (Set.mem_insert_of_mem g rfl))))
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
  have h4 : (3 : ℕ∞) ≤ 2 :=
    calc (3 : ℕ∞) = 1 + 1 + 1 := by norm_num
      _ ≤ (Ideal.span ({g} : Set Poly)).height + 1 + 1 := by gcongr
      _ ≤ C'.height + 1 := by gcongr
      _ ≤ C.height := h2
      _ = 2 := hC2
  norm_num at h4
theorem exists_curve {G : Ideal Poly} [G.IsPrime] (g s : Poly) (hg : Irreducible g)
    (hG : G = Ideal.span {g}) (hs : ¬g ∣ s) (C : Ideal Poly) [C.IsPrime] (hC : C ∈ RCN072.componentFamily E g s)
    (hd : pderiv 1 g ∉ C) : ∃ S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C), IsCurveOnSurface G C S := by
  have hgC : g ∈ C := RCN072.cutIdeal_le_component E g s C hC (Ideal.subset_span (Set.mem_insert g _))
  have hGC : G ≤ C := hG ▸ (Ideal.span_singleton_le_iff_mem _).mpr hgC
  have : (C.map (Ideal.Quotient.mk G)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hGC)
  exact exists_isCurveOnSurface hGC
    (isDiscreteValuationRing_of_pderiv_notMem g hg hG hgC (height_eq_two_of_mem g s hg hs C hC) 1 hd)
theorem exists_zeros_bound [IsAlgClosed E] (C : Ideal Poly) [C.IsPrime] (sep : RCN341.SeparableLiteralCoordinate C) (W : RCN095.FlagDegree)
    (x : RCN002.CoordinateField E C) (hx : x ≠ 0)
    (hpole : ∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E C),
      RCN204.flagPole v.val (coordinate E C) W ≤ RCN187.poleOrder v.val x) :
    ∃ Zf : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)), ∀ T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)),
      ∑ v ∈ T, RCN204.flagPole v.val (coordinate E C) W ≤
        ∑ v ∈ Zf, ((RCN026.order_p19 E (RCN002.CoordinateField E C) v x).toNat : ℤ) := by
  let _ := RCN006.polynomialBaseAlgebra E C sep.index
  let _ := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  let _ := RCN006.polynomialBaseScalarTower E C sep.index
  let _ := RCN006.polynomialRationalScalarTower E C sep.index sep.transcendental
  let _ := RCN005.rationalBaseScalarTower E C sep.index sep.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  refine ⟨RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, fun T => ?_⟩
  have hzero : ∀ v : RCN026.Place_p19 E (RCN002.CoordinateField E C), v ∉ RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx →
      RCN187.poleOrder v.val x = 0 := fun v hv => by
    have ho : RCN026.order_p19 E (RCN002.CoordinateField E C) v x = 0 := by
      by_contra hn
      exact hv (RCN026.ALB E (RCN002.CoordinateField E C) x hx v hn)
    rw [RCN026.order_p19, neg_eq_zero] at ho
    rw [RCN187.poleOrder, ho, max_self]
  calc ∑ v ∈ T, RCN204.flagPole v.val (coordinate E C) W ≤ ∑ v ∈ T, RCN187.poleOrder v.val x :=
        Finset.sum_le_sum fun v _ => hpole v
    _ ≤ ∑ v ∈ T ∪ RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, RCN187.poleOrder v.val x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun v _ _ => le_max_left _ _)
    _ = ∑ v ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, RCN187.poleOrder v.val x :=
        (Finset.sum_subset Finset.subset_union_right fun v _ hv => hzero v hv).symm
    _ = ∑ v ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E C) v x :=
        (RCN026.AJO E (RCN002.CoordinateField E C) x hx).symm
    _ = ∑ v ∈ RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, ((RCN026.order_p19 E (RCN002.CoordinateField E C) v x).toNat : ℤ) :=
        Finset.sum_congr rfl fun v _ => by
          rw [RCN026.zeroOrder_p19, Int.toNat_eq_max, max_comm]
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
namespace PlaceSurf
namespace Statement
open WithZero MvPolynomial
open RCN002
section Generic
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
  (E : Type*) [Field E] [Algebra E F] (S : Specialization L F)
  (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
def LengthEqZeros : Prop :=
  ∀ P : Ideal O, (∀ x : O, x ∈ P ↔ S.val (algebraMap O L x) < 1) → ∀ h : O, h ∉ P →
    Module.length O (O ⧸ (P ⊔ Ideal.span {h})) =
      ((∑ᶠ μ ∈ S.placesOn E hO, (RCN026.order_p19 E F μ (S.resOn hO h)).toNat : ℕ) : ℕ∞)
def LeastOrderLE : Prop :=
  ∀ P : Ideal O, (∀ x : O, x ∈ P ↔ S.val (algebraMap O L x) < 1) → ∀ I : Ideal O, ¬I ≤ P →
    ((∑ᶠ μ ∈ S.placesOn E hO, S.leastOrder hO I μ.val : ℕ) : ℕ∞) ≤
      Module.length O (O ⧸ (P ⊔ I)) + closureColength (S.image hO) F
def FinitePlaces : Prop :=
  ∀ P : Ideal O, (∀ x : O, x ∈ P ↔ S.val (algebraMap O L x) < 1) → ¬P.IsMaximal →
    (S.placesOn E hO).Finite
end Generic
section Ring
variable (O : Type*) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  [IsLocalRing O] (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L] (F : Type*) [Field F]
  (E : Type*) [Field E] [IsAlgClosed E] [Algebra E F]
def generic (C : ∀ (S : Specialization L F), (∀ a : O, S.val (algebraMap O L a) ≤ 1) → Prop) : Prop :=
  PrimeChain O → ∀ φ : O →+* E, Function.Surjective φ →
    ∀ (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1),
      Module.Finite (S.image hO) (integralClosure (S.image hO) F) → C S hO
def length_eq_zeros : Prop := generic O L F E fun S hO => LengthEqZeros E S hO
def leastOrder_le : Prop := generic O L F E fun S hO => LeastOrderLE E S hO
def finite_places : Prop := generic O L F E fun S hO => FinitePlaces E S hO
end Ring
section Surface
variable (E : Type) [Field E] [IsAlgClosed E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime]
  (F : Type*) [Field F] [Algebra E F]
def surface (C : ∀ (q : SurfacePoint G) (S : Specialization (RCN002.CoordinateField E G) F), q.On S → Prop) : Prop :=
  ∀ (q : SurfacePoint G) (S : Specialization (RCN002.CoordinateField E G) F) (hq : q.On S),
    Module.Finite (S.image hq) (integralClosure (S.image hq) F) → C q S hq
def surfacePoint_length_eq_zeros : Prop := surface E G F fun _ S hq => LengthEqZeros E S hq
def surfacePoint_leastOrder_le : Prop := surface E G F fun _ S hq => LeastOrderLE E S hq
def surfacePoint_finite_places : Prop := surface E G F fun _ S hq => FinitePlaces E S hq
end Surface
end Statement
end PlaceSurf
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
open RCN002 RCN055 RCN095 RCN135 RCN136 RCN187 RCN204 RCN313
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
namespace Curve
theorem pole_sub_log_le {L E : Type*} [Field L] [Field E] [Algebra E L]
    (nu : Valuation L ℤᵐ⁰) (f : L) (c : E) (hc : nu (algebraMap E L c) ≤ 1) :
    poleOrder nu f - (nu (f - algebraMap E L c)).log ≤ max (-(nu (f - algebraMap E L c)).log) 0 := by
  rw [poleOrder]
  by_cases hf : nu f ≤ 1
  · have h0 : (nu f).log ≤ 0 := by
      rcases eq_or_ne (nu f) 0 with h | h
      · rw [h, log_zero]
      · exact (log_le_iff_le_exp h).2 (by rwa [exp_zero])
    rw [max_eq_left h0, zero_sub]
    exact le_max_left _ _
  · have hlt : nu (algebraMap E L c) < nu f := lt_of_le_of_lt hc (not_le.mp hf)
    have h0 : 0 ≤ (nu f).log := by
      by_contra h
      have hne : nu f ≠ 0 := fun h0 => hf (h0 ▸ zero_le)
      have h1 := (log_le_iff_le_exp (a := 0) hne).1 (le_of_lt (not_le.mp h))
      rw [exp_zero] at h1
      exact hf h1
    rw [Valuation.map_sub_eq_of_lt_left nu hlt, max_eq_right h0, sub_self]
    exact le_max_right _ _
theorem quot_le (T v : ℤᵐ⁰) (hv : v ≠ 0) (a b pf : ℤ) (m : ℕ)
    (h1 : T ≤ exp (4 * m * a + b)) (ha : a ≤ pf) (hint : pf - v.log ≤ max (-v.log) 0) :
    T / v ^ (4 * m) / exp b ≤ exp (4 * m * max (-v.log) 0) := by
  obtain ⟨l, rfl⟩ : ∃ l, v = exp l := ⟨v.log, (exp_log hv).symm⟩
  rw [log_exp] at hint ⊢
  rw [← exp_nsmul, div_eq_mul_inv, div_eq_mul_inv, ← exp_neg, ← exp_neg]
  calc T * exp (-((4 * m) • l)) * exp (-b)
      ≤ exp (4 * m * a + b) * exp (-((4 * m) • l)) * exp (-b) :=
        mul_le_mul' (mul_le_mul' h1 le_rfl) le_rfl
    _ = exp (4 * m * (a - l)) := by
        rw [← exp_add, ← exp_add]
        congr 1
        simp only [nsmul_eq_mul]
        push_cast
        ring
    _ ≤ exp (4 * m * max (-l) 0) :=
        exp_le_exp.2 (mul_le_mul_of_nonneg_left (by omega) (by positivity))
variable {K : Type} [Field K]
theorem step_one (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (G : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime]
    (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {F})
    (hH : sliceProj F (polyH K F) ≠ 0) (hcG : ∀ j, coordinate (GenericField K) G j ≠ 0)
    (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : ∀ (sR sY sZ : Bool) (v : Valuation (SliceField F) ℤᵐ⁰), ChartDivisor F sR sY sZ v →
      v (sliceProj F (polyH K F)) ≤ exp (flagPole v (sliceCoord F) Hf))
    (hPL : ∀ sR sY sZ, ChartPlaceLaw F F (dvd_refl F) sR sY sZ)
    {N p : ℕ} [CharP (GenericField K) p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (f : RCN002.CoordinateField (GenericField K) G) (c : GenericField K)
    (hfc : f - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) G) c ≠ 0)
    (hpole : ∀ (sR sY sZ : Bool) (nu : Valuation (RCN002.CoordinateField (GenericField K) G) ℤᵐ⁰),
      SurfaceDivisor G sR sY sZ nu →
        placeTOn nu (coordinate (GenericField K) G)
          (SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyG K F) / SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) G (polyH K F)) ≤ poleOrder nu f) :
    StepOne F G hker Hf f c := by
  intro q B m
  have hd := q.surfaceDivisor hN hp B
  have hb := surface_divisor_restrict_sliceEmbedding G F hker q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2
    (B.valuation (RCN002.CoordinateField (GenericField K) G)) hd.le_one hd.nonconst
  have h1 := tail_cube_bound_surface F F (dvd_refl F) hH Hf h5 _ _ _ (hHf _ _ _) (hPL _ _ _)
    (HFree6812.sliceEmbedding G F hker) (B.valuation (RCN002.CoordinateField (GenericField K) G)) hb m
  rw [show (fun j => HFree6812.sliceEmbedding G F hker (sliceCoord F j)) = coordinate (GenericField K) G from
    funext (sliceEmbedding_coord F G hker), sliceEmbedding_sigma] at h1
  have hvert := vertex_of_centred (B.valuation (RCN002.CoordinateField (GenericField K) G))
    (coordinate (GenericField K) G) q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 (fun _ => hcG 1)
    (fun _ => hcG 0) (fun _ => hcG 2) (fun i => hd.le_one _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    (cutFlag m Hf)
  have hlev : (q.level f c B : ℤ) = max (-(B.valuation (RCN002.CoordinateField (GenericField K) G)
      (f - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) G) c)).log) 0 := by
    rw [SurfacePoint.level, levelDivisor, zeroDivisor_apply _ hfc, Int.toNat_eq_max]
  rw [psiC, map_div₀, map_div₀, hvert, hlev, map_pow]
  simp only [map_mul, map_pow]
  exact quot_le _ _ ((Valuation.ne_zero_iff _).2 hfc) _ _ _ m h1 (hpole _ _ _ _ hd)
    (pole_sub_log_le _ f c (hd.le_one _ (Subalgebra.algebraMap_mem _ c)))
theorem chart_inverted (sR sY sZ : Bool) (l0 l1 l2 : ℤ) (h0 : l0 ≤ 0) (h1 : l1 ≤ 0)
    (h2 : l2 ≤ 0)
    (h : ∀ i, chartExp sR sY sZ i 0 * l0 + chartExp sR sY sZ i 1 * l1 +
      chartExp sR sY sZ i 2 * l2 ≤ 0) :
    (sY = true → l0 = 0) ∧ (sR = true → l1 = 0) ∧ (sZ = true → l2 = 0) := by
  have r0 := h 0
  have r1 := h 1
  have r2 := h 2
  rcases sR with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _ <;>
    simp [chartExp] at r0 r1 r2 ⊢ <;> omega
theorem exists_levelIdeal_val_eq_one {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)}
    [G.IsPrime] [C.IsPrime] {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)} (hS : IsCurveOnSurface G C S)
    (hcG : ∀ j, coordinate E G j ≠ 0) (htr : ∃ j, Transcendental E (coordinate E C j))
    (f : RCN002.CoordinateField E G) (c : E) (hSfc : S.val (f - algebraMap E (RCN002.CoordinateField E G) c) = 1) (q : SurfacePoint G)
    (hq : q.On S) (n : ℕ) :
    ∃ x ∈ levelIdeal (RCN002.CoordinateField E G) f c n, S.val (algebraMap q.ring (RCN002.CoordinateField E G) x) = 1 := by
  have hfc0 : f - algebraMap E (RCN002.CoordinateField E G) c ≠ 0 := fun h => by
    rw [h, map_zero] at hSfc
    exact zero_ne_one hSfc
  obtain ⟨Pa, hPa, hPaval⟩ := hS.exists_primeDivisor hcG htr q hq
  have h0 : (n • levelDivisor (O := q.ring) (RCN002.CoordinateField E G) f c) Pa = 0 := by
    rw [Finsupp.smul_apply, levelDivisor, zeroDivisor_apply _ hfc0, hPaval, hSfc, log_one,
      neg_zero, Int.toNat_zero, smul_zero]
  obtain ⟨x, hx, hxP⟩ := SetLike.not_le_iff_exists.mp (divisorIdeal_not_le (RCN002.CoordinateField E G) h0)
  exact ⟨x, hx, le_antisymm (hq x) (not_lt.mp fun hlt => hxP ((hPa x).mpr hlt))⟩
theorem level_restrict (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (G C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [G.IsPrime] [C.IsPrime]
    (hker : RingHom.ker (sliceMap (K := K) G) = Ideal.span {F})
    (S : Specialization (RCN002.CoordinateField (GenericField K) G) (RCN002.CoordinateField (GenericField K) C))
    (hS : IsCurveOnSurface G C S) (hcG : ∀ j, coordinate (GenericField K) G j ≠ 0)
    (htr : ∃ j, Transcendental (GenericField K) (coordinate (GenericField K) C j))
    (hHC : surfaceMap (RCN135.polynomialEmbedding K) (polyH K F) ∉ C) (Hf : FlagDegree)
    (f : RCN002.CoordinateField (GenericField K) G) (fC : RCN002.CoordinateField (GenericField K) C) (c : GenericField K)
    (hf : S.Restricts f fC)
    (hSfc : S.val (f - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) G) c) = 1)
    (hstep : StepOne F G hker Hf f c) (m : ℕ) : LevelRestrict F G C S Hf f fC c m := by
  intro q hq μ hμ n
  have hfcR := hf.sub (hS.restricts_algebraMap c)
  have hfC0 : fC - algebraMap (GenericField K) (RCN002.CoordinateField (GenericField K) C) c ≠ 0 := hfcR.ne_zero hSfc
  obtain ⟨x, hxI, -, hxμ⟩ := S.exists_leastOrder hq _ μ hμ
    (exists_levelIdeal_val_eq_one hS hcG htr f c hSfc q hq n)
  have hy : ∀ B : PrimeDivisor q.ring, B.valuation (RCN002.CoordinateField (GenericField K) G)
      ((psiC F G hker f c (m + 1) / lmono (coordinate (GenericField K) G)
          (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 (cutFlag (m + 1) Hf))) ^ n *
        algebraMap q.ring (RCN002.CoordinateField (GenericField K) G) x ^ (4 * (m + 1))) ≤ 1 := by
    intro B
    have h1 := hstep q B (m + 1)
    have h2 : B.valuation (RCN002.CoordinateField (GenericField K) G) (algebraMap q.ring (RCN002.CoordinateField (GenericField K) G) x) ≤
        exp (-(((n • q.level f c) B : ℕ) : ℤ)) := (mem_divisorIdeal (RCN002.CoordinateField (GenericField K) G)).mp hxI B
    rw [Finsupp.smul_apply, smul_eq_mul] at h2
    rw [map_mul, map_pow, map_pow]
    calc _ ≤ exp (4 * ((m + 1 : ℕ) : ℤ) * (q.level f c B : ℤ)) ^ n *
          exp (-((n * q.level f c B : ℕ) : ℤ)) ^ (4 * (m + 1)) :=
        mul_le_mul' (pow_le_pow_left' h1 n) (pow_le_pow_left' h2 _)
      _ = 1 := by
        rw [← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_zero]
        congr 1
        simp only [nsmul_eq_mul]
        push_cast
        ring
  obtain ⟨a, ha⟩ := mem_range_of_valuation_le_one (RCN002.CoordinateField (GenericField K) G) _ hy
  have hHC0 : SecondJetComponentRoots.coefficientMap (RCN135.polynomialEmbedding K) C (polyH K F) ≠ 0 := fun h => hHC ((SecondJetComponentRoots.evaluation_zero_iff C _).1 h)
  have hpsi : S.Restricts (psiC F G hker f c (m + 1)) (psiCOn F C fC c m) := by
    rw [psiC, tail_cube_eq F F (dvd_refl F)
      (sliceProj_ne_zero_of_notMem F G hker C hS.ideal_le _ hHC) m, map_div₀,
      sliceEmbedding_sliceProj, sliceEmbedding_sliceProj]
    exact ((hS.restricts_GP (RCN135.polynomialEmbedding K) _).div (hS.restricts_GP (RCN135.polynomialEmbedding K) _)
      (by rw [map_pow]; exact pow_ne_zero _ hHC0)).div (hfcR.pow _) (pow_ne_zero _ hfC0)
  have hlog : ∀ j, (S.val (coordinate (GenericField K) G j)).log ≤ 0 := fun j =>
    (log_le_iff_le_exp ((Valuation.ne_zero_iff _).2 (hcG j))).2 (by
      rw [exp_zero]
      exact (hS.restricts_coordinate j).val_le_one)
  have hinv := chart_inverted q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 _ _ _ (hlog 0) (hlog 1) (hlog 2)
    fun i => (lmono_le_one_iff S.val _ hcG _).1 (hq ⟨_, PlaceSurf.chart_mem_ring q i⟩)
  have hcj : ∀ j : Fin 3, (S.val (coordinate (GenericField K) G j)).log = 0 →
      coordinate (GenericField K) C j ≠ 0 := fun j h0 =>
    (hS.restricts_coordinate j).ne_zero
      (eq_one_of_log_eq_zero ((Valuation.ne_zero_iff _).2 (hcG j)) h0)
  have hbit : ∀ j : Fin 3, (j = 0 ∧ q.chartOf.2.1 = true) ∨ (j = 1 ∧ q.chartOf.1 = true) ∨
      (j = 2 ∧ q.chartOf.2.2 = true) → coordinate (GenericField K) C j ≠ 0 := by
    rintro j (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    exacts [hcj 0 (hinv.1 h), hcj 1 (hinv.2.1 h), hcj 2 (hinv.2.2 h)]
  have hvertμ := vertex_of_centred μ.val (coordinate (GenericField K) C) q.chartOf.1 q.chartOf.2.1
    q.chartOf.2.2 (fun h => hbit 1 (Or.inr (Or.inl ⟨rfl, h⟩))) (fun h => hbit 0 (Or.inl ⟨rfl, h⟩))
    (fun h => hbit 2 (Or.inr (Or.inr ⟨rfl, h⟩))) (hS.val_chart_le_one hcG q hq μ hμ)
    (cutFlag (m + 1) Hf)
  have hmonoR := hS.restricts_lmono
    (vertexExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 (cutFlag (m + 1) Hf))
    fun j hj => absurd hj (not_lt.mpr (vertexExp_nonneg _ _ _ _ j))
  have hres := (S.restricts_resOn hq a).unique (ha ▸ ((hpsi.div hmonoR fun h => by
    rw [h, map_zero] at hvertμ
    exact exp_ne_zero hvertμ.symm).pow n).mul ((S.restricts_resOn hq x).pow _))
  have hle : μ.val (S.resOn hq a) ≤ 1 := hμ _ ⟨a, rfl⟩
  rw [hres, map_mul, map_pow, map_pow, map_div₀, hvertμ, hxμ, div_pow, ← exp_nsmul, ← exp_nsmul,
    div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add] at hle
  have hexp : -(n • flagPole μ.val (coordinate (GenericField K) C) (cutFlag (m + 1) Hf)) +
      (4 * (m + 1)) • -(S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ) =
      -(n * flagPole μ.val (coordinate (GenericField K) C) (cutFlag (m + 1) Hf) +
        4 * (m + 1) * (S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ)) := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hexp] at hle
  calc μ.val (psiCOn F C fC c m) ^ n
      = μ.val (psiCOn F C fC c m) ^ n * exp (-(n * flagPole μ.val (coordinate (GenericField K) C)
          (cutFlag (m + 1) Hf) + 4 * (m + 1) *
            (S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ))) *
          exp (n * flagPole μ.val (coordinate (GenericField K) C) (cutFlag (m + 1) Hf) +
            4 * (m + 1) * (S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ)) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ 1 * exp (n * flagPole μ.val (coordinate (GenericField K) C) (cutFlag (m + 1) Hf) +
          4 * (m + 1) * (S.leastOrder hq (levelIdeal (RCN002.CoordinateField (GenericField K) G) f c n) μ.val : ℤ)) :=
        mul_le_mul' hle le_rfl
    _ = _ := one_mul _
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
namespace Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002
noncomputable section
def placeCentre {O F : Type*} [CommRing O] [Field F] (ρ : O →+* F) (v : Valuation F ℤᵐ⁰)
    (h : ∀ a : O, v (ρ a) ≤ 1) : Ideal O where
  carrier := {a | v (ρ a) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact (v.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (h c)) hx
theorem mem_placeCentre {O F : Type*} [CommRing O] [Field F] (ρ : O →+* F) (v : Valuation F ℤᵐ⁰)
    (h : ∀ a : O, v (ρ a) ≤ 1) (a : O) : a ∈ placeCentre ρ v h ↔ v (ρ a) < 1 :=
  Iff.rfl
theorem placeCentre_isPrime {O F : Type*} [CommRing O] [Field F] (ρ : O →+* F) (v : Valuation F ℤᵐ⁰)
    (h : ∀ a : O, v (ρ a) ≤ 1) : (placeCentre ρ v h).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : O) ∈ placeCentre ρ v h := htop ▸ Submodule.mem_top
    rw [mem_placeCentre, map_one, map_one] at h1
    exact lt_irrefl _ h1
  · rw [mem_placeCentre, map_mul, map_mul] at hxy
    by_contra hne
    rw [not_or, mem_placeCentre, mem_placeCentre, not_lt, not_lt] at hne
    rw [le_antisymm (h x) hne.1, le_antisymm (h y) hne.2, mul_one] at hxy
    exact lt_irrefl _ hxy
theorem resOn_eq_zero_iff {O L F : Type*} [CommRing O] [Field L] [Algebra O L] [Field F]
    (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (a : O) :
    S.resOn hO a = 0 ↔ S.val (algebraMap O L a) < 1 :=
  S.res_eq_zero_iff _
variable {E : Type} [Field E]
local notation "Poly" => MvPolynomial (Fin 3) E
theorem exists_BR_of_mem_chart {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] {a : RCN002.CoordinateField E G}
    (ha : a ∈ surfaceChartRing G false false false) : ∃ A : Poly, a = RCN002.coordinateEvaluation E G A := by
  refine Algebra.adjoin_induction (p := fun a _ => ∃ A : Poly, a = RCN002.coordinateEvaluation E G A) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨MvPolynomial.X 1, by simp [lmono, chartExp]; rfl⟩
    · exact ⟨MvPolynomial.X 0, by simp [lmono, chartExp]; rfl⟩
    · exact ⟨MvPolynomial.X 2, by simp [lmono, chartExp]; rfl⟩
  · exact fun r => ⟨MvPolynomial.C r, (algHom_C _ r).symm⟩
  · rintro _ _ - - ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A + B, (map_add _ A B).symm⟩
  · rintro _ _ - - ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A * B, (map_mul _ A B).symm⟩
theorem BR_mem_chart {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] (A : Poly) :
    RCN002.coordinateEvaluation E G A ∈ surfaceChartRing G false false false := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [algHom_C]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ?_)
    fin_cases i
    · exact ⟨1, by simp [lmono, chartExp]; rfl⟩
    · exact ⟨0, by simp [lmono, chartExp]; rfl⟩
    · exact ⟨2, by simp [lmono, chartExp]; rfl⟩
theorem place_BR_le_one {C : Ideal (MvPolynomial (Fin 3) E)} [C.IsPrime]
    (v : RCN026.Place_p19 E (RCN002.CoordinateField E C)) (hv : ∀ i, v.val (coordinate E C i) ≤ 1) (A : Poly) :
    v.val (RCN002.coordinateEvaluation E C A) ≤ 1 := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [algHom_C]
    exact RCN344.NP E (RCN002.CoordinateField E C) v a
  | add p q hp hq =>
    rw [map_add]
    exact (v.val.map_add _ _).trans (max_le hp hq)
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact mul_le_one' hp (hv i)
section Point
variable {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
  {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem chart_le_normalChart :
    surfaceChartRing G false false false ≤ normalChart G false false false := fun x hx =>
  isIntegral_algebraMap (R := surfaceChartRing G false false false) (x := ⟨x, hx⟩)
theorem BR_mem_normalChart (A : Poly) : RCN002.coordinateEvaluation E G A ∈ normalChart G false false false :=
  chart_le_normalChart (BR_mem_chart A)
theorem curve_val_le_one_normalChart (h : IsCurveOnSurface G C S)
    (a : normalChart G false false false) :
    S.val (algebraMap (normalChart G false false false) (RCN002.CoordinateField E G) a) ≤ 1 := by
  have hint : IsIntegral (surfaceChartRing G false false false) (a : RCN002.CoordinateField E G) := a.2
  refine Surf.valuation_le_one_of_isIntegral S.val (fun r => ?_) hint
  obtain ⟨A, hA⟩ := exists_BR_of_mem_chart r.2
  rw [show algebraMap (surfaceChartRing G false false false) (RCN002.CoordinateField E G) r = (r : RCN002.CoordinateField E G) from rfl, hA]
  exact curve_val_le_one h A
theorem resOn_BR (h : IsCurveOnSurface G C S) (A : Poly) :
    S.resOn (curve_val_le_one_normalChart h) ⟨RCN002.coordinateEvaluation E G A, BR_mem_normalChart A⟩ = RCN002.coordinateEvaluation E C A := by
  obtain ⟨hm, hr⟩ := h A
  exact hr
theorem place_resOn_le_one (h : IsCurveOnSurface G C S) (v : RCN026.Place_p19 E (RCN002.CoordinateField E C))
    (hv : ∀ i, v.val (coordinate E C i) ≤ 1) (a : normalChart G false false false) :
    v.val (S.resOn (curve_val_le_one_normalChart h) a) ≤ 1 := by
  obtain ⟨pp, hmonic, hroot⟩ :
    IsIntegral (surfaceChartRing G false false false) (a : RCN002.CoordinateField E G) := a.2
  let j : surfaceChartRing G false false false →+* normalChart G false false false :=
    (Subalgebra.inclusion chart_le_normalChart).toRingHom
  have h0 : Polynomial.eval₂ j a pp = 0 := by
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ pp j (algebraMap (normalChart G false false false) (RCN002.CoordinateField E G)) a
    exact h1.trans hroot
  have h1 : Polynomial.eval₂ ((S.resOn (curve_val_le_one_normalChart h)).comp j)
      (S.resOn (curve_val_le_one_normalChart h) a) pp = 0 := by
    rw [← Polynomial.hom_eval₂, h0, map_zero]
  let _ : Algebra (surfaceChartRing G false false false) (RCN002.CoordinateField E C) :=
    ((S.resOn (curve_val_le_one_normalChart h)).comp j).toAlgebra
  refine Surf.valuation_le_one_of_isIntegral v.val (fun r => ?_) ⟨pp, hmonic, h1⟩
  obtain ⟨A, hA⟩ := exists_BR_of_mem_chart r.2
  have hj : j r = ⟨RCN002.coordinateEvaluation E G A, BR_mem_normalChart A⟩ := Subtype.ext hA
  have hr : algebraMap (surfaceChartRing G false false false) (RCN002.CoordinateField E C) r = RCN002.coordinateEvaluation E C A := by
    show S.resOn (curve_val_le_one_normalChart h) (j r) = RCN002.coordinateEvaluation E C A
    rw [hj, resOn_BR h A]
  rw [hr]
  exact place_BR_le_one v hv A
theorem exists_finite_point {N p : ℕ} [CharP E p] [IsAlgClosed E] (h : IsCurveOnSurface G C S)
    (hN : SurfaceNoether G false false false N) (hp : 3 * N < p)
    (v : RCN026.Place_p19 E (RCN002.CoordinateField E C)) (hv : ∀ i, v.val (coordinate E C i) ≤ 1)
    (Hp : Poly) (hH : v.val (RCN002.coordinateEvaluation E C Hp) = 1) :
    ∃ (q : SurfacePoint G) (hq : q.On S), v ∈ S.placesOn E hq ∧
      (∀ A : Poly, RCN002.coordinateEvaluation E G A ∈ q.ring) ∧ (RCN002.coordinateEvaluation E G Hp)⁻¹ ∈ q.ring := by
  have hval := curve_val_le_one_normalChart h
  have hρ := place_resOn_le_one h v hv
  have hmprime := placeCentre_isPrime (S.resOn hval) v.val hρ
  have hfrac := normalChart_isFractionRing hN
  have hmax : (placeCentre (S.resOn hval) v.val hρ).IsMaximal := by
    refine normalChart_primeChain hN (centre (RCN002.CoordinateField E G) S.val hval) _
      (Surf.centre_isPrime (RCN002.CoordinateField E G) S.val hval) hmprime
      (Surf.centre_ne_bot (RCN002.CoordinateField E G) S.val S.surjective hval) (lt_of_le_of_ne (fun a ha => ?_) ?_)
    · rw [mem_placeCentre, (resOn_eq_zero_iff S hval a).mpr ha, map_zero]
      exact zero_lt_one
    · intro heq
      obtain ⟨y, hy⟩ := v.2.1 (exp (-1))
      obtain ⟨a, b, hb, hab⟩ := exists_fraction y
      have hy0 : y ≠ 0 := fun h0 => by
        rw [h0, map_zero] at hy
        exact exp_ne_zero hy.symm
      have ha0 : RCN002.coordinateEvaluation E C a ≠ 0 := hab ▸ mul_ne_zero hy0 hb
      have hlt : v.val (RCN002.coordinateEvaluation E C a) < 1 := by
        rw [← hab, map_mul]
        calc v.val y * v.val (RCN002.coordinateEvaluation E C b) ≤ v.val y * 1 :=
              mul_le_mul' le_rfl (place_BR_le_one v hv b)
          _ < 1 := by
              rw [mul_one]
              exact hy ▸ (exp_lt_exp.mpr (by norm_num) |>.trans_eq exp_zero)
      have hmem : (⟨RCN002.coordinateEvaluation E G a, BR_mem_normalChart a⟩ : normalChart G false false false) ∈
          placeCentre (S.resOn hval) v.val hρ := by
        rw [mem_placeCentre, resOn_BR h a]
        exact hlt
      have hcen : (⟨RCN002.coordinateEvaluation E G a, BR_mem_normalChart a⟩ : normalChart G false false false) ∈
          centre (RCN002.CoordinateField E G) S.val hval := heq ▸ hmem
      exact ha0 ((BR_eq_zero_iff (G := C) a).mpr ((curve_val_lt_one_iff h a).mp hcen))
  obtain ⟨pt, hpt⟩ := exists_surfacePoint hN hp (placeCentre (S.resOn hval) v.val hρ)
  have h1m : (1 : normalChart G false false false) ∉ placeCentre (S.resOn hval) v.val hρ :=
    fun h1 => hmprime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hAc : ∀ a : normalChart G false false false, (a : RCN002.CoordinateField E G) ∈ pt.ring := fun a =>
    (hpt _).mpr ⟨a, 1, h1m, by rw [OneMemClass.coe_one, mul_one]⟩
  have hunit : ∀ s : normalChart G false false false,
      s ∉ placeCentre (S.resOn hval) v.val hρ → v.val (S.resOn hval s) = 1 := fun s hs =>
    le_antisymm (hρ s) (not_lt.mp hs)
  have hSunit : ∀ s : normalChart G false false false,
      s ∉ placeCentre (S.resOn hval) v.val hρ → S.val (s : RCN002.CoordinateField E G) = 1 := by
    intro s hs
    refine le_antisymm (hval s) (not_lt.mp fun hlt => ?_)
    have h1 := hunit s hs
    rw [(resOn_eq_zero_iff S hval s).mpr hlt, map_zero] at h1
    exact zero_ne_one h1
  have hq : pt.On S := by
    intro x
    obtain ⟨a, s, hs, hxs⟩ := (hpt _).mp x.2
    have h1 := congrArg S.val hxs
    rw [map_mul, hSunit s hs, mul_one] at h1
    rw [show algebraMap pt.ring (RCN002.CoordinateField E G) x = (x : RCN002.CoordinateField E G) from rfl, h1]
    exact hval a
  refine ⟨pt, hq, ?_, fun A => hAc ⟨RCN002.coordinateEvaluation E G A, BR_mem_normalChart A⟩, ?_⟩
  · rintro b ⟨x, rfl⟩
    obtain ⟨a, s, hs, hxs⟩ := (hpt _).mp x.2
    have hmul : S.resOn hq x * S.resOn hval s = S.resOn hval a := by
      show S.res _ * S.res _ = S.res _
      rw [← map_mul]
      exact congrArg S.res (Subtype.ext hxs)
    have h1 := congrArg v.val hmul
    rw [map_mul, hunit s hs, mul_one] at h1
    rw [h1]
    exact hρ a
  · have hHC : RCN002.coordinateEvaluation E C Hp ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hH
      exact zero_ne_one hH
    have hHG : RCN002.coordinateEvaluation E G Hp ≠ 0 := fun h0 =>
      hHC ((BR_eq_zero_iff (G := C) Hp).mpr (h.le ((BR_eq_zero_iff (G := G) Hp).mp h0)))
    refine (hpt _).mpr ⟨1, ⟨RCN002.coordinateEvaluation E G Hp, BR_mem_normalChart Hp⟩, ?_, ?_⟩
    · rw [mem_placeCentre, resOn_BR h Hp, hH]
      exact lt_irrefl _
    · rw [OneMemClass.coe_one]
      exact inv_mul_cancel₀ hHG
end Point
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
namespace Sec
section Component
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
attribute [local instance] LevelComponent.isPrime
variable {E : Type} [Field E] (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime]
structure ComponentNeeds (H : MvPolynomial (Fin 3) E) (f : RCN002.CoordinateField E G) (c : E) (W : FlagDegree)
    (s : MvPolynomial (Fin 3) E) : Prop where
  ne : ∀ B : LevelComponent G f c, RCN002.coordinateEvaluation E B.prime s ≠ 0
  pole : ∀ (B : LevelComponent G f c) (v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
    RCN204.flagPole v.val (coordinate E B.prime) W ≤ RCN187.poleOrder v.val (RCN002.coordinateEvaluation E B.prime s)
  zero : ∀ (B : LevelComponent G f c) (v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
    v.val (RCN002.coordinateEvaluation E B.prime s) < 1 →
      (∀ i, v.val (coordinate E B.prime i) ≤ 1) ∧ v.val (RCN002.coordinateEvaluation E B.prime H) = 1
end
end Component
section Packet
noncomputable section
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN222
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime
structure Needs (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (W : FlagDegree) (s : MvPolynomial (Fin 3) Ω) : Prop where
  flag : RCN095.PolynomialInFlag W s
  good : ∀ g : RCN222.GeometricFactor K P.F, GoodSection (P.stage g).G s (SZ.leading (RCN135.polynomialEmbedding K))
  component : ∀ g, ComponentNeeds (Exch.component P g) (baseH P.F) (Exch.moving P Q A g) c W s
def FlagBound (P : Packet x t y r) (scale z u v : ℕ) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (W : FlagDegree) : Prop :=
  ∀ (s : ∀ g, Finset (LevelComponent (Exch.component P g) (Exch.moving P Q A g) c))
    (T : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Finset (RCN026.Place_p19 Ω (RCN002.CoordinateField Ω B.prime))),
    (scale : ℤ) * (∑ g, levelFlagSum (s g) (T g) W) ≤
      ((W.zOnly * z + W.yz * u + W.all * v : ℕ) : ℤ)
def FlagBoundStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) : Prop :=
  (∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN (RingHom.id Ω) P.F SZ Q A scale z u v) →
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hcoord : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (_hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (_hA : RCN095.PolynomialInFlag unitYZFlag A) (c : Ω)
    (_hlen : ∀ g (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime],
      PlaceSurf.Statement.surfacePoint_length_eq_zeros Ω (Exch.component P g) (RCN002.CoordinateField Ω C))
    (_hsep : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
    (W : FlagDegree) (s : MvPolynomial (Fin 3) Ω)
    (_hgate : 2 * t * (W.zOnly + W.yz + W.all) < 2130706433)
    (_hneeds : Needs P SZ Q A c W s),
    FlagBound P scale z u v Q A c W
def SectionBoundStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) : Prop :=
  (∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 →
    RCN095.PolynomialInFlag (2 • unitAllFlag) Q → RCN095.PolynomialInFlag unitYZFlag A → AGN (RingHom.id Ω) P.F SZ Q A scale z u v) →
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hcoord : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (_hQ : RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (_hA : RCN095.PolynomialInFlag unitYZFlag A) (c : Ω)
    (_hlen : ∀ g (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime],
      PlaceSurf.Statement.surfacePoint_length_eq_zeros Ω (Exch.component P g) (RCN002.CoordinateField Ω C))
    (_hsep : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
    (s₀ s₁ s₂ : MvPolynomial (Fin 3) Ω)
    (_h₀ : Needs P SZ Q A c unitZFlag s₀) (_h₁ : Needs P SZ Q A c unitYZFlag s₁)
    (_h₂ : Needs P SZ Q A c unitAllFlag s₂),
    SectionBound P scale z u v Q A c
end
end Packet
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
namespace PlaceSurf
open WithZero IsDedekindDomain
open RCN002
open Statement
noncomputable section
section Unit
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
  {E : Type*} [Field E] [Algebra E F] {S : Specialization L F}
  {hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1}
theorem val_resOn_of_isUnit {μ : RCN026.Place_p19 E F} (hμ : μ ∈ S.placesOn E hO) {a : O}
    (ha : IsUnit a) : μ.val (S.resOn hO a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : μ.val (S.resOn hO u) * μ.val (S.resOn hO ((u⁻¹ : Oˣ) : O)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm (hμ _ ⟨(u : O), rfl⟩) ?_
  calc (1 : ℤᵐ⁰) = μ.val (S.resOn hO u) * μ.val (S.resOn hO ((u⁻¹ : Oˣ) : O)) := h1.symm
    _ ≤ μ.val (S.resOn hO u) * 1 := mul_le_mul' le_rfl (hμ _ ⟨((u⁻¹ : Oˣ) : O), rfl⟩)
    _ = μ.val (S.resOn hO u) := mul_one _
end Unit
section Curve
variable {F : Type*} [Field F] (E : Type*) [Field E] [IsAlgClosed E] [Algebra E F] (B : Subring F)
  [IsNoetherianRing B] [Ring.DimensionLEOne B] [IsFractionRing B F]
  [Module.Finite B (integralClosure B F)]
def placeOf (V : HeightOneSpectrum (integralClosure B F)) : RCN026.Place_p19 E F :=
  ⟨V.valuation F, V.valuation_surjective F, ⟨fun _ ha => valuation_eq_one_of_isAlgClosed _ ha⟩⟩
theorem bijOn_placeOf :
    Set.BijOn (placeOf E B) Set.univ {μ : RCN026.Place_p19 E F | ∀ b ∈ B, μ.val b ≤ 1} := by
  refine ⟨fun V _ b hb => valuation_algebraMap_le_one V ⟨b, hb⟩, fun V _ W _ h => ?_,
    fun μ hμ => ?_⟩
  · exact HeightOneSpectrum.valuation_injective F (congrArg Subtype.val h)
  · exact ⟨(placeEquiv B F).symm ⟨μ.val, μ.2.1, fun b => hμ b b.2⟩, Set.mem_univ _,
      Subtype.ext (valuation_placeEquiv_symm _)⟩
theorem finsum_places (f : RCN026.Place_p19 E F → ℕ)
    [Fintype (HeightOneSpectrum (integralClosure B F))] :
    ∑ᶠ μ ∈ {μ : RCN026.Place_p19 E F | ∀ b ∈ B, μ.val b ≤ 1}, f μ = ∑ V, f (placeOf E B V) := by
  rw [← finsum_mem_eq_of_bijOn (placeOf E B) (bijOn_placeOf E B) fun _ _ => rfl, finsum_mem_univ,
    finsum_eq_sum_of_fintype]
variable {B} [IsLocalRing B]
theorem length_quotient_span_eq_finsum (φ : B →+* E) (hφ : Function.Surjective φ) {b : B}
    (hb : b ≠ 0) : Module.length B (B ⧸ Ideal.span {b}) =
      ((∑ᶠ μ ∈ {μ : RCN026.Place_p19 E F | ∀ b ∈ B, μ.val b ≤ 1},
        (RCN026.order_p19 E F μ b).toNat : ℕ) : ℕ∞) := by
  let _ := Fintype.ofFinite (HeightOneSpectrum (integralClosure B F))
  rw [finsum_places E B, length_quotient_span_singleton (K := F) hb]
  refine congrArg Nat.cast (Finset.sum_congr rfl fun V _ => ?_)
  rw [resDeg_eq_one_of_surjective φ hφ V, one_mul]
  rfl
theorem finsum_le_length_quotient (φ : B →+* E) (hφ : Function.Surjective φ) (J : Ideal B)
    (c : RCN026.Place_p19 E F → ℕ)
    (hc : ∀ μ : RCN026.Place_p19 E F, (∀ b ∈ B, μ.val b ≤ 1) → ∀ x ∈ J, x ≠ 0 →
      (c μ : ℤ) ≤ RCN026.order_p19 E F μ x) :
    ((∑ᶠ μ ∈ {μ : RCN026.Place_p19 E F | ∀ b ∈ B, μ.val b ≤ 1}, c μ : ℕ) : ℕ∞) ≤
      Module.length B (B ⧸ J) + closureColength B F := by
  let _ := Fintype.ofFinite (HeightOneSpectrum (integralClosure B F))
  rw [finsum_places E B]
  have h := sum_resDeg_mul_le J (fun V => c (placeOf E B V)) fun V x hx hx0 =>
    hc _ ((bijOn_placeOf E B).mapsTo (Set.mem_univ V)) x hx hx0
  simpa only [resDeg_eq_one_of_surjective φ hφ, one_mul] using h
end Curve
section Ring
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  [IsLocalRing O] {L : Type*} [Field L] [Algebra O L] [IsFractionRing O L] {F : Type*} [Field F]
  {E : Type*} [Field E] [IsAlgClosed E] [Algebra E F]
omit [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [IsFractionRing O L]
  [IsAlgClosed E] [Algebra E F] in
theorem exists_residue_image (S : Specialization L F)
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (φ : O →+* E) (hφ : Function.Surjective φ) :
    ∃ φ' : S.image hO →+* E, Function.Surjective φ' := by
  let f : O →+* S.image hO := (S.resOn hO).rangeRestrict
  have hf : Function.Surjective f := (S.resOn hO).rangeRestrict_surjective
  have hker : RingHom.ker f ≤ RingHom.ker φ := by
    rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  refine ⟨RingHom.liftOfSurjective f hf ⟨φ, hker⟩, Function.Surjective.of_comp (g := f) ?_⟩
  have h := RingHom.liftOfSurjective_comp f hf ⟨φ, hker⟩
  intro e
  obtain ⟨a, rfl⟩ := hφ e
  exact ⟨a, congrFun (congrArg DFunLike.coe h) a⟩
theorem length_eq_zeros : length_eq_zeros O L F E := by
  intro hO' φ hφ S hO hfin P hP h hh
  have hPc : P = centre L S.val hO := Ideal.ext fun x => hP x
  have hres : S.resOn hO h ≠ 0 := fun h0 => hh ((hP h).mpr ((S.resOn_eq_zero_iff hO h).mp h0))
  by_cases hmax : (centre L S.val hO).IsMaximal
  · have hunit : IsUnit h := IsLocalRing.notMem_maximalIdeal.mp fun hm =>
      hh (by rw [hPc, IsLocalRing.eq_maximalIdeal hmax]; exact hm)
    have htop : P ⊔ Ideal.span {h} = ⊤ := Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h)) hunit
    have hsub : Subsingleton (O ⧸ (P ⊔ Ideal.span {h})) := Ideal.Quotient.subsingleton_iff.mpr htop
    rw [Module.length_eq_zero_iff.mpr hsub, finsum_mem_eq_zero_of_forall_eq_zero fun μ hμ => by
      rw [RCN026.order_p19, val_resOn_of_isUnit hμ hunit, log_one, neg_zero, Int.toNat_zero]]
    rfl
  · have := S.image_isNoetherianRing hO
    have := S.image_isLocalRing hO
    have := S.image_dimensionLEOne hO' hO
    have := S.image_isFractionRing hO' hO hmax
    let f : O →+* S.image hO := (S.resOn hO).rangeRestrict
    have hf : Function.Surjective f := (S.resOn hO).rangeRestrict_surjective
    have hker : RingHom.ker f = P := by
      ext a
      rw [RingHom.mem_ker, ← Subtype.coe_inj, hP]
      exact S.resOn_eq_zero_iff hO a
    obtain ⟨φ', hφ'⟩ := exists_residue_image S hO φ hφ
    rw [← hker, length_quotient_ker_sup f hf, Ideal.map_span, Set.image_singleton]
    exact length_quotient_span_eq_finsum E φ' hφ' (b := f h) fun h0 => hres (congrArg Subtype.val h0)
theorem leastOrder_le : leastOrder_le O L F E := by
  intro hO' φ hφ S hO hfin P hP I hI
  have hPc : P = centre L S.val hO := Ideal.ext fun x => hP x
  by_cases hmax : (centre L S.val hO).IsMaximal
  · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hI
    have hunit : IsUnit y := IsLocalRing.notMem_maximalIdeal.mp fun hm =>
      hyP (by rw [hPc, IsLocalRing.eq_maximalIdeal hmax]; exact hm)
    have hy1 : S.val (algebraMap O L y) = 1 :=
      le_antisymm (hO y) (not_lt.mp fun hlt => hyP ((hP y).mpr hlt))
    have hzero : ∀ μ ∈ S.placesOn E hO, S.leastOrder hO I μ.val = 0 := fun μ hμ => by
      have hmem : (0 : ℕ) ∈ {k : ℕ | ∃ x ∈ I, S.val (algebraMap O L x) = 1 ∧
          μ.val (S.resOn hO x) = exp (-(k : ℤ))} :=
        ⟨y, hyI, hy1, by rw [val_resOn_of_isUnit hμ hunit, Nat.cast_zero, neg_zero, exp_zero]⟩
      exact Nat.le_zero.mp (Nat.sInf_le hmem)
    rw [finsum_mem_eq_zero_of_forall_eq_zero hzero]
    exact zero_le
  · have := S.image_isNoetherianRing hO
    have := S.image_isLocalRing hO
    have := S.image_dimensionLEOne hO' hO
    have := S.image_isFractionRing hO' hO hmax
    let f : O →+* S.image hO := (S.resOn hO).rangeRestrict
    have hf : Function.Surjective f := (S.resOn hO).rangeRestrict_surjective
    have hker : RingHom.ker f = P := by
      ext a
      rw [RingHom.mem_ker, ← Subtype.coe_inj, hP]
      exact S.resOn_eq_zero_iff hO a
    obtain ⟨φ', hφ'⟩ := exists_residue_image S hO φ hφ
    rw [← hker, length_quotient_ker_sup f hf]
    refine finsum_le_length_quotient E φ' hφ' (I.map f) (fun μ => S.leastOrder hO I μ.val) ?_
    intro μ hμ x hx hx0
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    have hy0 : S.resOn hO y ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    have hy1 : S.val (algebraMap O L y) = 1 := le_antisymm (hO y)
      (not_lt.mp fun hlt => hy0 ((S.resOn_eq_zero_iff hO y).mpr hlt))
    have hk := eq_exp_neg_toNat ((Valuation.ne_zero_iff μ.val).mpr hy0) (hμ _ ⟨y, rfl⟩)
    have hle : S.leastOrder hO I μ.val ≤ (-(μ.val (S.resOn hO y)).log).toNat :=
      Nat.sInf_le ⟨y, hy, hy1, hk⟩
    generalize (-(μ.val (S.resOn hO y)).log).toNat = k at hk hle
    change ((S.leastOrder hO I μ.val : ℕ) : ℤ) ≤ -(μ.val (S.resOn hO y)).log
    rw [hk, log_exp, neg_neg]
    exact_mod_cast hle
theorem finite_places : finite_places O L F E := by
  intro hO' _ _ S hO hfin P hP hPmax
  have hmax : ¬(centre L S.val hO).IsMaximal := by
    rwa [← show P = centre L S.val hO from Ideal.ext fun x => hP x]
  have := S.image_isNoetherianRing hO
  have := S.image_isLocalRing hO
  have := S.image_dimensionLEOne hO' hO
  have := S.image_isFractionRing hO' hO hmax
  have himage := (bijOn_placeOf E (S.image hO)).image_eq
  rw [show S.placesOn E hO = _ from himage.symm]
  exact Set.finite_univ.image _
end Ring
section Surface
variable {E : Type} [Field E] [IsAlgClosed E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
  {F : Type*} [Field F] [Algebra E F]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem surfacePoint_length_eq_zeros : surfacePoint_length_eq_zeros E G F := by
  intro q S hq hfin
  obtain ⟨φ, hφ⟩ := q.residue
  have := q.isLocalRing
  exact length_eq_zeros q.primeChain φ.toRingHom (fun e => ⟨algebraMap E q.ring e, φ.commutes e⟩)
    S hq hfin
theorem surfacePoint_leastOrder_le : surfacePoint_leastOrder_le E G F := by
  intro q S hq hfin
  obtain ⟨φ, hφ⟩ := q.residue
  have := q.isLocalRing
  exact leastOrder_le q.primeChain φ.toRingHom (fun e => ⟨algebraMap E q.ring e, φ.commutes e⟩)
    S hq hfin
theorem surfacePoint_finite_places : surfacePoint_finite_places E G F := by
  intro q S hq hfin
  obtain ⟨φ, hφ⟩ := q.residue
  have := q.isLocalRing
  exact finite_places q.primeChain φ.toRingHom (fun e => ⟨algebraMap E q.ring e, φ.commutes e⟩)
    S hq hfin
end Surface
end
end PlaceSurf
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
section Surface
noncomputable section
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
def LevelDisjoint (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) (W : FlagDegree) : Prop :=
  ∀ q : SurfacePoint G, f ∉ q.ring → ∀ P : PrimeDivisor q.ring, q.level f c P ≠ 0 →
    P.valuation (RCN002.CoordinateField E G) (q.localFunction A₁ W) = 1
open Classical in
def pointLoss (q : SurfacePoint G) (g : RCN002.CoordinateField E G) : ℕ :=
  if h : g ∈ q.ring then loss (RCN002.CoordinateField E G) (⟨g, h⟩ : q.ring) else 0
open Classical in
def componentLoss (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) (W : FlagDegree) {ι : Type*} (s : Finset ι)
    {F : ι → Type*} [∀ a, Field (F a)] (S : ∀ a, Specialization (RCN002.CoordinateField E G) (F a)) (m : ι → ℕ) : ℕ :=
  ∑ᶠ q : SurfacePoint G, if f ∉ q.ring ∧ q.level f c ≠ 0 then
    pointLoss q (q.localFunction A₁ W) +
      ∑ a ∈ s, if hq : q.On (S a) then m a * closureColength ((S a).image hq) (F a) else 0
  else 0
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
attribute [local instance] component_isPrime SurfacePoint.isNoetherianRing
  SurfacePoint.isIntegrallyClosed SurfacePoint.isFractionRing
structure ExchangeNeeds (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1)) (W : FlagDegree) :
    Prop where
  disjoint : ∀ a ∈ active P SZ, LevelDisjoint (moving P Q A a.1) c (function P SZ a.1) W
  closure : ∀ a ∈ active P SZ, ∀ (q : SurfacePoint (component P a.1)) (hq : q.On (S a)),
    moving P Q A a.1 ∉ q.ring → q.level (moving P Q A a.1) c ≠ 0 →
      Module.Finite ((S a).image hq) (integralClosure ((S a).image hq) (RCN002.CoordinateField Ω a.2.1))
def constant (P : Packet x t y r) (hp : ¬P.F ∣ numerator K P.F (w + 1)) (SZ : MovingFiberThreeSources6811.Source P.F)
    (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (component P a.1)) (RCN002.CoordinateField Ω a.2.1)) (W : FlagDegree) : ℕ :=
  ∑ g : RCN222.GeometricFactor K P.F, componentLoss (moving P Q A g) c (function P SZ g) W
    (Finset.univ.filter fun C : CM (P.stage g) => (⟨g, C⟩ : Curve P) ∈ active P SZ)
    (fun C : CM (P.stage g) => S ⟨g, C⟩) (fun C => 3 * SZ.d * multiplicity P hp ⟨g, C⟩)
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
open WithZero MvPolynomial
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
namespace Curve
open scoped Classical
theorem sum_le_finsum_mem {α : Type*} (g : α → ℕ) (s : Set α)
    (hfin : (s ∩ Function.support g).Finite) (T : Finset α) (hT : ∀ i ∈ T, i ∈ s) :
    ∑ i ∈ T, g i ≤ ∑ᶠ i ∈ s, g i := by
  rw [finsum_mem_eq_sum_of_inter_support_eq g (t := hfin.toFinset) (by
    rw [Set.Finite.coe_toFinset, Set.inter_assoc, Set.inter_self])]
  exact Finset.sum_le_sum_of_ne_zero fun i hi hne => hfin.mem_toFinset.mpr ⟨hT i hi, hne⟩
theorem sum_le_finsum {α : Type*} (g : α → ℕ) (hfin : (Function.support g).Finite)
    (T : Finset α) : ∑ i ∈ T, g i ≤ ∑ᶠ i, g i := by
  rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  exact Finset.sum_le_sum_of_ne_zero fun i _ hne => hfin.mem_toFinset.mpr hne
variable {E : Type} [Field E] [IsAlgClosed E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
  [C.IsPrime] {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
def placeOrder (q : SurfacePoint G) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)) (f : RCN002.CoordinateField E G) (c : E)
    (n : ℕ) (μ : RCN026.Place_p19 E (RCN002.CoordinateField E C)) : ℕ :=
  if h : q.On S then S.leastOrder h (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val else 0
omit [IsAlgClosed E] in
theorem placeOrder_of_on {q : SurfacePoint G} (hq : q.On S) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ)
    (μ : RCN026.Place_p19 E (RCN002.CoordinateField E C)) :
    placeOrder q S f c n μ = S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val :=
  dite_eq_left_of_eq_true (eq_true hq)
omit [IsAlgClosed E] in
theorem order_of_on {q : SurfacePoint G} (hq : q.On S) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) :
    q.order S f c n = ∑ᶠ μ ∈ S.placesOn E hq, S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val :=
  dite_eq_left_of_eq_true (eq_true hq)
omit [IsAlgClosed E] in
theorem order_of_not_on {q : SurfacePoint G} (hq : ¬q.On S) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) :
    q.order S f c n = 0 :=
  dite_eq_right_of_eq_false (eq_false hq)
theorem finite_support_leastOrder (base : RCN341.SeparableLiteralCoordinate C) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C))
    (q : SurfacePoint G) (hq : q.On S) (I : Ideal q.ring)
    (hI : ∃ x ∈ I, S.val (algebraMap q.ring (RCN002.CoordinateField E G) x) = 1) :
    (S.placesOn E hq ∩
      Function.support fun μ : RCN026.Place_p19 E (RCN002.CoordinateField E C) => S.leastOrder hq I μ.val).Finite := by
  obtain ⟨x, hxI, hxS⟩ := hI
  have hz : S.resOn hq x ≠ 0 := (S.restricts_resOn hq x).ne_zero hxS
  refine (finite_order_ne_zero C base _ hz).subset fun μ hμ h0 => hμ.2 ?_
  have h1 : μ.val (S.resOn hq x) = 1 :=
    eq_one_of_log_eq_zero ((Valuation.ne_zero_iff _).2 hz) (neg_eq_zero.mp h0)
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨x, hxI, hxS, by rw [h1, Nat.cast_zero, neg_zero, exp_zero]⟩)
omit [IsAlgClosed E] in
theorem order_eq_zero_of_level (q : SurfacePoint G) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C))
    (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) (h : q.level f c = 0) : q.order S f c n = 0 := by
  by_cases hq : q.On S
  · have hI : levelIdeal (RCN002.CoordinateField E G) f c n = (⊤ : Ideal q.ring) := by
      rw [levelIdeal, show levelDivisor (O := q.ring) (RCN002.CoordinateField E G) f c = 0 from h, smul_zero,
        divisorIdeal_zero]
    have h0 : ∀ μ : RCN026.Place_p19 E (RCN002.CoordinateField E C),
        S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val = 0 := fun μ => by
      rw [hI]
      exact Nat.sInf_eq_zero.mpr (Or.inl ⟨1, Submodule.mem_top, by rw [map_one, map_one],
        by rw [map_one, map_one, Nat.cast_zero, neg_zero, exp_zero]⟩)
    rw [order_of_on hq]
    simp only [h0, finsum_zero]
  · exact order_of_not_on hq f c n
section Count
variable (base : RCN341.SeparableLiteralCoordinate C) (hS : IsCurveOnSurface G C S) (hcG : ∀ j, coordinate E G j ≠ 0)
  (htr : ∃ j, Transcendental E (coordinate E C j)) (f : RCN002.CoordinateField E G) (c : E)
  (hSfc : S.val (f - algebraMap E (RCN002.CoordinateField E G) c) = 1)
omit [IsAlgClosed E] in
include hSfc in
theorem order_moving (q : SurfacePoint G) (hf : f ∈ q.ring) (n : ℕ) :
    q.order S f c n = n * q.order S f c 1 := by
  by_cases hq : q.On S
  · have hgS : S.val (algebraMap q.ring (RCN002.CoordinateField E G) (⟨f, hf⟩ - algebraMap E q.ring c)) = 1 := hSfc
    have key : ∀ μ ∈ S.placesOn E hq, S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val =
        n * S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c 1) μ.val := by
      intro μ hμ
      have h1 := S.leastOrder_levelIdeal hq f c (⟨f, hf⟩ - algebraMap E q.ring c) rfl hgS μ hμ n
      have h2 := S.leastOrder_levelIdeal hq f c (⟨f, hf⟩ - algebraMap E q.ring c) rfl hgS μ hμ 1
      have h3 : (S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c n) μ.val : ℤ) =
          n * (S.leastOrder hq (levelIdeal (RCN002.CoordinateField E G) f c 1) μ.val : ℤ) := by
        rw [h1, h2]
        push_cast
        ring
      exact_mod_cast h3
    rw [order_of_on hq, order_of_on hq, finsum_mem_congr rfl key, mul_finsum_mem]
  · rw [order_of_not_on hq, order_of_not_on hq, mul_zero]
variable {N p : ℕ} [CharP E p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
omit [IsAlgClosed E] in
include hSfc hN hp in
theorem sum_order_le (n : ℕ) (Qs : Finset (SurfacePoint G)) :
    ∑ q ∈ Qs, q.order S f c n ≤ n * curveMoving S f c + curveBase S f c n := by
  have hfin := finite_levelPoints hN hp S f c hSfc
  have hsupp : ∀ k : ℕ, ∀ q : SurfacePoint G, q.order S f c k ≠ 0 →
      q ∈ {q : SurfacePoint G | q.On S ∧ q.level f c ≠ 0} := fun k q hq =>
    ⟨by_contra fun h => hq (order_of_not_on h f c k),
      fun h => hq (order_eq_zero_of_level q S f c k h)⟩
  have h1 : ∑ q ∈ Qs, (if f ∈ q.ring then q.order S f c 1 else 0) ≤ curveMoving S f c :=
    sum_le_finsum _ (hfin.subset fun q hq => hsupp 1 q fun h0 => hq (by
      simp only [h0, ite_self])) Qs
  have h2 : ∑ q ∈ Qs, (if f ∈ q.ring then 0 else q.order S f c n) ≤ curveBase S f c n :=
    sum_le_finsum _ (hfin.subset fun q hq => hsupp n q fun h0 => hq (by
      simp only [h0, ite_self])) Qs
  calc ∑ q ∈ Qs, q.order S f c n
      = ∑ q ∈ Qs, (n * (if f ∈ q.ring then q.order S f c 1 else 0) +
          (if f ∈ q.ring then 0 else q.order S f c n)) := Finset.sum_congr rfl fun q _ => by
        by_cases hf : f ∈ q.ring
        · simp only [hf, ↓reduceIte, add_zero]
          exact order_moving f c hSfc q hf n
        · simp only [hf, ↓reduceIte, mul_zero, zero_add]
    _ = n * ∑ q ∈ Qs, (if f ∈ q.ring then q.order S f c 1 else 0) +
          ∑ q ∈ Qs, (if f ∈ q.ring then 0 else q.order S f c n) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left n h1) h2
include base hS hcG htr hSfc
theorem sum_placeOrder_le_order (q : SurfacePoint G) (n : ℕ)
    (T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C))) (hT : ∀ μ ∈ T, ∃ hq : q.On S, μ ∈ S.placesOn E hq) :
    ∑ μ ∈ T, placeOrder q S f c n μ ≤ q.order S f c n := by
  by_cases hq : q.On S
  · rw [Finset.sum_congr rfl fun μ _ => placeOrder_of_on hq f c n μ, order_of_on hq]
    exact sum_le_finsum_mem _ _ (finite_support_leastOrder base S q hq _
      (exists_levelIdeal_val_eq_one hS hcG htr f c hSfc q hq n)) T fun μ hμ => (hT μ hμ).2
  · rw [Finset.sum_eq_zero fun μ _ => by simp only [placeOrder, hq, ↓reduceDIte]]
    exact Nat.zero_le _
include hN hp
theorem sum_placeOrder_le (n : ℕ) (pt : RCN026.Place_p19 E (RCN002.CoordinateField E C) → SurfacePoint G)
    (hpt : ∀ μ, ∃ hq : (pt μ).On S, μ ∈ S.placesOn E hq) (T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C))) :
    ∑ μ ∈ T, placeOrder (pt μ) S f c n μ ≤ n * curveMoving S f c + curveBase S f c n := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := pt) (t := T.image pt) fun μ hμ =>
    Finset.mem_image_of_mem pt hμ]
  refine (Finset.sum_le_sum fun q _ => ?_).trans
    (sum_order_le f c hSfc hN hp n (T.image pt))
  have hcongr : ∑ μ ∈ T with pt μ = q, placeOrder (pt μ) S f c n μ =
      ∑ μ ∈ T with pt μ = q, placeOrder q S f c n μ :=
    Finset.sum_congr rfl fun μ hμ => by rw [(Finset.mem_filter.mp hμ).2]
  rw [hcongr]
  exact sum_placeOrder_le_order base hS hcG htr f c hSfc q n _ fun μ hμ =>
    (Finset.mem_filter.mp hμ).2 ▸ hpt μ
end Count
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
namespace Sec
open scoped Classical
open WithZero MvPolynomial
open RCN002 RCN072 RCN095 RCN264
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Places
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
  {F : Type*} [Field F] [Algebra E F]
def placesAt (S : Specialization (RCN002.CoordinateField E G) F) (q : SurfacePoint G) : Set (RCN026.Place_p19 E F) :=
  {μ | ∃ hq : q.On S, μ ∈ S.placesOn E hq}
theorem placesAt_of_on (S : Specialization (RCN002.CoordinateField E G) F) (q : SurfacePoint G) (hq : q.On S) :
    placesAt S q = S.placesOn E hq :=
  Set.ext fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hq, h⟩⟩
def zerosAt (S : Specialization (RCN002.CoordinateField E G) F) (q : SurfacePoint G) (y : F) : ℕ :=
  ∑ᶠ μ ∈ placesAt S q, (RCN026.order_p19 E F μ y).toNat
theorem zerosAt_of_not_on (S : Specialization (RCN002.CoordinateField E G) F) (q : SurfacePoint G) (hq : ¬q.On S)
    (y : F) : zerosAt S q y = 0 := by
  rw [zerosAt, show placesAt S q = ∅ from Set.eq_empty_of_forall_notMem fun _ ⟨h, _⟩ => hq h,
    finsum_mem_empty]
theorem sum_le_sum_zerosAt (S : Specialization (RCN002.CoordinateField E G) F) (y : F)
    (Zs : Finset (RCN026.Place_p19 E F))
    (hfin : {μ : RCN026.Place_p19 E F | (RCN026.order_p19 E F μ y).toNat ≠ 0}.Finite)
    (pt : RCN026.Place_p19 E F → SurfacePoint G) (Qs : Finset (SurfacePoint G))
    (hpt : ∀ v ∈ Zs, pt v ∈ Qs ∧ v ∈ placesAt S (pt v)) :
    ∑ v ∈ Zs, (RCN026.order_p19 E F v y).toNat ≤ ∑ q ∈ Qs, zerosAt S q y := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := pt) (t := Qs) fun v hv => (hpt v hv).1]
  refine Finset.sum_le_sum fun q _ => sum_le_finsum_mem _ _ _ (fun v hv => ?_)
    (hfin.subset fun μ hμ => hμ.2)
  obtain ⟨hvZ, rfl⟩ := Finset.mem_filter.mp hv
  exact (hpt v hvZ).2
theorem sum_zerosAt_le (hc : ∀ j, coordinate E G j ≠ 0) (S : Specialization (RCN002.CoordinateField E G) F) (y : F)
    (Qs : Finset (SurfacePoint G)) (V : Finset (RCN026.Place_p19 E F))
    (hV : ∀ μ, (RCN026.order_p19 E F μ y).toNat ≠ 0 → μ ∈ V) :
    ∑ q ∈ Qs, zerosAt S q y ≤ ∑ μ ∈ V, (RCN026.order_p19 E F μ y).toNat :=
  sum_finsum_mem_le Qs (placesAt S) _ V hV fun q _ q' _ μ ⟨hq, h⟩ ⟨hq', h'⟩ =>
    SurfacePoint.eq_of_place hc S q q' hq hq' μ h h'
theorem val_lt_one_of_order_toNat_ne_zero (μ : RCN026.Place_p19 E F) (y : F)
    (h : (RCN026.order_p19 E F μ y).toNat ≠ 0) : μ.val y < 1 := by
  have hpos : 0 < RCN026.order_p19 E F μ y := by omega
  rw [RCN026.order_p19, neg_pos] at hpos
  have h0 : μ.val y ≠ 0 := fun h0 => by
    rw [h0, log_zero] at hpos
    exact lt_irrefl _ hpos
  rw [← exp_zero]
  exact (log_lt_iff_lt_exp h0).mp hpos
end Places
section Curve
variable {E : Type} [Field E] [IsAlgClosed E]
theorem exists_zero_places (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (sep : RCN341.SeparableLiteralCoordinate C)
    (x : RCN002.CoordinateField E C) : ∃ V : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)),
      ∀ μ, (RCN026.order_p19 E (RCN002.CoordinateField E C) μ x).toNat ≠ 0 → μ ∈ V := by
  let _ := RCN006.polynomialBaseAlgebra E C sep.index
  let _ := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  let _ := RCN006.polynomialBaseScalarTower E C sep.index
  let _ := RCN006.polynomialRationalScalarTower E C sep.index sep.transcendental
  let _ := RCN005.rationalBaseScalarTower E C sep.index sep.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  by_cases hx : x = 0
  · refine ⟨∅, fun μ hμ => absurd ?_ hμ⟩
    rw [hx, RCN026.order_p19, map_zero, log_zero, neg_zero, Int.toNat_zero]
  · exact ⟨RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, fun μ hμ =>
      RCN026.ALB E (RCN002.CoordinateField E C) x hx μ fun h0 => hμ (by rw [h0, Int.toNat_zero])⟩
end Curve
section Component
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing LevelComponent.isPrime
local notation "Poly" => MvPolynomial (Fin 3) E
structure Setup (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (N p : ℕ)
    (g H Gs Q A : MvPolynomial (Fin 3) E) (c : E) (W : FlagDegree) (s : MvPolynomial (Fin 3) E) :
    Prop where
  algClosed : IsAlgClosed E
  charP : CharP E p
  noether : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N
  char : 3 * N < p
  coord : ∀ j, coordinate E G j ≠ 0
  irreducible : Irreducible g
  span : G = Ideal.span {g}
  unitH : RCN002.coordinateEvaluation E G H ≠ 0
  memH : H ∈ Ideal.span {g, pderiv 1 g}
  not_dvd : ¬g ∣ s
  localGen : ∀ C ∈ RCN072.componentFamily E g s, LocalGen g s C
  needs : ComponentNeeds G H (RCN208.movingValue G H Gs Q A) c W s
  sep : ∀ B : LevelComponent G (RCN208.movingValue G H Gs Q A) c, Nonempty (RCN341.SeparableLiteralCoordinate B.prime)
  sepD : ∀ D : RCN264.RegularComponent E g s H, Nonempty (RCN341.SeparableLiteralCoordinate D.1)
variable {N p : ℕ} {g H Gs Q A : MvPolynomial (Fin 3) E} {c : E} {W : FlagDegree}
  {s : MvPolynomial (Fin 3) E}
theorem Setup.mem (M : Setup G N p g H Gs Q A c W s) : g ∈ G :=
  M.span ▸ Ideal.mem_span_singleton_self g
theorem Setup.exists_sectionCurve (M : Setup G N p g H Gs Q A c W s) (D : RCN264.RegularComponent E g s H) :
    ∃ S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E D.1), IsCurveOnSurface G D.1 S := by
  refine exists_curve g s M.irreducible M.span M.not_dvd D.1 (AAS E g s H D) fun hd => ?_
  refine _Q6 E g s H D ((Ideal.span_le.mpr ?_) M.memH)
  rintro x (hx | hx)
  · rw [hx]
    exact EN E g s H D
  · rw [Set.mem_singleton_iff.mp hx]
    exact hd
def Setup.sectionCurve (M : Setup G N p g H Gs Q A c W s) (D : RCN264.RegularComponent E g s H) :
    Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E D.1) :=
  (M.exists_sectionCurve D).choose
theorem Setup.sectionCurve_spec (M : Setup G N p g H Gs Q A c W s) (D : RCN264.RegularComponent E g s H) :
    IsCurveOnSurface G D.1 (M.sectionCurve D) :=
  (M.exists_sectionCurve D).choose_spec
theorem Setup.exists_curve_of_primeDivisor (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G)
    (hpoly : ∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) (hHq : (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring)
    (Pd : PrimeDivisor q.ring) :
    ∃ (C : Ideal Poly) (_ : C.IsPrime) (S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)),
      IsCurveOnSurface G C S ∧ S.val = Pd.valuation (RCN002.CoordinateField E G) ∧ C.height = 2 ∧ H ∉ C := by
  have := M.charP
  have hsd := q.surfaceDivisor M.noether M.char Pd
  have hle : ∀ B : Poly, Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G B) ≤ 1 := fun B =>
    Pd.valuation_le_one (RCN002.CoordinateField E G) ⟨RCN002.coordinateEvaluation E G B, hpoly B⟩
  have hH1 : Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G H) = 1 := by
    refine le_antisymm (hle H) ?_
    have h2 := Pd.valuation_le_one (RCN002.CoordinateField E G) ⟨(RCN002.coordinateEvaluation E G H)⁻¹, hHq⟩
    rw [show algebraMap q.ring (RCN002.CoordinateField E G) ⟨(RCN002.coordinateEvaluation E G H)⁻¹, hHq⟩ = (RCN002.coordinateEvaluation E G H)⁻¹ from rfl, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr M.unitH))).mp h2
  have hd : Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G (pderiv 1 g)) = 1 := by
    refine le_antisymm (hle _) ?_
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp M.memH
    have hBR : RCN002.coordinateEvaluation E G H = RCN002.coordinateEvaluation E G b * RCN002.coordinateEvaluation E G (pderiv 1 g) := by
      rw [← hab, map_add, map_mul, map_mul, (BR_eq_zero_iff (G := G) g).mpr M.mem, mul_zero,
        zero_add]
    rw [hBR, map_mul] at hH1
    calc (1 : ℤᵐ⁰) = Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G b) * Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G (pderiv 1 g)) :=
          hH1.symm
      _ ≤ 1 * Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G (pderiv 1 g)) := mul_le_mul' (hle b) le_rfl
      _ = _ := one_mul _
  obtain ⟨C, hC, S, hS, hval, hC2, -⟩ :=
    hsd.exists_isCurveOnSurface M.coord (fun j => hle (MvPolynomial.X j)) g M.irreducible M.span 1 hd
  refine ⟨C, hC, S, hS, hval, hC2, fun hHC => ?_⟩
  have hlt := (curve_val_lt_one_iff hS H).mpr hHC
  rw [hval, hH1] at hlt
  exact lt_irrefl _ hlt
theorem Setup.not_mem_of_mem (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G)
    (hpoly : ∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) (hHq : (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring) {φ sb : q.ring}
    (hφ : (φ : RCN002.CoordinateField E G) = RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c)
    (hsb : (sb : RCN002.CoordinateField E G) = RCN002.coordinateEvaluation E G s) (Pd : PrimeDivisor q.ring) (hφP : φ ∈ Pd.ideal) :
    sb ∉ Pd.ideal := by
  intro hsP
  obtain ⟨C, hC, S, hS, hval, hC2, -⟩ := M.exists_curve_of_primeDivisor q hpoly hHq Pd
  have hlt : Pd.valuation (RCN002.CoordinateField E G)
      (RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c) < 1 := by
    rw [← hφ]
    exact (Pd.valuation_lt_one_iff (RCN002.CoordinateField E G) φ).mpr hφP
  let B' : LevelComponent G (RCN208.movingValue G H Gs Q A) c :=
    ⟨Pd.valuation (RCN002.CoordinateField E G), hlt, C, hC, S, hS, hval, hC2⟩
  have hs' : s ∈ B'.prime := (curve_val_lt_one_iff B'.isCurve s).mp (by
    rw [B'.curve_val]
    show Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G s) < 1
    rw [← hsb]
    exact (Pd.valuation_lt_one_iff (RCN002.CoordinateField E G) sb).mpr hsP)
  exact M.needs.ne B' ((BR_eq_zero_iff (G := B'.prime) s).mpr hs')
theorem mult_eq_div {q : SurfacePoint G} {f : RCN002.CoordinateField E G} (B : LevelComponent G f c) {φ : q.ring}
    (hφ0 : φ ≠ 0) (hφ : (φ : RCN002.CoordinateField E G) = f - algebraMap E (RCN002.CoordinateField E G) c) (P : PrimeDivisor q.ring)
    (hP : P.valuation (RCN002.CoordinateField E G) = B.curve.val) : B.mult = div (RCN002.CoordinateField E G) φ P := by
  have h := valuation_eq_exp_neg_div (RCN002.CoordinateField E G) hφ0 P
  rw [hP, B.curve_val] at h
  have h' : B.val (f - algebraMap E (RCN002.CoordinateField E G) c) = exp (-(div (RCN002.CoordinateField E G) φ P : ℤ)) := by
    rw [← hφ]
    exact h
  rw [LevelComponent.mult, h', log_exp, neg_neg, Int.toNat_natCast]
theorem Setup.zerosAt_level_le (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G) {sb : q.ring}
    (hsb : (sb : RCN002.CoordinateField E G) = RCN002.coordinateEvaluation E G s) (B : LevelComponent G (RCN208.movingValue G H Gs Q A) c)
    (hq : q.On B.curve) (P : PrimeDivisor q.ring)
    (hP : ∀ x : q.ring, x ∈ P.ideal ↔ B.curve.val (x : RCN002.CoordinateField E G) < 1) :
    ((zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) : ℕ) : ℕ∞) ≤
      Module.length q.ring (q.ring ⧸ (P.ideal ⊔ Ideal.span {sb})) := by
  have := M.algClosed
  have := M.charP
  obtain ⟨sepB⟩ := M.sep B
  have hsbP : sb ∉ P.ideal := fun hmem => by
    have hlt := (hP sb).mp hmem
    rw [hsb] at hlt
    exact M.needs.ne B ((BR_eq_zero_iff (G := B.prime) s).mpr
      ((curve_val_lt_one_iff B.isCurve s).mp hlt))
  have hlen := PlaceSurf.surfacePoint_length_eq_zeros q B.curve hq
    (B.isCurve.finite_integralClosure M.coord q hq sepB) P.ideal hP sb hsbP
  have hres : B.curve.resOn hq sb = RCN002.coordinateEvaluation E B.prime s := by
    obtain ⟨hm', hr⟩ := B.isCurve s
    rw [← hr]
    show B.curve.res _ = B.curve.res _
    exact congrArg B.curve.res (Subtype.ext hsb)
  rw [hlen, hres, zerosAt, placesAt_of_on _ _ hq]
theorem Setup.exists_section_of_primeDivisor (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G)
    (hpoly : ∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) (hHq : (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring) {sb : q.ring}
    (hsb : (sb : RCN002.CoordinateField E G) = RCN002.coordinateEvaluation E G s) (hsb0 : sb ≠ 0) (Pd : PrimeDivisor q.ring)
    (hsP : sb ∈ Pd.ideal) :
    ∃ D : RCN264.RegularComponent E g s H, Pd.valuation (RCN002.CoordinateField E G) = (M.sectionCurve D).val ∧
      div (RCN002.CoordinateField E G) sb Pd = 1 := by
  obtain ⟨C, hC, S, hS, hval, hC2, hHC⟩ := M.exists_curve_of_primeDivisor q hpoly hHq Pd
  have hsC : s ∈ C := (curve_val_lt_one_iff hS s).mp (by
    rw [hval, ← hsb]
    exact (Pd.valuation_lt_one_iff (RCN002.CoordinateField E G) sb).mpr hsP)
  have hCmem : C ∈ RCN072.componentFamily E g s :=
    mem_of_height_eq_two g s M.irreducible M.not_dvd C (hS.le M.mem) hsC hC2
  have hgen := M.localGen C hCmem
  have hvalP : ∀ B : Poly, Pd.valuation (RCN002.CoordinateField E G) (RCN002.coordinateEvaluation E G B) < 1 ↔ B ∈ C := fun B => by
    rw [← hval]
    exact curve_val_lt_one_iff hS B
  obtain ⟨D, hD⟩ : ∃ D : RCN264.RegularComponent E g s H, D.1 = C := ⟨⟨C, (AJF E).mpr ⟨hCmem, hHC⟩⟩, rfl⟩
  subst hD
  have hRD : Pd.valuation (RCN002.CoordinateField E G) = (M.sectionCurve D).val :=
    val_eq_curve_val (M.sectionCurve_spec D) g s M.mem hgen hsC (Pd.valuation (RCN002.CoordinateField E G))
      (Pd.valuation_surjective (RCN002.CoordinateField E G))
      (fun B => Pd.valuation_le_one (RCN002.CoordinateField E G) ⟨RCN002.coordinateEvaluation E G B, hpoly B⟩) hvalP
  refine ⟨D, hRD, ?_⟩
  have h1 := valuation_eq_exp_neg_div (RCN002.CoordinateField E G) hsb0 Pd
  have h2 := curve_val_section (M.sectionCurve_spec D) g s M.mem hgen hsC
  rw [hRD, show algebraMap q.ring (RCN002.CoordinateField E G) sb = RCN002.coordinateEvaluation E G s from hsb, h2, exp_inj] at h1
  omega
theorem Setup.length_le_zerosAt (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G) {φ : q.ring}
    (hφ : (φ : RCN002.CoordinateField E G) = RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c)
    (Pd : PrimeDivisor q.ring) (hφP : φ ∉ Pd.ideal) (D : RCN264.RegularComponent E g s H)
    (hRD : Pd.valuation (RCN002.CoordinateField E G) = (M.sectionCurve D).val) :
    Module.length q.ring (q.ring ⧸ (Pd.ideal ⊔ Ideal.span {φ})) ≤
      ((zerosAt (M.sectionCurve D) q
        (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) : ℕ) : ℕ∞) := by
  have := M.algClosed
  have := M.charP
  have hHC : H ∉ D.1 := _Q6 E g s H D
  have hqD : q.On (M.sectionCurve D) := fun x => by
    rw [← hRD]
    exact Pd.valuation_le_one (RCN002.CoordinateField E G) x
  have hPD : ∀ x : q.ring, x ∈ Pd.ideal ↔ (M.sectionCurve D).val (x : RCN002.CoordinateField E G) < 1 := fun x => by
    rw [← hRD]
    exact (Pd.valuation_lt_one_iff (RCN002.CoordinateField E G) x).symm
  obtain ⟨sepD⟩ := M.sepD D
  have hlen := PlaceSurf.surfacePoint_length_eq_zeros q (M.sectionCurve D) hqD
    ((M.sectionCurve_spec D).finite_integralClosure M.coord q hqD sepD) Pd.ideal hPD φ hφP
  have hBRc : ∀ (I : Ideal Poly) [I.IsPrime],
      RCN002.coordinateEvaluation E I (MvPolynomial.C c) = algebraMap E (RCN002.CoordinateField E I) c := fun I _ => by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  have hres : (M.sectionCurve D).resOn hqD φ =
      RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c := by
    obtain ⟨hf, hfr⟩ := (M.sectionCurve_spec D).res_movingValue H Gs Q A hHC
    obtain ⟨hcm, hcr⟩ := M.sectionCurve_spec D (MvPolynomial.C c)
    rw [← hfr, ← hBRc D.1, ← hcr, ← map_sub]
    show (M.sectionCurve D).res _ = (M.sectionCurve D).res _
    refine congrArg (M.sectionCurve D).res (Subtype.ext ?_)
    show (φ : RCN002.CoordinateField E G) = RCN208.movingValue G H Gs Q A - RCN002.coordinateEvaluation E G (MvPolynomial.C c)
    rw [hφ, hBRc G]
  rw [hlen, hres, zerosAt, placesAt_of_on _ _ hqD]
theorem Setup.local_le (M : Setup G N p g H Gs Q A c W s) (q : SurfacePoint G)
    (hpoly : ∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) (hHq : (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring)
    (sB : Finset (LevelComponent G (RCN208.movingValue G H Gs Q A) c)) :
    ∑ B ∈ sB, B.mult * zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) ≤
      ∑ D : RCN264.RegularComponent E g s H, zerosAt (M.sectionCurve D) q
        (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) := by
  have := M.algClosed
  have := M.charP
  by_cases hf0 : RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c = 0
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun B _ => ?_)) (Nat.zero_le _)
    have hm : B.mult = 0 := by
      rw [LevelComponent.mult, hf0, map_zero, log_zero, neg_zero, Int.toNat_zero]
    rw [hm, zero_mul]
  have hfq : RCN208.movingValue G H Gs Q A ∈ q.ring := by
    rw [RCN208.movingValue, div_eq_mul_inv]
    exact q.ring.add_mem (hpoly Q) (q.ring.mul_mem (q.ring.mul_mem (hpoly A) (hpoly Gs)) hHq)
  obtain ⟨φ, hφ⟩ : ∃ φ : q.ring,
      (φ : RCN002.CoordinateField E G) = RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c :=
    ⟨⟨_, q.ring.sub_mem hfq (q.ring.algebraMap_mem c)⟩, rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : q.ring, (sb : RCN002.CoordinateField E G) = RCN002.coordinateEvaluation E G s := ⟨⟨_, hpoly s⟩, rfl⟩
  have hφ0 : φ ≠ 0 := fun h0 => hf0 (by rw [← hφ, h0]; rfl)
  have hsb0 : sb ≠ 0 := fun h0 => M.not_dvd (by
    have h1 : RCN002.coordinateEvaluation E G s = 0 := by rw [← hsb, h0]; rfl
    exact Ideal.mem_span_singleton.mp (M.span ▸ (BR_eq_zero_iff (G := G) s).mp h1))
  have hdisj : ∀ Pd : PrimeDivisor q.ring, φ ∈ Pd.ideal → sb ∉ Pd.ideal :=
    M.not_mem_of_mem q hpoly hHq hφ hsb
  have hex : ∀ b : {B : LevelComponent G (RCN208.movingValue G H Gs Q A) c // q.On B.curve},
      ∃ P : PrimeDivisor q.ring, (∀ x : q.ring, x ∈ P.ideal ↔ b.1.curve.val (x : RCN002.CoordinateField E G) < 1) ∧
        P.valuation (RCN002.CoordinateField E G) = b.1.curve.val := fun b =>
    b.1.isCurve.exists_primeDivisor M.coord b.1.exists_transcendental q b.2
  choose Pb hPb1 hPb2 using hex
  have hsum : ∑ B ∈ sB, B.mult * zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) =
      ∑ b ∈ sB.subtype (fun B => q.On B.curve),
        b.1.mult * zerosAt b.1.curve q (RCN002.coordinateEvaluation E b.1.prime s) := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun B : LevelComponent G
      (RCN208.movingValue G H Gs Q A) c => B.mult * zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s))]
    refine (Finset.sum_filter_of_ne fun B _ hB => ?_).symm
    by_contra hq
    exact hB (by rw [zerosAt_of_not_on _ _ hq, mul_zero])
  rw [hsum]
  refine local_sum_le (RCN002.CoordinateField E G) q.divisorChain hsb0 hφ0 hdisj (sB.subtype fun B => q.On B.curve) Pb ?_
    (fun b => b.1.mult) (fun b => zerosAt b.1.curve q (RCN002.coordinateEvaluation E b.1.prime s))
    (fun b _ => le_of_eq (mult_eq_div b.1 hφ0 hφ (Pb b) (hPb2 b)))
    (fun b _ => M.zerosAt_level_le q hsb b.1 b.2 (Pb b) (hPb1 b)) Finset.univ
    (fun D : RCN264.RegularComponent E g s H => zerosAt (M.sectionCurve D) q
      (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c))
    (fun Pd D => Pd.valuation (RCN002.CoordinateField E G) = (M.sectionCurve D).val) ?_ ?_
  · intro b _ b' _ hbb'
    have h := hPb2 b
    rw [hbb', hPb2 b'] at h
    refine Subtype.ext (Subtype.ext ?_)
    show b.1.val = b'.1.val
    rw [← b.1.curve_val, ← b'.1.curve_val]
    exact h.symm
  · intro Pd Pd' D h1 h2
    exact PrimeDivisor.ext_ideal (Ideal.ext fun x => by
      rw [← Pd.valuation_lt_one_iff (RCN002.CoordinateField E G), ← Pd'.valuation_lt_one_iff (RCN002.CoordinateField E G), h1, h2])
  · intro Pd hsP
    obtain ⟨D, hRD, hdiv⟩ := M.exists_section_of_primeDivisor q hpoly hHq hsb hsb0 Pd hsP
    exact ⟨hdiv, D, Finset.mem_univ D, hRD,
      M.length_le_zerosAt q hφ Pd (fun h => hdisj Pd h hsP) D hRD⟩
theorem Setup.component_count (M : Setup G N p g H Gs Q A c W s) :
    ∃ V : ∀ D : RCN264.RegularComponent E g s H, Finset (RCN026.Place_p19 E (RCN002.CoordinateField E D.1)),
      ∀ (sB : Finset (LevelComponent G (RCN208.movingValue G H Gs Q A) c))
        (T : ∀ B : LevelComponent G (RCN208.movingValue G H Gs Q A) c,
          Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))),
        levelFlagSum sB T W ≤ ∑ D : RCN264.RegularComponent E g s H, ∑ ν ∈ V D,
          RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D.1) ν
            (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) := by
  have := M.algClosed
  have := M.charP
  choose V hV using fun D : RCN264.RegularComponent E g s H => exists_zero_places D.1 (M.sepD D).some
    (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c)
  refine ⟨V, fun sB T => ?_⟩
  choose Zf hZf using fun B : LevelComponent G (RCN208.movingValue G H Gs Q A) c =>
    exists_zeros_bound B.prime (M.sep B).some W (RCN002.coordinateEvaluation E B.prime s) (M.needs.ne B) (M.needs.pole B)
  have hfinB : ∀ B : LevelComponent G (RCN208.movingValue G H Gs Q A) c,
      {μ : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime) |
        (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (RCN002.coordinateEvaluation E B.prime s)).toNat ≠ 0}.Finite := fun B => by
    obtain ⟨V', hV'⟩ := exists_zero_places B.prime (M.sep B).some (RCN002.coordinateEvaluation E B.prime s)
    exact V'.finite_toSet.subset fun μ hμ => hV' μ hμ
  have hex : ∀ (B : LevelComponent G (RCN208.movingValue G H Gs Q A) c)
      (v : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
      (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat ≠ 0 →
      ∃ q : SurfacePoint G, ((∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) ∧ (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring) ∧
        v ∈ placesAt B.curve q := by
    intro B v hv
    obtain ⟨h1, h2⟩ := M.needs.zero B v (val_lt_one_of_order_toNat_ne_zero v _ hv)
    obtain ⟨q, hq, hvq, hpoly, hHq⟩ :=
      exists_finite_point B.isCurve (M.noether false false false) M.char v h1 H h2
    exact ⟨q, ⟨hpoly, hHq⟩, hq, hvq⟩
  obtain ⟨Qs, hQs, hQle⟩ : ∃ Qs : Finset (SurfacePoint G),
      (∀ q ∈ Qs, (∀ B : Poly, RCN002.coordinateEvaluation E G B ∈ q.ring) ∧ (RCN002.coordinateEvaluation E G H)⁻¹ ∈ q.ring) ∧
      ∀ B : LevelComponent G (RCN208.movingValue G H Gs Q A) c, B ∈ sB →
        ∑ v ∈ Zf B, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat ≤
          ∑ q ∈ Qs, zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) := by
    by_cases hne : Nonempty (SurfacePoint G)
    · choose! pt hpt1 hpt2 using hex
      refine ⟨sB.biUnion fun B => ((Zf B).filter fun v =>
        (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat ≠ 0).image (pt B),
        fun q hq => ?_, fun B hB => ?_⟩
      · obtain ⟨B, -, hq⟩ := Finset.mem_biUnion.mp hq
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
        exact hpt1 B v (Finset.mem_filter.mp hv).2
      · refine le_of_eq_of_le (Finset.sum_filter_ne_zero (Zf B)).symm ?_
        exact sum_le_sum_zerosAt B.curve _ _ (hfinB B) (pt B) _ fun v hv =>
          ⟨Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_image_of_mem _ hv⟩,
            hpt2 B v (Finset.mem_filter.mp hv).2⟩
    · refine ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q), fun B _ => ?_⟩
      rw [Finset.sum_empty, Nat.le_zero]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_contra hv
      obtain ⟨q, -⟩ := hex B v hv
      exact hne ⟨q⟩
  have hnat : ∑ B ∈ sB, B.mult *
        ∑ v ∈ Zf B, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat ≤
      ∑ D : RCN264.RegularComponent E g s H, ∑ μ ∈ V D, (RCN026.order_p19 E (RCN002.CoordinateField E D.1) μ
        (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c)).toNat := by
    calc ∑ B ∈ sB, B.mult *
          ∑ v ∈ Zf B, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat
        ≤ ∑ B ∈ sB, B.mult * ∑ q ∈ Qs, zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) :=
          Finset.sum_le_sum fun B hB => Nat.mul_le_mul_left _ (hQle B hB)
      _ = ∑ q ∈ Qs, ∑ B ∈ sB, B.mult * zerosAt B.curve q (RCN002.coordinateEvaluation E B.prime s) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ q ∈ Qs, ∑ D : RCN264.RegularComponent E g s H, zerosAt (M.sectionCurve D) q
            (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) :=
          Finset.sum_le_sum fun q hq => M.local_le q (hQs q hq).1 (hQs q hq).2 sB
      _ = ∑ D : RCN264.RegularComponent E g s H, ∑ q ∈ Qs, zerosAt (M.sectionCurve D) q
            (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun D _ =>
          sum_zerosAt_le M.coord (M.sectionCurve D) _ Qs (V D) (hV D)
  calc levelFlagSum sB T W
      = ∑ B ∈ sB, (B.mult : ℤ) *
          ∑ v ∈ T B, RCN204.flagPole v.val (coordinate E B.prime) W := rfl
    _ ≤ ∑ B ∈ sB, (B.mult : ℤ) * ∑ v ∈ Zf B,
          ((RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat : ℤ) :=
        Finset.sum_le_sum fun B _ =>
          mul_le_mul_of_nonneg_left (hZf B (T B)) (Int.natCast_nonneg _)
    _ = ((∑ B ∈ sB, B.mult *
          ∑ v ∈ Zf B, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) v (RCN002.coordinateEvaluation E B.prime s)).toNat : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [Nat.cast_mul, Nat.cast_sum]
    _ ≤ ((∑ D : RCN264.RegularComponent E g s H, ∑ μ ∈ V D, (RCN026.order_p19 E (RCN002.CoordinateField E D.1) μ
          (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c)).toNat : ℕ) : ℤ) :=
        Nat.cast_le.mpr hnat
    _ = ∑ D : RCN264.RegularComponent E g s H, ∑ ν ∈ V D, RCN026.zeroOrder_p19 E (RCN002.CoordinateField E D.1) ν
          (RCN208.movingValue D.1 H Gs Q A - algebraMap E (RCN002.CoordinateField E D.1) c) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [RCN026.zeroOrder_p19, Int.toNat_eq_max, max_comm]
end Component
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
namespace Exch
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
section Generic
variable {O : Type*} [CommRing O] {L : Type*} [Field L] [Algebra O L] {F : Type*} [Field F]
theorem leastOrder_top (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
    (μ : Valuation F ℤᵐ⁰) : S.leastOrder hO ⊤ μ = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inl ⟨1, Submodule.mem_top, ?_, ?_⟩)
  · rw [map_one, map_one]
  · rw [map_one, map_one, Nat.cast_zero, neg_zero, exp_zero]
variable {E : Type*} [Field E] [Algebra E F] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  [IsFractionRing O L] [Algebra E L]
theorem levelOrder_eq_zero (S : Specialization L F) (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1)
    (f : L) (c : E) (n : ℕ) (h : levelDivisor (O := O) L f c = 0) : S.levelOrder hO f c n = 0 := by
  unfold Specialization.levelOrder
  rw [levelIdeal, h, smul_zero, divisorIdeal_zero]
  simp only [leastOrder_top, finsum_zero]
end Generic
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem order_eq_zero {F : Type*} [Field F] [Algebra E F] (q : SurfacePoint G)
    (S : Specialization (RCN002.CoordinateField E G) F) (f : RCN002.CoordinateField E G) (c : E) (n : ℕ) (h : q.level f c = 0) :
    q.order S f c n = 0 := by
  classical
  unfold SurfacePoint.order
  split_ifs with hq
  · exact levelOrder_eq_zero S hq f c n h
  · rfl
theorem levelNumber_eq_zero (q : SurfacePoint G) (f : RCN002.CoordinateField E G) (c : E) (g : RCN002.CoordinateField E G)
    (h : q.level f c = 0) : q.levelNumber f c g = 0 := by
  classical
  unfold SurfacePoint.levelNumber
  split_ifs
  · rw [h, localNumber, Finsupp.sum_zero_index, ENat.toNat_zero]
  · rfl
theorem finite_base {N p : ℕ} [CharP E p] (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N)
    (hp : 3 * N < p) (f : RCN002.CoordinateField E G) (c : E) :
    {q : SurfacePoint G | f ∉ q.ring ∧ q.level f c ≠ 0}.Finite := by
  by_cases hf : f = algebraMap E (RCN002.CoordinateField E G) c
  · refine Set.Finite.subset Set.finite_empty fun q hq => hq.1 ?_
    rw [hf]
    exact q.ring.algebraMap_mem c
  · exact finite_basePoints hN hp f c hf
variable {ι : Type*} {F : ι → Type*} [∀ a, Field (F a)] [∀ a, Algebra E (F a)]
open Classical in
theorem point_exchange (hc : ∀ j, coordinate E G j ≠ 0) (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G)
    (W : FlagDegree) (hdisj : LevelDisjoint f c A₁ W) (s : Finset ι)
    (S : ∀ a, Specialization (RCN002.CoordinateField E G) (F a)) (m : ι → ℕ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, (S a).val = (S b).val → a = b)
    (hcoord : ∀ a ∈ s, ∀ j, (S a).val (coordinate E G j) ≤ 1)
    (hdiv : ∀ a ∈ s, ∀ q : SurfacePoint G, q.On (S a) → ∃ P : PrimeDivisor q.ring,
      (∀ x : q.ring, x ∈ P.ideal ↔ (S a).val (x : RCN002.CoordinateField E G) < 1) ∧
        P.valuation (RCN002.CoordinateField E G) = (S a).val)
    (hord : ∀ a ∈ s, (S a).val A₁ ≤ exp (-(m a : ℤ)))
    (q : SurfacePoint G) (hreg : q.localFunction A₁ W ∈ q.ring) (hf : f ∉ q.ring)
    (hL : q.level f c ≠ 0)
    (hp1 : ∀ a ∈ s, ∀ hq : q.On (S a), PlaceSurf.Statement.LeastOrderLE E (S a) hq) (n : ℕ) :
    ∑ a ∈ s, m a * q.order (S a) f c n ≤
      n * q.levelNumber f c (q.localFunction A₁ W) + pointLoss q (q.localFunction A₁ W) +
        ∑ a ∈ s, if hq : q.On (S a) then m a * closureColength ((S a).image hq) (F a) else 0 := by
  classical
  have hO : DivisorChain q.ring := q.divisorChain
  have hD : ∀ P ∈ (q.level f c).support, (⟨_, hreg⟩ : q.ring) ∉ P.ideal := fun P hP =>
    (P.valuation_eq_one_iff (RCN002.CoordinateField E G) ⟨_, hreg⟩).mp (hdisj q hf P (Finsupp.mem_support_iff.mp hP))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q.level f c P₀ ≠ 0 := by
    by_contra h
    exact hL (Finsupp.ext fun P => not_not.mp fun hP => h ⟨P, hP⟩)
  have hg : (⟨_, hreg⟩ : q.ring) ≠ 0 := by
    intro h0
    have h1 := hdisj q hf P₀ hP₀
    rw [show q.localFunction A₁ W = 0 from congrArg Subtype.val h0, map_zero] at h1
    exact zero_ne_one h1
  have hval : ∀ a ∈ s, q.On (S a) → (S a).val (q.localFunction A₁ W) ≤ exp (-(m a : ℤ)) := by
    intro a ha hq
    rw [SurfacePoint.localFunction, map_div₀, val_vertex_eq_one hc q (S a) hq (hcoord a ha) W,
      div_one]
    exact hord a ha
  let Pd : ι → PrimeDivisor q.ring := fun a =>
    if h : a ∈ s ∧ q.On (S a) then (hdiv a h.1 q h.2).choose else P₀
  have hPd : ∀ a (ha : a ∈ s) (hq : q.On (S a)),
      (∀ x : q.ring, x ∈ (Pd a).ideal ↔ (S a).val (x : RCN002.CoordinateField E G) < 1) ∧
        (Pd a).valuation (RCN002.CoordinateField E G) = (S a).val := by
    intro a ha hq
    simp only [Pd, dite_eq_left (And.intro ha hq)]
    exact (hdiv a ha q hq).choose_spec
  let δf : ι → ℕ := fun a =>
    if hq : q.On (S a) then closureColength ((S a).image hq) (F a) else 0
  have key := sum_mul_le_toNat (RCN002.CoordinateField E G) hO hg (q.level f c) hD
    (s.filter fun a => 0 < m a ∧ q.On (S a)) Pd ?_ m ?_ (fun a => q.order (S a) f c n) δf n ?_
  · have hlhs : ∑ a ∈ s, m a * q.order (S a) f c n =
        ∑ a ∈ s.filter (fun a => 0 < m a ∧ q.On (S a)), m a * q.order (S a) f c n := by
      refine (Finset.sum_filter_of_ne fun a _ hne => ⟨?_, ?_⟩).symm
      · exact Nat.pos_of_ne_zero fun h0 => hne (by rw [h0, zero_mul])
      · by_contra hq
        exact hne (by rw [SurfacePoint.order, dite_eq_right hq, mul_zero])
    have hnum : q.levelNumber f c (q.localFunction A₁ W) =
        ((q.level f c).sum fun Q k => (k : ℕ∞) * Module.length q.ring
          (q.ring ⧸ (Q.ideal ⊔ Ideal.span {(⟨_, hreg⟩ : q.ring)}))).toNat := by
      rw [SurfacePoint.levelNumber, dite_eq_left hreg]
      rfl
    have hloss : pointLoss q (q.localFunction A₁ W) = loss (RCN002.CoordinateField E G) (⟨_, hreg⟩ : q.ring) := by
      rw [pointLoss, dite_eq_left hreg]
    have hrhs : ∑ a ∈ s.filter (fun a => 0 < m a ∧ q.On (S a)), m a * δf a ≤
        ∑ a ∈ s, if hq : q.On (S a) then m a * closureColength ((S a).image hq) (F a) else 0 := by
      refine (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans_eq
        (Finset.sum_congr rfl fun a _ => ?_)
      simp only [δf]
      split_ifs <;> simp
    rw [hlhs, hnum, hloss]
    exact key.trans (Nat.add_le_add_left hrhs _)
  · intro a ha b hb hab
    rw [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    refine hinj a ha.1 b hb.1 ?_
    rw [← (hPd a ha.1 ha.2.2).2, ← (hPd b hb.1 hb.2.2).2, hab]
  · intro a ha
    rw [Finset.mem_filter] at ha
    have h1 := hval a ha.1 ha.2.2
    rw [← (hPd a ha.1 ha.2.2).2] at h1
    have h2 := valuation_eq_exp_neg_div (RCN002.CoordinateField E G) hg (Pd a)
    rw [show algebraMap q.ring (RCN002.CoordinateField E G) ⟨_, hreg⟩ = q.localFunction A₁ W from rfl] at h2
    rw [h2, exp_le_exp] at h1
    omega
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨has, hma, hq⟩ := ha
    have hzero : q.level f c (Pd a) = 0 := by
      by_contra hne
      have h1 := hdisj q hf (Pd a) hne
      have h2 := hval a has hq
      rw [← (hPd a has hq).2, h1] at h2
      have h3 : exp (-(m a : ℤ)) < 1 := by
        rw [← exp_zero]
        exact exp_lt_exp.mpr (by omega)
      exact absurd h2 (not_le.mpr h3)
    have hI : ¬levelIdeal (O := q.ring) (RCN002.CoordinateField E G) f c n ≤ (Pd a).ideal :=
      divisorIdeal_not_le (RCN002.CoordinateField E G) (by
        rw [Finsupp.smul_apply]
        exact (smul_eq_zero_of_right n hzero : n • (levelDivisor (O := q.ring) (RCN002.CoordinateField E G) f c) (Pd a) = 0))
    have h4 := hp1 a has hq (Pd a).ideal (hPd a has hq).1 _ hI
    simp only [δf, dite_eq_left hq, SurfacePoint.order, Specialization.levelOrder]
    exact h4
theorem component_exchange {N p : ℕ} [CharP E p]
    (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p)
    (hc : ∀ j, coordinate E G j ≠ 0) (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) (W : FlagDegree)
    (hreg : ∀ q : SurfacePoint G, q.localFunction A₁ W ∈ q.ring)
    (hdisj : LevelDisjoint f c A₁ W) (s : Finset ι)
    (S : ∀ a, Specialization (RCN002.CoordinateField E G) (F a)) (m : ι → ℕ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, (S a).val = (S b).val → a = b)
    (hcoord : ∀ a ∈ s, ∀ j, (S a).val (coordinate E G j) ≤ 1)
    (hdiv : ∀ a ∈ s, ∀ q : SurfacePoint G, q.On (S a) → ∃ P : PrimeDivisor q.ring,
      (∀ x : q.ring, x ∈ P.ideal ↔ (S a).val (x : RCN002.CoordinateField E G) < 1) ∧
        P.valuation (RCN002.CoordinateField E G) = (S a).val)
    (hord : ∀ a ∈ s, (S a).val A₁ ≤ exp (-(m a : ℤ)))
    (hp1 : ∀ a ∈ s, ∀ (q : SurfacePoint G) (hq : q.On (S a)), f ∉ q.ring → q.level f c ≠ 0 →
      PlaceSurf.Statement.LeastOrderLE E (S a) hq) (n : ℕ) :
    ∑ a ∈ s, m a * curveBase (S a) f c n ≤
      n * baseNumber f c A₁ W + componentLoss f c A₁ W s S m := by
  classical
  have hfin := finite_base hN hp f c
  have hT : ∀ q, q ∈ hfin.toFinset ↔ f ∉ q.ring ∧ q.level f c ≠ 0 := fun q => hfin.mem_toFinset
  have hbase : ∀ a, curveBase (S a) f c n = ∑ q ∈ hfin.toFinset, q.order (S a) f c n := by
    intro a
    unfold curveBase
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · exact Finset.sum_congr rfl fun q hq => ite_eq_right ((hT q).mp hq).1
    · intro q hq
      rw [Function.mem_support] at hq
      rw [Finset.mem_coe, hT]
      by_cases h1 : f ∈ q.ring
      · exact absurd (ite_eq_left h1) hq
      · exact ⟨h1, fun h0 => hq (by rw [ite_eq_right h1, order_eq_zero q (S a) f c n h0])⟩
  have hnum : baseNumber f c A₁ W =
      ∑ q ∈ hfin.toFinset, q.levelNumber f c (q.localFunction A₁ W) := by
    unfold baseNumber
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · exact Finset.sum_congr rfl fun q hq => ite_eq_right ((hT q).mp hq).1
    · intro q hq
      rw [Function.mem_support] at hq
      rw [Finset.mem_coe, hT]
      by_cases h1 : f ∈ q.ring
      · exact absurd (ite_eq_left h1) hq
      · exact ⟨h1, fun h0 => hq (by rw [ite_eq_right h1, levelNumber_eq_zero q f c _ h0])⟩
  have hloss : componentLoss f c A₁ W s S m = ∑ q ∈ hfin.toFinset,
      (pointLoss q (q.localFunction A₁ W) +
        ∑ a ∈ s, if hq : q.On (S a) then m a * closureColength ((S a).image hq) (F a) else 0) := by
    unfold componentLoss
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · exact Finset.sum_congr rfl fun q hq => ite_eq_left ((hT q).mp hq)
    · intro q hq
      rw [Function.mem_support] at hq
      rw [Finset.mem_coe, hT]
      by_contra h
      exact hq (ite_eq_right h)
  calc ∑ a ∈ s, m a * curveBase (S a) f c n
      = ∑ q ∈ hfin.toFinset, ∑ a ∈ s, m a * q.order (S a) f c n := by
        simp only [hbase, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ q ∈ hfin.toFinset, (n * q.levelNumber f c (q.localFunction A₁ W) +
          pointLoss q (q.localFunction A₁ W) +
          ∑ a ∈ s, if hq : q.On (S a) then m a * closureColength ((S a).image hq) (F a) else 0) :=
        Finset.sum_le_sum fun q hq =>
          point_exchange hc f c A₁ W hdisj s S m hinj hcoord hdiv hord q (hreg q)
            ((hT q).mp hq).1 ((hT q).mp hq).2
            (fun a ha hqa => hp1 a ha q hqa ((hT q).mp hq).1 ((hT q).mp hq).2) n
    _ = n * baseNumber f c A₁ W + componentLoss f c A₁ W s S m := by
        rw [hnum, hloss, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => add_assoc _ _ _
end Surface
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
namespace Exch
open WithZero MvPolynomial HFree6812
open RCN002 RCN095
open RCN095 renaming PolynomialInFlag → BI
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing
theorem SurfaceDivisor.trivial_on_constants {sR sY sZ : Bool} {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰}
    (h : SurfaceDivisor G sR sY sZ nu) (a : E) (ha : a ≠ 0) : nu (algebraMap E (RCN002.CoordinateField E G) a) = 1 := by
  obtain ⟨t, -, -, ht⟩ := h.nonconst
  exact ht _ (IntermediateField.algebraMap_mem _ a) ((map_ne_zero _).mpr ha)
theorem levelDisjoint_of_unit {N p : ℕ} [CharP E p]
    (hN : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N) (hp : 3 * N < p) (f : RCN002.CoordinateField E G) (c : E)
    (A₁ : RCN002.CoordinateField E G) (W : FlagDegree)
    (hunit : ∀ nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰, (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) →
      nu (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 → (∀ j, nu (coordinate E G j) = 1) ∧ nu A₁ = 1) :
    LevelDisjoint f c A₁ W := by
  intro q hf P hlev
  have hne : f - algebraMap E (RCN002.CoordinateField E G) c ≠ 0 := fun h0 => hf (by
    rw [sub_eq_zero.mp h0]
    exact q.ring.algebraMap_mem c)
  have h3 : q.level f c P = (-(P.valuation (RCN002.CoordinateField E G) (f - algebraMap E (RCN002.CoordinateField E G) c)).log).toNat :=
    zeroDivisor_apply (RCN002.CoordinateField E G) hne P
  rw [h3] at hlev
  have hlt : P.valuation (RCN002.CoordinateField E G) (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 := by
    rw [← exp_zero]
    exact (log_lt_iff_lt_exp ((Valuation.ne_zero_iff _).mpr hne)).mp (by omega)
  obtain ⟨h2, h1⟩ := hunit _ ⟨_, _, _, q.surfaceDivisor hN hp P⟩ hlt
  rw [SurfacePoint.localFunction, map_div₀, h1, lmono, map_mul, map_mul, map_zpow₀, map_zpow₀,
    map_zpow₀, h2, h2, h2, one_zpow, one_zpow, one_zpow, mul_one, mul_one, div_one]
end Surface
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
namespace Sec
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
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime
def ChoiceStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
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
        Module.Finite (S.image hq) (integralClosure (S.image hq) (RCN002.CoordinateField Ω C))),
    ∃ (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
      (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1))
      (s₀ s₁ s₂ : MvPolynomial (Fin 3) Ω),
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q ∧ RCN095.PolynomialInFlag unitYZFlag A ∧ (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 ∧
      (∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) ∧
      CurveNeeds P SZ Q A c S ∧
      Exch.ExchangeNeeds P SZ Q A c S (Exch.flag SZ ⟨t - y, y - r, r - 1⟩) ∧
      LevelNeeds P SZ Q A c S ∧
      Needs P SZ Q A c unitZFlag s₀ ∧ Needs P SZ Q A c unitYZFlag s₁ ∧
      Needs P SZ Q A c unitAllFlag s₂
def DataStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
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
        Module.Finite (S.image hq) (integralClosure (S.image hq) (RCN002.CoordinateField Ω C))),
    ∃ (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
      (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1)),
      RCN095.PolynomialInFlag (2 • unitAllFlag) Q ∧ RCN095.PolynomialInFlag unitYZFlag A ∧ (2 : MvPolynomial (Fin 3) Ω) * A ≠ 0 ∧
      (∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a)) ∧
      CurveNeeds P SZ Q A c S ∧
      Exch.ExchangeNeeds P SZ Q A c S (Exch.flag SZ ⟨t - y, y - r, r - 1⟩) ∧
      LevelNeeds P SZ Q A c S
def SectionStatement (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) : Prop :=
  haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  ∀ (N : ℕ) (_hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (_hNp : 3 * N < 2130706433) (_hc : ∀ j, sliceCoord P.F j ≠ 0)
    (_hlead : srcLead P.F P.F SZ ≠ 0) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (_hcomp : ∀ g, LevelCount.Needs (Exch.component P g) (P.stage g).G (baseH P.F)
      (Exch.moving P Q A g) c (Exch.function P SZ g))
    (_hsep : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Nonempty (RCN341.SeparableLiteralCoordinate B.prime)),
    ∃ s₀ s₁ s₂ : MvPolynomial (Fin 3) Ω,
      Needs P SZ Q A c unitZFlag s₀ ∧ Needs P SZ Q A c unitYZFlag s₁ ∧
      Needs P SZ Q A c unitAllFlag s₂
theorem choice_of_data_of_section (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F)
    (hdata : DataStatement P SZ) (hsection : SectionStatement P SZ) : ChoiceStatement P SZ := by
  intro N hN hNp hc htail hlead hbase hsep hclosure
  obtain ⟨Q, A, c, S, hQ, hA, h2, hS, hcurve, hexch, hlevel⟩ :=
    hdata N hN hNp hc htail hlead hbase hsep hclosure
  obtain ⟨s₀, s₁, s₂, h₀, h₁, h₂⟩ := hsection N hN hNp hc hlead Q A c hlevel.component
    fun g B => hsep Q A hQ hA c g (hlevel.component g).ne B
  exact ⟨Q, A, c, S, s₀, s₁, s₂, hQ, hA, h2, hS, hcurve, hexch, hlevel, h₀, h₁, h₂⟩
end
end Packet
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
section Packet
noncomputable section
open scoped Classical BigOperators
open WithZero HFree6812
open RCN002 RCN055 RCN074 RCN086 RCN095 RCN135 RCN136 RCN156 RCN187 RCN199 RCN204 RCN222 RCN238
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open RCN243 RCN264 RCN313
open DU AFA BOE BD
open MovingFiberThreeSources6811 (direction weight)
open SecondJetCoefficients (liftExponent)
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] Exch.component_isPrime SurfacePoint.isNoetherianRing
  SurfacePoint.isIntegrallyClosed SurfacePoint.isFractionRing
omit [CharP K 2130706433] in
theorem Curve.order_of_levelRestrict (F : MvPolynomial (Fin 4) K)
    (G C : Ideal (MvPolynomial (Fin 3) Ω)) [G.IsPrime] [C.IsPrime]
    (S : Specialization (RCN002.CoordinateField Ω G) (RCN002.CoordinateField Ω C)) (Hf : FlagDegree) (f : RCN002.CoordinateField Ω G) (fC : RCN002.CoordinateField Ω C) (c : Ω) (m : ℕ)
    (hlev : LevelRestrict F G C S Hf f fC c m) (n : ℕ)
    (hpsi0 : tailCubeOn (RCN135.polynomialEmbedding K) F C m ^ n * ((fC - algebraMap Ω (RCN002.CoordinateField Ω C) c) ^ (4 * (m + 1)))⁻¹ ^ n ≠ 0)
    (q : SurfacePoint G) (hq : q.On S) (μ : RCN026.Place_p19 Ω (RCN002.CoordinateField Ω C)) (hμ : μ ∈ S.placesOn Ω hq) :
    -flagPole μ.val (coordinate Ω C) (n • cutFlag (m + 1) Hf) -
        ((4 * (m + 1) * placeOrder q S f c n μ : ℕ) : ℤ) ≤
      RCN026.order_p19 Ω (RCN002.CoordinateField Ω C) μ
        (tailCubeOn (RCN135.polynomialEmbedding K) F C m ^ n * ((fC - algebraMap Ω (RCN002.CoordinateField Ω C) c) ^ (4 * (m + 1)))⁻¹ ^ n) := by
  have h1 := hlev q hq μ hμ n
  rw [← map_pow, show psiCOn F C fC c m ^ n = tailCubeOn (RCN135.polynomialEmbedding K) F C m ^ n *
      ((fC - algebraMap Ω (RCN002.CoordinateField Ω C) c) ^ (4 * (m + 1)))⁻¹ ^ n by
    rw [psiCOn, div_eq_mul_inv, mul_pow]] at h1
  have h2 := (log_le_iff_le_exp ((Valuation.ne_zero_iff _).2 hpsi0)).2 h1
  rw [RCN204.flagPole_nsmul, placeOrder_of_on hq]
  show _ ≤ -(μ.val (tailCubeOn (RCN135.polynomialEmbedding K) F C m ^ n * _)).log
  push_cast
  linarith
theorem Curve.moving_unit {E : Type} [Field E] {C : Ideal (MvPolynomial (Fin 3) E)} [C.IsPrime]
    {v : Fin 3 → E} {mu : RCN026.Place_p19 E (RCN002.CoordinateField E C)} (hmu : PlaceOver C v mu)
    (H Gs Q U : MvPolynomial (Fin 3) E) (c : E) (hH : mu.val (RCN002.coordinateEvaluation E C H) = 1)
    (hv : MvPolynomial.aeval v (H * (Q - MvPolynomial.C c) + U * Gs) ≠ 0) (k n : ℕ) :
    mu.val (((RCN208.movingValue C H Gs Q U - algebraMap E (RCN002.CoordinateField E C) c) ^ k)⁻¹ ^ n) = 1 := by
  have hH0 : RCN002.coordinateEvaluation E C H ≠ 0 := fun h => by
    rw [h, map_zero] at hH
    exact zero_ne_one hH
  have h2 := hmu.eq_one _ hv
  have h3 : RCN002.coordinateEvaluation E C (H * (Q - MvPolynomial.C c) + U * Gs) =
      RCN002.coordinateEvaluation E C H * (RCN208.movingValue C H Gs Q U - algebraMap E (RCN002.CoordinateField E C) c) := by
    rw [RCN208.movingValue, map_add, map_mul, map_mul, map_sub,
      show RCN002.coordinateEvaluation E C (MvPolynomial.C c) = algebraMap E (RCN002.CoordinateField E C) c from (RCN002.coordinateEvaluation E C).commutes c, div_eq_mul_inv]
    linear_combination (-(RCN002.coordinateEvaluation E C U * RCN002.coordinateEvaluation E C Gs)) * mul_inv_cancel₀ hH0
  rw [h3, map_mul, hH, one_mul] at h2
  rw [map_pow, map_inv₀, map_pow, h2, one_pow, inv_one, one_pow]
theorem Curve.count_flag (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (Hf : FlagDegree) (h5 : 5 ≤ 2 * Hf.all)
    (hHf : haveI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
      ∀ (sR sY sZ : Bool) (v : Valuation (SliceField P.F) ℤᵐ⁰), ChartDivisor P.F sR sY sZ v →
        v (sliceProj P.F (polyH K P.F)) ≤ exp (flagPole v (sliceCoord P.F) Hf))
    (budget : ∀ a : Curve P, RD a.2.1 (baseH P.F) (baseG P.F)) (base : ∀ a : Curve P, RCN341.SeparableLiteralCoordinate a.2.1)
    (N : ℕ) (hN : ∀ (g : RCN222.GeometricFactor K P.F) (sR sY sZ : Bool), SurfaceNoether (Exch.component P g) sR sY sZ N)
    (hp : 3 * N < 2130706433) (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (S : ∀ a : Curve P, Specialization (RCN002.CoordinateField Ω (Exch.component P a.1)) (RCN002.CoordinateField Ω a.2.1))
    (hS : ∀ a ∈ active P SZ, IsCurveOnSurface (Exch.component P a.1) a.2.1 (S a))
    (needs : CurveNeeds P SZ Q A c S) :
    ∀ n : ℕ, ∀ a ∈ active P SZ, ∀ delay : ℕ, 1 ≤ delay →
      RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1 + delay) ∉ a.2.1 →
      3 * n * (RCN264.componentSeeds Ω (P.stage a.1).G (RCN086.globalTailCut (RCN135.polynomialEmbedding K) (P.stage a.1).F (w + 1)) (CR (RCN135.polynomialEmbedding K) (P.stage a.1).F)
          (KK K P.F P.selected P.seeds a.1) (DK (RCN135.polynomialEmbedding K) (P.stage a.1).selected) a.2).card ≤
        n * (budget a).weightedCost (cutFlag (w + delay) Hf) +
          4 * (w + delay) * (n * curveMoving (S a) (Exch.moving P Q A a.1) c +
            Exch.baseOrder P Q A c S n a) := by
  intro n a ha delay _ hcut
  have hFact : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  have hker := Exch.ker_sliceMap_component P a.1
  have hSa := hS a ha
  have hSfc := needs.off_level a ha
  obtain ⟨m, hm1, hm2⟩ : ∃ m, w + delay = m + 1 ∧ w + 1 + delay = m + 2 :=
    ⟨131070 + delay, by unfold RCN326.w; omega, by unfold RCN326.w; omega⟩
  have hcut' : RCN086.globalTailCut (RCN135.polynomialEmbedding K) P.F (m + 2) ∉ a.2.1 := hm2 ▸ hcut
  have hHC : surfaceMap (RCN135.polynomialEmbedding K) (polyH K P.F) ∉ a.2.1 := fun h => hcut' (by
    rw [tailCut_eq]
    exact a.2.1.mul_mem_right _ (a.2.1.mul_mem_right _ (a.2.1.pow_mem_of_mem h 3 (by norm_num))))
  have hNC : surfaceMap (RCN135.polynomialEmbedding K) (RCN055.baseNumerator P.F m) ∉ a.2.1 := fun h => hcut' (by
    rw [tailCut_eq]
    exact a.2.1.mul_mem_right _ (a.2.1.mul_mem_left _ h))
  have hH : sliceProj P.F (polyH K P.F) ≠ 0 :=
    sliceProj_ne_zero_of_notMem P.F _ hker a.2.1 hSa.ideal_le _ hHC
  have hc : ∀ j, sliceCoord P.F j ≠ 0 := sliceCoord_ne_zero P.F P.F (dvd_refl P.F) hH m
    (sliceProj_ne_zero_of_notMem P.F _ hker a.2.1 hSa.ideal_le _ hNC)
  have hcG : ∀ j, coordinate Ω (Exch.component P a.1) j ≠ 0 := fun j => by
    rw [← sliceEmbedding_coord P.F _ hker j]
    exact (map_ne_zero _).mpr (hc j)
  have htr : ∃ j, Transcendental Ω (coordinate Ω a.2.1 j) :=
    ⟨(base a).index, (base a).transcendental⟩
  have hfR : (S a).Restricts (Exch.moving P Q A a.1)
      (RCN208.movingValue a.2.1 (baseH P.F) (baseG P.F) Q A) :=
    hSa.restricts_movingValue _ _ Q A hHC
  have hfC0 := (hfR.sub (hSa.restricts_algebraMap c)).ne_zero hSfc
  have hstep := Curve.step_one P.F (Exch.component P a.1) hker hH hcG Hf h5 hHf
    (fun sR sY sZ => Chart.common_place_law P.F P.F (dvd_refl P.F) hH t P.total_weight
      (by have := packet_t_le P; omega) hc sR sY sZ)
    (hN a.1) hp (Exch.moving P Q A a.1) c
    (fun h => by rw [h, map_zero] at hSfc; exact zero_ne_one hSfc) (needs.pole a ha)
  have hlev := Curve.level_restrict P.F (Exch.component P a.1) a.2.1 hker (S a) hSa hcG htr hHC
    Hf _ _ c hfR hSfc hstep m
  choose pt hpt using fun μ : RCN026.Place_p19 Ω (RCN002.CoordinateField Ω a.2.1) =>
    hSa.exists_point (hN a.1) hp hcG htr μ
  have hpsi0 : tailCubeOn (RCN135.polynomialEmbedding K) P.F a.2.1 m ^ n *
      ((RCN208.movingValue a.2.1 (baseH P.F) (baseG P.F) Q A - algebraMap Ω (RCN002.CoordinateField Ω a.2.1) c) ^
        (4 * (m + 1)))⁻¹ ^ n ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hfC0)))
    rw [tailCubeOn, map_pow, map_pow]
    exact div_ne_zero (pow_ne_zero _ fun h => hNC ((SecondJetComponentRoots.evaluation_zero_iff a.2.1 _).1 h))
      (pow_ne_zero _ fun h => hHC ((SecondJetComponentRoots.evaluation_zero_iff a.2.1 _).1 h))
  have hcount := tail_curve_count_of_bound (P.stage a.1) a.2 (base a) (budget a) m n
    (by unfold RCN326.w at hm1 ⊢; omega) _
    (fun γ hγ mu hmu => moving_unit hmu (baseH P.F) (baseG P.F) Q A c
      (seed_place (P.stage a.1) a.2 γ hγ mu hmu).1 (needs.seed a ha γ hγ) (4 * (m + 1)) n)
    hpsi0 (n • cutFlag (m + 1) Hf)
    (fun μ => 4 * (m + 1) * placeOrder (pt μ) (S a) (Exch.moving P Q A a.1) c n μ)
    (4 * (m + 1) * (n * curveMoving (S a) (Exch.moving P Q A a.1) c +
      curveBase (S a) (Exch.moving P Q A a.1) c n))
    (fun T => by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (sum_placeOrder_le (base a) hSa hcG htr _ c hSfc (hN a.1) hp
        n pt hpt T))
    (fun μ => (hpt μ).elim fun hq hμ =>
      order_of_levelRestrict P.F _ a.2.1 (S a) Hf _ _ c m hlev n hpsi0 (pt μ) hq μ hμ)
  have hw : (budget a).weightedCost (n • cutFlag (m + 1) Hf) =
      n * (budget a).weightedCost (cutFlag (w + delay) Hf) := by
    rw [hm1]
    simp only [RD.weightedCost, nsmul_zOnly, nsmul_yz, nsmul_all]
    ring
  rw [hw, ← hm1] at hcount
  exact hcount
end
end Packet
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
section Packet
noncomputable section
open scoped Classical BigOperators
open MvPolynomial
open RCN002 RCN072 RCN084 RCN095 RCN135 RCN136 RCN222 RCN264
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN222 renaming GeometricFactor → EX
open BD DU _Q7 AFA OT LF YE AVZ
open MovingFiberThreeSources6811 (direction weight)
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] LevelComponent.isPrime Exch.component_isPrime
theorem baseH_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    RCN002.coordinateEvaluation Ω (Exch.component P g) (baseH P.F) ≠ 0 := fun h0 =>
  (P.stage g).BLO (Ideal.mem_span_singleton.mp
    ((BR_eq_zero_iff (G := Exch.component P g) (baseH P.F)).mp h0))
theorem baseH_mem_span (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    baseH P.F ∈ Ideal.span {(P.stage g).G, pderiv 1 (P.stage g).G} := by
  obtain ⟨h, hh⟩ := (P.stage g).RR
  have hH : baseH P.F = pderiv 1 (surfaceMap (RCN135.polynomialEmbedding K) P.F) := (RCN267.surfaceMap_pderiv_R (RCN135.polynomialEmbedding K) P.F).symm
  have hh' : surfaceMap (RCN135.polynomialEmbedding K) P.F = (P.stage g).G * h := hh
  rw [hH, hh', Derivation.leibniz]
  exact Ideal.mem_span_pair.mpr ⟨pderiv 1 h, h, by simp only [smul_eq_mul]; ring⟩
theorem pderiv_stage_ne_zero (P : Packet x t y r) (g : RCN222.GeometricFactor K P.F) :
    pderiv 1 (P.stage g).G ≠ 0 := fun h0 => by
  have h := baseH_mem_span P g
  rw [h0] at h
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  rw [mul_zero, add_zero] at hab
  exact (P.stage g).BLO ⟨a, hab.symm.trans (mul_comm a _)⟩
theorem setup (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (N : ℕ)
    (hN : ∀ g sR sY sZ, SurfaceNoether (Exch.component P g) sR sY sZ N)
    (hNp : 3 * N < 2130706433) (hcoord : ∀ g j, coordinate Ω (Exch.component P g) j ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (c : Ω)
    (hsep : ∀ g (B : LevelComponent (Exch.component P g) (Exch.moving P Q A g) c),
      Nonempty (RCN341.SeparableLiteralCoordinate B.prime))
    (W : FlagDegree) (s : MvPolynomial (Fin 3) Ω)
    (hgate : 2 * t * (W.zOnly + W.yz + W.all) < 2130706433) (hneeds : Needs P SZ Q A c W s)
    (g : RCN222.GeometricFactor K P.F) :
    Setup (Exch.component P g) N 2130706433 (P.stage g).G (baseH P.F) (baseG P.F) Q A c W s where
  algClosed := inferInstance
  charP := RCN135.genericField_charP K 2130706433
  noether := hN g
  char := hNp
  coord := hcoord g
  irreducible := (P.stage g).MW
  span := rfl
  unitH := baseH_ne_zero P g
  memH := baseH_mem_span P g
  not_dvd := (hneeds.good g).1
  localGen := fun C hC => ((hneeds.good g).2 C hC).2
  needs := hneeds.component g
  sep := hsep g
  sepD := fun D => by
    have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
    have hthi := packet_t_le P
    have hylo := P.ylow
    have hyt := P.yt
    obtain ⟨B⟩ := EFX (baseCarrier P.F) s (baseH P.F) ⟨t - y, y - r, r⟩ W
      (RCN136.surfaceMap_ne_zero (RCN135.polynomialEmbedding K) (RCN135.polynomialEmbedding_injective K) P.F P.irreducible.ne_zero) (P.parent_flag Ω (RCN135.polynomialEmbedding K))
      hneeds.flag 2130706433
      (by show t - y + (y - r) + r < 2130706433; omega)
      (by show 2 * (t - y + (y - r) + r) * (W.zOnly + W.yz + W.all) < 2130706433
          rw [show t - y + (y - r) + r = t by omega]
          exact hgate)
    exact ⟨B.base ⟨(P.stage g).G, Finset.mem_filter.mpr
      ⟨g.2, (hneeds.good g).1, pderiv_stage_ne_zero P g⟩⟩ D⟩
theorem flag_bound (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) :
    FlagBoundStatement P SZ scale z u v := by
  intro hbudget N hN hNp hcoord Q A hQ hA c _ hsep W s hgate hneeds sfam T
  have hchar : CharP Ω 2130706433 := RCN135.genericField_charP K 2130706433
  have hthi := packet_t_le P
  have hylo := P.ylow
  have hyt := P.yt
  choose Vg hVg using fun g =>
    (setup P SZ N hN hNp hcoord Q A c hsep W s hgate hneeds g).component_count
  let emb : ((g : RCN222.GeometricFactor K P.F) × RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F)) →
      ANR (baseCarrier P.F) s (baseH P.F) := fun xx =>
    ⟨⟨(P.stage xx.1).G, Finset.mem_filter.mpr
      ⟨xx.1.2, (hneeds.good xx.1).1, pderiv_stage_ne_zero P xx.1⟩⟩, xx.2⟩
  let back : ANR (baseCarrier P.F) s (baseH P.F) →
      ((g : RCN222.GeometricFactor K P.F) × RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F)) := fun a =>
    ⟨⟨a.1.1, (Finset.mem_filter.mp a.1.2).1⟩, a.2⟩
  have hback : Function.LeftInverse back emb := fun _ => rfl
  have hlead : ∀ a ∈ Finset.univ.map ⟨emb, hback.injective⟩, SZ.leading (RCN135.polynomialEmbedding K) ∉ a.2.1 := by
    intro a ha
    obtain ⟨xx, -, rfl⟩ := Finset.mem_map.mp ha
    exact ((hneeds.good xx.1).2 xx.2.1 (AAS Ω _ _ _ xx.2)).1
  have hzero := sectionZeroBudget (K := K) (E := Ω) (RingHom.id Ω) P.F SZ ⟨t - y, y - r, r⟩ W s
    scale z u v P.irreducible.ne_zero (P.parent_flag Ω (RCN135.polynomialEmbedding K)) hneeds.flag
    (by show t - y + (y - r) + r < 2130706433; omega)
    (by show 2 * (t - y + (y - r) + r) * (W.zOnly + W.yz + W.all) < 2130706433
        rw [show t - y + (y - r) + r = t by omega]
        exact hgate)
    hbudget Q A c hQ hA (Finset.univ.map ⟨emb, hback.injective⟩) hlead
    (fun a => Vg (back a).1 (back a).2)
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg scale)) hzero
  calc ∑ g, levelFlagSum (sfam g) (T g) W
      ≤ ∑ g : RCN222.GeometricFactor K P.F, ∑ D : RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F),
          levelZeros D.1 (baseH P.F) (baseG P.F) Q A c (Vg g D) :=
        Finset.sum_le_sum fun g _ => hVg g (sfam g) (T g)
    _ = ∑ xx : (g : RCN222.GeometricFactor K P.F) × RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F),
          levelZeros xx.2.1 (baseH P.F) (baseG P.F) Q A c (Vg xx.1 xx.2) :=
        (Fintype.sum_sigma' fun (g : RCN222.GeometricFactor K P.F) (D : RCN264.RegularComponent Ω (P.stage g).G s (baseH P.F)) =>
          levelZeros D.1 (baseH P.F) (baseG P.F) Q A c (Vg g D)).symm
    _ = _ := (Finset.sum_map Finset.univ ⟨emb, hback.injective⟩ fun a =>
          levelZeros a.2.1 (baseH P.F) (baseG P.F) Q A c (Vg (back a).1 (back a).2)).symm
theorem section_bound (P : Packet x t y r) (SZ : MovingFiberThreeSources6811.Source P.F) (scale z u v : ℕ) :
    SectionBoundStatement P SZ scale z u v := by
  intro hbudget N hN hNp hcoord Q A hQ hA c hlen hsep s₀ s₁ s₂ h₀ h₁ h₂ sfam T
  have hthi := packet_t_le P
  have h0 := flag_bound P SZ scale z u v hbudget N hN hNp hcoord Q A hQ hA c hlen hsep unitZFlag s₀
    (by show 2 * t * (1 + 0 + 0) < 2130706433; omega) h₀ sfam T
  have h1 := flag_bound P SZ scale z u v hbudget N hN hNp hcoord Q A hQ hA c hlen hsep unitYZFlag s₁
    (by show 2 * t * (0 + 1 + 0) < 2130706433; omega) h₁ sfam T
  have h2 := flag_bound P SZ scale z u v hbudget N hN hNp hcoord Q A hQ hA c hlen hsep unitAllFlag s₂
    (by show 2 * t * (0 + 0 + 1) < 2130706433; omega) h₂ sfam T
  have e0 : unitZFlag.zOnly * z + unitZFlag.yz * u + unitZFlag.all * v = z := by
    show 1 * z + 0 * u + 0 * v = z
    omega
  have e1 : unitYZFlag.zOnly * z + unitYZFlag.yz * u + unitYZFlag.all * v = u := by
    show 0 * z + 1 * u + 0 * v = u
    omega
  have e2 : unitAllFlag.zOnly * z + unitAllFlag.yz * u + unitAllFlag.all * v = v := by
    show 0 * z + 0 * u + 1 * v = v
    omega
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h0, h1, h2⟩
end
end Packet
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
namespace LevelCount
open WithZero MvPolynomial HFree6812
open RCN002 RCN095 RCN204
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
section Ring
variable {O : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
  (L : Type*) [Field L] [Algebra O L] [IsFractionRing O L]
omit [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] in
theorem sum_le_divisor_sum {ι : Type*} (s : Finset ι) (P : ι → PrimeDivisor O) (hP : Set.InjOn P s)
    (D : Divisor O) (e : ι → ℕ) (he : ∀ i ∈ s, e i ≤ D (P i)) (F : PrimeDivisor O → ℕ∞) :
    ∑ i ∈ s, (e i : ℕ∞) * F (P i) ≤ D.sum fun Q n => (n : ℕ∞) * F Q := by
  classical
  calc ∑ i ∈ s, (e i : ℕ∞) * F (P i) ≤ ∑ i ∈ s, (D (P i) : ℕ∞) * F (P i) :=
        Finset.sum_le_sum fun i hi => mul_le_mul' (Nat.cast_le.mpr (he i hi)) le_rfl
    _ = ∑ Q ∈ s.image P, (D Q : ℕ∞) * F Q :=
        (Finset.sum_image (f := fun Q => (D Q : ℕ∞) * F Q) hP).symm
    _ ≤ ∑ Q ∈ s.image P ∪ D.support, (D Q : ℕ∞) * F Q :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ Q ∈ D.support, (D Q : ℕ∞) * F Q := by
        refine (Finset.sum_subset Finset.subset_union_right fun Q _ hQ => ?_).symm
        rw [Finsupp.notMem_support_iff.mp hQ, Nat.cast_zero, zero_mul]
    _ = D.sum fun Q n => (n : ℕ∞) * F Q := rfl
theorem sum_mul_length_le_localNumber (hO : DivisorChain O) {g φ : O} (hg : g ≠ 0) (hφ : φ ≠ 0)
    (h : ∀ P : PrimeDivisor O, φ ∈ P.ideal → g ∉ P.ideal) {ι : Type*} (s : Finset ι)
    (P : ι → PrimeDivisor O) (hP : Set.InjOn P s) (e : ι → ℕ)
    (he : ∀ i ∈ s, (P i).valuation L (algebraMap O L g) ≤ exp (-(e i : ℤ))) :
    ∑ i ∈ s, (e i : ℕ∞) * Module.length O (O ⧸ ((P i).ideal ⊔ Ideal.span {φ})) ≤
      localNumber (zeroDivisor L (algebraMap O L φ)) g := by
  rw [LevelSurf.zeroDivisor_algebraMap L hφ, localNumber, sum_div_length_quotient_comm L hO hg hφ h]
  refine sum_le_divisor_sum s P hP (div L g) e (fun i hi => ?_)
    fun Q => Module.length O (O ⧸ (Q.ideal ⊔ Ideal.span {φ}))
  have h1 := he i hi
  rw [(P i).valuation_eq_exp_neg_ord L hg, exp_le_exp] at h1
  rw [div_apply]
  omega
end Ring
section Residue
variable {L F : Type*} [Field L] [Field F] (S : Specialization L F)
open Classical in
def resOf (x : L) : F :=
  if h : S.val x ≤ 1 then S.res ⟨x, (Valuation.mem_valuationSubring_iff _ _).mpr h⟩ else 0
theorem resOf_of_le {x : L} (h : S.val x ≤ 1) :
    resOf S x = S.res ⟨x, (Valuation.mem_valuationSubring_iff _ _).mpr h⟩ := by
  simp only [resOf, h, ↓reduceDIte]
theorem resOn_eq_resOf {O : Type*} [CommRing O] [Algebra O L]
    (hO : ∀ a : O, S.val (algebraMap O L a) ≤ 1) (a : O) :
    S.resOn hO a = resOf S (algebraMap O L a) :=
  (resOf_of_le S (hO a)).symm
theorem resOf_eq_zero_iff {x : L} (h : S.val x ≤ 1) : resOf S x = 0 ↔ S.val x < 1 := by
  rw [resOf_of_le S h, S.res_eq_zero_iff]
theorem resOf_ne_zero {x : L} (h : S.val x = 1) : resOf S x ≠ 0 := fun h0 =>
  absurd ((resOf_eq_zero_iff S h.le).mp h0) (by rw [h]; exact lt_irrefl _)
theorem resOf_one : resOf S 1 = 1 := by
  rw [resOf_of_le S (by rw [map_one])]
  exact map_one S.res
theorem resOf_mul {x y : L} (hx : S.val x ≤ 1) (hy : S.val y ≤ 1) :
    resOf S (x * y) = resOf S x * resOf S y := by
  rw [resOf_of_le S hx, resOf_of_le S hy, resOf_of_le S (by rw [map_mul]; exact mul_le_one' hx hy)]
  exact map_mul S.res ⟨x, (Valuation.mem_valuationSubring_iff _ _).mpr hx⟩
    ⟨y, (Valuation.mem_valuationSubring_iff _ _).mpr hy⟩
theorem resOf_pow {x : L} (hx : S.val x ≤ 1) (n : ℕ) : resOf S (x ^ n) = resOf S x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resOf_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, resOf_mul S (by rw [map_pow]; exact pow_le_one' hx n) hx, ih]
theorem resOf_inv {x : L} (hx : S.val x = 1) : resOf S x⁻¹ = (resOf S x)⁻¹ := by
  have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hi : S.val x⁻¹ = 1 := by rw [map_inv₀, hx, inv_one]
  have h := resOf_mul S hx.le hi.le
  rw [mul_inv_cancel₀ hx0, resOf_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm
theorem resOf_zpow {x : L} (hx : S.val x = 1) (n : ℤ) : resOf S (x ^ n) = resOf S x ^ n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast, resOf_pow S hx.le]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow,
      resOf_pow S (by rw [map_inv₀, hx, inv_one]), resOf_inv S hx]
theorem val_zpow_eq_one {x : L} (hx : S.val x = 1) (n : ℤ) : S.val (x ^ n) = 1 := by
  rw [map_zpow₀, hx, one_zpow]
theorem val_lmono_eq_one {x : Fin 3 → L} (hx : ∀ j, S.val (x j) = 1) (a : Fin 3 → ℤ) :
    S.val (lmono x a) = 1 := by
  rw [lmono, map_mul, map_mul, val_zpow_eq_one S (hx 0), val_zpow_eq_one S (hx 1),
    val_zpow_eq_one S (hx 2), one_mul, one_mul]
theorem resOf_lmono {x : Fin 3 → L} (hx : ∀ j, S.val (x j) = 1) (a : Fin 3 → ℤ) :
    resOf S (lmono x a) = lmono (fun j => resOf S (x j)) a := by
  have h0 := val_zpow_eq_one S (hx 0) (a 0)
  have h1 := val_zpow_eq_one S (hx 1) (a 1)
  have h2 := val_zpow_eq_one S (hx 2) (a 2)
  rw [lmono, lmono, resOf_mul S (by rw [map_mul, h0, h1, one_mul]) h2.le, resOf_mul S h0.le h1.le,
    resOf_zpow S (hx 0), resOf_zpow S (hx 1), resOf_zpow S (hx 2)]
end Residue
section Curve
variable {E : Type} [Field E] {G C : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime] [C.IsPrime]
  {S : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C)}
theorem resOf_BR (h : IsCurveOnSurface G C S) (A : MvPolynomial (Fin 3) E) :
    resOf S (RCN002.coordinateEvaluation E G A) = RCN002.coordinateEvaluation E C A := by
  rw [resOf_of_le S (LevelSurf.val_le_one h A)]
  exact (h A).2
theorem resOf_coordinate (h : IsCurveOnSurface G C S) (j : Fin 3) :
    resOf S (coordinate E G j) = coordinate E C j :=
  resOf_BR h (MvPolynomial.X j)
theorem prime_eq_of_val_eq {C' : Ideal (MvPolynomial (Fin 3) E)} [C'.IsPrime]
    {S' : Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E C')} (h : IsCurveOnSurface G C S)
    (h' : IsCurveOnSurface G C' S') (hval : S.val = S'.val) : C = C' := by
  ext A
  rw [← LevelSurf.val_lt_one_iff h, ← LevelSurf.val_lt_one_iff h', hval]
theorem order_resOf_localFunction (h : IsCurveOnSurface G C S)
    (hx : ∀ j, S.val (coordinate E G j) = 1) {A₁ : RCN002.CoordinateField E G} (hA : S.val A₁ = 1) (sR sY sZ : Bool)
    (W : FlagDegree) (μ : RCN026.Place_p19 E (RCN002.CoordinateField E C))
    (hμ : ∀ i, μ.val (lmono (coordinate E C) (chartExp sR sY sZ i)) ≤ 1) :
    RCN026.order_p19 E (RCN002.CoordinateField E C) μ
        (resOf S (A₁ / lmono (coordinate E G) (vertexExp sR sY sZ W))) =
      RCN026.order_p19 E (RCN002.CoordinateField E C) μ (resOf S A₁) + flagPole μ.val (coordinate E C) W := by
  have hxC : ∀ j, coordinate E C j ≠ 0 := fun j => by
    rw [← resOf_coordinate h j]
    exact resOf_ne_zero S (hx j)
  have hm := val_lmono_eq_one S hx (vertexExp sR sY sZ W)
  have hres : resOf S (A₁ / lmono (coordinate E G) (vertexExp sR sY sZ W)) =
      resOf S A₁ / lmono (coordinate E C) (vertexExp sR sY sZ W) := by
    rw [div_eq_mul_inv, resOf_mul S hA.le (by rw [map_inv₀, hm, inv_one]), resOf_inv S hm,
      resOf_lmono S hx, div_eq_mul_inv]
    simp only [resOf_coordinate h]
  have hv := flagPole_eq_vertex μ.val (coordinate E C) hxC sR sY sZ hμ W
  have ha : μ.val (resOf S A₁) ≠ 0 := (Valuation.ne_zero_iff _).mpr (resOf_ne_zero S hA)
  rw [hres, RCN026.order_p19, RCN026.order_p19, map_div₀, hv, log_div ha exp_ne_zero, log_exp]
  ring
theorem exists_sum_order_eq_zero [IsAlgClosed E] (sep : RCN341.SeparableLiteralCoordinate C) (x : RCN002.CoordinateField E C) (hx : x ≠ 0) :
    ∃ T₁ : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E C)), ∀ T, T₁ ⊆ T →
      ∑ v ∈ T, RCN026.order_p19 E (RCN002.CoordinateField E C) v x = 0 := by
  let _ := RCN006.polynomialBaseAlgebra E C sep.index
  let _ := RCN005.rationalBaseAlgebra E C sep.index sep.transcendental
  let _ := RCN006.polynomialBaseScalarTower E C sep.index
  let _ := RCN006.polynomialRationalScalarTower E C sep.index sep.transcendental
  let _ := RCN005.rationalBaseScalarTower E C sep.index sep.transcendental
  let _ : FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C) := sep.finite
  let _ : Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C) := sep.separable
  exact ⟨RCN026.placesFor_p19 E (RCN002.CoordinateField E C) x hx, fun T hT => sum_order_eq_zero E (RCN002.CoordinateField E C) x hx T hT⟩
theorem nonempty_separable [IsAlgClosed E] {p : ℕ} [CharP E p] (i : Fin 3)
    (hi : Transcendental E (coordinate E C i)) (F g T : MvPolynomial (Fin 3) E) (hF : F ≠ 0)
    (hg : Irreducible g) (hgF : g ∣ F) (hgC : g ∈ C) (hTC : T ∈ C) (hgT : ¬g ∣ T) (a b : FlagDegree)
    (hFa : RCN095.PolynomialInFlag a F) (hTb : RCN095.PolynomialInFlag b T) (hdeg : a.zOnly + a.yz + a.all < p)
    (hmix : 2 * (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) < p) :
    Nonempty (RCN341.SeparableLiteralCoordinate C) := by
  have hgdeg : ∀ j : Fin 3, g.degreeOf j ≤ a.zOnly + a.yz + a.all := fun j =>
    (RCN137.coordinate_degree_le_of_dvd j g F hgF hF).trans (RCN084.degreeOf_le_flag_total F a hFa j)
  have hTdeg : ∀ j : Fin 3, T.degreeOf j ≤ b.zOnly + b.yz + b.all := fun j => RCN084.degreeOf_le_flag_total T b hTb j
  have hprod : ∀ u v : Fin 3, T.degreeOf u * g.degreeOf v + g.degreeOf u * T.degreeOf v ≤
      2 * (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) := fun u v =>
    calc T.degreeOf u * g.degreeOf v + g.degreeOf u * T.degreeOf v
        ≤ (b.zOnly + b.yz + b.all) * (a.zOnly + a.yz + a.all) +
          (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) :=
          Nat.add_le_add (Nat.mul_le_mul (hTdeg u) (hgdeg v)) (Nat.mul_le_mul (hgdeg u) (hTdeg v))
      _ = 2 * (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) := by ring
  have hmixed : RCN001.coordinateMixedDegree E g T i < p := by
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [RCN001.coordinateMixedDegree_zero]
      exact (hprod 1 2).trans_lt hmix
    · rw [RCN001.coordinateMixedDegree_one]
      exact (hprod 0 2).trans_lt hmix
    · rw [RCN001.coordinateMixedDegree_two]
      exact (hprod 0 1).trans_lt hmix
  have h := RCN003.RH E C i hi p g T hg hgC hTC hgT (fun j => (hgdeg j).trans_lt hdeg) hmixed
  exact ⟨⟨i, hi, h.1, h.2⟩⟩
end Curve
section Surface
variable {E : Type} [Field E] {G : Ideal (MvPolynomial (Fin 3) E)} [G.IsPrime]
attribute [local instance] SurfacePoint.isNoetherianRing SurfacePoint.isIntegrallyClosed
  SurfacePoint.isFractionRing LevelComponent.isPrime
structure Setup (G : Ideal (MvPolynomial (Fin 3) E)) [G.IsPrime] (N p : ℕ)
    (g H : MvPolynomial (Fin 3) E) (f : RCN002.CoordinateField E G) (c : E) (A₁ : RCN002.CoordinateField E G) (W : FlagDegree) : Prop where
  algClosed : IsAlgClosed E
  charP : CharP E p
  noether : ∀ sR sY sZ, SurfaceNoether G sR sY sZ N
  char : 3 * N < p
  coord : ∀ j, coordinate E G j ≠ 0
  irreducible : Irreducible g
  span : G = Ideal.span {g}
  needs : Needs G g H f c A₁
  regular : ∀ q : SurfacePoint G, q.localFunction A₁ W ∈ q.ring
  sep : ∀ B : LevelComponent G f c, Nonempty (RCN341.SeparableLiteralCoordinate B.prime)
  closure : ∀ (B : LevelComponent G f c) (q : SurfacePoint G) (hq : q.On B.curve),
    Module.Finite (B.curve.image hq) (integralClosure (B.curve.image hq) (RCN002.CoordinateField E B.prime))
theorem chartCoord_mem (q : SurfacePoint G) (i : Fin 3) :
    lmono (coordinate E G) (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i) ∈ q.ring :=
  q.chartOf_spec.1 (isIntegral_algebraMap (R := surfaceChartRing G _ _ _)
    (x := ⟨_, Algebra.subset_adjoin ⟨i, rfl⟩⟩))
theorem order_nonneg {F : Type*} [Field F] [Algebra E F] (μ : RCN026.Place_p19 E F) {x : F}
    (h : μ.val x ≤ 1) : 0 ≤ RCN026.order_p19 E F μ x := by
  rw [RCN026.order_p19, neg_nonneg]
  by_cases h0 : μ.val x = 0
  · rw [h0, log_zero]
  · exact (log_le_iff_le_exp h0).mpr (by rw [exp_zero]; exact h)
variable {N p : ℕ} {g H : MvPolynomial (Fin 3) E} {f : RCN002.CoordinateField E G} {c : E} {A₁ : RCN002.CoordinateField E G}
  {W : FlagDegree}
theorem not_isMaximal (M : Setup G N p g H f c A₁ W) (q : SurfacePoint G)
    (P : PrimeDivisor q.ring) : ¬P.ideal.IsMaximal := by
  intro hmax
  have := M.charP
  have := q.isLocalRing
  obtain ⟨t, ht, htr, hone⟩ := (q.surfaceDivisor M.noether M.char P).nonconst
  obtain ⟨φ, hφ⟩ := q.residue
  have htq : t ∈ q.ring := q.chartOf_spec.1 (isIntegral_algebraMap
    (R := surfaceChartRing G _ _ _) (x := ⟨t, ht⟩))
  have hy : φ (⟨t, htq⟩ - algebraMap E q.ring (φ ⟨t, htq⟩)) = 0 := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hmem : (⟨t, htq⟩ - algebraMap E q.ring (φ ⟨t, htq⟩) : q.ring) ∈ P.ideal := by
    rw [IsLocalRing.eq_maximalIdeal hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (hφ _).mp hy
  have hlt := (P.valuation_lt_one_iff (RCN002.CoordinateField E G) _).mpr hmem
  have hne : t - algebraMap E (RCN002.CoordinateField E G) (φ ⟨t, htq⟩) ≠ 0 := fun h0 =>
    htr (sub_eq_zero.mp h0 ▸ isAlgebraic_algebraMap _)
  have h1 := hone (t - algebraMap E (RCN002.CoordinateField E G) (φ ⟨t, htq⟩))
    (sub_mem (IntermediateField.subset_adjoin E {t} rfl) (IntermediateField.algebraMap_mem _ _)) hne
  rw [show algebraMap q.ring (RCN002.CoordinateField E G) (⟨t, htq⟩ - algebraMap E q.ring (φ ⟨t, htq⟩)) =
    t - algebraMap E (RCN002.CoordinateField E G) (φ ⟨t, htq⟩) from rfl, h1] at hlt
  exact lt_irrefl _ hlt
theorem exists_transcendental (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c) :
    ∃ j, Transcendental E (coordinate E B.prime j) := by
  have := M.algClosed
  exact B.exists_transcendental
theorem units_of_needs [IsAlgClosed E] (hc : ∀ j, coordinate E G j ≠ 0) (hneeds : Needs G g H f c A₁)
    (B : LevelComponent G f c) :
    (∀ j, B.curve.val (coordinate E G j) = 1) ∧ B.curve.val (RCN002.coordinateEvaluation E G H) = 1 ∧
      B.curve.val A₁ = 1 := by
  have hle : ∀ i, B.curve.val (lmono (coordinate E G) (chartExp false false false i)) ≤ 1 := by
    intro i
    fin_cases i <;> simp [lmono, chartExp] <;> exact LevelSurf.val_le_one B.isCurve (MvPolynomial.X _)
  have hsd := B.isCurve.surfaceDivisor hc B.exists_transcendental false false false hle
  have h := hneeds.unit B.curve.val ⟨_, _, _, hsd⟩ (by rw [B.curve_val]; exact B.val_lt_one)
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩
theorem units (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c) :
    (∀ j, B.curve.val (coordinate E G j) = 1) ∧ B.curve.val (RCN002.coordinateEvaluation E G H) = 1 ∧
      B.curve.val A₁ = 1 := by
  have := M.algClosed
  exact units_of_needs M.coord M.needs B
theorem BR_levelCut {Gs Q A : MvPolynomial (Fin 3) E} (hH : RCN002.coordinateEvaluation E G H ≠ 0) (c : E) :
    RCN002.coordinateEvaluation E G (RCN207.movingEquation H Gs Q A c) =
      -(RCN002.coordinateEvaluation E G H * (RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c)) := by
  rw [RCN207.movingEquation, RCN208.movingValue, map_sub, map_mul, map_mul, map_sub,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  field_simp
  ring
theorem nonempty_separable_levelComponent [IsAlgClosed E] [CharP E p] (hG : G = Ideal.span {g})
    (hg : Irreducible g) {Gs Q A : MvPolynomial (Fin 3) E} (hH : RCN002.coordinateEvaluation E G H ≠ 0)
    (hne : RCN208.movingValue G H Gs Q A ≠ algebraMap E (RCN002.CoordinateField E G) c)
    (F : MvPolynomial (Fin 3) E) (hF : F ≠ 0) (hgF : g ∣ F) (a b : FlagDegree) (hFa : RCN095.PolynomialInFlag a F)
    (hTb : RCN095.PolynomialInFlag b (RCN207.movingEquation H Gs Q A c)) (hdeg : a.zOnly + a.yz + a.all < p)
    (hmix : 2 * (a.zOnly + a.yz + a.all) * (b.zOnly + b.yz + b.all) < p)
    (B : LevelComponent G (RCN208.movingValue G H Gs Q A) c) : Nonempty (RCN341.SeparableLiteralCoordinate B.prime) := by
  obtain ⟨i, hi⟩ := B.exists_transcendental
  have hBT := BR_levelCut (Gs := Gs) (Q := Q) (A := A) hH c
  have hTC : RCN207.movingEquation H Gs Q A c ∈ B.prime := by
    rw [← LevelSurf.val_lt_one_iff B.isCurve, hBT, Valuation.map_neg, map_mul, B.curve_val]
    calc B.val (RCN002.coordinateEvaluation E G H) * B.val (RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c)
        ≤ 1 * B.val (RCN208.movingValue G H Gs Q A - algebraMap E (RCN002.CoordinateField E G) c) :=
          mul_le_mul' (B.curve_val ▸ LevelSurf.val_le_one B.isCurve H) le_rfl
      _ < 1 := by
          rw [one_mul]
          exact B.val_lt_one
  have hgT : ¬g ∣ RCN207.movingEquation H Gs Q A c := fun hdvd => by
    have h0 : RCN002.coordinateEvaluation E G (RCN207.movingEquation H Gs Q A c) = 0 :=
      (LevelSurf.BR_eq_zero_iff G _).mpr (hG ▸ Ideal.mem_span_singleton.mpr hdvd)
    rw [hBT, neg_eq_zero, mul_eq_zero] at h0
    exact h0.elim hH (sub_ne_zero.mpr hne)
  exact nonempty_separable i hi F g _ hF hg hgF
    (B.isCurve.le (hG ▸ Ideal.mem_span_singleton_self g)) hTC hgT a b hFa hTb hdeg hmix
theorem exists_component (M : Setup G N p g H f c A₁ W) (q : SurfacePoint G)
    (P : PrimeDivisor q.ring) (hP : P.valuation (RCN002.CoordinateField E G) (f - algebraMap E (RCN002.CoordinateField E G) c) < 1) :
    ∃ B : LevelComponent G f c, B.val = P.valuation (RCN002.CoordinateField E G) := by
  have := M.charP
  have hsd := q.surfaceDivisor M.noether M.char P
  obtain ⟨hx, hd, -, -⟩ := M.needs.unit _ ⟨_, _, _, hsd⟩ hP
  obtain ⟨C, hC, S, hS, hval, hC2, -⟩ := hsd.exists_isCurveOnSurface M.coord (fun j => (hx j).le) g
    M.irreducible M.span 1 hd
  exact ⟨⟨P.valuation (RCN002.CoordinateField E G), hP, C, hC, S, hS, hval, hC2⟩, rfl⟩
theorem finite_component (M : Setup G N p g H f c A₁ W) : Finite (LevelComponent G f c) := by
  have := M.charP
  have hfin := finite_surfaceDivisor_ne_one M.noether M.char (f - algebraMap E (RCN002.CoordinateField E G) c)
    (sub_ne_zero.mpr M.needs.ne)
  have := hfin.to_subtype
  have hle : ∀ B : LevelComponent G f c,
      ∀ i, B.curve.val (lmono (coordinate E G) (chartExp false false false i)) ≤ 1 := by
    intro B i
    fin_cases i <;> simp [lmono, chartExp] <;> exact LevelSurf.val_le_one B.isCurve (MvPolynomial.X _)
  refine Finite.of_injective (fun B : LevelComponent G f c =>
    (⟨B.val, ⟨_, _, _, B.curve_val ▸ B.isCurve.surfaceDivisor M.coord (exists_transcendental M B)
      false false false (hle B)⟩, B.val_lt_one.ne⟩ :
      {nu : Valuation (RCN002.CoordinateField E G) ℤᵐ⁰ | (∃ sR sY sZ, SurfaceDivisor G sR sY sZ nu) ∧
        nu (f - algebraMap E (RCN002.CoordinateField E G) c) ≠ 1})) ?_
  intro B B' h
  exact Subtype.ext (Subtype.mk.inj h)
theorem exists_prime (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (q : SurfacePoint G) (hq : q.On B.curve) :
    ∃ P : PrimeDivisor q.ring, (∀ x : q.ring, x ∈ P.ideal ↔ B.curve.val (x : RCN002.CoordinateField E G) < 1) ∧
      P.valuation (RCN002.CoordinateField E G) = B.curve.val :=
  B.isCurve.exists_primeDivisor M.coord (exists_transcendental M B) q hq
theorem finite_places (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (q : SurfacePoint G) (hq : q.On B.curve) : (B.curve.placesOn E hq).Finite := by
  have := M.algClosed
  obtain ⟨P, hP, -⟩ := exists_prime M B q hq
  exact PlaceSurf.surfacePoint_finite_places q B.curve hq (M.closure B q hq) P.ideal hP
    (not_isMaximal M q P)
open Classical in
def pointSum (B : LevelComponent G f c) (q : SurfacePoint G) (x : RCN002.CoordinateField E G) : ℕ :=
  if hq : q.On B.curve then
    ∑ᶠ μ ∈ B.curve.placesOn E hq, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve x)).toNat
  else 0
theorem pointSum_of_on (B : LevelComponent G f c) (q : SurfacePoint G) (x : RCN002.CoordinateField E G)
    (hq : q.On B.curve) : pointSum B q x =
      ∑ᶠ μ ∈ B.curve.placesOn E hq, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve x)).toNat :=
  dite_eq_left hq
theorem pointSum_of_not_on (B : LevelComponent G f c) (q : SurfacePoint G) (x : RCN002.CoordinateField E G)
    (hq : ¬q.On B.curve) : pointSum B q x = 0 :=
  dite_eq_right hq
theorem order_at_place (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (q : SurfacePoint G) (hq : q.On B.curve) (μ : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime))
    (hμ : μ ∈ B.curve.placesOn E hq) :
    RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve (q.localFunction A₁ W)) =
      RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
        flagPole μ.val (coordinate E B.prime) W := by
  obtain ⟨hx, -, hA⟩ := units M B
  refine order_resOf_localFunction B.isCurve hx hA _ _ _ W μ fun i => ?_
  have h := hμ _ ⟨⟨_, chartCoord_mem q i⟩, rfl⟩
  have h1 : B.curve.resOn hq ⟨_, chartCoord_mem q i⟩ = resOf B.curve
      (lmono (coordinate E G) (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i)) :=
    resOn_eq_resOf B.curve hq ⟨_, chartCoord_mem q i⟩
  have h2 := resOf_lmono B.curve hx (chartExp q.chartOf.1 q.chartOf.2.1 q.chartOf.2.2 i)
  simp only [resOf_coordinate B.isCurve] at h2
  rwa [h1, h2] at h
theorem order_add_flagPole_nonneg (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (μ : RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)) :
    0 ≤ RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
      flagPole μ.val (coordinate E B.prime) W := by
  have := M.charP
  have := M.algClosed
  obtain ⟨q, hq, hμ⟩ := B.isCurve.exists_point M.noether M.char M.coord
    (exists_transcendental M B) μ
  rw [← order_at_place M B q hq μ hμ]
  refine order_nonneg μ ?_
  have h := hμ _ ⟨⟨_, M.regular q⟩, rfl⟩
  have h1 : B.curve.resOn hq ⟨_, M.regular q⟩ = resOf B.curve (q.localFunction A₁ W) :=
    resOn_eq_resOf B.curve hq ⟨_, M.regular q⟩
  rwa [h1] at h
theorem sum_pointSum_le (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (Q₀ : Finset (SurfacePoint G)) :
    ∃ T : Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)),
      ((∑ q ∈ Q₀, pointSum B q (q.localFunction A₁ W) : ℕ) : ℤ) ≤
        ∑ μ ∈ T, flagPole μ.val (coordinate E B.prime) W := by
  classical
  have := M.algClosed
  obtain ⟨-, -, hA⟩ := units M B
  obtain ⟨T₁, hT₁⟩ := exists_sum_order_eq_zero (M.sep B).some (resOf B.curve A₁)
    (resOf_ne_zero B.curve hA)
  let U : SurfacePoint G → Finset (RCN026.Place_p19 E (RCN002.CoordinateField E B.prime)) := fun q =>
    if hq : q.On B.curve then (finite_places M B q hq).toFinset else ∅
  have hU : ∀ (q : SurfacePoint G) (hq : q.On B.curve), U q = (finite_places M B q hq).toFinset :=
    fun q hq => dite_eq_left hq
  have hU0 : ∀ q : SurfacePoint G, ¬q.On B.curve → U q = ∅ := fun q hq => dite_eq_right hq
  have hpoint : ∀ q, ((pointSum B q (q.localFunction A₁ W) : ℕ) : ℤ) =
      ∑ μ ∈ U q, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
        flagPole μ.val (coordinate E B.prime) W) := by
    intro q
    by_cases hq : q.On B.curve
    · rw [pointSum_of_on B q _ hq, hU q hq,
        finsum_mem_eq_finite_toFinset_sum _ (finite_places M B q hq), Nat.cast_sum]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      rw [order_at_place M B q hq μ ((finite_places M B q hq).mem_toFinset.mp hμ)]
      exact Int.toNat_of_nonneg (order_add_flagPole_nonneg M B μ)
    · rw [pointSum_of_not_on B q _ hq, hU0 q hq, Nat.cast_zero, Finset.sum_empty]
  have hdisj : (Q₀ : Set (SurfacePoint G)).PairwiseDisjoint U := by
    intro q _ q' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro μ hμ hμ'
    by_cases hq : q.On B.curve
    · by_cases hq' : q'.On B.curve
      · rw [hU q hq, Set.Finite.mem_toFinset] at hμ
        rw [hU q' hq', Set.Finite.mem_toFinset] at hμ'
        exact hne (SurfacePoint.eq_of_place M.coord B.curve q q' hq hq' μ hμ hμ')
      · rw [hU0 q' hq'] at hμ'
        exact absurd hμ' (Finset.notMem_empty μ)
    · rw [hU0 q hq] at hμ
      exact absurd hμ (Finset.notMem_empty μ)
  refine ⟨Q₀.biUnion U ∪ T₁, ?_⟩
  calc ((∑ q ∈ Q₀, pointSum B q (q.localFunction A₁ W) : ℕ) : ℤ)
      = ∑ q ∈ Q₀, ∑ μ ∈ U q, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
          flagPole μ.val (coordinate E B.prime) W) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun q _ => hpoint q
    _ = ∑ μ ∈ Q₀.biUnion U, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
          flagPole μ.val (coordinate E B.prime) W) := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ μ ∈ Q₀.biUnion U ∪ T₁, (RCN026.order_p19 E (RCN002.CoordinateField E B.prime) μ (resOf B.curve A₁) +
          flagPole μ.val (coordinate E B.prime) W) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun μ _ _ =>
          order_add_flagPole_nonneg M B μ
    _ = ∑ μ ∈ Q₀.biUnion U ∪ T₁, flagPole μ.val (coordinate E B.prime) W := by
        rw [Finset.sum_add_distrib, hT₁ _ Finset.subset_union_right, zero_add]
theorem mult_pos (hne : f ≠ algebraMap E (RCN002.CoordinateField E G) c) (B : LevelComponent G f c) : 0 < B.mult := by
  have h0 : B.val (f - algebraMap E (RCN002.CoordinateField E G) c) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  have h1 := (log_lt_iff_lt_exp h0).mpr (by rw [exp_zero]; exact B.val_lt_one)
  rw [LevelComponent.mult]
  omega
theorem level_apply (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c) (q : SurfacePoint G)
    (P : PrimeDivisor q.ring) (hP : P.valuation (RCN002.CoordinateField E G) = B.curve.val) :
    q.level f c P = B.mult := by
  rw [SurfacePoint.level, levelDivisor, zeroDivisor_apply _ (sub_ne_zero.mpr M.needs.ne), hP,
    B.curve_val]
  rfl
theorem val_localFunction (M : Setup G N p g H f c A₁ W) (B : LevelComponent G f c)
    (q : SurfacePoint G) : B.curve.val (q.localFunction A₁ W) = 1 := by
  obtain ⟨hx, -, hA⟩ := units M B
  rw [SurfacePoint.localFunction, map_div₀, hA, val_lmono_eq_one B.curve hx, div_one]
theorem val_lt_one_of_level_ne_zero (M : Setup G N p g H f c A₁ W) (q : SurfacePoint G)
    (P : PrimeDivisor q.ring) (hP : q.level f c P ≠ 0) :
    P.valuation (RCN002.CoordinateField E G) (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 := by
  rw [SurfacePoint.level, levelDivisor, zeroDivisor_apply _ (sub_ne_zero.mpr M.needs.ne)] at hP
  by_contra hge
  refine hP (Int.toNat_eq_zero.mpr (neg_nonpos.mpr ?_))
  exact le_log_of_exp_le (by rw [exp_zero]; exact not_lt.mp hge)
theorem localNumber_eq (M : Setup G N p g H f c A₁ W) (q : SurfacePoint G)
    (s : Finset (LevelComponent G f c)) (hs : ∀ B : LevelComponent G f c, q.On B.curve → B ∈ s) :
    localNumber (q.level f c) (⟨q.localFunction A₁ W, M.regular q⟩ : q.ring) =
      ((∑ B ∈ s, B.mult * pointSum B q (q.localFunction A₁ W) : ℕ) : ℕ∞) := by
  classical
  have := M.algClosed
  have hsub : ∑ B ∈ s, B.mult * pointSum B q (q.localFunction A₁ W) =
      ∑ B ∈ s.filter (fun B => q.On B.curve), B.mult * pointSum B q (q.localFunction A₁ W) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun B hB hnot => ?_).symm
    have hq : ¬q.On B.curve := fun hq => hnot (Finset.mem_filter.mpr ⟨hB, hq⟩)
    rw [pointSum_of_not_on B q _ hq, mul_zero]
  rw [hsub, Nat.cast_sum, localNumber, Finsupp.sum]
  symm
  refine Finset.sum_bij
    (fun B hB => (exists_prime M B q (Finset.mem_filter.mp hB).2).choose) ?_ ?_ ?_ ?_
  · intro B hB
    have hq := (Finset.mem_filter.mp hB).2
    rw [Finsupp.mem_support_iff, level_apply M B q _ (exists_prime M B q hq).choose_spec.2]
    exact (mult_pos M.needs.ne B).ne'
  · intro B hB B' hB' h
    have hq := (Finset.mem_filter.mp hB).2
    have hq' := (Finset.mem_filter.mp hB').2
    have h1 := (exists_prime M B q hq).choose_spec.2
    have h2 := (exists_prime M B' q hq').choose_spec.2
    rw [h, h2, B.curve_val, B'.curve_val] at h1
    exact Subtype.ext h1.symm
  · intro P hP
    obtain ⟨B, hB⟩ := exists_component M q P
      (val_lt_one_of_level_ne_zero M q P (Finsupp.mem_support_iff.mp hP))
    have hq : q.On B.curve := fun a => by
      rw [B.curve_val, hB]
      exact P.valuation_le_one (RCN002.CoordinateField E G) a
    refine ⟨B, Finset.mem_filter.mpr ⟨hs B hq, hq⟩, PrimeDivisor.ext_ideal (Ideal.ext fun x => ?_)⟩
    rw [(exists_prime M B q hq).choose_spec.1 x, B.curve_val, hB]
    exact P.valuation_lt_one_iff (RCN002.CoordinateField E G) x
  · intro B hB
    have hq := (Finset.mem_filter.mp hB).2
    obtain ⟨hP, hval⟩ := (exists_prime M B q hq).choose_spec
    have hxP : (⟨q.localFunction A₁ W, M.regular q⟩ : q.ring) ∉
        (exists_prime M B q hq).choose.ideal := fun hmem => by
      have h1 : B.curve.val (q.localFunction A₁ W) < 1 := (hP _).mp hmem
      rw [val_localFunction M B q] at h1
      exact lt_irrefl _ h1
    have hres : B.curve.resOn hq ⟨q.localFunction A₁ W, M.regular q⟩ =
        resOf B.curve (q.localFunction A₁ W) := resOn_eq_resOf B.curve hq ⟨_, M.regular q⟩
    rw [level_apply M B q _ hval, Nat.cast_mul,
      PlaceSurf.surfacePoint_length_eq_zeros q B.curve hq (M.closure B q hq) _ hP _ hxP, hres,
      pointSum_of_on B q _ hq]
theorem levelNumber_eq (M : Setup G N p g H f c A₁ W) (q : SurfacePoint G)
    (s : Finset (LevelComponent G f c)) (hs : ∀ B : LevelComponent G f c, q.On B.curve → B ∈ s) :
    q.levelNumber f c (q.localFunction A₁ W) =
      ∑ B ∈ s, B.mult * pointSum B q (q.localFunction A₁ W) := by
  simp only [SurfacePoint.levelNumber, M.regular q, ↓reduceDIte]
  rw [localNumber_eq M q s hs, ENat.toNat_natCast]
variable {ι : Type*} {C : ι → Ideal (MvPolynomial (Fin 3) E)} [∀ i, (C i).IsPrime]
theorem sum_order_le_levelNumber (M : Setup G N p g H f c A₁ W) (live : Finset ι)
    (S : ∀ i, Specialization (RCN002.CoordinateField E G) (RCN002.CoordinateField E (C i)))
    (hS : ∀ i ∈ live, IsCurveOnSurface G (C i) (S i))
    (htr : ∀ i ∈ live, ∃ j, Transcendental E (coordinate E (C i) j))
    (hinj : ∀ i ∈ live, ∀ i' ∈ live, C i = C i' → i = i')
    (hlive : ∀ i ∈ live, (S i).val (f - algebraMap E (RCN002.CoordinateField E G) c) = 1)
    (e : ι → ℕ) (hord : ∀ i ∈ live, (S i).val A₁ ≤ exp (-(e i : ℤ)))
    (hcl : ∀ i ∈ live, ∀ (q : SurfacePoint G) (hq : q.On (S i)), f ∈ q.ring → q.level f c ≠ 0 →
      Module.Finite ((S i).image hq) (integralClosure ((S i).image hq) (RCN002.CoordinateField E (C i))))
    (q : SurfacePoint G) (hf : f ∈ q.ring) :
    ∑ i ∈ live, e i * q.order (S i) f c 1 ≤ q.levelNumber f c (q.localFunction A₁ W) := by
  classical
  have := M.algClosed
  by_cases hlev : q.level f c = 0
  · rw [Exch.levelNumber_eq_zero q f c _ hlev]
    exact (Finset.sum_eq_zero fun i _ => by
      rw [Exch.order_eq_zero q (S i) f c 1 hlev, mul_zero]).le
  have := finite_component M
  have := Fintype.ofFinite (LevelComponent G f c)
  have hφ0 : (⟨f, hf⟩ - algebraMap E q.ring c : q.ring) ≠ 0 := fun h0 =>
    sub_ne_zero.mpr M.needs.ne (congrArg (algebraMap q.ring (RCN002.CoordinateField E G)) h0)
  have hcommon : ∀ P : PrimeDivisor q.ring, (⟨f, hf⟩ - algebraMap E q.ring c : q.ring) ∈ P.ideal →
      (⟨q.localFunction A₁ W, M.regular q⟩ : q.ring) ∉ P.ideal := by
    intro P hP hx
    obtain ⟨B, hB⟩ := exists_component M q P ((P.valuation_lt_one_iff (RCN002.CoordinateField E G) _).mpr hP)
    have h1 : B.curve.val (q.localFunction A₁ W) < 1 := by
      rw [B.curve_val, hB]
      exact (P.valuation_lt_one_iff (RCN002.CoordinateField E G) _).mpr hx
    rw [val_localFunction M B q] at h1
    exact lt_irrefl _ h1
  have hx0 : (⟨q.localFunction A₁ W, M.regular q⟩ : q.ring) ≠ 0 := by
    obtain ⟨P, hP⟩ : ∃ P, q.level f c P ≠ 0 := by
      by_contra h
      exact hlev (Finsupp.ext fun P => not_not.mp fun hP => h ⟨P, hP⟩)
    intro h0
    refine hcommon P ((P.valuation_lt_one_iff (RCN002.CoordinateField E G) _).mp
      (val_lt_one_of_level_ne_zero M q P hP)) ?_
    rw [h0]
    exact P.ideal.zero_mem
  have hprime : ∀ i : {i // i ∈ live.filter fun i => q.On (S i)},
      ∃ P : PrimeDivisor q.ring, (∀ x : q.ring, x ∈ P.ideal ↔ (S i.1).val (x : RCN002.CoordinateField E G) < 1) ∧
        P.valuation (RCN002.CoordinateField E G) = (S i.1).val := fun i =>
    (hS i.1 (Finset.mem_filter.mp i.2).1).exists_primeDivisor M.coord
      (htr i.1 (Finset.mem_filter.mp i.2).1) q (Finset.mem_filter.mp i.2).2
  have hterm : ∀ i : {i // i ∈ live.filter fun i => q.On (S i)},
      Module.length q.ring (q.ring ⧸ ((hprime i).choose.ideal ⊔
        Ideal.span {(⟨f, hf⟩ - algebraMap E q.ring c : q.ring)})) =
        ((q.order (S i.1) f c 1 : ℕ) : ℕ∞) := by
    intro i
    have hi := (Finset.mem_filter.mp i.2).1
    have hq := (Finset.mem_filter.mp i.2).2
    have hφP : (⟨f, hf⟩ - algebraMap E q.ring c : q.ring) ∉ (hprime i).choose.ideal := fun hmem => by
      have h1 : (S i.1).val (f - algebraMap E (RCN002.CoordinateField E G) c) < 1 := ((hprime i).choose_spec.1 _).mp hmem
      rw [hlive i.1 hi] at h1
      exact lt_irrefl _ h1
    rw [PlaceSurf.surfacePoint_length_eq_zeros q (S i.1) hq (hcl i.1 hi q hq hf hlev) _
      (hprime i).choose_spec.1 _ hφP]
    rw [SurfacePoint.order, dite_eq_left hq, Specialization.levelOrder]
    refine congrArg _ (finsum_mem_congr rfl fun μ hμ => ?_)
    have h1 := (S i.1).leastOrder_levelIdeal hq f c (⟨f, hf⟩ - algebraMap E q.ring c) rfl
      (hlive i.1 hi) μ hμ 1
    rw [Nat.cast_one, one_mul] at h1
    rw [← h1, Int.toNat_natCast]
  have hmain := sum_mul_length_le_localNumber (RCN002.CoordinateField E G) q.divisorChain hx0 hφ0 hcommon
    (live.filter fun i => q.On (S i)).attach (fun i => (hprime i).choose)
    (fun i _ i' _ h => Subtype.ext (hinj i.1 (Finset.mem_filter.mp i.2).1 i'.1
      (Finset.mem_filter.mp i'.2).1 (prime_eq_of_val_eq (hS i.1 (Finset.mem_filter.mp i.2).1)
        (hS i'.1 (Finset.mem_filter.mp i'.2).1) (by
          rw [← (hprime i).choose_spec.2, ← (hprime i').choose_spec.2]
          exact congrArg _ h))))
    (fun i => e i.1) (fun i _ => by
      have hi := (Finset.mem_filter.mp i.2).1
      have hq := (Finset.mem_filter.mp i.2).2
      rw [(hprime i).choose_spec.2]
      have h1 : (S i.1).val (q.localFunction A₁ W) = (S i.1).val A₁ := by
        rw [SurfacePoint.localFunction, map_div₀, Exch.val_vertex_eq_one M.coord q (S i.1) hq
          (fun j => LevelSurf.val_le_one (hS i.1 hi) (MvPolynomial.X j)) W, div_one]
      exact h1 ▸ hord i.1 hi)
  have hlevel : zeroDivisor (RCN002.CoordinateField E G) (algebraMap q.ring (RCN002.CoordinateField E G)
      (⟨f, hf⟩ - algebraMap E q.ring c : q.ring)) = q.level f c := rfl
  rw [hlevel, localNumber_eq M q Finset.univ fun B _ => Finset.mem_univ B] at hmain
  simp only [hterm] at hmain
  rw [levelNumber_eq M q Finset.univ fun B _ => Finset.mem_univ B]
  have hsum : ∑ i ∈ live, e i * q.order (S i) f c 1 =
      ∑ i ∈ (live.filter fun i => q.On (S i)).attach, e i.1 * q.order (S i.1) f c 1 := by
    rw [Finset.sum_attach (live.filter fun i => q.On (S i)) fun i => e i * q.order (S i) f c 1]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hnot => ?_).symm
    have hq : ¬q.On (S i) := fun hq => hnot (Finset.mem_filter.mpr ⟨hi, hq⟩)
    rw [SurfacePoint.order, dite_eq_right hq, mul_zero]
  rw [hsum]
  exact_mod_cast hmain
end Surface
end
end LevelCount
end FormalR
end SubmissionLower
end ProximityPrize
end
