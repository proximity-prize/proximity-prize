import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.ENat.BigOperators
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.NatCard
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.KoalaTwoSectionCount -- serialize candidate build

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.Rect

open MvPolynomial
open scoped BigOperators Pointwise

abbrev Exp := Fin 4 →₀ ℕ
abbrev Ring (F : Type*) [Field F] := MvPolynomial (Fin 4) F

structure Box where
  base : ℕ
  velocity : ℕ
  seed₀ : ℕ
  seed₁ : ℕ

def Box.add (d k : Box) : Box :=
  ⟨d.base+k.base, d.velocity+k.velocity, d.seed₀+k.seed₀, d.seed₁+k.seed₁⟩

def Box.pad (d : Box) (n : ℕ) : Box := {d with base := d.base+n}

def Box.support (d : Box) : Set Exp := {m |
  m 1 ≤ d.velocity ∧ m 0 + 2*m 1 ≤ d.base + 2*d.velocity ∧
  m 2 ≤ d.seed₀ ∧ m 3 ≤ d.seed₁}

abbrev Slots (d : Box) :=
  ((i : Fin (d.velocity+1)) × Fin (d.base+2*(d.velocity-i.val)+1)) ×
    Fin (d.seed₀+1) × Fin (d.seed₁+1)

noncomputable def slots (d : Box) : d.support ≃ Slots d where
  toFun m :=
    let h := m.property
    ⟨⟨⟨m.val 1, by rcases h with ⟨h, _⟩; omega⟩,
      ⟨m.val 0, by
        change m.val 0 < d.base + 2*(d.velocity - m.val 1)+1
        rcases h with ⟨h, h', _⟩
        omega⟩⟩,
      ⟨m.val 2, by rcases h with ⟨_, _, h, _⟩; omega⟩,
      ⟨m.val 3, by rcases h with ⟨_, _, _, h⟩; omega⟩⟩
  invFun m :=
    let ⟨⟨i,j⟩,a,b⟩ := m
    ⟨Finsupp.equivFunOnFinite.symm ![j.val,i.val,a.val,b.val], by
      have hi := i.isLt
      have hj := j.isLt
      have ha := a.isLt
      have hb := b.isLt
      change i.val ≤ _ ∧ j.val+2*i.val ≤ _ ∧ a.val ≤ _ ∧ b.val ≤ _
      omega⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv m := by rcases m with ⟨⟨i,j⟩,a,b⟩; rfl

private theorem jet_count (h t : ℕ) :
    (∑ i : Fin (t+1), (h+2*(t-i.val)+1)) = (t+1)*(h+t+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
    rw [ih]
    ring

noncomputable def space (F : Type*) [Field F] (d : Box) : Submodule F (Ring F) :=
  restrictSupport F d.support

noncomputable instance finite_support (d : Box) : Fintype d.support :=
  Fintype.ofEquiv (Slots d) (slots d).symm

instance space_finite (F : Type*) [Field F] (d : Box) : Module.Finite F (space F d) :=
  Module.Finite.of_basis (basisRestrictSupport F d.support)

theorem ambient_rank (F : Type*) [Field F] (d : Box) :
    Module.finrank F (space F d) =
      (d.velocity+1)*(d.base+d.velocity+1)*(d.seed₀+1)*(d.seed₁+1) := by
  unfold space
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport F d.support),
    Nat.card_congr (slots d)]
  simp only [Slots, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fin, jet_count]
  ring

noncomputable def piece {F : Type*} [Field F] (I : Ideal (Ring F)) (d : Box) :
    Submodule F (Ring F ⧸ I) := (space F d).map (Ideal.Quotient.mkₐ F I).toLinearMap

instance piece_finite {F : Type*} [Field F] (I : Ideal (Ring F)) (d : Box) :
    Module.Finite F (piece I d) := by unfold piece; infer_instance

structure Section {F : Type*} [Field F] (I : Ideal (Ring F)) (d : Box) where
  order : ℕ
  finite : Ring F
  inverse : Ring F
  finite_bound : finite ∈ space F (d.pad order)
  inverse_bound : inverse ∈ space F (d.pad order)
  glue : X (0 : Fin 4)^order * finite - inverse ∈ I

theorem shift_mem {F : Type*} [Field F] (m : Exp) (c : F) (f : Ring F)
    (d k : Box) (hf : f ∈ space F d) (hm : ∀ n ∈ d.support, m+n ∈ k.support) :
    monomial m c * f ∈ space F k := by
  classical
  intro a ha
  obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp (support_mul _ _ ha)
  have h : i = m := Finset.mem_singleton.mp (support_monomial_subset hi)
  subst i
  exact hm _ (hf hj)

/-- The finite and inverse charts supply multiplication by a relative section
    with the claimed exact seed bidegrees even when both chart representatives
    have extra ordinate degree. -/
theorem mul_monomial {F : Type*} [Field F] {I : Ideal (Ring F)} {d k : Box}
    (S : Section I k) (h : 2*S.order ≤ d.base) (m : Exp) (hm : m ∈ d.support) (c : F) :
    Ideal.Quotient.mk I S.finite * Ideal.Quotient.mk I (monomial m c) ∈ piece I (d.add k) := by
  rcases hm with ⟨hv, hy, hu, hw⟩
  by_cases hl : m 0 + 2*m 1 + S.order ≤ d.base + 2*d.velocity
  · apply Submodule.mem_map.mpr
    refine ⟨monomial m c*S.finite, shift_mem _ _ _ _ _ S.finite_bound ?_, ?_⟩
    · intro n hn
      rcases hn with ⟨h1, h2, h3, h4⟩
      dsimp [Box.pad] at h1 h2 h3 h4
      change (m+n) 1 ≤ _ ∧ _ ∧ _ ∧ _
      simp only [Finsupp.add_apply, Box.add]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · change Ideal.Quotient.mk I (_ * _) = _
      rw [map_mul, mul_comm]
  · have hpad : S.order ≤ m 0 := by omega
    let q := m - Finsupp.single (0 : Fin 4) S.order
    have he : q + Finsupp.single (0 : Fin 4) S.order = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hpad)
    have coords (i : Fin 4) : q i + (Finsupp.single (0 : Fin 4) S.order) i = m i :=
      DFunLike.congr_fun he i
    have q0 : q 0 + S.order = m 0 := by simpa using coords 0
    have q1 : q 1 = m 1 := by simpa using coords 1
    have q2 : q 2 = m 2 := by simpa using coords 2
    have q3 : q 3 = m 3 := by simpa using coords 3
    apply Submodule.mem_map.mpr
    refine ⟨monomial q c*S.inverse, shift_mem _ _ _ _ _ S.inverse_bound ?_, ?_⟩
    · intro n hn
      rcases hn with ⟨h1, h2, h3, h4⟩
      dsimp [Box.pad] at h1 h2 h3 h4
      change (q+n) 1 ≤ _ ∧ _ ∧ _ ∧ _
      simp only [Finsupp.add_apply, Box.add]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · have hp : (monomial m c : Ring F) = monomial q c * X (0 : Fin 4)^S.order := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, he, mul_one]
      have hg := Ideal.Quotient.eq_zero_iff_mem.mpr S.glue
      simp only [map_sub, map_mul, sub_eq_zero] at hg
      change Ideal.Quotient.mk I (_ * _) = _
      rw [map_mul, ← hg, hp, map_mul]
      ac_rfl

theorem mul_piece {F : Type*} [Field F] {I : Ideal (Ring F)} {d k : Box}
    (S : Section I k) (h : 2*S.order ≤ d.base) {s : Ring F ⧸ I} (hs : s ∈ piece I d) :
    Ideal.Quotient.mk I S.finite * s ∈ piece I (d.add k) := by
  classical
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hs
  change Ideal.Quotient.mk I S.finite * Ideal.Quotient.mk I f ∈ _
  have he : Ideal.Quotient.mk I f =
      ∑ m ∈ f.support, Ideal.Quotient.mk I (monomial m (f.coeff m)) := by
    conv_lhs => rw [f.as_sum, map_sum]
  rw [he, Finset.mul_sum]
  apply Submodule.sum_mem
  exact fun m hm => mul_monomial S h m (hf hm) _

/-- The actual multigraded dimension loss on any on-chart regular quotient.
    Subsequent cuts and saturation may be included in `J`. -/
theorem hilbert_drop {F : Type*} [Field F] {I J : Ideal (Ring F)} (hIJ : I ≤ J)
    {d k : Box} (S : Section I k) (h : 2*S.order ≤ d.base) (hS : S.finite ∈ J)
    (hreg : IsLeftRegular (Ideal.Quotient.mk I S.finite)) :
    Module.finrank F (piece J (d.add k)) + Module.finrank F (piece I d) ≤
      Module.finrank F (piece I (d.add k)) := by
  let A := piece I d
  let B := piece I (d.add k)
  let C := piece J (d.add k)
  let phi := Ideal.Quotient.factorₐ F hIJ
  have hto (b : B) : phi b.val ∈ C := by
    obtain ⟨w, hw, hw'⟩ := Submodule.mem_map.mp b.property
    exact Submodule.mem_map.mpr ⟨w, hw, by rw [← hw']; rfl⟩
  let E : B →ₗ[F] C := (phi.toLinearMap.comp B.subtype).codRestrict C hto
  have hsurj : Function.Surjective E := by
    intro c
    obtain ⟨w, hw, hw'⟩ := Submodule.mem_map.mp c.property
    exact ⟨⟨Ideal.Quotient.mk I w, Submodule.mem_map.mpr ⟨w,hw,rfl⟩⟩, Subtype.ext hw'⟩
  let μ := LinearMap.mulLeft F (Ideal.Quotient.mk I S.finite)
  let M : A →ₗ[F] B := (μ.comp A.subtype).codRestrict B (fun a => mul_piece S h a.property)
  have hz (a : A) : M a ∈ LinearMap.ker E := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change phi (Ideal.Quotient.mk I S.finite * a.val) = 0
    rw [map_mul, show phi (Ideal.Quotient.mk I S.finite) = Ideal.Quotient.mk J S.finite from rfl,
      Ideal.Quotient.eq_zero_iff_mem.mpr hS, zero_mul]
  let K := M.codRestrict (LinearMap.ker E) hz
  have hi : Function.Injective K := by
    intro a b hab
    exact Subtype.ext (hreg (congrArg (fun x : LinearMap.ker E => x.val.val) hab))
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have he := E.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at he
  exact (Nat.add_le_add_left hdim _).trans_eq he

end SplitCut.Rect
