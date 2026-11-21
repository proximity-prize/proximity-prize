import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
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

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.BoxDegree
noncomputable section
open MvPolynomial Filter
open scoped BigOperators Pointwise Polynomial
abbrev Idx := Option (Fin 2)
abbrev Exp := Idx →₀ ℕ

def exps (a b c : ℕ) : Set Exp :=
  {m | m none ≤ a ∧ m (some 0) ≤ b ∧ m (some 1) ≤ c}

def slots (a b c : ℕ) : exps a b c ≃ Fin (a+1) × Fin (b+1) × Fin (c+1) where
  toFun m := ⟨⟨_, Nat.lt_succ_of_le m.2.1⟩, ⟨_, Nat.lt_succ_of_le m.2.2.1⟩,
    ⟨_, Nat.lt_succ_of_le m.2.2.2⟩⟩
  invFun p := ⟨Finsupp.equivFunOnFinite.symm (fun i : Idx => i.elim p.1.val ![p.2.1.val,p.2.2.val]),
    ⟨Nat.le_of_lt_succ p.1.isLt, Nat.le_of_lt_succ p.2.1.isLt,
      Nat.le_of_lt_succ p.2.2.isLt⟩⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

noncomputable instance (a b c : ℕ) : Fintype (exps a b c) := Fintype.ofEquiv _ (slots a b c).symm

variable {F : Type*} [Field F]
abbrev space (F : Type*) [Field F] (a b c : ℕ) :=
  MvPolynomial.restrictSupport (σ := Idx) F (exps a b c)

instance spaceFinite (a b c : ℕ) : Module.Finite F (space F a b c) :=
  Module.Finite.of_basis (basisRestrictSupport F (exps a b c))

theorem size (a b c : ℕ) : Module.finrank F (space F a b c) = (a+1)*(b+1)*(c+1) := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport F (exps a b c)),
    Nat.card_congr (slots a b c)]
  simp [Nat.card_eq_fintype_card, Nat.mul_assoc]

theorem add_box {a b c u v w : ℕ} :
    exps a b c + exps u v w ⊆ exps (a+u) (b+v) (c+w) := by
  rintro _ ⟨m, hm, n, hn, rfl⟩
  exact ⟨Nat.add_le_add hm.1 hn.1, Nat.add_le_add hm.2.1 hn.2.1, Nat.add_le_add hm.2.2 hn.2.2⟩

theorem mul_box {a b c u v w : ℕ} {f g : MvPolynomial Idx F}
    (hf : f ∈ space F a b c) (hg : g ∈ space F u v w) :
    f*g ∈ space F (a+u) (b+v) (c+w) := by
  apply restrictSupport_mono F add_box
  rw [restrictSupport_add]
  exact Submodule.mul_mem_mul hf hg

theorem scales (a b c n : ℕ) : n • exps a b c ⊆ exps (a*n) (b*n) (c*n) := by
  induction n with
  | zero =>
    rw [zero_smul, Set.zero_subset]
    exact ⟨by simp, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul]
    exact (Set.add_subset_add ih subset_rfl).trans add_box

theorem axis {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (i : Idx) :
    Finsupp.single i 1 ∈ exps a b c := by
  unfold exps
  simp only [Set.mem_ofPred_eq, Finsupp.single_apply]
  split_ifs <;> omega

abbrev proj (F : Type*) [Field F] (a b c : ℕ) := monomialMap F (exps a b c)

theorem dim_add {a b c h j r n : ℕ} {g : MvPolynomial Idx F} (hg0 : g ≠ 0)
    (hg : g ∈ space F h j r) (hh : h≤a*n) (hj : j≤b*n) (hr : r≤c*n) :
    affineHilbertFunction ((Ideal.span {g}).comap (proj F a b c)) n +
      (a*n-h+1)*(b*n-j+1)*(c*n-r+1) ≤ (a*n+1)*(b*n+1)*(c*n+1) := by
  have hdim := affineHilbertFunction_comap_span_singleton_add_finrank_le (proj F a b c) hg0
    (M := space F (a*n) (b*n) (c*n)) (M' := space F (a*n-h) (b*n-j) (c*n-r))
    (fun _ hp => restrictSupport_mono F (scales a b c n)
      (monomialMap_mem_restrictSupport_nsmul (show 0 ∈ exps a b c from
        ⟨by simp, by simp, by simp⟩) hp)) fun p hp => by
          simpa only [Nat.add_sub_cancel' hh, Nat.add_sub_cancel' hj,
            Nat.add_sub_cancel' hr] using mul_box hg hp
  simpa only [size] using hdim

/-- Ordinary affine degree of a surface in the rectangular monomial embedding. -/
theorem surface {a b c h j r : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    {g : MvPolynomial Idx F} (hg0 : g ≠ 0) (hg : g ∈ space F h j r) :
    affineDegree ((Ideal.span {g}).comap (proj F a b c)) ≤
      (2*(h*b*c+j*a*c+r*a*b) : ℕ) := by
  by_cases ht : Ideal.span {g} = ⊤
  · rw [ht, Ideal.comap_top, affineDegree_top]
    exact Nat.cast_nonneg _
  have hs := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
    (proj F a b c) (monomialMap_surjective (axis ha hb hc)) hg0 ht
  have hdim : (affineHilbertPolynomial ((Ideal.span {g}).comap (proj F a b c))).natDegree = 2 := by
    rw [show Nat.card Idx = 3 by simp [Idx,Nat.card_eq_fintype_card]] at hs
    omega
  let q₂ : ℚ := (h:ℚ)*b*c + (j:ℚ)*a*c + (r:ℚ)*a*b
  let q₁ : ℚ := (a:ℚ)+(b:ℚ)+(c:ℚ) - (a*(1-(j:ℚ))*(1-(r:ℚ)) +
    b*(1-(h:ℚ))*(1-(r:ℚ)) + c*(1-(h:ℚ))*(1-(j:ℚ)))
  let q₀ : ℚ := 1 - (1-(h:ℚ))*(1-(j:ℚ))*(1-(r:ℚ))
  let R : ℚ[X] := Polynomial.C q₂*Polynomial.X^2 + Polynomial.C q₁*Polynomial.X + Polynomial.C q₀
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim
    (R := R) Polynomial.natDegree_quadratic_le ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop (h+j+r)] with n hn
    have hh : h ≤ a*n := (show h≤n by omega).trans (Nat.le_mul_of_pos_left _ ha)
    have hj : j ≤ b*n := (show j≤n by omega).trans (Nat.le_mul_of_pos_left _ hb)
    have hr : r ≤ c*n := (show r≤n by omega).trans (Nat.le_mul_of_pos_left _ hc)
    have H := dim_add hg0 hg hh hj hr
    have Hq : ((_ : ℕ) : ℚ) ≤ ((_ : ℕ) : ℚ) := Nat.cast_le.mpr H
    push_cast [Nat.cast_sub hh, Nat.cast_sub hj, Nat.cast_sub hr] at Hq
    have HR : R.eval (n:ℚ) =
      ((a:ℚ)*n+1)*(b*n+1)*(c*n+1) - (a*n-h+1)*(b*n-j+1)*(c*n-r+1) := by
      simp only [R,q₂,q₁,q₀,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_C]
      push_cast
      ring
    rw [HR]
    linarith only [Hq]
  · have hh : R.coeff 2 = q₂ := by simp [R, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [hh]
    norm_num [Nat.factorial,q₂] <;> ring

/-- Total degree of the irreducible surfaces, including reducible root equations. -/
theorem surfaces {a b c h j r : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    {g : MvPolynomial Idx F} (hg0 : g ≠ 0) (hg : g ∈ space F h j r) :
    ∑ Q ∈ ((Ideal.span {g}).comap (proj F a b c)).minimalPrimesFinset,
      affineDegree Q ≤ (2*(h*b*c+j*a*c+r*a*b) : ℕ) :=
  (sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective (proj F a b c)
    (monomialMap_surjective (axis ha hb hc)) g).trans (surface ha hb hc hg0 hg)

end
end SplitCut.BoxDegree
#print axioms SplitCut.BoxDegree.surface
#print axioms SplitCut.BoxDegree.surfaces
