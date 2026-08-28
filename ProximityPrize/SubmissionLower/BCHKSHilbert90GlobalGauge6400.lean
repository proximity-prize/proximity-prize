import ProximityPrize.SubmissionLower.BCHKSFiniteUnionSubmoduleAvoidance6400
import ProximityPrize.SubmissionLower.BCHKSSemilinearLocatorSaturation6400

/-!
# A domain-wide Hilbert--90 gauge

The explicit six-cycle adjugate is linear over the KoalaBear base field in
its seed.  At each fixed node with nonzero first coefficient, evaluation is a
nonzero linear map of that seed.  Since the production domain has fewer
points than the base field, finite-union avoidance supplies one seed whose
adjugate is nonzero at every node simultaneously.

The scalar normalization lemmas at the end record the exact consequence:
two nonzero solutions of the same semilinear equation have a quotient fixed
by Frobenius.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSHilbert90GlobalGauge6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSFiniteUnionSubmoduleAvoidance6400
open BCHKSSemilinearLocatorSaturation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

local instance : CharP IRSProfile.Field 2130706433 :=
  ProximityPrize.SubmissionLower.koalaSexticChar

local instance : Fact (Nat.Prime 2130706433) :=
  ProximityPrize.SubmissionLower.koalaPrimeFact

/-- One Hilbert--90 seed avoids every node in an arbitrary family of at most
`p` fixed nodes. -/
theorem exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_finset6400
    {I : Type} [DecidableEq I]
    (v : I → IRSProfile.Field) (G : Finset I)
    (A B : IRSProfile.Field[X])
    (hfixed : ∀ i ∈ G, koalaSexticFrobenius (v i) = v i)
    (hAeval : ∀ i ∈ G, A.eval (v i) ≠ 0)
    (hcard : G.card ≤ 2130706433) :
    ∃ t : IRSProfile.Field, ∀ i ∈ G,
      (koalaHomogeneousHilbert90Kernel6400 A B t).eval (v i) ≠ 0 := by
  classical
  let evalMap : I → IRSProfile.Field →ₗ[KoalaBear.Field] IRSProfile.Field :=
    fun i => koalaHomogeneousHilbert90EvalLinear6400 A B (v i)
  have hmap : ∀ i ∈ G, evalMap i ≠ 0 := by
    intro i hi
    exact koalaHomogeneousHilbert90EvalLinear_ne_zero6400
      A B (v i) (hfixed i hi) (hAeval i hi)
  have hbaseCard : G.card ≤ Fintype.card KoalaBear.Field := by
    have hbase : Fintype.card KoalaBear.Field = 2130706433 := by
      norm_num [KoalaBear.Field, KoalaBear.fieldSize]
    rw [hbase]
    exact hcard
  obtain ⟨t, ht⟩ := exists_simultaneously_nonzero_linear_maps6400
    G evalMap hmap hbaseCard
  refine ⟨t, ?_⟩
  intro i hi
  simpa only [evalMap,
    koalaHomogeneousHilbert90EvalLinear_apply6400] using ht i hi

/-- Coprimality and equal norm supply the nodewise nonvanishing hypothesis
for both semilinear coefficients. -/
theorem exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_finset_of_isCoprime6400
    {I : Type} [DecidableEq I]
    (v : I → IRSProfile.Field) (G : Finset I)
    (A B : IRSProfile.Field[X])
    (hfixed : ∀ i ∈ G, koalaSexticFrobenius (v i) = v i)
    (hcoprime : IsCoprime A B)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hcard : G.card ≤ 2130706433) :
    ∃ t : IRSProfile.Field, ∀ i ∈ G,
      (koalaHomogeneousHilbert90Kernel6400 A B t).eval (v i) ≠ 0 := by
  apply exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_finset6400
    v G A B hfixed
  · intro i hi
    exact (eval_pair_ne_zero_of_norm_eq6400 A B (v i) (hfixed i hi)
      hnorm (not_both_eval_eq_zero_of_isCoprime A B hcoprime (v i))).1
  · exact hcard

/-- Production specialization: a coprime equal-norm pair has one adjugate
kernel polynomial nonzero on the entire NTT domain. -/
theorem exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_domain6400
    (A B : IRSProfile.Field[X])
    (hcoprime : IsCoprime A B)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B) :
    ∃ t : IRSProfile.Field, ∀ i : IRSProfile.Index,
      (koalaHomogeneousHilbert90Kernel6400 A B t).eval
        (IRSProfile.domain i) ≠ 0 := by
  obtain ⟨t, ht⟩ :=
    exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_finset_of_isCoprime6400
      IRSProfile.domain Finset.univ A B
      (fun i hi => koalaSexticFrobenius_fixed_domain i)
      hcoprime hnorm (by
        norm_num [IRSProfile.Index])
  exact ⟨t, fun i => ht i (Finset.mem_univ i)⟩

/-- The explicit adjugate contains five conjugate factors in every term. -/
theorem koalaHomogeneousHilbert90Kernel_natDegree_le6400
    (A B : IRSProfile.Field[X]) (t : IRSProfile.Field) :
    (koalaHomogeneousHilbert90Kernel6400 A B t).natDegree ≤
      5 * max A.natDegree B.natDegree := by
  unfold koalaHomogeneousHilbert90Kernel6400
  compute_degree
  all_goals simp only [koalaFrobeniusConjugate_natDegree]
  all_goals omega

/-- Convenient common-degree form of the adjugate bound. -/
theorem koalaHomogeneousHilbert90Kernel_natDegree_le_of_le6400
    (A B : IRSProfile.Field[X]) (t : IRSProfile.Field) (d : Nat)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (koalaHomogeneousHilbert90Kernel6400 A B t).natDegree ≤ 5 * d := by
  exact (koalaHomogeneousHilbert90Kernel_natDegree_le6400 A B t).trans
    (Nat.mul_le_mul_left 5 (max_le hA hB))

/-- Two solutions of the same scalar semilinear equation have zero
Frobenius cross-product. -/
theorem frobenius_cross_eq_of_common_semilinear_zero6400
    (a b e h : IRSProfile.Field)
    (hb : b ≠ 0)
    (he : a * e + b * koalaSexticFrobenius e = 0)
    (hh : a * h + b * koalaSexticFrobenius h = 0) :
    koalaSexticFrobenius e * h =
      e * koalaSexticFrobenius h := by
  have hcrossProduct :
      b * (koalaSexticFrobenius e * h -
        e * koalaSexticFrobenius h) = 0 := by
    linear_combination he * h - hh * e
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hcrossProduct).resolve_left hb)

/-- If the denominator solution is nonzero, the quotient of two solutions
lies in the Frobenius-fixed base field. -/
theorem frobenius_div_eq_self_of_common_semilinear_zero6400
    (a b e h : IRSProfile.Field)
    (hb : b ≠ 0) (hhne : h ≠ 0)
    (he : a * e + b * koalaSexticFrobenius e = 0)
    (hh : a * h + b * koalaSexticFrobenius h = 0) :
    koalaSexticFrobenius (e / h) = e / h := by
  have hcross := frobenius_cross_eq_of_common_semilinear_zero6400
    a b e h hb he hh
  rw [map_div₀]
  exact (div_eq_div_iff
    ((_root_.map_ne_zero (f := koalaSexticFrobenius)).mpr hhne)
      hhne).2 hcross

end BCHKSHilbert90GlobalGauge6400
end ProximityPrize.SubmissionLower
