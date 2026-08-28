import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch

/-!
# The algebraic core of the positive-characteristic separating shear

Research module, deliberately kept off the green submission chain.

For a one-variable function field over a perfect field of characteristic
`p`, a nonconstant parameter is separating exactly when its universal
differential is nonzero (equivalently, when it is not a `p`-th power).
Consequently, if `R` is nonseparating and `Z` is separating, then
`S = R + Z` is separating.  The difficult function-field equivalence is not
yet in Mathlib; this file isolates it as the predicate/differential bridge
`hcriterion`.  Everything after that bridge is proved here.

The file also records two useful pieces which *are* already formalizable:

* translation by a Frobenius image preserves non-membership in the
  Frobenius image;
* in a purely inseparable extension of prime total degree `p`, every
  `p`-th power in the top field lies in the bottom field.

Neither statement falsely claims that the bottom parameter itself is a
`p`-th power; that latter conclusion additionally uses the one-variable
function-field theorem `[L : L^p] = p` (or Kähler differentials).
-/

namespace ProximityPrize.SubmissionLower.SeparableShearFieldResearch

open scoped Classical

noncomputable section

/-- The image of Frobenius is an additive subgroup, so translating a point
outside it by a point inside it cannot enter it. -/
theorem add_not_mem_frobenius_range_of_mem_not_mem
    (L : Type*) [Field L] (p : ℕ) [ExpChar L p]
    {r z : L} (hr : r ∈ (frobenius L p).range)
    (hz : z ∉ (frobenius L p).range) :
    r + z ∉ (frobenius L p).range := by
  intro hrs
  apply hz
  have hsub : (r + z) - r ∈ (frobenius L p).range :=
    Subring.sub_mem (frobenius L p).range hrs hr
  simpa only [add_sub_cancel_left] using hsub

/-- In a purely inseparable extension whose total degree is the
characteristic prime, every first Frobenius power already descends to the
base.  This is the exponent-one fact available from the degree-`p`
exceptional block. -/
theorem pow_prime_mem_base_of_pure_degree_prime
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsPurelyInseparable F E]
    (p : ℕ) [ExpChar F p] (hp : p.Prime)
    (hdegree : Module.finrank F E = p) (x : E) :
    x ^ p ∈ (algebraMap F E).range := by
  obtain ⟨n, y, hmin⟩ :=
    IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hmin_degree : (minpoly F x).natDegree = p ^ n := by
    rw [hmin, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
  have hpow_le : p ^ n ≤ p := by
    calc
      p ^ n = (minpoly F x).natDegree := hmin_degree.symm
      _ ≤ Module.finrank F E := minpoly.natDegree_le x
      _ = p := hdegree
  have hn_le : n ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    simpa only [pow_one] using hpow_le
  have hrel : x ^ p ^ n = algebraMap F E y := by
    have hroot := minpoly.aeval F x
    rw [hmin, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C,
      sub_eq_zero] at hroot
    exact hroot
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with rfl | rfl
  · have hx : x ∈ (algebraMap F E).range := by
      refine ⟨y, ?_⟩
      simpa only [pow_zero, pow_one] using hrel.symm
    exact Subring.pow_mem (algebraMap F E).range hx p
  · exact ⟨y, by simpa only [pow_one] using hrel.symm⟩

/-- The exact formal core of the separating-shear argument.  The predicate
`Separating` is intended to mean that the induced finite rational
projection is separable; `hcriterion` is the missing one-variable
function-field theorem identifying this with a nonzero differential. -/
theorem separating_add_of_differential_criterion
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (D : Derivation K L L) (Separating : L → Prop)
    (hcriterion : ∀ f, Separating f ↔ D f ≠ 0)
    {r z : L} (hr : ¬ Separating r) (hz : Separating z) :
    Separating (r + z) := by
  rw [hcriterion]
  have hDr : D r = 0 := by
    by_contra hne
    exact hr ((hcriterion r).mpr hne)
  have hDz : D z ≠ 0 := (hcriterion z).mp hz
  rw [map_add, hDr, zero_add]
  exact hDz

/-- A cap-level version of the conservative box calculation.  If the
sheared parameter degree satisfies `dS ≤ dR + dZ`, substitution
`R = S - Z` changes `(cY,cR,cZ)` to `(cY,cR,cZ+cR)` and costs at most
`2*cR*dZ` beyond the old box. -/
theorem sheared_box_cost_le_old_add_two_penalty
    (cY cR cZ dY dR dZ dS : ℕ) (hS : dS ≤ dR + dZ) :
    cY * dY + cR * dS + (cZ + cR) * dZ ≤
      (cY * dY + cR * dR + cZ * dZ) + 2 * cR * dZ := by
  calc
    cY * dY + cR * dS + (cZ + cR) * dZ ≤
        cY * dY + cR * (dR + dZ) + (cZ + cR) * dZ := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left (Nat.mul_le_mul_left cR hS) (cY * dY))
            ((cZ + cR) * dZ)
    _ = (cY * dY + cR * dR + cZ * dZ) + 2 * cR * dZ := by
      ring

end

end ProximityPrize.SubmissionLower.SeparableShearFieldResearch

#print axioms ProximityPrize.SubmissionLower.SeparableShearFieldResearch.add_not_mem_frobenius_range_of_mem_not_mem
#print axioms ProximityPrize.SubmissionLower.SeparableShearFieldResearch.pow_prime_mem_base_of_pure_degree_prime
#print axioms ProximityPrize.SubmissionLower.SeparableShearFieldResearch.separating_add_of_differential_criterion
#print axioms ProximityPrize.SubmissionLower.SeparableShearFieldResearch.sheared_box_cost_le_old_add_two_penalty
