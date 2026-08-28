import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SmallPurelyInseparablePole

/-!
# Pole mass below twice the characteristic

For a finite rational-function projection of degree below `2p`, either
the extension is separable and the established normalization theorem
applies, or it is the rigid purely inseparable degree-`p` case handled
by `SmallPurelyInseparablePole`.
-/

namespace ProximityPrize.SubmissionLower.SmallProjectionPoleMass

open scoped Classical BigOperators

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [IsAlgClosed K]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

/-- Characteristic-free pole mass for every projection whose full field
degree is strictly below twice the prime characteristic. -/
theorem finite_sum_pole_le_finrank
    (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (c : RatFunc K →ₐ[K] L)
    (hfinite : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hsmall : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      Module.finrank (RatFunc K) L < 2 * p)
    (W : Finset (Place K L)) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c RatFunc.X)) ≤
      ((letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
        Module.finrank (RatFunc K) L : ℕ) : ℤ) := by
  letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
  letI : Algebra (Polynomial K) L :=
    (c.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
  letI : IsScalarTower (Polynomial K) (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (c.commutes a).symm
  letI : IsScalarTower K (Polynomial K) L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap K L a =
        c (algebraMap (Polynomial K) (RatFunc K)
          (algebraMap K (Polynomial K) a))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      exact (c.commutes a).symm
  letI : FiniteDimensional (RatFunc K) L := hfinite
  by_cases hsep : Algebra.IsSeparable (RatFunc K) L
  · letI : Algebra.IsSeparable (RatFunc K) L := hsep
    exact CoordinatePoleMass.finite_sum_pole_le_finrank K L W
  · obtain ⟨hdegree, hpure⟩ :=
      SmallInseparableProjection.finrank_eq_prime_and_purelyInseparable_of_not_separable
        (F := RatFunc K) (E := L) p hp hsep hsmall
    have hpoles := SmallPurelyInseparablePole.finite_sum_pole_le_prime
      K L p hp c hfinite hpure hdegree W
    simpa only [hdegree, Nat.cast_ofNat] using hpoles

end

end ProximityPrize.SubmissionLower.SmallProjectionPoleMass

#print axioms ProximityPrize.SubmissionLower.SmallProjectionPoleMass.finite_sum_pole_le_finrank
