import ProximityPrize.SubmissionLower.BCHKSUniversalSelectedPairCore
import ProximityPrize.SubmissionLower.BCHKSFullCoreOwnerBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCanonicalGammaCoreQuotient6400

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSFullCoreLineArrangement6400

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
The canonical finite-Hensel branch may be quotiented by a common evaluation
core before any owner specialization.  This file isolates the algebraic
part of that reduction.  In particular, division is by the mapped monic
core locator, so it introduces no new denominator in the function field.
-/

/-- A polynomial over an extension field which vanishes on the embedded core
is divisible by the mapped ground-field locator. -/
theorem map_coreLocator_dvd_of_eval_eq_zero
    {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (phi : F →+* K) (hphi : Function.Injective phi)
    (E : Finset F) (D : K[X])
    (hzero : ∀ x ∈ E, D.eval (phi x) = 0) :
    (coreLocator E).map phi ∣ D := by
  classical
  unfold coreLocator
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_dvd_of_coprime
  · intro x hx y hy hxy
    exact Polynomial.pairwise_coprime_X_sub_C hphi hxy
  · intro x hx
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero x hx

@[simp]
theorem natDegree_map_coreLocator
    {F K : Type*} [Field F] [Field K]
    (phi : F →+* K) (E : Finset F) :
    ((coreLocator E).map phi).natDegree = E.card := by
  rw [Polynomial.Monic.natDegree_map (coreLocator_monic E)]
  exact coreLocator_natDegree E

/-- Extension-field version of the bounded core quotient.  The base term is
allowed to contain one distinguished extension-field scalar `y`; this is
the role played by the generic challenge coordinate in `𝕃 H`. -/
theorem exists_extension_coreQuotient_natDegree_le
    {F K : Type*} [Field F] [Field K]
    (phi : F →+* K) (hphi : Function.Injective phi)
    (E : Finset F) (gamma : K[X]) (B0 B1 : F[X]) (y : K)
    (k s : ℕ)
    (hcard : E.card + s = k)
    (hgamma : gamma.natDegree ≤ k)
    (hB0 : B0.natDegree ≤ k) (hB1 : B1.natDegree ≤ k)
    (heval : ∀ x ∈ E,
      gamma.eval (phi x) = phi (B0.eval x) + y * phi (B1.eval x)) :
    ∃ gammaQ : K[X], gammaQ.natDegree ≤ s ∧
      gamma = B0.map phi + Polynomial.C y * B1.map phi +
        (coreLocator E).map phi * gammaQ := by
  classical
  letI : DecidableEq F := Classical.decEq F
  letI : DecidableEq K := Classical.decEq K
  let base : K[X] := B0.map phi + Polynomial.C y * B1.map phi
  let D : K[X] := gamma - base
  have hbase : base.natDegree ≤ k := by
    dsimp [base]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_map_le.trans hB0)
        ((Polynomial.natDegree_C_mul_le _ _).trans
          (Polynomial.natDegree_map_le.trans hB1)))
  have hDdegree : D.natDegree ≤ k := by
    dsimp [D]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hgamma hbase)
  have hDzero : ∀ x ∈ E, D.eval (phi x) = 0 := by
    intro x hx
    simp only [D, base, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map]
    rw [heval x hx]
    simp
  obtain ⟨gammaQ, hfac⟩ :=
    map_coreLocator_dvd_of_eval_eq_zero phi hphi E D hDzero
  have hQdegree : gammaQ.natDegree ≤ s := by
    by_cases hQ0 : gammaQ = 0
    · simp [hQ0]
    · have hlocMonic : ((coreLocator E).map phi).Monic :=
        (coreLocator_monic E).map phi
      have hdegreeEq : D.natDegree = E.card + gammaQ.natDegree := by
        rw [hfac, hlocMonic.natDegree_mul' hQ0,
          natDegree_map_coreLocator]
      omega
  refine ⟨gammaQ, hQdegree, ?_⟩
  dsimp [D, base] at hfac
  linear_combination hfac

/-- Once the universal obstruction identities have been converted by
`gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero`, their values on
the common core directly produce the bounded quotient of the canonical
function-field branch. -/
theorem exists_canonicalGamma_coreQuotient_of_core_evaluations
    {F : Type} [Field F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x0 : F) (R : F[X][X][Y]) (N k s : ℕ)
    (E : Finset F) (hcard : E.card + s = k)
    (U0 U1 : F → F) (B0 B1 : F[X])
    (hB0 : B0.natDegree ≤ k) (hB1 : B1.natDegree ≤ k)
    (hB0eval : ∀ x ∈ E, B0.eval x = U0 x)
    (hB1eval : ∀ x ∈ E, B1.eval x = U1 x)
    (hgammaEval : ∀ x ∈ E,
      (canonicalFunctionFieldGamma H x0 R N k).eval
          (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (U0 x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (U1 x)) :
    ∃ gammaQ : (𝕃 H)[X], gammaQ.natDegree ≤ s ∧
      canonicalFunctionFieldGamma H x0 R N k =
        B0.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            B1.map (groundToFunctionField H) +
          (coreLocator E).map (groundToFunctionField H) * gammaQ := by
  have heval : ∀ x ∈ E,
      (canonicalFunctionFieldGamma H x0 R N k).eval
          (groundToFunctionField H x) =
        groundToFunctionField H (B0.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            groundToFunctionField H (B1.eval x) := by
    intro x hx
    change (canonicalFunctionFieldGamma H x0 R N k).eval
        (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) (B0.eval x) +
        liftToFunctionField (H := H) Polynomial.X *
          fieldTo𝕃 (H := H) (B1.eval x)
    simpa [hB0eval x hx, hB1eval x hx] using hgammaEval x hx
  exact exists_extension_coreQuotient_natDegree_le
    (groundToFunctionField H) (RingHom.injective _)
    E (canonicalFunctionFieldGamma H x0 R N k) B0 B1
    (liftToFunctionField (H := H) Polynomial.X) k s hcard
    (canonicalFunctionFieldGamma_natDegree_le x0 R N k)
    hB0 hB1 heval

end BCHKSCanonicalGammaCoreQuotient6400
end ProximityPrize.SubmissionLower
