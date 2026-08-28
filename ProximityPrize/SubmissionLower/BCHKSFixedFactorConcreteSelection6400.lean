import ProximityPrize.SubmissionLower.BCHKSFixedFactorUniversalSelection6400
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionLower.BCHKSUniversalPairFiberBridge6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace FixedFactorConcreteSelection6400

open FixedFactorCover6400
open FixedFactorUniversalSelection6400
open UniversalNumerator

/-- Concrete instantiation of the fixed-factor selector with the universal
affine obstruction attached to the received affine word. -/
theorem exists_concrete_fixed_factor_pair_6400
    (U : Fin 2 → IRSProfile.Index → F)
    (S : Finset F)
    (A : F → Finset IRSProfile.Index)
    (P : ↑S → Polynomial F)
    (R : TriPoly)
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hD : D ≤ 1898945373)
    (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424)
    (hPdeg : ∀ z : ↑S, (P z).natDegree ≤ 131071)
    (hAcard : ∀ z : ↑S, 185364 ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + z.1 * U 1 i)
    (hRroot : ∀ z : ↑S, triEval R z.1 (P z) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ x₀ : F, ∃ Bad : Finset F, ∃ H : BiPoly,
      ∃ Coord : Finset IRSProfile.Index,
      Bad.card ≤ 2 * R.natDegree * D ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      (∀ z ∉ Bad, Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0) ∧
      H ∈ innerFactors R x₀ ∧
      bchksErrors6400 + 1 <
        (innerFiber S Bad
          (fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0) x₀ H).card ∧
      131072 ≤ Coord.card ∧
      (∀ z ∈ innerFiber S Bad
        (fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0) x₀ H,
          innerRel (fun z => if hz : z ∈ S then P ⟨z, hz⟩ else 0)
            x₀ z H) ∧
      (∀ i ∈ Coord, H ∣
        concreteUniversalAffineObstruction x₀ R
          bchksUniversalExponent6399 131071
          (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)) ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let PE : F → Polynomial F := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let G : F → BiPoly → IRSProfile.Index → BiPoly := fun x₀ _H i =>
    concreteUniversalAffineObstruction x₀ R
      bchksUniversalExponent6399 131071
      (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
  have hPEdeg : ∀ z ∈ S, (PE z).natDegree ≤ 131071 := by
    intro z hz
    simpa [PE, hz] using hPdeg ⟨z, hz⟩
  have hPEroot : ∀ z ∈ S, triEval R z (PE z) = 0 := by
    intro z hz
    simpa [PE, hz] using hRroot ⟨z, hz⟩
  have hrow : ∀ z ∈ S,
      262144 - bchksErrors6400 ≤ (A z).card := by
    intro z hz
    norm_num [bchksErrors6400]
    exact hAcard ⟨z, hz⟩
  have hDpos : 0 < D := by
    have hR0 : R ≠ 0 := hR.ne_zero
    have hdD := natDegree_le_of_YZCap R D hR0 hYZ
    omega
  have hGcaps : ∀ x₀ H, H ∈ innerFactors R x₀ → ∀ i,
      (G x₀ H i).natDegree ≤
          bchksUniversalExponent6399 * R.natDegree ∧
      Bivariate.degreeX (G x₀ H i) ≤
          bchksUniversalExponent6399 * D := by
    intro x₀ H hH i
    simpa [G] using
      concreteUniversalAffineObstruction_degree_bounds x₀ R
        bchksUniversalExponent6399 131071 R.natDegree D
        (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
        (by norm_num [bchksUniversalExponent6399,
          FiniteHenselWeight.denominatorExponent])
        (by norm_num) (by omega) hDpos (by omega) le_rfl hYZ
  have hGroot : ∀ x₀ z H, H ∈ innerFactors R x₀ →
      z ∈ S →
      innerRel PE x₀ z H →
      Polynomial.eval ((PE z).eval x₀)
        (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0 →
      ∀ i ∈ A z, biEval (G x₀ H i) ((PE z).eval x₀) z = 0 := by
    intro x₀ z H hH hzS hHroot hslope i hi
    have hsimple : FiniteHensel.ySlope (triSpecializeZ R z) x₀
        ((PE z).eval x₀) ≠ 0 := by
      rw [UniversalPairFiberBridge6399.ySlope_eq_derivative_specialization]
      exact hslope
    apply biEval_concreteUniversalAffineObstruction_eq_zero
      x₀ z ((PE z).eval x₀) R (PE z)
      bchksUniversalExponent6399 131071
      (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
    · norm_num [bchksUniversalExponent6399,
        FiniteHenselWeight.denominatorExponent]
    · omega
    · rfl
    · exact hPEdeg z hzS
    · exact hPEroot z hzS
    · exact hsimple
    · have ha := hagree ⟨z, hzS⟩ i hi
      simpa [PE, hzS] using ha
  simpa [PE, G] using
    exists_fixed_factor_coordinate_divisibility_6400
      S PE R A G hR hpos hd D hD hYZ hweighted hPEroot hS hrow
      hGcaps hGroot

end FixedFactorConcreteSelection6400

end ProximityPrize.SubmissionLower
