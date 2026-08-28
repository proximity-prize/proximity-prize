import ProximityPrize.SubmissionLower.BCHKSUniversalOuterSelection6399
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionLower.BCHKSUniversalPairFiberBridge6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace UniversalConcreteSelection6399

open UniversalOuterCover6399
open UniversalOuterSelection6399
open UniversalPairFiberBridge6399
open UniversalNumerator

/-- The global universal-resultant selector, instantiated with the concrete
rooted numerator obstruction attached to the interpolant. -/
theorem exists_concrete_selected_pair6399
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↑S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hScard : bchksNumerator6399 < S.card)
    (hQ : Q ≠ 0)
    (hPdeg : ∀ z : ↑S, (P z).natDegree ≤ 131071)
    (hAcard : ∀ z : ↑S, 185374 ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + z.1 * U 1 i)
    (hQeval : ∀ z : ↑S, triEval Q z.1 (P z) = 0)
    (hcaps : SupportCaps Q) :
    ∃ x₀ : IRSProfile.Field, ∃ RH : Pair,
      ∃ T : Finset IRSProfile.Field,
      ∃ Coord : Finset IRSProfile.Index,
      RH ∈ pairs Q x₀ ∧
      ((triSpecializeX RH.1 x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₀ ≠ 0 ∧
        (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₀)
          (rawSepResultant RH.1) ≠ 0) ∧
      T ⊆ S ∧
      bchksErrors6399 + 1 < T.card ∧
      131072 ≤ Coord.card ∧
      (∀ z ∈ T,
        pairRel (fun w => if hw : w ∈ S then P ⟨w, hw⟩ else 0)
          x₀ z RH) ∧
      (∀ i ∈ Coord, RH.2 ∣
        concreteUniversalAffineObstruction x₀ RH.1
          bchksUniversalExponent6399 131071
          (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)) := by
  classical
  let PE : IRSProfile.Field → Polynomial IRSProfile.Field := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let G : IRSProfile.Field → Pair → IRSProfile.Index →
      Polynomial (Polynomial IRSProfile.Field) := fun x₀ RH i =>
    concreteUniversalAffineObstruction x₀ RH.1
      bchksUniversalExponent6399 131071
      (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
  have hPEdeg : ∀ z ∈ S, (PE z).natDegree ≤ 131071 := by
    intro z hz
    simpa [PE, hz] using hPdeg ⟨z, hz⟩
  have hPEeval : ∀ z ∈ S, triEval Q z (PE z) = 0 := by
    intro z hz
    simpa [PE, hz] using hQeval ⟨z, hz⟩
  have hrow : ∀ z ∈ S,
      262144 - bchksErrors6399 ≤ (A z).card := by
    intro z hz
    norm_num [bchksErrors6399]
    exact hAcard ⟨z, hz⟩
  have hGcaps : ∀ x₀ RH, RH ∈ pairs Q x₀ → ∀ i,
      (G x₀ RH i).natDegree ≤
          bchksUniversalExponent6399 * RH.1.natDegree ∧
      Bivariate.degreeX (G x₀ RH i) ≤
          bchksUniversalExponent6399 * bchksFactorZMass6399 := by
    intro x₀ RH hRH i
    have hm := pair_mem_facts Q x₀ RH hRH
    have hRYZraw := YZFactorCap.normalizedFactor_YZ_cap
      Q RH.1 bchksZCap6399 hQ hm.1
        (fun j a ha => (hcaps j a ha).2.2)
    have hRYZ : YZCap RH.1 bchksFactorZMass6399 := by
      intro j a ha
      have hh := hRYZraw j a ha
      norm_num [bchksZCap6399, bchksFactorZMass6399] at hh ⊢
      omega
    simpa [G] using
      concreteUniversalAffineObstruction_degree_bounds x₀ RH.1
        bchksUniversalExponent6399 131071 RH.1.natDegree
        bchksFactorZMass6399 (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
        (by norm_num [bchksUniversalExponent6399,
          FiniteHenselWeight.denominatorExponent])
        (by norm_num) (by exact hm.2.1)
        (by norm_num [bchksFactorZMass6399]) hm.2.1 le_rfl hRYZ
  have hGroot : ∀ x₀ z RH, RH ∈ pairs Q x₀ →
      (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree →
      z ∈ S → pairRel PE x₀ z RH → ∀ i ∈ A z,
      biEval (G x₀ RH i) (Polynomial.eval x₀ (PE z)) z = 0 := by
    intro x₀ z RH hRH hdeg hzS hrel i hi
    have hm := pair_mem_facts Q x₀ RH hRH
    apply biEval_concreteUniversalAffineObstruction_eq_zero
      x₀ z (Polynomial.eval x₀ (PE z)) RH.1 (PE z)
      bchksUniversalExponent6399 131071
      (IRSProfile.domain i - x₀) (U 0 i) (U 1 i)
    · norm_num [bchksUniversalExponent6399,
        FiniteHenselWeight.denominatorExponent]
    · exact hm.2.1
    · rfl
    · exact hPEdeg z hzS
    · exact hrel.1
    · exact simple_slope_of_pairRel PE x₀ z RH.1 RH.2 hrel hdeg hm.2.1
    · have ha := hagree ⟨z, hzS⟩ i hi
      simpa [PE, hzS] using ha
  obtain ⟨x₀, RH, T, Coord, hRH, hx, hTS, hTcard, hCoord, hrel, hdiv⟩ :=
    exists_selected_pair_coordinate_divisibility S PE Q A G hScard hQ
      hPEeval hcaps hrow hGcaps hGroot
  exact ⟨x₀, RH, T, Coord, hRH, hx, hTS, hTcard, hCoord,
    by simpa [PE] using hrel, by simpa [G] using hdiv⟩

end UniversalConcreteSelection6399

end ProximityPrize.SubmissionLower
