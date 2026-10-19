import ProximityPrize.SubmissionBinaryLower.BCHKSConcreteGoodSpecialization
import ProximityPrize.SubmissionBinaryLower.BCHKSFactorPigeon

/-!
# Pair vocabulary for the universal-numerator route

The definitions shared by the universal selection files: nested factor pairs
`(R, H)` with `H` a positive normalized factor of `R(x₀, Y, Z)`, and the
relation recorded for a selected challenge.
-/

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace UniversalOuterCover6399

abbrev F := BinaryIRSProfile.Field
abbrev TriPoly := Polynomial (Polynomial (Polynomial F))
abbrev BiPoly := Polynomial (Polynomial F)
abbrev Pair := TriPoly × BiPoly

noncomputable def outerFactors (Q : TriPoly) : Finset TriPoly :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)

noncomputable def pairs (Q : TriPoly) (x₀ : F) : Finset Pair :=
  positiveNormalizedFactorPairs Q x₀

/-- The relation retained by pigeonholing: both root identities, the outer
obstruction at this seed, and nonvanishing of the specialized outer factor. -/
def pairRel (Pz : F → Polynomial F) (x₀ z : F) (RH : Pair) : Prop :=
  triEval RH.1 z (Pz z) = 0 ∧
  biEval RH.2 (Polynomial.eval x₀ (Pz z)) z = 0 ∧
  Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (factorXObstruction RH.1)) ≠ 0 ∧
  biSpecializeZ (triSpecializeX RH.1 x₀) z ≠ 0

/-- Membership in the pair finset exposes the normalized-factor and
divisibility facts required by the fixed-pair consumer. -/
theorem pair_mem_facts
    (Q : TriPoly) (x₀ : F) (RH : Pair) (hRH : RH ∈ pairs Q x₀) :
    RH.1 ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
    0 < RH.1.natDegree ∧
    RH.2 ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX RH.1 x₀) ∧
    0 < RH.2.natDegree ∧ RH.2 ∣ triSpecializeX RH.1 x₀ := by
  simp only [pairs, positiveNormalizedFactorPairs, Finset.mem_biUnion,
    Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter] at hRH
  obtain ⟨R, hRQ, H, ⟨hHB, hHpos⟩, heq⟩ := hRH
  cases heq
  have hB : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    simpa [hz] using hHB
  have hHdeg : H.natDegree ≤ (triSpecializeX R x₀).natDegree := by
    calc
      H.natDegree ≤ ∑ J ∈
          (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R x₀)).toFinset, J.natDegree :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hHB)
      _ ≤ (triSpecializeX R x₀).natDegree :=
        normalizedFactors_toFinset_sum_natDegree_le _ hB
  have hRpos : 0 < R.natDegree := by
    have := hHdeg.trans (triSpecializeX_natDegree_le R x₀)
    omega
  exact ⟨hRQ, hRpos, hHB, hHpos,
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHB⟩

end UniversalOuterCover6399

end ProximityPrize.SubmissionBinaryLower
