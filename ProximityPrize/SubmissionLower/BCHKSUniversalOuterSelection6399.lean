import ProximityPrize.SubmissionLower.BCHKSUniversalOuterCover6399
import ProximityPrize.SubmissionLower.BCHKSUniversalSelection6399
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace UniversalOuterSelection6399

open UniversalOuterCover6399

/-- Generic outer assembly for the universal-numerator route.  Once a caller
supplies one branch-independent bivariate obstruction `G x₀ RH i` per nested
factor pair and RS coordinate, together with its degree and common-root facts,
the global ledger selects one pair and proves that its inner factor divides
`G` at `k+1` coordinates. -/
theorem exists_selected_pair_coordinate_divisibility
    (S : Finset F) (Pz : F → Polynomial F) (Q : TriPoly)
    (Arow : F → Finset IRSProfile.Index)
    (G : F → Pair → IRSProfile.Index → BiPoly)
    (hS : bchksNumerator6399 < S.card)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (Pz z) = 0)
    (hcaps : SupportCaps Q)
    (hrow : ∀ z ∈ S,
      262144 - bchksErrors6399 ≤ (Arow z).card)
    (hGcaps : ∀ x₀ RH, RH ∈ pairs Q x₀ → ∀ i,
      (G x₀ RH i).natDegree ≤
          bchksUniversalExponent6399 * RH.1.natDegree ∧
      Bivariate.degreeX (G x₀ RH i) ≤
          bchksUniversalExponent6399 * bchksFactorZMass6399)
    (hGroot : ∀ x₀ z RH, RH ∈ pairs Q x₀ →
      (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree →
      z ∈ S → pairRel Pz x₀ z RH → ∀ i ∈ Arow z,
      biEval (G x₀ RH i) (Polynomial.eval x₀ (Pz z)) z = 0) :
    ∃ x₀ : F, ∃ RH : Pair, ∃ T : Finset F,
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
      (∀ z ∈ T, pairRel Pz x₀ z RH) ∧
      (∀ i ∈ Coord, RH.2 ∣ G x₀ RH i) := by
  classical
  obtain ⟨x₀, hqBad, houterBad, hpairs, hx₀, hcover⟩ :=
    exists_outer_pair_cover S Pz Q hQ hQeval hcaps
  let rdeg : Pair → ℕ := universalPairResultantCapacity
    bchksUniversalExponent6399 bchksFactorZMass6399
  have hQdeg : Q.natDegree ≤ bchksFactorMass6399 :=
    natDegree_le_factorMass Q hQ hcaps
  have hBZ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      Bivariate.degreeX (triSpecializeX R x₀) ≤ bchksFactorZMass6399 := by
    intro R hRQ
    apply normalizedFactor_triSpecializeX_degreeX_le Q R x₀
      bchksFactorZMass6399 hQ hRQ
    intro j a hja
    have hz := (hcaps j a hja).2.2
    norm_num [bchksFactorZMass6399] at hz ⊢
    exact hz
  have hsum : (∑ RH ∈ pairs Q x₀, rdeg RH) ≤
      2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
        bchksFactorZMass6399 + bchksFactorMass6399 := by
    have hsharp := positiveNormalizedFactorPairs_universal_capacity_le
      Q hQ x₀ bchksUniversalExponent6399 bchksFactorZMass6399
      bchksFactorMass6399 hQdeg hBZ
    exact hsharp.trans (Nat.le_add_right _ _)
  obtain ⟨RH, hRH, hincidence, hTcard⟩ :=
    exists_large_universal_pair_6399 S (qBad S Q) (outerFactors Q)
      (outerBad x₀) (pairs Q x₀) (pairRel Pz x₀) rdeg hS hqBad
      houterBad hsum hpairs hcover
  let T : Finset F :=
    (S \ (qBad S Q ∪ (outerFactors Q).biUnion (outerBad x₀))).filter
      fun z => pairRel Pz x₀ z RH
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrel : ∀ z ∈ T, pairRel Pz x₀ z RH := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hxSelected :
      (triSpecializeX RH.1 x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₀ ≠ 0 ∧
        (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₀)
          (rawSepResultant RH.1) ≠ 0 := by
    have hm := pair_mem_facts Q x₀ RH hRH
    have houter : RH.1 ∈ outerFactors Q :=
      Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hm.1, hm.2.1⟩
    exact hx₀ RH.1 houter
  have hrowT : ∀ z ∈ T,
      262144 - bchksErrors6399 ≤ (Arow z).card := by
    intro z hz
    exact hrow z (hTsub hz)
  obtain ⟨Coord, hCoord, hlarge⟩ :=
    exists_large_universal_coordinates_6399 T Arow (rdeg RH) hrowT
      (by simpa [T] using hincidence)
  let Res : IRSProfile.Index → F[X] := fun i =>
    Polynomial.resultant (G x₀ RH i) RH.2
      (G x₀ RH i).natDegree RH.2.natDegree
  have hResdeg : ∀ i ∈ Coord, (Res i).natDegree ≤ rdeg RH := by
    intro i hi
    have hg := hGcaps x₀ RH hRH i
    calc
      (Res i).natDegree ≤
          RH.2.natDegree * Bivariate.degreeX (G x₀ RH i) +
            (G x₀ RH i).natDegree * Bivariate.degreeX RH.2 :=
        bivariate_resultant_natDegree_le (G x₀ RH i) RH.2
          (G x₀ RH i).natDegree RH.2.natDegree
      _ ≤ RH.2.natDegree *
            (bchksUniversalExponent6399 * bchksFactorZMass6399) +
          (bchksUniversalExponent6399 * RH.1.natDegree) *
            Bivariate.degreeX RH.2 := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left RH.2.natDegree hg.2)
          (Nat.mul_le_mul_right (Bivariate.degreeX RH.2) hg.1)
      _ = rdeg RH := by
        rfl
  have hResroot : ∀ i ∈ Coord, ∀ z ∈ T, i ∈ Arow z →
      (Res i).eval z = 0 := by
    intro i hi z hzT hiz
    have hpair := hrel z hzT
    have hsize : 0 < (G x₀ RH i).natDegree + RH.2.natDegree := by
      have hfacts := pair_mem_facts Q x₀ RH hRH
      exact Nat.add_pos_right _ hfacts.2.2.2.1
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (G x₀ RH i) RH.2 (G x₀ RH i).natDegree RH.2.natDegree
      z (Polynomial.eval x₀ (Pz z))
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize
      (hGroot x₀ z RH hRH hxSelected.2.2.2.1 (hTsub hzT) hpair i hiz)
      hpair.2.1
  have hReszero : ∀ i ∈ Coord, Res i = 0 :=
    universal_coordinate_obstructions_eq_zero T Arow Coord (rdeg RH) Res
      hlarge hResdeg hResroot
  have hdiv : ∀ i ∈ Coord, RH.2 ∣ G x₀ RH i := by
    intro i hi
    have hfacts := pair_mem_facts Q x₀ RH hRH
    have hHi :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor RH.2
        hfacts.2.2.1).irreducible
    apply irreducible_dvd_of_resultant_eq_zero_nonmonic
      (G x₀ RH i) RH.2 hHi hfacts.2.2.2.1
    simpa only [Res] using hReszero i hi
  exact ⟨x₀, RH, T, Coord, hRH, hxSelected, hTsub,
    by simpa [T] using hTcard,
    hCoord, hrel, hdiv⟩

end UniversalOuterSelection6399

end ProximityPrize.SubmissionLower
