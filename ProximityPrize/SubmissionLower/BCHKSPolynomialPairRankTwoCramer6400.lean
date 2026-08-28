import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantRankTwo6400
import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantCramerBridge6400

/-!
# Rank-two polynomial pairs give a bounded Cramer obstruction

This module composes the sharp rank-two determinant theorem with the
fraction-field span bridge.  Once the retained polynomial-pair family has
dimension `L`, rational rank two, and `c + h - L < l`, the original pairwise
determinant candidates have the strict high-part rank drop needed by the
bounded Cramer construction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

variable {F : Type} [Field F]

theorem exists_bounded_locatorCramerObstruction_of_pair_span_rank_two_with_span
    {I : Type} [Fintype I]
    {c h D l S L : ℕ} (A B : I → F[X][X])
    (hc : 0 < c) (hh : 0 < h) (hLd : L ≤ c + h)
    (hcut : c + h - L < l)
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (hbounded : ∀ ij, locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ ij n,
      ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤ S)
    (hlD : l ≤ D)
    (hVrank : Module.finrank (FractionRing F[X])
      (Submodule.span (FractionRing F[X])
        (Set.range (locatorPairFamilyFraction c h A B hA hB))) = L)
    (hrankTwo : ∃ u v : Submodule.span (FractionRing F[X])
        (Set.range (locatorPairFamilyFraction c h A B hA hB)),
      polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X]
        (Set.range (locatorPairDetCandidate A B)) := by
  let K := FractionRing F[X]
  let family : I → PolynomialPairSpace K c h :=
    locatorPairFamilyFraction c h A B hA hB
  let V : Submodule K (PolynomialPairSpace K c h) :=
    Submodule.span K (Set.range family)
  have hVrank' : Module.finrank K V = L := by
    simpa [K, V, family] using hVrank
  have hrankTwo' : ∃ u v : V, polynomialPairDet u.1 v.1 ≠ 0 := by
    simpa [K, V, family] using hrankTwo
  obtain ⟨u, v, hdetne, hdetdegree⟩ :=
    exists_low_degree_pairDet_of_rank_two c h L hc hh hLd
      V hVrank' hrankTwo'
  have hdetdegree' : (polynomialPairDet u.1 v.1).natDegree < l :=
    hdetdegree.trans_lt hcut
  exact exists_bounded_locatorCramerObstruction_of_pair_span_det_with_span
    A B hA hB hbounded hcoeff hlD u.1 v.1 u.2 v.2
      hdetne hdetdegree'

/-- Compatibility wrapper which forgets pair-determinant span membership. -/
theorem exists_bounded_locatorCramerObstruction_of_pair_span_rank_two
    {I : Type} [Fintype I]
    {c h D l S L : ℕ} (A B : I → F[X][X])
    (hc : 0 < c) (hh : 0 < h) (hLd : L ≤ c + h)
    (hcut : c + h - L < l)
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (hbounded : ∀ ij, locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ ij n,
      ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤ S)
    (hlD : l ≤ D)
    (hVrank : Module.finrank (FractionRing F[X])
      (Submodule.span (FractionRing F[X])
        (Set.range (locatorPairFamilyFraction c h A B hA hB))) = L)
    (hrankTwo : ∃ u v : Submodule.span (FractionRing F[X])
        (Set.range (locatorPairFamilyFraction c h A B hA hB)),
      polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_pair_span_rank_two_with_span
      A B hc hh hLd hcut hA hB hbounded hcoeff hlD hVrank hrankTwo
  exact ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower
