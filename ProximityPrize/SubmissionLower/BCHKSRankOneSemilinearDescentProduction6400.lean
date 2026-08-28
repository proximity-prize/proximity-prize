import ProximityPrize.SubmissionLower.BCHKSRankOneReducedCompatibility6400
import ProximityPrize.SubmissionLower.BCHKSSemilinearPolynomialDescent6400

/-!
# Production semilinear descent in the rank-one branch

Away from the two leading-coefficient specialization loci, the primitive
rank-one lanes retain their common locator degree.  The production norm and
compatibility theorems can therefore be fed directly into exact semilinear
polynomial division.  This file also records the affordable size of the two
exceptional loci.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneSemilinearDescentProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSPrimitiveTripleRelation6400
open BCHKSPrimitiveTripleBicomponent6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSCyclicNormSpecialization6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSRankOneEffectiveNormProduction6400
open BCHKSEffectiveGlobalQuotient6400
open BCHKSRankOneReducedGlobalQuotient6400
open BCHKSRankOneReducedCompatibility6400
open BCHKSInhomogeneousCyclicCompatibility6400
open BCHKSSemilinearPolynomialDescent6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private abbrev CramerChallengeCap6400 : Nat := 76779 * 2130706433

theorem Score6400RankOneEffectiveDefectData.A_leadingCoeff_natDegree_le
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T) :
    data.A.leadingCoeff.natDegree ≤ CramerChallengeCap6400 := by
  have hH : data.H ≠ 0 := by
    have hpositive := data.H_positive
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hpositive
    omega
  simpa only [Polynomial.leadingCoeff] using
    (quotient_coeff_natDegree_le
      (score6400PolynomialLocatorRelationPair data.q).1.1
      data.H data.A CramerChallengeCap6400 data.A.natDegree
      data.A_factor hH data.A_ne
      (fun n ↦
        score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
          data.q CramerChallengeCap6400 n data.q_degree))

theorem Score6400RankOneEffectiveDefectData.B_leadingCoeff_natDegree_le
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T) :
    data.B.leadingCoeff.natDegree ≤ CramerChallengeCap6400 := by
  have hH : data.H ≠ 0 := by
    have hpositive := data.H_positive
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hpositive
    omega
  simpa only [Polynomial.leadingCoeff] using
    (quotient_coeff_natDegree_le
      (score6400PolynomialLocatorRelationPair data.q).2.1
      data.H data.B CramerChallengeCap6400 data.B.natDegree
      data.B_factor hH data.B_ne
      (fun n ↦
        score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
          data.q CramerChallengeCap6400 n data.q_degree))

/-- The specializations at which either primitive lane loses its locator
degree occupy at most two ordinary Cramer challenge-degree budgets. -/
theorem Score6400RankOneEffectiveDefectData.irregularSpecialization_card_le
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T) :
    (T.filter fun z ↦
      data.A.leadingCoeff.eval z = 0 ∨
        data.B.leadingCoeff.eval z = 0).card ≤
      2 * CramerChallengeCap6400 := by
  classical
  let ZA := T.filter fun z ↦ data.A.leadingCoeff.eval z = 0
  let ZB := T.filter fun z ↦ data.B.leadingCoeff.eval z = 0
  have hAlead : data.A.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr data.A_ne
  have hBlead : data.B.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr data.B_ne
  have hZA : ZA.card ≤ CramerChallengeCap6400 := by
    have hsubset : ZA ⊆ data.A.leadingCoeff.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hAlead]
      exact (Finset.mem_filter.mp hz).2
    calc
      ZA.card ≤ data.A.leadingCoeff.roots.toFinset.card :=
        Finset.card_le_card hsubset
      _ ≤ data.A.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ data.A.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ CramerChallengeCap6400 :=
        Score6400RankOneEffectiveDefectData.A_leadingCoeff_natDegree_le data
  have hZB : ZB.card ≤ CramerChallengeCap6400 := by
    have hsubset : ZB ⊆ data.B.leadingCoeff.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hBlead]
      exact (Finset.mem_filter.mp hz).2
    calc
      ZB.card ≤ data.B.leadingCoeff.roots.toFinset.card :=
        Finset.card_le_card hsubset
      _ ≤ data.B.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ data.B.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ CramerChallengeCap6400 :=
        Score6400RankOneEffectiveDefectData.B_leadingCoeff_natDegree_le data
  have hfilter :
      T.filter (fun z ↦ data.A.leadingCoeff.eval z = 0 ∨
        data.B.leadingCoeff.eval z = 0) = ZA ∪ ZB := by
    ext z
    simp only [ZA, ZB, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hfilter]
  exact (Finset.card_union_le ZA ZB).trans (by omega)

/-- Every regular retained specialization in the low, large-nullity
rank-one branch has an exact semilinear quotient and a compatible remainder
below the common primitive locator degree. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal_semilinear_remainder
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hTcard : ownerFloor ≤ T.card)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z)
    (z : IRSProfile.Field) (hz : z ∈ T)
    (hAregular : data.A.leadingCoeff.eval z ≠ 0)
    (hBregular : data.B.leadingCoeff.eval z ≠ 0) :
    let Az := data.A.map (Polynomial.evalRingHom z)
    let Bz := data.B.map (Polynomial.evalRingHom z)
    let Kz := (score6400ReducedGlobalQuotient data.Fixed data.K).map
      (Polynomial.evalRingHom z)
    ∃ Q : IRSProfile.Field[X],
      koalaCyclicCompatibilitySix Az Bz
          (Kz - koalaPolynomialSemilinear6400 Az Bz Q) = 0 ∧
        ((Kz - koalaPolynomialSemilinear6400 Az Bz Q) = 0 ∨
          (Kz - koalaPolynomialSemilinear6400 Az Bz Q).natDegree <
            data.A.natDegree) := by
  dsimp only
  let Az := data.A.map (Polynomial.evalRingHom z)
  let Bz := data.B.map (Polynomial.evalRingHom z)
  let Kz := (score6400ReducedGlobalQuotient data.Fixed data.K).map
    (Polynomial.evalRingHom z)
  have hglobalDegree := Score6400RankOneEffectiveDefectData.locatorDegree_eq
    data hLlarge hTcard hAdirection hbad hnotOld
  have hAzDegree : Az.natDegree = data.A.natDegree := by
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom z) hAregular
  have hBzDegree : Bz.natDegree = data.B.natDegree := by
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom z) hBregular
  have hAz : Az ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun P : IRSProfile.Field[X] ↦ P.coeff data.A.natDegree) hzero
    have hmap : (Polynomial.evalRingHom z) data.A.leadingCoeff = 0 := by
      simpa only [Az, Polynomial.coeff_map, Polynomial.coeff_natDegree,
        Polynomial.coeff_zero] using hcoeff
    change data.A.leadingCoeff.eval z = 0 at hmap
    exact hAregular hmap
  have hBz : Bz ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun P : IRSProfile.Field[X] ↦ P.coeff data.B.natDegree) hzero
    have hmap : (Polynomial.evalRingHom z) data.B.leadingCoeff = 0 := by
      simpa only [Bz, Polynomial.coeff_map, Polynomial.coeff_natDegree,
        Polynomial.coeff_zero] using hcoeff
    change data.B.leadingCoeff.eval z = 0 at hmap
    exact hBregular hmap
  have hdegree : Az.natDegree = Bz.natDegree := by
    rw [hAzDegree, hBzDegree, hglobalDegree]
  have hnorm := Score6400RankOneEffectiveDefectData.specializedNorm_eq
    data hLlarge hAdirection hbad hnotOld z hz
  have hcompat :=
    Score6400RankOneEffectiveDefectData.reducedGlobal_compatibility_eq_zero
      data hLlarge hAdirection hbad hnotOld z hz
  obtain ⟨Q, hQcompat, hQremainder⟩ :=
    exists_koalaPolynomialSemilinear_remainder6400
      Az Bz Kz hAz hBz hdegree hnorm hcompat
  refine ⟨Q, hQcompat, ?_⟩
  rcases hQremainder with hzero | hdegreeLow
  · exact Or.inl hzero
  · exact Or.inr (by simpa only [hAzDegree] using hdegreeLow)

end BCHKSRankOneSemilinearDescentProduction6400
end ProximityPrize.SubmissionLower
