import ProximityPrize.SubmissionLower.BCHKSRaisedNumeratorEndpoint6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSHeterogeneousUniversalLedger6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSBranchwiseHybridAudit6400
def heterogeneousLowUniversalCoefficient6400 : Nat :=
  bchksHybridUniversalUnitCoefficient6400 * bchksHybridLowDegreeCap6400
lemma heterogeneous_low_coefficient_absorbed6400 :
    heterogeneousLowUniversalCoefficient6400 = 67082789 /\
      heterogeneousLowUniversalCoefficient6400 <
        branchwiseCoreFirstMissEffectiveCoefficient6400 /\
      branchwiseCoreFirstMissEffectiveCoefficient6400 -
          heterogeneousLowUniversalCoefficient6400 = 95708671 := by
  norm_num [heterogeneousLowUniversalCoefficient6400,
    bchksHybridUniversalUnitCoefficient6400,
    bchksHybridLowDegreeCap6400,
    branchwiseCoreFirstMissEffectiveCoefficient6400]
theorem heterogeneous_universal_charge_le_core390
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (high : R -> Prop) [DecidablePred high]
    (degree zDegree charge : R -> Nat)
    (hlowDegree : ∀ r ∈ Rs, Not (high r) ->
      degree r <= bchksHybridLowDegreeCap6400)
    (hlow : ∀ r ∈ Rs, Not (high r) ->
      charge r <= bchksHybridUniversalUnitCoefficient6400 *
        degree r * zDegree r)
    (hhigh : ∀ r ∈ Rs, high r ->
      charge r <= branchwiseCoreFirstMissEffectiveCoefficient6400 *
        zDegree r)
    (hzMass : (∑ r ∈ Rs, zDegree r) <= bchksHybridZMass6400) :
    (∑ r ∈ Rs, charge r) <=
      branchwiseCoreFirstMissEffectiveCoefficient6400 *
        bchksHybridZMass6400 := by
  have hterm : ∀ r ∈ Rs,
      charge r <= branchwiseCoreFirstMissEffectiveCoefficient6400 *
        zDegree r := by
    intro r hr
    by_cases hbranch : high r
    · exact hhigh r hr hbranch
    · refine (hlow r hr hbranch).trans ?_
      apply Nat.mul_le_mul_right (zDegree r)
      calc
        bchksHybridUniversalUnitCoefficient6400 * degree r <=
            bchksHybridUniversalUnitCoefficient6400 *
              bchksHybridLowDegreeCap6400 :=
          Nat.mul_le_mul_left _ (hlowDegree r hr hbranch)
        _ = heterogeneousLowUniversalCoefficient6400 := by
          rfl
        _ <= branchwiseCoreFirstMissEffectiveCoefficient6400 :=
          Nat.le_of_lt heterogeneous_low_coefficient_absorbed6400.2.1
  calc
    (∑ r ∈ Rs, charge r) <=
        ∑ r ∈ Rs,
          branchwiseCoreFirstMissEffectiveCoefficient6400 * zDegree r :=
      Finset.sum_le_sum hterm
    _ = branchwiseCoreFirstMissEffectiveCoefficient6400 *
        (∑ r ∈ Rs, zDegree r) := by
      rw [Finset.mul_sum]
    _ <= branchwiseCoreFirstMissEffectiveCoefficient6400 *
        bchksHybridZMass6400 :=
      Nat.mul_le_mul_left _ hzMass
def heterogeneousAllUniversalTotal6400 : Nat :=
  branchwiseCoreFirstMissEffectiveCoefficient6400 *
      bchksHybridZMass6400 +
    bchksHybridPairCardCover6400 + bchksHybridQBadCover6400
lemma heterogeneous_allUniversal_exact6400 :
    heterogeneousAllUniversalTotal6400 = 274950784013430375 /\
      heterogeneousAllUniversalTotal6400 < bchksWeightedNumerator6400 /\
      bchksWeightedNumerator6400 - heterogeneousAllUniversalTotal6400 =
        28215986569625 /\
      heterogeneousAllUniversalTotal6400 < bchksResidualNumerator6400 /\
      bchksResidualNumerator6400 - heterogeneousAllUniversalTotal6400 =
        29915986569625 := by
  norm_num [heterogeneousAllUniversalTotal6400,
    branchwiseCoreFirstMissEffectiveCoefficient6400,
    bchksHybridZMass6400, bchksHybridPairCardCover6400,
    bchksHybridQBadCover6400, bchksWeightedNumerator6400,
    bchksResidualNumerator6400]
theorem affineLineAlignmentBound_mono_threshold
    {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode I F) (e a b : Nat) (hab : a <= b)
    (h : AffineLineAlignmentBound C e a) :
    AffineLineAlignmentBound C e b := by
  intro U S A hS hA hcomb
  exact h U S A (hab.trans_lt hS) hA hcomb
end BCHKSHeterogeneousUniversalLedger6400
end ProximityPrize.SubmissionLower
