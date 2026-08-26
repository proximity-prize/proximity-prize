import ProximityPrize.SubmissionLower.BCHKSTopEdgeSplitJetCap6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSRaisedNumeratorEndpoint6400
open BCHKSTopEdgeSplitJetCap6400
def raisedCore390Headroom6400 : Nat := 1589445535109
def exactFieldSeedCeiling6400 : Nat := 274980728111352763
lemma exactFieldSeedCeiling_eq6400 :
    exactFieldSeedCeiling6400 =
      (2130706433 : Nat) ^ 6 / 2 ^ (128 : Nat) - bchksListBound6400 := by
  norm_num [exactFieldSeedCeiling6400, bchksListBound6400]
lemma residualNumerator_below_exactCeiling6400 :
    bchksResidualNumerator6400 < exactFieldSeedCeiling6400 /\
      exactFieldSeedCeiling6400 - bchksResidualNumerator6400 =
        28111352763 := by
  norm_num [bchksResidualNumerator6400, exactFieldSeedCeiling6400]
lemma branchwiseSplit_core390_raisedNumerator_fits6400 :
    branchwiseSplitCore390Total6400 < bchksResidualNumerator6400 /\
      bchksResidualNumerator6400 - branchwiseSplitCore390Total6400 =
        raisedCore390Headroom6400 /\
      2 ^ (128 : Nat) *
          (bchksResidualNumerator6400 + bchksListBound6400) <=
        (2130706433 : Nat) ^ 6 := by
  norm_num [branchwiseSplitCore390Total6400,
    bchksResidualNumerator6400, raisedCore390Headroom6400,
    bchksListBound6400]
theorem exists_seedSubset_card_residualNumerator_succ
    {F : Type*} [DecidableEq F] (S : Finset F)
    (hS : bchksResidualNumerator6400 < S.card) :
    exists T : Finset F, T ⊆ S /\
      T.card = bchksResidualNumerator6400 + 1 := by
  have hcard : bchksResidualNumerator6400 + 1 <= S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨T, hTS, hTcard⟩
theorem restrict_pointwise_to_seedSubset
    {F : Type*} [DecidableEq F] {S T : Finset F} (hTS : T ⊆ S)
    {P : F -> Prop} (hP : ∀ z ∈ S, P z) :
    ∀ z ∈ T, P z := by
  intro z hz
  exact hP z (hTS hz)
end BCHKSRaisedNumeratorEndpoint6400
end ProximityPrize.SubmissionLower
