import ProximityPrize.SubmissionLower.BCHKSTopEdgeSplitJetCap6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSRaisedNumeratorEndpoint6400

open BCHKSTopEdgeSplitJetCap6400

/-!
The earlier hybrid audits compared the cover against the deliberately rounded
working numerator `274979000000000000`.  The field-capacity inequality permits
the already-defined safe residual numerator `274980700000000000`.  No
interpolation parameter changes when the large-set case is split at this
higher threshold.

At the first residual common-core profile (`390` full-order coordinates), the
split `G/H` jet ledger is therefore inside the actual safe field budget by
more than `1.5 * 10^12` seeds.
-/

def raisedCore390Headroom6400 : Nat := 1589445535109

/-- The exact field-capacity ceiling after subtracting the list term. -/
def exactFieldSeedCeiling6400 : Nat := 274980728111352763

lemma exactFieldSeedCeiling_eq6400 :
    exactFieldSeedCeiling6400 =
      (2130706433 : Nat) ^ 6 / 2 ^ (128 : Nat) - bchksListBound6400 := by
  norm_num [exactFieldSeedCeiling6400, bchksListBound6400]

/-- The rounded residual numerator leaves a further `28,111,352,763` seeds
below the exact integer ceiling. -/
lemma residualNumerator_below_exactCeiling6400 :
    bchksResidualNumerator6400 < exactFieldSeedCeiling6400 /\
      exactFieldSeedCeiling6400 - bchksResidualNumerator6400 =
        28111352763 := by
  norm_num [bchksResidualNumerator6400, exactFieldSeedCeiling6400]

/-- Corrected endpoint: the core-390 split ledger fits the safe numerator,
and that numerator satisfies the exact 128-bit field budget. -/
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

/-- Any strict large-set hypothesis at the raised threshold may be replaced
by an exact-cardinality subset.  All pointwise hypotheses on the original
seed set restrict automatically to this subset; downstream root covers and
interpolation only use membership in the chosen set. -/
theorem exists_seedSubset_card_residualNumerator_succ
    {F : Type*} [DecidableEq F] (S : Finset F)
    (hS : bchksResidualNumerator6400 < S.card) :
    exists T : Finset F, T ⊆ S /\
      T.card = bchksResidualNumerator6400 + 1 := by
  have hcard : bchksResidualNumerator6400 + 1 <= S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨T, hTS, hTcard⟩

/-- Pointwise owner/agreement hypotheses survive the exact-cardinality
restriction used above. -/
theorem restrict_pointwise_to_seedSubset
    {F : Type*} [DecidableEq F] {S T : Finset F} (hTS : T ⊆ S)
    {P : F -> Prop} (hP : ∀ z ∈ S, P z) :
    ∀ z ∈ T, P z := by
  intro z hz
  exact hP z (hTS hz)

end BCHKSRaisedNumeratorEndpoint6400
end ProximityPrize.SubmissionLower
