import ProximityPrize.SubmissionLower.PrimaryTaperRankData
import ProximityPrize.SubmissionLower.ThetaPrimary

set_option Elab.async false
set_option maxHeartbeats 2400000

namespace CutterTaperTheta
open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open TaperBudget (cap cap_antitone tailSaving power fastSavings_le sumChunk_eq_fastSavings)
open private fees fees_le_baseline saved_by_fees from ProximityPrize.SubmissionLower.PrimaryTaperBudget
open private sum_checked from ProximityPrize.SubmissionLower.PrimaryTaperRankData
open private combine baseline_budget_on sum_add_pointwise_eq from ProximityPrize.SubmissionLower.Fast022

abbrev localRank : ℕ := 343784081800064

private abbrev z : BlockIndex → Powers := ThetaPrimary.zeroPowers

private def combined (p : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if i.1.val < 3012 then ThetaPrimary.bound (combine z z p z) i else fees z z p i

theorem thinned_fee (p : BlockIndex → Powers) (i : BlockIndex) :
    combined p i + ThetaSum.stripSave i = fees z z p i := by
  by_cases hi : i.1.val < 3012
  · have hj : i.1.val < 3514 := by omega
    have he : combine z z p z i = ⟨0, 0, 0⟩ := by
      unfold combine z ThetaPrimary.zeroPowers
      split_ifs <;> first | rfl | omega
    have hf : fees z z p i = baseline i := by
      rw [fees, if_pos hj]
      change blockBound i (combine z z p z i).expand = baseline i
      rw [he, ThetaPrimary.expand_zero] <;> rfl
    have hc : combined p i = min (baseline i) (ThetaSum.thetaBound i) := by
      rw [combined, if_pos hi, ThetaPrimary.bound, if_pos hi]
    rw [hc, ThetaSum.stripSave, if_pos hi, ThetaSum.thetaSave, hf]
    exact Nat.add_sub_of_le (min_le_left ..)
  · simp only [combined, ThetaSum.stripSave, if_neg hi, Nat.add_zero]

/-- Theta savings below grade 3012 and the tapered receipts above grade 3513
apply to disjoint blocks of the same primary source. -/
theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  classical
  obtain ⟨p, hp⟩ := K1_13_2_3_6.proof
  have h₂ := K1_13_2_2_2.proof
  have h₃ := K1_13_2_2_3.proof
  have h₄ := K1_13_2_2_4.proof
  have h₅ := K1_13_2_2_5.proof
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  refine (TaperNormalize.rank_le_of_blocks cap_antitone x y (combined p) ?_).trans ?_
  · intro i
    have ho := Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
    unfold combined
    split
    · exact ho.trans (ThetaPrimary.block_le hBlock _ i)
    · unfold fees
      split
      · exact ho.trans (hBlock i _)
      · exact le_min (ho.trans (hBlock i _))
          (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
  have hbase := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have ht : 396610034658 ≤ ∑ i : BlockIndex, tailSaving i := by
    have h := fastSavings_le (J := 600) (by decide)
    rw [← sumChunk_eq_fastSavings, sum_checked] at h
    exact h
  have htheta := ThetaSum.total_le
  have hsaved := saved_by_fees z z p
  have hsum := sum_add_pointwise_eq Finset.univ (fees z z p)
    (fun i => baseline i - fees z z p i) baseline
    (fun i _ => Nat.add_sub_of_le (fees_le_baseline z z p i))
  have hdiscount : (∑ i, combined p i) + (∑ i, ThetaSum.stripSave i) = ∑ i, fees z z p i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => thinned_fee p i
  unfold localRank
  omega

end CutterTaperTheta
