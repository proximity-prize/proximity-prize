import ProximityPrize.SubmissionLower.KoalaTaperTransfer
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRaw
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3

set_option Elab.async false
namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative

theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap)))≤localRank:=by
  apply node_rank_of_receipts x y
  · rw [rawWindow_w2,rawWindow_w3]
  · have h2 := debit_le_binCompute w2 (by decide)
    have h3:=debit_le_binCompute w3 (by decide)
    rw [binCompute2] at h2
    rw [binCompute3] at h3
    omega

#print axioms node_rank
end KoalaTaperTransfer
