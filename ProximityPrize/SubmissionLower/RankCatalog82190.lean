import ProximityPrize.SubmissionLower.RankRows82190G0
import ProximityPrize.SubmissionLower.RankRows82190G1
import ProximityPrize.SubmissionLower.RankRows82190G2
import ProximityPrize.SubmissionLower.RankRows82190G3
import ProximityPrize.SubmissionLower.RankRows82190G4
import ProximityPrize.SubmissionLower.RankRows82190G5
import ProximityPrize.SubmissionLower.RankRows82190G6
import ProximityPrize.SubmissionLower.RankRows82190G7
import ProximityPrize.SubmissionLower.RankRows82190G8
import ProximityPrize.SubmissionLower.RankRows82190G9
import ProximityPrize.SubmissionLower.RankRows82190G10
import ProximityPrize.SubmissionLower.RankRows82190G11
import ProximityPrize.SubmissionLower.RankRows82190G12
import ProximityPrize.SubmissionLower.RankRows82190G13
import ProximityPrize.SubmissionLower.RankRows82190G14
import ProximityPrize.SubmissionLower.RankRows82190G15
import ProximityPrize.SubmissionLower.RankRows82190G16
import ProximityPrize.SubmissionLower.RankRows82190G17
import ProximityPrize.SubmissionLower.RankRows82190G18
import ProximityPrize.SubmissionLower.RankRows82190G19

set_option Elab.async false
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000
namespace RankRows82190

def catalog : List Row := rows0 ++ rows1 ++ rows2 ++ rows3 ++ rows4 ++ rows5 ++ rows6 ++ rows7 ++ rows8 ++ rows9 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19

theorem good (r : Row) (hr : r ∈ catalog) : r.good 48 = true := by
  apply List.all_eq_true.mp _ r hr
  simp only [catalog, List.all_append, good0, good1, good2, good3, good4, good5, good6, good7, good8, good9, good10, good11, good12, good13, good14, good15, good16, good17, good18, good19, Bool.and_self]

theorem sorted : catalog.Pairwise (fun a b => a.tag < b.tag) := by
  have h : (catalog.map Row.tag).IsChain (· < ·) := by decide +kernel
  exact List.pairwise_map.mp (List.isChain_iff_pairwise.mp h)

#print axioms sorted
end RankRows82190
