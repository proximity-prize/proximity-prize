import ProximityPrize.SubmissionLower.LocatorReplacementDataFine0
import ProximityPrize.SubmissionLower.LocatorReplacementDataFine1
import ProximityPrize.SubmissionLower.LocatorReplacementDataFine2
import ProximityPrize.SubmissionLower.LocatorReplacementDataFine3
import ProximityPrize.SubmissionLower.LocatorReplacementDataUnit10
import ProximityPrize.SubmissionLower.LocatorReplacementDataUnit11
import ProximityPrize.SubmissionLower.LocatorReplacementDataUnit12
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_fine (c:FineCell):Receipt (Sum.inr (Sum.inl c)):=by
  by_cases h8:fineR c≤8
  · exact receipt_fine_le8 c h8
  by_cases h9:fineR c=9
  · exact receipt_fine_r9 c h9
  by_cases h10:fineR c=10
  · exact receipt_fine_r10 c h10
  exact receipt_fine_ge11 c (by omega)

theorem receipt_unit (c:UnitCell):Receipt (Sum.inr (Sum.inr c)):=by
  have h:=c.parent.2
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r10 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r11 c (by simp only [unitR]; omega)
  · exact receipt_unit_r12 c (by simp only [unitR]; omega)
end ProximityPrize.SubmissionLower.LocatorReplacementData
