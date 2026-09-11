import ProximityPrize.SubmissionLower.Part.G081


section Compact_SecondJetRelaxedRanksReceipt
/-! Kernel-checked concrete local rank counts. The geometric use of the
resulting interpolants is a separate theorem obligation. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt
open SecondJetRelaxedCounts SecondJetRelaxedCoefficientsReceipt
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem rank_116 : rankBound 116 2233 47 21 157 = 5982635361 := by decide

theorem rank_96 : rankBound 96 2141 38 17 130 = 2658383500 := by decide

theorem rank_108 : rankBound 108 2111 41 19 146 = 3889536981 := by decide

theorem exact_rank_116 :
    SecondJetRelaxedGlobalMap.rankBound 116 2233 47 21 157
      (fun h => (cutoff 116 5 7 h+47-1)/131071) = 5982635361 := by
  rw [rankBound_eq_closed _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (fun h hh => caps_116 ⟨h,by omega⟩), rank_116]

theorem exact_rank_96 :
    SecondJetRelaxedGlobalMap.rankBound 96 2141 38 17 130
      (fun h => (cutoff 96 4 5 h+38-1)/131071) = 2658383500 := by
  rw [rankBound_eq_closed _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (fun h hh => caps_96 ⟨h,by omega⟩), rank_96]

theorem exact_rank_108 :
    SecondJetRelaxedGlobalMap.rankBound 108 2111 41 19 146
      (fun h => (cutoff 108 4 7 h+41-1)/131071) = 3889536981 := by
  rw [rankBound_eq_closed _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (fun h hh => caps_108 ⟨h,by omega⟩), rank_108]

end ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt

end Compact_SecondJetRelaxedRanksReceipt
