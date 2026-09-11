import ProximityPrize.SubmissionLower.PartG089


section Compact_SecondJetUniformReceipts
/-! Common characteristic and exceptional-count receipts for all three
second-jet profiles. The maximum source caps are (47,157,2233,21). -/
namespace ProximityPrize.SubmissionLower.SecondJetUniformReceipts
open SecondJetNumericGeometry RCN260 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem uniform_gates (r y t R U T : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 136) (ht : t ≤ 6917)
    (hR : R ≤ 656) (hU : U ≤ 2992) (hT : T ≤ 147469) :
    (parameters r y t R U T).mixedCost.y < 2130706433 ∧
    (parameters r y t R U T).mixedCost.r < 2130706433 ∧
    (parameters r y t R U T).mixedCost.z < 2130706433 := by
  have h := mixed_mono hr hy ht hR hU hT
  exact ⟨h.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.2.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost])⟩

theorem helper_gates (r y t B U L s : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 136) (ht : t ≤ 6917)
    (hB : B ≤ 47) (hU : U ≤ 157) (hL : L ≤ 2233) (hs : s ≤ 21) :
    (parameters r y t (B+s*(r-1)) (U+s*(y-1)) (L+s*(t-1))).mixedCost.y < 2130706433 ∧
    (parameters r y t (B+s*(r-1)) (U+s*(y-1)) (L+s*(t-1))).mixedCost.r < 2130706433 ∧
    (parameters r y t (B+s*(r-1)) (U+s*(y-1)) (L+s*(t-1))).mixedCost.z < 2130706433 := by
  apply uniform_gates _ _ _ _ _ _ hr hy ht
  · calc B+s*(r-1) ≤ 47+21*(30-1) := by gcongr
         _ = 656 := by decide
  · calc U+s*(y-1) ≤ 157+21*(136-1) := by gcongr
         _ = 2992 := by decide
  · calc L+s*(t-1) ≤ 2233+21*(6917-1) := by gcongr
         _ = 147469 := by decide

theorem coefficient_gates (r y t B U L : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 136) (ht : t ≤ 6917)
    (hB : B ≤ 47) (hU : U ≤ 157) (hL : L ≤ 2233) :
    (parameters r y t B U L).mixedCost.y < 2130706433 ∧
    (parameters r y t B U L).mixedCost.r < 2130706433 ∧
    (parameters r y t B U L).mixedCost.z < 2130706433 :=
  uniform_gates _ _ _ _ _ _ hr hy ht (by omega) (by omega) (by omega)

theorem coefficient_count (r y t B U L : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 136) (ht : t ≤ 6917)
    (hB : B ≤ 47) (hU : U ≤ 157) (hL : L ≤ 2233) :
    (parameters r y t B U L).regularCountCap ≤ 500000000000000 := by
  calc
    _ ≤ (parameters 30 136 6917 47 157 2233).regularCountCap := count_mono hr hy ht hB hU hL
    _ ≤ _ := by norm_num [parameters,UnequalParameters.regularCountCap,
      UnequalParameters.regularNumerator,UnequalParameters.agreement,UnequalParameters.leftAgreement,
      UnequalParameters.rightAgreement,UnequalParameters.mixedCost,UnequalParameters.errors,
      UnequalParameters.gap,RCN294.dot]

end ProximityPrize.SubmissionLower.SecondJetUniformReceipts

end Compact_SecondJetUniformReceipts
