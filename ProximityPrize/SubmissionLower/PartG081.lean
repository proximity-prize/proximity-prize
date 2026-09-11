import ProximityPrize.SubmissionLower.PartG080


section Compact_SecondJetRelaxedCoefficientsReceipt
/-! Exact global coefficient dimensions for the three exploratory profiles.
Local rank values and geometric use are separate obligations. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def cutoff (m k n0 h : ℕ) : ℕ := m*181353-reserve k n0 h*50284

theorem coefficient_116 : coefficientCount (cutoff 116 5 7) 131071 2233 47 21 157 =
    1568312109846347 := by decide

theorem coefficient_96 : coefficientCount (cutoff 96 4 5) 131071 2141 38 17 130 =
    696880613507366 := by decide

theorem coefficient_108 : coefficientCount (cutoff 108 4 7) 131071 2111 41 19 146 =
    1019620196403719 := by decide

theorem caps_116 : ∀ h : Fin 22, 157 ≤ (cutoff 116 5 7 h.val+47-1)/131071 := by decide
theorem caps_96 : ∀ h : Fin 18, 130 ≤ (cutoff 96 4 5 h.val+38-1)/131071 := by decide
theorem caps_108 : ∀ h : Fin 20, 146 ≤ (cutoff 108 4 7 h.val+41-1)/131071 := by decide

theorem card_116 : Fintype.card (Index (cutoff 116 5 7) 131071 2233 47 21 157) =
    1568312109846347 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide), coefficient_116]

theorem card_96 : Fintype.card (Index (cutoff 96 4 5) 131071 2141 38 17 130) =
    696880613507366 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide), coefficient_96]

theorem card_108 : Fintype.card (Index (cutoff 108 4 7) 131071 2111 41 19 146) =
    1019620196403719 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide), coefficient_108]

end ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt

end Compact_SecondJetRelaxedCoefficientsReceipt
