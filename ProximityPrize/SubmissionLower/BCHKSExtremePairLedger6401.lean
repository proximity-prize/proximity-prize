import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusExtremeKernelCounter6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremeThreeRectangleProducer6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def extremePairIdentityCutoff6401 : Fin 3 → Fin 3 → ℕ := ![
  ![0, 185132, 185197],
  ![185132, 0, 185197],
  ![185197, 185197, 0]]
def extremePairLightThreshold6401 : Fin 3 → Fin 3 → ℕ := ![
  ![0, 18020, 18042],
  ![18020, 0, 18042],
  ![18042, 18042, 0]]
def extremePairSmallOwnerCap6401 (s t : Fin 3) : ℕ :=
  (n6401 * extremePairMismatchCap6401 s t +
      (a6401 - extremePairIdentityCutoff6401 s t) - 1) /
    (a6401 - extremePairIdentityCutoff6401 s t)
def extremePairLargeOwnerCap6401 (s t : Fin 3) : ℕ :=
  (n6401 * extremePairDenominatorCap6401 s t) /
      (extremePairLightThreshold6401 s t + 1) + 1182
theorem extremePairLedgers_exact6401 (s t : Fin 3) (hst : s ≠ t) :
    n6401 * extremePairMismatchCap6401 s t <
        weakCurveSeedInput6401 *
          (a6401 - extremePairIdentityCutoff6401 s t) ∧
      ownerDegreeCap6401 + 3 * extremePairLightThreshold6401 s t <
        extremePairIdentityCutoff6401 s t + 1 ∧
      extremePairSmallOwnerCap6401 s t < weakCurveSeedInput6401 ∧
      extremePairLargeOwnerCap6401 s t < weakCurveSeedInput6401 := by
  fin_cases s <;> fin_cases t <;>
    simp at hst ⊢ <;> native_decide
theorem extremePairLedgers_values6401 :
    extremePairSmallOwnerCap6401 0 1 = 273149494695030157 ∧
      extremePairSmallOwnerCap6401 0 2 = 273192362931368380 ∧
      extremePairSmallOwnerCap6401 1 2 = 273192362878313440 ∧
      extremePairLargeOwnerCap6401 0 1 = 3364918030204635 ∧
      extremePairLargeOwnerCap6401 0 2 = 2377165714140990 ∧
      extremePairLargeOwnerCap6401 1 2 = 2377165713679336 := by
  native_decide
end BCHKSExtremeThreeRectangleProducer6401
end ProximityPrize.SubmissionLower
