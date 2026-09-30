import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_056
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source60 : Parameters := ⟨112,3686,45,20,152,5,7⟩
theorem shape60 : Shape source60 := by constructor <;> decide +kernel
theorem middle60 (h : ℕ) (hh : h≤20) : 152≤(source60.cutoff h+45-1)/131071 := by
  simp only [source60,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients60 :
    SecondJetRelaxedGlobalCounts.coefficientCount source60.cutoff 131071 3686 45 20 152=2249479125216988 := by
  decide +kernel
theorem rank60 : SecondJetRelaxedCounts.rankBound 112 3686 45 20 152=8581076106 := by decide +kernel
theorem dimension60 : Dimension source60 1510485724 := by
  exact dimension_of_counts source60 1510485724 2249479125216988 8581076106
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle60 coefficients60 rank60 (by decide)
def source61 : Parameters := ⟨113,3378,46,21,153,5,7⟩
theorem shape61 : Shape source61 := by constructor <;> decide +kernel
theorem middle61 (h : ℕ) (hh : h≤21) : 153≤(source61.cutoff h+46-1)/131071 := by
  simp only [source61,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients61 :
    SecondJetRelaxedGlobalCounts.coefficientCount source61.cutoff 131071 3378 46 21 153=2184636438284102 := by
  decide +kernel
theorem rank61 : SecondJetRelaxedCounts.rankBound 113 3378 46 21 153=8333726260 := by decide +kernel
theorem dimension61 : Dimension source61 101582662 := by
  exact dimension_of_counts source61 101582662 2184636438284102 8333726260
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle61 coefficients61 rank61 (by decide)
def source62 : Parameters := ⟨114,3146,47,21,154,5,7⟩
theorem shape62 : Shape source62 := by constructor <;> decide +kernel
theorem middle62 (h : ℕ) (hh : h≤21) : 154≤(source62.cutoff h+47-1)/131071 := by
  simp only [source62,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients62 :
    SecondJetRelaxedGlobalCounts.coefficientCount source62.cutoff 131071 3146 47 21 154=2137585483518867 := by
  decide +kernel
theorem rank62 : SecondJetRelaxedCounts.rankBound 114 3146 47 21 154=8154240246 := by decide +kernel
theorem dimension62 : Dimension source62 328471443 := by
  exact dimension_of_counts source62 328471443 2137585483518867 8154240246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle62 coefficients62 rank62 (by decide)
def source63 : Parameters := ⟨120,1405,54,25,164,4,5⟩
theorem shape63 : Shape source63 := by constructor <;> decide +kernel
theorem middle63 (h : ℕ) (hh : h≤25) : 164≤(source63.cutoff h+54-1)/131071 := by
  simp only [source63,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients63 :
    SecondJetRelaxedGlobalCounts.coefficientCount source63.cutoff 131071 1405 54 25 164=1311372005594373 := by
  decide +kernel
theorem rank63 : SecondJetRelaxedCounts.rankBound 120 1405 54 25 164=4999133419 := by decide +kernel
theorem dimension63 : Dimension source63 879174604037 := by
  exact dimension_of_counts source63 879174604037 1311372005594373 4999133419
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle63 coefficients63 rank63 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
