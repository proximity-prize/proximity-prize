import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_064
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source68 : Parameters := ⟨140,1226,58,27,192,4,5⟩
theorem shape68 : Shape source68 := by constructor <;> decide +kernel
theorem middle68 (h : ℕ) (hh : h≤27) : 192≤(source68.cutoff h+58-1)/131071 := by
  simp only [source68,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients68 :
    SecondJetRelaxedGlobalCounts.coefficientCount source68.cutoff 131071 1226 58 27 192=1814324904887663 := by
  decide +kernel
theorem rank68 : SecondJetRelaxedCounts.rankBound 140 1226 58 27 192=6921026674 := by decide +kernel
theorem dimension68 : Dimension source68 19288458607 := by
  exact dimension_of_counts source68 19288458607 1814324904887663 6921026674
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle68 coefficients68 rank68 (by decide)
def source69 : Parameters := ⟨140,1231,58,27,192,4,5⟩
theorem shape69 : Shape source69 := by constructor <;> decide +kernel
theorem middle69 (h : ℕ) (hh : h≤27) : 192≤(source69.cutoff h+58-1)/131071 := by
  simp only [source69,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients69 :
    SecondJetRelaxedGlobalCounts.coefficientCount source69.cutoff 131071 1231 58 27 192=1822246912208023 := by
  decide +kernel
theorem rank69 : SecondJetRelaxedCounts.rankBound 140 1231 58 27 192=6950888619 := by decide +kernel
theorem dimension69 : Dimension source69 113166068887 := by
  exact dimension_of_counts source69 113166068887 1822246912208023 6950888619
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle69 coefficients69 rank69 (by decide)
def source70 : Parameters := ⟨140,1178,60,28,192,4,5⟩
theorem shape70 : Shape source70 := by constructor <;> decide +kernel
theorem middle70 (h : ℕ) (hh : h≤28) : 192≤(source70.cutoff h+60-1)/131071 := by
  simp only [source70,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients70 :
    SecondJetRelaxedGlobalCounts.coefficientCount source70.cutoff 131071 1178 60 28 192=1833713039376830 := by
  decide +kernel
theorem rank70 : SecondJetRelaxedCounts.rankBound 140 1178 60 28 192=6995050875 := by decide +kernel
theorem dimension70 : Dimension source70 2422800830 := by
  exact dimension_of_counts source70 2422800830 1833713039376830 6995050875
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle70 coefficients70 rank70 (by decide)
def source71 : Parameters := ⟨140,1179,60,28,192,4,5⟩
theorem shape71 : Shape source71 := by constructor <;> decide +kernel
theorem middle71 (h : ℕ) (hh : h≤28) : 192≤(source71.cutoff h+60-1)/131071 := by
  simp only [source71,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients71 :
    SecondJetRelaxedGlobalCounts.coefficientCount source71.cutoff 131071 1179 60 28 192=1835385307375790 := by
  decide +kernel
theorem rank71 : SecondJetRelaxedCounts.rankBound 140 1179 60 28 192=7001352760 := by decide +kernel
theorem dimension71 : Dimension source71 22689458350 := by
  exact dimension_of_counts source71 22689458350 1835385307375790 7001352760
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle71 coefficients71 rank71 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
