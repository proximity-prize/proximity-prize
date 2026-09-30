import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_004
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source8 : Parameters := ⟨58,800,25,11,79,1,2⟩
theorem shape8 : Shape source8 := by constructor <;> decide +kernel
theorem middle8 (h : ℕ) (hh : h≤11) : 79≤(source8.cutoff h+25-1)/131071 := by
  simp only [source8,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients8 :
    SecondJetRelaxedGlobalCounts.coefficientCount source8.cutoff 131071 800 25 11 79=41957371084639 := by
  decide +kernel
theorem rank8 : SecondJetRelaxedCounts.rankBound 58 800 25 11 79=159703717 := by decide +kernel
theorem dimension8 : Dimension source8 91999895391 := by
  exact dimension_of_counts source8 91999895391 41957371084639 159703717
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle8 coefficients8 rank8 (by decide)
def source9 : Parameters := ⟨58,1000,25,11,79,1,2⟩
theorem shape9 : Shape source9 := by constructor <;> decide +kernel
theorem middle9 (h : ℕ) (hh : h≤11) : 79≤(source9.cutoff h+25-1)/131071 := by
  simp only [source9,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients9 :
    SecondJetRelaxedGlobalCounts.coefficientCount source9.cutoff 131071 1000 25 11 79=52898428096639 := by
  decide +kernel
theorem rank9 : SecondJetRelaxedCounts.rankBound 58 1000 25 11 79=201052517 := by decide +kernel
theorem dimension9 : Dimension source9 193717080191 := by
  exact dimension_of_counts source9 193717080191 52898428096639 201052517
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle9 coefficients9 rank9 (by decide)
def source10 : Parameters := ⟨58,1200,25,11,79,1,2⟩
theorem shape10 : Shape source10 := by constructor <;> decide +kernel
theorem middle10 (h : ℕ) (hh : h≤11) : 79≤(source10.cutoff h+25-1)/131071 := by
  simp only [source10,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients10 :
    SecondJetRelaxedGlobalCounts.coefficientCount source10.cutoff 131071 1200 25 11 79=63839485108639 := by
  decide +kernel
theorem rank10 : SecondJetRelaxedCounts.rankBound 58 1200 25 11 79=242401317 := by decide +kernel
theorem dimension10 : Dimension source10 295434264991 := by
  exact dimension_of_counts source10 295434264991 63839485108639 242401317
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle10 coefficients10 rank10 (by decide)
def source11 : Parameters := ⟨60,1000,25,12,82,1,2⟩
theorem shape11 : Shape source11 := by constructor <;> decide +kernel
theorem middle11 (h : ℕ) (hh : h≤12) : 82≤(source11.cutoff h+25-1)/131071 := by
  simp only [source11,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients11 :
    SecondJetRelaxedGlobalCounts.coefficientCount source11.cutoff 131071 1000 25 12 82=57843985150588 := by
  decide +kernel
theorem rank11 : SecondJetRelaxedCounts.rankBound 60 1000 25 12 82=219762148 := by decide +kernel
theorem dimension11 : Dimension source11 234656625276 := by
  exact dimension_of_counts source11 234656625276 57843985150588 219762148
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle11 coefficients11 rank11 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
