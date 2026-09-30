import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_000
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source4 : Parameters := ⟨56,1000,25,12,77,1,2⟩
theorem shape4 : Shape source4 := by constructor <;> decide +kernel
theorem middle4 (h : ℕ) (hh : h≤12) : 77≤(source4.cutoff h+25-1)/131071 := by
  simp only [source4,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients4 :
    SecondJetRelaxedGlobalCounts.coefficientCount source4.cutoff 131071 1000 25 12 77=49287363174413 := by
  decide +kernel
theorem rank4 : SecondJetRelaxedCounts.rankBound 56 1000 25 12 77=187451594 := by decide +kernel
theorem dimension4 : Dimension source4 148052516877 := by
  exact dimension_of_counts source4 148052516877 49287363174413 187451594
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle4 coefficients4 rank4 (by decide)
def source5 : Parameters := ⟨56,1200,25,12,77,1,2⟩
theorem shape5 : Shape source5 := by constructor <;> decide +kernel
theorem middle5 (h : ℕ) (hh : h≤12) : 77≤(source5.cutoff h+25-1)/131071 := by
  simp only [source5,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients5 :
    SecondJetRelaxedGlobalCounts.coefficientCount source5.cutoff 131071 1200 25 12 77=59471633652613 := by
  decide +kernel
theorem rank5 : SecondJetRelaxedCounts.rankBound 56 1200 25 12 77=225978994 := by decide +kernel
theorem dimension5 : Dimension source5 232596249477 := by
  exact dimension_of_counts source5 232596249477 59471633652613 225978994
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle5 coefficients5 rank5 (by decide)
def source6 : Parameters := ⟨56,1400,25,12,77,1,2⟩
theorem shape6 : Shape source6 := by constructor <;> decide +kernel
theorem middle6 (h : ℕ) (hh : h≤12) : 77≤(source6.cutoff h+25-1)/131071 := by
  simp only [source6,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients6 :
    SecondJetRelaxedGlobalCounts.coefficientCount source6.cutoff 131071 1400 25 12 77=69655904130813 := by
  decide +kernel
theorem rank6 : SecondJetRelaxedCounts.rankBound 56 1400 25 12 77=264506394 := by decide +kernel
theorem dimension6 : Dimension source6 317139982077 := by
  exact dimension_of_counts source6 317139982077 69655904130813 264506394
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle6 coefficients6 rank6 (by decide)
def source7 : Parameters := ⟨58,620,25,11,79,1,2⟩
theorem shape7 : Shape source7 := by constructor <;> decide +kernel
theorem middle7 (h : ℕ) (hh : h≤11) : 79≤(source7.cutoff h+25-1)/131071 := by
  simp only [source7,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients7 :
    SecondJetRelaxedGlobalCounts.coefficientCount source7.cutoff 131071 620 25 11 79=32110419773839 := by
  decide +kernel
theorem rank7 : SecondJetRelaxedCounts.rankBound 58 620 25 11 79=122489797 := by decide +kernel
theorem dimension7 : Dimension source7 454429071 := by
  exact dimension_of_counts source7 454429071 32110419773839 122489797
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle7 coefficients7 rank7 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
