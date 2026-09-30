import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_032
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source36 : Parameters := ⟨82,2232,34,15,112,3,4⟩
theorem shape36 : Shape source36 := by constructor <;> decide +kernel
theorem middle36 (h : ℕ) (hh : h≤15) : 112≤(source36.cutoff h+34-1)/131071 := by
  simp only [source36,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients36 :
    SecondJetRelaxedGlobalCounts.coefficientCount source36.cutoff 131071 2232 34 15 112=424697136587660 := by
  decide +kernel
theorem rank36 : SecondJetRelaxedCounts.rankBound 82 2232 34 15 112=1618876085 := by decide +kernel
theorem dimension36 : Dimension source36 318484161420 := by
  exact dimension_of_counts source36 318484161420 424697136587660 1618876085
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle36 coefficients36 rank36 (by decide)
def source37 : Parameters := ⟨82,815,36,16,112,2,3⟩
theorem shape37 : Shape source37 := by constructor <;> decide +kernel
theorem middle37 (h : ℕ) (hh : h≤16) : 112≤(source37.cutoff h+36-1)/131071 := by
  simp only [source37,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients37 :
    SecondJetRelaxedGlobalCounts.coefficientCount source37.cutoff 131071 815 36 16 112=163990216271279 := by
  decide +kernel
theorem rank37 : SecondJetRelaxedCounts.rankBound 82 815 36 16 112=625567910 := by decide +kernel
theorem dimension37 : Dimension source37 1342072239 := by
  exact dimension_of_counts source37 1342072239 163990216271279 625567910
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle37 coefficients37 rank37 (by decide)
def source38 : Parameters := ⟨82,2103,36,16,112,3,4⟩
theorem shape38 : Shape source38 := by constructor <;> decide +kernel
theorem middle38 (h : ℕ) (hh : h≤16) : 112≤(source38.cutoff h+36-1)/131071 := by
  simp only [source38,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients38 :
    SecondJetRelaxedGlobalCounts.coefficientCount source38.cutoff 131071 2103 36 16 112=436710695110703 := by
  decide +kernel
theorem rank38 : SecondJetRelaxedCounts.rankBound 82 2103 36 16 112=1664811318 := by decide +kernel
theorem dimension38 : Dimension source38 290396964911 := by
  exact dimension_of_counts source38 290396964911 436710695110703 1664811318
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle38 coefficients38 rank38 (by decide)
def source39 : Parameters := ⟨84,2213,34,15,115,3,4⟩
theorem shape39 : Shape source39 := by constructor <;> decide +kernel
theorem middle39 (h : ℕ) (hh : h≤15) : 115≤(source39.cutoff h+34-1)/131071 := by
  simp only [source39,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients39 :
    SecondJetRelaxedGlobalCounts.coefficientCount source39.cutoff 131071 2213 34 15 115=445273896268892 := by
  decide +kernel
theorem rank39 : SecondJetRelaxedCounts.rankBound 84 2213 34 15 115=1696905609 := by decide +kernel
theorem dimension39 : Dimension source39 440272303196 := by
  exact dimension_of_counts source39 440272303196 445273896268892 1696905609
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle39 coefficients39 rank39 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
