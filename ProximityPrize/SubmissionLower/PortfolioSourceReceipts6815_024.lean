import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_020
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source24 : Parameters := ⟨68,1640,27,13,93,2,3⟩
theorem shape24 : Shape source24 := by constructor <;> decide +kernel
theorem middle24 (h : ℕ) (hh : h≤13) : 93≤(source24.cutoff h+27-1)/131071 := by
  simp only [source24,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients24 :
    SecondJetRelaxedGlobalCounts.coefficientCount source24.cutoff 131071 1640 27 13 93=143318347743312 := by
  decide +kernel
theorem rank24 : SecondJetRelaxedCounts.rankBound 68 1640 27 13 93=546190638 := by decide +kernel
theorem dimension24 : Dimension source24 137749135440 := by
  exact dimension_of_counts source24 137749135440 143318347743312 546190638
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle24 coefficients24 rank24 (by decide)
def source25 : Parameters := ⟨68,1680,27,13,93,2,3⟩
theorem shape25 : Shape source25 := by constructor <;> decide +kernel
theorem middle25 (h : ℕ) (hh : h≤13) : 93≤(source25.cutoff h+27-1)/131071 := by
  simp only [source25,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients25 :
    SecondJetRelaxedGlobalCounts.coefficientCount source25.cutoff 131071 1680 27 13 93=146897347918552 := by
  decide +kernel
theorem rank25 : SecondJetRelaxedCounts.rankBound 68 1680 27 13 93=559773398 := by decide +kernel
theorem dimension25 : Dimension source25 156110273240 := by
  exact dimension_of_counts source25 156110273240 146897347918552 559773398
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle25 coefficients25 rank25 (by decide)
def source26 : Parameters := ⟨68,1683,28,12,93,2,3⟩
theorem shape26 : Shape source26 := by constructor <;> decide +kernel
theorem middle26 (h : ℕ) (hh : h≤12) : 93≤(source26.cutoff h+28-1)/131071 := by
  simp only [source26,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients26 :
    SecondJetRelaxedGlobalCounts.coefficientCount source26.cutoff 131071 1683 28 12 93=153003835417819 := by
  decide +kernel
theorem rank26 : SecondJetRelaxedCounts.rankBound 68 1683 28 12 93=582826619 := by decide +kernel
theorem dimension26 : Dimension source26 219334206683 := by
  exact dimension_of_counts source26 219334206683 153003835417819 582826619
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle26 coefficients26 rank26 (by decide)
def source27 : Parameters := ⟨76,967,31,14,104,2,3⟩
theorem shape27 : Shape source27 := by constructor <;> decide +kernel
theorem middle27 (h : ℕ) (hh : h≤14) : 104≤(source27.cutoff h+31-1)/131071 := by
  simp only [source27,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients27 :
    SecondJetRelaxedGlobalCounts.coefficientCount source27.cutoff 131071 967 31 14 104=131575175268415 := by
  decide +kernel
theorem rank27 : SecondJetRelaxedCounts.rankBound 76 967 31 14 104=501917624 := by decide +kernel
theorem dimension27 : Dimension source27 481642559 := by
  exact dimension_of_counts source27 481642559 131575175268415 501917624
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle27 coefficients27 rank27 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
