import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_016
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source20 : Parameters := ⟨68,1340,27,13,93,2,3⟩
theorem shape20 : Shape source20 := by constructor <;> decide +kernel
theorem middle20 (h : ℕ) (hh : h≤13) : 93≤(source20.cutoff h+27-1)/131071 := by
  simp only [source20,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients20 :
    SecondJetRelaxedGlobalCounts.coefficientCount source20.cutoff 131071 1340 27 13 93=116475846429012 := by
  decide +kernel
theorem rank20 : SecondJetRelaxedCounts.rankBound 68 1340 27 13 93=444319938 := by decide +kernel
theorem dimension20 : Dimension source20 40601940 := by
  exact dimension_of_counts source20 40601940 116475846429012 444319938
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle20 coefficients20 rank20 (by decide)
def source21 : Parameters := ⟨68,1400,27,13,93,2,3⟩
theorem shape21 : Shape source21 := by constructor <;> decide +kernel
theorem middle21 (h : ℕ) (hh : h≤13) : 93≤(source21.cutoff h+27-1)/131071 := by
  simp only [source21,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients21 :
    SecondJetRelaxedGlobalCounts.coefficientCount source21.cutoff 131071 1400 27 13 93=121844346691872 := by
  decide +kernel
theorem rank21 : SecondJetRelaxedCounts.rankBound 68 1400 27 13 93=464694078 := by decide +kernel
theorem dimension21 : Dimension source21 27582308640 := by
  exact dimension_of_counts source21 27582308640 121844346691872 464694078
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle21 coefficients21 rank21 (by decide)
def source22 : Parameters := ⟨68,1500,27,13,93,2,3⟩
theorem shape22 : Shape source22 := by constructor <;> decide +kernel
theorem middle22 (h : ℕ) (hh : h≤13) : 93≤(source22.cutoff h+27-1)/131071 := by
  simp only [source22,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients22 :
    SecondJetRelaxedGlobalCounts.coefficientCount source22.cutoff 131071 1500 27 13 93=130791847129972 := by
  decide +kernel
theorem rank22 : SecondJetRelaxedCounts.rankBound 68 1500 27 13 93=498650978 := by decide +kernel
theorem dimension22 : Dimension source22 73485153140 := by
  exact dimension_of_counts source22 73485153140 130791847129972 498650978
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle22 coefficients22 rank22 (by decide)
def source23 : Parameters := ⟨68,1600,27,13,93,2,3⟩
theorem shape23 : Shape source23 := by constructor <;> decide +kernel
theorem middle23 (h : ℕ) (hh : h≤13) : 93≤(source23.cutoff h+27-1)/131071 := by
  simp only [source23,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients23 :
    SecondJetRelaxedGlobalCounts.coefficientCount source23.cutoff 131071 1600 27 13 93=139739347568072 := by
  decide +kernel
theorem rank23 : SecondJetRelaxedCounts.rankBound 68 1600 27 13 93=532607878 := by decide +kernel
theorem dimension23 : Dimension source23 119387997640 := by
  exact dimension_of_counts source23 119387997640 139739347568072 532607878
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle23 coefficients23 rank23 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
