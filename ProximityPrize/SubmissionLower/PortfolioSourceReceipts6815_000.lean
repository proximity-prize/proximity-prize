import ProximityPrize.SubmissionLower.PortfolioSourceDimension6815
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source0 : Parameters := ⟨48,1122,20,9,65,1,2⟩
theorem shape0 : Shape source0 := by constructor <;> decide +kernel
theorem middle0 (h : ℕ) (hh : h≤9) : 65≤(source0.cutoff h+20-1)/131071 := by
  simp only [source0,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients0 :
    SecondJetRelaxedGlobalCounts.coefficientCount source0.cutoff 131071 1122 20 9 65=27720790276737 := by
  decide +kernel
theorem rank0 : SecondJetRelaxedCounts.rankBound 48 1122 20 9 65=105705598 := by decide +kernel
theorem dimension0 : Dimension source0 10701994625 := by
  exact dimension_of_counts source0 10701994625 27720790276737 105705598
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle0 coefficients0 rank0 (by decide)
def source1 : Parameters := ⟨50,1038,20,9,68,1,2⟩
theorem shape1 : Shape source1 := by constructor <;> decide +kernel
theorem middle1 (h : ℕ) (hh : h≤9) : 68≤(source1.cutoff h+20-1)/131071 := by
  simp only [source1,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients1 :
    SecondJetRelaxedGlobalCounts.coefficientCount source1.cutoff 131071 1038 20 9 68=28118224644489 := by
  decide +kernel
theorem rank1 : SecondJetRelaxedCounts.rankBound 50 1038 20 9 68=107197185 := by decide +kernel
theorem dimension1 : Dimension source1 17125779849 := by
  exact dimension_of_counts source1 17125779849 28118224644489 107197185
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle1 coefficients1 rank1 (by decide)
def source2 : Parameters := ⟨52,949,22,10,71,1,2⟩
theorem shape2 : Shape source2 := by constructor <;> decide +kernel
theorem middle2 (h : ℕ) (hh : h≤10) : 71≤(source2.cutoff h+22-1)/131071 := by
  simp only [source2,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients2 :
    SecondJetRelaxedGlobalCounts.coefficientCount source2.cutoff 131071 949 22 10 71=32365601879810 := by
  decide +kernel
theorem rank2 : SecondJetRelaxedCounts.rankBound 52 949 22 10 71=123296314 := by decide +kernel
theorem dimension2 : Dimension source2 44212942594 := by
  exact dimension_of_counts source2 44212942594 32365601879810 123296314
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle2 coefficients2 rank2 (by decide)
def source3 : Parameters := ⟨56,800,25,12,77,1,2⟩
theorem shape3 : Shape source3 := by constructor <;> decide +kernel
theorem middle3 (h : ℕ) (hh : h≤12) : 77≤(source3.cutoff h+25-1)/131071 := by
  simp only [source3,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients3 :
    SecondJetRelaxedGlobalCounts.coefficientCount source3.cutoff 131071 800 25 12 77=39103092696213 := by
  decide +kernel
theorem rank3 : SecondJetRelaxedCounts.rankBound 56 800 25 12 77=148924194 := by decide +kernel
theorem dimension3 : Dimension source3 63508784277 := by
  exact dimension_of_counts source3 63508784277 39103092696213 148924194
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle3 coefficients3 rank3 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
