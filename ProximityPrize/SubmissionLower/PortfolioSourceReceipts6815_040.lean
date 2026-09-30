import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_036
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source40 : Parameters := ⟨84,1623,36,16,115,3,4⟩
theorem shape40 : Shape source40 := by constructor <;> decide +kernel
theorem middle40 (h : ℕ) (hh : h≤16) : 115≤(source40.cutoff h+36-1)/131071 := by
  simp only [source40,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients40 :
    SecondJetRelaxedGlobalCounts.coefficientCount source40.cutoff 131071 1623 36 16 115=354171654136457 := by
  decide +kernel
theorem rank40 : SecondJetRelaxedCounts.rankBound 84 1623 36 16 115=1351056981 := by decide +kernel
theorem dimension40 : Dimension source40 172909193 := by
  exact dimension_of_counts source40 172909193 354171654136457 1351056981
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle40 coefficients40 rank40 (by decide)
def source41 : Parameters := ⟨84,1902,36,16,115,3,4⟩
theorem shape41 : Shape source41 := by constructor <;> decide +kernel
theorem middle41 (h : ℕ) (hh : h≤16) : 115≤(source41.cutoff h+36-1)/131071 := by
  simp only [source41,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients41 :
    SecondJetRelaxedGlobalCounts.coefficientCount source41.cutoff 131071 1902 36 16 115=416920853559563 := by
  decide +kernel
theorem rank41 : SecondJetRelaxedCounts.rankBound 84 1902 36 16 115=1589225610 := by decide +kernel
theorem dimension41 : Dimension source41 314895251723 := by
  exact dimension_of_counts source41 314895251723 416920853559563 1589225610
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle41 coefficients41 rank41 (by decide)
def source42 : Parameters := ⟨84,2138,36,16,115,3,4⟩
theorem shape42 : Shape source42 := by constructor <;> decide +kernel
theorem middle42 (h : ℕ) (hh : h≤16) : 115≤(source42.cutoff h+36-1)/131071 := by
  simp only [source42,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients42 :
    SecondJetRelaxedGlobalCounts.coefficientCount source42.cutoff 131071 2138 36 16 115=469999029415667 := by
  decide +kernel
theorem rank42 : SecondJetRelaxedCounts.rankBound 84 2138 36 16 115=1790687246 := by decide +kernel
theorem dimension42 : Dimension source42 581112000243 := by
  exact dimension_of_counts source42 581112000243 469999029415667 1790687246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle42 coefficients42 rank42 (by decide)
def source43 : Parameters := ⟨84,2131,36,17,115,3,4⟩
theorem shape43 : Shape source43 := by constructor <;> decide +kernel
theorem middle43 (h : ℕ) (hh : h≤17) : 115≤(source43.cutoff h+36-1)/131071 := by
  simp only [source43,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients43 :
    SecondJetRelaxedGlobalCounts.coefficientCount source43.cutoff 131071 2131 36 17 115=472316662530566 := by
  decide +kernel
theorem rank43 : SecondJetRelaxedCounts.rankBound 84 2131 36 17 115=1799540541 := by decide +kernel
theorem dimension43 : Dimension source43 577906950662 := by
  exact dimension_of_counts source43 577906950662 472316662530566 1799540541
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle43 coefficients43 rank43 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
