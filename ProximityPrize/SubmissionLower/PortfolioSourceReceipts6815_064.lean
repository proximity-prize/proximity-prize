import ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815_060
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
open PortfolioSource6815
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source64 : Parameters := ⟨128,3734,53,24,174,6,8⟩
theorem shape64 : Shape source64 := by constructor <;> decide +kernel
theorem middle64 (h : ℕ) (hh : h≤24) : 174≤(source64.cutoff h+53-1)/131071 := by
  simp only [source64,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients64 :
    SecondJetRelaxedGlobalCounts.coefficientCount source64.cutoff 131071 3734 53 24 174=4029055746580152 := by
  decide +kernel
theorem rank64 : SecondJetRelaxedCounts.rankBound 128 3734 53 24 174=15369613990 := by decide +kernel
theorem dimension64 : Dimension source64 3656785592 := by
  exact dimension_of_counts source64 3656785592 4029055746580152 15369613990
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle64 coefficients64 rank64 (by decide)
def source65 : Parameters := ⟨129,3680,53,25,175,6,8⟩
theorem shape65 : Shape source65 := by constructor <;> decide +kernel
theorem middle65 (h : ℕ) (hh : h≤25) : 175≤(source65.cutoff h+53-1)/131071 := by
  simp only [source65,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients65 :
    SecondJetRelaxedGlobalCounts.coefficientCount source65.cutoff 131071 3680 53 25 175=4063748936792714 := by
  decide +kernel
theorem rank65 : SecondJetRelaxedCounts.rankBound 129 3680 53 25 175=15501968380 := by decide +kernel
theorem dimension65 : Dimension source65 937785994 := by
  exact dimension_of_counts source65 937785994 4063748936792714 15501968380
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle65 coefficients65 rank65 (by decide)
def source66 : Parameters := ⟨130,3618,53,24,176,6,8⟩
theorem shape66 : Shape source66 := by constructor <;> decide +kernel
theorem middle66 (h : ℕ) (hh : h≤24) : 176≤(source66.cutoff h+53-1)/131071 := by
  simp only [source66,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients66 :
    SecondJetRelaxedGlobalCounts.coefficientCount source66.cutoff 131071 3618 53 24 176=4045135712180991 := by
  decide +kernel
theorem rank66 : SecondJetRelaxedCounts.rankBound 130 3618 53 24 176=15430961278 := by decide +kernel
theorem dimension66 : Dimension source66 1798920959 := by
  exact dimension_of_counts source66 1798920959 4045135712180991 15430961278
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle66 coefficients66 rank66 (by decide)
def source67 : Parameters := ⟨130,3543,53,24,177,6,8⟩
theorem shape67 : Shape source67 := by constructor <;> decide +kernel
theorem middle67 (h : ℕ) (hh : h≤24) : 177≤(source67.cutoff h+53-1)/131071 := by
  simp only [source67,Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve]
  split_ifs <;> omega
theorem coefficients67 :
    SecondJetRelaxedGlobalCounts.coefficientCount source67.cutoff 131071 3543 53 24 177=3959844937245224 := by
  decide +kernel
theorem rank67 : SecondJetRelaxedCounts.rankBound 130 3543 53 24 177=15105604012 := by decide +kernel
theorem dimension67 : Dimension source67 1479123496 := by
  exact dimension_of_counts source67 1479123496 3959844937245224 15105604012
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle67 coefficients67 rank67 (by decide)
end ProximityPrize.SubmissionLower.PortfolioSourceReceipts6815
