import ProximityPrize.SubmissionLower.GoldBranch5
set_option autoImplicit true
section
namespace P3_3
noncomputable section
open P3 Polynomial
open P1_3 (Bank cutDegree)
abbrev sourceCutoff : ℕ := 4 * agreement - 1
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
end
end P3_3
end
