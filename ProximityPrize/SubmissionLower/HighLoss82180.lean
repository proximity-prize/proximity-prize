import ProximityPrize.SubmissionLower.HighPrices82180
import ProximityPrize.SubmissionLower.GoldBranch7N3

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace HighLoss82180

open P3 (HighBand p)
open P3_7 (degreeAt fees)
open P3_7_3 (history cutWeight lossWeight laterCount seedLimit pointLimit)
open P1_7_4 (Mass dotQ running weightedBill)
open HighBanks82180 (start)
open HighPrices82180 (finish)
open scoped BigOperators

abbrev factor : ℚ := 101 / 100
private theorem positive : (0 : ℚ) ≤ factor := by norm_num [factor]

private def alpha (A h : ℕ) : ℚ := 1 + 2 * ((262144 : ℚ)/A) * degreeAt h
private def mu (A h : ℕ) : ℚ := ((262144 - degreeAt h : ℕ) : ℚ) / (A - degreeAt h : ℕ)

def curve (A h g : ℕ) : ℚ := (2*(g : ℚ)-1)*alpha A h + mu A h

theorem old_direct (b : HighBand) : 7773 ≤ start b → 7773 ≤ b.row.lo := by
  cases b <;> decide +kernel

theorem direct (b : HighBand) (hb : 7773 ≤ start b) :
    ((p+1 : ℕ) : ℚ)*seedLimit b ≤ ((fees b).loss : ℚ) :=
  (P3_7_3_4.proof b).direct (old_direct b hb)

theorem points (b : HighBand) : pointLimit b ≤ ((fees b).point : ℚ) := (P3_7_3_4.proof b).points

end HighLoss82180
