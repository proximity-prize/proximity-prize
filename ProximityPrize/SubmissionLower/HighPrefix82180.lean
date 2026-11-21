import ProximityPrize.SubmissionLower.HighLoss82180

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

namespace HighPrefix82180
open P3 (HighBand)
open P3_7 (stages Stage fees degreeAt)
open P3_7_3 (initialCap rankB rankJ stageAt)
open HighPrices82180 (finish)
open scoped BigOperators
open private sum_stages from ProximityPrize.SubmissionLower.GoldBranch7N3

/-- Charge for a fixed component at the new agreement and the stated maximum height. -/
def fixedFee (hi B J : ℕ) : ℕ :=
  let d := degreeAt hi
  let lam : ℚ := (262144 : ℚ) / 179964
  let mu : ℚ := ((262144 - d : ℕ) : ℚ) / (179964 - d : ℕ)
  let base := mu + 2*lam*d*(B-1 : ℕ)
  let jet := min base (lam*d*(2*J-1 : ℕ))
  (((B-J : ℕ) : ℚ)*jet + J*base).ceil.toNat + B^2

private def stageCost (hi : ℕ) (s : Stage) : ℕ :=
  fixedFee hi s.free.shape.B s.free.shape.J + fixedFee hi s.moving.shape.B s.moving.shape.J

def fixedBudget (b : HighBand) : ℕ :=
  ∑ i ∈ Finset.range (stages b).length, stageCost (finish b) (stageAt b i)

def book (b : HighBand) : P3_7.PrefixFees :=
  let (loss, jet, fixed) : ℕ × ℕ × ℕ := match b with
    | .h2274 => (57146924523229699, 22701183600978758, 15684732358746)
    | .h2294 => (52497702431057432, 21929376639689480, 22827201124821)
    | .h7773 => (667673328253744, 8141058494411, 6135201704)
  ⟨loss, (fees b).point, (fees b).lowSeed, jet, fixed, (fees b).content⟩

def prefixTotal (b : HighBand) : ℕ :=
  let f := book b
  f.loss + f.point + f.lowSeed + f.lowJet + f.fixedODE + f.content

def total : HighBand → ℕ
  | .h2274 => 264421827535251154
  | .h2294 => 225455414515823865
  | .h7773 => 994249782152492

theorem jet_exact (b : HighBand) :
    initialCap b 0 + fixedFee (finish b) (rankB b) (rankJ b) = (book b).lowJet := by
  rw [P3_7_3_3.initial_eq, (P3_7_3_3.rank_eq b).1, (P3_7_3_3.rank_eq b).2]
  cases b <;> decide +kernel

theorem fixed_exact (b : HighBand) : fixedBudget b = (book b).fixedODE := by
  unfold fixedBudget stageAt
  rw [sum_stages]
  cases b <;> decide +kernel

theorem loss_discount (b : HighBand) : HighBanks82180.start b < 7773 →
    HighLoss82180.factor * ((fees b).loss : ℚ) ≤ ((book b).loss : ℚ) := by
  cases b <;> decide +kernel

theorem loss_direct (b : HighBand) : 7773 ≤ HighBanks82180.start b →
    (fees b).loss = (book b).loss := by cases b <;> decide +kernel

theorem total_exact (b : HighBand) : prefixTotal b + HighPrices82180.cap b + 1 = total b := by
  cases b <;> decide +kernel

/-- The six prefix charges, the retained-root charge and one extra slope fit in each band. -/
theorem total_le (b : HighBand) : prefixTotal b + HighPrices82180.cap b + 1 ≤ 264421827535251154 := by
  rw [total_exact]
  cases b <;> decide +kernel

#print axioms jet_exact
#print axioms fixed_exact
#print axioms total_le
end HighPrefix82180
