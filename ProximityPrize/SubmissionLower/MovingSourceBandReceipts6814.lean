import ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
import ProximityPrize.SubmissionLower.MovingSourceBandIdentity6814
import ProximityPrize.SubmissionLower.MovingSourceBandLeading6814

/-! Eleven eligibility-constant endpoint cells cover the five requested
intervals. These are small ledger receipts, not interpolation existence
or an exhaustive owner-cover theorem. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandReceipts6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 20000
open RCN095 MovingSourceBandPairArithmetic6814 MovingSourceBandIdentity6814
open MovingSourceBandLeading6814 MovingSourcePairRetainedStage6814 MovingFiberThreeSources6811
open MovingSourceTwoProfiles6814

structure Cell where
  total : ℕ
  middle : ℕ
  slope : ℕ
  B : ℕ
  U : ℕ
  L : ℕ
  s : ℕ
  k : ℕ
  n0 : ℕ

def cell (i : Fin 11) : Cell := ![
  ⟨3568,55,12,53,177,3429,24,6,8⟩,
  ⟨3578,56,12,53,177,3429,24,6,8⟩,
  ⟨3382,57,12,47,154,3043,21,5,7⟩,
  ⟨3411,57,12,45,155,3382,20,5,7⟩,
  ⟨3429,57,12,46,151,3411,21,5,7⟩,
  ⟨3561,57,12,53,177,3429,24,6,8⟩,
  ⟨3429,53,13,46,151,3411,21,5,7⟩,
  ⟨3560,53,13,53,177,3429,24,6,8⟩,
  ⟨3382,54,13,47,154,3043,21,5,7⟩,
  ⟨3411,54,13,45,155,3382,20,5,7⟩,
  ⟨3428,54,13,46,151,3411,21,5,7⟩] i

def numericPrice (c : Cell) (delta u v : ℕ) : ℕ :=
  pairNumerator ((c.k+1)*delta)
    (delta*flagMixed ⟨c.total-c.middle,c.middle-c.slope,c.slope⟩ unitZFlag
      (SecondJetRelaxedFlag.budgetFlag c.B c.U c.L (c.k+1) c.n0))
    ((c.k+1)*u) ((c.k+1)*v) c.total c.middle c.slope
    ⟨c.total-c.middle,c.middle-c.slope,c.slope⟩/(3*((c.k+1)*delta))

def numericLeading (c : Cell) : ℕ :=
  AsymmetricHelper.leftRegularCountCap
    (pair c.total c.middle c.slope (c.B-2*c.n0) (c.U-c.n0) (c.L-c.n0))

def Receipt (c : Cell) : Prop :=
  coefficient c.total c.middle c.slope 1≤5*coefficient c.total c.middle c.slope 2 ∧
  Gates c.total c.middle c.slope (c.B-2*c.n0) (c.U-c.n0) (c.L-c.n0) ∧
  1700<c.L ∧ c.k<2130706433 ∧
  max (identityPrice c.total c.middle c.slope)
    (numericPrice c 1 26233 98890+numericLeading c)<270000000000000000

theorem receipts (i : Fin 11) : Receipt (cell i) := by
  fin_cases i <;> unfold Receipt Gates <;> decide +kernel

theorem pricedPair_of_profile {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (S : Source F) (c : Cell) (hS : Profile S c.B c.U c.L c.s c.k c.n0)
    (delta u v : ℕ) :
    pricedPair S delta u v c.total c.middle c.slope=numericPrice c delta u v := by
  rcases hS with ⟨hB,hU,hT,hs,hk,hn⟩
  simp only [pricedPair,numericPrice,Source.flag,Source.d,hB,hU,hT,hk,hn]

theorem leadingPrice_of_profile {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (S : Source F) (c : Cell) (hS : Profile S c.B c.U c.L c.s c.k c.n0) :
    leadingPrice S c.total c.middle c.slope=numericLeading c := by
  rcases hS with ⟨hB,hU,hT,hs,hk,hn⟩
  simp only [leadingPrice,numericLeading,hB,hU,hT,hn]

#print axioms receipts
#print axioms pricedPair_of_profile
end
end ProximityPrize.SubmissionLower.MovingSourceBandReceipts6814
