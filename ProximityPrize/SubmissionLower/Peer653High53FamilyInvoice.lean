import ProximityPrize.SubmissionLower.Peer653High53FamilyTrace

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
open Peer653High53 (Band agreement blockLength)
open P1_7_7 (localOrd localSeed)
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7
def ordinateFee (lo hi e : ℕ) := muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * (e - 1)
def seedFee (lo hi v : ℕ) := 2 * hi * muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * v
theorem band_invoice {b : Band} {w : ℕ} (hwlo : (start b) ≤ w) (hwhi : w ≤ (finish b))
    (e v : ℕ) :
    Invoice (131071+w) w e v (ordinateFee (start b) (finish b) e) (seedFee (start b) (finish b) v)
      (scale (finish b)) := by
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hdhi : degreeAt (finish b) < agreement := by
    change 131071 + (finish b) < 179896
    omega
  have hd : 131071+w < agreement := (Nat.add_le_add_left hwhi _).trans_lt hdhi
  have hA : agreement ≤ blockLength := by decide
  have hD : 0 < scale (finish b) := Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hdhi)
  have hm : scale (finish b) ≤ muNum (finish b) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hA _)
  have hpos : 1 ≤ 2*(finish b) := by omega
  refine ⟨hD, hm.trans (Nat.le_add_right _ _), ?_, hd, ?_⟩
  · exact hm.trans ((by
      simpa only [one_mul] using Nat.mul_le_mul_right (muNum (finish b)) hpos :
      muNum (finish b) ≤ 2*(finish b)*muNum (finish b)).trans (Nat.le_add_right _ _))
  · intro s hs
    have hord : (131071+w) - 2*w ≤ quotientOrder (start b) := by
      unfold quotientOrder P1_7.quotientOrder
      omega
    exact coordinate_bounds hA (Nat.add_le_add_left hwhi _) hdhi hwhi hord hs
theorem fee_of_bound {lo hi e v count : ℕ} (hD : 0 < scale hi)
    (hcount : ((scale hi : ℕ) : ℚ)^2 * count ≤
      ((e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v) : ℕ) : ℚ) +
        ((scale hi : ℕ) : ℚ)^2 * e) :
    count ≤ persistentFee lo hi e v := by
  let D := (scale hi)^2
  let num := e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v)
  have hd : 0 < D := pow_pos hD _
  have h : D * count ≤ num + D * e := by exact_mod_cast hcount
  have hmul : (count-e) * D ≤ num := by
    rw [Nat.sub_mul, Nat.mul_comm count, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hd).mpr (hmul.trans (Nat.le_add_right num (D-1)))
  change count ≤ (num + (D-1)) / D + e
  omega
end Peer653High53
end
