/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The trilinear charge and factor partition are due to Lucieno's PR 618
and the accepted Bome2017 construction. Here the retained degree in the seed alone is
credited as well, and any lower interval endpoint may be used for a uniform credit. -/
import ProximityPrize.SubmissionLower.Koala6831MovingFixedRooms

namespace ProximityPrize.SubmissionLower.IntermediateCredit
open scoped BigOperators Classical
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
open Koala6831Moving Koala6831MovingSources
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero)

private theorem mixed_add (p q right cut : FlagDegree) :
    flagMixed (p + q) right cut = flagMixed p right cut + flagMixed q right cut := by
  simp only [flagMixed, add_zOnly, add_yz, add_all]
  ring

private theorem mixed_sum {ι : Type} (factors : Finset ι) (degree : ι → FlagDegree)
    (right cut : FlagDegree) :
    flagMixed (sumFlag factors degree) right cut = ∑ i ∈ factors, flagMixed (degree i) right cut := by
  simp only [mixed_expansion, sumFlag_all, sumFlag_middle, sumFlag_total,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem full_credit {ι : Type} {K : Type*} [DecidableEq K]
    (factors : Finset ι) (degree : ι → FlagDegree) (seeds : ι → Finset K)
    (floor residue incoming right cut : FlagDegree) {denominator : ℕ} (hd : 0 < denominator)
    (hf : Below floor residue) (hb : Below (sumFlag factors degree + residue) incoming)
    (hc : ∀ i ∈ factors, (seeds i).card ≤ flagMixed (degree i) right cut / denominator) :
    (factors.biUnion seeds).card + flagMixed floor right cut / denominator ≤
      flagMixed incoming right cut / denominator := by
  have hr : (factors.biUnion seeds).card * denominator ≤ flagMixed (sumFlag factors degree) right cut := by
    apply (Nat.mul_le_mul_right denominator Finset.card_biUnion_le).trans
    rw [Finset.sum_mul, mixed_sum]
    exact Finset.sum_le_sum fun i hi => (Nat.le_div_iff_mul_le hd).mp (hc i hi)
  have hcr := (Nat.div_mul_le_self (flagMixed floor right cut) denominator).trans (mixed_mono_first hf right cut)
  apply (Nat.le_div_iff_mul_le hd).mpr
  rw [Nat.add_mul]
  exact (Nat.add_le_add hr hcr).trans ((mixed_add ..).symm.le.trans (mixed_mono_first hb right cut))

/-- Lift the actual residual of any fixed-room stage into the complete trilinear credit. -/
theorem room_full_credit {K I : Type} [Field K] [Fintype I] [DecidableEq K]
    (s : Stage) (nodes u₀ u₁ : I → K) (H : P4 K)
    (A final : Finset (RCN266.RegularIndex H)) (hf : final ⊆ stageRoomResidual s nodes u₀ u₁ H A)
    (seeds : RCN266.RegularIndex H → Finset K) (floor incoming right cut : FlagDegree)
    {denominator : ℕ} (hd : 0 < denominator) (low : Below floor (contactFlag (regularProduct H final)))
    (up : Below (contactFlag (regularProduct H A)) incoming)
    (count : ∀ F ∈ A \ stageRoomResidual s nodes u₀ u₁ H A,
      (seeds F).card ≤ flagMixed (contactFlag F.1) right cut / denominator) :
    ((A \ stageRoomResidual s nodes u₀ u₁ H A).biUnion seeds).card + flagMixed floor right cut / denominator ≤
      flagMixed incoming right cut / denominator := by
  let R := stageRoomResidual s nodes u₀ u₁ H A
  let removed := sumFlag (A \ R) (fun F => contactFlag F.1)
  have dvd : regularProduct H final ∣ regularProduct H R := Finset.prod_dvd_prod_of_subset final R (fun F => F.1) hf
  have sub := contactFlag_below_of_dvd (regularProduct_ne_zero H R) dvd
  have split : Below (removed + contactFlag (regularProduct H R)) incoming :=
    room_partition_flag H A (stageRoomFamily s nodes u₀ u₁) s.roomOrder incoming up
  have hb : Below (removed + contactFlag (regularProduct H final)) incoming := by
    simp only [Below, middle, total, add_all, add_yz, add_zOnly] at sub split ⊢
    omega
  exact full_credit (A \ R) (fun F => contactFlag F.1) seeds floor _ incoming right cut hd low hb count

#print axioms full_credit
#print axioms room_full_credit
end ProximityPrize.SubmissionLower.IntermediateCredit
