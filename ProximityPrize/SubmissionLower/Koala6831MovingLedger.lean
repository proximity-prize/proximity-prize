import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Koala6831MovingLedger

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)

private theorem mixed_add_first (p q right cut : FlagDegree) :
    flagMixed (p + q) right cut = flagMixed p right cut + flagMixed q right cut := by
  simp only [flagMixed, add_zOnly, add_yz, add_all]
  ring

private theorem mixed_sum {ι : Type} (factors : Finset ι) (degree : ι → FlagDegree)
    (right cut : FlagDegree) :
    flagMixed (sumFlag factors degree) right cut =
      ∑ i ∈ factors, flagMixed (degree i) right cut := by
  simp only [mixed_expansion, sumFlag_all, sumFlag_middle, sumFlag_total,
    Finset.sum_add_distrib, Finset.mul_sum]

def creditFlag (residue : FlagDegree) : FlagDegree := ⟨0, residue.yz, residue.all⟩

theorem creditFlag_below (residue : FlagDegree) : Below (creditFlag residue) residue := by
  simp [Below, creditFlag, middle, total]

theorem room_card_add_credit_le {ι : Type} {K : Type*} [DecidableEq K]
    (factors : Finset ι) (degree : ι → FlagDegree) (seeds : ι → Finset K)
    (residue incoming right cut : FlagDegree) {denominator : ℕ} (hdenominator : 0 < denominator)
    (hflags : Below (sumFlag factors degree + residue) incoming)
    (hcount : ∀ i ∈ factors, (seeds i).card ≤ flagMixed (degree i) right cut / denominator) :
    (factors.biUnion seeds).card + flagMixed (creditFlag residue) right cut / denominator ≤
      flagMixed incoming right cut / denominator := by
  have hremoved : (factors.biUnion seeds).card * denominator ≤
      flagMixed (sumFlag factors degree) right cut := by
    apply (Nat.mul_le_mul_right denominator Finset.card_biUnion_le).trans
    rw [Finset.sum_mul, mixed_sum]
    exact Finset.sum_le_sum fun i hi => (Nat.le_div_iff_mul_le hdenominator).mp (hcount i hi)
  have hcredit := (Nat.div_mul_le_self (flagMixed (creditFlag residue) right cut) denominator).trans
    (mixed_mono_first (creditFlag_below residue) right cut)
  apply (Nat.le_div_iff_mul_le hdenominator).mpr
  rw [Nat.add_mul]
  calc
    _ ≤ flagMixed (sumFlag factors degree) right cut + flagMixed residue right cut :=
      Nat.add_le_add hremoved hcredit
    _ = flagMixed (sumFlag factors degree + residue) right cut :=
      (mixed_add_first _ _ _ _).symm
    _ ≤ _ := mixed_mono_first hflags right cut

end ProximityPrize.SubmissionLower.Koala6831MovingLedger
