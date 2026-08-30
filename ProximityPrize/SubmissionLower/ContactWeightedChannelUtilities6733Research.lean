import ProximityPrize.SubmissionLower.ContactWeightedGroupedResultantChannel6733Research
namespace ProximityPrize.SubmissionLower.ContactWeightedChannelUtilities6733Research
open scoped Classical BigOperators
open ContactWeightedGroupedResultantChannel6733Research
noncomputable section
set_option autoImplicit false
variable {Base:Type} [Field Base] [DecidableEq Base]
noncomputable def recost
    {I:Type*} [Fintype I] {multiplicity oldCost newCost:I → ℕ}
    {budget:ℕ}
    (C:WeightedGroupedResultantChannel (Base:=Base)
      multiplicity oldCost budget)
    (hcost:∀ i,newCost i ≤ oldCost i):
    WeightedGroupedResultantChannel (Base:=Base)
      multiplicity newCost budget where
  resultant:=C.resultant
  factor:=C.factor
  residueWeight:=C.residueWeight
  resultant_ne:=C.resultant_ne
  factor_irreducible:=C.factor_irreducible
  factor_monic:=C.factor_monic
  groupedPowerDvd:=C.groupedPowerDvd
  cost_le_residue_mul_degree i:=(hcost i).trans (C.cost_le_residue_mul_degree i)
  resultant_degree_le:=C.resultant_degree_le
noncomputable def emptyChannel
    {I:Type*} [Fintype I] [IsEmpty I]
    (multiplicity cost:I → ℕ) (budget:ℕ):
    WeightedGroupedResultantChannel (Base:=Base) multiplicity cost budget where
  resultant:=1
  factor i:=isEmptyElim i
  residueWeight i:=isEmptyElim i
  resultant_ne:=one_ne_zero
  factor_irreducible i:=isEmptyElim i
  factor_monic i:=isEmptyElim i
  groupedPowerDvd f hf:=by simp at hf
  cost_le_residue_mul_degree i:=isEmptyElim i
  resultant_degree_le:=by simp
end
end ProximityPrize.SubmissionLower.ContactWeightedChannelUtilities6733Research
