import ProximityPrize.SubmissionLower.CK
namespace ProximityPrize.SubmissionLower.RCN343
open scoped Classical BigOperators
open RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Base:Type} [Field Base] [DecidableEq Base]
structure WeightedGroupedResultantChannel
   {I:Type*} [Fintype I]
   (multiplicity cost:I → ℕ) (budget:ℕ) where
 resultant:Polynomial Base
 factor:I → Polynomial Base
 residueWeight:I → ℕ
 resultant_ne:resultant≠0
 factor_irreducible:∀ i,Irreducible (factor i)
 factor_monic:∀ i,(factor i).Monic
 groupedPowerDvd:∀ f∈Finset.univ.image factor,
   f^(∑ i with factor i=f,multiplicity i*residueWeight i)∣resultant
 cost_le_residue_mul_degree:∀ i,
   cost i ≤ residueWeight i*(factor i).natDegree
 resultant_degree_le:resultant.natDegree ≤ budget
theorem WeightedGroupedResultantChannel.sum_mul_cost_le
   {I:Type*} [Fintype I]
   {multiplicity cost:I → ℕ} {budget:ℕ}
   (C:WeightedGroupedResultantChannel
     (Base:=Base) multiplicity cost budget):
   (∑ i,multiplicity i*cost i) ≤ budget:=by
 let weightedMultiplicity:I → ℕ:=fun i↦
   multiplicity i*C.residueWeight i
 have hfactor:=sum_grouped_power_factor_degrees_le
   C.resultant C.factor weightedMultiplicity C.resultant_ne
     C.factor_irreducible C.factor_monic C.groupedPowerDvd
 calc
   (∑ i,multiplicity i*cost i) ≤
       ∑ i,multiplicity i*
         (C.residueWeight i*(C.factor i).natDegree):=
     Finset.sum_le_sum (fun i _↦
       Nat.mul_le_mul_left (multiplicity i)
         (C.cost_le_residue_mul_degree i))
   _=∑ i,weightedMultiplicity i*(C.factor i).natDegree:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [weightedMultiplicity,Nat.mul_assoc]
   _ ≤ C.resultant.natDegree:=hfactor
   _ ≤ budget:=C.resultant_degree_le
end
end ProximityPrize.SubmissionLower.RCN343
