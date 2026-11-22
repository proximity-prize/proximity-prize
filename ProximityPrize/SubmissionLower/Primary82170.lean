import ProximityPrize.SubmissionLower.PrimaryFourthWindowReceipt
import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

namespace Primary82170

open K1_13 K1_13_2 K1_13_2_3
open scoped BigOperators
open private combine baseline_budget_on savings_parts sum_add_pointwise_eq bound_le_baseline
  from ProximityPrize.SubmissionLower.Fast022

/-- Retain the whole fourth-window saving from the published interpolation certificate. -/
theorem block_budget :
    ∃ power : BlockIndex → Fin 11 → ℕ,
      (∑ i, blockBound i (power i)) ≤ 344122366652253 := by
  obtain ⟨p₁, hp₁⟩ := K1_13_2_3_4.proof
  obtain ⟨p₂, hp₂⟩ := K1_13_2_3_5.proof
  obtain ⟨p₃, hp₃⟩ := K1_13_2_3_6.proof
  let p₄ := K1_13_2_3_7.witness
  have hp₄ : 177382348097 ≤ savingsSum w4 p₄ :=
    K1_13_2_3_7.numeric_total ▸ K1_13_2_3_7.numeric_le_savings
  let p := combine p₁ p₂ p₃ p₄
  refine ⟨fun i => (p i).expand, ?_⟩
  have hstatic := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hsave : 447233088208 ≤ ∑ i : BlockIndex, savings i (p i) := calc
    _ ≤ (9573892230 + 159735926601 + 100540921280 + 177382348097) := by decide
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp₁ hp₂) hp₃) hp₄
    _ ≤ _ := savings_parts p₁ p₂ p₃ p₄
  have hsum : (∑ i : BlockIndex, blockBound i (p i).expand) +
      (∑ i : BlockIndex, savings i (p i)) = ∑ i : BlockIndex, baseline i :=
    sum_add_pointwise_eq Finset.univ (fun i => blockBound i (p i).expand)
      (fun i => savings i (p i)) baseline
      (fun i _ => Nat.add_sub_of_le (bound_le_baseline i (p i).expand))
  change (∑ i : BlockIndex, blockBound i (p i).expand) ≤ 344122366652253
  omega

theorem origin_rank :
    Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ 344122366652253 := by
  have hblock := K1_13_2_2.of_children K1_13_2_2_1.proof K1_13_2_2_2.proof
    K1_13_2_2_3.proof K1_13_2_2_4.proof K1_13_2_2_5.proof
  obtain ⟨power, hp⟩ := block_budget
  exact (K1_13_2.origin_rank_le power hblock).trans hp

#print axioms origin_rank

end Primary82170
