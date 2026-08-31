import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactHighTDerivativeSelectorPositive6750Research

open ContactHighTDerivativeRouter6750Research

set_option autoImplicit false

 

theorem highTDerivativeOrder_pos (t y r : Nat) :
    0 < highTDerivativeOrder t y r := by
  unfold highTDerivativeOrder
  cases hfind : (((List.range 14).map Nat.succ).reverse.find?
      (fun j ↦ decide (HighTDerivativeRoute t y r j))) with
  | none => simp
  | some j =>
      have hjmem : j ∈ (List.range 14).map Nat.succ := by
        simpa using List.mem_of_find?_eq_some hfind
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hjmem
      simp

end ContactHighTDerivativeSelectorPositive6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactHighTDerivativeSelectorPositive6750Research.highTDerivativeOrder_pos
