import ProximityPrize.SubmissionLower.Part.G085


section Compact_SecondJetRounding
/-! Scale once and round only after summing all geometric components. -/
namespace ProximityPrize.SubmissionLower.SecondJetRounding
set_option autoImplicit false

theorem le_scaled_ceiling (M k : ℕ) : M ≤ (k+1)*((M+k)/(k+1)) := by
  have h := Nat.mod_add_div (M+k) (k+1)
  have hr := Nat.mod_lt (M+k) (by omega : 0 < k+1)
  omega

theorem count_le (count normal moving factor k : ℕ)
    (hc : (k+1)*count ≤ (k+1)*normal+factor*moving) :
    count ≤ normal+factor*((moving+k)/(k+1)) := by
  have hm := Nat.mul_le_mul_left factor (le_scaled_ceiling moving k)
  apply Nat.le_of_mul_le_mul_left (c := k+1) ?_ (by omega : 0 < k+1)
  calc
    (k+1)*count ≤ (k+1)*normal+factor*moving := hc
    _ ≤ (k+1)*normal+factor*((k+1)*((moving+k)/(k+1))) := Nat.add_le_add_left hm _
    _ = (k+1)*(normal+factor*((moving+k)/(k+1))) := by ring

end ProximityPrize.SubmissionLower.SecondJetRounding

end Compact_SecondJetRounding
