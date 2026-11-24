import ProximityPrize.SubmissionLower.Numeric6Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_1
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
end CJ6_1
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
def sumFrom (f : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFrom f j n + f (j + n)
end K1_13_2_3_6
end
