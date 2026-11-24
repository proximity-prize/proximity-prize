import ProximityPrize.SubmissionLower.Numeric5Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
open scoped BigOperators
structure Row where
  first : ℕ
  count : ℕ
  packed : ℕ
  deriving Inhabited
def unpack (packed : ℕ) : Powers :=
  ⟨packed % 512, packed / 512 % 512, packed / 262144 % 1024⟩
private def powersAt : ℕ → ℕ → Powers
  | 0, packed => unpack packed
  | k + 1, packed => powersAt k (packed / 268435456)
private def rowPowers (r : Row) (j : ℕ) : Powers :=
  powersAt (j - r.first) r.packed
private def assignment (start : ℕ) (rows : List Row) (i : BlockIndex) : Powers :=
  rowPowers (rows[i.1.val - start]?.getD default) i.2.val
end K1_13_2_3_5
end
