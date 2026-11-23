import ProximityPrize.SubmissionLower.KoalaH2430PrefixSource
import ProximityPrize.SubmissionLower.KoalaH2430SeedParentFinish

set_option autoImplicit false

namespace KoalaH2430
open HighCore82258
open HighCore82258_3 (initialE seedParentPrefix)
open KoalaH2430Receipt (prefixFee2430)

theorem prefix_books (e : ℕ) : seedParentPrefix .h2430 e + 1 ≤ prefixFee2430 e := by
  have hE : initialE .h2430 = 3085492 := by decide +kernel
  unfold seedParentPrefix
  rw [hE]
  by_cases h16 : e = 16
  · subst e
    decide +kernel
  by_cases h17 : e = 17
  · subst e
    decide +kernel
  · simp only [gradedLoss, fees, prefixFee2430, h16, h17, if_false] <;> decide +kernel

/-- Real parent inventory and terminal bank from the checked H2430 schedule. -/
theorem prefix_geometry : PrefixTerminalGeometry :=
  prefix_geometry_of_seed_parent .h2430 band
    (congrArg (fun t : HighCore82258.Bank => t.shape) terminal_eq)
    prefix_books crt_source
    (HighCore82258_3.of_children_seed_parent HighCore82258_3_1.proof
      HighCore82258_3_2.proof HighCore82258.schedule HighCore82258.graded_ledger)

#print axioms prefix_geometry
end KoalaH2430
