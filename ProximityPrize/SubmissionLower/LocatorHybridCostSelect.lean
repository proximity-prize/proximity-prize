import ProximityPrize.SubmissionLower.LocatorHybridCostC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostSelect. -/
section PackedLocator_LocatorHybridCostSelect
/-!
# The ordinary cost of the 6800 certificate (C2 selection)

`LocatorHybridCost.ordinaryCostOf` is the C2 hybrid cost on the C2 branch
(`3 ≤ slope` and `slope + 2 ≤ middle`) and the padded two-tail cost otherwise.
There is deliberately no `min` against the padded cost: on the narrow box
`hybridCostC2 ≤ paddedCost 131072 131073` holds pointwise, and the `if` shape
is what `LocatorOrdinaryZConvex` needs (affine in `z`, not merely concave).
`OwnBound` is `OwnBoundC2`, produced by `LocatorFixedOwnBoundC2`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open RCN095 LocatorFactorAggregate LocatorHybridCostC2

def ordinaryCostOf (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then hybridCostC2 p else paddedCost 131072 131073 p

theorem ordinaryCostOf_of_hybrid (p : FlagDegree) (hp : HybridAppliesC2 p) :
    ordinaryCostOf p = hybridCostC2 p := by
  unfold ordinaryCostOf
  rw [if_pos hp]

theorem ordinaryCostOf_of_padded (p : FlagDegree) (hp : ¬ HybridAppliesC2 p) :
    ordinaryCostOf p = paddedCost 131072 131073 p := by
  unfold ordinaryCostOf
  rw [if_neg hp]

/-- The per-factor own bound consumed by the batch and bridge modules. -/
abbrev OwnBound (count : ℕ) (p : FlagDegree) : Prop := OwnBoundC2 count p

theorem ownBound_le_ordinaryCostOf {count : ℕ} {p : FlagDegree} (h : OwnBound count p) :
    count ≤ ordinaryCostOf p := by
  unfold ordinaryCostOf
  split_ifs with hp
  · exact h.2 hp
  · exact h.1

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier10 : True := by trivial
end ProximityPrize.SubmissionLower

