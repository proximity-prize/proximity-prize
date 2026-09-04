import ProximityPrize.SubmissionLower.LocatorBatchPhase6803

/-! The aggregate regular-factor flag is exactly the original cumulative
flag of the corresponding squarefree regular product. -/

namespace ProximityPrize.SubmissionLower.LocatorAggregateFlagProduct6803

open RCN052 RCN095 RCN130 RCN234
open LocatorFactorAggregate LocatorBatchProductRoute LocatorBatchPhase6803

set_option autoImplicit false

abbrev K := LocatorBatchPhase6803.K
abbrev P4 := LocatorBatchPhase6803.P4

theorem originalCumulativeFlag_regularProduct
    (H : P4) (A : Finset (RegularIndex H)) :
    originalCumulativeFlag (regularProduct H A) =
      regularAggregateFlag H A := by
  have hc := originalCumulativeFlag_cumulative (regularProduct H A)
  have hall : (originalCumulativeFlag (regularProduct H A)).all =
      (regularAggregateFlag H A).all :=
    hc.1.trans (regularAggregateFlag_all H A).symm
  have hmiddle : middle (originalCumulativeFlag (regularProduct H A)) =
      middle (regularAggregateFlag H A) :=
    hc.2.1.trans (regularAggregateFlag_middle H A).symm
  have htotal : total (originalCumulativeFlag (regularProduct H A)) =
      total (regularAggregateFlag H A) :=
    hc.2.2.trans (regularAggregateFlag_total H A).symm
  cases hleft : originalCumulativeFlag (regularProduct H A) with
  | mk lz ly la =>
      cases hright : regularAggregateFlag H A with
      | mk rz ry ra =>
          simp only [hleft, hright, FlagDegree.mk.injEq] at ⊢
          simp only [hleft, hright, middle, total] at hall hmiddle htotal
          omega

end ProximityPrize.SubmissionLower.LocatorAggregateFlagProduct6803
