import ProximityPrize.SubmissionLower.LocatorFinalCore6803
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptChecked
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseCertificate
import ProximityPrize.SubmissionLower.LocatorClosureScaffold6803

/-! Closed 68.03 theorem obtained by instantiating the checked receipt. -/

namespace ProximityPrize.SubmissionLower.LocatorFinal6803

open ProximityPrize.Benchmark

theorem protocolClaim6803 : ProtocolClaim 6803 10340095 33554432 :=
  LocatorClosureScaffold6803.protocolClaim6803_of_pair_count (by
    simpa only [LocatorClosureScaffold6803.SelectedPairCountBound,
      LocatorFinalCore6803.SelectedPairCountBound] using
        LocatorFinalCore6803.selected_pair_count_bound
          LocatorPhase6803ReceiptChecked.checkedRows
          LocatorPhase6803BaseCertificate.baseSound)

end ProximityPrize.SubmissionLower.LocatorFinal6803
