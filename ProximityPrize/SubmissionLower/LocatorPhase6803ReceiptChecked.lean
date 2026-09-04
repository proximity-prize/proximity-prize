import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCertificate
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptChecked

open LocatorPhase6803ReceiptCore
open LocatorPhase6803ReceiptCertificate
open LocatorPhase6803ReceiptSemantic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkedRows : CheckedRows where
  stateAt := by
    intro R V hR hR29 hRV
    have hV : V ∈ List.range (middleCap + 1 - R) :=
      List.mem_range.mpr (by omega)
    interval_cases R <;>
      first
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state01 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state02 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state03 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state04 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state05 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state06 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state07 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state08 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state09 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state10 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state11 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state12 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state13 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state14 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state15 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state16 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state17 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state18 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state19 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state20 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state21 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state22 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state23 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state24 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state25 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state26 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state27 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state28 V hV
      | simpa [lookupBase, lookupThreshold, lookupPrefix, previousPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.state29 V hV
  prefixRowsAt := by
    intro R V hR hR28 hRV
    have hV : V ∈ List.range (middleCap - R) :=
      List.mem_range.mpr (by omega)
    interval_cases R <;>
      first
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix01 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix02 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix03 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix04 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix05 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix06 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix07 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix08 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix09 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix10 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix11 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix12 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix13 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix14 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix15 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix16 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix17 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix18 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix19 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix20 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix21 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix22 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix23 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix24 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix25 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix26 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix27 hR28 V hV
      | simpa [lookupPrefix] using
          LocatorPhase6803ReceiptCertificate.certificate.prefix28 hR28 V hV
      | omega

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptChecked
