import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck01
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck02
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck03
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck04
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck05
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck06
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck07
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck08
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck09
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck10
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck11
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck12
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck13
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck14
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck15
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck16
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck17
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck18
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck19
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck20
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck21
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck22
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck23
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck24
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck25
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck26
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck27
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck28
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck29

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCertificate

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000

structure Certificate : Prop where
  state01 : RowValid 1 LocatorPhase6803ReceiptRowData01.base LocatorPhase6803ReceiptRowData01.threshold
    LocatorPhase6803ReceiptRowData01.prefixData (fun _ => zeroPrefix)
  prefix01 : PrefixRowValid 1 LocatorPhase6803ReceiptRowData01.prefixData (LocatorPhase6803ReceiptRowData02.prefixData)
  state02 : RowValid 2 LocatorPhase6803ReceiptRowData02.base LocatorPhase6803ReceiptRowData02.threshold
    LocatorPhase6803ReceiptRowData02.prefixData (LocatorPhase6803ReceiptRowData01.prefixData)
  prefix02 : PrefixRowValid 2 LocatorPhase6803ReceiptRowData02.prefixData (LocatorPhase6803ReceiptRowData03.prefixData)
  state03 : RowValid 3 LocatorPhase6803ReceiptRowData03.base LocatorPhase6803ReceiptRowData03.threshold
    LocatorPhase6803ReceiptRowData03.prefixData (LocatorPhase6803ReceiptRowData02.prefixData)
  prefix03 : PrefixRowValid 3 LocatorPhase6803ReceiptRowData03.prefixData (LocatorPhase6803ReceiptRowData04.prefixData)
  state04 : RowValid 4 LocatorPhase6803ReceiptRowData04.base LocatorPhase6803ReceiptRowData04.threshold
    LocatorPhase6803ReceiptRowData04.prefixData (LocatorPhase6803ReceiptRowData03.prefixData)
  prefix04 : PrefixRowValid 4 LocatorPhase6803ReceiptRowData04.prefixData (LocatorPhase6803ReceiptRowData05.prefixData)
  state05 : RowValid 5 LocatorPhase6803ReceiptRowData05.base LocatorPhase6803ReceiptRowData05.threshold
    LocatorPhase6803ReceiptRowData05.prefixData (LocatorPhase6803ReceiptRowData04.prefixData)
  prefix05 : PrefixRowValid 5 LocatorPhase6803ReceiptRowData05.prefixData (LocatorPhase6803ReceiptRowData06.prefixData)
  state06 : RowValid 6 LocatorPhase6803ReceiptRowData06.base LocatorPhase6803ReceiptRowData06.threshold
    LocatorPhase6803ReceiptRowData06.prefixData (LocatorPhase6803ReceiptRowData05.prefixData)
  prefix06 : PrefixRowValid 6 LocatorPhase6803ReceiptRowData06.prefixData (LocatorPhase6803ReceiptRowData07.prefixData)
  state07 : RowValid 7 LocatorPhase6803ReceiptRowData07.base LocatorPhase6803ReceiptRowData07.threshold
    LocatorPhase6803ReceiptRowData07.prefixData (LocatorPhase6803ReceiptRowData06.prefixData)
  prefix07 : PrefixRowValid 7 LocatorPhase6803ReceiptRowData07.prefixData (LocatorPhase6803ReceiptRowData08.prefixData)
  state08 : RowValid 8 LocatorPhase6803ReceiptRowData08.base LocatorPhase6803ReceiptRowData08.threshold
    LocatorPhase6803ReceiptRowData08.prefixData (LocatorPhase6803ReceiptRowData07.prefixData)
  prefix08 : PrefixRowValid 8 LocatorPhase6803ReceiptRowData08.prefixData (LocatorPhase6803ReceiptRowData09.prefixData)
  state09 : RowValid 9 LocatorPhase6803ReceiptRowData09.base LocatorPhase6803ReceiptRowData09.threshold
    LocatorPhase6803ReceiptRowData09.prefixData (LocatorPhase6803ReceiptRowData08.prefixData)
  prefix09 : PrefixRowValid 9 LocatorPhase6803ReceiptRowData09.prefixData (LocatorPhase6803ReceiptRowData10.prefixData)
  state10 : RowValid 10 LocatorPhase6803ReceiptRowData10.base LocatorPhase6803ReceiptRowData10.threshold
    LocatorPhase6803ReceiptRowData10.prefixData (LocatorPhase6803ReceiptRowData09.prefixData)
  prefix10 : PrefixRowValid 10 LocatorPhase6803ReceiptRowData10.prefixData (LocatorPhase6803ReceiptRowData11.prefixData)
  state11 : RowValid 11 LocatorPhase6803ReceiptRowData11.base LocatorPhase6803ReceiptRowData11.threshold
    LocatorPhase6803ReceiptRowData11.prefixData (LocatorPhase6803ReceiptRowData10.prefixData)
  prefix11 : PrefixRowValid 11 LocatorPhase6803ReceiptRowData11.prefixData (LocatorPhase6803ReceiptRowData12.prefixData)
  state12 : RowValid 12 LocatorPhase6803ReceiptRowData12.base LocatorPhase6803ReceiptRowData12.threshold
    LocatorPhase6803ReceiptRowData12.prefixData (LocatorPhase6803ReceiptRowData11.prefixData)
  prefix12 : PrefixRowValid 12 LocatorPhase6803ReceiptRowData12.prefixData (LocatorPhase6803ReceiptRowData13.prefixData)
  state13 : RowValid 13 LocatorPhase6803ReceiptRowData13.base LocatorPhase6803ReceiptRowData13.threshold
    LocatorPhase6803ReceiptRowData13.prefixData (LocatorPhase6803ReceiptRowData12.prefixData)
  prefix13 : PrefixRowValid 13 LocatorPhase6803ReceiptRowData13.prefixData (LocatorPhase6803ReceiptRowData14.prefixData)
  state14 : RowValid 14 LocatorPhase6803ReceiptRowData14.base LocatorPhase6803ReceiptRowData14.threshold
    LocatorPhase6803ReceiptRowData14.prefixData (LocatorPhase6803ReceiptRowData13.prefixData)
  prefix14 : PrefixRowValid 14 LocatorPhase6803ReceiptRowData14.prefixData (LocatorPhase6803ReceiptRowData15.prefixData)
  state15 : RowValid 15 LocatorPhase6803ReceiptRowData15.base LocatorPhase6803ReceiptRowData15.threshold
    LocatorPhase6803ReceiptRowData15.prefixData (LocatorPhase6803ReceiptRowData14.prefixData)
  prefix15 : PrefixRowValid 15 LocatorPhase6803ReceiptRowData15.prefixData (LocatorPhase6803ReceiptRowData16.prefixData)
  state16 : RowValid 16 LocatorPhase6803ReceiptRowData16.base LocatorPhase6803ReceiptRowData16.threshold
    LocatorPhase6803ReceiptRowData16.prefixData (LocatorPhase6803ReceiptRowData15.prefixData)
  prefix16 : PrefixRowValid 16 LocatorPhase6803ReceiptRowData16.prefixData (LocatorPhase6803ReceiptRowData17.prefixData)
  state17 : RowValid 17 LocatorPhase6803ReceiptRowData17.base LocatorPhase6803ReceiptRowData17.threshold
    LocatorPhase6803ReceiptRowData17.prefixData (LocatorPhase6803ReceiptRowData16.prefixData)
  prefix17 : PrefixRowValid 17 LocatorPhase6803ReceiptRowData17.prefixData (LocatorPhase6803ReceiptRowData18.prefixData)
  state18 : RowValid 18 LocatorPhase6803ReceiptRowData18.base LocatorPhase6803ReceiptRowData18.threshold
    LocatorPhase6803ReceiptRowData18.prefixData (LocatorPhase6803ReceiptRowData17.prefixData)
  prefix18 : PrefixRowValid 18 LocatorPhase6803ReceiptRowData18.prefixData (LocatorPhase6803ReceiptRowData19.prefixData)
  state19 : RowValid 19 LocatorPhase6803ReceiptRowData19.base LocatorPhase6803ReceiptRowData19.threshold
    LocatorPhase6803ReceiptRowData19.prefixData (LocatorPhase6803ReceiptRowData18.prefixData)
  prefix19 : PrefixRowValid 19 LocatorPhase6803ReceiptRowData19.prefixData (LocatorPhase6803ReceiptRowData20.prefixData)
  state20 : RowValid 20 LocatorPhase6803ReceiptRowData20.base LocatorPhase6803ReceiptRowData20.threshold
    LocatorPhase6803ReceiptRowData20.prefixData (LocatorPhase6803ReceiptRowData19.prefixData)
  prefix20 : PrefixRowValid 20 LocatorPhase6803ReceiptRowData20.prefixData (LocatorPhase6803ReceiptRowData21.prefixData)
  state21 : RowValid 21 LocatorPhase6803ReceiptRowData21.base LocatorPhase6803ReceiptRowData21.threshold
    LocatorPhase6803ReceiptRowData21.prefixData (LocatorPhase6803ReceiptRowData20.prefixData)
  prefix21 : PrefixRowValid 21 LocatorPhase6803ReceiptRowData21.prefixData (LocatorPhase6803ReceiptRowData22.prefixData)
  state22 : RowValid 22 LocatorPhase6803ReceiptRowData22.base LocatorPhase6803ReceiptRowData22.threshold
    LocatorPhase6803ReceiptRowData22.prefixData (LocatorPhase6803ReceiptRowData21.prefixData)
  prefix22 : PrefixRowValid 22 LocatorPhase6803ReceiptRowData22.prefixData (LocatorPhase6803ReceiptRowData23.prefixData)
  state23 : RowValid 23 LocatorPhase6803ReceiptRowData23.base LocatorPhase6803ReceiptRowData23.threshold
    LocatorPhase6803ReceiptRowData23.prefixData (LocatorPhase6803ReceiptRowData22.prefixData)
  prefix23 : PrefixRowValid 23 LocatorPhase6803ReceiptRowData23.prefixData (LocatorPhase6803ReceiptRowData24.prefixData)
  state24 : RowValid 24 LocatorPhase6803ReceiptRowData24.base LocatorPhase6803ReceiptRowData24.threshold
    LocatorPhase6803ReceiptRowData24.prefixData (LocatorPhase6803ReceiptRowData23.prefixData)
  prefix24 : PrefixRowValid 24 LocatorPhase6803ReceiptRowData24.prefixData (LocatorPhase6803ReceiptRowData25.prefixData)
  state25 : RowValid 25 LocatorPhase6803ReceiptRowData25.base LocatorPhase6803ReceiptRowData25.threshold
    LocatorPhase6803ReceiptRowData25.prefixData (LocatorPhase6803ReceiptRowData24.prefixData)
  prefix25 : PrefixRowValid 25 LocatorPhase6803ReceiptRowData25.prefixData (LocatorPhase6803ReceiptRowData26.prefixData)
  state26 : RowValid 26 LocatorPhase6803ReceiptRowData26.base LocatorPhase6803ReceiptRowData26.threshold
    LocatorPhase6803ReceiptRowData26.prefixData (LocatorPhase6803ReceiptRowData25.prefixData)
  prefix26 : PrefixRowValid 26 LocatorPhase6803ReceiptRowData26.prefixData (LocatorPhase6803ReceiptRowData27.prefixData)
  state27 : RowValid 27 LocatorPhase6803ReceiptRowData27.base LocatorPhase6803ReceiptRowData27.threshold
    LocatorPhase6803ReceiptRowData27.prefixData (LocatorPhase6803ReceiptRowData26.prefixData)
  prefix27 : PrefixRowValid 27 LocatorPhase6803ReceiptRowData27.prefixData (LocatorPhase6803ReceiptRowData28.prefixData)
  state28 : RowValid 28 LocatorPhase6803ReceiptRowData28.base LocatorPhase6803ReceiptRowData28.threshold
    LocatorPhase6803ReceiptRowData28.prefixData (LocatorPhase6803ReceiptRowData27.prefixData)
  prefix28 : PrefixRowValid 28 LocatorPhase6803ReceiptRowData28.prefixData (LocatorPhase6803ReceiptRowData29.prefixData)
  state29 : RowValid 29 LocatorPhase6803ReceiptRowData29.base LocatorPhase6803ReceiptRowData29.threshold
    LocatorPhase6803ReceiptRowData29.prefixData (LocatorPhase6803ReceiptRowData28.prefixData)
  prefix29 : PrefixRowValid 29 LocatorPhase6803ReceiptRowData29.prefixData (fun _ => defaultPrefix)

theorem certificate : Certificate where
  state01 := LocatorPhase6803ReceiptRowCheck01.stateChecked
  prefix01 := LocatorPhase6803ReceiptRowCheck01.prefixChecked
  state02 := LocatorPhase6803ReceiptRowCheck02.stateChecked
  prefix02 := LocatorPhase6803ReceiptRowCheck02.prefixChecked
  state03 := LocatorPhase6803ReceiptRowCheck03.stateChecked
  prefix03 := LocatorPhase6803ReceiptRowCheck03.prefixChecked
  state04 := LocatorPhase6803ReceiptRowCheck04.stateChecked
  prefix04 := LocatorPhase6803ReceiptRowCheck04.prefixChecked
  state05 := LocatorPhase6803ReceiptRowCheck05.stateChecked
  prefix05 := LocatorPhase6803ReceiptRowCheck05.prefixChecked
  state06 := LocatorPhase6803ReceiptRowCheck06.stateChecked
  prefix06 := LocatorPhase6803ReceiptRowCheck06.prefixChecked
  state07 := LocatorPhase6803ReceiptRowCheck07.stateChecked
  prefix07 := LocatorPhase6803ReceiptRowCheck07.prefixChecked
  state08 := LocatorPhase6803ReceiptRowCheck08.stateChecked
  prefix08 := LocatorPhase6803ReceiptRowCheck08.prefixChecked
  state09 := LocatorPhase6803ReceiptRowCheck09.stateChecked
  prefix09 := LocatorPhase6803ReceiptRowCheck09.prefixChecked
  state10 := LocatorPhase6803ReceiptRowCheck10.stateChecked
  prefix10 := LocatorPhase6803ReceiptRowCheck10.prefixChecked
  state11 := LocatorPhase6803ReceiptRowCheck11.stateChecked
  prefix11 := LocatorPhase6803ReceiptRowCheck11.prefixChecked
  state12 := LocatorPhase6803ReceiptRowCheck12.stateChecked
  prefix12 := LocatorPhase6803ReceiptRowCheck12.prefixChecked
  state13 := LocatorPhase6803ReceiptRowCheck13.stateChecked
  prefix13 := LocatorPhase6803ReceiptRowCheck13.prefixChecked
  state14 := LocatorPhase6803ReceiptRowCheck14.stateChecked
  prefix14 := LocatorPhase6803ReceiptRowCheck14.prefixChecked
  state15 := LocatorPhase6803ReceiptRowCheck15.stateChecked
  prefix15 := LocatorPhase6803ReceiptRowCheck15.prefixChecked
  state16 := LocatorPhase6803ReceiptRowCheck16.stateChecked
  prefix16 := LocatorPhase6803ReceiptRowCheck16.prefixChecked
  state17 := LocatorPhase6803ReceiptRowCheck17.stateChecked
  prefix17 := LocatorPhase6803ReceiptRowCheck17.prefixChecked
  state18 := LocatorPhase6803ReceiptRowCheck18.stateChecked
  prefix18 := LocatorPhase6803ReceiptRowCheck18.prefixChecked
  state19 := LocatorPhase6803ReceiptRowCheck19.stateChecked
  prefix19 := LocatorPhase6803ReceiptRowCheck19.prefixChecked
  state20 := LocatorPhase6803ReceiptRowCheck20.stateChecked
  prefix20 := LocatorPhase6803ReceiptRowCheck20.prefixChecked
  state21 := LocatorPhase6803ReceiptRowCheck21.stateChecked
  prefix21 := LocatorPhase6803ReceiptRowCheck21.prefixChecked
  state22 := LocatorPhase6803ReceiptRowCheck22.stateChecked
  prefix22 := LocatorPhase6803ReceiptRowCheck22.prefixChecked
  state23 := LocatorPhase6803ReceiptRowCheck23.stateChecked
  prefix23 := LocatorPhase6803ReceiptRowCheck23.prefixChecked
  state24 := LocatorPhase6803ReceiptRowCheck24.stateChecked
  prefix24 := LocatorPhase6803ReceiptRowCheck24.prefixChecked
  state25 := LocatorPhase6803ReceiptRowCheck25.stateChecked
  prefix25 := LocatorPhase6803ReceiptRowCheck25.prefixChecked
  state26 := LocatorPhase6803ReceiptRowCheck26.stateChecked
  prefix26 := LocatorPhase6803ReceiptRowCheck26.prefixChecked
  state27 := LocatorPhase6803ReceiptRowCheck27.stateChecked
  prefix27 := LocatorPhase6803ReceiptRowCheck27.prefixChecked
  state28 := LocatorPhase6803ReceiptRowCheck28.stateChecked
  prefix28 := LocatorPhase6803ReceiptRowCheck28.prefixChecked
  state29 := LocatorPhase6803ReceiptRowCheck29.stateChecked
  prefix29 := LocatorPhase6803ReceiptRowCheck29.prefixChecked

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCertificate
