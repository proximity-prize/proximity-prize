import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData04
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData05
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData06
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData07
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData08
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData09
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData10
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData11
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData12
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData13
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData14
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData15
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData16
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData17
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData18
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData19
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData20
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData21
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData22
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData23
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData24
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData25
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData26
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData27
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData28

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptDirectData

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def defaultThreshold : ThresholdReceipt := LocatorPhase6800ReceiptCellCore.defaultThreshold
def defaultPrefix : PrefixReceipt := LocatorPhase6800ReceiptCellCore.defaultPrefix

def thresholdRow1 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData01.threshold
def thresholdRow2 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData02.threshold
def thresholdRow3 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData03.threshold
def thresholdRow4 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData04.threshold
def thresholdRow5 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData05.threshold
def thresholdRow6 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData06.threshold
def thresholdRow7 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData07.threshold
def thresholdRow8 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData08.threshold
def thresholdRow9 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData09.threshold
def thresholdRow10 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData10.threshold
def thresholdRow11 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData11.threshold
def thresholdRow12 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData12.threshold
def thresholdRow13 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData13.threshold
def thresholdRow14 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData14.threshold
def thresholdRow15 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData15.threshold
def thresholdRow16 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData16.threshold
def thresholdRow17 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData17.threshold
def thresholdRow18 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData18.threshold
def thresholdRow19 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData19.threshold
def thresholdRow20 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData20.threshold
def thresholdRow21 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData21.threshold
def thresholdRow22 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData22.threshold
def thresholdRow23 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData23.threshold
def thresholdRow24 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData24.threshold
def thresholdRow25 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData25.threshold
def thresholdRow26 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData26.threshold
def thresholdRow27 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData27.threshold
def thresholdRow28 : ℕ → ThresholdReceipt := LocatorPhase6800ReceiptRowData28.threshold

def lookupThreshold (r v : ℕ) : ThresholdReceipt :=
  match r with
  | 1 => thresholdRow1 v
  | 2 => thresholdRow2 v
  | 3 => thresholdRow3 v
  | 4 => thresholdRow4 v
  | 5 => thresholdRow5 v
  | 6 => thresholdRow6 v
  | 7 => thresholdRow7 v
  | 8 => thresholdRow8 v
  | 9 => thresholdRow9 v
  | 10 => thresholdRow10 v
  | 11 => thresholdRow11 v
  | 12 => thresholdRow12 v
  | 13 => thresholdRow13 v
  | 14 => thresholdRow14 v
  | 15 => thresholdRow15 v
  | 16 => thresholdRow16 v
  | 17 => thresholdRow17 v
  | 18 => thresholdRow18 v
  | 19 => thresholdRow19 v
  | 20 => thresholdRow20 v
  | 21 => thresholdRow21 v
  | 22 => thresholdRow22 v
  | 23 => thresholdRow23 v
  | 24 => thresholdRow24 v
  | 25 => thresholdRow25 v
  | 26 => thresholdRow26 v
  | 27 => thresholdRow27 v
  | 28 => thresholdRow28 v
  | _ => defaultThreshold

def prefixRow1 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData01.prefixData
def prefixRow2 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData02.prefixData
def prefixRow3 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData03.prefixData
def prefixRow4 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData04.prefixData
def prefixRow5 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData05.prefixData
def prefixRow6 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData06.prefixData
def prefixRow7 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData07.prefixData
def prefixRow8 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData08.prefixData
def prefixRow9 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData09.prefixData
def prefixRow10 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData10.prefixData
def prefixRow11 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData11.prefixData
def prefixRow12 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData12.prefixData
def prefixRow13 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData13.prefixData
def prefixRow14 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData14.prefixData
def prefixRow15 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData15.prefixData
def prefixRow16 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData16.prefixData
def prefixRow17 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData17.prefixData
def prefixRow18 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData18.prefixData
def prefixRow19 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData19.prefixData
def prefixRow20 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData20.prefixData
def prefixRow21 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData21.prefixData
def prefixRow22 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData22.prefixData
def prefixRow23 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData23.prefixData
def prefixRow24 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData24.prefixData
def prefixRow25 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData25.prefixData
def prefixRow26 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData26.prefixData
def prefixRow27 : ℕ → PrefixReceipt := LocatorPhase6800ReceiptRowData27.prefixData

def lookupPrefix (r v : ℕ) : PrefixReceipt :=
  match r with
  | 1 => prefixRow1 v
  | 2 => prefixRow2 v
  | 3 => prefixRow3 v
  | 4 => prefixRow4 v
  | 5 => prefixRow5 v
  | 6 => prefixRow6 v
  | 7 => prefixRow7 v
  | 8 => prefixRow8 v
  | 9 => prefixRow9 v
  | 10 => prefixRow10 v
  | 11 => prefixRow11 v
  | 12 => prefixRow12 v
  | 13 => prefixRow13 v
  | 14 => prefixRow14 v
  | 15 => prefixRow15 v
  | 16 => prefixRow16 v
  | 17 => prefixRow17 v
  | 18 => prefixRow18 v
  | 19 => prefixRow19 v
  | 20 => prefixRow20 v
  | 21 => prefixRow21 v
  | 22 => prefixRow22 v
  | 23 => prefixRow23 v
  | 24 => prefixRow24 v
  | 25 => prefixRow25 v
  | 26 => prefixRow26 v
  | 27 => prefixRow27 v
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptDirectData
