import ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdPrefixData

/-! Direct lookup for all 29 threshold rows and 28 prefix rows. -/
section PackedLocator_LocatorPhase6802ReceiptDirectData
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ReceiptDirectData
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore
set_option autoImplicit false
set_option maxRecDepth 100000

def defaultThreshold : ThresholdReceipt := LocatorPhase6802ReceiptCellCore.defaultThreshold
def defaultPrefix : PrefixReceipt := LocatorPhase6802ReceiptCellCore.defaultPrefix

def thresholdRow1 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData01.threshold
def thresholdRow2 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData02.threshold
def thresholdRow3 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData03.threshold
def thresholdRow4 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData04.threshold
def thresholdRow5 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData05.threshold
def thresholdRow6 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData06.threshold
def thresholdRow7 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData07.threshold
def thresholdRow8 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData08.threshold
def thresholdRow9 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData09.threshold
def thresholdRow10 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData10.threshold
def thresholdRow11 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData11.threshold
def thresholdRow12 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData12.threshold
def thresholdRow13 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData13.threshold
def thresholdRow14 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData14.threshold
def thresholdRow15 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData15.threshold
def thresholdRow16 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData16.threshold
def thresholdRow17 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData17.threshold
def thresholdRow18 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData18.threshold
def thresholdRow19 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData19.threshold
def thresholdRow20 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData20.threshold
def thresholdRow21 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData21.threshold
def thresholdRow22 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData22.threshold
def thresholdRow23 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData23.threshold
def thresholdRow24 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData24.threshold
def thresholdRow25 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData25.threshold
def thresholdRow26 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData26.threshold
def thresholdRow27 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData27.threshold
def thresholdRow28 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData28.threshold
def thresholdRow29 : ℕ → ThresholdReceipt := LocatorPhase6802ReceiptRowData29.threshold

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
  | 29 => thresholdRow29 v
  | _ => defaultThreshold

def prefixRow1 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData01.prefixData
def prefixRow2 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData02.prefixData
def prefixRow3 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData03.prefixData
def prefixRow4 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData04.prefixData
def prefixRow5 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData05.prefixData
def prefixRow6 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData06.prefixData
def prefixRow7 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData07.prefixData
def prefixRow8 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData08.prefixData
def prefixRow9 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData09.prefixData
def prefixRow10 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData10.prefixData
def prefixRow11 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData11.prefixData
def prefixRow12 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData12.prefixData
def prefixRow13 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData13.prefixData
def prefixRow14 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData14.prefixData
def prefixRow15 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData15.prefixData
def prefixRow16 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData16.prefixData
def prefixRow17 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData17.prefixData
def prefixRow18 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData18.prefixData
def prefixRow19 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData19.prefixData
def prefixRow20 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData20.prefixData
def prefixRow21 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData21.prefixData
def prefixRow22 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData22.prefixData
def prefixRow23 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData23.prefixData
def prefixRow24 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData24.prefixData
def prefixRow25 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData25.prefixData
def prefixRow26 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData26.prefixData
def prefixRow27 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData27.prefixData
def prefixRow28 : ℕ → PrefixReceipt := LocatorPhase6802ReceiptRowData28.prefixData

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
  | 28 => prefixRow28 v
  | _ => defaultPrefix

end ProximityPrize.SubmissionLower.LocatorPhase6802ReceiptDirectData
end PackedLocator_LocatorPhase6802ReceiptDirectData
