import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total20 : ((rows 20).map (price 20)).sum = 126525 := by decide +kernel

theorem row_total21 : ((rows 21).map (price 21)).sum = 140674 := by decide +kernel

theorem row_total22 : ((rows 22).map (price 22)).sum = 154906 := by decide +kernel

theorem row_total23 : ((rows 23).map (price 23)).sum = 168912 := by decide +kernel

theorem row_total24 : ((rows 24).map (price 24)).sum = 182399 := by decide +kernel

theorem row_total25 : ((rows 25).map (price 25)).sum = 195090 := by decide +kernel

theorem row_total26 : ((rows 26).map (price 26)).sum = 206724 := by decide +kernel

theorem row_total27 : ((rows 27).map (price 27)).sum = 217056 := by decide +kernel

theorem row_total28 : ((rows 28).map (price 28)).sum = 226058 := by decide +kernel

theorem row_total29 : ((rows 29).map (price 29)).sum = 233838 := by decide +kernel

theorem row_total30 : ((rows 30).map (price 30)).sum = 240435 := by decide +kernel

theorem row_total31 : ((rows 31).map (price 31)).sum = 245952 := by decide +kernel

theorem row_total32 : ((rows 32).map (price 32)).sum = 250557 := by decide +kernel

theorem row_total33 : ((rows 33).map (price 33)).sum = 254349 := by decide +kernel

end Low51At2403AnchorRankReceipt
