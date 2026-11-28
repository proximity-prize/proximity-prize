import ProximityPrize.SubmissionLower.R6970Height2313ReceiptIndex
import ProximityPrize.SubmissionLower.Bundle6970_7a0ead0a3fc2768d
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.R6970Height2313MeasuredTests03

section Pack_R6970Height2313ExplicitRows42

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows42_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows42_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6438 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow0 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6438 : IndexedReceipts.checked rows6438 = true := by decide +kernel
theorem route6438 (i : Fin 4) : (rows6438.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6438 ⟨i.val,i.isLt⟩

private def rows6442 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow1 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6442 : IndexedReceipts.checked rows6442 = true := by decide +kernel
theorem route6442 (i : Fin 10) : (rows6442.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6442 ⟨i.val,i.isLt⟩

private def rows6458 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow2 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6458 : IndexedReceipts.checked rows6458 = true := by decide +kernel
theorem route6458 (i : Fin 10) : (rows6458.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6458 ⟨i.val,i.isLt⟩

private def rows6474 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow3 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6474 : IndexedReceipts.checked rows6474 = true := by decide +kernel
theorem route6474 (i : Fin 10) : (rows6474.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6474 ⟨i.val,i.isLt⟩

private def rows6490 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow4 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6490 : IndexedReceipts.checked rows6490 = true := by decide +kernel
theorem route6490 (i : Fin 10) : (rows6490.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6490 ⟨i.val,i.isLt⟩

private def rows6506 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow5 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6506 : IndexedReceipts.checked rows6506 = true := by decide +kernel
theorem route6506 (i : Fin 10) : (rows6506.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6506 ⟨i.val,i.isLt⟩

private def rows6522 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows42_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows42_pairRow6 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6522 : IndexedReceipts.checked rows6522 = true := by decide +kernel
theorem route6522 (i : Fin 10) : (rows6522.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6522 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows42

section Pack_R6970Height2313ExplicitRows43

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows43_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows43_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6538 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow0 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6538 : IndexedReceipts.checked rows6538 = true := by decide +kernel
theorem route6538 (i : Fin 10) : (rows6538.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6538 ⟨i.val,i.isLt⟩

private def rows6554 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow1 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6554 : IndexedReceipts.checked rows6554 = true := by decide +kernel
theorem route6554 (i : Fin 10) : (rows6554.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6554 ⟨i.val,i.isLt⟩

private def rows6570 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow2 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6570 : IndexedReceipts.checked rows6570 = true := by decide +kernel
theorem route6570 (i : Fin 10) : (rows6570.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6570 ⟨i.val,i.isLt⟩

private def rows6586 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow3 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6586 : IndexedReceipts.checked rows6586 = true := by decide +kernel
theorem route6586 (i : Fin 10) : (rows6586.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6586 ⟨i.val,i.isLt⟩

private def rows6602 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow4 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6602 : IndexedReceipts.checked rows6602 = true := by decide +kernel
theorem route6602 (i : Fin 10) : (rows6602.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6602 ⟨i.val,i.isLt⟩

private def rows6618 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow5 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6618 : IndexedReceipts.checked rows6618 = true := by decide +kernel
theorem route6618 (i : Fin 10) : (rows6618.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6618 ⟨i.val,i.isLt⟩

private def rows6634 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows43_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows43_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows43_decision0⟩]
private theorem paid6634 : IndexedReceipts.checked rows6634 = true := by decide +kernel
theorem route6634 (i : Fin 3) : (rows6634.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6634 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows43

section Pack_R6970Height2313ExplicitRows44

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows44_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,25,some 25,axisLo,some axisLo,385979,[MeasuredChoices.test924],rect⟩
private def pack_R6970Height2313ExplicitRows44_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,39,some 39,axisLo,some axisLo,385979,[MeasuredChoices.test1105],rect⟩
private def pack_R6970Height2313ExplicitRows44_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,38,some 38,axisLo,some axisLo,385979,[MeasuredChoices.test1092],rect⟩
private def pack_R6970Height2313ExplicitRows44_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows44_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows44_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows6639 : List IndexedReceipts.Receipt := [
  ⟨⟨63,63,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩]
private theorem paid6639 : IndexedReceipts.checked rows6639 = true := by decide +kernel
theorem route6639 (i : Fin 1) : (rows6639.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6639 ⟨i.val,i.isLt⟩

private def rows3223 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,33,some 33,0,none,385979,[MeasuredChoices.test1029],[]⟩,2,.pair pack_R6970Height2313ExplicitRows44_decision2⟩,
  ⟨⟨50,63,10,3,29,some 29,0,none,385979,[MeasuredChoices.test977],[]⟩,2,.pair pack_R6970Height2313ExplicitRows44_decision2⟩,
  ⟨⟨50,63,10,3,28,some 28,0,none,385979,[MeasuredChoices.test966],[]⟩,2,.pair pack_R6970Height2313ExplicitRows44_decision2⟩,
  ⟨⟨50,63,10,3,27,some 27,0,none,385979,[MeasuredChoices.test952],[]⟩,2,.pair pack_R6970Height2313ExplicitRows44_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 26 [AxisChoices.test1847],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 27 [AxisChoices.test1848],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 31 [AxisChoices.test1852],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 32 [AxisChoices.test1853],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 33 [AxisChoices.test1854],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.excluded none⟩]
private theorem paid3223 : IndexedReceipts.checked rows3223 = true := by decide +kernel
theorem route3223 (i : Fin 24) : (rows3223.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3223 ⟨i.val,i.isLt⟩

private def rows3176 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 38 [AxisChoices.test1859],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow1 39 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows44_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩]
private theorem paid3176 : IndexedReceipts.checked rows3176 = true := by decide +kernel
theorem route3176 (i : Fin 24) : (rows3176.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3176 ⟨i.val,i.isLt⟩

private def rows3204 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 25 [AxisChoices.test1845,AxisChoices.test1846],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 26 [AxisChoices.test1847],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 27 [AxisChoices.test1848],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 28 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 29 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 30 [AxisChoices.test1848,AxisChoices.test1851],2,.pair pack_R6970Height2313ExplicitRows44_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 31 [AxisChoices.test1852],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 32 [AxisChoices.test1853],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 33 [AxisChoices.test1854],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 34 [AxisChoices.test1854,AxisChoices.test1855],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 35 [AxisChoices.test1854,AxisChoices.test1856],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 36 [AxisChoices.test1854,AxisChoices.test1857],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows44_pairRow2 38 [AxisChoices.test1859],2,.excluded none⟩]
private theorem paid3204 : IndexedReceipts.checked rows3204 = true := by decide +kernel
theorem route3204 (i : Fin 16) : (rows3204.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3204 ⟨i.val,i.isLt⟩

private def rows3400 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,1,1,some 1,0,none,128659,[],[]⟩,2,.pair ⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,0,some 0,0,none,128659,[],[]⟩,2,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid3400 : IndexedReceipts.checked rows3400 = true := by decide +kernel
theorem route3400 (i : Fin 2) : (rows3400.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3400 ⟨i.val,i.isLt⟩

private def rows3402 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,2,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,722,12,2,49,some 50,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,2,.pair ⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩,
  ⟨⟨64,722,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,2,.pair ⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,2,.pair ⟨(.node 12122407664504094),.intersection,.impossible,304553⟩⟩,
  ⟨⟨64,722,12,2,23,some 24,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,2,.pair ⟨(.node 8075014212150647),.intersection,.impossible,304158⟩⟩]
private theorem paid3402 : IndexedReceipts.checked rows3402 = true := by decide +kernel
theorem route3402 (i : Fin 6) : (rows3402.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3402 ⟨i.val,i.isLt⟩

private def rows3403 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,2,.excluded none⟩]
private theorem paid3403 : IndexedReceipts.checked rows3403 = true := by decide +kernel
theorem route3403 (i : Fin 1) : (rows3403.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3403 ⟨i.val,i.isLt⟩

private def rows3406 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,49,some 50,0,none,289917,[MeasuredChoices.test104,MeasuredChoices.test118],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩]
private theorem paid3406 : IndexedReceipts.checked rows3406 = true := by decide +kernel
theorem route3406 (i : Fin 1) : (rows3406.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3406 ⟨i.val,i.isLt⟩

private def rows3409 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,41,some 44,0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩]
private theorem paid3409 : IndexedReceipts.checked rows3409 = true := by decide +kernel
theorem route3409 (i : Fin 1) : (rows3409.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3409 ⟨i.val,i.isLt⟩

private def rows3417 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,23,some 24,0,none,304158,[MeasuredChoices.test215,MeasuredChoices.test216],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩]
private theorem paid3417 : IndexedReceipts.checked rows3417 = true := by decide +kernel
theorem route3417 (i : Fin 1) : (rows3417.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3417 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows44

section Pack_R6970Height2313ExplicitRows45

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows45_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows45_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows45_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows45_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows3418 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,21,some 22,0,none,257319,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,2,17,some 20,0,none,257319,[],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩]
private theorem paid3418 : IndexedReceipts.checked rows3418 = true := by decide +kernel
theorem route3418 (i : Fin 2) : (rows3418.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3418 ⟨i.val,i.isLt⟩

private def rows5420 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 27 [AxisChoices.test1848],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow0 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5420 : IndexedReceipts.checked rows5420 = true := by decide +kernel
theorem route5420 (i : Fin 21) : (rows5420.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5420 ⟨i.val,i.isLt⟩

private def rows5442 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5442 : IndexedReceipts.checked rows5442 = true := by decide +kernel
theorem route5442 (i : Fin 24) : (rows5442.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5442 ⟨i.val,i.isLt⟩

private def rows5470 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5470 : IndexedReceipts.checked rows5470 = true := by decide +kernel
theorem route5470 (i : Fin 10) : (rows5470.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5470 ⟨i.val,i.isLt⟩

private def rows5480 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows45_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5480 : IndexedReceipts.checked rows5480 = true := by decide +kernel
theorem route5480 (i : Fin 24) : (rows5480.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5480 ⟨i.val,i.isLt⟩

private def rows5508 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows45_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5508 : IndexedReceipts.checked rows5508 = true := by decide +kernel
theorem route5508 (i : Fin 10) : (rows5508.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5508 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows45

section Pack_R6970Height2313ExplicitRows46

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows46_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows46_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows46_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows46_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows5518 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5518 : IndexedReceipts.checked rows5518 = true := by decide +kernel
theorem route5518 (i : Fin 24) : (rows5518.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5518 ⟨i.val,i.isLt⟩

private def rows5546 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow0 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5546 : IndexedReceipts.checked rows5546 = true := by decide +kernel
theorem route5546 (i : Fin 10) : (rows5546.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5546 ⟨i.val,i.isLt⟩

private def rows5556 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5556 : IndexedReceipts.checked rows5556 = true := by decide +kernel
theorem route5556 (i : Fin 24) : (rows5556.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5556 ⟨i.val,i.isLt⟩

private def rows5584 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5584 : IndexedReceipts.checked rows5584 = true := by decide +kernel
theorem route5584 (i : Fin 10) : (rows5584.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5584 ⟨i.val,i.isLt⟩

private def rows5594 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows46_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows46_pairRow2 23 [AxisChoices.test1844],2,.three none⟩]
private theorem paid5594 : IndexedReceipts.checked rows5594 = true := by decide +kernel
theorem route5594 (i : Fin 20) : (rows5594.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5594 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows46

section Pack_R6970Height2313ExplicitRows47

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows47_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows47_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows47_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows47_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows47_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows5618 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 27 [AxisChoices.test1848],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow0 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5618 : IndexedReceipts.checked rows5618 = true := by decide +kernel
theorem route5618 (i : Fin 14) : (rows5618.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5618 ⟨i.val,i.isLt⟩

private def rows5632 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5632 : IndexedReceipts.checked rows5632 = true := by decide +kernel
theorem route5632 (i : Fin 24) : (rows5632.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5632 ⟨i.val,i.isLt⟩

private def rows5660 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5660 : IndexedReceipts.checked rows5660 = true := by decide +kernel
theorem route5660 (i : Fin 10) : (rows5660.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5660 ⟨i.val,i.isLt⟩

private def rows5670 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5670 : IndexedReceipts.checked rows5670 = true := by decide +kernel
theorem route5670 (i : Fin 24) : (rows5670.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5670 ⟨i.val,i.isLt⟩

private def rows5698 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5698 : IndexedReceipts.checked rows5698 = true := by decide +kernel
theorem route5698 (i : Fin 10) : (rows5698.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5698 ⟨i.val,i.isLt⟩

private def rows5708 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows47_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows47_decision0⟩]
private theorem paid5708 : IndexedReceipts.checked rows5708 = true := by decide +kernel
theorem route5708 (i : Fin 9) : (rows5708.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5708 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows47

section Pack_R6970Height2313ExplicitRows48

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows48_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows48_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows48_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows48_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows5720 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 27 [AxisChoices.test1848],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩]
private theorem paid5720 : IndexedReceipts.checked rows5720 = true := by decide +kernel
theorem route5720 (i : Fin 24) : (rows5720.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5720 ⟨i.val,i.isLt⟩

private def rows5745 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow0 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5745 : IndexedReceipts.checked rows5745 = true := by decide +kernel
theorem route5745 (i : Fin 1) : (rows5745.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5745 ⟨i.val,i.isLt⟩

private def rows5746 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5746 : IndexedReceipts.checked rows5746 = true := by decide +kernel
theorem route5746 (i : Fin 24) : (rows5746.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5746 ⟨i.val,i.isLt⟩

private def rows5774 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5774 : IndexedReceipts.checked rows5774 = true := by decide +kernel
theorem route5774 (i : Fin 10) : (rows5774.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5774 ⟨i.val,i.isLt⟩

private def rows5784 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows48_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5784 : IndexedReceipts.checked rows5784 = true := by decide +kernel
theorem route5784 (i : Fin 24) : (rows5784.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5784 ⟨i.val,i.isLt⟩

private def rows5812 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows48_pairRow2 33 [AxisChoices.test1854],2,.three none⟩]
private theorem paid5812 : IndexedReceipts.checked rows5812 = true := by decide +kernel
theorem route5812 (i : Fin 6) : (rows5812.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5812 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows48

section Pack_R6970Height2313ExplicitRows49

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows49_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows49_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows49_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows49_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows49_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows5818 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow0 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow0 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow0 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow0 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5818 : IndexedReceipts.checked rows5818 = true := by decide +kernel
theorem route5818 (i : Fin 4) : (rows5818.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5818 ⟨i.val,i.isLt⟩

private def rows5822 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5822 : IndexedReceipts.checked rows5822 = true := by decide +kernel
theorem route5822 (i : Fin 24) : (rows5822.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5822 ⟨i.val,i.isLt⟩

private def rows5850 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow1 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5850 : IndexedReceipts.checked rows5850 = true := by decide +kernel
theorem route5850 (i : Fin 10) : (rows5850.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5850 ⟨i.val,i.isLt⟩

private def rows5860 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 19 [AxisChoices.test1840],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 20 [AxisChoices.test1841],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 21 [AxisChoices.test1842],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 27 [AxisChoices.test1848],2,.three none⟩]
private theorem paid5860 : IndexedReceipts.checked rows5860 = true := by decide +kernel
theorem route5860 (i : Fin 24) : (rows5860.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5860 ⟨i.val,i.isLt⟩

private def rows5888 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5888 : IndexedReceipts.checked rows5888 = true := by decide +kernel
theorem route5888 (i : Fin 10) : (rows5888.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5888 ⟨i.val,i.isLt⟩

private def rows5898 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows49_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 16 [AxisChoices.test1837],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 18 [AxisChoices.test1839],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows49_pairRow3 19 [AxisChoices.test1840],2,.three none⟩]
private theorem paid5898 : IndexedReceipts.checked rows5898 = true := by decide +kernel
theorem route5898 (i : Fin 16) : (rows5898.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5898 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows49

section Pack_R6970Height2313ExplicitRows50

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows50_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows50_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,13,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test770],rect⟩
private def pack_R6970Height2313ExplicitRows50_decision0 : PairPrices.Decision := ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩
private def pack_R6970Height2313ExplicitRows50_decision1 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows50_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows50_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩

private def rows5918 : List IndexedReceipts.Receipt := [
  ⟨⟨63,63,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩,2,.three none⟩,
  ⟨⟨63,63,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩,2,.three none⟩]
private theorem paid5918 : IndexedReceipts.checked rows5918 = true := by decide +kernel
theorem route5918 (i : Fin 2) : (rows5918.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5918 ⟨i.val,i.isLt⟩

private def rows3420 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,13,some 16,0,none,257319,[],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,2,9,some 12,0,none,257319,[],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,2,4,some 8,0,none,257319,[],[]⟩,2,.pair ⟨.surface,.whole,.impossible,0⟩⟩]
private theorem paid3420 : IndexedReceipts.checked rows3420 = true := by decide +kernel
theorem route3420 (i : Fin 3) : (rows3420.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3420 ⟨i.val,i.isLt⟩

private def rows3423 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision0⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision3⟩]
private theorem paid3423 : IndexedReceipts.checked rows3423 = true := by decide +kernel
theorem route3423 (i : Fin 5) : (rows3423.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3423 ⟨i.val,i.isLt⟩

private def rows3430 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 0 [AxisChoices.test1821],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 1 [AxisChoices.test1822],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 2 [AxisChoices.test1823],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 5 [AxisChoices.test1826],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 8 [AxisChoices.test1829],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 9 [AxisChoices.test1830],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 12 [AxisChoices.test1833],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 13 [AxisChoices.test1834],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 14 [AxisChoices.test1835],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 15 [AxisChoices.test1836],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 16 [AxisChoices.test1837],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 18 [AxisChoices.test1839],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 19 [AxisChoices.test1840],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow0 20 [AxisChoices.test1841],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 0 [AxisChoices.test1821],3,.pair ⟨.separate,.intersection,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 1 [AxisChoices.test1822],3,.pair ⟨.separate,.intersection,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 2 [AxisChoices.test1823],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 5 [AxisChoices.test1826],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 8 [AxisChoices.test1829],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 9 [AxisChoices.test1830],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 12 [AxisChoices.test1833],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 13 [AxisChoices.test1834],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 14 [AxisChoices.test1835],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 15 [AxisChoices.test1836],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩]
private theorem paid3430 : IndexedReceipts.checked rows3430 = true := by decide +kernel
theorem route3430 (i : Fin 24) : (rows3430.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3430 ⟨i.val,i.isLt⟩

private def rows3467 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows50_pairRow1 16 [AxisChoices.test1837],3,.pair pack_R6970Height2313ExplicitRows50_decision1⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩]
private theorem paid3467 : IndexedReceipts.checked rows3467 = true := by decide +kernel
theorem route3467 (i : Fin 2) : (rows3467.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3467 ⟨i.val,i.isLt⟩

private def rows3469 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision0⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision3⟩]
private theorem paid3469 : IndexedReceipts.checked rows3469 = true := by decide +kernel
theorem route3469 (i : Fin 5) : (rows3469.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3469 ⟨i.val,i.isLt⟩

private def rows3482 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩]
private theorem paid3482 : IndexedReceipts.checked rows3482 = true := by decide +kernel
theorem route3482 (i : Fin 1) : (rows3482.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3482 ⟨i.val,i.isLt⟩

private def rows3483 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision0⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision3⟩]
private theorem paid3483 : IndexedReceipts.checked rows3483 = true := by decide +kernel
theorem route3483 (i : Fin 6) : (rows3483.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3483 ⟨i.val,i.isLt⟩

private def rows3498 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩]
private theorem paid3498 : IndexedReceipts.checked rows3498 = true := by decide +kernel
theorem route3498 (i : Fin 1) : (rows3498.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3498 ⟨i.val,i.isLt⟩

private def rows3499 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,3,.pair ⟨.marked,.intersection,.impossible,0⟩⟩,
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision0⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision3⟩]
private theorem paid3499 : IndexedReceipts.checked rows3499 = true := by decide +kernel
theorem route3499 (i : Fin 7) : (rows3499.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3499 ⟨i.val,i.isLt⟩

private def rows7001 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,40,some 40,0,none,385979,[MeasuredChoices.test1120],[]⟩,3,.pair ⟨.marked,.intersection,.impossible,0⟩⟩,
  ⟨⟨33,40,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,3,.pair pack_R6970Height2313ExplicitRows50_decision2⟩]
private theorem paid7001 : IndexedReceipts.checked rows7001 = true := by decide +kernel
theorem route7001 (i : Fin 2) : (rows7001.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7001 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows50

section Pack_R6970Height2313ExplicitRows51

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows51_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows51_pairRow1 (axisLo : ℕ) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩
private def pack_R6970Height2313ExplicitRows51_pairRow2 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨41,49,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows51_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows51_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows51_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows3517 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩]
private theorem paid3517 : IndexedReceipts.checked rows3517 = true := by decide +kernel
theorem route3517 (i : Fin 1) : (rows3517.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3517 ⟨i.val,i.isLt⟩

private def rows3518 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 0 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 1 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 62 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 63 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 64 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 41 (some 48) [MeasuredChoices.test50],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 33 (some 40) [MeasuredChoices.test44],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 29 (some 32) [MeasuredChoices.test39],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 25 (some 28) [MeasuredChoices.test36],3,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 21 (some 24) [MeasuredChoices.test25],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 17 (some 20) [],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 13 (some 16) [],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 9 (some 12) [],3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow2 4 (some 8) [],3,.pair ⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 2 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 3 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 4 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 5 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 6 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 7 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 8 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 9 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 10 [],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩]
private theorem paid3518 : IndexedReceipts.checked rows3518 = true := by decide +kernel
theorem route3518 (i : Fin 24) : (rows3518.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3518 ⟨i.val,i.isLt⟩

private def rows3530 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 22 [AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 23 [AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 25 [AxisChoices.test1788],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 26 [AxisChoices.test1788,AxisChoices.test1789],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 28 [AxisChoices.test1791],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],3,.pair pack_R6970Height2313ExplicitRows51_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩]
private theorem paid3530 : IndexedReceipts.checked rows3530 = true := by decide +kernel
theorem route3530 (i : Fin 24) : (rows3530.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3530 ⟨i.val,i.isLt⟩

private def rows3556 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 56 [AxisChoices.test1819],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 57 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 58 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 59 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 60 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow0 61 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩]
private theorem paid3556 : IndexedReceipts.checked rows3556 = true := by decide +kernel
theorem route3556 (i : Fin 16) : (rows3556.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3556 ⟨i.val,i.isLt⟩

private def rows3595 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,41,some 44,0,none,385979,[MeasuredChoices.test1133],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨⟨41,49,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨⟨41,49,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨⟨41,49,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨⟨41,49,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows51_decision2⟩]
private theorem paid3595 : IndexedReceipts.checked rows3595 = true := by decide +kernel
theorem route3595 (i : Fin 6) : (rows3595.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3595 ⟨i.val,i.isLt⟩

private def rows3609 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,3,.pair ⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 0,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 1,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 2,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 3,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 4,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows51_pairRow1 5,3,.pair pack_R6970Height2313ExplicitRows51_decision1⟩]
private theorem paid3609 : IndexedReceipts.checked rows3609 = true := by decide +kernel
theorem route3609 (i : Fin 7) : (rows3609.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3609 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows51

section Pack_R6970Height2313ExplicitRows52

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows52_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows52_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows52_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows52_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows52_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows52_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows52_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows3617 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 6 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 7 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 8 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,3,.pair ⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨50,63,10,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,3,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨50,63,10,2,25,some 26,0,none,257319,[MeasuredChoices.test36],[]⟩,3,.pair ⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩,
  ⟨⟨50,63,10,2,4,some 8,0,none,257319,[],[]⟩,3,.pair ⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 9 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 10 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow0 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩]
private theorem paid3617 : IndexedReceipts.checked rows3617 = true := by decide +kernel
theorem route3617 (i : Fin 24) : (rows3617.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3617 ⟨i.val,i.isLt⟩

private def rows3633 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩]
private theorem paid3633 : IndexedReceipts.checked rows3633 = true := by decide +kernel
theorem route3633 (i : Fin 24) : (rows3633.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3633 ⟨i.val,i.isLt⟩

private def rows3667 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 56 [AxisChoices.test1819],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow1 57 [AxisChoices.test1819,AxisChoices.test1820],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 0 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 1 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 2 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 3 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 4 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 5 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 6 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 7 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 8 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 9 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 10 [],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows52_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow2 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩]
private theorem paid3667 : IndexedReceipts.checked rows3667 = true := by decide +kernel
theorem route3667 (i : Fin 24) : (rows3667.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3667 ⟨i.val,i.isLt⟩

private def rows3691 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows52_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows52_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩]
private theorem paid3691 : IndexedReceipts.checked rows3691 = true := by decide +kernel
theorem route3691 (i : Fin 5) : (rows3691.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3691 ⟨i.val,i.isLt⟩

private def rows4004 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,29,some 32,0,none,300842,[MeasuredChoices.test165],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩]
private theorem paid4004 : IndexedReceipts.checked rows4004 = true := by decide +kernel
theorem route4004 (i : Fin 1) : (rows4004.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4004 ⟨i.val,i.isLt⟩

private def rows4006 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,27,some 28,0,none,302619,[MeasuredChoices.test169],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩]
private theorem paid4006 : IndexedReceipts.checked rows4006 = true := by decide +kernel
theorem route4006 (i : Fin 1) : (rows4006.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4006 ⟨i.val,i.isLt⟩

private def rows4019 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,3,.pair pack_R6970Height2313ExplicitRows52_decision2⟩]
private theorem paid4019 : IndexedReceipts.checked rows4019 = true := by decide +kernel
theorem route4019 (i : Fin 1) : (rows4019.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4019 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows52

section Pack_R6970Height2313ExplicitRows53

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows53_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows53_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,55,some 55,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test74],rect⟩
private def pack_R6970Height2313ExplicitRows53_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,55,some 55,axisLo,some axisLo,257319,[MeasuredChoices.test74],rect⟩
private def pack_R6970Height2313ExplicitRows53_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows53_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows53_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows3696 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow0 56 [AxisChoices.test1819],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 0 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 1 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 2 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 3 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩]
private theorem paid3696 : IndexedReceipts.checked rows3696 = true := by decide +kernel
theorem route3696 (i : Fin 24) : (rows3696.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3696 ⟨i.val,i.isLt⟩

private def rows3730 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 4 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 5 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 6 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 7 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 8 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 9 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 10 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow1 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows53_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩]
private theorem paid3730 : IndexedReceipts.checked rows3730 = true := by decide +kernel
theorem route3730 (i : Fin 24) : (rows3730.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3730 ⟨i.val,i.isLt⟩

private def rows3754 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow2 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 0 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 1 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 2 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 3 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 4 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 5 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩]
private theorem paid3754 : IndexedReceipts.checked rows3754 = true := by decide +kernel
theorem route3754 (i : Fin 24) : (rows3754.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3754 ⟨i.val,i.isLt⟩

private def rows3788 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 6 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 7 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 8 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 9 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 10 [],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows53_pairRow3 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows53_decision1⟩]
private theorem paid3788 : IndexedReceipts.checked rows3788 = true := by decide +kernel
theorem route3788 (i : Fin 8) : (rows3788.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3788 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows53

section Pack_R6970Height2313ExplicitRows54

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows54_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows54_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows54_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,53,some 53,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test71],rect⟩
private def pack_R6970Height2313ExplicitRows54_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,53,some 53,axisLo,some axisLo,257319,[MeasuredChoices.test71],rect⟩
private def pack_R6970Height2313ExplicitRows54_pairRow4 (axisLo : ℕ) : PairCell.Row := ⟨50,63,10,2,52,some 52,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩
private def pack_R6970Height2313ExplicitRows54_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows54_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows3796 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow0 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 39 [AxisChoices.test1802],3,.excluded none⟩]
private theorem paid3796 : IndexedReceipts.checked rows3796 = true := by decide +kernel
theorem route3796 (i : Fin 24) : (rows3796.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3796 ⟨i.val,i.isLt⟩

private def rows3822 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 0 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 1 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 2 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 3 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 4 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 5 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 6 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 7 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 8 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 9 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 10 [],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩]
private theorem paid3822 : IndexedReceipts.checked rows3822 = true := by decide +kernel
theorem route3822 (i : Fin 24) : (rows3822.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3822 ⟨i.val,i.isLt⟩

private def rows3853 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow2 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows54_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩]
private theorem paid3853 : IndexedReceipts.checked rows3853 = true := by decide +kernel
theorem route3853 (i : Fin 24) : (rows3853.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3853 ⟨i.val,i.isLt⟩

private def rows3879 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow3 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow4 0,3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow4 1,3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow4 2,3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow4 3,3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows54_pairRow4 4,3,.pair pack_R6970Height2313ExplicitRows54_decision1⟩]
private theorem paid3879 : IndexedReceipts.checked rows3879 = true := by decide +kernel
theorem route3879 (i : Fin 11) : (rows3879.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3879 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows54

section Pack_R6970Height2313ExplicitRows55

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows55_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,52,some 52,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test69],rect⟩
private def pack_R6970Height2313ExplicitRows55_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,52,some 52,axisLo,some axisLo,257319,[MeasuredChoices.test69],rect⟩
private def pack_R6970Height2313ExplicitRows55_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows55_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows55_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows55_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows3896 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 5 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 6 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 7 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 8 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 9 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 10 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow0 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 28 [AxisChoices.test1791],3,.excluded none⟩]
private theorem paid3896 : IndexedReceipts.checked rows3896 = true := by decide +kernel
theorem route3896 (i : Fin 24) : (rows3896.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3896 ⟨i.val,i.isLt⟩

private def rows3920 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 32 [AxisChoices.test1795],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 0 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 1 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 2 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 3 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 4 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 5 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 6 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩]
private theorem paid3920 : IndexedReceipts.checked rows3920 = true := by decide +kernel
theorem route3920 (i : Fin 24) : (rows3920.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3920 ⟨i.val,i.isLt⟩

private def rows3951 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 7 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 8 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 9 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 10 [],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 11 [AxisChoices.test1774],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 12 [AxisChoices.test1775],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 13 [AxisChoices.test1776],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 14 [AxisChoices.test1777],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 15 [AxisChoices.test1778],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 16 [AxisChoices.test1779],3,.pair pack_R6970Height2313ExplicitRows55_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 17 [AxisChoices.test1780],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 18 [AxisChoices.test1781],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow2 19 [AxisChoices.test1782],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 20 [AxisChoices.test1783],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 21 [AxisChoices.test1784],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 24 [AxisChoices.test1787],3,.pair pack_R6970Height2313ExplicitRows55_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 25 [AxisChoices.test1788],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 27 [AxisChoices.test1788,AxisChoices.test1790],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 28 [AxisChoices.test1791],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 29 [AxisChoices.test1791,AxisChoices.test1792],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 32 [AxisChoices.test1795],3,.excluded none⟩]
private theorem paid3951 : IndexedReceipts.checked rows3951 = true := by decide +kernel
theorem route3951 (i : Fin 24) : (rows3951.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3951 ⟨i.val,i.isLt⟩

private def rows3977 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 33 [AxisChoices.test1795,AxisChoices.test1796],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 34 [AxisChoices.test1795,AxisChoices.test1797],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 35 [AxisChoices.test1798],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 36 [AxisChoices.test1798,AxisChoices.test1799],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 37 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 38 [AxisChoices.test1798,AxisChoices.test1800],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 39 [AxisChoices.test1802],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 40 [AxisChoices.test1802,AxisChoices.test1803],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 41 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 42 [AxisChoices.test1802,AxisChoices.test1804],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 43 [AxisChoices.test1802,AxisChoices.test1806],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 44 [AxisChoices.test1802,AxisChoices.test1807],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 45 [AxisChoices.test1802,AxisChoices.test1808],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 46 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows55_pairRow3 47 [AxisChoices.test1802,AxisChoices.test1809],3,.excluded none⟩]
private theorem paid3977 : IndexedReceipts.checked rows3977 = true := by decide +kernel
theorem route3977 (i : Fin 15) : (rows3977.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3977 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows55

section Pack_R6970Height2313ExplicitRows56

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows56_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows56_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows56_pairRow2 (axisLo : ℕ) : PairCell.Row := ⟨64,650,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩
private def pack_R6970Height2313ExplicitRows56_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows56_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,650,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows56_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows56_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows56_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows56_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows56_decision4 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

def cell4071:PairCell.Row:=⟨64,650,12,1,49,some 64,0,none,128659,[MeasuredChoices.test5,MeasuredChoices.test6],[]⟩
def choice4071:PairPrices.Decision:=⟨.affine,.whole,.impossible,0⟩
theorem check4071:PairPrices.valid cell4071 (3:Fin 18) choice4071:=by decide +kernel

def cell4072:PairCell.Row:=⟨64,650,12,1,41,some 48,0,none,128659,[MeasuredChoices.test3,MeasuredChoices.test4],[]⟩
def choice4072:PairPrices.Decision:=⟨.affine,.whole,.impossible,0⟩
theorem check4072:PairPrices.valid cell4072 (3:Fin 18) choice4072:=by decide +kernel

def cell4073:PairCell.Row:=⟨64,650,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩
def choice4073:PairPrices.Decision:=⟨(.node 8028273500198129),.intersection,.impossible,288407⟩
theorem check4073:PairPrices.valid cell4073 (3:Fin 18) choice4073:=by decide +kernel

def cell4074:PairCell.Row:=⟨64,650,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check4074:(cell4074.cap (3:Fin 18)).grade<cell4074.lowerGrade-cell4074.off:=by decide +kernel

def cell4075:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow2 0
def choice4075:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision2
theorem check4075:PairPrices.valid cell4075 (3:Fin 18) choice4075:=by decide +kernel

def cell4076:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow2 1
def choice4076:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision2
theorem check4076:PairPrices.valid cell4076 (3:Fin 18) choice4076:=by decide +kernel

def cell4077:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow2 2
def choice4077:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision2
theorem check4077:PairPrices.valid cell4077 (3:Fin 18) choice4077:=by decide +kernel

def cell4078:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow2 3
def choice4078:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision2
theorem check4078:PairPrices.valid cell4078 (3:Fin 18) choice4078:=by decide +kernel

def cell4079:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow2 4
def choice4079:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision2
theorem check4079:PairPrices.valid cell4079 (3:Fin 18) choice4079:=by decide +kernel

def cell4183:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 41 (some 44) [MeasuredChoices.test49,MeasuredChoices.test50]
def choice4183:PairPrices.Decision:=⟨(.node 8033475077956950),.intersection,.impossible,294092⟩
theorem check4183:PairPrices.valid cell4183 (3:Fin 18) choice4183:=by decide +kernel

def cell4185:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46]
def choice4185:PairPrices.Decision:=⟨(.node 8037210057961988),.intersection,.impossible,296579⟩
theorem check4185:PairPrices.valid cell4185 (3:Fin 18) choice4185:=by decide +kernel

def cell4187:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44]
def choice4187:PairPrices.Decision:=⟨(.node 8042152515659111),.intersection,.impossible,298829⟩
theorem check4187:PairPrices.valid cell4187 (3:Fin 18) choice4187:=by decide +kernel

def cell4189:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 29 (some 32) [MeasuredChoices.test39]
def choice4189:PairPrices.Decision:=⟨(.node 8048914296280450),.intersection,.impossible,300842⟩
theorem check4189:PairPrices.valid cell4189 (3:Fin 18) choice4189:=by decide +kernel

def cell4191:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 27 (some 28) [MeasuredChoices.test37]
def choice4191:PairPrices.Decision:=⟨(.node 8059959167344767),.intersection,.impossible,302619⟩
theorem check4191:PairPrices.valid cell4191 (3:Fin 18) choice4191:=by decide +kernel

def cell4192:PairCell.Row:=⟨64,650,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩
def choice4192:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision4
theorem check4192:PairPrices.valid cell4192 (3:Fin 18) choice4192:=by decide +kernel

def cell4193:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 25 (some 26) [MeasuredChoices.test35,MeasuredChoices.test36]
def choice4193:PairPrices.Decision:=⟨(.node 8066455423319456),.intersection,.impossible,303418⟩
theorem check4193:PairPrices.valid cell4193 (3:Fin 18) choice4193:=by decide +kernel

def cell4198:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 17 (some 20) []
def choice4198:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision4
theorem check4198:PairPrices.valid cell4198 (3:Fin 18) choice4198:=by decide +kernel

def cell4199:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 13 (some 16) []
def choice4199:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision4
theorem check4199:PairPrices.valid cell4199 (3:Fin 18) choice4199:=by decide +kernel

def cell4200:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 9 (some 12) []
def choice4200:PairPrices.Decision:=pack_R6970Height2313ExplicitRows56_decision4
theorem check4200:PairPrices.valid cell4200 (3:Fin 18) choice4200:=by decide +kernel

def cell4201:PairCell.Row:=pack_R6970Height2313ExplicitRows56_pairRow4 4 (some 8) []
def choice4201:PairPrices.Decision:=⟨.surface,.whole,.surface,0⟩
theorem check4201:PairPrices.valid cell4201 (3:Fin 18) choice4201:=by decide +kernel

private def rows3996 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 50,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,3,.pair ⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩]
private theorem paid3996 : IndexedReceipts.checked rows3996 = true := by decide +kernel
theorem route3996 (i : Fin 1) : (rows3996.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3996 ⟨i.val,i.isLt⟩

private def rows4041 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 14 [AxisChoices.test1835],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 15 [AxisChoices.test1836],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 16 [AxisChoices.test1837],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 18 [AxisChoices.test1839],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 19 [AxisChoices.test1840],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 0 [AxisChoices.test1821],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 1 [AxisChoices.test1822],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 2 [AxisChoices.test1823],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 5 [AxisChoices.test1826],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 8 [AxisChoices.test1829],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 14 [AxisChoices.test1835],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 15 [AxisChoices.test1836],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow1 16 [AxisChoices.test1837],3,.pair pack_R6970Height2313ExplicitRows56_decision0⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨50,63,10,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,3,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨50,63,10,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,3,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨50,63,10,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,3,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 0 [AxisChoices.test1821],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 1 [AxisChoices.test1822],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 2 [AxisChoices.test1823],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow0 5 [AxisChoices.test1826],3,.pair pack_R6970Height2313ExplicitRows56_decision1⟩]
private theorem paid4041 : IndexedReceipts.checked rows4041 = true := by decide +kernel
theorem route4041 (i : Fin 21) : (rows4041.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4041 ⟨i.val,i.isLt⟩

private def rows4203 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows56_decision3⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows56_decision3⟩]
private theorem paid4203 : IndexedReceipts.checked rows4203 = true := by decide +kernel
theorem route4203 (i : Fin 4) : (rows4203.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4203 ⟨i.val,i.isLt⟩

private def rows4207 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,4,.pair ⟨.marked,.intersection,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow3 0 [AxisChoices.test1821],4,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow3 1 [AxisChoices.test1822],4,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow3 2 [AxisChoices.test1823],4,.pair pack_R6970Height2313ExplicitRows56_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows56_pairRow3 5 [AxisChoices.test1826],4,.pair pack_R6970Height2313ExplicitRows56_decision0⟩]
private theorem paid4207 : IndexedReceipts.checked rows4207 = true := by decide +kernel
theorem route4207 (i : Fin 5) : (rows4207.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4207 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows56

section Pack_R6970Height2313ExplicitRows57

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows57_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,650,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows57_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,650,12,2,50,some 50,axisLo,some axisLo,257319,[MeasuredChoices.test64],rect⟩
private def pack_R6970Height2313ExplicitRows57_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,650,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows57_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows57_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

def cell4120:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808]
theorem check4120:(cell4120.cap (3:Fin 18)).grade<cell4120.lowerGrade-cell4120.off:=by decide +kernel

def cell4121:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809]
theorem check4121:(cell4121.cap (3:Fin 18)).grade<cell4121.lowerGrade-cell4121.off:=by decide +kernel

def cell4122:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809]
theorem check4122:(cell4122.cap (3:Fin 18)).grade<cell4122.lowerGrade-cell4122.off:=by decide +kernel

def cell4127:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 0 []
def choice4127:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4127:PairPrices.valid cell4127 (3:Fin 18) choice4127:=by decide +kernel

def cell4128:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 1 []
def choice4128:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4128:PairPrices.valid cell4128 (3:Fin 18) choice4128:=by decide +kernel

def cell4129:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 2 []
def choice4129:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4129:PairPrices.valid cell4129 (3:Fin 18) choice4129:=by decide +kernel

def cell4130:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 3 []
def choice4130:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4130:PairPrices.valid cell4130 (3:Fin 18) choice4130:=by decide +kernel

def cell4131:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 4 []
def choice4131:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4131:PairPrices.valid cell4131 (3:Fin 18) choice4131:=by decide +kernel

def cell4132:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 5 []
def choice4132:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4132:PairPrices.valid cell4132 (3:Fin 18) choice4132:=by decide +kernel

def cell4133:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 6 []
def choice4133:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4133:PairPrices.valid cell4133 (3:Fin 18) choice4133:=by decide +kernel

def cell4134:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 7 []
def choice4134:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4134:PairPrices.valid cell4134 (3:Fin 18) choice4134:=by decide +kernel

def cell4135:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 8 []
def choice4135:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4135:PairPrices.valid cell4135 (3:Fin 18) choice4135:=by decide +kernel

def cell4136:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 9 []
def choice4136:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4136:PairPrices.valid cell4136 (3:Fin 18) choice4136:=by decide +kernel

def cell4137:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 10 []
def choice4137:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4137:PairPrices.valid cell4137 (3:Fin 18) choice4137:=by decide +kernel

def cell4138:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 11 [AxisChoices.test1774]
def choice4138:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4138:PairPrices.valid cell4138 (3:Fin 18) choice4138:=by decide +kernel

def cell4139:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 12 [AxisChoices.test1775]
def choice4139:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4139:PairPrices.valid cell4139 (3:Fin 18) choice4139:=by decide +kernel

def cell4140:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 13 [AxisChoices.test1776]
def choice4140:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4140:PairPrices.valid cell4140 (3:Fin 18) choice4140:=by decide +kernel

def cell4141:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 14 [AxisChoices.test1777]
def choice4141:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4141:PairPrices.valid cell4141 (3:Fin 18) choice4141:=by decide +kernel

def cell4142:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 15 [AxisChoices.test1778]
def choice4142:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4142:PairPrices.valid cell4142 (3:Fin 18) choice4142:=by decide +kernel

def cell4143:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 16 [AxisChoices.test1779]
def choice4143:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4143:PairPrices.valid cell4143 (3:Fin 18) choice4143:=by decide +kernel

def cell4144:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 17 [AxisChoices.test1780]
def choice4144:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4144:PairPrices.valid cell4144 (3:Fin 18) choice4144:=by decide +kernel

def cell4145:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 18 [AxisChoices.test1781]
def choice4145:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4145:PairPrices.valid cell4145 (3:Fin 18) choice4145:=by decide +kernel

def cell4146:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 19 [AxisChoices.test1782]
def choice4146:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4146:PairPrices.valid cell4146 (3:Fin 18) choice4146:=by decide +kernel

def cell4147:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 20 [AxisChoices.test1783]
def choice4147:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4147:PairPrices.valid cell4147 (3:Fin 18) choice4147:=by decide +kernel

def cell4148:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 21 [AxisChoices.test1784]
theorem check4148:(cell4148.cap (3:Fin 18)).grade<cell4148.lowerGrade-cell4148.off:=by decide +kernel

def cell4149:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785]
theorem check4149:(cell4149.cap (3:Fin 18)).grade<cell4149.lowerGrade-cell4149.off:=by decide +kernel

def cell4150:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786]
theorem check4150:(cell4150.cap (3:Fin 18)).grade<cell4150.lowerGrade-cell4150.off:=by decide +kernel

def cell4151:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 24 [AxisChoices.test1787]
theorem check4151:(cell4151.cap (3:Fin 18)).grade<cell4151.lowerGrade-cell4151.off:=by decide +kernel

def cell4152:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 25 [AxisChoices.test1788]
theorem check4152:(cell4152.cap (3:Fin 18)).grade<cell4152.lowerGrade-cell4152.off:=by decide +kernel

def cell4153:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789]
theorem check4153:(cell4153.cap (3:Fin 18)).grade<cell4153.lowerGrade-cell4153.off:=by decide +kernel

def cell4154:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790]
theorem check4154:(cell4154.cap (3:Fin 18)).grade<cell4154.lowerGrade-cell4154.off:=by decide +kernel

def cell4155:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 28 [AxisChoices.test1791]
theorem check4155:(cell4155.cap (3:Fin 18)).grade<cell4155.lowerGrade-cell4155.off:=by decide +kernel

def cell4156:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792]
theorem check4156:(cell4156.cap (3:Fin 18)).grade<cell4156.lowerGrade-cell4156.off:=by decide +kernel

def cell4159:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 32 [AxisChoices.test1795]
theorem check4159:(cell4159.cap (3:Fin 18)).grade<cell4159.lowerGrade-cell4159.off:=by decide +kernel

def cell4160:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796]
theorem check4160:(cell4160.cap (3:Fin 18)).grade<cell4160.lowerGrade-cell4160.off:=by decide +kernel

def cell4161:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797]
theorem check4161:(cell4161.cap (3:Fin 18)).grade<cell4161.lowerGrade-cell4161.off:=by decide +kernel

def cell4162:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 35 [AxisChoices.test1798]
theorem check4162:(cell4162.cap (3:Fin 18)).grade<cell4162.lowerGrade-cell4162.off:=by decide +kernel

def cell4163:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799]
theorem check4163:(cell4163.cap (3:Fin 18)).grade<cell4163.lowerGrade-cell4163.off:=by decide +kernel

def cell4164:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800]
theorem check4164:(cell4164.cap (3:Fin 18)).grade<cell4164.lowerGrade-cell4164.off:=by decide +kernel

def cell4165:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800]
theorem check4165:(cell4165.cap (3:Fin 18)).grade<cell4165.lowerGrade-cell4165.off:=by decide +kernel

def cell4166:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 39 [AxisChoices.test1802]
theorem check4166:(cell4166.cap (3:Fin 18)).grade<cell4166.lowerGrade-cell4166.off:=by decide +kernel

def cell4167:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803]
theorem check4167:(cell4167.cap (3:Fin 18)).grade<cell4167.lowerGrade-cell4167.off:=by decide +kernel

def cell4168:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804]
theorem check4168:(cell4168.cap (3:Fin 18)).grade<cell4168.lowerGrade-cell4168.off:=by decide +kernel

def cell4169:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804]
theorem check4169:(cell4169.cap (3:Fin 18)).grade<cell4169.lowerGrade-cell4169.off:=by decide +kernel

def cell4170:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806]
theorem check4170:(cell4170.cap (3:Fin 18)).grade<cell4170.lowerGrade-cell4170.off:=by decide +kernel

def cell4171:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807]
theorem check4171:(cell4171.cap (3:Fin 18)).grade<cell4171.lowerGrade-cell4171.off:=by decide +kernel

def cell4172:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808]
theorem check4172:(cell4172.cap (3:Fin 18)).grade<cell4172.lowerGrade-cell4172.off:=by decide +kernel

def cell4173:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809]
theorem check4173:(cell4173.cap (3:Fin 18)).grade<cell4173.lowerGrade-cell4173.off:=by decide +kernel

def cell4174:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809]
theorem check4174:(cell4174.cap (3:Fin 18)).grade<cell4174.lowerGrade-cell4174.off:=by decide +kernel

def cell4178:PairCell.Row:=⟨64,650,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩
def choice4178:PairPrices.Decision:=⟨(.node 8029965254169422),.intersection,.impossible,290650⟩
theorem check4178:PairPrices.valid cell4178 (3:Fin 18) choice4178:=by decide +kernel

def cell4080:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 5 []
def choice4080:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4080:PairPrices.valid cell4080 (3:Fin 18) choice4080:=by decide +kernel

def cell4081:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 6 []
def choice4081:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4081:PairPrices.valid cell4081 (3:Fin 18) choice4081:=by decide +kernel

def cell4082:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 7 []
def choice4082:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4082:PairPrices.valid cell4082 (3:Fin 18) choice4082:=by decide +kernel

def cell4083:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 8 []
def choice4083:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4083:PairPrices.valid cell4083 (3:Fin 18) choice4083:=by decide +kernel

def cell4084:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 9 []
def choice4084:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4084:PairPrices.valid cell4084 (3:Fin 18) choice4084:=by decide +kernel

def cell4085:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 10 []
def choice4085:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4085:PairPrices.valid cell4085 (3:Fin 18) choice4085:=by decide +kernel

def cell4086:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 11 [AxisChoices.test1774]
def choice4086:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4086:PairPrices.valid cell4086 (3:Fin 18) choice4086:=by decide +kernel

def cell4087:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 12 [AxisChoices.test1775]
def choice4087:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4087:PairPrices.valid cell4087 (3:Fin 18) choice4087:=by decide +kernel

def cell4088:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 13 [AxisChoices.test1776]
def choice4088:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4088:PairPrices.valid cell4088 (3:Fin 18) choice4088:=by decide +kernel

def cell4089:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 14 [AxisChoices.test1777]
def choice4089:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4089:PairPrices.valid cell4089 (3:Fin 18) choice4089:=by decide +kernel

def cell4090:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 15 [AxisChoices.test1778]
def choice4090:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision1
theorem check4090:PairPrices.valid cell4090 (3:Fin 18) choice4090:=by decide +kernel

def cell4091:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 16 [AxisChoices.test1779]
def choice4091:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4091:PairPrices.valid cell4091 (3:Fin 18) choice4091:=by decide +kernel

def cell4092:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 17 [AxisChoices.test1780]
def choice4092:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4092:PairPrices.valid cell4092 (3:Fin 18) choice4092:=by decide +kernel

def cell4093:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 18 [AxisChoices.test1781]
def choice4093:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4093:PairPrices.valid cell4093 (3:Fin 18) choice4093:=by decide +kernel

def cell4094:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow2 19 [AxisChoices.test1782]
def choice4094:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4094:PairPrices.valid cell4094 (3:Fin 18) choice4094:=by decide +kernel

def cell4095:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 20 [AxisChoices.test1783]
def choice4095:PairPrices.Decision:=pack_R6970Height2313ExplicitRows57_decision0
theorem check4095:PairPrices.valid cell4095 (3:Fin 18) choice4095:=by decide +kernel

def cell4096:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 21 [AxisChoices.test1784]
theorem check4096:(cell4096.cap (3:Fin 18)).grade<cell4096.lowerGrade-cell4096.off:=by decide +kernel

def cell4097:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 22 [AxisChoices.test1784,AxisChoices.test1785]
theorem check4097:(cell4097.cap (3:Fin 18)).grade<cell4097.lowerGrade-cell4097.off:=by decide +kernel

def cell4098:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 23 [AxisChoices.test1784,AxisChoices.test1786]
theorem check4098:(cell4098.cap (3:Fin 18)).grade<cell4098.lowerGrade-cell4098.off:=by decide +kernel

def cell4099:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 24 [AxisChoices.test1787]
theorem check4099:(cell4099.cap (3:Fin 18)).grade<cell4099.lowerGrade-cell4099.off:=by decide +kernel

def cell4100:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 25 [AxisChoices.test1788]
theorem check4100:(cell4100.cap (3:Fin 18)).grade<cell4100.lowerGrade-cell4100.off:=by decide +kernel

def cell4101:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 26 [AxisChoices.test1788,AxisChoices.test1789]
theorem check4101:(cell4101.cap (3:Fin 18)).grade<cell4101.lowerGrade-cell4101.off:=by decide +kernel

def cell4102:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790]
theorem check4102:(cell4102.cap (3:Fin 18)).grade<cell4102.lowerGrade-cell4102.off:=by decide +kernel

def cell4103:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 28 [AxisChoices.test1791]
theorem check4103:(cell4103.cap (3:Fin 18)).grade<cell4103.lowerGrade-cell4103.off:=by decide +kernel

def cell4104:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792]
theorem check4104:(cell4104.cap (3:Fin 18)).grade<cell4104.lowerGrade-cell4104.off:=by decide +kernel

def cell4107:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 32 [AxisChoices.test1795]
theorem check4107:(cell4107.cap (3:Fin 18)).grade<cell4107.lowerGrade-cell4107.off:=by decide +kernel

def cell4108:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796]
theorem check4108:(cell4108.cap (3:Fin 18)).grade<cell4108.lowerGrade-cell4108.off:=by decide +kernel

def cell4109:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797]
theorem check4109:(cell4109.cap (3:Fin 18)).grade<cell4109.lowerGrade-cell4109.off:=by decide +kernel

def cell4110:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 35 [AxisChoices.test1798]
theorem check4110:(cell4110.cap (3:Fin 18)).grade<cell4110.lowerGrade-cell4110.off:=by decide +kernel

def cell4111:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799]
theorem check4111:(cell4111.cap (3:Fin 18)).grade<cell4111.lowerGrade-cell4111.off:=by decide +kernel

def cell4112:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800]
theorem check4112:(cell4112.cap (3:Fin 18)).grade<cell4112.lowerGrade-cell4112.off:=by decide +kernel

def cell4113:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800]
theorem check4113:(cell4113.cap (3:Fin 18)).grade<cell4113.lowerGrade-cell4113.off:=by decide +kernel

def cell4114:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 39 [AxisChoices.test1802]
theorem check4114:(cell4114.cap (3:Fin 18)).grade<cell4114.lowerGrade-cell4114.off:=by decide +kernel

def cell4115:PairCell.Row:=pack_R6970Height2313ExplicitRows57_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803]
theorem check4115:(cell4115.cap (3:Fin 18)).grade<cell4115.lowerGrade-cell4115.off:=by decide +kernel

private def rows4216 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,17,some 20,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,4,.pair ⟨.markedAxis,.intersection,.impossible,0⟩⟩,
  ⟨⟨25,27,9,3,17,some 20,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,4,.pair ⟨.markedAxis,.intersection,.impossible,0⟩⟩]
private theorem paid4216 : IndexedReceipts.checked rows4216 = true := by decide +kernel
theorem route4216 (i : Fin 2) : (rows4216.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4216 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows57

section Pack_R6970Height2313ExplicitRows58

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows58_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,650,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows58_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows58_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows58_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows58_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows58_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

def cell4116:PairCell.Row:=pack_R6970Height2313ExplicitRows58_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804]
theorem check4116:(cell4116.cap (3:Fin 18)).grade<cell4116.lowerGrade-cell4116.off:=by decide +kernel

def cell4117:PairCell.Row:=pack_R6970Height2313ExplicitRows58_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804]
theorem check4117:(cell4117.cap (3:Fin 18)).grade<cell4117.lowerGrade-cell4117.off:=by decide +kernel

def cell4118:PairCell.Row:=pack_R6970Height2313ExplicitRows58_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806]
theorem check4118:(cell4118.cap (3:Fin 18)).grade<cell4118.lowerGrade-cell4118.off:=by decide +kernel

def cell4119:PairCell.Row:=pack_R6970Height2313ExplicitRows58_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807]
theorem check4119:(cell4119.cap (3:Fin 18)).grade<cell4119.lowerGrade-cell4119.off:=by decide +kernel

private def rows4220 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 12 [AxisChoices.test1833],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 13 [AxisChoices.test1834],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 14 [AxisChoices.test1835],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 15 [AxisChoices.test1836],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 16 [AxisChoices.test1837],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 18 [AxisChoices.test1839],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 19 [AxisChoices.test1840],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow1 20 [AxisChoices.test1841],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩]
private theorem paid4220 : IndexedReceipts.checked rows4220 = true := by decide +kernel
theorem route4220 (i : Fin 9) : (rows4220.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4220 ⟨i.val,i.isLt⟩

private def rows4232 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩]
private theorem paid4232 : IndexedReceipts.checked rows4232 = true := by decide +kernel
theorem route4232 (i : Fin 4) : (rows4232.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4232 ⟨i.val,i.isLt⟩

private def rows4240 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩]
private theorem paid4240 : IndexedReceipts.checked rows4240 = true := by decide +kernel
theorem route4240 (i : Fin 1) : (rows4240.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4240 ⟨i.val,i.isLt⟩

private def rows4242 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,4,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid4242 : IndexedReceipts.checked rows4242 = true := by decide +kernel
theorem route4242 (i : Fin 5) : (rows4242.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4242 ⟨i.val,i.isLt⟩

private def rows4247 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,.pair pack_R6970Height2313ExplicitRows58_decision2⟩]
private theorem paid4247 : IndexedReceipts.checked rows4247 = true := by decide +kernel
theorem route4247 (i : Fin 3) : (rows4247.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4247 ⟨i.val,i.isLt⟩

private def rows4254 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 0 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 1 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 2 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 3 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 4 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 5 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 6 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 7 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 8 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 9 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 10 [],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 11 [AxisChoices.test1774],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 12 [AxisChoices.test1775],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 13 [AxisChoices.test1776],4,.pair pack_R6970Height2313ExplicitRows58_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 14 [AxisChoices.test1777],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 15 [AxisChoices.test1778],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 16 [AxisChoices.test1779],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 17 [AxisChoices.test1780],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 18 [AxisChoices.test1781],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 19 [AxisChoices.test1782],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 20 [AxisChoices.test1783],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 21 [AxisChoices.test1784],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 22 [AxisChoices.test1785],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 23 [AxisChoices.test1786],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩]
private theorem paid4254 : IndexedReceipts.checked rows4254 = true := by decide +kernel
theorem route4254 (i : Fin 24) : (rows4254.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4254 ⟨i.val,i.isLt⟩

private def rows4278 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 24 [AxisChoices.test1787],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 25 [AxisChoices.test1788],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 28 [AxisChoices.test1791],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],4,.pair pack_R6970Height2313ExplicitRows58_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 32 [AxisChoices.test1795],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 35 [AxisChoices.test1798],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 39 [AxisChoices.test1802],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 47 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 56 [AxisChoices.test1819],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 57 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩]
private theorem paid4278 : IndexedReceipts.checked rows4278 = true := by decide +kernel
theorem route4278 (i : Fin 24) : (rows4278.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4278 ⟨i.val,i.isLt⟩

private def rows4312 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 58 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 59 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 60 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows58_pairRow2 61 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩]
private theorem paid4312 : IndexedReceipts.checked rows4312 = true := by decide +kernel
theorem route4312 (i : Fin 4) : (rows4312.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4312 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows58

section Pack_R6970Height2313ExplicitRows59

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows59_pairRow0 (axisLo : ℕ) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
private def pack_R6970Height2313ExplicitRows59_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows59_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows59_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows59_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows59_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows4316 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows59_pairRow0 62,4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow0 63,4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow0 64,4,.excluded none⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,4,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid4316 : IndexedReceipts.checked rows4316 = true := by decide +kernel
theorem route4316 (i : Fin 8) : (rows4316.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4316 ⟨i.val,i.isLt⟩

private def rows4327 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩]
private theorem paid4327 : IndexedReceipts.checked rows4327 = true := by decide +kernel
theorem route4327 (i : Fin 3) : (rows4327.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4327 ⟨i.val,i.isLt⟩

private def rows4334 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,4,.pair ⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 0 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 1 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 2 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 3 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 4 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 5 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 6 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 7 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 8 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 9 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 10 [],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 11 [AxisChoices.test1774],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 12 [AxisChoices.test1775],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 13 [AxisChoices.test1776],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 14 [AxisChoices.test1777],4,.pair pack_R6970Height2313ExplicitRows59_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 15 [AxisChoices.test1778],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 16 [AxisChoices.test1779],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 17 [AxisChoices.test1780],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 18 [AxisChoices.test1781],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩]
private theorem paid4334 : IndexedReceipts.checked rows4334 = true := by decide +kernel
theorem route4334 (i : Fin 24) : (rows4334.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4334 ⟨i.val,i.isLt⟩

private def rows4355 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 19 [AxisChoices.test1782],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow1 20 [AxisChoices.test1783],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 21 [AxisChoices.test1784],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 22 [AxisChoices.test1784,AxisChoices.test1785],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 23 [AxisChoices.test1784,AxisChoices.test1786],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 24 [AxisChoices.test1787],4,.pair pack_R6970Height2313ExplicitRows59_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 25 [AxisChoices.test1788],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 28 [AxisChoices.test1791],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 32 [AxisChoices.test1795],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 35 [AxisChoices.test1798],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 39 [AxisChoices.test1802],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],4,.excluded none⟩]
private theorem paid4355 : IndexedReceipts.checked rows4355 = true := by decide +kernel
theorem route4355 (i : Fin 24) : (rows4355.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4355 ⟨i.val,i.isLt⟩

private def rows4381 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 47 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 56 [AxisChoices.test1819],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows59_pairRow2 57 [AxisChoices.test1819,AxisChoices.test1820],4,.excluded none⟩,
  ⟨⟨50,63,10,2,53,some 56,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test71],[]⟩,4,.pair ⟨(.node 8026411704957730),.intersection,.impossible,285209⟩⟩]
private theorem paid4381 : IndexedReceipts.checked rows4381 = true := by decide +kernel
theorem route4381 (i : Fin 6) : (rows4381.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4381 ⟨i.val,i.isLt⟩

private def rows4335 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,4,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid4335 : IndexedReceipts.checked rows4335 = true := by decide +kernel
theorem route4335 (i : Fin 1) : (rows4335.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4335 ⟨i.val,i.isLt⟩

private def rows4407 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨50,63,10,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,.pair pack_R6970Height2313ExplicitRows59_decision2⟩]
private theorem paid4407 : IndexedReceipts.checked rows4407 = true := by decide +kernel
theorem route4407 (i : Fin 4) : (rows4407.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4407 ⟨i.val,i.isLt⟩

private def rows4417 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,4,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,654,12,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,.pair ⟨.separate,.whole,.impossible,0⟩⟩]
private theorem paid4417 : IndexedReceipts.checked rows4417 = true := by decide +kernel
theorem route4417 (i : Fin 2) : (rows4417.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4417 ⟨i.val,i.isLt⟩

private def rows4418 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,4,.excluded none⟩]
private theorem paid4418 : IndexedReceipts.checked rows4418 = true := by decide +kernel
theorem route4418 (i : Fin 1) : (rows4418.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4418 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows59

section Pack_R6970Height2313ExplicitRows60

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows60_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows60_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows60_pairRow2 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,654,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows60_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows60_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows60_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows60_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows4398 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,4,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,4,.pair pack_R6970Height2313ExplicitRows60_decision2⟩]
private theorem paid4398 : IndexedReceipts.checked rows4398 = true := by decide +kernel
theorem route4398 (i : Fin 2) : (rows4398.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4398 ⟨i.val,i.isLt⟩

private def rows4522 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,4,.pair ⟨(.node 8029965254169422),.intersection,.impossible,290650⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 41 (some 44) [MeasuredChoices.test49,MeasuredChoices.test50],4,.pair ⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46],4,.pair ⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44],4,.pair ⟨(.node 8042152515659111),.intersection,.impossible,298829⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 29 (some 32) [MeasuredChoices.test39],4,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 27 (some 28) [MeasuredChoices.test37],4,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 25 (some 26) [MeasuredChoices.test35,MeasuredChoices.test36],4,.pair ⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 17 (some 20) [],4,.pair pack_R6970Height2313ExplicitRows60_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 13 (some 16) [],4,.pair pack_R6970Height2313ExplicitRows60_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 9 (some 12) [],4,.pair pack_R6970Height2313ExplicitRows60_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow2 4 (some 8) [],4,.pair ⟨.surface,.whole,.surface,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 1 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 2 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 3 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 4 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 5 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 6 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 7 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 8 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 9 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 10 [],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 11 [AxisChoices.test1774],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 12 [AxisChoices.test1775],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 13 [AxisChoices.test1776],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩]
private theorem paid4522 : IndexedReceipts.checked rows4522 = true := by decide +kernel
theorem route4522 (i : Fin 24) : (rows4522.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4522 ⟨i.val,i.isLt⟩

private def rows4433 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 14 [AxisChoices.test1777],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 15 [AxisChoices.test1778],4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 16 [AxisChoices.test1779],4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 17 [AxisChoices.test1780],4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 18 [AxisChoices.test1781],4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow0 19 [AxisChoices.test1782],4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 20 [AxisChoices.test1783],4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 21 [AxisChoices.test1784],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 24 [AxisChoices.test1787],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 25 [AxisChoices.test1788],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 28 [AxisChoices.test1791],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 32 [AxisChoices.test1795],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 35 [AxisChoices.test1798],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 39 [AxisChoices.test1802],4,.excluded none⟩]
private theorem paid4433 : IndexedReceipts.checked rows4433 = true := by decide +kernel
theorem route4433 (i : Fin 24) : (rows4433.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4433 ⟨i.val,i.isLt⟩

private def rows4459 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows60_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨⟨64,654,12,2,50,some 50,0,some 0,257319,[MeasuredChoices.test64],[]⟩,4,.pair pack_R6970Height2313ExplicitRows60_decision1⟩]
private theorem paid4459 : IndexedReceipts.checked rows4459 = true := by decide +kernel
theorem route4459 (i : Fin 9) : (rows4459.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4459 ⟨i.val,i.isLt⟩

private def rows7013 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,36,some 36,20,some 36,298829,[],[AxisChoices.test1783]⟩,4,.pair pack_R6970Height2313ExplicitRows60_decision0⟩]
private theorem paid7013 : IndexedReceipts.checked rows7013 = true := by decide +kernel
theorem route7013 (i : Fin 1) : (rows7013.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7013 ⟨i.val,i.isLt⟩

private def rows4537 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,4,.pair pack_R6970Height2313ExplicitRows60_decision3⟩]
private theorem paid4537 : IndexedReceipts.checked rows4537 = true := by decide +kernel
theorem route4537 (i : Fin 1) : (rows4537.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4537 ⟨i.val,i.isLt⟩

private def rows4547 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩]
private theorem paid4547 : IndexedReceipts.checked rows4547 = true := by decide +kernel
theorem route4547 (i : Fin 5) : (rows4547.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4547 ⟨i.val,i.isLt⟩

private def rows4553 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩]
private theorem paid4553 : IndexedReceipts.checked rows4553 = true := by decide +kernel
theorem route4553 (i : Fin 2) : (rows4553.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4553 ⟨i.val,i.isLt⟩

private def rows4555 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows60_decision2⟩]
private theorem paid4555 : IndexedReceipts.checked rows4555 = true := by decide +kernel
theorem route4555 (i : Fin 5) : (rows4555.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4555 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows60

section Pack_R6970Height2313ExplicitRows61

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows61_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,50,some 50,axisLo,some axisLo,257319,[MeasuredChoices.test64],rect⟩
private def pack_R6970Height2313ExplicitRows61_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows61_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows61_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows61_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows61_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows4472 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 1 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 2 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 3 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 4 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 5 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 6 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 7 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 8 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 9 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 10 [],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 11 [AxisChoices.test1774],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 12 [AxisChoices.test1775],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 13 [AxisChoices.test1776],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 14 [AxisChoices.test1777],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 15 [AxisChoices.test1778],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 16 [AxisChoices.test1779],4,.pair pack_R6970Height2313ExplicitRows61_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 17 [AxisChoices.test1780],4,.pair pack_R6970Height2313ExplicitRows61_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 18 [AxisChoices.test1781],4,.pair pack_R6970Height2313ExplicitRows61_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 19 [AxisChoices.test1782],4,.pair pack_R6970Height2313ExplicitRows61_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 20 [AxisChoices.test1783],4,.pair pack_R6970Height2313ExplicitRows61_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 21 [AxisChoices.test1784],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 22 [AxisChoices.test1784,AxisChoices.test1785],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 23 [AxisChoices.test1784,AxisChoices.test1786],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 24 [AxisChoices.test1787],4,.excluded none⟩]
private theorem paid4472 : IndexedReceipts.checked rows4472 = true := by decide +kernel
theorem route4472 (i : Fin 24) : (rows4472.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4472 ⟨i.val,i.isLt⟩

private def rows4496 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 25 [AxisChoices.test1788],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 26 [AxisChoices.test1788,AxisChoices.test1789],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 28 [AxisChoices.test1791],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 32 [AxisChoices.test1795],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 35 [AxisChoices.test1798],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 39 [AxisChoices.test1802],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],4,.excluded none⟩]
private theorem paid4496 : IndexedReceipts.checked rows4496 = true := by decide +kernel
theorem route4496 (i : Fin 21) : (rows4496.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4496 ⟨i.val,i.isLt⟩

private def rows4560 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨28,32,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩]
private theorem paid4560 : IndexedReceipts.checked rows4560 = true := by decide +kernel
theorem route4560 (i : Fin 3) : (rows4560.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4560 ⟨i.val,i.isLt⟩

private def rows4564 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩]
private theorem paid4564 : IndexedReceipts.checked rows4564 = true := by decide +kernel
theorem route4564 (i : Fin 5) : (rows4564.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4564 ⟨i.val,i.isLt⟩

private def rows4569 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩]
private theorem paid4569 : IndexedReceipts.checked rows4569 = true := by decide +kernel
theorem route4569 (i : Fin 3) : (rows4569.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4569 ⟨i.val,i.isLt⟩

private def rows4573 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 0 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 1 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 2 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 3 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 4 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 5 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 6 [],5,.pair pack_R6970Height2313ExplicitRows61_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 56 [AxisChoices.test1819],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 57 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 58 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 59 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 60 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 61 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 62 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 63 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows61_pairRow1 64 [AxisChoices.test1819,AxisChoices.test1820],5,.excluded none⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩]
private theorem paid4573 : IndexedReceipts.checked rows4573 = true := by decide +kernel
theorem route4573 (i : Fin 22) : (rows4573.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4573 ⟨i.val,i.isLt⟩

private def rows4643 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,.pair pack_R6970Height2313ExplicitRows61_decision3⟩]
private theorem paid4643 : IndexedReceipts.checked rows4643 = true := by decide +kernel
theorem route4643 (i : Fin 5) : (rows4643.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4643 ⟨i.val,i.isLt⟩

private def rows4649 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,57,some 60,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,5,.pair ⟨(.node 12044597464245294),.intersection,.impossible,290657⟩⟩]
private theorem paid4649 : IndexedReceipts.checked rows4649 = true := by decide +kernel
theorem route4649 (i : Fin 1) : (rows4649.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4649 ⟨i.val,i.isLt⟩

private def rows7051 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,60,some 60,0,none,290657,[MeasuredChoices.test83],[]⟩,5,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid7051 : IndexedReceipts.checked rows7051 = true := by decide +kernel
theorem route7051 (i : Fin 1) : (rows7051.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7051 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows61

section Pack_R6970Height2313ExplicitRows62

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows62_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows62_pairRow1 (axisLo : ℕ) : PairCell.Row := ⟨64,654,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩
private def pack_R6970Height2313ExplicitRows62_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,48,some 48,axisLo,some axisLo,257319,[MeasuredChoices.test61],rect⟩
private def pack_R6970Height2313ExplicitRows62_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows62_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows62_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows62_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows62_decision4 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows4651 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,.pair ⟨(.node 8026411704957730),.intersection,.impossible,285209⟩⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩]
private theorem paid4651 : IndexedReceipts.checked rows4651 = true := by decide +kernel
theorem route4651 (i : Fin 8) : (rows4651.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4651 ⟨i.val,i.isLt⟩

private def rows4580 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 7 [],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 8 [],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 9 [],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 10 [],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 11 [AxisChoices.test1774],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 12 [AxisChoices.test1775],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 13 [AxisChoices.test1776],5,.pair pack_R6970Height2313ExplicitRows62_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 14 [AxisChoices.test1777],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 15 [AxisChoices.test1778],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 16 [AxisChoices.test1779],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 17 [AxisChoices.test1780],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 18 [AxisChoices.test1781],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 19 [AxisChoices.test1782],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 20 [AxisChoices.test1783],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 21 [AxisChoices.test1784],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 22 [AxisChoices.test1785],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 23 [AxisChoices.test1786],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 24 [AxisChoices.test1787],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 25 [AxisChoices.test1788],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 26 [AxisChoices.test1788,AxisChoices.test1789],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 28 [AxisChoices.test1791],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],5,.pair pack_R6970Height2313ExplicitRows62_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 32 [AxisChoices.test1795],5,.excluded none⟩]
private theorem paid4580 : IndexedReceipts.checked rows4580 = true := by decide +kernel
theorem route4580 (i : Fin 24) : (rows4580.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4580 ⟨i.val,i.isLt⟩

private def rows4606 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 35 [AxisChoices.test1798],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 39 [AxisChoices.test1802],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩]
private theorem paid4606 : IndexedReceipts.checked rows4606 = true := by decide +kernel
theorem route4606 (i : Fin 14) : (rows4606.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4606 ⟨i.val,i.isLt⟩

private def rows4662 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision3⟩]
private theorem paid4662 : IndexedReceipts.checked rows4662 = true := by decide +kernel
theorem route4662 (i : Fin 3) : (rows4662.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4662 ⟨i.val,i.isLt⟩

private def rows4669 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,5,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 0,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 1,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 2,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 3,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 4,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 5,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 6,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 7,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow1 8,5,.pair pack_R6970Height2313ExplicitRows62_decision2⟩,
  ⟨⟨64,654,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,5,.pair ⟨(.node 25309255810936571),.intersection,.impossible,305352⟩⟩,
  ⟨⟨64,654,12,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,5,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,654,12,2,25,some 26,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,5,.pair ⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨64,654,12,2,24,some 24,0,none,257319,[MeasuredChoices.test32,MeasuredChoices.test34],[]⟩,5,.pair ⟨(.node 8075014212150647),.intersection,.impossible,304158⟩⟩,
  ⟨⟨64,654,12,2,23,some 23,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,5,.pair ⟨(.node 12169361715993978),.intersection,.impossible,305811⟩⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision4⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision4⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 39 [AxisChoices.test1802],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩]
private theorem paid4669 : IndexedReceipts.checked rows4669 = true := by decide +kernel
theorem route4669 (i : Fin 24) : (rows4669.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4669 ⟨i.val,i.isLt⟩

private def rows4866 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows62_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩]
private theorem paid4866 : IndexedReceipts.checked rows4866 = true := by decide +kernel
theorem route4866 (i : Fin 5) : (rows4866.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4866 ⟨i.val,i.isLt⟩

private def rows4670 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,5,.excluded none⟩]
private theorem paid4670 : IndexedReceipts.checked rows4670 = true := by decide +kernel
theorem route4670 (i : Fin 1) : (rows4670.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4670 ⟨i.val,i.isLt⟩

private def rows4887 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,5,.pair pack_R6970Height2313ExplicitRows62_decision4⟩]
private theorem paid4887 : IndexedReceipts.checked rows4887 = true := by decide +kernel
theorem route4887 (i : Fin 1) : (rows4887.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4887 ⟨i.val,i.isLt⟩

private def rows4898 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,.pair pack_R6970Height2313ExplicitRows62_decision3⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows62_decision3⟩]
private theorem paid4898 : IndexedReceipts.checked rows4898 = true := by decide +kernel
theorem route4898 (i : Fin 2) : (rows4898.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4898 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows62

section Pack_R6970Height2313ExplicitRows63

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows63_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows63_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows63_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,50,some 50,axisLo,some axisLo,257319,[MeasuredChoices.test64],rect⟩
private def pack_R6970Height2313ExplicitRows63_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows63_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows4871 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,48,some 48,47,some 47,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1809]⟩,5,.excluded none⟩,
  ⟨⟨64,654,12,2,47,some 47,0,none,257319,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩,5,.pair ⟨(.node 16092526819772228),.intersection,.impossible,300246⟩⟩,
  ⟨⟨64,654,12,2,43,some 44,0,none,257319,[MeasuredChoices.test51,MeasuredChoices.test52],[]⟩,5,.pair ⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,654,12,2,41,some 42,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,5,.pair ⟨(.node 8035141832419182),.intersection,.impossible,295365⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 9 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 10 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 11 [AxisChoices.test1774],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 12 [AxisChoices.test1775],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 13 [AxisChoices.test1776],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 14 [AxisChoices.test1777],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 15 [AxisChoices.test1778],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 16 [AxisChoices.test1779],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 17 [AxisChoices.test1780],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 18 [AxisChoices.test1781],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow0 19 [AxisChoices.test1782],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 20 [AxisChoices.test1783],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 21 [AxisChoices.test1784],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 24 [AxisChoices.test1787],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 25 [AxisChoices.test1788],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 28 [AxisChoices.test1791],5,.excluded none⟩]
private theorem paid4871 : IndexedReceipts.checked rows4871 = true := by decide +kernel
theorem route4871 (i : Fin 24) : (rows4871.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4871 ⟨i.val,i.isLt⟩

private def rows4700 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 32 [AxisChoices.test1795],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 35 [AxisChoices.test1798],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 39 [AxisChoices.test1802],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 0 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 1 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 2 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 3 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 4 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 5 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 6 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩]
private theorem paid4700 : IndexedReceipts.checked rows4700 = true := by decide +kernel
theorem route4700 (i : Fin 24) : (rows4700.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4700 ⟨i.val,i.isLt⟩

private def rows4730 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 7 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 8 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 9 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 10 [],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 11 [AxisChoices.test1774],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 12 [AxisChoices.test1775],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 13 [AxisChoices.test1776],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 14 [AxisChoices.test1777],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 15 [AxisChoices.test1778],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 16 [AxisChoices.test1779],5,.pair pack_R6970Height2313ExplicitRows63_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 17 [AxisChoices.test1780],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 18 [AxisChoices.test1781],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 19 [AxisChoices.test1782],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 20 [AxisChoices.test1783],5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 21 [AxisChoices.test1784],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 22 [AxisChoices.test1784,AxisChoices.test1785],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 23 [AxisChoices.test1784,AxisChoices.test1786],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 24 [AxisChoices.test1787],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 25 [AxisChoices.test1788],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 28 [AxisChoices.test1791],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 32 [AxisChoices.test1795],5,.excluded none⟩]
private theorem paid4730 : IndexedReceipts.checked rows4730 = true := by decide +kernel
theorem route4730 (i : Fin 24) : (rows4730.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4730 ⟨i.val,i.isLt⟩

private def rows4756 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 35 [AxisChoices.test1798],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 39 [AxisChoices.test1802],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows63_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],5,.excluded none⟩]
private theorem paid4756 : IndexedReceipts.checked rows4756 = true := by decide +kernel
theorem route4756 (i : Fin 13) : (rows4756.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4756 ⟨i.val,i.isLt⟩

private def rows7022 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,47,some 47,28,some 47,300246,[],[AxisChoices.test1791]⟩,5,.pair pack_R6970Height2313ExplicitRows63_decision0⟩]
private theorem paid7022 : IndexedReceipts.checked rows7022 = true := by decide +kernel
theorem route7022 (i : Fin 1) : (rows7022.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7022 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows63

section Pack_R6970Height2313ExplicitRows64

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows64_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,49,some 49,axisLo,some axisLo,257319,[MeasuredChoices.test58,MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows64_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,49,some 49,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows64_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,48,some 48,axisLo,some axisLo,257319,[MeasuredChoices.test58,MeasuredChoices.test61],rect⟩
private def pack_R6970Height2313ExplicitRows64_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,654,12,2,48,some 48,axisLo,some axisLo,257319,[MeasuredChoices.test61],rect⟩
private def pack_R6970Height2313ExplicitRows64_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows64_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows64_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows4769 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,50,some 50,46,some 46,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩,5,.excluded none⟩,
  ⟨⟨64,654,12,2,50,some 50,47,some 47,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩,5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 0 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 1 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 2 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 3 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 4 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 5 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 6 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 7 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 8 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 9 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 10 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 11 [AxisChoices.test1774],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 12 [AxisChoices.test1775],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 13 [AxisChoices.test1776],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 14 [AxisChoices.test1777],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 15 [AxisChoices.test1778],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 16 [AxisChoices.test1779],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 17 [AxisChoices.test1780],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow0 18 [AxisChoices.test1781],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 19 [AxisChoices.test1782],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 20 [AxisChoices.test1783],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 21 [AxisChoices.test1784],5,.excluded none⟩]
private theorem paid4769 : IndexedReceipts.checked rows4769 = true := by decide +kernel
theorem route4769 (i : Fin 24) : (rows4769.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4769 ⟨i.val,i.isLt⟩

private def rows4796 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 24 [AxisChoices.test1787],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 25 [AxisChoices.test1788],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 28 [AxisChoices.test1791],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 32 [AxisChoices.test1795],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 35 [AxisChoices.test1798],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 39 [AxisChoices.test1802],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],5,.excluded none⟩]
private theorem paid4796 : IndexedReceipts.checked rows4796 = true := by decide +kernel
theorem route4796 (i : Fin 24) : (rows4796.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4796 ⟨i.val,i.isLt⟩

private def rows4824 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 0 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 1 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 2 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 3 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 4 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 5 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 6 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 7 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 8 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 9 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 10 [],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 11 [AxisChoices.test1774],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 12 [AxisChoices.test1775],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 13 [AxisChoices.test1776],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 14 [AxisChoices.test1777],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 15 [AxisChoices.test1778],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 16 [AxisChoices.test1779],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 17 [AxisChoices.test1780],5,.pair pack_R6970Height2313ExplicitRows64_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow2 18 [AxisChoices.test1781],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 19 [AxisChoices.test1782],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 20 [AxisChoices.test1783],5,.pair pack_R6970Height2313ExplicitRows64_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 21 [AxisChoices.test1784],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],5,.excluded none⟩]
private theorem paid4824 : IndexedReceipts.checked rows4824 = true := by decide +kernel
theorem route4824 (i : Fin 24) : (rows4824.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4824 ⟨i.val,i.isLt⟩

private def rows4848 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 24 [AxisChoices.test1787],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 25 [AxisChoices.test1788],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 27 [AxisChoices.test1788,AxisChoices.test1790],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 28 [AxisChoices.test1791],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 29 [AxisChoices.test1791,AxisChoices.test1792],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 32 [AxisChoices.test1795],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 33 [AxisChoices.test1795,AxisChoices.test1796],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 34 [AxisChoices.test1795,AxisChoices.test1797],5,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows64_pairRow3 35 [AxisChoices.test1798],5,.excluded none⟩]
private theorem paid4848 : IndexedReceipts.checked rows4848 = true := by decide +kernel
theorem route4848 (i : Fin 10) : (rows4848.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4848 ⟨i.val,i.isLt⟩

private def rows4900 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩]
private theorem paid4900 : IndexedReceipts.checked rows4900 = true := by decide +kernel
theorem route4900 (i : Fin 3) : (rows4900.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4900 ⟨i.val,i.isLt⟩

private def rows4904 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩]
private theorem paid4904 : IndexedReceipts.checked rows4904 = true := by decide +kernel
theorem route4904 (i : Fin 1) : (rows4904.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4904 ⟨i.val,i.isLt⟩

private def rows4905 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows64_decision2⟩]
private theorem paid4905 : IndexedReceipts.checked rows4905 = true := by decide +kernel
theorem route4905 (i : Fin 4) : (rows4905.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4905 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows64

section Pack_R6970Height2313ExplicitRows65

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows65_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,706,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test64,MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows65_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,706,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows65_pairRow2 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,706,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows65_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows65_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows65_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows4909 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4909 : IndexedReceipts.checked rows4909 = true := by decide +kernel
theorem route4909 (i : Fin 1) : (rows4909.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4909 ⟨i.val,i.isLt⟩

private def rows4910 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨28,32,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4910 : IndexedReceipts.checked rows4910 = true := by decide +kernel
theorem route4910 (i : Fin 3) : (rows4910.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4910 ⟨i.val,i.isLt⟩

private def rows4914 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4914 : IndexedReceipts.checked rows4914 = true := by decide +kernel
theorem route4914 (i : Fin 5) : (rows4914.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4914 ⟨i.val,i.isLt⟩

private def rows4919 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4919 : IndexedReceipts.checked rows4919 = true := by decide +kernel
theorem route4919 (i : Fin 3) : (rows4919.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4919 ⟨i.val,i.isLt⟩

private def rows4923 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,6,.pair ⟨(.node 16064838841308028),.intersection,.impossible,293263⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4923 : IndexedReceipts.checked rows4923 = true := by decide +kernel
theorem route4923 (i : Fin 6) : (rows4923.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4923 ⟨i.val,i.isLt⟩

private def rows4930 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4930 : IndexedReceipts.checked rows4930 = true := by decide +kernel
theorem route4930 (i : Fin 5) : (rows4930.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4930 ⟨i.val,i.isLt⟩

private def rows7070 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 52,0,none,257319,[MeasuredChoices.test63],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,53,some 56,0,none,257319,[MeasuredChoices.test69],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid7070 : IndexedReceipts.checked rows7070 = true := by decide +kernel
theorem route7070 (i : Fin 7) : (rows7070.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7070 ⟨i.val,i.isLt⟩

private def rows4944 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid4944 : IndexedReceipts.checked rows4944 = true := by decide +kernel
theorem route4944 (i : Fin 5) : (rows4944.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4944 ⟨i.val,i.isLt⟩

private def rows4951 : List IndexedReceipts.Receipt := [
  ⟨⟨64,706,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,6,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 0 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 1 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 2 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 3 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 4 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 5 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 6 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 41 (some 44) [MeasuredChoices.test49,MeasuredChoices.test50],6,.pair ⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46],6,.pair ⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44],6,.pair ⟨(.node 8042152515659111),.intersection,.impossible,298829⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 29 (some 32) [MeasuredChoices.test39],6,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 27 (some 28) [MeasuredChoices.test37],6,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 25 (some 26) [MeasuredChoices.test35,MeasuredChoices.test36],6,.pair ⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 17 (some 20) [],6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 13 (some 16) [],6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow2 9 (some 12) [],6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 7 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 8 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 9 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 10 [],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 11 [AxisChoices.test1774],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 12 [AxisChoices.test1775],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 13 [AxisChoices.test1776],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩]
private theorem paid4951 : IndexedReceipts.checked rows4951 = true := by decide +kernel
theorem route4951 (i : Fin 24) : (rows4951.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4951 ⟨i.val,i.isLt⟩

private def rows4967 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 14 [AxisChoices.test1777],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 15 [AxisChoices.test1778],6,.pair pack_R6970Height2313ExplicitRows65_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 16 [AxisChoices.test1779],6,.pair pack_R6970Height2313ExplicitRows65_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 17 [AxisChoices.test1780],6,.pair pack_R6970Height2313ExplicitRows65_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 18 [AxisChoices.test1781],6,.pair pack_R6970Height2313ExplicitRows65_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow0 19 [AxisChoices.test1782],6,.pair pack_R6970Height2313ExplicitRows65_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 20 [AxisChoices.test1783],6,.pair pack_R6970Height2313ExplicitRows65_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 21 [AxisChoices.test1784],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 24 [AxisChoices.test1787],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 25 [AxisChoices.test1788],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 28 [AxisChoices.test1791],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 32 [AxisChoices.test1795],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows65_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],6,.excluded none⟩]
private theorem paid4967 : IndexedReceipts.checked rows4967 = true := by decide +kernel
theorem route4967 (i : Fin 19) : (rows4967.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4967 ⟨i.val,i.isLt⟩

private def rows4952 : List IndexedReceipts.Receipt := [
  ⟨⟨64,706,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,6,.excluded none⟩]
private theorem paid4952 : IndexedReceipts.checked rows4952 = true := by decide +kernel
theorem route4952 (i : Fin 1) : (rows4952.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4952 ⟨i.val,i.isLt⟩

private def rows5070 : List IndexedReceipts.Receipt := [
  ⟨⟨64,706,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,6,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid5070 : IndexedReceipts.checked rows5070 = true := by decide +kernel
theorem route5070 (i : Fin 1) : (rows5070.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5070 ⟨i.val,i.isLt⟩

private def rows5079 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,.pair pack_R6970Height2313ExplicitRows65_decision2⟩]
private theorem paid5079 : IndexedReceipts.checked rows5079 = true := by decide +kernel
theorem route5079 (i : Fin 1) : (rows5079.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5079 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows65

section Pack_R6970Height2313ExplicitRows66

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows66_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,706,12,2,51,some 51,axisLo,some axisLo,257319,[MeasuredChoices.test66],rect⟩
private def pack_R6970Height2313ExplicitRows66_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨64,706,12,2,50,some 50,axisLo,some axisLo,257319,[MeasuredChoices.test64],rect⟩
private def pack_R6970Height2313ExplicitRows66_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows66_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows66_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows4988 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 35 [AxisChoices.test1798],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 39 [AxisChoices.test1802],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 0 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 1 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 2 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 3 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 4 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 5 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 6 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 7 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 8 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 9 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 10 [],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩]
private theorem paid4988 : IndexedReceipts.checked rows4988 = true := by decide +kernel
theorem route4988 (i : Fin 24) : (rows4988.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid4988 ⟨i.val,i.isLt⟩

private def rows5016 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 11 [AxisChoices.test1774],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 12 [AxisChoices.test1775],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 13 [AxisChoices.test1776],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 14 [AxisChoices.test1777],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 15 [AxisChoices.test1778],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 16 [AxisChoices.test1779],6,.pair pack_R6970Height2313ExplicitRows66_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 17 [AxisChoices.test1780],6,.pair pack_R6970Height2313ExplicitRows66_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 18 [AxisChoices.test1781],6,.pair pack_R6970Height2313ExplicitRows66_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 19 [AxisChoices.test1782],6,.pair pack_R6970Height2313ExplicitRows66_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 20 [AxisChoices.test1783],6,.pair pack_R6970Height2313ExplicitRows66_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 21 [AxisChoices.test1784],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 24 [AxisChoices.test1787],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 25 [AxisChoices.test1788],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 28 [AxisChoices.test1791],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 32 [AxisChoices.test1795],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 35 [AxisChoices.test1798],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],6,.excluded none⟩]
private theorem paid5016 : IndexedReceipts.checked rows5016 = true := by decide +kernel
theorem route5016 (i : Fin 24) : (rows5016.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5016 ⟨i.val,i.isLt⟩

private def rows5042 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 39 [AxisChoices.test1802],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],6,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows66_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],6,.excluded none⟩,
  ⟨⟨64,706,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,6,.pair ⟨(.node 8029965254169422),.intersection,.impossible,290650⟩⟩]
private theorem paid5042 : IndexedReceipts.checked rows5042 = true := by decide +kernel
theorem route5042 (i : Fin 12) : (rows5042.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5042 ⟨i.val,i.isLt⟩

private def rows5080 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩]
private theorem paid5080 : IndexedReceipts.checked rows5080 = true := by decide +kernel
theorem route5080 (i : Fin 4) : (rows5080.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5080 ⟨i.val,i.isLt⟩

private def rows5084 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩]
private theorem paid5084 : IndexedReceipts.checked rows5084 = true := by decide +kernel
theorem route5084 (i : Fin 5) : (rows5084.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5084 ⟨i.val,i.isLt⟩

private def rows5090 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩]
private theorem paid5090 : IndexedReceipts.checked rows5090 = true := by decide +kernel
theorem route5090 (i : Fin 5) : (rows5090.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5090 ⟨i.val,i.isLt⟩

private def rows5096 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩]
private theorem paid5096 : IndexedReceipts.checked rows5096 = true := by decide +kernel
theorem route5096 (i : Fin 6) : (rows5096.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5096 ⟨i.val,i.isLt⟩

private def rows5103 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,57,some 64,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,7,.pair ⟨.marked,.intersection,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows66_decision2⟩]
private theorem paid5103 : IndexedReceipts.checked rows5103 = true := by decide +kernel
theorem route5103 (i : Fin 5) : (rows5103.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5103 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows66

section Pack_R6970Height2313ExplicitRows67

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows67_pairRow0 : PairCell.Row := ⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow1 : PairCell.Row := ⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow2 : PairCell.Row := ⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow3 : PairCell.Row := ⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow4 : PairCell.Row := ⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow5 : PairCell.Row := ⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow6 : PairCell.Row := ⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow7 : PairCell.Row := ⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩
private def pack_R6970Height2313ExplicitRows67_pairRow8 : PairCell.Row := ⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩
private def pairRow9 : PairCell.Row := ⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩
private def pairRow10 (seedHi : Option ℕ) : PairCell.Row := ⟨50,63,10,2,49,seedHi,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩
private def pairRow11 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,654,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pairRow12 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,650,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows67_decision0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows67_decision1 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩

private def rows5108 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows67_pairRow0,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow1,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid5108 : IndexedReceipts.checked rows5108 = true := by decide +kernel
theorem route5108 (i : Fin 2) : (rows5108.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5108 ⟨i.val,i.isLt⟩

private def rows5110 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨50,63,10,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨50,63,10,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid5110 : IndexedReceipts.checked rows5110 = true := by decide +kernel
theorem route5110 (i : Fin 3) : (rows5110.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5110 ⟨i.val,i.isLt⟩

private def rows5114 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,49,some 52,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,7,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,7,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,7,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,722,12,2,17,some 20,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨64,722,12,2,13,some 16,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨64,722,12,2,9,some 12,0,none,257319,[],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid5114 : IndexedReceipts.checked rows5114 = true := by decide +kernel
theorem route5114 (i : Fin 6) : (rows5114.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5114 ⟨i.val,i.isLt⟩

private def rows5121 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,7,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid5121 : IndexedReceipts.checked rows5121 = true := by decide +kernel
theorem route5121 (i : Fin 1) : (rows5121.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5121 ⟨i.val,i.isLt⟩

private def rows5128 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow2,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow3,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid5128 : IndexedReceipts.checked rows5128 = true := by decide +kernel
theorem route5128 (i : Fin 5) : (rows5128.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5128 ⟨i.val,i.isLt⟩

private def rows5133 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid5133 : IndexedReceipts.checked rows5133 = true := by decide +kernel
theorem route5133 (i : Fin 5) : (rows5133.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5133 ⟨i.val,i.isLt⟩

private def rows5138 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow4,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow5,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow6,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid5138 : IndexedReceipts.checked rows5138 = true := by decide +kernel
theorem route5138 (i : Fin 6) : (rows5138.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5138 ⟨i.val,i.isLt⟩

private def rows5144 : List IndexedReceipts.Receipt := [
  ⟨pairRow10 (some 56),8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow7,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow8,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow9,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow0,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow1,8,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid5144 : IndexedReceipts.checked rows5144 = true := by decide +kernel
theorem route5144 (i : Fin 6) : (rows5144.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5144 ⟨i.val,i.isLt⟩

private def rows5150 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨50,63,10,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid5150 : IndexedReceipts.checked rows5150 = true := by decide +kernel
theorem route5150 (i : Fin 2) : (rows5150.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5150 ⟨i.val,i.isLt⟩

private def rows5153 : List IndexedReceipts.Receipt := [
  ⟨pairRow11 49 (some 52) [MeasuredChoices.test58,MeasuredChoices.test62],8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 41 (some 48) [MeasuredChoices.test49,MeasuredChoices.test50],8,.pair ⟨(.node 8030575396047635),.intersection,.impossible,291368⟩⟩,
  ⟨pairRow11 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46],8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44],8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 29 (some 32) [MeasuredChoices.test39],8,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],8,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩]
private theorem paid5153 : IndexedReceipts.checked rows5153 = true := by decide +kernel
theorem route5153 (i : Fin 6) : (rows5153.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5153 ⟨i.val,i.isLt⟩

private def rows980 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows67_pairRow4,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow5,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow6,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid980 : IndexedReceipts.checked rows980 = true := by decide +kernel
theorem route980 (i : Fin 4) : (rows980.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid980 ⟨i.val,i.isLt⟩

private def rows984 : List IndexedReceipts.Receipt := [
  ⟨pairRow10 (some 64),9,.pair ⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow7,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow8,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow9,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow0,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow1,9,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid984 : IndexedReceipts.checked rows984 = true := by decide +kernel
theorem route984 (i : Fin 6) : (rows984.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid984 ⟨i.val,i.isLt⟩

private def rows985 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid985 : IndexedReceipts.checked rows985 = true := by decide +kernel
theorem route985 (i : Fin 1) : (rows985.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid985 ⟨i.val,i.isLt⟩

private def rows991 : List IndexedReceipts.Receipt := [
  ⟨pairRow12 49 (some 56) [MeasuredChoices.test58,MeasuredChoices.test62],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 41 (some 48) [MeasuredChoices.test49,MeasuredChoices.test50],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 33 (some 40) [MeasuredChoices.test43,MeasuredChoices.test44],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 29 (some 32) [MeasuredChoices.test39],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 21 (some 24) [MeasuredChoices.test26],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 17 (some 20) [],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 13 (some 16) [],9,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow12 9 (some 12) [],9,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid991 : IndexedReceipts.checked rows991 = true := by decide +kernel
theorem route991 (i : Fin 9) : (rows991.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid991 ⟨i.val,i.isLt⟩

private def rows1000 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow2,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow3,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid1000 : IndexedReceipts.checked rows1000 = true := by decide +kernel
theorem route1000 (i : Fin 4) : (rows1000.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1000 ⟨i.val,i.isLt⟩

private def rows1004 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid1004 : IndexedReceipts.checked rows1004 = true := by decide +kernel
theorem route1004 (i : Fin 4) : (rows1004.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1004 ⟨i.val,i.isLt⟩

private def rows1008 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow4,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow5,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow6,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid1008 : IndexedReceipts.checked rows1008 = true := by decide +kernel
theorem route1008 (i : Fin 4) : (rows1008.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1008 ⟨i.val,i.isLt⟩

private def rows1012 : List IndexedReceipts.Receipt := [
  ⟨pairRow10 (some 64),10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow7,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow8,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow9,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow0,10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid1012 : IndexedReceipts.checked rows1012 = true := by decide +kernel
theorem route1012 (i : Fin 5) : (rows1012.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1012 ⟨i.val,i.isLt⟩

private def rows1017 : List IndexedReceipts.Receipt := [
  ⟨pairRow11 49 (some 56) [MeasuredChoices.test58,MeasuredChoices.test62],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 41 (some 48) [MeasuredChoices.test49,MeasuredChoices.test50],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 33 (some 40) [MeasuredChoices.test43,MeasuredChoices.test44],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 29 (some 32) [MeasuredChoices.test39],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 21 (some 24) [MeasuredChoices.test26],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 17 (some 20) [],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 13 (some 16) [],10,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pairRow11 9 (some 12) [],10,.pair pack_R6970Height2313ExplicitRows67_decision1⟩]
private theorem paid1017 : IndexedReceipts.checked rows1017 = true := by decide +kernel
theorem route1017 (i : Fin 9) : (rows1017.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1017 ⟨i.val,i.isLt⟩

private def rows1026 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows67_pairRow2,11,.pair pack_R6970Height2313ExplicitRows67_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows67_pairRow3,11,.pair pack_R6970Height2313ExplicitRows67_decision0⟩]
private theorem paid1026 : IndexedReceipts.checked rows1026 = true := by decide +kernel
theorem route1026 (i : Fin 2) : (rows1026.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1026 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows67

section Pack_R6970Height2313ExplicitRows68

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows68_pairRow0 : PairCell.Row := ⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow1 : PairCell.Row := ⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow2 : PairCell.Row := ⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow3 : PairCell.Row := ⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow4 : PairCell.Row := ⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow5 : PairCell.Row := ⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow6 : PairCell.Row := ⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow7 : PairCell.Row := ⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩
private def pack_R6970Height2313ExplicitRows68_pairRow8 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,628,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows68_decision0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows68_decision1 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩

private def rows1028 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1028 : IndexedReceipts.checked rows1028 = true := by decide +kernel
theorem route1028 (i : Fin 1) : (rows1028.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1028 ⟨i.val,i.isLt⟩

private def rows1029 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow0,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow1,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1029 : IndexedReceipts.checked rows1029 = true := by decide +kernel
theorem route1029 (i : Fin 3) : (rows1029.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1029 ⟨i.val,i.isLt⟩

private def rows1032 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow2,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow3,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1032 : IndexedReceipts.checked rows1032 = true := by decide +kernel
theorem route1032 (i : Fin 3) : (rows1032.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1032 ⟨i.val,i.isLt⟩

private def rows1035 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow4,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow5,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1035 : IndexedReceipts.checked rows1035 = true := by decide +kernel
theorem route1035 (i : Fin 5) : (rows1035.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1035 ⟨i.val,i.isLt⟩

private def rows1040 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,11,.pair ⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨⟨64,654,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,654,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,654,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,654,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1040 : IndexedReceipts.checked rows1040 = true := by decide +kernel
theorem route1040 (i : Fin 7) : (rows1040.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1040 ⟨i.val,i.isLt⟩

private def rows1041 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,11,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1041 : IndexedReceipts.checked rows1041 = true := by decide +kernel
theorem route1041 (i : Fin 1) : (rows1041.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1041 ⟨i.val,i.isLt⟩

private def rows1048 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow6,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow7,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1048 : IndexedReceipts.checked rows1048 = true := by decide +kernel
theorem route1048 (i : Fin 3) : (rows1048.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1048 ⟨i.val,i.isLt⟩

private def rows1051 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow0,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow1,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1051 : IndexedReceipts.checked rows1051 = true := by decide +kernel
theorem route1051 (i : Fin 3) : (rows1051.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1051 ⟨i.val,i.isLt⟩

private def rows1054 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow2,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow3,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1054 : IndexedReceipts.checked rows1054 = true := by decide +kernel
theorem route1054 (i : Fin 3) : (rows1054.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1054 ⟨i.val,i.isLt⟩

private def rows1057 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow4,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow5,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1057 : IndexedReceipts.checked rows1057 = true := by decide +kernel
theorem route1057 (i : Fin 3) : (rows1057.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1057 ⟨i.val,i.isLt⟩

private def rows1060 : List IndexedReceipts.Receipt := [
  ⟨⟨64,591,12,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,17,some 20,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨⟨64,591,12,2,13,some 16,0,none,257319,[],[]⟩,12,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1060 : IndexedReceipts.checked rows1060 = true := by decide +kernel
theorem route1060 (i : Fin 7) : (rows1060.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1060 ⟨i.val,i.isLt⟩

private def rows1067 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow6,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow7,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1067 : IndexedReceipts.checked rows1067 = true := by decide +kernel
theorem route1067 (i : Fin 2) : (rows1067.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1067 ⟨i.val,i.isLt⟩

private def rows1069 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow0,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow1,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1069 : IndexedReceipts.checked rows1069 = true := by decide +kernel
theorem route1069 (i : Fin 2) : (rows1069.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1069 ⟨i.val,i.isLt⟩

private def rows1071 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow2,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow3,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1071 : IndexedReceipts.checked rows1071 = true := by decide +kernel
theorem route1071 (i : Fin 2) : (rows1071.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1071 ⟨i.val,i.isLt⟩

private def rows1073 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow4,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow5,13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1073 : IndexedReceipts.checked rows1073 = true := by decide +kernel
theorem route1073 (i : Fin 2) : (rows1073.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1073 ⟨i.val,i.isLt⟩

private def rows1075 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 49 (some 64) [MeasuredChoices.test58,MeasuredChoices.test62],13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 29 (some 32) [MeasuredChoices.test39],13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 21 (some 24) [MeasuredChoices.test26],13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 17 (some 20) [],13,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 13 (some 16) [],13,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1075 : IndexedReceipts.checked rows1075 = true := by decide +kernel
theorem route1075 (i : Fin 6) : (rows1075.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1075 ⟨i.val,i.isLt⟩

private def rows1081 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow6,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow7,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1081 : IndexedReceipts.checked rows1081 = true := by decide +kernel
theorem route1081 (i : Fin 2) : (rows1081.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1081 ⟨i.val,i.isLt⟩

private def rows1083 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow0,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow1,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1083 : IndexedReceipts.checked rows1083 = true := by decide +kernel
theorem route1083 (i : Fin 2) : (rows1083.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1083 ⟨i.val,i.isLt⟩

private def rows1085 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow2,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow3,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1085 : IndexedReceipts.checked rows1085 = true := by decide +kernel
theorem route1085 (i : Fin 2) : (rows1085.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1085 ⟨i.val,i.isLt⟩

private def rows1087 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow4,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow5,14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1087 : IndexedReceipts.checked rows1087 = true := by decide +kernel
theorem route1087 (i : Fin 2) : (rows1087.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1087 ⟨i.val,i.isLt⟩

private def rows1089 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 21 (some 24) [MeasuredChoices.test26],14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 17 (some 20) [],14,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow8 13 (some 16) [],14,.pair pack_R6970Height2313ExplicitRows68_decision1⟩]
private theorem paid1089 : IndexedReceipts.checked rows1089 = true := by decide +kernel
theorem route1089 (i : Fin 4) : (rows1089.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1089 ⟨i.val,i.isLt⟩

private def rows1093 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow6,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow7,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1093 : IndexedReceipts.checked rows1093 = true := by decide +kernel
theorem route1093 (i : Fin 2) : (rows1093.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1093 ⟨i.val,i.isLt⟩

private def rows1095 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow0,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow1,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1095 : IndexedReceipts.checked rows1095 = true := by decide +kernel
theorem route1095 (i : Fin 2) : (rows1095.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1095 ⟨i.val,i.isLt⟩

private def rows1097 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow2,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows68_pairRow3,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1097 : IndexedReceipts.checked rows1097 = true := by decide +kernel
theorem route1097 (i : Fin 2) : (rows1097.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1097 ⟨i.val,i.isLt⟩

private def rows1099 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows68_pairRow4,15,.pair pack_R6970Height2313ExplicitRows68_decision0⟩]
private theorem paid1099 : IndexedReceipts.checked rows1099 = true := by decide +kernel
theorem route1099 (i : Fin 1) : (rows1099.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1099 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows68
