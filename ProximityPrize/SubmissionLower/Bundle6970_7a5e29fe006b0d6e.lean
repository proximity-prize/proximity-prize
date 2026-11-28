import ProximityPrize.SubmissionLower.R6970Height2313ReceiptIndex
import ProximityPrize.SubmissionLower.Bundle6970_7a0ead0a3fc2768d
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.R6970Height2313MeasuredTests03

section Pack_R6970Height2313ExplicitRows00

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows00_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨22,22,9,3,15,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows00_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨22,22,9,3,13,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test770],rect⟩
private def pack_R6970Height2313ExplicitRows00_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows00_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows00_decision0 : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows00_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows00_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows0 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩]
private theorem paid0 : IndexedReceipts.checked rows0 = true := by decide +kernel
theorem route0 (i : Fin 1) : (rows0.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid0 ⟨i.val,i.isLt⟩

private def rows1 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨⟨22,22,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨22,22,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨22,22,9,2,17,some 20,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨22,22,9,2,13,some 16,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨22,22,9,2,9,some 12,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨22,22,9,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩]
private theorem paid1 : IndexedReceipts.checked rows1 = true := by decide +kernel
theorem route1 (i : Fin 7) : (rows1.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1 ⟨i.val,i.isLt⟩

private def rows3 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩]
private theorem paid3 : IndexedReceipts.checked rows3 = true := by decide +kernel
theorem route3 (i : Fin 1) : (rows3.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3 ⟨i.val,i.isLt⟩

private def rows9 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,3,513,some 1024,0,none,385979,[MeasuredChoices.test1154,MeasuredChoices.test1155],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨⟨22,22,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨⟨22,22,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨22,22,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 0 [AxisChoices.test1821],0,.pair ⟨.separate,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 1 [AxisChoices.test1822],0,.pair ⟨.separate,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩]
private theorem paid9 : IndexedReceipts.checked rows9 = true := by decide +kernel
theorem route9 (i : Fin 24) : (rows9.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid9 ⟨i.val,i.isLt⟩

private def rows46 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,4,513,some 1024,0,none,514639,[MeasuredChoices.test1378],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩]
private theorem paid46 : IndexedReceipts.checked rows46 = true := by decide +kernel
theorem route46 (i : Fin 1) : (rows46.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid46 ⟨i.val,i.isLt⟩

private def rows48 : List IndexedReceipts.Receipt := [
  ⟨⟨22,22,9,6,1025,some 1536,0,none,771959,[MeasuredChoices.test1669],[]⟩,0,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid48 : IndexedReceipts.checked rows48 = true := by decide +kernel
theorem route48 (i : Fin 1) : (rows48.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid48 ⟨i.val,i.isLt⟩

private def rows49 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩]
private theorem paid49 : IndexedReceipts.checked rows49 = true := by decide +kernel
theorem route49 (i : Fin 1) : (rows49.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid49 ⟨i.val,i.isLt⟩

private def rows50 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨23,24,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩]
private theorem paid50 : IndexedReceipts.checked rows50 = true := by decide +kernel
theorem route50 (i : Fin 8) : (rows50.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid50 ⟨i.val,i.isLt⟩

private def rows53 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩]
private theorem paid53 : IndexedReceipts.checked rows53 = true := by decide +kernel
theorem route53 (i : Fin 1) : (rows53.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid53 ⟨i.val,i.isLt⟩

private def rows59 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,3,513,some 1024,0,none,385979,[MeasuredChoices.test1154,MeasuredChoices.test1155],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨⟨23,24,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision2⟩,
  ⟨⟨23,24,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows00_pairRow3 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows00_decision1⟩]
private theorem paid59 : IndexedReceipts.checked rows59 = true := by decide +kernel
theorem route59 (i : Fin 23) : (rows59.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid59 ⟨i.val,i.isLt⟩

private def rows136 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,4,513,some 1024,0,none,514639,[MeasuredChoices.test1377,MeasuredChoices.test1378],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩]
private theorem paid136 : IndexedReceipts.checked rows136 = true := by decide +kernel
theorem route136 (i : Fin 1) : (rows136.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid136 ⟨i.val,i.isLt⟩

private def rows137 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,5,513,some 1024,0,none,643299,[MeasuredChoices.test1533],[]⟩,0,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid137 : IndexedReceipts.checked rows137 = true := by decide +kernel
theorem route137 (i : Fin 1) : (rows137.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid137 ⟨i.val,i.isLt⟩

private def rows138 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,6,513,some 1024,0,none,771959,[MeasuredChoices.test1667],[]⟩,0,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid138 : IndexedReceipts.checked rows138 = true := by decide +kernel
theorem route138 (i : Fin 1) : (rows138.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid138 ⟨i.val,i.isLt⟩

private def rows139 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,.pair pack_R6970Height2313ExplicitRows00_decision0⟩]
private theorem paid139 : IndexedReceipts.checked rows139 = true := by decide +kernel
theorem route139 (i : Fin 1) : (rows139.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid139 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows00

section Pack_R6970Height2313ExplicitRows01

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows01_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,21,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows01_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows01_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows01_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows01_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows80 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩]
private theorem paid80 : IndexedReceipts.checked rows80 = true := by decide +kernel
theorem route80 (i : Fin 24) : (rows80.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid80 ⟨i.val,i.isLt⟩

private def rows117 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows01_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩]
private theorem paid117 : IndexedReceipts.checked rows117 = true := by decide +kernel
theorem route117 (i : Fin 2) : (rows117.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid117 ⟨i.val,i.isLt⟩

private def rows140 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid140 : IndexedReceipts.checked rows140 = true := by decide +kernel
theorem route140 (i : Fin 1) : (rows140.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid140 ⟨i.val,i.isLt⟩

private def rows141 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩]
private theorem paid141 : IndexedReceipts.checked rows141 = true := by decide +kernel
theorem route141 (i : Fin 8) : (rows141.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid141 ⟨i.val,i.isLt⟩

private def rows144 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows01_decision2⟩]
private theorem paid144 : IndexedReceipts.checked rows144 = true := by decide +kernel
theorem route144 (i : Fin 1) : (rows144.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid144 ⟨i.val,i.isLt⟩

private def rows150 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow4 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩]
private theorem paid150 : IndexedReceipts.checked rows150 = true := by decide +kernel
theorem route150 (i : Fin 24) : (rows150.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid150 ⟨i.val,i.isLt⟩

private def rows210 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow5 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows01_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow6 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow6 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows01_pairRow6 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows01_decision1⟩]
private theorem paid210 : IndexedReceipts.checked rows210 = true := by decide +kernel
theorem route210 (i : Fin 8) : (rows210.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid210 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows01

section Pack_R6970Height2313ExplicitRows02

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows02_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows02_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows02_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows02_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows02_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,21,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows02_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows02_decision0 : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows02_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows02_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows02_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows221 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow0 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩]
private theorem paid221 : IndexedReceipts.checked rows221 = true := by decide +kernel
theorem route221 (i : Fin 24) : (rows221.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid221 ⟨i.val,i.isLt⟩

private def rows261 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow2 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨⟨25,27,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩]
private theorem paid261 : IndexedReceipts.checked rows261 = true := by decide +kernel
theorem route261 (i : Fin 24) : (rows261.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid261 ⟨i.val,i.isLt⟩

private def rows166 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow4 22 [AxisChoices.test1843],0,.pair pack_R6970Height2313ExplicitRows02_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow5 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow5 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows02_pairRow5 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows02_decision2⟩]
private theorem paid166 : IndexedReceipts.checked rows166 = true := by decide +kernel
theorem route166 (i : Fin 11) : (rows166.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid166 ⟨i.val,i.isLt⟩

private def rows290 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision0⟩,
  ⟨⟨28,32,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid290 : IndexedReceipts.checked rows290 = true := by decide +kernel
theorem route290 (i : Fin 2) : (rows290.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid290 ⟨i.val,i.isLt⟩

private def rows292 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision0⟩,
  ⟨⟨28,32,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision0⟩,
  ⟨⟨28,32,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision0⟩,
  ⟨⟨28,32,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩]
private theorem paid292 : IndexedReceipts.checked rows292 = true := by decide +kernel
theorem route292 (i : Fin 7) : (rows292.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid292 ⟨i.val,i.isLt⟩

private def rows298 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows02_decision3⟩]
private theorem paid298 : IndexedReceipts.checked rows298 = true := by decide +kernel
theorem route298 (i : Fin 1) : (rows298.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid298 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows02

section Pack_R6970Height2313ExplicitRows03

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows03_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows03_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows03_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows03_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows03_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows03_decision0 : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows03_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows03_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows03_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows300 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩]
private theorem paid300 : IndexedReceipts.checked rows300 = true := by decide +kernel
theorem route300 (i : Fin 4) : (rows300.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid300 ⟨i.val,i.isLt⟩

private def rows304 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision0⟩,
  ⟨⟨28,32,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision0⟩,
  ⟨⟨28,32,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨⟨28,32,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩]
private theorem paid304 : IndexedReceipts.checked rows304 = true := by decide +kernel
theorem route304 (i : Fin 24) : (rows304.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid304 ⟨i.val,i.isLt⟩

private def rows329 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow0 22 [AxisChoices.test1843],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow2 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩]
private theorem paid329 : IndexedReceipts.checked rows329 = true := by decide +kernel
theorem route329 (i : Fin 24) : (rows329.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid329 ⟨i.val,i.isLt⟩

private def rows366 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow3 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows03_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow4 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow4 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows03_pairRow4 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows03_decision2⟩]
private theorem paid366 : IndexedReceipts.checked rows366 = true := by decide +kernel
theorem route366 (i : Fin 11) : (rows366.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid366 ⟨i.val,i.isLt⟩

private def rows468 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision0⟩,
  ⟨⟨28,32,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨28,32,9,4,13,some 16,0,none,514639,[MeasuredChoices.test1256],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩]
private theorem paid468 : IndexedReceipts.checked rows468 = true := by decide +kernel
theorem route468 (i : Fin 3) : (rows468.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid468 ⟨i.val,i.isLt⟩

private def rows471 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid471 : IndexedReceipts.checked rows471 = true := by decide +kernel
theorem route471 (i : Fin 1) : (rows471.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid471 ⟨i.val,i.isLt⟩

private def rows472 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision0⟩,
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision0⟩,
  ⟨⟨33,40,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨33,40,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩]
private theorem paid472 : IndexedReceipts.checked rows472 = true := by decide +kernel
theorem route472 (i : Fin 7) : (rows472.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid472 ⟨i.val,i.isLt⟩

private def rows478 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows03_decision3⟩]
private theorem paid478 : IndexedReceipts.checked rows478 = true := by decide +kernel
theorem route478 (i : Fin 1) : (rows478.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid478 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows03

section Pack_R6970Height2313ExplicitRows04

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows04_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows04_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows04_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows04_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows04_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows04_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows04_decision0 : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows04_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows04_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows04_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows380 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow0 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow1 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩]
private theorem paid380 : IndexedReceipts.checked rows380 = true := by decide +kernel
theorem route380 (i : Fin 24) : (rows380.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid380 ⟨i.val,i.isLt⟩

private def rows416 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow2 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow3 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩]
private theorem paid416 : IndexedReceipts.checked rows416 = true := by decide +kernel
theorem route416 (i : Fin 24) : (rows416.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid416 ⟨i.val,i.isLt⟩

private def rows457 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow4 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows04_decision1⟩]
private theorem paid457 : IndexedReceipts.checked rows457 = true := by decide +kernel
theorem route457 (i : Fin 2) : (rows457.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid457 ⟨i.val,i.isLt⟩

private def rows480 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩]
private theorem paid480 : IndexedReceipts.checked rows480 = true := by decide +kernel
theorem route480 (i : Fin 4) : (rows480.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid480 ⟨i.val,i.isLt⟩

private def rows484 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1147],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision0⟩,
  ⟨⟨33,40,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision0⟩,
  ⟨⟨33,40,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision0⟩,
  ⟨⟨33,40,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision0⟩,
  ⟨⟨33,40,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨⟨33,40,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,0,.pair pack_R6970Height2313ExplicitRows04_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow5 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow5 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow5 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows04_pairRow5 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows04_decision2⟩]
private theorem paid484 : IndexedReceipts.checked rows484 = true := by decide +kernel
theorem route484 (i : Fin 11) : (rows484.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid484 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows04

section Pack_R6970Height2313ExplicitRows05

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows05_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows05_pairRow1 (axisLo : ℕ) : PairCell.Row := ⟨41,49,9,2,57,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test79],[]⟩
private def pack_R6970Height2313ExplicitRows05_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows05_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows05_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows05_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows05_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows05_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows05_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows05_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows620 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows05_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨⟨33,40,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩,
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow2 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩]
private theorem paid620 : IndexedReceipts.checked rows620 = true := by decide +kernel
theorem route620 (i : Fin 24) : (rows620.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid620 ⟨i.val,i.isLt⟩

private def rows525 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow3 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow4 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩]
private theorem paid525 : IndexedReceipts.checked rows525 = true := by decide +kernel
theorem route525 (i : Fin 24) : (rows525.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid525 ⟨i.val,i.isLt⟩

private def rows559 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow5 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows05_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow6 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow6 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow6 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩]
private theorem paid559 : IndexedReceipts.checked rows559 = true := by decide +kernel
theorem route559 (i : Fin 13) : (rows559.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid559 ⟨i.val,i.isLt⟩

private def rows630 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,4,33,some 40,0,none,514639,[MeasuredChoices.test1298],[]⟩,0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨33,40,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩,
  ⟨⟨33,40,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩,
  ⟨⟨33,40,9,4,13,some 16,0,none,514639,[MeasuredChoices.test1256],[]⟩,0,.pair pack_R6970Height2313ExplicitRows05_decision2⟩]
private theorem paid630 : IndexedReceipts.checked rows630 = true := by decide +kernel
theorem route630 (i : Fin 4) : (rows630.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid630 ⟨i.val,i.isLt⟩

private def rows635 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid635 : IndexedReceipts.checked rows635 = true := by decide +kernel
theorem route635 (i : Fin 1) : (rows635.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid635 ⟨i.val,i.isLt⟩

private def rows636 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,65,some 96,0,none,257319,[MeasuredChoices.test86,MeasuredChoices.test87],[]⟩,0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow1 0,0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow1 1,0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows05_pairRow1 2,0,.pair pack_R6970Height2313ExplicitRows05_decision1⟩]
private theorem paid636 : IndexedReceipts.checked rows636 = true := by decide +kernel
theorem route636 (i : Fin 4) : (rows636.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid636 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows05

section Pack_R6970Height2313ExplicitRows06

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows06_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,57,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,47,some 48,axisLo,some axisLo,385979,[MeasuredChoices.test1141],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows06_pairRow6 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨41,49,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows06_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows06_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows06_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows06_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows581 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩]
private theorem paid581 : IndexedReceipts.checked rows581 = true := by decide +kernel
theorem route581 (i : Fin 24) : (rows581.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid581 ⟨i.val,i.isLt⟩

private def rows700 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 63 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 64 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 49 (some 56) [MeasuredChoices.test62],0,.pair ⟨(.node 8026411704957730),.whole,.impossible,285209⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 41 (some 48) [MeasuredChoices.test50],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 33 (some 40) [MeasuredChoices.test44],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 29 (some 32) [MeasuredChoices.test39],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 25 (some 28) [MeasuredChoices.test36],0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 21 (some 24) [MeasuredChoices.test25],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 17 (some 20) [],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 13 (some 16) [],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 9 (some 12) [],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow6 4 (some 8) [],0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 3 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 4 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 5 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 6 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 7 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 8 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 9 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 10 [],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 11 [AxisChoices.test1774],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 12 [AxisChoices.test1775],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 13 [AxisChoices.test1776],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 14 [AxisChoices.test1777],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩]
private theorem paid700 : IndexedReceipts.checked rows700 = true := by decide +kernel
theorem route700 (i : Fin 24) : (rows700.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid700 ⟨i.val,i.isLt⟩

private def rows652 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 15 [AxisChoices.test1778],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 16 [AxisChoices.test1779],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 17 [AxisChoices.test1780],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 18 [AxisChoices.test1781],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 19 [AxisChoices.test1782],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 20 [AxisChoices.test1783],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 21 [AxisChoices.test1784],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow3 22 [AxisChoices.test1785],0,.pair pack_R6970Height2313ExplicitRows06_decision0⟩]
private theorem paid652 : IndexedReceipts.checked rows652 = true := by decide +kernel
theorem route652 (i : Fin 8) : (rows652.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid652 ⟨i.val,i.isLt⟩

private def rows708 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows06_decision3⟩]
private theorem paid708 : IndexedReceipts.checked rows708 = true := by decide +kernel
theorem route708 (i : Fin 1) : (rows708.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid708 ⟨i.val,i.isLt⟩

private def rows714 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 3 [AxisChoices.test1824],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 4 [AxisChoices.test1825],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow4 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩,0,.three none⟩,
  ⟨⟨41,49,9,3,57,some 64,0,none,385979,[MeasuredChoices.test1144],[]⟩,0,.three none⟩]
private theorem paid714 : IndexedReceipts.checked rows714 = true := by decide +kernel
theorem route714 (i : Fin 8) : (rows714.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid714 ⟨i.val,i.isLt⟩

private def rows5160 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩,8,.pair pack_R6970Height2313ExplicitRows06_decision2⟩]
private theorem paid5160 : IndexedReceipts.checked rows5160 = true := by decide +kernel
theorem route5160 (i : Fin 1) : (rows5160.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5160 ⟨i.val,i.isLt⟩

private def rows5161 : List IndexedReceipts.Receipt := [
  ⟨⟨64,654,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,8,.pair pack_R6970Height2313ExplicitRows06_decision2⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows06_decision2⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,8,.pair pack_R6970Height2313ExplicitRows06_decision2⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,8,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid5161 : IndexedReceipts.checked rows5161 = true := by decide +kernel
theorem route5161 (i : Fin 4) : (rows5161.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5161 ⟨i.val,i.isLt⟩

private def rows5169 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,1,.three none⟩]
private theorem paid5169 : IndexedReceipts.checked rows5169 = true := by decide +kernel
theorem route5169 (i : Fin 1) : (rows5169.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5169 ⟨i.val,i.isLt⟩

private def rows5170 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,1,.three none⟩]
private theorem paid5170 : IndexedReceipts.checked rows5170 = true := by decide +kernel
theorem route5170 (i : Fin 1) : (rows5170.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5170 ⟨i.val,i.isLt⟩

private def rows5171 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,1,.three none⟩]
private theorem paid5171 : IndexedReceipts.checked rows5171 = true := by decide +kernel
theorem route5171 (i : Fin 1) : (rows5171.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5171 ⟨i.val,i.isLt⟩

private def rows5172 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩,1,.three none⟩,
  ⟨⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,1,.three none⟩,
  ⟨⟨41,49,9,3,45,some 48,0,none,385979,[MeasuredChoices.test1139],[]⟩,1,.three none⟩]
private theorem paid5172 : IndexedReceipts.checked rows5172 = true := by decide +kernel
theorem route5172 (i : Fin 3) : (rows5172.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5172 ⟨i.val,i.isLt⟩

private def rows5176 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows06_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows06_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows06_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows06_decision1⟩]
private theorem paid5176 : IndexedReceipts.checked rows5176 = true := by decide +kernel
theorem route5176 (i : Fin 3) : (rows5176.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5176 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows06

section Pack_R6970Height2313ExplicitRows07

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows07_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,57,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows07_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows07_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,45,some 46,axisLo,some axisLo,385979,[MeasuredChoices.test1139],rect⟩
private def pack_R6970Height2313ExplicitRows07_pairRow3 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨41,49,9,3,seedLo,seedHi,0,none,385979,tests,[]⟩
private def pack_R6970Height2313ExplicitRows07_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨50,63,10,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows07_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows07_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows07_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows660 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 23 [AxisChoices.test1786],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 24 [AxisChoices.test1787],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 25 [AxisChoices.test1788],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 26 [AxisChoices.test1788,AxisChoices.test1789],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 27 [AxisChoices.test1788,AxisChoices.test1790],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 28 [AxisChoices.test1791],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 32 [AxisChoices.test1795],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 35 [AxisChoices.test1798],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 39 [AxisChoices.test1802],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 56 [AxisChoices.test1819],0,.excluded none⟩]
private theorem paid660 : IndexedReceipts.checked rows660 = true := by decide +kernel
theorem route660 (i : Fin 24) : (rows660.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid660 ⟨i.val,i.isLt⟩

private def rows694 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 57 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 58 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 59 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 60 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 61 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow0 62 [AxisChoices.test1819,AxisChoices.test1820],0,.excluded none⟩]
private theorem paid694 : IndexedReceipts.checked rows694 = true := by decide +kernel
theorem route694 (i : Fin 6) : (rows694.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid694 ⟨i.val,i.isLt⟩

private def rows881 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows07_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 13 (some 14) [MeasuredChoices.test770],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 9 (some 12) [MeasuredChoices.test724],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 4 (some 8) [MeasuredChoices.test671],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],0,.pair pack_R6970Height2313ExplicitRows07_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 38 [AxisChoices.test1859],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 39 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 40 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 41 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 42 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 43 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 44 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 45 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow2 46 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩]
private theorem paid881 : IndexedReceipts.checked rows881 = true := by decide +kernel
theorem route881 (i : Fin 24) : (rows881.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid881 ⟨i.val,i.isLt⟩

private def rows811 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 41 (some 42) [MeasuredChoices.test1133],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 33 (some 36) [MeasuredChoices.test1029],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 31 (some 32) [MeasuredChoices.test1005],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 29 (some 30) [MeasuredChoices.test977],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 27 (some 28) [MeasuredChoices.test952],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow3 25 (some 26) [MeasuredChoices.test924],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩]
private theorem paid811 : IndexedReceipts.checked rows811 = true := by decide +kernel
theorem route811 (i : Fin 6) : (rows811.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid811 ⟨i.val,i.isLt⟩

private def rows902 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,1,49,some 64,0,none,128659,[MeasuredChoices.test5,MeasuredChoices.test6],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,1,41,some 48,0,none,128659,[MeasuredChoices.test4],[]⟩,0,.pair ⟨.affine,.whole,.impossible,0⟩⟩]
private theorem paid902 : IndexedReceipts.checked rows902 = true := by decide +kernel
theorem route902 (i : Fin 2) : (rows902.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid902 ⟨i.val,i.isLt⟩

private def rows904 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 61 (some 64) [MeasuredChoices.test82,MeasuredChoices.test85],0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 59 (some 60) [MeasuredChoices.test82],0,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,0,.pair ⟨(.node 8025893007439878),.whole,.impossible,283522⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 49 (some 52) [MeasuredChoices.test58,MeasuredChoices.test62],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 41 (some 48) [MeasuredChoices.test50],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 33 (some 40) [MeasuredChoices.test44],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 29 (some 32) [MeasuredChoices.test39],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 25 (some 28) [MeasuredChoices.test36],0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 21 (some 24) [MeasuredChoices.test25],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 17 (some 20) [],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 13 (some 16) [],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows07_pairRow4 9 (some 12) [],0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩]
private theorem paid904 : IndexedReceipts.checked rows904 = true := by decide +kernel
theorem route904 (i : Fin 12) : (rows904.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid904 ⟨i.val,i.isLt⟩

private def rows907 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,0,.pair ⟨.marked,.whole,.impossible,0⟩⟩]
private theorem paid907 : IndexedReceipts.checked rows907 = true := by decide +kernel
theorem route907 (i : Fin 1) : (rows907.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid907 ⟨i.val,i.isLt⟩

private def rows915 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,.pair pack_R6970Height2313ExplicitRows07_decision2⟩]
private theorem paid915 : IndexedReceipts.checked rows915 = true := by decide +kernel
theorem route915 (i : Fin 1) : (rows915.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid915 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows07

section Pack_R6970Height2313ExplicitRows08

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows08_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows08_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows08_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows08_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,47,some 48,axisLo,some axisLo,385979,[MeasuredChoices.test1141],rect⟩
private def pack_R6970Height2313ExplicitRows08_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows08_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows821 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow0 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩]
private theorem paid821 : IndexedReceipts.checked rows821 = true := by decide +kernel
theorem route821 (i : Fin 24) : (rows821.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid821 ⟨i.val,i.isLt⟩

private def rows858 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow1 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow2 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 6 [AxisChoices.test1827],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 7 [AxisChoices.test1828],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 10 [AxisChoices.test1831],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 11 [AxisChoices.test1832],0,.pair pack_R6970Height2313ExplicitRows08_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩]
private theorem paid858 : IndexedReceipts.checked rows858 = true := by decide +kernel
theorem route858 (i : Fin 24) : (rows858.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid858 ⟨i.val,i.isLt⟩

private def rows730 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 22 [AxisChoices.test1843],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 23 [AxisChoices.test1844],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 24 [AxisChoices.test1845],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 25 [AxisChoices.test1845,AxisChoices.test1846],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 26 [AxisChoices.test1847],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 27 [AxisChoices.test1848],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 28 [AxisChoices.test1848,AxisChoices.test1849],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 29 [AxisChoices.test1848,AxisChoices.test1849],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 30 [AxisChoices.test1848,AxisChoices.test1851],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 31 [AxisChoices.test1852],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 32 [AxisChoices.test1853],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 33 [AxisChoices.test1854],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 34 [AxisChoices.test1854,AxisChoices.test1855],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 35 [AxisChoices.test1854,AxisChoices.test1856],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 36 [AxisChoices.test1854,AxisChoices.test1857],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 37 [AxisChoices.test1857,AxisChoices.test1858],0,.pair pack_R6970Height2313ExplicitRows08_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 38 [AxisChoices.test1859],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 39 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 40 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩]
private theorem paid730 : IndexedReceipts.checked rows730 = true := by decide +kernel
theorem route730 (i : Fin 24) : (rows730.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid730 ⟨i.val,i.isLt⟩

private def rows755 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 41 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 42 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 43 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 44 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows08_pairRow3 45 [AxisChoices.test1859,AxisChoices.test1860],0,.excluded none⟩]
private theorem paid755 : IndexedReceipts.checked rows755 = true := by decide +kernel
theorem route755 (i : Fin 5) : (rows755.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid755 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows08

section Pack_R6970Height2313ExplicitRows09

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows09_pairRow0 (axisLo : ℕ) : PairCell.Row := ⟨41,49,9,3,47,some 48,axisLo,some axisLo,385979,[MeasuredChoices.test1141],[AxisChoices.test1859,AxisChoices.test1860]⟩
private def pack_R6970Height2313ExplicitRows09_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,45,some 46,axisLo,some axisLo,385979,[MeasuredChoices.test1139],rect⟩
private def pack_R6970Height2313ExplicitRows09_pairRow2 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨50,63,10,3,seedLo,seedHi,0,none,385979,tests,[]⟩
private def pack_R6970Height2313ExplicitRows09_pairRow3 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,721,12,1,seedLo,seedHi,0,none,128659,tests,[]⟩
private def pack_R6970Height2313ExplicitRows09_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,721,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows09_decision0 : PairPrices.Decision := ⟨.affine,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows09_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows09_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows09_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows09_decision4 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows760 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows09_pairRow0 46,0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow0 47,0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow0 48,0,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 0 [AxisChoices.test1821],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 1 [AxisChoices.test1822],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 2 [AxisChoices.test1823],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 3 [AxisChoices.test1824],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 4 [AxisChoices.test1825],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 5 [AxisChoices.test1826],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 6 [AxisChoices.test1827],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 7 [AxisChoices.test1828],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 8 [AxisChoices.test1829],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 9 [AxisChoices.test1830],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 10 [AxisChoices.test1831],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 11 [AxisChoices.test1832],0,.pair pack_R6970Height2313ExplicitRows09_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 12 [AxisChoices.test1833],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 13 [AxisChoices.test1834],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 14 [AxisChoices.test1835],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 15 [AxisChoices.test1836],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 16 [AxisChoices.test1837],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 18 [AxisChoices.test1839],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 19 [AxisChoices.test1840],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 20 [AxisChoices.test1841],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 21 [AxisChoices.test1842],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩]
private theorem paid760 : IndexedReceipts.checked rows760 = true := by decide +kernel
theorem route760 (i : Fin 24) : (rows760.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid760 ⟨i.val,i.isLt⟩

private def rows785 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 22 [AxisChoices.test1843],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 23 [AxisChoices.test1844],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 24 [AxisChoices.test1845],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 26 [AxisChoices.test1847],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 27 [AxisChoices.test1848],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 31 [AxisChoices.test1852],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 32 [AxisChoices.test1853],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 33 [AxisChoices.test1854],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 34 [AxisChoices.test1854,AxisChoices.test1855],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 35 [AxisChoices.test1854,AxisChoices.test1856],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow1 36 [AxisChoices.test1854,AxisChoices.test1857],0,.pair pack_R6970Height2313ExplicitRows09_decision1⟩]
private theorem paid785 : IndexedReceipts.checked rows785 = true := by decide +kernel
theorem route785 (i : Fin 15) : (rows785.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid785 ⟨i.val,i.isLt⟩

private def rows920 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,4,some 8,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩]
private theorem paid920 : IndexedReceipts.checked rows920 = true := by decide +kernel
theorem route920 (i : Fin 1) : (rows920.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid920 ⟨i.val,i.isLt⟩

private def rows921 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 39 (some 40) [MeasuredChoices.test1105],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 37 (some 38) [MeasuredChoices.test1079],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 31 (some 32) [MeasuredChoices.test1005],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 29 (some 30) [MeasuredChoices.test977],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 27 (some 28) [MeasuredChoices.test952],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 25 (some 26) [MeasuredChoices.test924],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨⟨50,63,10,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 13 (some 14) [MeasuredChoices.test770],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 9 (some 12) [MeasuredChoices.test724],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow2 4 (some 8) [MeasuredChoices.test671],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩]
private theorem paid921 : IndexedReceipts.checked rows921 = true := by decide +kernel
theorem route921 (i : Fin 10) : (rows921.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid921 ⟨i.val,i.isLt⟩

private def rows940 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 49 (some 64) [MeasuredChoices.test5,MeasuredChoices.test6],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 41 (some 48) [MeasuredChoices.test3,MeasuredChoices.test4],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 33 (some 40) [MeasuredChoices.test1,MeasuredChoices.test2],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 29 (some 32) [MeasuredChoices.test0],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 25 (some 28) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 21 (some 24) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 17 (some 20) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 13 (some 16) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 9 (some 12) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 4 (some 8) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow3 2 (some 3) [],0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨⟨64,721,12,1,1,some 1,0,none,128659,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩,
  ⟨⟨64,721,12,1,0,some 0,0,none,128659,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision0⟩]
private theorem paid940 : IndexedReceipts.checked rows940 = true := by decide +kernel
theorem route940 (i : Fin 13) : (rows940.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid940 ⟨i.val,i.isLt⟩

private def rows953 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 49 (some 52) [MeasuredChoices.test58,MeasuredChoices.test62],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 41 (some 48) [MeasuredChoices.test49,MeasuredChoices.test50],0,.pair ⟨(.node 8030575396047635),.whole,.impossible,291368⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],0,.pair ⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 21 (some 24) [MeasuredChoices.test25,MeasuredChoices.test26],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 17 (some 20) [],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 13 (some 16) [],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 9 (some 12) [],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 4 (some 8) [],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨pack_R6970Height2313ExplicitRows09_pairRow4 2 (some 3) [],0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩,
  ⟨⟨64,721,12,2,1,some 1,0,none,257319,[],[]⟩,0,.pair ⟨.surface,.whole,.surface,0⟩⟩,
  ⟨⟨64,721,12,2,0,some 0,0,none,257319,[],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩]
private theorem paid953 : IndexedReceipts.checked rows953 = true := by decide +kernel
theorem route953 (i : Fin 13) : (rows953.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid953 ⟨i.val,i.isLt⟩

private def rows960 : List IndexedReceipts.Receipt := [
  ⟨⟨64,721,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩,0,.pair pack_R6970Height2313ExplicitRows09_decision4⟩]
private theorem paid960 : IndexedReceipts.checked rows960 = true := by decide +kernel
theorem route960 (i : Fin 1) : (rows960.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid960 ⟨i.val,i.isLt⟩

private def rows969 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,9,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid969 : IndexedReceipts.checked rows969 = true := by decide +kernel
theorem route969 (i : Fin 5) : (rows969.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid969 ⟨i.val,i.isLt⟩

private def rows974 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,9,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid974 : IndexedReceipts.checked rows974 = true := by decide +kernel
theorem route974 (i : Fin 5) : (rows974.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid974 ⟨i.val,i.isLt⟩

private def rows979 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,.pair pack_R6970Height2313ExplicitRows09_decision3⟩]
private theorem paid979 : IndexedReceipts.checked rows979 = true := by decide +kernel
theorem route979 (i : Fin 1) : (rows979.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid979 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows09

section Pack_R6970Height2313ExplicitRows10

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows10_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows10_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows10_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows10_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows10_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows10_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows10_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows10_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1100 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,15,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1100 : IndexedReceipts.checked rows1100 = true := by decide +kernel
theorem route1100 (i : Fin 1) : (rows1100.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1100 ⟨i.val,i.isLt⟩

private def rows1101 : List IndexedReceipts.Receipt := [
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,15,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,15,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,15,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,628,12,2,13,some 16,0,none,257319,[],[]⟩,15,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid1101 : IndexedReceipts.checked rows1101 = true := by decide +kernel
theorem route1101 (i : Fin 4) : (rows1101.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1101 ⟨i.val,i.isLt⟩

private def rows1105 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1105 : IndexedReceipts.checked rows1105 = true := by decide +kernel
theorem route1105 (i : Fin 1) : (rows1105.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1105 ⟨i.val,i.isLt⟩

private def rows1106 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1106 : IndexedReceipts.checked rows1106 = true := by decide +kernel
theorem route1106 (i : Fin 1) : (rows1106.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1106 ⟨i.val,i.isLt⟩

private def rows1107 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1107 : IndexedReceipts.checked rows1107 = true := by decide +kernel
theorem route1107 (i : Fin 1) : (rows1107.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1107 ⟨i.val,i.isLt⟩

private def rows1108 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1108 : IndexedReceipts.checked rows1108 = true := by decide +kernel
theorem route1108 (i : Fin 1) : (rows1108.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1108 ⟨i.val,i.isLt⟩

private def rows1109 : List IndexedReceipts.Receipt := [
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,16,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,16,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid1109 : IndexedReceipts.checked rows1109 = true := by decide +kernel
theorem route1109 (i : Fin 3) : (rows1109.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1109 ⟨i.val,i.isLt⟩

private def rows1112 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,17,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1112 : IndexedReceipts.checked rows1112 = true := by decide +kernel
theorem route1112 (i : Fin 1) : (rows1112.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1112 ⟨i.val,i.isLt⟩

private def rows1113 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,17,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1113 : IndexedReceipts.checked rows1113 = true := by decide +kernel
theorem route1113 (i : Fin 1) : (rows1113.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1113 ⟨i.val,i.isLt⟩

private def rows1114 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,17,.pair pack_R6970Height2313ExplicitRows10_decision2⟩]
private theorem paid1114 : IndexedReceipts.checked rows1114 = true := by decide +kernel
theorem route1114 (i : Fin 1) : (rows1114.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1114 ⟨i.val,i.isLt⟩

private def rows1115 : List IndexedReceipts.Receipt := [
  ⟨⟨64,581,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,17,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,581,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,17,.pair pack_R6970Height2313ExplicitRows10_decision2⟩,
  ⟨⟨64,581,12,2,17,some 20,0,none,257319,[],[]⟩,17,.pair ⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid1115 : IndexedReceipts.checked rows1115 = true := by decide +kernel
theorem route1115 (i : Fin 3) : (rows1115.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1115 ⟨i.val,i.isLt⟩

private def rows1118 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨23,24,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩]
private theorem paid1118 : IndexedReceipts.checked rows1118 = true := by decide +kernel
theorem route1118 (i : Fin 7) : (rows1118.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1118 ⟨i.val,i.isLt⟩

private def rows1126 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨⟨23,24,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows10_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩]
private theorem paid1126 : IndexedReceipts.checked rows1126 = true := by decide +kernel
theorem route1126 (i : Fin 24) : (rows1126.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1126 ⟨i.val,i.isLt⟩

private def rows1143 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows10_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows10_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows10_decision0⟩]
private theorem paid1143 : IndexedReceipts.checked rows1143 = true := by decide +kernel
theorem route1143 (i : Fin 24) : (rows1143.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1143 ⟨i.val,i.isLt⟩

private def rows1199 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩]
private theorem paid1199 : IndexedReceipts.checked rows1199 = true := by decide +kernel
theorem route1199 (i : Fin 1) : (rows1199.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1199 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows10

section Pack_R6970Height2313ExplicitRows11

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows11_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows11_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows11_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows11_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows11_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows11_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows11_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows11_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows11_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1200 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩]
private theorem paid1200 : IndexedReceipts.checked rows1200 = true := by decide +kernel
theorem route1200 (i : Fin 7) : (rows1200.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1200 ⟨i.val,i.isLt⟩

private def rows1208 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow1 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow2 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩]
private theorem paid1208 : IndexedReceipts.checked rows1208 = true := by decide +kernel
theorem route1208 (i : Fin 24) : (rows1208.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1208 ⟨i.val,i.isLt⟩

private def rows1287 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow4 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩]
private theorem paid1287 : IndexedReceipts.checked rows1287 = true := by decide +kernel
theorem route1287 (i : Fin 24) : (rows1287.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1287 ⟨i.val,i.isLt⟩

private def rows1325 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows11_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows11_pairRow5 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows11_decision0⟩,
  ⟨⟨25,27,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩]
private theorem paid1325 : IndexedReceipts.checked rows1325 = true := by decide +kernel
theorem route1325 (i : Fin 9) : (rows1325.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1325 ⟨i.val,i.isLt⟩

private def rows1338 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,.pair pack_R6970Height2313ExplicitRows11_decision2⟩]
private theorem paid1338 : IndexedReceipts.checked rows1338 = true := by decide +kernel
theorem route1338 (i : Fin 2) : (rows1338.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1338 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows11

section Pack_R6970Height2313ExplicitRows12

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows12_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows12_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows12_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows12_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows12_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1221 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow1 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩]
private theorem paid1221 : IndexedReceipts.checked rows1221 = true := by decide +kernel
theorem route1221 (i : Fin 24) : (rows1221.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1221 ⟨i.val,i.isLt⟩

private def rows1255 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩]
private theorem paid1255 : IndexedReceipts.checked rows1255 = true := by decide +kernel
theorem route1255 (i : Fin 3) : (rows1255.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1255 ⟨i.val,i.isLt⟩

private def rows1340 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,.pair pack_R6970Height2313ExplicitRows12_decision2⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows12_decision2⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows12_decision2⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows12_decision2⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows12_decision2⟩]
private theorem paid1340 : IndexedReceipts.checked rows1340 = true := by decide +kernel
theorem route1340 (i : Fin 6) : (rows1340.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1340 ⟨i.val,i.isLt⟩

private def rows1347 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow4 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow5 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows12_decision0⟩]
private theorem paid1347 : IndexedReceipts.checked rows1347 = true := by decide +kernel
theorem route1347 (i : Fin 24) : (rows1347.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1347 ⟨i.val,i.isLt⟩

private def rows1473 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows12_pairRow6 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow6 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow6 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows12_pairRow6 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows12_decision1⟩]
private theorem paid1473 : IndexedReceipts.checked rows1473 = true := by decide +kernel
theorem route1473 (i : Fin 4) : (rows1473.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1473 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows12

section Pack_R6970Height2313ExplicitRows13

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows13_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows13_pairRow6 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨33,40,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows13_decision0 : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows13_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows13_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows13_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1481 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩]
private theorem paid1481 : IndexedReceipts.checked rows1481 = true := by decide +kernel
theorem route1481 (i : Fin 24) : (rows1481.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1481 ⟨i.val,i.isLt⟩

private def rows1519 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨⟨28,32,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow3 22 [AxisChoices.test1843],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩]
private theorem paid1519 : IndexedReceipts.checked rows1519 = true := by decide +kernel
theorem route1519 (i : Fin 24) : (rows1519.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1519 ⟨i.val,i.isLt⟩

private def rows1388 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow4 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows13_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows13_decision2⟩]
private theorem paid1388 : IndexedReceipts.checked rows1388 = true := by decide +kernel
theorem route1388 (i : Fin 9) : (rows1388.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1388 ⟨i.val,i.isLt⟩

private def rows1524 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 65 (some 96) [MeasuredChoices.test87],1,.pair pack_R6970Height2313ExplicitRows13_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 49 (some 64) [MeasuredChoices.test62],1,.pair pack_R6970Height2313ExplicitRows13_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 41 (some 48) [MeasuredChoices.test50],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 33 (some 40) [MeasuredChoices.test44],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 29 (some 32) [MeasuredChoices.test39],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 25 (some 28) [MeasuredChoices.test36],1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 21 (some 24) [MeasuredChoices.test25],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 17 (some 20) [],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 13 (some 16) [],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 9 (some 12) [],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows13_pairRow6 4 (some 8) [],1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩]
private theorem paid1524 : IndexedReceipts.checked rows1524 = true := by decide +kernel
theorem route1524 (i : Fin 11) : (rows1524.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1524 ⟨i.val,i.isLt⟩

private def rows1536 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision0⟩,
  ⟨⟨33,40,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision0⟩,
  ⟨⟨33,40,9,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩,
  ⟨⟨33,40,9,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,.pair pack_R6970Height2313ExplicitRows13_decision3⟩]
private theorem paid1536 : IndexedReceipts.checked rows1536 = true := by decide +kernel
theorem route1536 (i : Fin 4) : (rows1536.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1536 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows13

section Pack_R6970Height2313ExplicitRows14

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows14_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows14_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows14_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows14_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows1400 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow1 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩]
private theorem paid1400 : IndexedReceipts.checked rows1400 = true := by decide +kernel
theorem route1400 (i : Fin 24) : (rows1400.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1400 ⟨i.val,i.isLt⟩

private def rows1436 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows14_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩]
private theorem paid1436 : IndexedReceipts.checked rows1436 = true := by decide +kernel
theorem route1436 (i : Fin 3) : (rows1436.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1436 ⟨i.val,i.isLt⟩

private def rows1580 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow3 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow4 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩]
private theorem paid1580 : IndexedReceipts.checked rows1580 = true := by decide +kernel
theorem route1580 (i : Fin 24) : (rows1580.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1580 ⟨i.val,i.isLt⟩

private def rows1616 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow5 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows14_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow6 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow6 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow6 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow6 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows14_pairRow6 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows14_decision1⟩]
private theorem paid1616 : IndexedReceipts.checked rows1616 = true := by decide +kernel
theorem route1616 (i : Fin 14) : (rows1616.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1616 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows14

section Pack_R6970Height2313ExplicitRows15

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows15_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows15_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows15_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows15_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows15_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows15_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows15_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows15_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows15_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1640 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩]
private theorem paid1640 : IndexedReceipts.checked rows1640 = true := by decide +kernel
theorem route1640 (i : Fin 24) : (rows1640.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1640 ⟨i.val,i.isLt⟩

private def rows1680 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow2 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩]
private theorem paid1680 : IndexedReceipts.checked rows1680 = true := by decide +kernel
theorem route1680 (i : Fin 24) : (rows1680.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1680 ⟨i.val,i.isLt⟩

private def rows1716 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨⟨33,40,9,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨⟨33,40,9,3,25,some 25,0,none,385979,[MeasuredChoices.test924],[]⟩,1,.pair pack_R6970Height2313ExplicitRows15_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows15_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows15_pairRow5 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows15_decision0⟩]
private theorem paid1716 : IndexedReceipts.checked rows1716 = true := by decide +kernel
theorem route1716 (i : Fin 13) : (rows1716.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1716 ⟨i.val,i.isLt⟩

private def rows1719 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,4,29,some 32,0,none,514639,[MeasuredChoices.test1285],[]⟩,1,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid1719 : IndexedReceipts.checked rows1719 = true := by decide +kernel
theorem route1719 (i : Fin 1) : (rows1719.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1719 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows15

section Pack_R6970Height2313ExplicitRows16

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows16_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows16_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows16_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,57,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows16_pairRow3 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨41,49,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows16_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows16_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows16_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows16_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1560 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow0 22 [AxisChoices.test1843],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩]
private theorem paid1560 : IndexedReceipts.checked rows1560 = true := by decide +kernel
theorem route1560 (i : Fin 13) : (rows1560.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1560 ⟨i.val,i.isLt⟩

private def rows1720 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,4,25,some 28,0,none,514639,[MeasuredChoices.test1272],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision2⟩,
  ⟨⟨33,40,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision2⟩,
  ⟨⟨33,40,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision2⟩]
private theorem paid1720 : IndexedReceipts.checked rows1720 = true := by decide +kernel
theorem route1720 (i : Fin 3) : (rows1720.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1720 ⟨i.val,i.isLt⟩

private def rows1723 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 65 (some 96) [MeasuredChoices.test86,MeasuredChoices.test87],1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 0 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 1 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 2 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 3 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 4 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 5 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 6 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 7 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 8 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 9 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 10 [],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 11 [AxisChoices.test1774],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 12 [AxisChoices.test1775],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 13 [AxisChoices.test1776],1,.pair pack_R6970Height2313ExplicitRows16_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 14 [AxisChoices.test1777],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 15 [AxisChoices.test1778],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨⟨41,49,9,2,49,some 56,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩,1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 41 (some 48) [MeasuredChoices.test50],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 33 (some 40) [MeasuredChoices.test44],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 29 (some 32) [MeasuredChoices.test39],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 25 (some 28) [MeasuredChoices.test36],1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 21 (some 24) [MeasuredChoices.test25],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 17 (some 20) [],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩]
private theorem paid1723 : IndexedReceipts.checked rows1723 = true := by decide +kernel
theorem route1723 (i : Fin 24) : (rows1723.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1723 ⟨i.val,i.isLt⟩

private def rows1853 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 13 (some 16) [],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 9 (some 12) [],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow3 4 (some 8) [],1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 16 [AxisChoices.test1779],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 17 [AxisChoices.test1780],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 18 [AxisChoices.test1781],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 19 [AxisChoices.test1782],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 20 [AxisChoices.test1783],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 21 [AxisChoices.test1784],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 22 [AxisChoices.test1785],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 23 [AxisChoices.test1786],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 24 [AxisChoices.test1787],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 25 [AxisChoices.test1788],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 28 [AxisChoices.test1791],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],1,.pair pack_R6970Height2313ExplicitRows16_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 32 [AxisChoices.test1795],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 35 [AxisChoices.test1798],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩]
private theorem paid1853 : IndexedReceipts.checked rows1853 = true := by decide +kernel
theorem route1853 (i : Fin 24) : (rows1853.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1853 ⟨i.val,i.isLt⟩

private def rows1763 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 39 [AxisChoices.test1802],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows16_pairRow2 47 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩]
private theorem paid1763 : IndexedReceipts.checked rows1763 = true := by decide +kernel
theorem route1763 (i : Fin 9) : (rows1763.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1763 ⟨i.val,i.isLt⟩

private def rows1856 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,39,some 40,0,none,385979,[MeasuredChoices.test1105],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨⟨41,49,9,3,37,some 38,0,none,385979,[MeasuredChoices.test1079],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨⟨41,49,9,3,35,some 36,0,none,385979,[MeasuredChoices.test1055],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩,
  ⟨⟨41,49,9,3,33,some 34,0,none,385979,[MeasuredChoices.test1029],[]⟩,1,.pair pack_R6970Height2313ExplicitRows16_decision3⟩]
private theorem paid1856 : IndexedReceipts.checked rows1856 = true := by decide +kernel
theorem route1856 (i : Fin 4) : (rows1856.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1856 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows16

section Pack_R6970Height2313ExplicitRows17

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows17_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,57,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows17_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows17_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows17_pairRow3 (axisLo : ℕ) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩
private def pack_R6970Height2313ExplicitRows17_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows17_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows17_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows17_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1780 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 56 [AxisChoices.test1819],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 57 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 58 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 59 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 60 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 61 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 62 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 63 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow0 64 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 0 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 1 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 2 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 3 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 4 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 5 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 6 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 7 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 8 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 9 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 10 [],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 11 [AxisChoices.test1774],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 12 [AxisChoices.test1775],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 13 [AxisChoices.test1776],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 14 [AxisChoices.test1777],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩]
private theorem paid1780 : IndexedReceipts.checked rows1780 = true := by decide +kernel
theorem route1780 (i : Fin 24) : (rows1780.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1780 ⟨i.val,i.isLt⟩

private def rows1804 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 15 [AxisChoices.test1778],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 16 [AxisChoices.test1779],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 17 [AxisChoices.test1780],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 18 [AxisChoices.test1781],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 19 [AxisChoices.test1782],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 20 [AxisChoices.test1783],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 21 [AxisChoices.test1784],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 22 [AxisChoices.test1785],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 23 [AxisChoices.test1786],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 24 [AxisChoices.test1787],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 25 [AxisChoices.test1788],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 28 [AxisChoices.test1791],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 32 [AxisChoices.test1795],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 35 [AxisChoices.test1798],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 39 [AxisChoices.test1802],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],1,.excluded none⟩]
private theorem paid1804 : IndexedReceipts.checked rows1804 = true := by decide +kernel
theorem route1804 (i : Fin 24) : (rows1804.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1804 ⟨i.val,i.isLt⟩

private def rows1830 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩]
private theorem paid1830 : IndexedReceipts.checked rows1830 = true := by decide +kernel
theorem route1830 (i : Fin 7) : (rows1830.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1830 ⟨i.val,i.isLt⟩

private def rows2020 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows17_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow2 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩,
  ⟨⟨41,49,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨⟨41,49,9,3,25,some 25,0,none,385979,[MeasuredChoices.test924],[]⟩,1,.pair pack_R6970Height2313ExplicitRows17_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows17_decision0⟩]
private theorem paid2020 : IndexedReceipts.checked rows2020 = true := by decide +kernel
theorem route2020 (i : Fin 18) : (rows2020.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2020 ⟨i.val,i.isLt⟩

private def rows2027 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,61,some 64,0,none,257319,[MeasuredChoices.test82,MeasuredChoices.test85],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,59,some 60,0,none,257319,[MeasuredChoices.test82],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,1,.pair ⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 0,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 1,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 2,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 3,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 4,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 5,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 6,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 7,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows17_pairRow3 8,1,.pair pack_R6970Height2313ExplicitRows17_decision1⟩]
private theorem paid2027 : IndexedReceipts.checked rows2027 = true := by decide +kernel
theorem route2027 (i : Fin 12) : (rows2027.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2027 ⟨i.val,i.isLt⟩

private def rows2030 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,1,.pair ⟨.marked,.whole,.impossible,0⟩⟩]
private theorem paid2030 : IndexedReceipts.checked rows2030 = true := by decide +kernel
theorem route2030 (i : Fin 1) : (rows2030.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2030 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows17

section Pack_R6970Height2313ExplicitRows18

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows18_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows18_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows18_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows18_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows18_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows18_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows18_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows18_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows1880 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow0 22 [AxisChoices.test1843],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow1 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩]
private theorem paid1880 : IndexedReceipts.checked rows1880 = true := by decide +kernel
theorem route1880 (i : Fin 24) : (rows1880.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1880 ⟨i.val,i.isLt⟩

private def rows1912 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow2 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩]
private theorem paid1912 : IndexedReceipts.checked rows1912 = true := by decide +kernel
theorem route1912 (i : Fin 24) : (rows1912.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1912 ⟨i.val,i.isLt⟩

private def rows1952 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows18_pairRow3 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow4 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows18_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows18_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows18_decision1⟩]
private theorem paid1952 : IndexedReceipts.checked rows1952 = true := by decide +kernel
theorem route1952 (i : Fin 17) : (rows1952.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1952 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows18

section Pack_R6970Height2313ExplicitRows19

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows19_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows19_pairRow6 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨50,63,10,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows19_pairRow7 (seedLo : ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨50,63,10,3,seedLo,some seedLo,0,none,385979,tests,[]⟩
private def pack_R6970Height2313ExplicitRows19_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows19_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows19_decision2 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows1980 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩]
private theorem paid1980 : IndexedReceipts.checked rows1980 = true := by decide +kernel
theorem route1980 (i : Fin 24) : (rows1980.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid1980 ⟨i.val,i.isLt⟩

private def rows2019 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows19_pairRow2 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩]
private theorem paid2019 : IndexedReceipts.checked rows2019 = true := by decide +kernel
theorem route2019 (i : Fin 1) : (rows2019.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2019 ⟨i.val,i.isLt⟩

private def rows2145 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,56,some 56,56,some 56,257319,[MeasuredChoices.test77],[AxisChoices.test1819]⟩,1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 53 (some 54) [MeasuredChoices.test70,MeasuredChoices.test71],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 49 (some 52) [MeasuredChoices.test58,MeasuredChoices.test62],1,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 41 (some 48) [MeasuredChoices.test50],1,.pair ⟨(.node 8030575396047635),.intersection,.impossible,291368⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 33 (some 40) [MeasuredChoices.test44],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 29 (some 32) [MeasuredChoices.test39],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 25 (some 28) [MeasuredChoices.test36],1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 21 (some 24) [MeasuredChoices.test25],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 17 (some 20) [],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 13 (some 16) [],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 9 (some 12) [],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow6 4 (some 8) [],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 9 [],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 10 [],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 11 [AxisChoices.test1774],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 12 [AxisChoices.test1775],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 13 [AxisChoices.test1776],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 14 [AxisChoices.test1777],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 15 [AxisChoices.test1778],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 16 [AxisChoices.test1779],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 17 [AxisChoices.test1780],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 18 [AxisChoices.test1781],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 19 [AxisChoices.test1782],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow4 20 [AxisChoices.test1783],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩]
private theorem paid2145 : IndexedReceipts.checked rows2145 = true := by decide +kernel
theorem route2145 (i : Fin 24) : (rows2145.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2145 ⟨i.val,i.isLt⟩

private def rows2052 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 21 [AxisChoices.test1784],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 22 [AxisChoices.test1784,AxisChoices.test1785],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 23 [AxisChoices.test1784,AxisChoices.test1786],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 24 [AxisChoices.test1787],1,.pair pack_R6970Height2313ExplicitRows19_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 25 [AxisChoices.test1788],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 26 [AxisChoices.test1788,AxisChoices.test1789],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow5 27 [AxisChoices.test1788,AxisChoices.test1790],1,.excluded none⟩]
private theorem paid2052 : IndexedReceipts.checked rows2052 = true := by decide +kernel
theorem route2052 (i : Fin 7) : (rows2052.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2052 ⟨i.val,i.isLt⟩

private def rows2149 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 52,0,none,288407,[MeasuredChoices.test104,MeasuredChoices.test114],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩]
private theorem paid2149 : IndexedReceipts.checked rows2149 = true := by decide +kernel
theorem route2149 (i : Fin 1) : (rows2149.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2149 ⟨i.val,i.isLt⟩

private def rows2151 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,41,some 48,0,none,291368,[MeasuredChoices.test125],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩]
private theorem paid2151 : IndexedReceipts.checked rows2151 = true := by decide +kernel
theorem route2151 (i : Fin 1) : (rows2151.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2151 ⟨i.val,i.isLt⟩

private def rows2161 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows19_pairRow7 39 [MeasuredChoices.test1105],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow7 37 [MeasuredChoices.test1080],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow7 38 [MeasuredChoices.test1093],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨⟨50,63,10,3,33,some 34,0,none,385979,[MeasuredChoices.test1029],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨⟨50,63,10,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨⟨50,63,10,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨⟨50,63,10,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow7 26 [MeasuredChoices.test939],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow7 25 [MeasuredChoices.test924],1,.pair pack_R6970Height2313ExplicitRows19_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows19_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows19_decision1⟩]
private theorem paid2161 : IndexedReceipts.checked rows2161 = true := by decide +kernel
theorem route2161 (i : Fin 13) : (rows2161.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2161 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows19

section Pack_R6970Height2313ExplicitRows20

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows20_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows20_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows20_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows20_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows20_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows20_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows2059 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 28 [AxisChoices.test1791],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 29 [AxisChoices.test1791,AxisChoices.test1792],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 32 [AxisChoices.test1795],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 33 [AxisChoices.test1795,AxisChoices.test1796],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 34 [AxisChoices.test1795,AxisChoices.test1797],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 35 [AxisChoices.test1798],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 39 [AxisChoices.test1802],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 56 [AxisChoices.test1819],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow0 57 [AxisChoices.test1819,AxisChoices.test1820],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 0 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 1 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 2 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 3 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩]
private theorem paid2059 : IndexedReceipts.checked rows2059 = true := by decide +kernel
theorem route2059 (i : Fin 24) : (rows2059.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2059 ⟨i.val,i.isLt⟩

private def rows2093 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 4 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 5 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 6 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 7 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 8 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 9 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 10 [],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 11 [AxisChoices.test1774],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 12 [AxisChoices.test1775],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 13 [AxisChoices.test1776],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 14 [AxisChoices.test1777],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 15 [AxisChoices.test1778],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 16 [AxisChoices.test1779],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 17 [AxisChoices.test1780],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 18 [AxisChoices.test1781],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 19 [AxisChoices.test1782],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow1 20 [AxisChoices.test1783],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 21 [AxisChoices.test1784],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 22 [AxisChoices.test1784,AxisChoices.test1785],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 23 [AxisChoices.test1784,AxisChoices.test1786],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 24 [AxisChoices.test1787],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 25 [AxisChoices.test1788],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 26 [AxisChoices.test1788,AxisChoices.test1789],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 27 [AxisChoices.test1788,AxisChoices.test1790],1,.excluded none⟩]
private theorem paid2093 : IndexedReceipts.checked rows2093 = true := by decide +kernel
theorem route2093 (i : Fin 24) : (rows2093.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2093 ⟨i.val,i.isLt⟩

private def rows2117 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 28 [AxisChoices.test1791],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 29 [AxisChoices.test1791,AxisChoices.test1792],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 32 [AxisChoices.test1795],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 33 [AxisChoices.test1795,AxisChoices.test1796],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 34 [AxisChoices.test1795,AxisChoices.test1797],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 35 [AxisChoices.test1798],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 36 [AxisChoices.test1798,AxisChoices.test1799],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 37 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 38 [AxisChoices.test1798,AxisChoices.test1800],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 39 [AxisChoices.test1802],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 40 [AxisChoices.test1802,AxisChoices.test1803],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 41 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 42 [AxisChoices.test1802,AxisChoices.test1804],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 43 [AxisChoices.test1802,AxisChoices.test1806],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 44 [AxisChoices.test1802,AxisChoices.test1807],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 45 [AxisChoices.test1802,AxisChoices.test1808],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 46 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow2 47 [AxisChoices.test1802,AxisChoices.test1809],1,.excluded none⟩]
private theorem paid2117 : IndexedReceipts.checked rows2117 = true := by decide +kernel
theorem route2117 (i : Fin 18) : (rows2117.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2117 ⟨i.val,i.isLt⟩

private def rows2240 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows20_pairRow3 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows20_decision0⟩,
  ⟨⟨50,63,10,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,1,.pair pack_R6970Height2313ExplicitRows20_decision1⟩]
private theorem paid2240 : IndexedReceipts.checked rows2240 = true := by decide +kernel
theorem route2240 (i : Fin 10) : (rows2240.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2240 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows20

section Pack_R6970Height2313ExplicitRows21

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows21_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows21_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows21_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows21_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows21_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows21_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows21_decision0 : PairPrices.Decision := ⟨.affine,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows21_decision1 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows21_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows21_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows2259 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩]
private theorem paid2259 : IndexedReceipts.checked rows2259 = true := by decide +kernel
theorem route2259 (i : Fin 24) : (rows2259.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2259 ⟨i.val,i.isLt⟩

private def rows2309 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow2 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows21_decision1⟩,
  ⟨⟨50,63,10,3,14,some 14,0,none,385979,[MeasuredChoices.test785],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision3⟩,
  ⟨⟨50,63,10,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision3⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision3⟩,
  ⟨⟨50,63,10,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision3⟩]
private theorem paid2309 : IndexedReceipts.checked rows2309 = true := by decide +kernel
theorem route2309 (i : Fin 7) : (rows2309.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2309 ⟨i.val,i.isLt⟩

private def rows2316 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,1,49,some 64,0,none,128659,[MeasuredChoices.test5,MeasuredChoices.test6],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision0⟩,
  ⟨⟨64,722,12,1,41,some 48,0,none,128659,[MeasuredChoices.test3,MeasuredChoices.test4],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision0⟩,
  ⟨⟨64,722,12,1,33,some 40,0,none,128659,[MeasuredChoices.test1,MeasuredChoices.test2],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision0⟩,
  ⟨⟨64,722,12,1,29,some 32,0,none,128659,[MeasuredChoices.test0],[]⟩,1,.pair pack_R6970Height2313ExplicitRows21_decision0⟩]
private theorem paid2316 : IndexedReceipts.checked rows2316 = true := by decide +kernel
theorem route2316 (i : Fin 4) : (rows2316.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2316 ⟨i.val,i.isLt⟩

private def rows5181 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow3 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5181 : IndexedReceipts.checked rows5181 = true := by decide +kernel
theorem route5181 (i : Fin 7) : (rows5181.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5181 ⟨i.val,i.isLt⟩

private def rows5192 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow4 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5192 : IndexedReceipts.checked rows5192 = true := by decide +kernel
theorem route5192 (i : Fin 10) : (rows5192.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5192 ⟨i.val,i.isLt⟩

private def rows5208 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows21_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows21_decision2⟩]
private theorem paid5208 : IndexedReceipts.checked rows5208 = true := by decide +kernel
theorem route5208 (i : Fin 6) : (rows5208.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5208 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows21

section Pack_R6970Height2313ExplicitRows22

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows22_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows22_decision0 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows5220 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow0 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow0 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow0 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow0 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5220 : IndexedReceipts.checked rows5220 = true := by decide +kernel
theorem route5220 (i : Fin 4) : (rows5220.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5220 ⟨i.val,i.isLt⟩

private def rows5224 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow1 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5224 : IndexedReceipts.checked rows5224 = true := by decide +kernel
theorem route5224 (i : Fin 10) : (rows5224.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5224 ⟨i.val,i.isLt⟩

private def rows5240 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow2 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5240 : IndexedReceipts.checked rows5240 = true := by decide +kernel
theorem route5240 (i : Fin 10) : (rows5240.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5240 ⟨i.val,i.isLt⟩

private def rows5256 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow3 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5256 : IndexedReceipts.checked rows5256 = true := by decide +kernel
theorem route5256 (i : Fin 10) : (rows5256.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5256 ⟨i.val,i.isLt⟩

private def rows5272 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow4 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5272 : IndexedReceipts.checked rows5272 = true := by decide +kernel
theorem route5272 (i : Fin 10) : (rows5272.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5272 ⟨i.val,i.isLt⟩

private def rows5288 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow5 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5288 : IndexedReceipts.checked rows5288 = true := by decide +kernel
theorem route5288 (i : Fin 10) : (rows5288.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5288 ⟨i.val,i.isLt⟩

private def rows5304 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows22_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows22_pairRow6 14 [AxisChoices.test1835],1,.three none⟩]
private theorem paid5304 : IndexedReceipts.checked rows5304 = true := by decide +kernel
theorem route5304 (i : Fin 9) : (rows5304.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5304 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows22

section Pack_R6970Height2313ExplicitRows23

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows23_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows23_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows23_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows23_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows5319 : List IndexedReceipts.Receipt := [
  ⟨⟨58,58,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,.three none⟩]
private theorem paid5319 : IndexedReceipts.checked rows5319 = true := by decide +kernel
theorem route5319 (i : Fin 1) : (rows5319.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5319 ⟨i.val,i.isLt⟩

private def rows5320 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow0 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5320 : IndexedReceipts.checked rows5320 = true := by decide +kernel
theorem route5320 (i : Fin 10) : (rows5320.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5320 ⟨i.val,i.isLt⟩

private def rows5336 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow1 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5336 : IndexedReceipts.checked rows5336 = true := by decide +kernel
theorem route5336 (i : Fin 10) : (rows5336.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5336 ⟨i.val,i.isLt⟩

private def rows5352 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow2 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5352 : IndexedReceipts.checked rows5352 = true := by decide +kernel
theorem route5352 (i : Fin 10) : (rows5352.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5352 ⟨i.val,i.isLt⟩

private def rows5368 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow3 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5368 : IndexedReceipts.checked rows5368 = true := by decide +kernel
theorem route5368 (i : Fin 10) : (rows5368.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5368 ⟨i.val,i.isLt⟩

private def rows5384 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 12 [AxisChoices.test1833],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 13 [AxisChoices.test1834],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 14 [AxisChoices.test1835],1,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow4 15 [AxisChoices.test1836],1,.three none⟩]
private theorem paid5384 : IndexedReceipts.checked rows5384 = true := by decide +kernel
theorem route5384 (i : Fin 10) : (rows5384.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5384 ⟨i.val,i.isLt⟩

private def rows2180 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow5 22 [AxisChoices.test1843],1,.pair pack_R6970Height2313ExplicitRows23_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow6 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow6 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows23_pairRow6 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows23_decision1⟩]
private theorem paid2180 : IndexedReceipts.checked rows2180 = true := by decide +kernel
theorem route2180 (i : Fin 15) : (rows2180.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2180 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows23

section Pack_R6970Height2313ExplicitRows24

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows24_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows24_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows24_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows24_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,15,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows24_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) : PairCell.Row := ⟨64,722,12,1,seedLo,seedHi,0,none,128659,[],[]⟩
private def pack_R6970Height2313ExplicitRows24_pairRow5 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,722,12,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows24_decision0 : PairPrices.Decision := ⟨.affine,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows24_decision1 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows24_decision2 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows24_decision3 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows24_decision4 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private def decision5 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows2200 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 9 [AxisChoices.test1830],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 12 [AxisChoices.test1833],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 13 [AxisChoices.test1834],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow0 21 [AxisChoices.test1842],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 0 [AxisChoices.test1821],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 1 [AxisChoices.test1822],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 2 [AxisChoices.test1823],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 5 [AxisChoices.test1826],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 8 [AxisChoices.test1829],1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 14 [AxisChoices.test1835],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 15 [AxisChoices.test1836],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 16 [AxisChoices.test1837],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 18 [AxisChoices.test1839],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 19 [AxisChoices.test1840],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow1 20 [AxisChoices.test1841],1,.pair pack_R6970Height2313ExplicitRows24_decision2⟩,
  ⟨⟨50,63,10,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩]
private theorem paid2200 : IndexedReceipts.checked rows2200 = true := by decide +kernel
theorem route2200 (i : Fin 24) : (rows2200.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2200 ⟨i.val,i.isLt⟩

private def rows2239 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,.pair pack_R6970Height2313ExplicitRows24_decision3⟩]
private theorem paid2239 : IndexedReceipts.checked rows2239 = true := by decide +kernel
theorem route2239 (i : Fin 1) : (rows2239.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2239 ⟨i.val,i.isLt⟩

private def rows2320 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 25 (some 28),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 21 (some 24),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 17 (some 20),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 13 (some 16),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 9 (some 12),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 4 (some 8),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow4 2 (some 3),1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨⟨64,722,12,1,1,some 1,0,none,128659,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩,
  ⟨⟨64,722,12,1,0,some 0,0,none,128659,[],[]⟩,1,.pair pack_R6970Height2313ExplicitRows24_decision0⟩]
private theorem paid2320 : IndexedReceipts.checked rows2320 = true := by decide +kernel
theorem route2320 (i : Fin 9) : (rows2320.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2320 ⟨i.val,i.isLt⟩

private def rows2329 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 49 (some 52) [MeasuredChoices.test58,MeasuredChoices.test62],1,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 45 (some 48) [MeasuredChoices.test55,MeasuredChoices.test56],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 41 (some 44) [MeasuredChoices.test49,MeasuredChoices.test50],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 37 (some 40) [MeasuredChoices.test45,MeasuredChoices.test46],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 33 (some 36) [MeasuredChoices.test43,MeasuredChoices.test44],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 29 (some 32) [MeasuredChoices.test39],1,.pair ⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 25 (some 28) [MeasuredChoices.test35,MeasuredChoices.test36],1,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 21 (some 24) [MeasuredChoices.test25,MeasuredChoices.test26],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 17 (some 20) [],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 13 (some 16) [],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 9 (some 12) [],1,.pair decision5⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow5 4 (some 8) [],1,.pair decision5⟩]
private theorem paid2329 : IndexedReceipts.checked rows2329 = true := by decide +kernel
theorem route2329 (i : Fin 12) : (rows2329.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2329 ⟨i.val,i.isLt⟩

private def rows2330 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,49,some 52,0,none,288407,[MeasuredChoices.test104,MeasuredChoices.test114],[]⟩,1,.pair decision5⟩]
private theorem paid2330 : IndexedReceipts.checked rows2330 = true := by decide +kernel
theorem route2330 (i : Fin 1) : (rows2330.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2330 ⟨i.val,i.isLt⟩

private def rows2336 : List IndexedReceipts.Receipt := [
  ⟨⟨64,722,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,1,.pair decision5⟩]
private theorem paid2336 : IndexedReceipts.checked rows2336 = true := by decide +kernel
theorem route2336 (i : Fin 1) : (rows2336.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2336 ⟨i.val,i.isLt⟩

private def rows2344 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,.pair ⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨⟨23,24,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,.pair ⟨(.node 16272920511362425),.intersection,.impossible,306290⟩⟩,
  ⟨⟨23,24,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩]
private theorem paid2344 : IndexedReceipts.checked rows2344 = true := by decide +kernel
theorem route2344 (i : Fin 8) : (rows2344.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2344 ⟨i.val,i.isLt⟩

private def rows2348 : List IndexedReceipts.Receipt := [
  ⟨⟨23,24,9,2,23,some 24,0,none,306290,[MeasuredChoices.test347],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩]
private theorem paid2348 : IndexedReceipts.checked rows2348 = true := by decide +kernel
theorem route2348 (i : Fin 1) : (rows2348.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2348 ⟨i.val,i.isLt⟩

private def rows2354 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows24_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows24_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows24_decision1⟩,
  ⟨⟨23,24,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩]
private theorem paid2354 : IndexedReceipts.checked rows2354 = true := by decide +kernel
theorem route2354 (i : Fin 15) : (rows2354.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2354 ⟨i.val,i.isLt⟩

private def rows2395 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,.pair pack_R6970Height2313ExplicitRows24_decision4⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,.pair ⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨⟨25,27,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,.pair ⟨(.node 16272920511362425),.intersection,.impossible,306290⟩⟩]
private theorem paid2395 : IndexedReceipts.checked rows2395 = true := by decide +kernel
theorem route2395 (i : Fin 3) : (rows2395.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2395 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows24

section Pack_R6970Height2313ExplicitRows25

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows25_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,17,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows25_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨23,24,9,3,15,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows25_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,21,some 24,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows25_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,19,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows25_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows25_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows25_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows25_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows25_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows2399 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,23,some 24,0,none,306290,[MeasuredChoices.test347],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩]
private theorem paid2399 : IndexedReceipts.checked rows2399 = true := by decide +kernel
theorem route2399 (i : Fin 1) : (rows2399.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2399 ⟨i.val,i.isLt⟩

private def rows2362 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow0 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩]
private theorem paid2362 : IndexedReceipts.checked rows2362 = true := by decide +kernel
theorem route2362 (i : Fin 13) : (rows2362.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2362 ⟨i.val,i.isLt⟩

private def rows2400 : List IndexedReceipts.Receipt := [
  ⟨⟨25,27,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,2,.pair pack_R6970Height2313ExplicitRows25_decision2⟩]
private theorem paid2400 : IndexedReceipts.checked rows2400 = true := by decide +kernel
theorem route2400 (i : Fin 5) : (rows2400.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2400 ⟨i.val,i.isLt⟩

private def rows2405 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow2 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩]
private theorem paid2405 : IndexedReceipts.checked rows2405 = true := by decide +kernel
theorem route2405 (i : Fin 24) : (rows2405.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2405 ⟨i.val,i.isLt⟩

private def rows2442 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow3 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow4 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows25_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows25_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩]
private theorem paid2442 : IndexedReceipts.checked rows2442 = true := by decide +kernel
theorem route2442 (i : Fin 24) : (rows2442.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2442 ⟨i.val,i.isLt⟩

private def rows2478 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows25_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows25_decision0⟩]
private theorem paid2478 : IndexedReceipts.checked rows2478 = true := by decide +kernel
theorem route2478 (i : Fin 1) : (rows2478.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2478 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows25

section Pack_R6970Height2313ExplicitRows26

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows26_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows26_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows26_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨25,27,9,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows26_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows26_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows26_pairRow5 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨28,32,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows26_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows26_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows26_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows2479 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow0 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow1 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩]
private theorem paid2479 : IndexedReceipts.checked rows2479 = true := by decide +kernel
theorem route2479 (i : Fin 24) : (rows2479.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2479 ⟨i.val,i.isLt⟩

private def rows2518 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨⟨25,27,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩]
private theorem paid2518 : IndexedReceipts.checked rows2518 = true := by decide +kernel
theorem route2518 (i : Fin 6) : (rows2518.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2518 ⟨i.val,i.isLt⟩

private def rows2524 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 33 (some 40) [MeasuredChoices.test44],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 29 (some 32) [MeasuredChoices.test39],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 25 (some 28) [MeasuredChoices.test36],2,.pair ⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 23 (some 24) [MeasuredChoices.test29],2,.pair ⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 21 (some 22) [MeasuredChoices.test25],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 17 (some 20) [],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 13 (some 16) [],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 9 (some 12) [],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow5 4 (some 8) [],2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩]
private theorem paid2524 : IndexedReceipts.checked rows2524 = true := by decide +kernel
theorem route2524 (i : Fin 9) : (rows2524.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2524 ⟨i.val,i.isLt⟩

private def rows2529 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩]
private theorem paid2529 : IndexedReceipts.checked rows2529 = true := by decide +kernel
theorem route2529 (i : Fin 1) : (rows2529.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2529 ⟨i.val,i.isLt⟩

private def rows2536 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow4 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨⟨28,32,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows26_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows26_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩]
private theorem paid2536 : IndexedReceipts.checked rows2536 = true := by decide +kernel
theorem route2536 (i : Fin 24) : (rows2536.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2536 ⟨i.val,i.isLt⟩

private def rows2556 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows26_pairRow3 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows26_decision0⟩]
private theorem paid2556 : IndexedReceipts.checked rows2556 = true := by decide +kernel
theorem route2556 (i : Fin 3) : (rows2556.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2556 ⟨i.val,i.isLt⟩

private def rows2619 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,2,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid2619 : IndexedReceipts.checked rows2619 = true := by decide +kernel
theorem route2619 (i : Fin 1) : (rows2619.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2619 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows26

section Pack_R6970Height2313ExplicitRows27

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows27_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows27_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨28,32,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows27_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows27_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows27_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨33,40,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows27_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows27_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows27_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows2559 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow0 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow1 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩]
private theorem paid2559 : IndexedReceipts.checked rows2559 = true := by decide +kernel
theorem route2559 (i : Fin 24) : (rows2559.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2559 ⟨i.val,i.isLt⟩

private def rows2598 : List IndexedReceipts.Receipt := [
  ⟨⟨28,32,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨⟨28,32,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨⟨28,32,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,2,.three none⟩]
private theorem paid2598 : IndexedReceipts.checked rows2598 = true := by decide +kernel
theorem route2598 (i : Fin 3) : (rows2598.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2598 ⟨i.val,i.isLt⟩

private def rows2620 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 49 (some 64) [MeasuredChoices.test62],2,.pair ⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 41 (some 48) [MeasuredChoices.test50],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 33 (some 40) [MeasuredChoices.test44],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 29 (some 32) [MeasuredChoices.test39],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 25 (some 28) [MeasuredChoices.test36],2,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 23 (some 24) [MeasuredChoices.test29],2,.pair ⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 21 (some 22) [MeasuredChoices.test25],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 17 (some 20) [],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 13 (some 16) [],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 9 (some 12) [],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow4 4 (some 8) [],2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩]
private theorem paid2620 : IndexedReceipts.checked rows2620 = true := by decide +kernel
theorem route2620 (i : Fin 11) : (rows2620.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2620 ⟨i.val,i.isLt⟩

private def rows2621 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,2,.pair ⟨.marked,.intersection,.impossible,0⟩⟩]
private theorem paid2621 : IndexedReceipts.checked rows2621 = true := by decide +kernel
theorem route2621 (i : Fin 1) : (rows2621.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2621 ⟨i.val,i.isLt⟩

private def rows7060 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,25,some 26,0,none,302619,[MeasuredChoices.test166],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨⟨33,40,9,2,27,some 28,0,none,302619,[MeasuredChoices.test169],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩]
private theorem paid7060 : IndexedReceipts.checked rows7060 = true := by decide +kernel
theorem route7060 (i : Fin 2) : (rows7060.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid7060 ⟨i.val,i.isLt⟩

private def rows2628 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩]
private theorem paid2628 : IndexedReceipts.checked rows2628 = true := by decide +kernel
theorem route2628 (i : Fin 1) : (rows2628.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2628 ⟨i.val,i.isLt⟩

private def rows2634 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨⟨33,40,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨⟨33,40,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision2⟩,
  ⟨⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,2,.three none⟩,
  ⟨⟨33,40,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows27_decision0⟩]
private theorem paid2634 : IndexedReceipts.checked rows2634 = true := by decide +kernel
theorem route2634 (i : Fin 16) : (rows2634.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2634 ⟨i.val,i.isLt⟩

private def rows5402 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩,2,.three none⟩,
  ⟨⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,2,.three none⟩]
private theorem paid5402 : IndexedReceipts.checked rows5402 = true := by decide +kernel
theorem route5402 (i : Fin 2) : (rows5402.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5402 ⟨i.val,i.isLt⟩

private def rows5404 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows27_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows27_pairRow2 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid5404 : IndexedReceipts.checked rows5404 = true := by decide +kernel
theorem route5404 (i : Fin 13) : (rows5404.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5404 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows27

section Pack_R6970Height2313ExplicitRows28

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows28_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows28_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows28_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨33,40,9,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows28_pairRow3 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨41,49,9,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows28_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows28_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows28_decision2 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows2678 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow0 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨⟨33,40,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩]
private theorem paid2678 : IndexedReceipts.checked rows2678 = true := by decide +kernel
theorem route2678 (i : Fin 24) : (rows2678.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2678 ⟨i.val,i.isLt⟩

private def rows2656 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow2 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩]
private theorem paid2656 : IndexedReceipts.checked rows2656 = true := by decide +kernel
theorem route2656 (i : Fin 3) : (rows2656.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2656 ⟨i.val,i.isLt⟩

private def rows2701 : List IndexedReceipts.Receipt := [
  ⟨⟨33,40,9,4,25,some 28,0,none,514639,[MeasuredChoices.test1272],[]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩]
private theorem paid2701 : IndexedReceipts.checked rows2701 = true := by decide +kernel
theorem route2701 (i : Fin 1) : (rows2701.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2701 ⟨i.val,i.isLt⟩

private def rows2702 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 65 (some 96) [MeasuredChoices.test86,MeasuredChoices.test87],2,.pair ⟨.marked,.intersection,.impossible,0⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 0 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 1 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 2 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 3 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 4 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 5 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 6 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 7 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 8 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 9 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 10 [],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 13 [AxisChoices.test1776],2,.pair pack_R6970Height2313ExplicitRows28_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 14 [AxisChoices.test1777],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 15 [AxisChoices.test1778],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 16 [AxisChoices.test1779],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 57 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 58 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 59 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 60 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 61 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 62 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 63 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 64 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩]
private theorem paid2702 : IndexedReceipts.checked rows2702 = true := by decide +kernel
theorem route2702 (i : Fin 24) : (rows2702.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2702 ⟨i.val,i.isLt⟩

private def rows2768 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 41 (some 48) [MeasuredChoices.test50],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 33 (some 40) [MeasuredChoices.test44],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 29 (some 32) [MeasuredChoices.test39],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 25 (some 28) [MeasuredChoices.test36],2,.pair ⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 23 (some 24) [MeasuredChoices.test29],2,.pair ⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 21 (some 22) [MeasuredChoices.test25],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 17 (some 20) [],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 13 (some 16) [],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 9 (some 12) [],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow3 4 (some 8) [],2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 17 [AxisChoices.test1780],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 18 [AxisChoices.test1781],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 19 [AxisChoices.test1782],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 20 [AxisChoices.test1783],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 21 [AxisChoices.test1784],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 22 [AxisChoices.test1785],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 23 [AxisChoices.test1786],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 24 [AxisChoices.test1787],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 25 [AxisChoices.test1788],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 28 [AxisChoices.test1791],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],2,.pair pack_R6970Height2313ExplicitRows28_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 32 [AxisChoices.test1795],2,.excluded none⟩]
private theorem paid2768 : IndexedReceipts.checked rows2768 = true := by decide +kernel
theorem route2768 (i : Fin 24) : (rows2768.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2768 ⟨i.val,i.isLt⟩

private def rows2736 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows28_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],2,.excluded none⟩]
private theorem paid2736 : IndexedReceipts.checked rows2736 = true := by decide +kernel
theorem route2736 (i : Fin 2) : (rows2736.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2736 ⟨i.val,i.isLt⟩

private def rows2774 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,.pair pack_R6970Height2313ExplicitRows28_decision2⟩]
private theorem paid2774 : IndexedReceipts.checked rows2774 = true := by decide +kernel
theorem route2774 (i : Fin 1) : (rows2774.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2774 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows28

section Pack_R6970Height2313ExplicitRows29

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows29_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,2,49,some 64,axisLo,some axisLo,257319,[MeasuredChoices.test62],rect⟩
private def pack_R6970Height2313ExplicitRows29_pairRow1 (axisLo : ℕ) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩
private def pack_R6970Height2313ExplicitRows29_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,41,some 44,axisLo,some axisLo,385979,[MeasuredChoices.test1133],rect⟩
private def pack_R6970Height2313ExplicitRows29_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,45,some 48,axisLo,some axisLo,385979,[MeasuredChoices.test1139],rect⟩
private def pack_R6970Height2313ExplicitRows29_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows29_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows29_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows29_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows2738 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 35 [AxisChoices.test1798],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 36 [AxisChoices.test1798,AxisChoices.test1799],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 37 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 38 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 39 [AxisChoices.test1802],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 40 [AxisChoices.test1802,AxisChoices.test1803],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 41 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 42 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 43 [AxisChoices.test1802,AxisChoices.test1806],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 44 [AxisChoices.test1802,AxisChoices.test1807],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 45 [AxisChoices.test1802,AxisChoices.test1808],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 46 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 47 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow0 56 [AxisChoices.test1819],2,.excluded none⟩]
private theorem paid2738 : IndexedReceipts.checked rows2738 = true := by decide +kernel
theorem route2738 (i : Fin 14) : (rows2738.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2738 ⟨i.val,i.isLt⟩

private def rows2880 : List IndexedReceipts.Receipt := [
  ⟨⟨41,49,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 31 [AxisChoices.test1852],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 32 [AxisChoices.test1853],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 33 [AxisChoices.test1854],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 34 [AxisChoices.test1854,AxisChoices.test1855],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 35 [AxisChoices.test1854,AxisChoices.test1856],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 36 [AxisChoices.test1854,AxisChoices.test1857],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 37 [AxisChoices.test1857,AxisChoices.test1858],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 38 [AxisChoices.test1859],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 39 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 40 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 41 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 42 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 43 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow2 44 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨⟨41,49,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨⟨41,49,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,2,.pair pack_R6970Height2313ExplicitRows29_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩]
private theorem paid2880 : IndexedReceipts.checked rows2880 = true := by decide +kernel
theorem route2880 (i : Fin 24) : (rows2880.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2880 ⟨i.val,i.isLt⟩

private def rows2781 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 10 [AxisChoices.test1831],2,.pair pack_R6970Height2313ExplicitRows29_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 25 [AxisChoices.test1845,AxisChoices.test1846],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 26 [AxisChoices.test1847],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩]
private theorem paid2781 : IndexedReceipts.checked rows2781 = true := by decide +kernel
theorem route2781 (i : Fin 24) : (rows2781.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2781 ⟨i.val,i.isLt⟩

private def rows2807 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 27 [AxisChoices.test1848],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 28 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 29 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 30 [AxisChoices.test1848,AxisChoices.test1851],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 31 [AxisChoices.test1852],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 32 [AxisChoices.test1853],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 33 [AxisChoices.test1854],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 34 [AxisChoices.test1854,AxisChoices.test1855],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 35 [AxisChoices.test1854,AxisChoices.test1856],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 36 [AxisChoices.test1854,AxisChoices.test1857],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow3 37 [AxisChoices.test1857,AxisChoices.test1858],2,.pair pack_R6970Height2313ExplicitRows29_decision0⟩]
private theorem paid2807 : IndexedReceipts.checked rows2807 = true := by decide +kernel
theorem route2807 (i : Fin 11) : (rows2807.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2807 ⟨i.val,i.isLt⟩

private def rows2891 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,61,some 64,0,none,257319,[MeasuredChoices.test82,MeasuredChoices.test85],[]⟩,2,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,59,some 60,0,none,257319,[MeasuredChoices.test82],[]⟩,2,.pair ⟨.marked,.whole,.impossible,0⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,2,.pair ⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow1 0,2,.pair pack_R6970Height2313ExplicitRows29_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow1 1,2,.pair pack_R6970Height2313ExplicitRows29_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow1 2,2,.pair pack_R6970Height2313ExplicitRows29_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow1 3,2,.pair pack_R6970Height2313ExplicitRows29_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows29_pairRow1 4,2,.pair pack_R6970Height2313ExplicitRows29_decision2⟩]
private theorem paid2891 : IndexedReceipts.checked rows2891 = true := by decide +kernel
theorem route2891 (i : Fin 8) : (rows2891.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2891 ⟨i.val,i.isLt⟩

private def rows2894 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,2,.pair ⟨.marked,.whole,.impossible,0⟩⟩]
private theorem paid2894 : IndexedReceipts.checked rows2894 = true := by decide +kernel
theorem route2894 (i : Fin 1) : (rows2894.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2894 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows29

section Pack_R6970Height2313ExplicitRows30

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows30_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,45,some 48,axisLo,some axisLo,385979,[MeasuredChoices.test1139],rect⟩
private def pack_R6970Height2313ExplicitRows30_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨41,49,9,3,41,some 44,axisLo,some axisLo,385979,[MeasuredChoices.test1133],rect⟩
private def pack_R6970Height2313ExplicitRows30_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,39,some 39,axisLo,some axisLo,385979,[MeasuredChoices.test1105],rect⟩
private def pack_R6970Height2313ExplicitRows30_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows30_pairRow4 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨50,63,10,2,seedLo,seedHi,0,none,257319,tests,[]⟩
private def pack_R6970Height2313ExplicitRows30_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows30_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows30_decision2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows30_decision3 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩

private def rows2818 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 38 [AxisChoices.test1859],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 39 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 40 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 41 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 42 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 43 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 44 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 45 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 46 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 47 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow0 48 [AxisChoices.test1859,AxisChoices.test1860],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 10 [AxisChoices.test1831],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩]
private theorem paid2818 : IndexedReceipts.checked rows2818 = true := by decide +kernel
theorem route2818 (i : Fin 24) : (rows2818.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2818 ⟨i.val,i.isLt⟩

private def rows2843 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 25 [AxisChoices.test1845,AxisChoices.test1846],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 26 [AxisChoices.test1847],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 27 [AxisChoices.test1848],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 28 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 29 [AxisChoices.test1848,AxisChoices.test1849],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow1 30 [AxisChoices.test1848,AxisChoices.test1851],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩]
private theorem paid2843 : IndexedReceipts.checked rows2843 = true := by decide +kernel
theorem route2843 (i : Fin 16) : (rows2843.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2843 ⟨i.val,i.isLt⟩

private def rows3121 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,53,some 53,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test71],[]⟩,2,.pair ⟨(.node 8027880449706932),.intersection,.impossible,287630⟩⟩,
  ⟨⟨50,63,10,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,2,.pair ⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 49 (some 50) [MeasuredChoices.test58,MeasuredChoices.test62],2,.pair ⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 41 (some 44) [MeasuredChoices.test50],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 29 (some 32) [MeasuredChoices.test39],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 25 (some 28) [MeasuredChoices.test36],2,.pair ⟨(.node 12122407664504094),.intersection,.impossible,304553⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 23 (some 24) [MeasuredChoices.test29],2,.pair ⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 21 (some 22) [MeasuredChoices.test25],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 17 (some 20) [],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 13 (some 16) [],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 9 (some 12) [],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow4 4 (some 8) [],2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 0 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 1 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 2 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 3 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 4 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 5 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 6 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 7 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 8 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 9 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 10 [],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow3 11 [AxisChoices.test1774],2,.pair pack_R6970Height2313ExplicitRows30_decision2⟩]
private theorem paid3121 : IndexedReceipts.checked rows3121 = true := by decide +kernel
theorem route3121 (i : Fin 24) : (rows3121.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3121 ⟨i.val,i.isLt⟩

private def rows3124 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩]
private theorem paid3124 : IndexedReceipts.checked rows3124 = true := by decide +kernel
theorem route3124 (i : Fin 1) : (rows3124.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3124 ⟨i.val,i.isLt⟩

private def rows3127 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,49,some 50,0,none,289917,[MeasuredChoices.test104,MeasuredChoices.test118],[]⟩,2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩]
private theorem paid3127 : IndexedReceipts.checked rows3127 = true := by decide +kernel
theorem route3127 (i : Fin 1) : (rows3127.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3127 ⟨i.val,i.isLt⟩

private def rows3135 : List IndexedReceipts.Receipt := [
  ⟨⟨50,63,10,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,.pair pack_R6970Height2313ExplicitRows30_decision3⟩]
private theorem paid3135 : IndexedReceipts.checked rows3135 = true := by decide +kernel
theorem route3135 (i : Fin 1) : (rows3135.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3135 ⟨i.val,i.isLt⟩

private def rows3141 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 3 [AxisChoices.test1824],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 4 [AxisChoices.test1825],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 6 [AxisChoices.test1827],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 7 [AxisChoices.test1828],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows30_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows30_pairRow2 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows30_decision0⟩]
private theorem paid3141 : IndexedReceipts.checked rows3141 = true := by decide +kernel
theorem route3141 (i : Fin 16) : (rows3141.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3141 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows30

section Pack_R6970Height2313ExplicitRows31

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows31_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows31_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,54,some 54,axisLo,some axisLo,257319,[MeasuredChoices.test73],rect⟩
private def pack_R6970Height2313ExplicitRows31_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows31_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,57,some 57,axisLo,some axisLo,257319,[MeasuredChoices.test79],rect⟩
private def pack_R6970Height2313ExplicitRows31_pairRow4 (axisLo : ℕ) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩
private def pack_R6970Height2313ExplicitRows31_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows31_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows3078 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 12 [AxisChoices.test1775],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 13 [AxisChoices.test1776],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 14 [AxisChoices.test1777],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 15 [AxisChoices.test1778],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 16 [AxisChoices.test1779],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 17 [AxisChoices.test1780],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 18 [AxisChoices.test1781],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 19 [AxisChoices.test1782],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow0 20 [AxisChoices.test1783],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 21 [AxisChoices.test1784],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 24 [AxisChoices.test1787],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 25 [AxisChoices.test1788],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 28 [AxisChoices.test1791],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 32 [AxisChoices.test1795],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 35 [AxisChoices.test1798],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩]
private theorem paid3078 : IndexedReceipts.checked rows3078 = true := by decide +kernel
theorem route3078 (i : Fin 24) : (rows3078.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3078 ⟨i.val,i.isLt⟩

private def rows3104 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 39 [AxisChoices.test1802],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 5 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 6 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 7 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 8 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 9 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 10 [],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 11 [AxisChoices.test1774],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 12 [AxisChoices.test1775],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 13 [AxisChoices.test1776],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 14 [AxisChoices.test1777],2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 15 [AxisChoices.test1778],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 16 [AxisChoices.test1779],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 17 [AxisChoices.test1780],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 18 [AxisChoices.test1781],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩]
private theorem paid3104 : IndexedReceipts.checked rows3104 = true := by decide +kernel
theorem route3104 (i : Fin 24) : (rows3104.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3104 ⟨i.val,i.isLt⟩

private def rows2914 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 19 [AxisChoices.test1782],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow2 20 [AxisChoices.test1783],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 21 [AxisChoices.test1784],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 24 [AxisChoices.test1787],2,.pair pack_R6970Height2313ExplicitRows31_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 25 [AxisChoices.test1788],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 27 [AxisChoices.test1788,AxisChoices.test1790],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 28 [AxisChoices.test1791],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 29 [AxisChoices.test1791,AxisChoices.test1792],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 32 [AxisChoices.test1795],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 33 [AxisChoices.test1795,AxisChoices.test1796],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 34 [AxisChoices.test1795,AxisChoices.test1797],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 35 [AxisChoices.test1798],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 36 [AxisChoices.test1798,AxisChoices.test1799],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 37 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 38 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 39 [AxisChoices.test1802],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 40 [AxisChoices.test1802,AxisChoices.test1803],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 41 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 42 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 43 [AxisChoices.test1802,AxisChoices.test1806],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 44 [AxisChoices.test1802,AxisChoices.test1807],2,.excluded none⟩]
private theorem paid2914 : IndexedReceipts.checked rows2914 = true := by decide +kernel
theorem route2914 (i : Fin 24) : (rows2914.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2914 ⟨i.val,i.isLt⟩

private def rows2940 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 45 [AxisChoices.test1802,AxisChoices.test1808],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 46 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 47 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 56 [AxisChoices.test1819],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow3 57 [AxisChoices.test1819,AxisChoices.test1820],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow4 0,2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow4 1,2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow4 2,2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow4 3,2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows31_pairRow4 4,2,.pair pack_R6970Height2313ExplicitRows31_decision1⟩]
private theorem paid2940 : IndexedReceipts.checked rows2940 = true := by decide +kernel
theorem route2940 (i : Fin 10) : (rows2940.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2940 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows31

section Pack_R6970Height2313ExplicitRows32

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows32_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows32_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,56,some 56,axisLo,some axisLo,257319,[MeasuredChoices.test77],rect⟩
private def pack_R6970Height2313ExplicitRows32_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,55,some 55,axisLo,some axisLo,257319,[MeasuredChoices.test70,MeasuredChoices.test74],rect⟩
private def pack_R6970Height2313ExplicitRows32_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,2,55,some 55,axisLo,some axisLo,257319,[MeasuredChoices.test74],rect⟩
private def pack_R6970Height2313ExplicitRows32_decision0 : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows32_decision1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩

private def rows2958 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 5 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 6 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 7 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 8 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 9 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 10 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 11 [AxisChoices.test1774],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 12 [AxisChoices.test1775],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 13 [AxisChoices.test1776],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 14 [AxisChoices.test1777],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 15 [AxisChoices.test1778],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 16 [AxisChoices.test1779],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 17 [AxisChoices.test1780],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 18 [AxisChoices.test1781],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 19 [AxisChoices.test1782],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow0 20 [AxisChoices.test1783],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 21 [AxisChoices.test1784],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 22 [AxisChoices.test1784,AxisChoices.test1785],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 23 [AxisChoices.test1784,AxisChoices.test1786],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 24 [AxisChoices.test1787],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 25 [AxisChoices.test1788],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 26 [AxisChoices.test1788,AxisChoices.test1789],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 27 [AxisChoices.test1788,AxisChoices.test1790],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 28 [AxisChoices.test1791],2,.excluded none⟩]
private theorem paid2958 : IndexedReceipts.checked rows2958 = true := by decide +kernel
theorem route2958 (i : Fin 24) : (rows2958.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2958 ⟨i.val,i.isLt⟩

private def rows2982 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 29 [AxisChoices.test1791,AxisChoices.test1792],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 32 [AxisChoices.test1795],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 33 [AxisChoices.test1795,AxisChoices.test1796],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 34 [AxisChoices.test1795,AxisChoices.test1797],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 35 [AxisChoices.test1798],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 36 [AxisChoices.test1798,AxisChoices.test1799],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 37 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 38 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 39 [AxisChoices.test1802],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 40 [AxisChoices.test1802,AxisChoices.test1803],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 41 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 42 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 43 [AxisChoices.test1802,AxisChoices.test1806],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 44 [AxisChoices.test1802,AxisChoices.test1807],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 45 [AxisChoices.test1802,AxisChoices.test1808],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 46 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 47 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow1 56 [AxisChoices.test1819],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 0 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 1 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 2 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 3 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 4 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 5 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩]
private theorem paid2982 : IndexedReceipts.checked rows2982 = true := by decide +kernel
theorem route2982 (i : Fin 24) : (rows2982.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid2982 ⟨i.val,i.isLt⟩

private def rows3016 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 6 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 7 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 8 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 9 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 10 [],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 11 [AxisChoices.test1774],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 12 [AxisChoices.test1775],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 13 [AxisChoices.test1776],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 14 [AxisChoices.test1777],2,.pair pack_R6970Height2313ExplicitRows32_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 15 [AxisChoices.test1778],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 16 [AxisChoices.test1779],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 17 [AxisChoices.test1780],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 18 [AxisChoices.test1781],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 19 [AxisChoices.test1782],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow2 20 [AxisChoices.test1783],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 21 [AxisChoices.test1784],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 22 [AxisChoices.test1784,AxisChoices.test1785],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 23 [AxisChoices.test1784,AxisChoices.test1786],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 24 [AxisChoices.test1787],2,.pair pack_R6970Height2313ExplicitRows32_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 25 [AxisChoices.test1788],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 26 [AxisChoices.test1788,AxisChoices.test1789],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 27 [AxisChoices.test1788,AxisChoices.test1790],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 28 [AxisChoices.test1791],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 29 [AxisChoices.test1791,AxisChoices.test1792],2,.excluded none⟩]
private theorem paid3016 : IndexedReceipts.checked rows3016 = true := by decide +kernel
theorem route3016 (i : Fin 24) : (rows3016.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3016 ⟨i.val,i.isLt⟩

private def rows3042 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 32 [AxisChoices.test1795],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 33 [AxisChoices.test1795,AxisChoices.test1796],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 34 [AxisChoices.test1795,AxisChoices.test1797],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 35 [AxisChoices.test1798],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 36 [AxisChoices.test1798,AxisChoices.test1799],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 37 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 38 [AxisChoices.test1798,AxisChoices.test1800],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 39 [AxisChoices.test1802],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 40 [AxisChoices.test1802,AxisChoices.test1803],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 41 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 42 [AxisChoices.test1802,AxisChoices.test1804],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 43 [AxisChoices.test1802,AxisChoices.test1806],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 44 [AxisChoices.test1802,AxisChoices.test1807],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 45 [AxisChoices.test1802,AxisChoices.test1808],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 46 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩,
  ⟨pack_R6970Height2313ExplicitRows32_pairRow3 47 [AxisChoices.test1802,AxisChoices.test1809],2,.excluded none⟩]
private theorem paid3042 : IndexedReceipts.checked rows3042 = true := by decide +kernel
theorem route3042 (i : Fin 16) : (rows3042.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3042 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows32

section Pack_R6970Height2313ExplicitRows33

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows33_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows33_pairRow7 (seedLo : ℕ) (seedHi : Option ℕ) (tests : List MeasuredBound.Test) : PairCell.Row := ⟨64,722,12,1,seedLo,seedHi,0,none,128659,tests,[]⟩
private def pack_R6970Height2313ExplicitRows33_decision0 : PairPrices.Decision := ⟨.affine,.whole,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows33_decision1 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows33_decision2 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows33_decision3 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩

private def rows3381 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow0 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows33_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow0 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows33_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow0 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows33_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow0 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows33_decision1⟩,
  ⟨⟨50,63,10,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,2,.pair pack_R6970Height2313ExplicitRows33_decision3⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,.pair pack_R6970Height2313ExplicitRows33_decision3⟩,
  ⟨⟨50,63,10,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,.pair pack_R6970Height2313ExplicitRows33_decision3⟩]
private theorem paid3381 : IndexedReceipts.checked rows3381 = true := by decide +kernel
theorem route3381 (i : Fin 7) : (rows3381.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3381 ⟨i.val,i.isLt⟩

private def rows3389 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 49 (some 64) [MeasuredChoices.test5,MeasuredChoices.test6],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 41 (some 48) [MeasuredChoices.test3,MeasuredChoices.test4],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 33 (some 40) [MeasuredChoices.test1,MeasuredChoices.test2],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 29 (some 32) [MeasuredChoices.test0],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 25 (some 28) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 21 (some 24) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 17 (some 20) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 13 (some 16) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 9 (some 12) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 4 (some 8) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow7 2 (some 3) [],2,.pair pack_R6970Height2313ExplicitRows33_decision0⟩]
private theorem paid3389 : IndexedReceipts.checked rows3389 = true := by decide +kernel
theorem route3389 (i : Fin 11) : (rows3389.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3389 ⟨i.val,i.isLt⟩

private def rows6642 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow1 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6642 : IndexedReceipts.checked rows6642 = true := by decide +kernel
theorem route6642 (i : Fin 6) : (rows6642.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6642 ⟨i.val,i.isLt⟩

private def rows6650 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow2 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6650 : IndexedReceipts.checked rows6650 = true := by decide +kernel
theorem route6650 (i : Fin 9) : (rows6650.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6650 ⟨i.val,i.isLt⟩

private def rows6665 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow3 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6665 : IndexedReceipts.checked rows6665 = true := by decide +kernel
theorem route6665 (i : Fin 9) : (rows6665.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6665 ⟨i.val,i.isLt⟩

private def rows6680 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow4 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6680 : IndexedReceipts.checked rows6680 = true := by decide +kernel
theorem route6680 (i : Fin 9) : (rows6680.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6680 ⟨i.val,i.isLt⟩

private def rows6695 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow5 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6695 : IndexedReceipts.checked rows6695 = true := by decide +kernel
theorem route6695 (i : Fin 9) : (rows6695.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6695 ⟨i.val,i.isLt⟩

private def rows6710 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows33_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩,
  ⟨pack_R6970Height2313ExplicitRows33_pairRow6 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows33_decision2⟩]
private theorem paid6710 : IndexedReceipts.checked rows6710 = true := by decide +kernel
theorem route6710 (i : Fin 4) : (rows6710.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6710 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows33

section Pack_R6970Height2313ExplicitRows34

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows34_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_pairRow7 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows34_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6718 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow0 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6718 : IndexedReceipts.checked rows6718 = true := by decide +kernel
theorem route6718 (i : Fin 5) : (rows6718.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6718 ⟨i.val,i.isLt⟩

private def rows6725 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow1 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6725 : IndexedReceipts.checked rows6725 = true := by decide +kernel
theorem route6725 (i : Fin 9) : (rows6725.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6725 ⟨i.val,i.isLt⟩

private def rows6740 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow2 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6740 : IndexedReceipts.checked rows6740 = true := by decide +kernel
theorem route6740 (i : Fin 9) : (rows6740.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6740 ⟨i.val,i.isLt⟩

private def rows6755 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow3 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6755 : IndexedReceipts.checked rows6755 = true := by decide +kernel
theorem route6755 (i : Fin 9) : (rows6755.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6755 ⟨i.val,i.isLt⟩

private def rows6770 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow4 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6770 : IndexedReceipts.checked rows6770 = true := by decide +kernel
theorem route6770 (i : Fin 9) : (rows6770.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6770 ⟨i.val,i.isLt⟩

private def rows6785 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow5 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6785 : IndexedReceipts.checked rows6785 = true := by decide +kernel
theorem route6785 (i : Fin 9) : (rows6785.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6785 ⟨i.val,i.isLt⟩

private def rows6800 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow6 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6800 : IndexedReceipts.checked rows6800 = true := by decide +kernel
theorem route6800 (i : Fin 9) : (rows6800.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6800 ⟨i.val,i.isLt⟩

private def rows6815 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows34_pairRow7 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow7 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows34_pairRow7 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows34_decision0⟩]
private theorem paid6815 : IndexedReceipts.checked rows6815 = true := by decide +kernel
theorem route6815 (i : Fin 3) : (rows6815.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6815 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows34

section Pack_R6970Height2313ExplicitRows35

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows35_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows35_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows35_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,14,some 14,axisLo,some axisLo,385979,[MeasuredChoices.test785],rect⟩
private def pack_R6970Height2313ExplicitRows35_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,25,some 25,axisLo,some axisLo,385979,[MeasuredChoices.test924],rect⟩
private def pack_R6970Height2313ExplicitRows35_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,23,some 23,axisLo,some axisLo,385979,[MeasuredChoices.test896],rect⟩
private def pack_R6970Height2313ExplicitRows35_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows35_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows35_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6820 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow0 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6820 : IndexedReceipts.checked rows6820 = true := by decide +kernel
theorem route6820 (i : Fin 6) : (rows6820.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6820 ⟨i.val,i.isLt⟩

private def rows6830 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow1 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6830 : IndexedReceipts.checked rows6830 = true := by decide +kernel
theorem route6830 (i : Fin 9) : (rows6830.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6830 ⟨i.val,i.isLt⟩

private def rows6845 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow2 14 [AxisChoices.test1835],2,.three none⟩]
private theorem paid6845 : IndexedReceipts.checked rows6845 = true := by decide +kernel
theorem route6845 (i : Fin 9) : (rows6845.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6845 ⟨i.val,i.isLt⟩

private def rows3242 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 24 [AxisChoices.test1845],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow3 25 [AxisChoices.test1845,AxisChoices.test1846],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow4 23 [AxisChoices.test1844],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩]
private theorem paid3242 : IndexedReceipts.checked rows3242 = true := by decide +kernel
theorem route3242 (i : Fin 24) : (rows3242.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3242 ⟨i.val,i.isLt⟩

private def rows3294 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows35_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows35_pairRow5 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows35_decision0⟩]
private theorem paid3294 : IndexedReceipts.checked rows3294 = true := by decide +kernel
theorem route3294 (i : Fin 4) : (rows3294.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3294 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows35

section Pack_R6970Height2313ExplicitRows36

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows36_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,22,some 22,axisLo,some axisLo,385979,[MeasuredChoices.test882],rect⟩
private def pack_R6970Height2313ExplicitRows36_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,21,some 21,axisLo,some axisLo,385979,[MeasuredChoices.test869],rect⟩
private def pack_R6970Height2313ExplicitRows36_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,20,some 20,axisLo,some axisLo,385979,[MeasuredChoices.test856],rect⟩
private def pack_R6970Height2313ExplicitRows36_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,19,some 19,axisLo,some axisLo,385979,[MeasuredChoices.test843],rect⟩
private def pack_R6970Height2313ExplicitRows36_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,63,10,3,18,some 18,axisLo,some axisLo,385979,[MeasuredChoices.test831],rect⟩
private def pack_R6970Height2313ExplicitRows36_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,37,some 37,axisLo,some axisLo,385979,[MeasuredChoices.test1079],rect⟩
private def pack_R6970Height2313ExplicitRows36_decision0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private def pack_R6970Height2313ExplicitRows36_decision1 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows3299 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows36_pairRow0 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow0 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow0 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow0 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow0 22 [AxisChoices.test1843],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 12 [AxisChoices.test1833],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 13 [AxisChoices.test1834],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow1 21 [AxisChoices.test1842],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩]
private theorem paid3299 : IndexedReceipts.checked rows3299 = true := by decide +kernel
theorem route3299 (i : Fin 24) : (rows3299.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3299 ⟨i.val,i.isLt⟩

private def rows3340 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow2 20 [AxisChoices.test1841],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 14 [AxisChoices.test1835],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 15 [AxisChoices.test1836],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 16 [AxisChoices.test1837],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 18 [AxisChoices.test1839],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow3 19 [AxisChoices.test1840],2,.pair pack_R6970Height2313ExplicitRows36_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩]
private theorem paid3340 : IndexedReceipts.checked rows3340 = true := by decide +kernel
theorem route3340 (i : Fin 20) : (rows3340.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid3340 ⟨i.val,i.isLt⟩

private def rows5920 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 22 [AxisChoices.test1843],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 23 [AxisChoices.test1844],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 24 [AxisChoices.test1845],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 25 [AxisChoices.test1845,AxisChoices.test1846],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 26 [AxisChoices.test1847],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 27 [AxisChoices.test1848],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 28 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 29 [AxisChoices.test1848,AxisChoices.test1849],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 30 [AxisChoices.test1848,AxisChoices.test1851],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 31 [AxisChoices.test1852],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 32 [AxisChoices.test1853],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 33 [AxisChoices.test1854],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 34 [AxisChoices.test1854,AxisChoices.test1855],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 35 [AxisChoices.test1854,AxisChoices.test1856],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 36 [AxisChoices.test1854,AxisChoices.test1857],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows36_pairRow5 37 [AxisChoices.test1857,AxisChoices.test1858],2,.three none⟩]
private theorem paid5920 : IndexedReceipts.checked rows5920 = true := by decide +kernel
theorem route5920 (i : Fin 16) : (rows5920.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5920 ⟨i.val,i.isLt⟩

private def rows5936 : List IndexedReceipts.Receipt := [
  ⟨⟨50,50,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩,
  ⟨⟨50,50,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,.pair pack_R6970Height2313ExplicitRows36_decision1⟩]
private theorem paid5936 : IndexedReceipts.checked rows5936 = true := by decide +kernel
theorem route5936 (i : Fin 2) : (rows5936.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5936 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows36

section Pack_R6970Height2313ExplicitRows37

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows37_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows37_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows5938 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow0 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid5938 : IndexedReceipts.checked rows5938 = true := by decide +kernel
theorem route5938 (i : Fin 9) : (rows5938.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5938 ⟨i.val,i.isLt⟩

private def rows5954 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow1 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid5954 : IndexedReceipts.checked rows5954 = true := by decide +kernel
theorem route5954 (i : Fin 11) : (rows5954.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5954 ⟨i.val,i.isLt⟩

private def rows5972 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow2 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid5972 : IndexedReceipts.checked rows5972 = true := by decide +kernel
theorem route5972 (i : Fin 11) : (rows5972.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5972 ⟨i.val,i.isLt⟩

private def rows5990 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow3 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid5990 : IndexedReceipts.checked rows5990 = true := by decide +kernel
theorem route5990 (i : Fin 11) : (rows5990.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid5990 ⟨i.val,i.isLt⟩

private def rows6008 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow4 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6008 : IndexedReceipts.checked rows6008 = true := by decide +kernel
theorem route6008 (i : Fin 11) : (rows6008.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6008 ⟨i.val,i.isLt⟩

private def rows6026 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows37_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows37_decision0⟩]
private theorem paid6026 : IndexedReceipts.checked rows6026 = true := by decide +kernel
theorem route6026 (i : Fin 6) : (rows6026.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6026 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows37

section Pack_R6970Height2313ExplicitRows38

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows38_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows38_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6038 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow0 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6038 : IndexedReceipts.checked rows6038 = true := by decide +kernel
theorem route6038 (i : Fin 5) : (rows6038.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6038 ⟨i.val,i.isLt⟩

private def rows6044 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow1 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6044 : IndexedReceipts.checked rows6044 = true := by decide +kernel
theorem route6044 (i : Fin 11) : (rows6044.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6044 ⟨i.val,i.isLt⟩

private def rows6062 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow2 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6062 : IndexedReceipts.checked rows6062 = true := by decide +kernel
theorem route6062 (i : Fin 11) : (rows6062.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6062 ⟨i.val,i.isLt⟩

private def rows6080 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow3 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6080 : IndexedReceipts.checked rows6080 = true := by decide +kernel
theorem route6080 (i : Fin 11) : (rows6080.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6080 ⟨i.val,i.isLt⟩

private def rows6098 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow4 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6098 : IndexedReceipts.checked rows6098 = true := by decide +kernel
theorem route6098 (i : Fin 11) : (rows6098.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6098 ⟨i.val,i.isLt⟩

private def rows6116 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow5 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6116 : IndexedReceipts.checked rows6116 = true := by decide +kernel
theorem route6116 (i : Fin 11) : (rows6116.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6116 ⟨i.val,i.isLt⟩

private def rows6134 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows38_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows38_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows38_decision0⟩]
private theorem paid6134 : IndexedReceipts.checked rows6134 = true := by decide +kernel
theorem route6134 (i : Fin 3) : (rows6134.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6134 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows38

section Pack_R6970Height2313ExplicitRows39

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows39_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows39_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows39_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,17,some 17,axisLo,some axisLo,385979,[MeasuredChoices.test821],rect⟩
private def pack_R6970Height2313ExplicitRows39_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows39_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨51,51,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows39_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨52,52,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows39_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6139 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow0 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6139 : IndexedReceipts.checked rows6139 = true := by decide +kernel
theorem route6139 (i : Fin 8) : (rows6139.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6139 ⟨i.val,i.isLt⟩

private def rows6152 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow1 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6152 : IndexedReceipts.checked rows6152 = true := by decide +kernel
theorem route6152 (i : Fin 11) : (rows6152.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6152 ⟨i.val,i.isLt⟩

private def rows6170 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow2 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6170 : IndexedReceipts.checked rows6170 = true := by decide +kernel
theorem route6170 (i : Fin 11) : (rows6170.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6170 ⟨i.val,i.isLt⟩

private def rows6188 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow3 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6188 : IndexedReceipts.checked rows6188 = true := by decide +kernel
theorem route6188 (i : Fin 11) : (rows6188.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6188 ⟨i.val,i.isLt⟩

private def rows6205 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow4 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6205 : IndexedReceipts.checked rows6205 = true := by decide +kernel
theorem route6205 (i : Fin 11) : (rows6205.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6205 ⟨i.val,i.isLt⟩

private def rows6222 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows39_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows39_pairRow5 15 [AxisChoices.test1836],2,.three none⟩]
private theorem paid6222 : IndexedReceipts.checked rows6222 = true := by decide +kernel
theorem route6222 (i : Fin 10) : (rows6222.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6222 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows39

section Pack_R6970Height2313ExplicitRows40

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows40_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨53,53,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨54,54,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨55,55,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨56,56,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨57,57,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows40_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6238 : List IndexedReceipts.Receipt := [
  ⟨⟨52,52,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,2,.three none⟩]
private theorem paid6238 : IndexedReceipts.checked rows6238 = true := by decide +kernel
theorem route6238 (i : Fin 1) : (rows6238.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6238 ⟨i.val,i.isLt⟩

private def rows6239 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow0 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6239 : IndexedReceipts.checked rows6239 = true := by decide +kernel
theorem route6239 (i : Fin 11) : (rows6239.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6239 ⟨i.val,i.isLt⟩

private def rows6256 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow1 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6256 : IndexedReceipts.checked rows6256 = true := by decide +kernel
theorem route6256 (i : Fin 11) : (rows6256.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6256 ⟨i.val,i.isLt⟩

private def rows6273 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow2 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6273 : IndexedReceipts.checked rows6273 = true := by decide +kernel
theorem route6273 (i : Fin 11) : (rows6273.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6273 ⟨i.val,i.isLt⟩

private def rows6290 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow3 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6290 : IndexedReceipts.checked rows6290 = true := by decide +kernel
theorem route6290 (i : Fin 11) : (rows6290.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6290 ⟨i.val,i.isLt⟩

private def rows6307 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow4 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6307 : IndexedReceipts.checked rows6307 = true := by decide +kernel
theorem route6307 (i : Fin 11) : (rows6307.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6307 ⟨i.val,i.isLt⟩

private def rows6324 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows40_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows40_pairRow5 13 [AxisChoices.test1834],2,.three none⟩]
private theorem paid6324 : IndexedReceipts.checked rows6324 = true := by decide +kernel
theorem route6324 (i : Fin 8) : (rows6324.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6324 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows40

section Pack_R6970Height2313ExplicitRows41

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.PairReceipts

private def pack_R6970Height2313ExplicitRows41_pairRow0 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨58,58,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow1 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨59,59,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow2 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨60,60,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow3 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨61,61,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow4 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨62,62,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow5 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨63,63,10,3,16,some 16,axisLo,some axisLo,385979,[MeasuredChoices.test807],rect⟩
private def pack_R6970Height2313ExplicitRows41_pairRow6 (axisLo : ℕ) (rect : List AxisTests.Test) : PairCell.Row := ⟨50,50,10,3,15,some 15,axisLo,some axisLo,385979,[MeasuredChoices.test797],rect⟩
private def pack_R6970Height2313ExplicitRows41_decision0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

private def rows6338 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow0 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow0 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow0 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6338 : IndexedReceipts.checked rows6338 = true := by decide +kernel
theorem route6338 (i : Fin 3) : (rows6338.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6338 ⟨i.val,i.isLt⟩

private def rows6341 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow1 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6341 : IndexedReceipts.checked rows6341 = true := by decide +kernel
theorem route6341 (i : Fin 11) : (rows6341.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6341 ⟨i.val,i.isLt⟩

private def rows6358 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow2 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6358 : IndexedReceipts.checked rows6358 = true := by decide +kernel
theorem route6358 (i : Fin 11) : (rows6358.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6358 ⟨i.val,i.isLt⟩

private def rows6375 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow3 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6375 : IndexedReceipts.checked rows6375 = true := by decide +kernel
theorem route6375 (i : Fin 11) : (rows6375.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6375 ⟨i.val,i.isLt⟩

private def rows6392 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow4 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6392 : IndexedReceipts.checked rows6392 = true := by decide +kernel
theorem route6392 (i : Fin 11) : (rows6392.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6392 ⟨i.val,i.isLt⟩

private def rows6409 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 12 [AxisChoices.test1833],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 13 [AxisChoices.test1834],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 14 [AxisChoices.test1835],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 15 [AxisChoices.test1836],2,.three none⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow5 16 [AxisChoices.test1837],2,.three none⟩]
private theorem paid6409 : IndexedReceipts.checked rows6409 = true := by decide +kernel
theorem route6409 (i : Fin 11) : (rows6409.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6409 ⟨i.val,i.isLt⟩

private def rows6426 : List IndexedReceipts.Receipt := [
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 0 [AxisChoices.test1821],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 1 [AxisChoices.test1822],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 2 [AxisChoices.test1823],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 5 [AxisChoices.test1826],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 8 [AxisChoices.test1829],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩,
  ⟨pack_R6970Height2313ExplicitRows41_pairRow6 9 [AxisChoices.test1830],2,.pair pack_R6970Height2313ExplicitRows41_decision0⟩]
private theorem paid6426 : IndexedReceipts.checked rows6426 = true := by decide +kernel
theorem route6426 (i : Fin 6) : (rows6426.get ⟨i.val,i.isLt⟩).Done :=
  IndexedReceipts.doneAt paid6426 ⟨i.val,i.isLt⟩

end Research6970.Height2313.Research6969.PairReceipts
end Pack_R6970Height2313ExplicitRows41
