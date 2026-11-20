import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_8_58_flag : Flag := ⟨8, 58, 3310⟩
private def endpoint_8_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_58_base : receiptBase endpoint_8_58_flag endpoint_8_58_sources = some 208141947499313143 := by decide +kernel
private theorem endpoint_8_58_window_0 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 2 208141947499313143 = some 208141947499313143 := by decide +kernel
private theorem endpoint_8_58_window_2 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 2 2 208141947499313143 = some 208141947499313143 := by decide +kernel
private theorem endpoint_8_58_prefix_4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 4 208141947499313143 = some 208141947499313143 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 2 2 208141947499313143 208141947499313143 208141947499313143 endpoint_8_58_window_0 endpoint_8_58_window_2
private theorem endpoint_8_58_window_4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 4 2 208141947499313143 = some 208141947499313143 := by decide +kernel
private theorem endpoint_8_58_prefix_6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 6 208141947499313143 = some 208141947499313143 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 4 2 208141947499313143 208141947499313143 208141947499313143 endpoint_8_58_prefix_4 endpoint_8_58_window_4
private theorem endpoint_8_58_window_6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 6 1 208141947499313143 = some 208141947499313143 := by decide +kernel
private theorem endpoint_8_58_prefix_7 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 7 208141947499313143 = some 208141947499313143 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 6 1 208141947499313143 208141947499313143 208141947499313143 endpoint_8_58_prefix_6 endpoint_8_58_window_6

def endpoint_8_58 : CertifiedEndpoint :=
  ⟨⟨8, 58, 3310⟩, 208141947499313143, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_58_flag endpoint_8_58_sources 7 208141947499313143 208141947499313143 rfl endpoint_8_58_base endpoint_8_58_prefix_7) (by decide)⟩
private def endpoint_8_59_flag : Flag := ⟨8, 59, 3272⟩
private def endpoint_8_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_59_base : receiptBase endpoint_8_59_flag endpoint_8_59_sources = some 208893928829690438 := by decide +kernel
private theorem endpoint_8_59_window_0 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 2 208893928829690438 = some 208893928829690438 := by decide +kernel
private theorem endpoint_8_59_window_2 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 2 2 208893928829690438 = some 208893928829690438 := by decide +kernel
private theorem endpoint_8_59_prefix_4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 4 208893928829690438 = some 208893928829690438 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 2 2 208893928829690438 208893928829690438 208893928829690438 endpoint_8_59_window_0 endpoint_8_59_window_2
private theorem endpoint_8_59_window_4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 4 2 208893928829690438 = some 208893928829690438 := by decide +kernel
private theorem endpoint_8_59_prefix_6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 6 208893928829690438 = some 208893928829690438 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 4 2 208893928829690438 208893928829690438 208893928829690438 endpoint_8_59_prefix_4 endpoint_8_59_window_4
private theorem endpoint_8_59_window_6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 6 1 208893928829690438 = some 208893928829690438 := by decide +kernel
private theorem endpoint_8_59_prefix_7 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 7 208893928829690438 = some 208893928829690438 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 6 1 208893928829690438 208893928829690438 208893928829690438 endpoint_8_59_prefix_6 endpoint_8_59_window_6

def endpoint_8_59 : CertifiedEndpoint :=
  ⟨⟨8, 59, 3272⟩, 208893928829690438, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_59_flag endpoint_8_59_sources 7 208893928829690438 208893928829690438 rfl endpoint_8_59_base endpoint_8_59_prefix_7) (by decide)⟩
private def endpoint_8_60_flag : Flag := ⟨8, 60, 3234⟩
private def endpoint_8_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_60_base : receiptBase endpoint_8_60_flag endpoint_8_60_sources = some 209573392868107263 := by decide +kernel
private theorem endpoint_8_60_window_0 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 2 209573392868107263 = some 209573392868107263 := by decide +kernel
private theorem endpoint_8_60_window_2 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 2 2 209573392868107263 = some 209573392868107263 := by decide +kernel
private theorem endpoint_8_60_prefix_4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 4 209573392868107263 = some 209573392868107263 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 2 2 209573392868107263 209573392868107263 209573392868107263 endpoint_8_60_window_0 endpoint_8_60_window_2
private theorem endpoint_8_60_window_4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 4 2 209573392868107263 = some 209573392868107263 := by decide +kernel
private theorem endpoint_8_60_prefix_6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 6 209573392868107263 = some 209573392868107263 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 4 2 209573392868107263 209573392868107263 209573392868107263 endpoint_8_60_prefix_4 endpoint_8_60_window_4
private theorem endpoint_8_60_window_6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 6 1 209573392868107263 = some 209573392868107263 := by decide +kernel
private theorem endpoint_8_60_prefix_7 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 7 209573392868107263 = some 209573392868107263 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 6 1 209573392868107263 209573392868107263 209573392868107263 endpoint_8_60_prefix_6 endpoint_8_60_window_6

def endpoint_8_60 : CertifiedEndpoint :=
  ⟨⟨8, 60, 3234⟩, 209573392868107263, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_60_flag endpoint_8_60_sources 7 209573392868107263 209573392868107263 rfl endpoint_8_60_base endpoint_8_60_prefix_7) (by decide)⟩
private def endpoint_8_61_flag : Flag := ⟨8, 61, 3193⟩
private def endpoint_8_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_61_base : receiptBase endpoint_8_61_flag endpoint_8_61_sources = some 212074870372819803 := by decide +kernel
private theorem endpoint_8_61_window_0 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 2 212074870372819803 = some 212074870372819803 := by decide +kernel
private theorem endpoint_8_61_window_2 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 2 2 212074870372819803 = some 212074870372819803 := by decide +kernel
private theorem endpoint_8_61_prefix_4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 4 212074870372819803 = some 212074870372819803 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 2 2 212074870372819803 212074870372819803 212074870372819803 endpoint_8_61_window_0 endpoint_8_61_window_2
private theorem endpoint_8_61_window_4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 4 2 212074870372819803 = some 212074870372819803 := by decide +kernel
private theorem endpoint_8_61_prefix_6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 6 212074870372819803 = some 212074870372819803 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 4 2 212074870372819803 212074870372819803 212074870372819803 endpoint_8_61_prefix_4 endpoint_8_61_window_4
private theorem endpoint_8_61_window_6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 6 1 212074870372819803 = some 212074870372819803 := by decide +kernel
private theorem endpoint_8_61_prefix_7 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 7 212074870372819803 = some 212074870372819803 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 6 1 212074870372819803 212074870372819803 212074870372819803 endpoint_8_61_prefix_6 endpoint_8_61_window_6

def endpoint_8_61 : CertifiedEndpoint :=
  ⟨⟨8, 61, 3193⟩, 212074870372819803, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_61_flag endpoint_8_61_sources 7 212074870372819803 212074870372819803 rfl endpoint_8_61_base endpoint_8_61_prefix_7) (by decide)⟩
private def endpoint_8_62_flag : Flag := ⟨8, 62, 3151⟩
private def endpoint_8_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_62_base : receiptBase endpoint_8_62_flag endpoint_8_62_sources = some 212325556688037799 := by decide +kernel
private theorem endpoint_8_62_window_0 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 2 212325556688037799 = some 212325556688037799 := by decide +kernel
private theorem endpoint_8_62_window_2 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 2 2 212325556688037799 = some 212325556688037799 := by decide +kernel
private theorem endpoint_8_62_prefix_4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 4 212325556688037799 = some 212325556688037799 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 2 2 212325556688037799 212325556688037799 212325556688037799 endpoint_8_62_window_0 endpoint_8_62_window_2
private theorem endpoint_8_62_window_4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 4 2 212325556688037799 = some 212325556688037799 := by decide +kernel
private theorem endpoint_8_62_prefix_6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 6 212325556688037799 = some 212325556688037799 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 4 2 212325556688037799 212325556688037799 212325556688037799 endpoint_8_62_prefix_4 endpoint_8_62_window_4
private theorem endpoint_8_62_window_6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 6 1 212325556688037799 = some 212325556688037799 := by decide +kernel
private theorem endpoint_8_62_prefix_7 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 7 212325556688037799 = some 212325556688037799 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 6 1 212325556688037799 212325556688037799 212325556688037799 endpoint_8_62_prefix_6 endpoint_8_62_window_6

def endpoint_8_62 : CertifiedEndpoint :=
  ⟨⟨8, 62, 3151⟩, 212325556688037799, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_62_flag endpoint_8_62_sources 7 212325556688037799 212325556688037799 rfl endpoint_8_62_base endpoint_8_62_prefix_7) (by decide)⟩
private def endpoint_8_63_flag : Flag := ⟨8, 63, 3107⟩
private def endpoint_8_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_63_base : receiptBase endpoint_8_63_flag endpoint_8_63_sources = some 212360207479407271 := by decide +kernel
private theorem endpoint_8_63_window_0 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 2 212360207479407271 = some 212360207479407271 := by decide +kernel
private theorem endpoint_8_63_window_2 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 2 2 212360207479407271 = some 212360207479407271 := by decide +kernel
private theorem endpoint_8_63_prefix_4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 4 212360207479407271 = some 212360207479407271 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 2 2 212360207479407271 212360207479407271 212360207479407271 endpoint_8_63_window_0 endpoint_8_63_window_2
private theorem endpoint_8_63_window_4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 4 2 212360207479407271 = some 212360207479407271 := by decide +kernel
private theorem endpoint_8_63_prefix_6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 6 212360207479407271 = some 212360207479407271 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 4 2 212360207479407271 212360207479407271 212360207479407271 endpoint_8_63_prefix_4 endpoint_8_63_window_4
private theorem endpoint_8_63_window_6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 6 1 212360207479407271 = some 212360207479407271 := by decide +kernel
private theorem endpoint_8_63_prefix_7 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 7 212360207479407271 = some 212360207479407271 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 6 1 212360207479407271 212360207479407271 212360207479407271 endpoint_8_63_prefix_6 endpoint_8_63_window_6

def endpoint_8_63 : CertifiedEndpoint :=
  ⟨⟨8, 63, 3107⟩, 212360207479407271, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_63_flag endpoint_8_63_sources 7 212360207479407271 212360207479407271 rfl endpoint_8_63_base endpoint_8_63_prefix_7) (by decide)⟩
private def endpoint_8_64_flag : Flag := ⟨8, 64, 3061⟩
private def endpoint_8_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_64_base : receiptBase endpoint_8_64_flag endpoint_8_64_sources = some 212173118076377848 := by decide +kernel
private theorem endpoint_8_64_window_0 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 2 212173118076377848 = some 212173118076377848 := by decide +kernel
private theorem endpoint_8_64_window_2 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 2 2 212173118076377848 = some 212173118076377848 := by decide +kernel
private theorem endpoint_8_64_prefix_4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 4 212173118076377848 = some 212173118076377848 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 2 2 212173118076377848 212173118076377848 212173118076377848 endpoint_8_64_window_0 endpoint_8_64_window_2
private theorem endpoint_8_64_window_4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 4 2 212173118076377848 = some 212173118076377848 := by decide +kernel
private theorem endpoint_8_64_prefix_6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 6 212173118076377848 = some 212173118076377848 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 4 2 212173118076377848 212173118076377848 212173118076377848 endpoint_8_64_prefix_4 endpoint_8_64_window_4
private theorem endpoint_8_64_window_6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 6 1 212173118076377848 = some 212173118076377848 := by decide +kernel
private theorem endpoint_8_64_prefix_7 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 7 212173118076377848 = some 212173118076377848 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 6 1 212173118076377848 212173118076377848 212173118076377848 endpoint_8_64_prefix_6 endpoint_8_64_window_6

def endpoint_8_64 : CertifiedEndpoint :=
  ⟨⟨8, 64, 3061⟩, 212173118076377848, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_64_flag endpoint_8_64_sources 7 212173118076377848 212173118076377848 rfl endpoint_8_64_base endpoint_8_64_prefix_7) (by decide)⟩
private def endpoint_8_65_flag : Flag := ⟨8, 65, 3013⟩
private def endpoint_8_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_65_base : receiptBase endpoint_8_65_flag endpoint_8_65_sources = some 213111685604637459 := by decide +kernel
private theorem endpoint_8_65_window_0 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 2 213111685604637459 = some 213111685604637459 := by decide +kernel
private theorem endpoint_8_65_window_2 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 2 2 213111685604637459 = some 213111685604637459 := by decide +kernel
private theorem endpoint_8_65_prefix_4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 4 213111685604637459 = some 213111685604637459 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 2 2 213111685604637459 213111685604637459 213111685604637459 endpoint_8_65_window_0 endpoint_8_65_window_2
private theorem endpoint_8_65_window_4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 4 2 213111685604637459 = some 213111685604637459 := by decide +kernel
private theorem endpoint_8_65_prefix_6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 6 213111685604637459 = some 213111685604637459 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 4 2 213111685604637459 213111685604637459 213111685604637459 endpoint_8_65_prefix_4 endpoint_8_65_window_4
private theorem endpoint_8_65_window_6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 6 1 213111685604637459 = some 213111685604637459 := by decide +kernel
private theorem endpoint_8_65_prefix_7 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 7 213111685604637459 = some 213111685604637459 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 6 1 213111685604637459 213111685604637459 213111685604637459 endpoint_8_65_prefix_6 endpoint_8_65_window_6

def endpoint_8_65 : CertifiedEndpoint :=
  ⟨⟨8, 65, 3013⟩, 213111685604637459, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_65_flag endpoint_8_65_sources 7 213111685604637459 213111685604637459 rfl endpoint_8_65_base endpoint_8_65_prefix_7) (by decide)⟩
private def endpoint_8_66_flag : Flag := ⟨8, 66, 2962⟩
private def endpoint_8_66_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_66_base : receiptBase endpoint_8_66_flag endpoint_8_66_sources = some 212390695502859941 := by decide +kernel
private theorem endpoint_8_66_window_0 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 2 212390695502859941 = some 212390695502859941 := by decide +kernel
private theorem endpoint_8_66_window_2 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 2 2 212390695502859941 = some 212390695502859941 := by decide +kernel
private theorem endpoint_8_66_prefix_4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 4 212390695502859941 = some 212390695502859941 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 2 2 212390695502859941 212390695502859941 212390695502859941 endpoint_8_66_window_0 endpoint_8_66_window_2
private theorem endpoint_8_66_window_4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 4 2 212390695502859941 = some 212390695502859941 := by decide +kernel
private theorem endpoint_8_66_prefix_6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 6 212390695502859941 = some 212390695502859941 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 4 2 212390695502859941 212390695502859941 212390695502859941 endpoint_8_66_prefix_4 endpoint_8_66_window_4
private theorem endpoint_8_66_window_6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 6 1 212390695502859941 = some 212390695502859941 := by decide +kernel
private theorem endpoint_8_66_prefix_7 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 7 212390695502859941 = some 212390695502859941 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 6 1 212390695502859941 212390695502859941 212390695502859941 endpoint_8_66_prefix_6 endpoint_8_66_window_6

def endpoint_8_66 : CertifiedEndpoint :=
  ⟨⟨8, 66, 2962⟩, 212390695502859941, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_66_flag endpoint_8_66_sources 7 212390695502859941 212390695502859941 rfl endpoint_8_66_base endpoint_8_66_prefix_7) (by decide)⟩
private def endpoint_8_67_flag : Flag := ⟨8, 67, 2909⟩
private def endpoint_8_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_67_base : receiptBase endpoint_8_67_flag endpoint_8_67_sources = some 211426967021782745 := by decide +kernel
private theorem endpoint_8_67_window_0 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 2 211426967021782745 = some 211426967021782745 := by decide +kernel
private theorem endpoint_8_67_window_2 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 2 2 211426967021782745 = some 211426967021782745 := by decide +kernel
private theorem endpoint_8_67_prefix_4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 4 211426967021782745 = some 211426967021782745 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 2 2 211426967021782745 211426967021782745 211426967021782745 endpoint_8_67_window_0 endpoint_8_67_window_2
private theorem endpoint_8_67_window_4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 4 2 211426967021782745 = some 211426967021782745 := by decide +kernel
private theorem endpoint_8_67_prefix_6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 6 211426967021782745 = some 211426967021782745 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 4 2 211426967021782745 211426967021782745 211426967021782745 endpoint_8_67_prefix_4 endpoint_8_67_window_4
private theorem endpoint_8_67_window_6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 6 1 211426967021782745 = some 211426967021782745 := by decide +kernel
private theorem endpoint_8_67_prefix_7 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 7 211426967021782745 = some 211426967021782745 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 6 1 211426967021782745 211426967021782745 211426967021782745 endpoint_8_67_prefix_6 endpoint_8_67_window_6

def endpoint_8_67 : CertifiedEndpoint :=
  ⟨⟨8, 67, 2909⟩, 211426967021782745, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_67_flag endpoint_8_67_sources 7 211426967021782745 211426967021782745 rfl endpoint_8_67_base endpoint_8_67_prefix_7) (by decide)⟩
private def endpoint_8_68_flag : Flag := ⟨8, 68, 2852⟩
private def endpoint_8_68_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_68_base : receiptBase endpoint_8_68_flag endpoint_8_68_sources = some 211455524574666971 := by decide +kernel
private theorem endpoint_8_68_window_0 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 2 211455524574666971 = some 211455524574666971 := by decide +kernel
private theorem endpoint_8_68_window_2 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 2 2 211455524574666971 = some 211455524574666971 := by decide +kernel
private theorem endpoint_8_68_prefix_4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 4 211455524574666971 = some 211455524574666971 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 2 2 211455524574666971 211455524574666971 211455524574666971 endpoint_8_68_window_0 endpoint_8_68_window_2
private theorem endpoint_8_68_window_4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 4 2 211455524574666971 = some 211455524574666971 := by decide +kernel
private theorem endpoint_8_68_prefix_6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 6 211455524574666971 = some 211455524574666971 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 4 2 211455524574666971 211455524574666971 211455524574666971 endpoint_8_68_prefix_4 endpoint_8_68_window_4
private theorem endpoint_8_68_window_6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 6 1 211455524574666971 = some 211455524574666971 := by decide +kernel
private theorem endpoint_8_68_prefix_7 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 7 211455524574666971 = some 211455524574666971 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 6 1 211455524574666971 211455524574666971 211455524574666971 endpoint_8_68_prefix_6 endpoint_8_68_window_6

def endpoint_8_68 : CertifiedEndpoint :=
  ⟨⟨8, 68, 2852⟩, 211455524574666971, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_68_flag endpoint_8_68_sources 7 211455524574666971 211455524574666971 rfl endpoint_8_68_base endpoint_8_68_prefix_7) (by decide)⟩
private def endpoint_8_69_flag : Flag := ⟨8, 69, 2794⟩
private def endpoint_8_69_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_69_base : receiptBase endpoint_8_69_flag endpoint_8_69_sources = some 209904573899675139 := by decide +kernel
private theorem endpoint_8_69_window_0 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 2 209904573899675139 = some 209904573899675139 := by decide +kernel
private theorem endpoint_8_69_window_2 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 2 2 209904573899675139 = some 209904573899675139 := by decide +kernel
private theorem endpoint_8_69_prefix_4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 4 209904573899675139 = some 209904573899675139 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 2 2 209904573899675139 209904573899675139 209904573899675139 endpoint_8_69_window_0 endpoint_8_69_window_2
private theorem endpoint_8_69_window_4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 4 2 209904573899675139 = some 209904573899675139 := by decide +kernel
private theorem endpoint_8_69_prefix_6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 6 209904573899675139 = some 209904573899675139 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 4 2 209904573899675139 209904573899675139 209904573899675139 endpoint_8_69_prefix_4 endpoint_8_69_window_4
private theorem endpoint_8_69_window_6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 6 1 209904573899675139 = some 209904573899675139 := by decide +kernel
private theorem endpoint_8_69_prefix_7 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 7 209904573899675139 = some 209904573899675139 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 6 1 209904573899675139 209904573899675139 209904573899675139 endpoint_8_69_prefix_6 endpoint_8_69_window_6

def endpoint_8_69 : CertifiedEndpoint :=
  ⟨⟨8, 69, 2794⟩, 209904573899675139, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_69_flag endpoint_8_69_sources 7 209904573899675139 209904573899675139 rfl endpoint_8_69_base endpoint_8_69_prefix_7) (by decide)⟩
private def endpoint_8_70_flag : Flag := ⟨8, 70, 2732⟩
private def endpoint_8_70_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_8_70_base : receiptBase endpoint_8_70_flag endpoint_8_70_sources = some 209346630526950275 := by decide +kernel
private theorem endpoint_8_70_window_0 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 2 209346630526950275 = some 209346630526950275 := by decide +kernel
private theorem endpoint_8_70_window_2 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 2 2 209346630526950275 = some 209346630526950275 := by decide +kernel
private theorem endpoint_8_70_prefix_4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 4 209346630526950275 = some 209346630526950275 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 2 2 209346630526950275 209346630526950275 209346630526950275 endpoint_8_70_window_0 endpoint_8_70_window_2
private theorem endpoint_8_70_window_4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 4 2 209346630526950275 = some 209346630526950275 := by decide +kernel
private theorem endpoint_8_70_prefix_6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 6 209346630526950275 = some 209346630526950275 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 4 2 209346630526950275 209346630526950275 209346630526950275 endpoint_8_70_prefix_4 endpoint_8_70_window_4
private theorem endpoint_8_70_window_6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 6 1 209346630526950275 = some 209346630526950275 := by decide +kernel
private theorem endpoint_8_70_prefix_7 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 7 209346630526950275 = some 209346630526950275 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 6 1 209346630526950275 209346630526950275 209346630526950275 endpoint_8_70_prefix_6 endpoint_8_70_window_6

def endpoint_8_70 : CertifiedEndpoint :=
  ⟨⟨8, 70, 2732⟩, 209346630526950275, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_8_70_flag endpoint_8_70_sources 7 209346630526950275 209346630526950275 rfl endpoint_8_70_base endpoint_8_70_prefix_7) (by decide)⟩
private def endpoint_8_71_flag : Flag := ⟨8, 71, 2668⟩
private def endpoint_8_71_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_8_71_base : receiptBase endpoint_8_71_flag endpoint_8_71_sources = some 208519235336179473 := by decide +kernel
private theorem endpoint_8_71_window_0 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 2 208519235336179473 = some 208519235336179473 := by decide +kernel
private theorem endpoint_8_71_window_2 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 2 2 208519235336179473 = some 208519235336179473 := by decide +kernel
private theorem endpoint_8_71_prefix_4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 4 208519235336179473 = some 208519235336179473 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 2 2 208519235336179473 208519235336179473 208519235336179473 endpoint_8_71_window_0 endpoint_8_71_window_2
private theorem endpoint_8_71_window_4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 4 2 208519235336179473 = some 208519235336179473 := by decide +kernel
private theorem endpoint_8_71_prefix_6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 6 208519235336179473 = some 208519235336179473 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 4 2 208519235336179473 208519235336179473 208519235336179473 endpoint_8_71_prefix_4 endpoint_8_71_window_4
private theorem endpoint_8_71_window_6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 6 1 208519235336179473 = some 208519235336179473 := by decide +kernel
private theorem endpoint_8_71_prefix_7 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 7 208519235336179473 = some 208519235336179473 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 6 1 208519235336179473 208519235336179473 208519235336179473 endpoint_8_71_prefix_6 endpoint_8_71_window_6

def endpoint_8_71 : CertifiedEndpoint :=
  ⟨⟨8, 71, 2668⟩, 208519235336179473, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_8_71_flag endpoint_8_71_sources 7 208519235336179473 208519235336179473 rfl endpoint_8_71_base endpoint_8_71_prefix_7) (by decide)⟩
private def endpoint_8_72_flag : Flag := ⟨8, 72, 2601⟩
private def endpoint_8_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_72_base : receiptBase endpoint_8_72_flag endpoint_8_72_sources = some 207201741709547811 := by decide +kernel
private theorem endpoint_8_72_window_0 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 2 207201741709547811 = some 207201741709547811 := by decide +kernel
private theorem endpoint_8_72_window_2 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 2 2 207201741709547811 = some 207201741709547811 := by decide +kernel
private theorem endpoint_8_72_prefix_4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 4 207201741709547811 = some 207201741709547811 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 2 2 207201741709547811 207201741709547811 207201741709547811 endpoint_8_72_window_0 endpoint_8_72_window_2
private theorem endpoint_8_72_window_4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 4 2 207201741709547811 = some 207201741709547811 := by decide +kernel
private theorem endpoint_8_72_prefix_6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 6 207201741709547811 = some 207201741709547811 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 4 2 207201741709547811 207201741709547811 207201741709547811 endpoint_8_72_prefix_4 endpoint_8_72_window_4
private theorem endpoint_8_72_window_6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 6 1 207201741709547811 = some 207201741709547811 := by decide +kernel
private theorem endpoint_8_72_prefix_7 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 7 207201741709547811 = some 207201741709547811 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 6 1 207201741709547811 207201741709547811 207201741709547811 endpoint_8_72_prefix_6 endpoint_8_72_window_6

def endpoint_8_72 : CertifiedEndpoint :=
  ⟨⟨8, 72, 2601⟩, 207201741709547811, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_72_flag endpoint_8_72_sources 7 207201741709547811 207201741709547811 rfl endpoint_8_72_base endpoint_8_72_prefix_7) (by decide)⟩
private def endpoint_8_73_flag : Flag := ⟨8, 73, 2531⟩
private def endpoint_8_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_73_base : receiptBase endpoint_8_73_flag endpoint_8_73_sources = some 204180979199306154 := by decide +kernel
private theorem endpoint_8_73_window_0 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 2 204180979199306154 = some 204180979199306154 := by decide +kernel
private theorem endpoint_8_73_window_2 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 2 2 204180979199306154 = some 204180979199306154 := by decide +kernel
private theorem endpoint_8_73_prefix_4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 4 204180979199306154 = some 204180979199306154 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 2 2 204180979199306154 204180979199306154 204180979199306154 endpoint_8_73_window_0 endpoint_8_73_window_2
private theorem endpoint_8_73_window_4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 4 2 204180979199306154 = some 204180979199306154 := by decide +kernel
private theorem endpoint_8_73_prefix_6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 6 204180979199306154 = some 204180979199306154 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 4 2 204180979199306154 204180979199306154 204180979199306154 endpoint_8_73_prefix_4 endpoint_8_73_window_4
private theorem endpoint_8_73_window_6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 6 1 204180979199306154 = some 204180979199306154 := by decide +kernel
private theorem endpoint_8_73_prefix_7 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 7 204180979199306154 = some 204180979199306154 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 6 1 204180979199306154 204180979199306154 204180979199306154 endpoint_8_73_prefix_6 endpoint_8_73_window_6

def endpoint_8_73 : CertifiedEndpoint :=
  ⟨⟨8, 73, 2531⟩, 204180979199306154, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_73_flag endpoint_8_73_sources 7 204180979199306154 204180979199306154 rfl endpoint_8_73_base endpoint_8_73_prefix_7) (by decide)⟩
private def endpoint_8_74_flag : Flag := ⟨8, 74, 2459⟩
private def endpoint_8_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_74_base : receiptBase endpoint_8_74_flag endpoint_8_74_sources = some 200857768028667127 := by decide +kernel
private theorem endpoint_8_74_window_0 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 2 200857768028667127 = some 200857768028667127 := by decide +kernel
private theorem endpoint_8_74_window_2 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 2 2 200857768028667127 = some 200857768028667127 := by decide +kernel
private theorem endpoint_8_74_prefix_4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 4 200857768028667127 = some 200857768028667127 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 2 2 200857768028667127 200857768028667127 200857768028667127 endpoint_8_74_window_0 endpoint_8_74_window_2
private theorem endpoint_8_74_window_4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 4 2 200857768028667127 = some 200857768028667127 := by decide +kernel
private theorem endpoint_8_74_prefix_6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 6 200857768028667127 = some 200857768028667127 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 4 2 200857768028667127 200857768028667127 200857768028667127 endpoint_8_74_prefix_4 endpoint_8_74_window_4
private theorem endpoint_8_74_window_6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 6 1 200857768028667127 = some 200857768028667127 := by decide +kernel
private theorem endpoint_8_74_prefix_7 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 7 200857768028667127 = some 200857768028667127 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 6 1 200857768028667127 200857768028667127 200857768028667127 endpoint_8_74_prefix_6 endpoint_8_74_window_6

def endpoint_8_74 : CertifiedEndpoint :=
  ⟨⟨8, 74, 2459⟩, 200857768028667127, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_74_flag endpoint_8_74_sources 7 200857768028667127 200857768028667127 rfl endpoint_8_74_base endpoint_8_74_prefix_7) (by decide)⟩
private def endpoint_8_75_flag : Flag := ⟨8, 75, 2384⟩
private def endpoint_8_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_75_base : receiptBase endpoint_8_75_flag endpoint_8_75_sources = some 201105618730753110 := by decide +kernel
private theorem endpoint_8_75_window_0 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 2 201105618730753110 = some 201105618730753110 := by decide +kernel
private theorem endpoint_8_75_window_2 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 2 2 201105618730753110 = some 201105618730753110 := by decide +kernel
private theorem endpoint_8_75_prefix_4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 4 201105618730753110 = some 201105618730753110 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 2 2 201105618730753110 201105618730753110 201105618730753110 endpoint_8_75_window_0 endpoint_8_75_window_2
private theorem endpoint_8_75_window_4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 4 2 201105618730753110 = some 201105618730753110 := by decide +kernel
private theorem endpoint_8_75_prefix_6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 6 201105618730753110 = some 201105618730753110 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 4 2 201105618730753110 201105618730753110 201105618730753110 endpoint_8_75_prefix_4 endpoint_8_75_window_4
private theorem endpoint_8_75_window_6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 6 1 201105618730753110 = some 201105618730753110 := by decide +kernel
private theorem endpoint_8_75_prefix_7 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 7 201105618730753110 = some 201105618730753110 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 6 1 201105618730753110 201105618730753110 201105618730753110 endpoint_8_75_prefix_6 endpoint_8_75_window_6

def endpoint_8_75 : CertifiedEndpoint :=
  ⟨⟨8, 75, 2384⟩, 201105618730753110, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_75_flag endpoint_8_75_sources 7 201105618730753110 201105618730753110 rfl endpoint_8_75_base endpoint_8_75_prefix_7) (by decide)⟩
private def endpoint_8_76_flag : Flag := ⟨8, 76, 2306⟩
private def endpoint_8_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_76_base : receiptBase endpoint_8_76_flag endpoint_8_76_sources = some 196957967169370009 := by decide +kernel
private theorem endpoint_8_76_window_0 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 2 196957967169370009 = some 196957967169370009 := by decide +kernel
private theorem endpoint_8_76_window_2 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 2 2 196957967169370009 = some 196957967169370009 := by decide +kernel
private theorem endpoint_8_76_prefix_4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 4 196957967169370009 = some 196957967169370009 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 2 2 196957967169370009 196957967169370009 196957967169370009 endpoint_8_76_window_0 endpoint_8_76_window_2
private theorem endpoint_8_76_window_4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 4 2 196957967169370009 = some 196957967169370009 := by decide +kernel
private theorem endpoint_8_76_prefix_6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 6 196957967169370009 = some 196957967169370009 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 4 2 196957967169370009 196957967169370009 196957967169370009 endpoint_8_76_prefix_4 endpoint_8_76_window_4
private theorem endpoint_8_76_window_6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 6 1 196957967169370009 = some 196957967169370009 := by decide +kernel
private theorem endpoint_8_76_prefix_7 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 7 196957967169370009 = some 196957967169370009 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 6 1 196957967169370009 196957967169370009 196957967169370009 endpoint_8_76_prefix_6 endpoint_8_76_window_6

def endpoint_8_76 : CertifiedEndpoint :=
  ⟨⟨8, 76, 2306⟩, 196957967169370009, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_76_flag endpoint_8_76_sources 7 196957967169370009 196957967169370009 rfl endpoint_8_76_base endpoint_8_76_prefix_7) (by decide)⟩
private def endpoint_8_77_flag : Flag := ⟨8, 77, 2226⟩
private def endpoint_8_77_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_8_77_base : receiptBase endpoint_8_77_flag endpoint_8_77_sources = some 192477357487306460 := by decide +kernel
private theorem endpoint_8_77_window_0 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 2 192477357487306460 = some 192477357487306460 := by decide +kernel
private theorem endpoint_8_77_window_2 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 2 2 192477357487306460 = some 192477357487306460 := by decide +kernel
private theorem endpoint_8_77_prefix_4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 4 192477357487306460 = some 192477357487306460 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 2 2 192477357487306460 192477357487306460 192477357487306460 endpoint_8_77_window_0 endpoint_8_77_window_2
private theorem endpoint_8_77_window_4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 4 2 192477357487306460 = some 192477357487306460 := by decide +kernel
private theorem endpoint_8_77_prefix_6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 6 192477357487306460 = some 192477357487306460 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 4 2 192477357487306460 192477357487306460 192477357487306460 endpoint_8_77_prefix_4 endpoint_8_77_window_4
private theorem endpoint_8_77_window_6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 6 1 192477357487306460 = some 192477357487306460 := by decide +kernel
private theorem endpoint_8_77_prefix_7 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 7 192477357487306460 = some 192477357487306460 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 6 1 192477357487306460 192477357487306460 192477357487306460 endpoint_8_77_prefix_6 endpoint_8_77_window_6

def endpoint_8_77 : CertifiedEndpoint :=
  ⟨⟨8, 77, 2226⟩, 192477357487306460, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_8_77_flag endpoint_8_77_sources 7 192477357487306460 192477357487306460 rfl endpoint_8_77_base endpoint_8_77_prefix_7) (by decide)⟩
private def endpoint_8_78_flag : Flag := ⟨8, 78, 2143⟩
private def endpoint_8_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_78_base : receiptBase endpoint_8_78_flag endpoint_8_78_sources = some 189394452507632625 := by decide +kernel
private theorem endpoint_8_78_window_0 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 2 189394452507632625 = some 189394452507632625 := by decide +kernel
private theorem endpoint_8_78_window_2 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 2 2 189394452507632625 = some 189394452507632625 := by decide +kernel
private theorem endpoint_8_78_prefix_4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 4 189394452507632625 = some 189394452507632625 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 2 2 189394452507632625 189394452507632625 189394452507632625 endpoint_8_78_window_0 endpoint_8_78_window_2
private theorem endpoint_8_78_window_4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 4 2 189394452507632625 = some 189394452507632625 := by decide +kernel
private theorem endpoint_8_78_prefix_6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 6 189394452507632625 = some 189394452507632625 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 4 2 189394452507632625 189394452507632625 189394452507632625 endpoint_8_78_prefix_4 endpoint_8_78_window_4
private theorem endpoint_8_78_window_6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 6 1 189394452507632625 = some 189394452507632625 := by decide +kernel
private theorem endpoint_8_78_prefix_7 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 7 189394452507632625 = some 189394452507632625 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 6 1 189394452507632625 189394452507632625 189394452507632625 endpoint_8_78_prefix_6 endpoint_8_78_window_6

def endpoint_8_78 : CertifiedEndpoint :=
  ⟨⟨8, 78, 2143⟩, 189394452507632625, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_78_flag endpoint_8_78_sources 7 189394452507632625 189394452507632625 rfl endpoint_8_78_base endpoint_8_78_prefix_7) (by decide)⟩
private def endpoint_8_79_flag : Flag := ⟨8, 79, 2057⟩
private def endpoint_8_79_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_79_base : receiptBase endpoint_8_79_flag endpoint_8_79_sources = some 183951106204070889 := by decide +kernel
private theorem endpoint_8_79_window_0 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 2 183951106204070889 = some 183951106204070889 := by decide +kernel
private theorem endpoint_8_79_window_2 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 2 2 183951106204070889 = some 183951106204070889 := by decide +kernel
private theorem endpoint_8_79_prefix_4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 4 183951106204070889 = some 183951106204070889 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 2 2 183951106204070889 183951106204070889 183951106204070889 endpoint_8_79_window_0 endpoint_8_79_window_2
private theorem endpoint_8_79_window_4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 4 2 183951106204070889 = some 183951106204070889 := by decide +kernel
private theorem endpoint_8_79_prefix_6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 6 183951106204070889 = some 183951106204070889 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 4 2 183951106204070889 183951106204070889 183951106204070889 endpoint_8_79_prefix_4 endpoint_8_79_window_4
private theorem endpoint_8_79_window_6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 6 1 183951106204070889 = some 183951106204070889 := by decide +kernel
private theorem endpoint_8_79_prefix_7 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 7 183951106204070889 = some 183951106204070889 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 6 1 183951106204070889 183951106204070889 183951106204070889 endpoint_8_79_prefix_6 endpoint_8_79_window_6

def endpoint_8_79 : CertifiedEndpoint :=
  ⟨⟨8, 79, 2057⟩, 183951106204070889, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_79_flag endpoint_8_79_sources 7 183951106204070889 183951106204070889 rfl endpoint_8_79_base endpoint_8_79_prefix_7) (by decide)⟩
private def endpoint_8_80_flag : Flag := ⟨8, 80, 1968⟩
private def endpoint_8_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_80_base : receiptBase endpoint_8_80_flag endpoint_8_80_sources = some 178063967533649746 := by decide +kernel
private theorem endpoint_8_80_window_0 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 2 178063967533649746 = some 178063967533649746 := by decide +kernel
private theorem endpoint_8_80_window_2 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 2 2 178063967533649746 = some 178063967533649746 := by decide +kernel
private theorem endpoint_8_80_prefix_4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 4 178063967533649746 = some 178063967533649746 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 2 2 178063967533649746 178063967533649746 178063967533649746 endpoint_8_80_window_0 endpoint_8_80_window_2
private theorem endpoint_8_80_window_4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 4 2 178063967533649746 = some 178063967533649746 := by decide +kernel
private theorem endpoint_8_80_prefix_6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 6 178063967533649746 = some 178063967533649746 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 4 2 178063967533649746 178063967533649746 178063967533649746 endpoint_8_80_prefix_4 endpoint_8_80_window_4
private theorem endpoint_8_80_window_6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 6 1 178063967533649746 = some 178063967533649746 := by decide +kernel
private theorem endpoint_8_80_prefix_7 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 7 178063967533649746 = some 178063967533649746 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 6 1 178063967533649746 178063967533649746 178063967533649746 endpoint_8_80_prefix_6 endpoint_8_80_window_6

def endpoint_8_80 : CertifiedEndpoint :=
  ⟨⟨8, 80, 1968⟩, 178063967533649746, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_80_flag endpoint_8_80_sources 7 178063967533649746 178063967533649746 rfl endpoint_8_80_base endpoint_8_80_prefix_7) (by decide)⟩
private def endpoint_8_81_flag : Flag := ⟨8, 81, 1877⟩
private def endpoint_8_81_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_8_81_base : receiptBase endpoint_8_81_flag endpoint_8_81_sources = some 173682948308696559 := by decide +kernel
private theorem endpoint_8_81_window_0 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 2 173682948308696559 = some 173682948308696559 := by decide +kernel
private theorem endpoint_8_81_window_2 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 2 2 173682948308696559 = some 173682948308696559 := by decide +kernel
private theorem endpoint_8_81_prefix_4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 4 173682948308696559 = some 173682948308696559 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 2 2 173682948308696559 173682948308696559 173682948308696559 endpoint_8_81_window_0 endpoint_8_81_window_2
private theorem endpoint_8_81_window_4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 4 2 173682948308696559 = some 173682948308696559 := by decide +kernel
private theorem endpoint_8_81_prefix_6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 6 173682948308696559 = some 173682948308696559 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 4 2 173682948308696559 173682948308696559 173682948308696559 endpoint_8_81_prefix_4 endpoint_8_81_window_4
private theorem endpoint_8_81_window_6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 6 1 173682948308696559 = some 173682948308696559 := by decide +kernel
private theorem endpoint_8_81_prefix_7 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 7 173682948308696559 = some 173682948308696559 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 6 1 173682948308696559 173682948308696559 173682948308696559 endpoint_8_81_prefix_6 endpoint_8_81_window_6

def endpoint_8_81 : CertifiedEndpoint :=
  ⟨⟨8, 81, 1877⟩, 173682948308696559, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_8_81_flag endpoint_8_81_sources 7 173682948308696559 173682948308696559 rfl endpoint_8_81_base endpoint_8_81_prefix_7) (by decide)⟩
private def endpoint_8_82_flag : Flag := ⟨8, 82, 1783⟩
private def endpoint_8_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_82_base : receiptBase endpoint_8_82_flag endpoint_8_82_sources = some 168709421706579654 := by decide +kernel
private theorem endpoint_8_82_window_0 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 2 168709421706579654 = some 168709421706579654 := by decide +kernel
private theorem endpoint_8_82_window_2 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 2 2 168709421706579654 = some 168709421706579654 := by decide +kernel
private theorem endpoint_8_82_prefix_4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 4 168709421706579654 = some 168709421706579654 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 2 2 168709421706579654 168709421706579654 168709421706579654 endpoint_8_82_window_0 endpoint_8_82_window_2
private theorem endpoint_8_82_window_4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 4 2 168709421706579654 = some 168709421706579654 := by decide +kernel
private theorem endpoint_8_82_prefix_6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 6 168709421706579654 = some 168709421706579654 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 4 2 168709421706579654 168709421706579654 168709421706579654 endpoint_8_82_prefix_4 endpoint_8_82_window_4
private theorem endpoint_8_82_window_6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 6 1 168709421706579654 = some 168709421706579654 := by decide +kernel
private theorem endpoint_8_82_prefix_7 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 7 168709421706579654 = some 168709421706579654 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 6 1 168709421706579654 168709421706579654 168709421706579654 endpoint_8_82_prefix_6 endpoint_8_82_window_6

def endpoint_8_82 : CertifiedEndpoint :=
  ⟨⟨8, 82, 1783⟩, 168709421706579654, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_82_flag endpoint_8_82_sources 7 168709421706579654 168709421706579654 rfl endpoint_8_82_base endpoint_8_82_prefix_7) (by decide)⟩
def endpoint_8_83 : CertifiedEndpoint :=
  ⟨⟨8, 83, 1686⟩, 250294485218651283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_84 : CertifiedEndpoint :=
  ⟨⟨8, 84, 1587⟩, 238125098057466265, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_85 : CertifiedEndpoint :=
  ⟨⟨8, 85, 1485⟩, 225100509649607274, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_86 : CertifiedEndpoint :=
  ⟨⟨8, 86, 1380⟩, 211203247625743536, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_87 : CertifiedEndpoint :=
  ⟨⟨8, 87, 1272⟩, 196415839616544277, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_88 : CertifiedEndpoint :=
  ⟨⟨8, 88, 1161⟩, 180720813252678723, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_89 : CertifiedEndpoint :=
  ⟨⟨8, 89, 1048⟩, 164264750911305397, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_90 : CertifiedEndpoint :=
  ⟨⟨8, 90, 932⟩, 146870008225344400, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_91 : CertifiedEndpoint :=
  ⟨⟨8, 91, 814⟩, 128687050320694427, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_92 : CertifiedEndpoint :=
  ⟨⟨8, 92, 692⟩, 109364471211935852, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_93 : CertifiedEndpoint :=
  ⟨⟨8, 93, 568⟩, 89222614894566925, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_94 : CertifiedEndpoint :=
  ⟨⟨8, 94, 441⟩, 68076071504027403, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_95 : CertifiedEndpoint :=
  ⟨⟨8, 95, 311⟩, 45907368670986512, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_96 : CertifiedEndpoint :=
  ⟨⟨8, 96, 179⟩, 22876678393193377, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_9 : CertifiedEndpoint :=
  ⟨⟨9, 9, 4417⟩, 51936281316380670, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_10 : CertifiedEndpoint :=
  ⟨⟨9, 10, 4398⟩, 54840371795864356, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_11 : CertifiedEndpoint :=
  ⟨⟨9, 11, 4380⟩, 57730572014059115, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_12 : CertifiedEndpoint :=
  ⟨⟨9, 12, 4362⟩, 67060008325368726, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_13 : CertifiedEndpoint :=
  ⟨⟨9, 13, 4343⟩, 76290477480173024, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_14 : CertifiedEndpoint :=
  ⟨⟨9, 14, 4324⟩, 85435182565703140, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_15 : CertifiedEndpoint :=
  ⟨⟨9, 15, 4305⟩, 94494123581959074, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_16 : CertifiedEndpoint :=
  ⟨⟨9, 16, 4286⟩, 103467300528940826, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_17 : CertifiedEndpoint :=
  ⟨⟨9, 17, 4267⟩, 112354713406648396, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_18 : CertifiedEndpoint :=
  ⟨⟨9, 18, 4248⟩, 121156362215081784, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_19 : CertifiedEndpoint :=
  ⟨⟨9, 19, 4228⟩, 129841451237415155, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_20 : CertifiedEndpoint :=
  ⟨⟨9, 20, 4208⟩, 138436378033075668, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_21 : CertifiedEndpoint :=
  ⟨⟨9, 21, 4188⟩, 146941142602063323, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_22 : CertifiedEndpoint :=
  ⟨⟨9, 22, 4168⟩, 155355744944378120, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_23 : CertifiedEndpoint :=
  ⟨⟨9, 23, 4148⟩, 163680185060020059, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_24 : CertifiedEndpoint :=
  ⟨⟨9, 24, 4127⟩, 171872671838666615, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_25 : CertifiedEndpoint :=
  ⟨⟨9, 25, 4106⟩, 179970598233241637, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_26 : CertifiedEndpoint :=
  ⟨⟨9, 26, 4085⟩, 187973964243745125, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_27 : CertifiedEndpoint :=
  ⟨⟨9, 27, 4064⟩, 195882769870177079, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_28 : CertifiedEndpoint :=
  ⟨⟨9, 28, 4042⟩, 203646427687417622, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_29 : CertifiedEndpoint :=
  ⟨⟨9, 29, 4020⟩, 211311126963187955, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_30 : CertifiedEndpoint :=
  ⟨⟨9, 30, 3998⟩, 218876867697488078, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_31 : CertifiedEndpoint :=
  ⟨⟨9, 31, 3976⟩, 226343649890317991, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_32 : CertifiedEndpoint :=
  ⟨⟨9, 32, 3953⟩, 233652089801760465, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_33 : CertifiedEndpoint :=
  ⟨⟨9, 33, 3930⟩, 240857173014334053, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_34 : CertifiedEndpoint :=
  ⟨⟨9, 34, 3907⟩, 247958899528038755, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_35 : CertifiedEndpoint :=
  ⟨⟨9, 35, 3883⟩, 254891288366859328, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_9_36_flag : Flag := ⟨9, 36, 3860⟩
private def endpoint_9_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_36_base : receiptBase endpoint_9_36_flag endpoint_9_36_sources = some 172446099135900245 := by decide +kernel
private theorem endpoint_9_36_window_0 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 2 172446099135900245 = some 172446099135900245 := by decide +kernel
private theorem endpoint_9_36_window_2 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 2 2 172446099135900245 = some 172446099135900245 := by decide +kernel
private theorem endpoint_9_36_prefix_4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 4 172446099135900245 = some 172446099135900245 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 2 2 172446099135900245 172446099135900245 172446099135900245 endpoint_9_36_window_0 endpoint_9_36_window_2
private theorem endpoint_9_36_window_4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 4 2 172446099135900245 = some 172446099135900245 := by decide +kernel
private theorem endpoint_9_36_prefix_6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 6 172446099135900245 = some 172446099135900245 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 4 2 172446099135900245 172446099135900245 172446099135900245 endpoint_9_36_prefix_4 endpoint_9_36_window_4
private theorem endpoint_9_36_window_6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 6 2 172446099135900245 = some 172446099135900245 := by decide +kernel
private theorem endpoint_9_36_prefix_8 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 8 172446099135900245 = some 172446099135900245 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 6 2 172446099135900245 172446099135900245 172446099135900245 endpoint_9_36_prefix_6 endpoint_9_36_window_6

def endpoint_9_36 : CertifiedEndpoint :=
  ⟨⟨9, 36, 3860⟩, 172446099135900245, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_36_flag endpoint_9_36_sources 8 172446099135900245 172446099135900245 rfl endpoint_9_36_base endpoint_9_36_prefix_8) (by decide)⟩
private def endpoint_9_37_flag : Flag := ⟨9, 37, 3835⟩
private def endpoint_9_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_37_base : receiptBase endpoint_9_37_flag endpoint_9_37_sources = some 175300874906616631 := by decide +kernel
private theorem endpoint_9_37_window_0 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 2 175300874906616631 = some 175300874906616631 := by decide +kernel
private theorem endpoint_9_37_window_2 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 2 2 175300874906616631 = some 175300874906616631 := by decide +kernel
private theorem endpoint_9_37_prefix_4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 4 175300874906616631 = some 175300874906616631 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 2 2 175300874906616631 175300874906616631 175300874906616631 endpoint_9_37_window_0 endpoint_9_37_window_2
private theorem endpoint_9_37_window_4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 4 2 175300874906616631 = some 175300874906616631 := by decide +kernel
private theorem endpoint_9_37_prefix_6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 6 175300874906616631 = some 175300874906616631 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 4 2 175300874906616631 175300874906616631 175300874906616631 endpoint_9_37_prefix_4 endpoint_9_37_window_4
private theorem endpoint_9_37_window_6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 6 2 175300874906616631 = some 175300874906616631 := by decide +kernel
private theorem endpoint_9_37_prefix_8 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 8 175300874906616631 = some 175300874906616631 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 6 2 175300874906616631 175300874906616631 175300874906616631 endpoint_9_37_prefix_6 endpoint_9_37_window_6

def endpoint_9_37 : CertifiedEndpoint :=
  ⟨⟨9, 37, 3835⟩, 175300874906616631, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_37_flag endpoint_9_37_sources 8 175300874906616631 175300874906616631 rfl endpoint_9_37_base endpoint_9_37_prefix_8) (by decide)⟩
private def endpoint_9_38_flag : Flag := ⟨9, 38, 3811⟩
private def endpoint_9_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_38_base : receiptBase endpoint_9_38_flag endpoint_9_38_sources = some 178149964004055976 := by decide +kernel
private theorem endpoint_9_38_window_0 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 2 178149964004055976 = some 178149964004055976 := by decide +kernel
private theorem endpoint_9_38_window_2 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 2 2 178149964004055976 = some 178149964004055976 := by decide +kernel
private theorem endpoint_9_38_prefix_4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 4 178149964004055976 = some 178149964004055976 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 2 2 178149964004055976 178149964004055976 178149964004055976 endpoint_9_38_window_0 endpoint_9_38_window_2
private theorem endpoint_9_38_window_4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 4 2 178149964004055976 = some 178149964004055976 := by decide +kernel
private theorem endpoint_9_38_prefix_6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 6 178149964004055976 = some 178149964004055976 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 4 2 178149964004055976 178149964004055976 178149964004055976 endpoint_9_38_prefix_4 endpoint_9_38_window_4
private theorem endpoint_9_38_window_6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 6 2 178149964004055976 = some 178149964004055976 := by decide +kernel
private theorem endpoint_9_38_prefix_8 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 8 178149964004055976 = some 178149964004055976 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 6 2 178149964004055976 178149964004055976 178149964004055976 endpoint_9_38_prefix_6 endpoint_9_38_window_6

def endpoint_9_38 : CertifiedEndpoint :=
  ⟨⟨9, 38, 3811⟩, 178149964004055976, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_38_flag endpoint_9_38_sources 8 178149964004055976 178149964004055976 rfl endpoint_9_38_base endpoint_9_38_prefix_8) (by decide)⟩
private def endpoint_9_39_flag : Flag := ⟨9, 39, 3786⟩
private def endpoint_9_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_39_base : receiptBase endpoint_9_39_flag endpoint_9_39_sources = some 180902215534847679 := by decide +kernel
private theorem endpoint_9_39_window_0 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 2 180902215534847679 = some 180902215534847679 := by decide +kernel
private theorem endpoint_9_39_window_2 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 2 2 180902215534847679 = some 180902215534847679 := by decide +kernel
private theorem endpoint_9_39_prefix_4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 4 180902215534847679 = some 180902215534847679 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 2 2 180902215534847679 180902215534847679 180902215534847679 endpoint_9_39_window_0 endpoint_9_39_window_2
private theorem endpoint_9_39_window_4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 4 2 180902215534847679 = some 180902215534847679 := by decide +kernel
private theorem endpoint_9_39_prefix_6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 6 180902215534847679 = some 180902215534847679 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 4 2 180902215534847679 180902215534847679 180902215534847679 endpoint_9_39_prefix_4 endpoint_9_39_window_4
private theorem endpoint_9_39_window_6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 6 2 180902215534847679 = some 180902215534847679 := by decide +kernel
private theorem endpoint_9_39_prefix_8 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 8 180902215534847679 = some 180902215534847679 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 6 2 180902215534847679 180902215534847679 180902215534847679 endpoint_9_39_prefix_6 endpoint_9_39_window_6

def endpoint_9_39 : CertifiedEndpoint :=
  ⟨⟨9, 39, 3786⟩, 180902215534847679, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_39_flag endpoint_9_39_sources 8 180902215534847679 180902215534847679 rfl endpoint_9_39_base endpoint_9_39_prefix_8) (by decide)⟩
private def endpoint_9_40_flag : Flag := ⟨9, 40, 3761⟩
private def endpoint_9_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_40_base : receiptBase endpoint_9_40_flag endpoint_9_40_sources = some 183602697444485384 := by decide +kernel
private theorem endpoint_9_40_window_0 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 2 183602697444485384 = some 183602697444485384 := by decide +kernel
private theorem endpoint_9_40_window_2 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 2 2 183602697444485384 = some 183602697444485384 := by decide +kernel
private theorem endpoint_9_40_prefix_4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 4 183602697444485384 = some 183602697444485384 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 2 2 183602697444485384 183602697444485384 183602697444485384 endpoint_9_40_window_0 endpoint_9_40_window_2
private theorem endpoint_9_40_window_4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 4 2 183602697444485384 = some 183602697444485384 := by decide +kernel
private theorem endpoint_9_40_prefix_6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 6 183602697444485384 = some 183602697444485384 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 4 2 183602697444485384 183602697444485384 183602697444485384 endpoint_9_40_prefix_4 endpoint_9_40_window_4
private theorem endpoint_9_40_window_6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 6 2 183602697444485384 = some 183602697444485384 := by decide +kernel
private theorem endpoint_9_40_prefix_8 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 8 183602697444485384 = some 183602697444485384 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 6 2 183602697444485384 183602697444485384 183602697444485384 endpoint_9_40_prefix_6 endpoint_9_40_window_6

def endpoint_9_40 : CertifiedEndpoint :=
  ⟨⟨9, 40, 3761⟩, 183602697444485384, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_40_flag endpoint_9_40_sources 8 183602697444485384 183602697444485384 rfl endpoint_9_40_base endpoint_9_40_prefix_8) (by decide)⟩
private def endpoint_9_41_flag : Flag := ⟨9, 41, 3735⟩
private def endpoint_9_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_41_base : receiptBase endpoint_9_41_flag endpoint_9_41_sources = some 186646128265153486 := by decide +kernel
private theorem endpoint_9_41_window_0 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 2 186646128265153486 = some 186646128265153486 := by decide +kernel
private theorem endpoint_9_41_window_2 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 2 2 186646128265153486 = some 186646128265153486 := by decide +kernel
private theorem endpoint_9_41_prefix_4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 4 186646128265153486 = some 186646128265153486 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 2 2 186646128265153486 186646128265153486 186646128265153486 endpoint_9_41_window_0 endpoint_9_41_window_2
private theorem endpoint_9_41_window_4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 4 2 186646128265153486 = some 186646128265153486 := by decide +kernel
private theorem endpoint_9_41_prefix_6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 6 186646128265153486 = some 186646128265153486 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 4 2 186646128265153486 186646128265153486 186646128265153486 endpoint_9_41_prefix_4 endpoint_9_41_window_4
private theorem endpoint_9_41_window_6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 6 2 186646128265153486 = some 186646128265153486 := by decide +kernel
private theorem endpoint_9_41_prefix_8 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 8 186646128265153486 = some 186646128265153486 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 6 2 186646128265153486 186646128265153486 186646128265153486 endpoint_9_41_prefix_6 endpoint_9_41_window_6

def endpoint_9_41 : CertifiedEndpoint :=
  ⟨⟨9, 41, 3735⟩, 186646128265153486, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_41_flag endpoint_9_41_sources 8 186646128265153486 186646128265153486 rfl endpoint_9_41_base endpoint_9_41_prefix_8) (by decide)⟩
private def endpoint_9_42_flag : Flag := ⟨9, 42, 3709⟩
private def endpoint_9_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_42_base : receiptBase endpoint_9_42_flag endpoint_9_42_sources = some 189164125783920467 := by decide +kernel
private theorem endpoint_9_42_window_0 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 2 189164125783920467 = some 189164125783920467 := by decide +kernel
private theorem endpoint_9_42_window_2 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 2 2 189164125783920467 = some 189164125783920467 := by decide +kernel
private theorem endpoint_9_42_prefix_4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 4 189164125783920467 = some 189164125783920467 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 2 2 189164125783920467 189164125783920467 189164125783920467 endpoint_9_42_window_0 endpoint_9_42_window_2
private theorem endpoint_9_42_window_4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 4 2 189164125783920467 = some 189164125783920467 := by decide +kernel
private theorem endpoint_9_42_prefix_6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 6 189164125783920467 = some 189164125783920467 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 4 2 189164125783920467 189164125783920467 189164125783920467 endpoint_9_42_prefix_4 endpoint_9_42_window_4
private theorem endpoint_9_42_window_6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 6 2 189164125783920467 = some 189164125783920467 := by decide +kernel
private theorem endpoint_9_42_prefix_8 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 8 189164125783920467 = some 189164125783920467 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 6 2 189164125783920467 189164125783920467 189164125783920467 endpoint_9_42_prefix_6 endpoint_9_42_window_6

def endpoint_9_42 : CertifiedEndpoint :=
  ⟨⟨9, 42, 3709⟩, 189164125783920467, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_42_flag endpoint_9_42_sources 8 189164125783920467 189164125783920467 rfl endpoint_9_42_base endpoint_9_42_prefix_8) (by decide)⟩
private def endpoint_9_43_flag : Flag := ⟨9, 43, 3682⟩
private def endpoint_9_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_43_base : receiptBase endpoint_9_43_flag endpoint_9_43_sources = some 191577228791708178 := by decide +kernel
private theorem endpoint_9_43_window_0 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 2 191577228791708178 = some 191577228791708178 := by decide +kernel
private theorem endpoint_9_43_window_2 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 2 2 191577228791708178 = some 191577228791708178 := by decide +kernel
private theorem endpoint_9_43_prefix_4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 4 191577228791708178 = some 191577228791708178 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 2 2 191577228791708178 191577228791708178 191577228791708178 endpoint_9_43_window_0 endpoint_9_43_window_2
private theorem endpoint_9_43_window_4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 4 2 191577228791708178 = some 191577228791708178 := by decide +kernel
private theorem endpoint_9_43_prefix_6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 6 191577228791708178 = some 191577228791708178 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 4 2 191577228791708178 191577228791708178 191577228791708178 endpoint_9_43_prefix_4 endpoint_9_43_window_4
private theorem endpoint_9_43_window_6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 6 2 191577228791708178 = some 191577228791708178 := by decide +kernel
private theorem endpoint_9_43_prefix_8 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 8 191577228791708178 = some 191577228791708178 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 6 2 191577228791708178 191577228791708178 191577228791708178 endpoint_9_43_prefix_6 endpoint_9_43_window_6

def endpoint_9_43 : CertifiedEndpoint :=
  ⟨⟨9, 43, 3682⟩, 191577228791708178, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_43_flag endpoint_9_43_sources 8 191577228791708178 191577228791708178 rfl endpoint_9_43_base endpoint_9_43_prefix_8) (by decide)⟩
private def endpoint_9_44_flag : Flag := ⟨9, 44, 3655⟩
private def endpoint_9_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_44_base : receiptBase endpoint_9_44_flag endpoint_9_44_sources = some 193934754104917679 := by decide +kernel
private theorem endpoint_9_44_window_0 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 2 193934754104917679 = some 193934754104917679 := by decide +kernel
private theorem endpoint_9_44_window_2 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 2 2 193934754104917679 = some 193934754104917679 := by decide +kernel
private theorem endpoint_9_44_prefix_4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 4 193934754104917679 = some 193934754104917679 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 2 2 193934754104917679 193934754104917679 193934754104917679 endpoint_9_44_window_0 endpoint_9_44_window_2
private theorem endpoint_9_44_window_4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 4 2 193934754104917679 = some 193934754104917679 := by decide +kernel
private theorem endpoint_9_44_prefix_6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 6 193934754104917679 = some 193934754104917679 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 4 2 193934754104917679 193934754104917679 193934754104917679 endpoint_9_44_prefix_4 endpoint_9_44_window_4
private theorem endpoint_9_44_window_6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 6 2 193934754104917679 = some 193934754104917679 := by decide +kernel
private theorem endpoint_9_44_prefix_8 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 8 193934754104917679 = some 193934754104917679 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 6 2 193934754104917679 193934754104917679 193934754104917679 endpoint_9_44_prefix_6 endpoint_9_44_window_6

def endpoint_9_44 : CertifiedEndpoint :=
  ⟨⟨9, 44, 3655⟩, 193934754104917679, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_44_flag endpoint_9_44_sources 8 193934754104917679 193934754104917679 rfl endpoint_9_44_base endpoint_9_44_prefix_8) (by decide)⟩
private def endpoint_9_45_flag : Flag := ⟨9, 45, 3628⟩
private def endpoint_9_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_45_base : receiptBase endpoint_9_45_flag endpoint_9_45_sources = some 196236701723548970 := by decide +kernel
private theorem endpoint_9_45_window_0 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 2 196236701723548970 = some 196236701723548970 := by decide +kernel
private theorem endpoint_9_45_window_2 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 2 2 196236701723548970 = some 196236701723548970 := by decide +kernel
private theorem endpoint_9_45_prefix_4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 4 196236701723548970 = some 196236701723548970 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 2 2 196236701723548970 196236701723548970 196236701723548970 endpoint_9_45_window_0 endpoint_9_45_window_2
private theorem endpoint_9_45_window_4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 4 2 196236701723548970 = some 196236701723548970 := by decide +kernel
private theorem endpoint_9_45_prefix_6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 6 196236701723548970 = some 196236701723548970 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 4 2 196236701723548970 196236701723548970 196236701723548970 endpoint_9_45_prefix_4 endpoint_9_45_window_4
private theorem endpoint_9_45_window_6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 6 2 196236701723548970 = some 196236701723548970 := by decide +kernel
private theorem endpoint_9_45_prefix_8 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 8 196236701723548970 = some 196236701723548970 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 6 2 196236701723548970 196236701723548970 196236701723548970 endpoint_9_45_prefix_6 endpoint_9_45_window_6

def endpoint_9_45 : CertifiedEndpoint :=
  ⟨⟨9, 45, 3628⟩, 196236701723548970, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_45_flag endpoint_9_45_sources 8 196236701723548970 196236701723548970 rfl endpoint_9_45_base endpoint_9_45_prefix_8) (by decide)⟩
private def endpoint_9_46_flag : Flag := ⟨9, 46, 3600⟩
private def endpoint_9_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_46_base : receiptBase endpoint_9_46_flag endpoint_9_46_sources = some 198428702313512063 := by decide +kernel
private theorem endpoint_9_46_window_0 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 2 198428702313512063 = some 198428702313512063 := by decide +kernel
private theorem endpoint_9_46_window_2 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 2 2 198428702313512063 = some 198428702313512063 := by decide +kernel
private theorem endpoint_9_46_prefix_4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 4 198428702313512063 = some 198428702313512063 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 2 2 198428702313512063 198428702313512063 198428702313512063 endpoint_9_46_window_0 endpoint_9_46_window_2
private theorem endpoint_9_46_window_4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 4 2 198428702313512063 = some 198428702313512063 := by decide +kernel
private theorem endpoint_9_46_prefix_6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 6 198428702313512063 = some 198428702313512063 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 4 2 198428702313512063 198428702313512063 198428702313512063 endpoint_9_46_prefix_4 endpoint_9_46_window_4
private theorem endpoint_9_46_window_6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 6 2 198428702313512063 = some 198428702313512063 := by decide +kernel
private theorem endpoint_9_46_prefix_8 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 8 198428702313512063 = some 198428702313512063 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 6 2 198428702313512063 198428702313512063 198428702313512063 endpoint_9_46_prefix_6 endpoint_9_46_window_6

def endpoint_9_46 : CertifiedEndpoint :=
  ⟨⟨9, 46, 3600⟩, 198428702313512063, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_46_flag endpoint_9_46_sources 8 198428702313512063 198428702313512063 rfl endpoint_9_46_base endpoint_9_46_prefix_8) (by decide)⟩
private def endpoint_9_47_flag : Flag := ⟨9, 47, 3571⟩
private def endpoint_9_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_47_base : receiptBase endpoint_9_47_flag endpoint_9_47_sources = some 200507724364193603 := by decide +kernel
private theorem endpoint_9_47_window_0 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 2 200507724364193603 = some 200507724364193603 := by decide +kernel
private theorem endpoint_9_47_window_2 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 2 2 200507724364193603 = some 200507724364193603 := by decide +kernel
private theorem endpoint_9_47_prefix_4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 4 200507724364193603 = some 200507724364193603 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 2 2 200507724364193603 200507724364193603 200507724364193603 endpoint_9_47_window_0 endpoint_9_47_window_2
private theorem endpoint_9_47_window_4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 4 2 200507724364193603 = some 200507724364193603 := by decide +kernel
private theorem endpoint_9_47_prefix_6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 6 200507724364193603 = some 200507724364193603 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 4 2 200507724364193603 200507724364193603 200507724364193603 endpoint_9_47_prefix_4 endpoint_9_47_window_4
private theorem endpoint_9_47_window_6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 6 2 200507724364193603 = some 200507724364193603 := by decide +kernel
private theorem endpoint_9_47_prefix_8 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 8 200507724364193603 = some 200507724364193603 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 6 2 200507724364193603 200507724364193603 200507724364193603 endpoint_9_47_prefix_6 endpoint_9_47_window_6

def endpoint_9_47 : CertifiedEndpoint :=
  ⟨⟨9, 47, 3571⟩, 200507724364193603, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_47_flag endpoint_9_47_sources 8 200507724364193603 200507724364193603 rfl endpoint_9_47_base endpoint_9_47_prefix_8) (by decide)⟩
private def endpoint_9_48_flag : Flag := ⟨9, 48, 3542⟩
private def endpoint_9_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_48_base : receiptBase endpoint_9_48_flag endpoint_9_48_sources = some 202527126706145789 := by decide +kernel
private theorem endpoint_9_48_window_0 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 2 202527126706145789 = some 202527126706145789 := by decide +kernel
private theorem endpoint_9_48_window_2 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 2 2 202527126706145789 = some 202527126706145789 := by decide +kernel
private theorem endpoint_9_48_prefix_4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 4 202527126706145789 = some 202527126706145789 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 2 2 202527126706145789 202527126706145789 202527126706145789 endpoint_9_48_window_0 endpoint_9_48_window_2
private theorem endpoint_9_48_window_4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 4 2 202527126706145789 = some 202527126706145789 := by decide +kernel
private theorem endpoint_9_48_prefix_6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 6 202527126706145789 = some 202527126706145789 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 4 2 202527126706145789 202527126706145789 202527126706145789 endpoint_9_48_prefix_4 endpoint_9_48_window_4
private theorem endpoint_9_48_window_6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 6 2 202527126706145789 = some 202527126706145789 := by decide +kernel
private theorem endpoint_9_48_prefix_8 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 8 202527126706145789 = some 202527126706145789 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 6 2 202527126706145789 202527126706145789 202527126706145789 endpoint_9_48_prefix_6 endpoint_9_48_window_6

def endpoint_9_48 : CertifiedEndpoint :=
  ⟨⟨9, 48, 3542⟩, 202527126706145789, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_48_flag endpoint_9_48_sources 8 202527126706145789 202527126706145789 rfl endpoint_9_48_base endpoint_9_48_prefix_8) (by decide)⟩
private def endpoint_9_49_flag : Flag := ⟨9, 49, 3512⟩
private def endpoint_9_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_49_base : receiptBase endpoint_9_49_flag endpoint_9_49_sources = some 204429508494665279 := by decide +kernel
private theorem endpoint_9_49_window_0 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 2 204429508494665279 = some 204429508494665279 := by decide +kernel
private theorem endpoint_9_49_window_2 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 2 2 204429508494665279 = some 204429508494665279 := by decide +kernel
private theorem endpoint_9_49_prefix_4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 4 204429508494665279 = some 204429508494665279 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 2 2 204429508494665279 204429508494665279 204429508494665279 endpoint_9_49_window_0 endpoint_9_49_window_2
private theorem endpoint_9_49_window_4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 4 2 204429508494665279 = some 204429508494665279 := by decide +kernel
private theorem endpoint_9_49_prefix_6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 6 204429508494665279 = some 204429508494665279 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 4 2 204429508494665279 204429508494665279 204429508494665279 endpoint_9_49_prefix_4 endpoint_9_49_window_4
private theorem endpoint_9_49_window_6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 6 2 204429508494665279 = some 204429508494665279 := by decide +kernel
private theorem endpoint_9_49_prefix_8 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 8 204429508494665279 = some 204429508494665279 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 6 2 204429508494665279 204429508494665279 204429508494665279 endpoint_9_49_prefix_6 endpoint_9_49_window_6

def endpoint_9_49 : CertifiedEndpoint :=
  ⟨⟨9, 49, 3512⟩, 204429508494665279, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_49_flag endpoint_9_49_sources 8 204429508494665279 204429508494665279 rfl endpoint_9_49_base endpoint_9_49_prefix_8) (by decide)⟩
private def endpoint_9_50_flag : Flag := ⟨9, 50, 3482⟩
private def endpoint_9_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_50_base : receiptBase endpoint_9_50_flag endpoint_9_50_sources = some 206270249567379845 := by decide +kernel
private theorem endpoint_9_50_window_0 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 2 206270249567379845 = some 206270249567379845 := by decide +kernel
private theorem endpoint_9_50_window_2 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 2 2 206270249567379845 = some 206270249567379845 := by decide +kernel
private theorem endpoint_9_50_prefix_4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 4 206270249567379845 = some 206270249567379845 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 2 2 206270249567379845 206270249567379845 206270249567379845 endpoint_9_50_window_0 endpoint_9_50_window_2
private theorem endpoint_9_50_window_4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 4 2 206270249567379845 = some 206270249567379845 := by decide +kernel
private theorem endpoint_9_50_prefix_6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 6 206270249567379845 = some 206270249567379845 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 4 2 206270249567379845 206270249567379845 206270249567379845 endpoint_9_50_prefix_4 endpoint_9_50_window_4
private theorem endpoint_9_50_window_6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 6 2 206270249567379845 = some 206270249567379845 := by decide +kernel
private theorem endpoint_9_50_prefix_8 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 8 206270249567379845 = some 206270249567379845 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 6 2 206270249567379845 206270249567379845 206270249567379845 endpoint_9_50_prefix_6 endpoint_9_50_window_6

def endpoint_9_50 : CertifiedEndpoint :=
  ⟨⟨9, 50, 3482⟩, 206270249567379845, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_50_flag endpoint_9_50_sources 8 206270249567379845 206270249567379845 rfl endpoint_9_50_base endpoint_9_50_prefix_8) (by decide)⟩
private def endpoint_9_51_flag : Flag := ⟨9, 51, 3450⟩
private def endpoint_9_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_51_base : receiptBase endpoint_9_51_flag endpoint_9_51_sources = some 207930506220731656 := by decide +kernel
private theorem endpoint_9_51_window_0 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 2 207930506220731656 = some 207930506220731656 := by decide +kernel
private theorem endpoint_9_51_window_2 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 2 2 207930506220731656 = some 207930506220731656 := by decide +kernel
private theorem endpoint_9_51_prefix_4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 4 207930506220731656 = some 207930506220731656 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 2 2 207930506220731656 207930506220731656 207930506220731656 endpoint_9_51_window_0 endpoint_9_51_window_2
private theorem endpoint_9_51_window_4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 4 2 207930506220731656 = some 207930506220731656 := by decide +kernel
private theorem endpoint_9_51_prefix_6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 6 207930506220731656 = some 207930506220731656 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 4 2 207930506220731656 207930506220731656 207930506220731656 endpoint_9_51_prefix_4 endpoint_9_51_window_4
private theorem endpoint_9_51_window_6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 6 2 207930506220731656 = some 207930506220731656 := by decide +kernel
private theorem endpoint_9_51_prefix_8 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 8 207930506220731656 = some 207930506220731656 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 6 2 207930506220731656 207930506220731656 207930506220731656 endpoint_9_51_prefix_6 endpoint_9_51_window_6

def endpoint_9_51 : CertifiedEndpoint :=
  ⟨⟨9, 51, 3450⟩, 207930506220731656, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_51_flag endpoint_9_51_sources 8 207930506220731656 207930506220731656 rfl endpoint_9_51_base endpoint_9_51_prefix_8) (by decide)⟩
private def endpoint_9_52_flag : Flag := ⟨9, 52, 3419⟩
private def endpoint_9_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_52_base : receiptBase endpoint_9_52_flag endpoint_9_52_sources = some 209585512499444102 := by decide +kernel
private theorem endpoint_9_52_window_0 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 2 209585512499444102 = some 209585512499444102 := by decide +kernel
private theorem endpoint_9_52_window_2 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 2 2 209585512499444102 = some 209585512499444102 := by decide +kernel
private theorem endpoint_9_52_prefix_4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 4 209585512499444102 = some 209585512499444102 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 2 2 209585512499444102 209585512499444102 209585512499444102 endpoint_9_52_window_0 endpoint_9_52_window_2
private theorem endpoint_9_52_window_4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 4 2 209585512499444102 = some 209585512499444102 := by decide +kernel
private theorem endpoint_9_52_prefix_6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 6 209585512499444102 = some 209585512499444102 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 4 2 209585512499444102 209585512499444102 209585512499444102 endpoint_9_52_prefix_4 endpoint_9_52_window_4
private theorem endpoint_9_52_window_6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 6 2 209585512499444102 = some 209585512499444102 := by decide +kernel
private theorem endpoint_9_52_prefix_8 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 8 209585512499444102 = some 209585512499444102 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 6 2 209585512499444102 209585512499444102 209585512499444102 endpoint_9_52_prefix_6 endpoint_9_52_window_6

def endpoint_9_52 : CertifiedEndpoint :=
  ⟨⟨9, 52, 3419⟩, 209585512499444102, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_52_flag endpoint_9_52_sources 8 209585512499444102 209585512499444102 rfl endpoint_9_52_base endpoint_9_52_prefix_8) (by decide)⟩
private def endpoint_9_53_flag : Flag := ⟨9, 53, 3386⟩
private def endpoint_9_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_53_base : receiptBase endpoint_9_53_flag endpoint_9_53_sources = some 211053971337567079 := by decide +kernel
private theorem endpoint_9_53_window_0 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 2 211053971337567079 = some 211053971337567079 := by decide +kernel
private theorem endpoint_9_53_window_2 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 2 2 211053971337567079 = some 211053971337567079 := by decide +kernel
private theorem endpoint_9_53_prefix_4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 4 211053971337567079 = some 211053971337567079 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 2 2 211053971337567079 211053971337567079 211053971337567079 endpoint_9_53_window_0 endpoint_9_53_window_2
private theorem endpoint_9_53_window_4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 4 2 211053971337567079 = some 211053971337567079 := by decide +kernel
private theorem endpoint_9_53_prefix_6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 6 211053971337567079 = some 211053971337567079 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 4 2 211053971337567079 211053971337567079 211053971337567079 endpoint_9_53_prefix_4 endpoint_9_53_window_4
private theorem endpoint_9_53_window_6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 6 2 211053971337567079 = some 211053971337567079 := by decide +kernel
private theorem endpoint_9_53_prefix_8 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 8 211053971337567079 = some 211053971337567079 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 6 2 211053971337567079 211053971337567079 211053971337567079 endpoint_9_53_prefix_6 endpoint_9_53_window_6

def endpoint_9_53 : CertifiedEndpoint :=
  ⟨⟨9, 53, 3386⟩, 211053971337567079, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_53_flag endpoint_9_53_sources 8 211053971337567079 211053971337567079 rfl endpoint_9_53_base endpoint_9_53_prefix_8) (by decide)⟩
private def endpoint_9_54_flag : Flag := ⟨9, 54, 3353⟩
private def endpoint_9_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_54_base : receiptBase endpoint_9_54_flag endpoint_9_54_sources = some 212454726438658419 := by decide +kernel
private theorem endpoint_9_54_window_0 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 2 212454726438658419 = some 212454726438658419 := by decide +kernel
private theorem endpoint_9_54_window_2 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 2 2 212454726438658419 = some 212454726438658419 := by decide +kernel
private theorem endpoint_9_54_prefix_4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 4 212454726438658419 = some 212454726438658419 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 2 2 212454726438658419 212454726438658419 212454726438658419 endpoint_9_54_window_0 endpoint_9_54_window_2
private theorem endpoint_9_54_window_4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 4 2 212454726438658419 = some 212454726438658419 := by decide +kernel
private theorem endpoint_9_54_prefix_6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 6 212454726438658419 = some 212454726438658419 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 4 2 212454726438658419 212454726438658419 212454726438658419 endpoint_9_54_prefix_4 endpoint_9_54_window_4
private theorem endpoint_9_54_window_6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 6 2 212454726438658419 = some 212454726438658419 := by decide +kernel
private theorem endpoint_9_54_prefix_8 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 8 212454726438658419 = some 212454726438658419 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 6 2 212454726438658419 212454726438658419 212454726438658419 endpoint_9_54_prefix_6 endpoint_9_54_window_6

def endpoint_9_54 : CertifiedEndpoint :=
  ⟨⟨9, 54, 3353⟩, 212454726438658419, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_54_flag endpoint_9_54_sources 8 212454726438658419 212454726438658419 rfl endpoint_9_54_base endpoint_9_54_prefix_8) (by decide)⟩
private def endpoint_9_55_flag : Flag := ⟨9, 55, 3318⟩
private def endpoint_9_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_55_base : receiptBase endpoint_9_55_flag endpoint_9_55_sources = some 214336312862352969 := by decide +kernel
private theorem endpoint_9_55_window_0 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 2 214336312862352969 = some 214336312862352969 := by decide +kernel
private theorem endpoint_9_55_window_2 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 2 2 214336312862352969 = some 214336312862352969 := by decide +kernel
private theorem endpoint_9_55_prefix_4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 4 214336312862352969 = some 214336312862352969 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 2 2 214336312862352969 214336312862352969 214336312862352969 endpoint_9_55_window_0 endpoint_9_55_window_2
private theorem endpoint_9_55_window_4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 4 2 214336312862352969 = some 214336312862352969 := by decide +kernel
private theorem endpoint_9_55_prefix_6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 6 214336312862352969 = some 214336312862352969 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 4 2 214336312862352969 214336312862352969 214336312862352969 endpoint_9_55_prefix_4 endpoint_9_55_window_4
private theorem endpoint_9_55_window_6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 6 2 214336312862352969 = some 214336312862352969 := by decide +kernel
private theorem endpoint_9_55_prefix_8 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 8 214336312862352969 = some 214336312862352969 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 6 2 214336312862352969 214336312862352969 214336312862352969 endpoint_9_55_prefix_6 endpoint_9_55_window_6

def endpoint_9_55 : CertifiedEndpoint :=
  ⟨⟨9, 55, 3318⟩, 214336312862352969, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_55_flag endpoint_9_55_sources 8 214336312862352969 214336312862352969 rfl endpoint_9_55_base endpoint_9_55_prefix_8) (by decide)⟩
private def endpoint_9_56_flag : Flag := ⟨9, 56, 3283⟩
private def endpoint_9_56_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_56_base : receiptBase endpoint_9_56_flag endpoint_9_56_sources = some 215477760180017521 := by decide +kernel
private theorem endpoint_9_56_window_0 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 2 215477760180017521 = some 215477760180017521 := by decide +kernel
private theorem endpoint_9_56_window_2 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 2 2 215477760180017521 = some 215477760180017521 := by decide +kernel
private theorem endpoint_9_56_prefix_4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 4 215477760180017521 = some 215477760180017521 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 2 2 215477760180017521 215477760180017521 215477760180017521 endpoint_9_56_window_0 endpoint_9_56_window_2
private theorem endpoint_9_56_window_4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 4 2 215477760180017521 = some 215477760180017521 := by decide +kernel
private theorem endpoint_9_56_prefix_6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 6 215477760180017521 = some 215477760180017521 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 4 2 215477760180017521 215477760180017521 215477760180017521 endpoint_9_56_prefix_4 endpoint_9_56_window_4
private theorem endpoint_9_56_window_6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 6 2 215477760180017521 = some 215477760180017521 := by decide +kernel
private theorem endpoint_9_56_prefix_8 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 8 215477760180017521 = some 215477760180017521 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 6 2 215477760180017521 215477760180017521 215477760180017521 endpoint_9_56_prefix_6 endpoint_9_56_window_6

def endpoint_9_56 : CertifiedEndpoint :=
  ⟨⟨9, 56, 3283⟩, 215477760180017521, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_56_flag endpoint_9_56_sources 8 215477760180017521 215477760180017521 rfl endpoint_9_56_base endpoint_9_56_prefix_8) (by decide)⟩
private def endpoint_9_57_flag : Flag := ⟨9, 57, 3246⟩
private def endpoint_9_57_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_57_base : receiptBase endpoint_9_57_flag endpoint_9_57_sources = some 216415735940010526 := by decide +kernel
private theorem endpoint_9_57_window_0 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 2 216415735940010526 = some 216415735940010526 := by decide +kernel
private theorem endpoint_9_57_window_2 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 2 2 216415735940010526 = some 216415735940010526 := by decide +kernel
private theorem endpoint_9_57_prefix_4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 4 216415735940010526 = some 216415735940010526 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 2 2 216415735940010526 216415735940010526 216415735940010526 endpoint_9_57_window_0 endpoint_9_57_window_2
private theorem endpoint_9_57_window_4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 4 2 216415735940010526 = some 216415735940010526 := by decide +kernel
private theorem endpoint_9_57_prefix_6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 6 216415735940010526 = some 216415735940010526 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 4 2 216415735940010526 216415735940010526 216415735940010526 endpoint_9_57_prefix_4 endpoint_9_57_window_4
private theorem endpoint_9_57_window_6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 6 2 216415735940010526 = some 216415735940010526 := by decide +kernel
private theorem endpoint_9_57_prefix_8 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 8 216415735940010526 = some 216415735940010526 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 6 2 216415735940010526 216415735940010526 216415735940010526 endpoint_9_57_prefix_6 endpoint_9_57_window_6

def endpoint_9_57 : CertifiedEndpoint :=
  ⟨⟨9, 57, 3246⟩, 216415735940010526, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_57_flag endpoint_9_57_sources 8 216415735940010526 216415735940010526 rfl endpoint_9_57_base endpoint_9_57_prefix_8) (by decide)⟩
private def endpoint_9_58_flag : Flag := ⟨9, 58, 3209⟩
private def endpoint_9_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_9_58_base : receiptBase endpoint_9_58_flag endpoint_9_58_sources = some 217348472248333875 := by decide +kernel
private theorem endpoint_9_58_window_0 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 2 217348472248333875 = some 217348472248333875 := by decide +kernel
private theorem endpoint_9_58_window_2 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 2 2 217348472248333875 = some 217348472248333875 := by decide +kernel
private theorem endpoint_9_58_prefix_4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 4 217348472248333875 = some 217348472248333875 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 2 2 217348472248333875 217348472248333875 217348472248333875 endpoint_9_58_window_0 endpoint_9_58_window_2
private theorem endpoint_9_58_window_4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 4 2 217348472248333875 = some 217348472248333875 := by decide +kernel
private theorem endpoint_9_58_prefix_6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 6 217348472248333875 = some 217348472248333875 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 4 2 217348472248333875 217348472248333875 217348472248333875 endpoint_9_58_prefix_4 endpoint_9_58_window_4
private theorem endpoint_9_58_window_6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 6 2 217348472248333875 = some 217348472248333875 := by decide +kernel
private theorem endpoint_9_58_prefix_8 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 8 217348472248333875 = some 217348472248333875 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 6 2 217348472248333875 217348472248333875 217348472248333875 endpoint_9_58_prefix_6 endpoint_9_58_window_6

def endpoint_9_58 : CertifiedEndpoint :=
  ⟨⟨9, 58, 3209⟩, 217348472248333875, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_9_58_flag endpoint_9_58_sources 8 217348472248333875 217348472248333875 rfl endpoint_9_58_base endpoint_9_58_prefix_8) (by decide)⟩
private def endpoint_9_59_flag : Flag := ⟨9, 59, 3170⟩
private def endpoint_9_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_59_base : receiptBase endpoint_9_59_flag endpoint_9_59_sources = some 220080058018593162 := by decide +kernel
private theorem endpoint_9_59_window_0 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 2 220080058018593162 = some 220080058018593162 := by decide +kernel
private theorem endpoint_9_59_window_2 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 2 2 220080058018593162 = some 220080058018593162 := by decide +kernel
private theorem endpoint_9_59_prefix_4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 4 220080058018593162 = some 220080058018593162 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 2 2 220080058018593162 220080058018593162 220080058018593162 endpoint_9_59_window_0 endpoint_9_59_window_2
private theorem endpoint_9_59_window_4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 4 2 220080058018593162 = some 220080058018593162 := by decide +kernel
private theorem endpoint_9_59_prefix_6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 6 220080058018593162 = some 220080058018593162 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 4 2 220080058018593162 220080058018593162 220080058018593162 endpoint_9_59_prefix_4 endpoint_9_59_window_4
private theorem endpoint_9_59_window_6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 6 2 220080058018593162 = some 220080058018593162 := by decide +kernel
private theorem endpoint_9_59_prefix_8 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 8 220080058018593162 = some 220080058018593162 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 6 2 220080058018593162 220080058018593162 220080058018593162 endpoint_9_59_prefix_6 endpoint_9_59_window_6

def endpoint_9_59 : CertifiedEndpoint :=
  ⟨⟨9, 59, 3170⟩, 220080058018593162, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_59_flag endpoint_9_59_sources 8 220080058018593162 220080058018593162 rfl endpoint_9_59_base endpoint_9_59_prefix_8) (by decide)⟩
private def endpoint_9_60_flag : Flag := ⟨9, 60, 3129⟩
private def endpoint_9_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_60_base : receiptBase endpoint_9_60_flag endpoint_9_60_sources = some 220478731053649565 := by decide +kernel
private theorem endpoint_9_60_window_0 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 2 220478731053649565 = some 220478731053649565 := by decide +kernel
private theorem endpoint_9_60_window_2 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 2 2 220478731053649565 = some 220478731053649565 := by decide +kernel
private theorem endpoint_9_60_prefix_4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 4 220478731053649565 = some 220478731053649565 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 2 2 220478731053649565 220478731053649565 220478731053649565 endpoint_9_60_window_0 endpoint_9_60_window_2
private theorem endpoint_9_60_window_4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 4 2 220478731053649565 = some 220478731053649565 := by decide +kernel
private theorem endpoint_9_60_prefix_6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 6 220478731053649565 = some 220478731053649565 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 4 2 220478731053649565 220478731053649565 220478731053649565 endpoint_9_60_prefix_4 endpoint_9_60_window_4
private theorem endpoint_9_60_window_6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 6 2 220478731053649565 = some 220478731053649565 := by decide +kernel
private theorem endpoint_9_60_prefix_8 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 8 220478731053649565 = some 220478731053649565 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 6 2 220478731053649565 220478731053649565 220478731053649565 endpoint_9_60_prefix_6 endpoint_9_60_window_6

def endpoint_9_60 : CertifiedEndpoint :=
  ⟨⟨9, 60, 3129⟩, 220478731053649565, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_60_flag endpoint_9_60_sources 8 220478731053649565 220478731053649565 rfl endpoint_9_60_base endpoint_9_60_prefix_8) (by decide)⟩
private def endpoint_9_61_flag : Flag := ⟨9, 61, 3087⟩
private def endpoint_9_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_61_base : receiptBase endpoint_9_61_flag endpoint_9_61_sources = some 220722132608664149 := by decide +kernel
private theorem endpoint_9_61_window_0 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 2 220722132608664149 = some 220722132608664149 := by decide +kernel
private theorem endpoint_9_61_window_2 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 2 2 220722132608664149 = some 220722132608664149 := by decide +kernel
private theorem endpoint_9_61_prefix_4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 4 220722132608664149 = some 220722132608664149 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 2 2 220722132608664149 220722132608664149 220722132608664149 endpoint_9_61_window_0 endpoint_9_61_window_2
private theorem endpoint_9_61_window_4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 4 2 220722132608664149 = some 220722132608664149 := by decide +kernel
private theorem endpoint_9_61_prefix_6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 6 220722132608664149 = some 220722132608664149 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 4 2 220722132608664149 220722132608664149 220722132608664149 endpoint_9_61_prefix_4 endpoint_9_61_window_4
private theorem endpoint_9_61_window_6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 6 2 220722132608664149 = some 220722132608664149 := by decide +kernel
private theorem endpoint_9_61_prefix_8 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 8 220722132608664149 = some 220722132608664149 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 6 2 220722132608664149 220722132608664149 220722132608664149 endpoint_9_61_prefix_6 endpoint_9_61_window_6

def endpoint_9_61 : CertifiedEndpoint :=
  ⟨⟨9, 61, 3087⟩, 220722132608664149, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_61_flag endpoint_9_61_sources 8 220722132608664149 220722132608664149 rfl endpoint_9_61_base endpoint_9_61_prefix_8) (by decide)⟩
private def endpoint_9_62_flag : Flag := ⟨9, 62, 3044⟩
private def endpoint_9_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_62_base : receiptBase endpoint_9_62_flag endpoint_9_62_sources = some 220807204186785794 := by decide +kernel
private theorem endpoint_9_62_window_0 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 2 220807204186785794 = some 220807204186785794 := by decide +kernel
private theorem endpoint_9_62_window_2 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 2 2 220807204186785794 = some 220807204186785794 := by decide +kernel
private theorem endpoint_9_62_prefix_4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 4 220807204186785794 = some 220807204186785794 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 2 2 220807204186785794 220807204186785794 220807204186785794 endpoint_9_62_window_0 endpoint_9_62_window_2
private theorem endpoint_9_62_window_4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 4 2 220807204186785794 = some 220807204186785794 := by decide +kernel
private theorem endpoint_9_62_prefix_6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 6 220807204186785794 = some 220807204186785794 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 4 2 220807204186785794 220807204186785794 220807204186785794 endpoint_9_62_prefix_4 endpoint_9_62_window_4
private theorem endpoint_9_62_window_6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 6 2 220807204186785794 = some 220807204186785794 := by decide +kernel
private theorem endpoint_9_62_prefix_8 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 8 220807204186785794 = some 220807204186785794 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 6 2 220807204186785794 220807204186785794 220807204186785794 endpoint_9_62_prefix_6 endpoint_9_62_window_6

def endpoint_9_62 : CertifiedEndpoint :=
  ⟨⟨9, 62, 3044⟩, 220807204186785794, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_62_flag endpoint_9_62_sources 8 220807204186785794 220807204186785794 rfl endpoint_9_62_base endpoint_9_62_prefix_8) (by decide)⟩
private def endpoint_9_63_flag : Flag := ⟨9, 63, 2998⟩
private def endpoint_9_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_63_base : receiptBase endpoint_9_63_flag endpoint_9_63_sources = some 220585503161040300 := by decide +kernel
private theorem endpoint_9_63_window_0 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 2 220585503161040300 = some 220585503161040300 := by decide +kernel
private theorem endpoint_9_63_window_2 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 2 2 220585503161040300 = some 220585503161040300 := by decide +kernel
private theorem endpoint_9_63_prefix_4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 4 220585503161040300 = some 220585503161040300 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 2 2 220585503161040300 220585503161040300 220585503161040300 endpoint_9_63_window_0 endpoint_9_63_window_2
private theorem endpoint_9_63_window_4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 4 2 220585503161040300 = some 220585503161040300 := by decide +kernel
private theorem endpoint_9_63_prefix_6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 6 220585503161040300 = some 220585503161040300 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 4 2 220585503161040300 220585503161040300 220585503161040300 endpoint_9_63_prefix_4 endpoint_9_63_window_4
private theorem endpoint_9_63_window_6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 6 2 220585503161040300 = some 220585503161040300 := by decide +kernel
private theorem endpoint_9_63_prefix_8 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 8 220585503161040300 = some 220585503161040300 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 6 2 220585503161040300 220585503161040300 220585503161040300 endpoint_9_63_prefix_6 endpoint_9_63_window_6

def endpoint_9_63 : CertifiedEndpoint :=
  ⟨⟨9, 63, 2998⟩, 220585503161040300, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_63_flag endpoint_9_63_sources 8 220585503161040300 220585503161040300 rfl endpoint_9_63_base endpoint_9_63_prefix_8) (by decide)⟩
private def endpoint_9_64_flag : Flag := ⟨9, 64, 2950⟩
private def endpoint_9_64_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_64_base : receiptBase endpoint_9_64_flag endpoint_9_64_sources = some 221376152868555758 := by decide +kernel
private theorem endpoint_9_64_window_0 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 2 221376152868555758 = some 221376152868555758 := by decide +kernel
private theorem endpoint_9_64_window_2 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 2 2 221376152868555758 = some 221376152868555758 := by decide +kernel
private theorem endpoint_9_64_prefix_4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 4 221376152868555758 = some 221376152868555758 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 2 2 221376152868555758 221376152868555758 221376152868555758 endpoint_9_64_window_0 endpoint_9_64_window_2
private theorem endpoint_9_64_window_4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 4 2 221376152868555758 = some 221376152868555758 := by decide +kernel
private theorem endpoint_9_64_prefix_6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 6 221376152868555758 = some 221376152868555758 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 4 2 221376152868555758 221376152868555758 221376152868555758 endpoint_9_64_prefix_4 endpoint_9_64_window_4
private theorem endpoint_9_64_window_6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 6 2 221376152868555758 = some 221376152868555758 := by decide +kernel
private theorem endpoint_9_64_prefix_8 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 8 221376152868555758 = some 221376152868555758 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 6 2 221376152868555758 221376152868555758 221376152868555758 endpoint_9_64_prefix_6 endpoint_9_64_window_6

def endpoint_9_64 : CertifiedEndpoint :=
  ⟨⟨9, 64, 2950⟩, 221376152868555758, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_64_flag endpoint_9_64_sources 8 221376152868555758 221376152868555758 rfl endpoint_9_64_base endpoint_9_64_prefix_8) (by decide)⟩
private def endpoint_9_65_flag : Flag := ⟨9, 65, 2899⟩
private def endpoint_9_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_65_base : receiptBase endpoint_9_65_flag endpoint_9_65_sources = some 220586281879280559 := by decide +kernel
private theorem endpoint_9_65_window_0 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 2 220586281879280559 = some 220586281879280559 := by decide +kernel
private theorem endpoint_9_65_window_2 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 2 2 220586281879280559 = some 220586281879280559 := by decide +kernel
private theorem endpoint_9_65_prefix_4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 4 220586281879280559 = some 220586281879280559 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 2 2 220586281879280559 220586281879280559 220586281879280559 endpoint_9_65_window_0 endpoint_9_65_window_2
private theorem endpoint_9_65_window_4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 4 2 220586281879280559 = some 220586281879280559 := by decide +kernel
private theorem endpoint_9_65_prefix_6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 6 220586281879280559 = some 220586281879280559 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 4 2 220586281879280559 220586281879280559 220586281879280559 endpoint_9_65_prefix_4 endpoint_9_65_window_4
private theorem endpoint_9_65_window_6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 6 2 220586281879280559 = some 220586281879280559 := by decide +kernel
private theorem endpoint_9_65_prefix_8 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 8 220586281879280559 = some 220586281879280559 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 6 2 220586281879280559 220586281879280559 220586281879280559 endpoint_9_65_prefix_6 endpoint_9_65_window_6

def endpoint_9_65 : CertifiedEndpoint :=
  ⟨⟨9, 65, 2899⟩, 220586281879280559, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_65_flag endpoint_9_65_sources 8 220586281879280559 220586281879280559 rfl endpoint_9_65_base endpoint_9_65_prefix_8) (by decide)⟩

def endpointBlock04 : List CertifiedEndpoint := [
  endpoint_8_58, endpoint_8_59, endpoint_8_60, endpoint_8_61, endpoint_8_62, endpoint_8_63,
  endpoint_8_64, endpoint_8_65, endpoint_8_66, endpoint_8_67, endpoint_8_68, endpoint_8_69,
  endpoint_8_70, endpoint_8_71, endpoint_8_72, endpoint_8_73, endpoint_8_74, endpoint_8_75,
  endpoint_8_76, endpoint_8_77, endpoint_8_78, endpoint_8_79, endpoint_8_80, endpoint_8_81,
  endpoint_8_82, endpoint_8_83, endpoint_8_84, endpoint_8_85, endpoint_8_86, endpoint_8_87,
  endpoint_8_88, endpoint_8_89, endpoint_8_90, endpoint_8_91, endpoint_8_92, endpoint_8_93,
  endpoint_8_94, endpoint_8_95, endpoint_8_96, endpoint_9_9, endpoint_9_10, endpoint_9_11,
  endpoint_9_12, endpoint_9_13, endpoint_9_14, endpoint_9_15, endpoint_9_16, endpoint_9_17,
  endpoint_9_18, endpoint_9_19, endpoint_9_20, endpoint_9_21, endpoint_9_22, endpoint_9_23,
  endpoint_9_24, endpoint_9_25, endpoint_9_26, endpoint_9_27, endpoint_9_28, endpoint_9_29,
  endpoint_9_30, endpoint_9_31, endpoint_9_32, endpoint_9_33, endpoint_9_34, endpoint_9_35,
  endpoint_9_36, endpoint_9_37, endpoint_9_38, endpoint_9_39, endpoint_9_40, endpoint_9_41,
  endpoint_9_42, endpoint_9_43, endpoint_9_44, endpoint_9_45, endpoint_9_46, endpoint_9_47,
  endpoint_9_48, endpoint_9_49, endpoint_9_50, endpoint_9_51, endpoint_9_52, endpoint_9_53,
  endpoint_9_54, endpoint_9_55, endpoint_9_56, endpoint_9_57, endpoint_9_58, endpoint_9_59,
  endpoint_9_60, endpoint_9_61, endpoint_9_62, endpoint_9_63, endpoint_9_64, endpoint_9_65
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
