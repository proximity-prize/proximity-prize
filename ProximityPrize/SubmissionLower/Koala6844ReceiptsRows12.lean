import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_17_50_flag : Flag := ⟨17, 50, 2189⟩
private def endpoint_17_50_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_50_base : receiptBase endpoint_17_50_flag endpoint_17_50_sources = some 210377518047221069 := by decide +kernel
private theorem endpoint_17_50_window_0 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 2 210377518047221069 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_window_2 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 2 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 4 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 2 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_window_0 endpoint_17_50_window_2
private theorem endpoint_17_50_window_4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 4 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 6 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 4 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_4 endpoint_17_50_window_4
private theorem endpoint_17_50_window_6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 6 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 8 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 6 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_6 endpoint_17_50_window_6
private theorem endpoint_17_50_window_8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 8 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 10 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 8 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_8 endpoint_17_50_window_8
private theorem endpoint_17_50_window_10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 10 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 12 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 10 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_10 endpoint_17_50_window_10
private theorem endpoint_17_50_window_12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 12 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 14 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 12 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_12 endpoint_17_50_window_12
private theorem endpoint_17_50_window_14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 14 2 221593590709894410 = some 221593590709894410 := by decide +kernel
private theorem endpoint_17_50_prefix_16 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 16 210377518047221069 = some 221593590709894410 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 14 2 210377518047221069 221593590709894410 221593590709894410 endpoint_17_50_prefix_14 endpoint_17_50_window_14

def endpoint_17_50 : CertifiedEndpoint :=
  ⟨⟨17, 50, 2189⟩, 221593590709894410, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_50_flag endpoint_17_50_sources 16 210377518047221069 221593590709894410 rfl endpoint_17_50_base endpoint_17_50_prefix_16) (by decide)⟩
private def endpoint_17_51_flag : Flag := ⟨17, 51, 2141⟩
private def endpoint_17_51_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_51_base : receiptBase endpoint_17_51_flag endpoint_17_51_sources = some 209494912325164904 := by decide +kernel
private theorem endpoint_17_51_window_0 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 2 209494912325164904 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_window_2 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 2 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 4 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 2 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_window_0 endpoint_17_51_window_2
private theorem endpoint_17_51_window_4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 4 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 6 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 4 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_4 endpoint_17_51_window_4
private theorem endpoint_17_51_window_6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 6 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 8 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 6 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_6 endpoint_17_51_window_6
private theorem endpoint_17_51_window_8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 8 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 10 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 8 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_8 endpoint_17_51_window_8
private theorem endpoint_17_51_window_10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 10 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 12 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 10 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_10 endpoint_17_51_window_10
private theorem endpoint_17_51_window_12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 12 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 14 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 12 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_12 endpoint_17_51_window_12
private theorem endpoint_17_51_window_14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 14 2 224377905526421957 = some 224377905526421957 := by decide +kernel
private theorem endpoint_17_51_prefix_16 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 16 209494912325164904 = some 224377905526421957 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 14 2 209494912325164904 224377905526421957 224377905526421957 endpoint_17_51_prefix_14 endpoint_17_51_window_14

def endpoint_17_51 : CertifiedEndpoint :=
  ⟨⟨17, 51, 2141⟩, 224377905526421957, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_51_flag endpoint_17_51_sources 16 209494912325164904 224377905526421957 rfl endpoint_17_51_base endpoint_17_51_prefix_16) (by decide)⟩
private def endpoint_17_52_flag : Flag := ⟨17, 52, 2091⟩
private def endpoint_17_52_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_52_base : receiptBase endpoint_17_52_flag endpoint_17_52_sources = some 208920917119272911 := by decide +kernel
private theorem endpoint_17_52_window_0 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 2 208920917119272911 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_window_2 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 2 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 4 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 2 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_window_0 endpoint_17_52_window_2
private theorem endpoint_17_52_window_4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 4 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 6 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 4 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_4 endpoint_17_52_window_4
private theorem endpoint_17_52_window_6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 6 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 8 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 6 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_6 endpoint_17_52_window_6
private theorem endpoint_17_52_window_8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 8 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 10 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 8 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_8 endpoint_17_52_window_8
private theorem endpoint_17_52_window_10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 10 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 12 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 10 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_10 endpoint_17_52_window_10
private theorem endpoint_17_52_window_12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 12 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 14 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 12 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_12 endpoint_17_52_window_12
private theorem endpoint_17_52_window_14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 14 2 215314119881643024 = some 215314119881643024 := by decide +kernel
private theorem endpoint_17_52_prefix_16 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 16 208920917119272911 = some 215314119881643024 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 14 2 208920917119272911 215314119881643024 215314119881643024 endpoint_17_52_prefix_14 endpoint_17_52_window_14

def endpoint_17_52 : CertifiedEndpoint :=
  ⟨⟨17, 52, 2091⟩, 215314119881643024, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_52_flag endpoint_17_52_sources 16 208920917119272911 215314119881643024 rfl endpoint_17_52_base endpoint_17_52_prefix_16) (by decide)⟩
private def endpoint_17_53_flag : Flag := ⟨17, 53, 2041⟩
private def endpoint_17_53_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_53_base : receiptBase endpoint_17_53_flag endpoint_17_53_sources = some 207515885271416825 := by decide +kernel
private theorem endpoint_17_53_window_0 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 2 207515885271416825 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_window_2 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 2 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 4 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 2 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_window_0 endpoint_17_53_window_2
private theorem endpoint_17_53_window_4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 4 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 6 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 4 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_4 endpoint_17_53_window_4
private theorem endpoint_17_53_window_6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 6 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 8 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 6 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_6 endpoint_17_53_window_6
private theorem endpoint_17_53_window_8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 8 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 10 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 8 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_8 endpoint_17_53_window_8
private theorem endpoint_17_53_window_10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 10 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 12 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 10 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_10 endpoint_17_53_window_10
private theorem endpoint_17_53_window_12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 12 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 14 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 12 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_12 endpoint_17_53_window_12
private theorem endpoint_17_53_window_14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 14 2 217450161895398492 = some 217450161895398492 := by decide +kernel
private theorem endpoint_17_53_prefix_16 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 16 207515885271416825 = some 217450161895398492 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 14 2 207515885271416825 217450161895398492 217450161895398492 endpoint_17_53_prefix_14 endpoint_17_53_window_14

def endpoint_17_53 : CertifiedEndpoint :=
  ⟨⟨17, 53, 2041⟩, 217450161895398492, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_53_flag endpoint_17_53_sources 16 207515885271416825 217450161895398492 rfl endpoint_17_53_base endpoint_17_53_prefix_16) (by decide)⟩
private def endpoint_17_54_flag : Flag := ⟨17, 54, 1990⟩
private def endpoint_17_54_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_54_base : receiptBase endpoint_17_54_flag endpoint_17_54_sources = some 205835818017460953 := by decide +kernel
private theorem endpoint_17_54_window_0 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 2 205835818017460953 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_window_2 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 2 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 4 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 2 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_window_0 endpoint_17_54_window_2
private theorem endpoint_17_54_window_4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 4 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 6 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 4 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_4 endpoint_17_54_window_4
private theorem endpoint_17_54_window_6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 6 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 8 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 6 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_6 endpoint_17_54_window_6
private theorem endpoint_17_54_window_8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 8 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 10 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 8 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_8 endpoint_17_54_window_8
private theorem endpoint_17_54_window_10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 10 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 12 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 10 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_10 endpoint_17_54_window_10
private theorem endpoint_17_54_window_12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 12 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 14 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 12 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_12 endpoint_17_54_window_12
private theorem endpoint_17_54_window_14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 14 2 219392590496297916 = some 219392590496297916 := by decide +kernel
private theorem endpoint_17_54_prefix_16 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 16 205835818017460953 = some 219392590496297916 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 14 2 205835818017460953 219392590496297916 219392590496297916 endpoint_17_54_prefix_14 endpoint_17_54_window_14

def endpoint_17_54 : CertifiedEndpoint :=
  ⟨⟨17, 54, 1990⟩, 219392590496297916, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_54_flag endpoint_17_54_sources 16 205835818017460953 219392590496297916 rfl endpoint_17_54_base endpoint_17_54_prefix_16) (by decide)⟩
private def endpoint_17_55_flag : Flag := ⟨17, 55, 1937⟩
private def endpoint_17_55_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_55_base : receiptBase endpoint_17_55_flag endpoint_17_55_sources = some 203759061309057780 := by decide +kernel
private theorem endpoint_17_55_window_0 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 2 203759061309057780 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_window_2 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 2 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 4 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 2 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_window_0 endpoint_17_55_window_2
private theorem endpoint_17_55_window_4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 4 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 6 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 4 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_4 endpoint_17_55_window_4
private theorem endpoint_17_55_window_6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 6 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 8 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 6 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_6 endpoint_17_55_window_6
private theorem endpoint_17_55_window_8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 8 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 10 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 8 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_8 endpoint_17_55_window_8
private theorem endpoint_17_55_window_10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 10 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 12 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 10 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_10 endpoint_17_55_window_10
private theorem endpoint_17_55_window_12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 12 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 14 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 12 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_12 endpoint_17_55_window_12
private theorem endpoint_17_55_window_14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 14 2 221077967404397738 = some 221077967404397738 := by decide +kernel
private theorem endpoint_17_55_prefix_16 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 16 203759061309057780 = some 221077967404397738 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 14 2 203759061309057780 221077967404397738 221077967404397738 endpoint_17_55_prefix_14 endpoint_17_55_window_14

def endpoint_17_55 : CertifiedEndpoint :=
  ⟨⟨17, 55, 1937⟩, 221077967404397738, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_55_flag endpoint_17_55_sources 16 203759061309057780 221077967404397738 rfl endpoint_17_55_base endpoint_17_55_prefix_16) (by decide)⟩
private def endpoint_17_56_flag : Flag := ⟨17, 56, 1883⟩
private def endpoint_17_56_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_56_base : receiptBase endpoint_17_56_flag endpoint_17_56_sources = some 202259672394747566 := by decide +kernel
private theorem endpoint_17_56_window_0 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 2 202259672394747566 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_window_2 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 2 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 4 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 2 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_window_0 endpoint_17_56_window_2
private theorem endpoint_17_56_window_4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 4 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 6 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 4 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_4 endpoint_17_56_window_4
private theorem endpoint_17_56_window_6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 6 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 8 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 6 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_6 endpoint_17_56_window_6
private theorem endpoint_17_56_window_8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 8 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 10 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 8 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_8 endpoint_17_56_window_8
private theorem endpoint_17_56_window_10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 10 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 12 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 10 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_10 endpoint_17_56_window_10
private theorem endpoint_17_56_window_12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 12 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 14 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 12 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_12 endpoint_17_56_window_12
private theorem endpoint_17_56_window_14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 14 2 216275522710996584 = some 216275522710996584 := by decide +kernel
private theorem endpoint_17_56_prefix_16 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 16 202259672394747566 = some 216275522710996584 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 14 2 202259672394747566 216275522710996584 216275522710996584 endpoint_17_56_prefix_14 endpoint_17_56_window_14

def endpoint_17_56 : CertifiedEndpoint :=
  ⟨⟨17, 56, 1883⟩, 216275522710996584, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_56_flag endpoint_17_56_sources 16 202259672394747566 216275522710996584 rfl endpoint_17_56_base endpoint_17_56_prefix_16) (by decide)⟩
private def endpoint_17_57_flag : Flag := ⟨17, 57, 1828⟩
private def endpoint_17_57_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_57_base : receiptBase endpoint_17_57_flag endpoint_17_57_sources = some 199591347722233413 := by decide +kernel
private theorem endpoint_17_57_window_0 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 2 199591347722233413 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_window_2 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 2 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 4 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 2 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_window_0 endpoint_17_57_window_2
private theorem endpoint_17_57_window_4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 4 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 6 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 4 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_4 endpoint_17_57_window_4
private theorem endpoint_17_57_window_6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 6 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 8 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 6 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_6 endpoint_17_57_window_6
private theorem endpoint_17_57_window_8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 8 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 10 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 8 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_8 endpoint_17_57_window_8
private theorem endpoint_17_57_window_10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 10 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 12 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 10 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_10 endpoint_17_57_window_10
private theorem endpoint_17_57_window_12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 12 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 14 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 12 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_12 endpoint_17_57_window_12
private theorem endpoint_17_57_window_14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 14 2 217414265424857967 = some 217414265424857967 := by decide +kernel
private theorem endpoint_17_57_prefix_16 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 16 199591347722233413 = some 217414265424857967 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 14 2 199591347722233413 217414265424857967 217414265424857967 endpoint_17_57_prefix_14 endpoint_17_57_window_14

def endpoint_17_57 : CertifiedEndpoint :=
  ⟨⟨17, 57, 1828⟩, 217414265424857967, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_57_flag endpoint_17_57_sources 16 199591347722233413 217414265424857967 rfl endpoint_17_57_base endpoint_17_57_prefix_16) (by decide)⟩
private def endpoint_17_58_flag : Flag := ⟨17, 58, 1772⟩
private def endpoint_17_58_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_58_base : receiptBase endpoint_17_58_flag endpoint_17_58_sources = some 196631109242460659 := by decide +kernel
private theorem endpoint_17_58_window_0 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 2 196631109242460659 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_window_2 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 2 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 4 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 2 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_window_0 endpoint_17_58_window_2
private theorem endpoint_17_58_window_4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 4 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 6 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 4 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_4 endpoint_17_58_window_4
private theorem endpoint_17_58_window_6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 6 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 8 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 6 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_6 endpoint_17_58_window_6
private theorem endpoint_17_58_window_8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 8 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 10 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 8 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_8 endpoint_17_58_window_8
private theorem endpoint_17_58_window_10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 10 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 12 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 10 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_10 endpoint_17_58_window_10
private theorem endpoint_17_58_window_12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 12 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 14 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 12 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_12 endpoint_17_58_window_12
private theorem endpoint_17_58_window_14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 14 2 218340994624460000 = some 218340994624460000 := by decide +kernel
private theorem endpoint_17_58_prefix_16 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 16 196631109242460659 = some 218340994624460000 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 14 2 196631109242460659 218340994624460000 218340994624460000 endpoint_17_58_prefix_14 endpoint_17_58_window_14

def endpoint_17_58 : CertifiedEndpoint :=
  ⟨⟨17, 58, 1772⟩, 218340994624460000, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_58_flag endpoint_17_58_sources 16 196631109242460659 218340994624460000 rfl endpoint_17_58_base endpoint_17_58_prefix_16) (by decide)⟩
private def endpoint_17_59_flag : Flag := ⟨17, 59, 1714⟩
private def endpoint_17_59_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_59_base : receiptBase endpoint_17_59_flag endpoint_17_59_sources = some 195393105092671266 := by decide +kernel
private theorem endpoint_17_59_window_0 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 2 195393105092671266 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_window_2 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 2 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 4 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 2 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_window_0 endpoint_17_59_window_2
private theorem endpoint_17_59_window_4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 4 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 6 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 4 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_4 endpoint_17_59_window_4
private theorem endpoint_17_59_window_6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 6 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 8 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 6 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_6 endpoint_17_59_window_6
private theorem endpoint_17_59_window_8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 8 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 10 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 8 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_8 endpoint_17_59_window_8
private theorem endpoint_17_59_window_10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 10 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 12 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 10 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_10 endpoint_17_59_window_10
private theorem endpoint_17_59_window_12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 12 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 14 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 12 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_12 endpoint_17_59_window_12
private theorem endpoint_17_59_window_14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 14 2 203071951878283056 = some 203071951878283056 := by decide +kernel
private theorem endpoint_17_59_prefix_16 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 16 195393105092671266 = some 203071951878283056 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 14 2 195393105092671266 203071951878283056 203071951878283056 endpoint_17_59_prefix_14 endpoint_17_59_window_14

def endpoint_17_59 : CertifiedEndpoint :=
  ⟨⟨17, 59, 1714⟩, 203071951878283056, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_59_flag endpoint_17_59_sources 16 195393105092671266 203071951878283056 rfl endpoint_17_59_base endpoint_17_59_prefix_16) (by decide)⟩
private def endpoint_17_60_flag : Flag := ⟨17, 60, 1655⟩
private def endpoint_17_60_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_60_base : receiptBase endpoint_17_60_flag endpoint_17_60_sources = some 191559487967946983 := by decide +kernel
private theorem endpoint_17_60_window_0 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 2 191559487967946983 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_window_2 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 2 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 4 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 2 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_window_0 endpoint_17_60_window_2
private theorem endpoint_17_60_window_4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 4 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 6 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 4 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_4 endpoint_17_60_window_4
private theorem endpoint_17_60_window_6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 6 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 8 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 6 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_6 endpoint_17_60_window_6
private theorem endpoint_17_60_window_8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 8 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 10 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 8 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_8 endpoint_17_60_window_8
private theorem endpoint_17_60_window_10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 10 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 12 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 10 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_10 endpoint_17_60_window_10
private theorem endpoint_17_60_window_12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 12 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 14 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 12 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_12 endpoint_17_60_window_12
private theorem endpoint_17_60_window_14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 14 2 203175487044374246 = some 203175487044374246 := by decide +kernel
private theorem endpoint_17_60_prefix_16 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 16 191559487967946983 = some 203175487044374246 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 14 2 191559487967946983 203175487044374246 203175487044374246 endpoint_17_60_prefix_14 endpoint_17_60_window_14

def endpoint_17_60 : CertifiedEndpoint :=
  ⟨⟨17, 60, 1655⟩, 203175487044374246, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_60_flag endpoint_17_60_sources 16 191559487967946983 203175487044374246 rfl endpoint_17_60_base endpoint_17_60_prefix_16) (by decide)⟩
private def endpoint_17_61_flag : Flag := ⟨17, 61, 1594⟩
private def endpoint_17_61_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_61_base : receiptBase endpoint_17_61_flag endpoint_17_61_sources = some 187293244986841625 := by decide +kernel
private theorem endpoint_17_61_window_0 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 2 187293244986841625 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_window_2 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 2 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 4 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 2 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_window_0 endpoint_17_61_window_2
private theorem endpoint_17_61_window_4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 4 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 6 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 4 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_4 endpoint_17_61_window_4
private theorem endpoint_17_61_window_6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 6 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 8 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 6 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_6 endpoint_17_61_window_6
private theorem endpoint_17_61_window_8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 8 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 10 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 8 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_8 endpoint_17_61_window_8
private theorem endpoint_17_61_window_10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 10 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 12 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 10 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_10 endpoint_17_61_window_10
private theorem endpoint_17_61_window_12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 12 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 14 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 12 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_12 endpoint_17_61_window_12
private theorem endpoint_17_61_window_14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 14 2 202985170314859222 = some 202985170314859222 := by decide +kernel
private theorem endpoint_17_61_prefix_16 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 16 187293244986841625 = some 202985170314859222 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 14 2 187293244986841625 202985170314859222 202985170314859222 endpoint_17_61_prefix_14 endpoint_17_61_window_14

def endpoint_17_61 : CertifiedEndpoint :=
  ⟨⟨17, 61, 1594⟩, 202985170314859222, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_61_flag endpoint_17_61_sources 16 187293244986841625 202985170314859222 rfl endpoint_17_61_base endpoint_17_61_prefix_16) (by decide)⟩
private def endpoint_17_62_flag : Flag := ⟨17, 62, 1532⟩
private def endpoint_17_62_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_62_base : receiptBase endpoint_17_62_flag endpoint_17_62_sources = some 182701859645935286 := by decide +kernel
private theorem endpoint_17_62_window_0 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 2 182701859645935286 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_window_2 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 2 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 4 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 2 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_window_0 endpoint_17_62_window_2
private theorem endpoint_17_62_window_4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 4 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 6 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 4 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_4 endpoint_17_62_window_4
private theorem endpoint_17_62_window_6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 6 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 8 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 6 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_6 endpoint_17_62_window_6
private theorem endpoint_17_62_window_8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 8 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 10 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 8 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_8 endpoint_17_62_window_8
private theorem endpoint_17_62_window_10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 10 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 12 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 10 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_10 endpoint_17_62_window_10
private theorem endpoint_17_62_window_12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 12 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 14 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 12 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_12 endpoint_17_62_window_12
private theorem endpoint_17_62_window_14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 14 2 202561811383766784 = some 202561811383766784 := by decide +kernel
private theorem endpoint_17_62_prefix_16 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 16 182701859645935286 = some 202561811383766784 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 14 2 182701859645935286 202561811383766784 202561811383766784 endpoint_17_62_prefix_14 endpoint_17_62_window_14

def endpoint_17_62 : CertifiedEndpoint :=
  ⟨⟨17, 62, 1532⟩, 202561811383766784, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_62_flag endpoint_17_62_sources 16 182701859645935286 202561811383766784 rfl endpoint_17_62_base endpoint_17_62_prefix_16) (by decide)⟩
private def endpoint_17_63_flag : Flag := ⟨17, 63, 1469⟩
private def endpoint_17_63_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_63_base : receiptBase endpoint_17_63_flag endpoint_17_63_sources = some 179230660428905857 := by decide +kernel
private theorem endpoint_17_63_window_0 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 2 179230660428905857 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_window_2 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 2 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 4 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 2 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_window_0 endpoint_17_63_window_2
private theorem endpoint_17_63_window_4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 4 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 6 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 4 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_4 endpoint_17_63_window_4
private theorem endpoint_17_63_window_6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 6 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 8 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 6 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_6 endpoint_17_63_window_6
private theorem endpoint_17_63_window_8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 8 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 10 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 8 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_8 endpoint_17_63_window_8
private theorem endpoint_17_63_window_10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 10 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 12 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 10 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_10 endpoint_17_63_window_10
private theorem endpoint_17_63_window_12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 12 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 14 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 12 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_12 endpoint_17_63_window_12
private theorem endpoint_17_63_window_14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 14 2 186873998892639779 = some 186873998892639779 := by decide +kernel
private theorem endpoint_17_63_prefix_16 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 16 179230660428905857 = some 186873998892639779 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 14 2 179230660428905857 186873998892639779 186873998892639779 endpoint_17_63_prefix_14 endpoint_17_63_window_14

def endpoint_17_63 : CertifiedEndpoint :=
  ⟨⟨17, 63, 1469⟩, 186873998892639779, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_63_flag endpoint_17_63_sources 16 179230660428905857 186873998892639779 rfl endpoint_17_63_base endpoint_17_63_prefix_16) (by decide)⟩
private def endpoint_17_64_flag : Flag := ⟨17, 64, 1403⟩
private def endpoint_17_64_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_64_base : receiptBase endpoint_17_64_flag endpoint_17_64_sources = some 173673263737356219 := by decide +kernel
private theorem endpoint_17_64_window_0 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 2 173673263737356219 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_window_2 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 2 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 4 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 2 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_window_0 endpoint_17_64_window_2
private theorem endpoint_17_64_window_4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 4 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 6 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 4 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_4 endpoint_17_64_window_4
private theorem endpoint_17_64_window_6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 6 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 8 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 6 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_6 endpoint_17_64_window_6
private theorem endpoint_17_64_window_8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 8 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 10 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 8 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_8 endpoint_17_64_window_8
private theorem endpoint_17_64_window_10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 10 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 12 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 10 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_10 endpoint_17_64_window_10
private theorem endpoint_17_64_window_12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 12 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 14 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 12 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_12 endpoint_17_64_window_12
private theorem endpoint_17_64_window_14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 14 2 185550452377541246 = some 185550452377541246 := by decide +kernel
private theorem endpoint_17_64_prefix_16 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 16 173673263737356219 = some 185550452377541246 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 14 2 173673263737356219 185550452377541246 185550452377541246 endpoint_17_64_prefix_14 endpoint_17_64_window_14

def endpoint_17_64 : CertifiedEndpoint :=
  ⟨⟨17, 64, 1403⟩, 185550452377541246, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_64_flag endpoint_17_64_sources 16 173673263737356219 185550452377541246 rfl endpoint_17_64_base endpoint_17_64_prefix_16) (by decide)⟩
private def endpoint_17_65_flag : Flag := ⟨17, 65, 1336⟩
private def endpoint_17_65_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_65_base : receiptBase endpoint_17_65_flag endpoint_17_65_sources = some 167766686637778091 := by decide +kernel
private theorem endpoint_17_65_window_0 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 2 167766686637778091 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_window_2 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 2 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 4 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 2 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_window_0 endpoint_17_65_window_2
private theorem endpoint_17_65_window_4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 4 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 6 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 4 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_4 endpoint_17_65_window_4
private theorem endpoint_17_65_window_6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 6 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 8 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 6 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_6 endpoint_17_65_window_6
private theorem endpoint_17_65_window_8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 8 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 10 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 8 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_8 endpoint_17_65_window_8
private theorem endpoint_17_65_window_10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 10 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 12 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 10 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_10 endpoint_17_65_window_10
private theorem endpoint_17_65_window_12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 12 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 14 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 12 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_12 endpoint_17_65_window_12
private theorem endpoint_17_65_window_14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 14 2 183976777852419372 = some 183976777852419372 := by decide +kernel
private theorem endpoint_17_65_prefix_16 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 16 167766686637778091 = some 183976777852419372 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 14 2 167766686637778091 183976777852419372 183976777852419372 endpoint_17_65_prefix_14 endpoint_17_65_window_14

def endpoint_17_65 : CertifiedEndpoint :=
  ⟨⟨17, 65, 1336⟩, 183976777852419372, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_65_flag endpoint_17_65_sources 16 167766686637778091 183976777852419372 rfl endpoint_17_65_base endpoint_17_65_prefix_16) (by decide)⟩
private def endpoint_17_66_flag : Flag := ⟨17, 66, 1268⟩
private def endpoint_17_66_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_66_base : receiptBase endpoint_17_66_flag endpoint_17_66_sources = some 161505843487814814 := by decide +kernel
private theorem endpoint_17_66_window_0 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 2 161505843487814814 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_window_2 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 2 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 4 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 2 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_window_0 endpoint_17_66_window_2
private theorem endpoint_17_66_window_4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 4 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 6 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 4 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_4 endpoint_17_66_window_4
private theorem endpoint_17_66_window_6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 6 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 8 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 6 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_6 endpoint_17_66_window_6
private theorem endpoint_17_66_window_8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 8 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 10 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 8 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_8 endpoint_17_66_window_8
private theorem endpoint_17_66_window_10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 10 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 12 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 10 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_10 endpoint_17_66_window_10
private theorem endpoint_17_66_window_12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 12 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 14 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 12 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_12 endpoint_17_66_window_12
private theorem endpoint_17_66_window_14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 14 2 182149032438402020 = some 182149032438402020 := by decide +kernel
private theorem endpoint_17_66_prefix_16 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 16 161505843487814814 = some 182149032438402020 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 14 2 161505843487814814 182149032438402020 182149032438402020 endpoint_17_66_prefix_14 endpoint_17_66_window_14

def endpoint_17_66 : CertifiedEndpoint :=
  ⟨⟨17, 66, 1268⟩, 182149032438402020, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_66_flag endpoint_17_66_sources 16 161505843487814814 182149032438402020 rfl endpoint_17_66_base endpoint_17_66_prefix_16) (by decide)⟩
private def endpoint_17_67_flag : Flag := ⟨17, 67, 1197⟩
private def endpoint_17_67_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_17_67_base : receiptBase endpoint_17_67_flag endpoint_17_67_sources = some 156134211636200298 := by decide +kernel
private theorem endpoint_17_67_window_0 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 2 156134211636200298 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_window_2 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 2 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 4 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 2 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_window_0 endpoint_17_67_window_2
private theorem endpoint_17_67_window_4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 4 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 6 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 4 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_4 endpoint_17_67_window_4
private theorem endpoint_17_67_window_6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 6 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 8 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 6 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_6 endpoint_17_67_window_6
private theorem endpoint_17_67_window_8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 8 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 10 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 8 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_8 endpoint_17_67_window_8
private theorem endpoint_17_67_window_10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 10 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 12 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 10 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_10 endpoint_17_67_window_10
private theorem endpoint_17_67_window_12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 12 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 14 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 12 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_12 endpoint_17_67_window_12
private theorem endpoint_17_67_window_14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 14 2 169045256684540145 = some 169045256684540145 := by decide +kernel
private theorem endpoint_17_67_prefix_16 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 16 156134211636200298 = some 169045256684540145 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 14 2 156134211636200298 169045256684540145 169045256684540145 endpoint_17_67_prefix_14 endpoint_17_67_window_14

def endpoint_17_67 : CertifiedEndpoint :=
  ⟨⟨17, 67, 1197⟩, 169045256684540145, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_17_67_flag endpoint_17_67_sources 16 156134211636200298 169045256684540145 rfl endpoint_17_67_base endpoint_17_67_prefix_16) (by decide)⟩
private def endpoint_17_68_flag : Flag := ⟨17, 68, 1125⟩
private def endpoint_17_68_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_17_68_base : receiptBase endpoint_17_68_flag endpoint_17_68_sources = some 148843333587284496 := by decide +kernel
private theorem endpoint_17_68_window_0 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 2 148843333587284496 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_window_2 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 2 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 4 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 2 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_window_0 endpoint_17_68_window_2
private theorem endpoint_17_68_window_4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 4 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 6 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 4 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_4 endpoint_17_68_window_4
private theorem endpoint_17_68_window_6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 6 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 8 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 6 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_6 endpoint_17_68_window_6
private theorem endpoint_17_68_window_8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 8 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 10 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 8 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_8 endpoint_17_68_window_8
private theorem endpoint_17_68_window_10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 10 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 12 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 10 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_10 endpoint_17_68_window_10
private theorem endpoint_17_68_window_12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 12 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 14 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 12 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_12 endpoint_17_68_window_12
private theorem endpoint_17_68_window_14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 14 2 166353539727895362 = some 166353539727895362 := by decide +kernel
private theorem endpoint_17_68_prefix_16 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 16 148843333587284496 = some 166353539727895362 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 14 2 148843333587284496 166353539727895362 166353539727895362 endpoint_17_68_prefix_14 endpoint_17_68_window_14

def endpoint_17_68 : CertifiedEndpoint :=
  ⟨⟨17, 68, 1125⟩, 166353539727895362, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_17_68_flag endpoint_17_68_sources 16 148843333587284496 166353539727895362 rfl endpoint_17_68_base endpoint_17_68_prefix_16) (by decide)⟩
private def endpoint_17_69_flag : Flag := ⟨17, 69, 1051⟩
private def endpoint_17_69_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_69_base : receiptBase endpoint_17_69_flag endpoint_17_69_sources = some 142356306595769164 := by decide +kernel
private theorem endpoint_17_69_window_0 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 2 142356306595769164 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_window_2 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 2 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 4 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 2 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_window_0 endpoint_17_69_window_2
private theorem endpoint_17_69_window_4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 4 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 6 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 4 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_4 endpoint_17_69_window_4
private theorem endpoint_17_69_window_6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 6 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 8 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 6 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_6 endpoint_17_69_window_6
private theorem endpoint_17_69_window_8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 8 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 10 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 8 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_8 endpoint_17_69_window_8
private theorem endpoint_17_69_window_10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 10 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 12 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 10 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_10 endpoint_17_69_window_10
private theorem endpoint_17_69_window_12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 12 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 14 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 12 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_12 endpoint_17_69_window_12
private theorem endpoint_17_69_window_14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 14 2 153835766626514544 = some 153835766626514544 := by decide +kernel
private theorem endpoint_17_69_prefix_16 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 16 142356306595769164 = some 153835766626514544 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 14 2 142356306595769164 153835766626514544 153835766626514544 endpoint_17_69_prefix_14 endpoint_17_69_window_14

def endpoint_17_69 : CertifiedEndpoint :=
  ⟨⟨17, 69, 1051⟩, 153835766626514544, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_69_flag endpoint_17_69_sources 16 142356306595769164 153835766626514544 rfl endpoint_17_69_base endpoint_17_69_prefix_16) (by decide)⟩
def endpoint_17_70 : CertifiedEndpoint :=
  ⟨⟨17, 70, 975⟩, 243196546293922263, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_71 : CertifiedEndpoint :=
  ⟨⟨17, 71, 896⟩, 226180705228377791, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_72 : CertifiedEndpoint :=
  ⟨⟨17, 72, 816⟩, 208218977165249044, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_73 : CertifiedEndpoint :=
  ⟨⟨17, 73, 733⟩, 188753191382707274, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_74 : CertifiedEndpoint :=
  ⟨⟨17, 74, 648⟩, 168021956464999992, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_75 : CertifiedEndpoint :=
  ⟨⟨17, 75, 560⟩, 145718492414546023, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_76 : CertifiedEndpoint :=
  ⟨⟨17, 76, 470⟩, 122089929242259586, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_77 : CertifiedEndpoint :=
  ⟨⟨17, 77, 377⟩, 96820965523892798, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_78 : CertifiedEndpoint :=
  ⟨⟨17, 78, 281⟩, 69873254839445473, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_79 : CertifiedEndpoint :=
  ⟨⟨17, 79, 183⟩, 41506709339831892, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_80 : CertifiedEndpoint :=
  ⟨⟨17, 80, 81⟩, 11090726176556289, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_18 : CertifiedEndpoint :=
  ⟨⟨18, 18, 3115⟩, 137972064853067919, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_19 : CertifiedEndpoint :=
  ⟨⟨18, 19, 3086⟩, 141238519518510180, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_20 : CertifiedEndpoint :=
  ⟨⟨18, 20, 3056⟩, 144371328599171592, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_21 : CertifiedEndpoint :=
  ⟨⟨18, 21, 3026⟩, 156527872108480235, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_22 : CertifiedEndpoint :=
  ⟨⟨18, 22, 2995⟩, 168352303279189577, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_23 : CertifiedEndpoint :=
  ⟨⟨18, 23, 2964⟩, 179892074137154741, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_24 : CertifiedEndpoint :=
  ⟨⟨18, 24, 2932⟩, 191081658985870180, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_25 : CertifiedEndpoint :=
  ⟨⟨18, 25, 2900⟩, 201977546686516229, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_26 : CertifiedEndpoint :=
  ⟨⟨18, 26, 2867⟩, 212505174707262129, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_27 : CertifiedEndpoint :=
  ⟨⟨18, 27, 2834⟩, 222730068744613427, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_28 : CertifiedEndpoint :=
  ⟨⟨18, 28, 2800⟩, 232568629431414152, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_29 : CertifiedEndpoint :=
  ⟨⟨18, 29, 2766⟩, 242095419299495063, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_30 : CertifiedEndpoint :=
  ⟨⟨18, 30, 2731⟩, 251217802146374977, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_18_31_flag : Flag := ⟨18, 31, 2696⟩
private def endpoint_18_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_31_base : receiptBase endpoint_18_31_flag endpoint_18_31_sources = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_window_0 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_window_2 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 2 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 4 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 2 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_window_0 endpoint_18_31_window_2
private theorem endpoint_18_31_window_4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 4 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 6 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 4 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_4 endpoint_18_31_window_4
private theorem endpoint_18_31_window_6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 6 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 8 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 6 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_6 endpoint_18_31_window_6
private theorem endpoint_18_31_window_8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 8 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 10 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 8 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_8 endpoint_18_31_window_8
private theorem endpoint_18_31_window_10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 10 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 12 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 10 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_10 endpoint_18_31_window_10
private theorem endpoint_18_31_window_12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 12 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 14 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 12 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_12 endpoint_18_31_window_12
private theorem endpoint_18_31_window_14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 14 2 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 16 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 14 2 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_14 endpoint_18_31_window_14
private theorem endpoint_18_31_window_16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 16 1 172672446232380433 = some 172672446232380433 := by decide +kernel
private theorem endpoint_18_31_prefix_17 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 17 172672446232380433 = some 172672446232380433 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 16 1 172672446232380433 172672446232380433 172672446232380433 endpoint_18_31_prefix_16 endpoint_18_31_window_16

def endpoint_18_31 : CertifiedEndpoint :=
  ⟨⟨18, 31, 2696⟩, 172672446232380433, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_31_flag endpoint_18_31_sources 17 172672446232380433 172672446232380433 rfl endpoint_18_31_base endpoint_18_31_prefix_17) (by decide)⟩
private def endpoint_18_32_flag : Flag := ⟨18, 32, 2660⟩
private def endpoint_18_32_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_32_base : receiptBase endpoint_18_32_flag endpoint_18_32_sources = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_window_0 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_window_2 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 2 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 4 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 2 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_window_0 endpoint_18_32_window_2
private theorem endpoint_18_32_window_4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 4 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 6 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 4 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_4 endpoint_18_32_window_4
private theorem endpoint_18_32_window_6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 6 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 8 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 6 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_6 endpoint_18_32_window_6
private theorem endpoint_18_32_window_8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 8 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 10 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 8 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_8 endpoint_18_32_window_8
private theorem endpoint_18_32_window_10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 10 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 12 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 10 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_10 endpoint_18_32_window_10
private theorem endpoint_18_32_window_12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 12 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 14 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 12 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_12 endpoint_18_32_window_12
private theorem endpoint_18_32_window_14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 14 2 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 16 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 14 2 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_14 endpoint_18_32_window_14
private theorem endpoint_18_32_window_16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 16 1 175199212457000241 = some 175199212457000241 := by decide +kernel
private theorem endpoint_18_32_prefix_17 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 17 175199212457000241 = some 175199212457000241 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 16 1 175199212457000241 175199212457000241 175199212457000241 endpoint_18_32_prefix_16 endpoint_18_32_window_16

def endpoint_18_32 : CertifiedEndpoint :=
  ⟨⟨18, 32, 2660⟩, 175199212457000241, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_32_flag endpoint_18_32_sources 17 175199212457000241 175199212457000241 rfl endpoint_18_32_base endpoint_18_32_prefix_17) (by decide)⟩
private def endpoint_18_33_flag : Flag := ⟨18, 33, 2623⟩
private def endpoint_18_33_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_33_base : receiptBase endpoint_18_33_flag endpoint_18_33_sources = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_window_0 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_window_2 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 2 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 4 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 2 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_window_0 endpoint_18_33_window_2
private theorem endpoint_18_33_window_4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 4 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 6 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 4 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_4 endpoint_18_33_window_4
private theorem endpoint_18_33_window_6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 6 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 8 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 6 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_6 endpoint_18_33_window_6
private theorem endpoint_18_33_window_8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 8 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 10 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 8 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_8 endpoint_18_33_window_8
private theorem endpoint_18_33_window_10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 10 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 12 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 10 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_10 endpoint_18_33_window_10
private theorem endpoint_18_33_window_12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 12 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 14 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 12 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_12 endpoint_18_33_window_12
private theorem endpoint_18_33_window_14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 14 2 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 16 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 14 2 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_14 endpoint_18_33_window_14
private theorem endpoint_18_33_window_16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 16 1 177317840278677497 = some 177317840278677497 := by decide +kernel
private theorem endpoint_18_33_prefix_17 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 17 177317840278677497 = some 177317840278677497 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 16 1 177317840278677497 177317840278677497 177317840278677497 endpoint_18_33_prefix_16 endpoint_18_33_window_16

def endpoint_18_33 : CertifiedEndpoint :=
  ⟨⟨18, 33, 2623⟩, 177317840278677497, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_33_flag endpoint_18_33_sources 17 177317840278677497 177317840278677497 rfl endpoint_18_33_base endpoint_18_33_prefix_17) (by decide)⟩
private def endpoint_18_34_flag : Flag := ⟨18, 34, 2586⟩
private def endpoint_18_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_34_base : receiptBase endpoint_18_34_flag endpoint_18_34_sources = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_window_0 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_window_2 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 2 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 4 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 2 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_window_0 endpoint_18_34_window_2
private theorem endpoint_18_34_window_4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 4 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 6 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 4 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_4 endpoint_18_34_window_4
private theorem endpoint_18_34_window_6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 6 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 8 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 6 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_6 endpoint_18_34_window_6
private theorem endpoint_18_34_window_8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 8 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 10 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 8 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_8 endpoint_18_34_window_8
private theorem endpoint_18_34_window_10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 10 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 12 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 10 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_10 endpoint_18_34_window_10
private theorem endpoint_18_34_window_12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 12 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 14 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 12 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_12 endpoint_18_34_window_12
private theorem endpoint_18_34_window_14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 14 2 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 16 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 14 2 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_14 endpoint_18_34_window_14
private theorem endpoint_18_34_window_16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 16 1 179698737719485671 = some 179698737719485671 := by decide +kernel
private theorem endpoint_18_34_prefix_17 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 17 179698737719485671 = some 179698737719485671 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 16 1 179698737719485671 179698737719485671 179698737719485671 endpoint_18_34_prefix_16 endpoint_18_34_window_16

def endpoint_18_34 : CertifiedEndpoint :=
  ⟨⟨18, 34, 2586⟩, 179698737719485671, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_34_flag endpoint_18_34_sources 17 179698737719485671 179698737719485671 rfl endpoint_18_34_base endpoint_18_34_prefix_17) (by decide)⟩
private def endpoint_18_35_flag : Flag := ⟨18, 35, 2548⟩
private def endpoint_18_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_35_base : receiptBase endpoint_18_35_flag endpoint_18_35_sources = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_window_0 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_window_2 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 2 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 4 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 2 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_window_0 endpoint_18_35_window_2
private theorem endpoint_18_35_window_4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 4 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 6 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 4 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_4 endpoint_18_35_window_4
private theorem endpoint_18_35_window_6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 6 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 8 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 6 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_6 endpoint_18_35_window_6
private theorem endpoint_18_35_window_8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 8 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 10 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 8 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_8 endpoint_18_35_window_8
private theorem endpoint_18_35_window_10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 10 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 12 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 10 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_10 endpoint_18_35_window_10
private theorem endpoint_18_35_window_12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 12 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 14 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 12 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_12 endpoint_18_35_window_12
private theorem endpoint_18_35_window_14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 14 2 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 16 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 14 2 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_14 endpoint_18_35_window_14
private theorem endpoint_18_35_window_16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 16 1 181470321397882343 = some 181470321397882343 := by decide +kernel
private theorem endpoint_18_35_prefix_17 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 17 181470321397882343 = some 181470321397882343 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 16 1 181470321397882343 181470321397882343 181470321397882343 endpoint_18_35_prefix_16 endpoint_18_35_window_16

def endpoint_18_35 : CertifiedEndpoint :=
  ⟨⟨18, 35, 2548⟩, 181470321397882343, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_35_flag endpoint_18_35_sources 17 181470321397882343 181470321397882343 rfl endpoint_18_35_base endpoint_18_35_prefix_17) (by decide)⟩
private def endpoint_18_36_flag : Flag := ⟨18, 36, 2509⟩
private def endpoint_18_36_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_36_base : receiptBase endpoint_18_36_flag endpoint_18_36_sources = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_window_0 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_window_2 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 2 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 4 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 2 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_window_0 endpoint_18_36_window_2
private theorem endpoint_18_36_window_4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 4 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 6 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 4 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_4 endpoint_18_36_window_4
private theorem endpoint_18_36_window_6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 6 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 8 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 6 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_6 endpoint_18_36_window_6
private theorem endpoint_18_36_window_8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 8 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 10 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 8 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_8 endpoint_18_36_window_8
private theorem endpoint_18_36_window_10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 10 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 12 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 10 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_10 endpoint_18_36_window_10
private theorem endpoint_18_36_window_12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 12 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 14 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 12 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_12 endpoint_18_36_window_12
private theorem endpoint_18_36_window_14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 14 2 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 16 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 14 2 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_14 endpoint_18_36_window_14
private theorem endpoint_18_36_window_16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 16 1 183040406105813315 = some 183040406105813315 := by decide +kernel
private theorem endpoint_18_36_prefix_17 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 17 183040406105813315 = some 183040406105813315 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 16 1 183040406105813315 183040406105813315 183040406105813315 endpoint_18_36_prefix_16 endpoint_18_36_window_16

def endpoint_18_36 : CertifiedEndpoint :=
  ⟨⟨18, 36, 2509⟩, 183040406105813315, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_36_flag endpoint_18_36_sources 17 183040406105813315 183040406105813315 rfl endpoint_18_36_base endpoint_18_36_prefix_17) (by decide)⟩
private def endpoint_18_37_flag : Flag := ⟨18, 37, 2470⟩
private def endpoint_18_37_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_37_base : receiptBase endpoint_18_37_flag endpoint_18_37_sources = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_window_0 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_window_2 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 2 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 4 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 2 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_window_0 endpoint_18_37_window_2
private theorem endpoint_18_37_window_4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 4 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 6 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 4 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_4 endpoint_18_37_window_4
private theorem endpoint_18_37_window_6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 6 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 8 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 6 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_6 endpoint_18_37_window_6
private theorem endpoint_18_37_window_8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 8 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 10 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 8 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_8 endpoint_18_37_window_8
private theorem endpoint_18_37_window_10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 10 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 12 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 10 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_10 endpoint_18_37_window_10
private theorem endpoint_18_37_window_12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 12 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 14 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 12 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_12 endpoint_18_37_window_12
private theorem endpoint_18_37_window_14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 14 2 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 16 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 14 2 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_14 endpoint_18_37_window_14
private theorem endpoint_18_37_window_16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 16 1 184477535055206817 = some 184477535055206817 := by decide +kernel
private theorem endpoint_18_37_prefix_17 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 17 184477535055206817 = some 184477535055206817 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 16 1 184477535055206817 184477535055206817 184477535055206817 endpoint_18_37_prefix_16 endpoint_18_37_window_16

def endpoint_18_37 : CertifiedEndpoint :=
  ⟨⟨18, 37, 2470⟩, 184477535055206817, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_37_flag endpoint_18_37_sources 17 184477535055206817 184477535055206817 rfl endpoint_18_37_base endpoint_18_37_prefix_17) (by decide)⟩
private def endpoint_18_38_flag : Flag := ⟨18, 38, 2430⟩
private def endpoint_18_38_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_38_base : receiptBase endpoint_18_38_flag endpoint_18_38_sources = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_window_0 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_window_2 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 2 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 4 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 2 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_window_0 endpoint_18_38_window_2
private theorem endpoint_18_38_window_4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 4 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 6 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 4 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_4 endpoint_18_38_window_4
private theorem endpoint_18_38_window_6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 6 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 8 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 6 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_6 endpoint_18_38_window_6
private theorem endpoint_18_38_window_8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 8 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 10 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 8 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_8 endpoint_18_38_window_8
private theorem endpoint_18_38_window_10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 10 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 12 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 10 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_10 endpoint_18_38_window_10
private theorem endpoint_18_38_window_12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 12 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 14 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 12 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_12 endpoint_18_38_window_12
private theorem endpoint_18_38_window_14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 14 2 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 16 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 14 2 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_14 endpoint_18_38_window_14
private theorem endpoint_18_38_window_16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 16 1 185706433096993482 = some 185706433096993482 := by decide +kernel
private theorem endpoint_18_38_prefix_17 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 17 185706433096993482 = some 185706433096993482 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 16 1 185706433096993482 185706433096993482 185706433096993482 endpoint_18_38_prefix_16 endpoint_18_38_window_16

def endpoint_18_38 : CertifiedEndpoint :=
  ⟨⟨18, 38, 2430⟩, 185706433096993482, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_38_flag endpoint_18_38_sources 17 185706433096993482 185706433096993482 rfl endpoint_18_38_base endpoint_18_38_prefix_17) (by decide)⟩
private def endpoint_18_39_flag : Flag := ⟨18, 39, 2389⟩
private def endpoint_18_39_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_39_base : receiptBase endpoint_18_39_flag endpoint_18_39_sources = some 186722051278317457 := by decide +kernel
private theorem endpoint_18_39_window_0 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 2 186722051278317457 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_window_2 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 2 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 4 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 2 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_window_0 endpoint_18_39_window_2
private theorem endpoint_18_39_window_4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 4 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 6 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 4 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_4 endpoint_18_39_window_4
private theorem endpoint_18_39_window_6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 6 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 8 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 6 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_6 endpoint_18_39_window_6
private theorem endpoint_18_39_window_8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 8 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 10 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 8 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_8 endpoint_18_39_window_8
private theorem endpoint_18_39_window_10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 10 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 12 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 10 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_10 endpoint_18_39_window_10
private theorem endpoint_18_39_window_12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 12 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 14 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 12 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_12 endpoint_18_39_window_12
private theorem endpoint_18_39_window_14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 14 2 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 16 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 14 2 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_14 endpoint_18_39_window_14
private theorem endpoint_18_39_window_16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 16 1 187074264779171106 = some 187074264779171106 := by decide +kernel
private theorem endpoint_18_39_prefix_17 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 17 186722051278317457 = some 187074264779171106 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 16 1 186722051278317457 187074264779171106 187074264779171106 endpoint_18_39_prefix_16 endpoint_18_39_window_16

def endpoint_18_39 : CertifiedEndpoint :=
  ⟨⟨18, 39, 2389⟩, 187074264779171106, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_39_flag endpoint_18_39_sources 17 186722051278317457 187074264779171106 rfl endpoint_18_39_base endpoint_18_39_prefix_17) (by decide)⟩
private def endpoint_18_40_flag : Flag := ⟨18, 40, 2348⟩
private def endpoint_18_40_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_40_base : receiptBase endpoint_18_40_flag endpoint_18_40_sources = some 187597981763962824 := by decide +kernel
private theorem endpoint_18_40_window_0 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 2 187597981763962824 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_window_2 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 2 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 4 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 2 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_window_0 endpoint_18_40_window_2
private theorem endpoint_18_40_window_4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 4 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 6 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 4 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_4 endpoint_18_40_window_4
private theorem endpoint_18_40_window_6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 6 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 8 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 6 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_6 endpoint_18_40_window_6
private theorem endpoint_18_40_window_8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 8 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 10 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 8 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_8 endpoint_18_40_window_8
private theorem endpoint_18_40_window_10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 10 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 12 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 10 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_10 endpoint_18_40_window_10
private theorem endpoint_18_40_window_12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 12 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 14 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 12 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_12 endpoint_18_40_window_12
private theorem endpoint_18_40_window_14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 14 2 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 16 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 14 2 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_14 endpoint_18_40_window_14
private theorem endpoint_18_40_window_16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 16 1 191751676655427320 = some 191751676655427320 := by decide +kernel
private theorem endpoint_18_40_prefix_17 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 17 187597981763962824 = some 191751676655427320 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 16 1 187597981763962824 191751676655427320 191751676655427320 endpoint_18_40_prefix_16 endpoint_18_40_window_16

def endpoint_18_40 : CertifiedEndpoint :=
  ⟨⟨18, 40, 2348⟩, 191751676655427320, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_40_flag endpoint_18_40_sources 17 187597981763962824 191751676655427320 rfl endpoint_18_40_base endpoint_18_40_prefix_17) (by decide)⟩
private def endpoint_18_41_flag : Flag := ⟨18, 41, 2306⟩
private def endpoint_18_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_41_base : receiptBase endpoint_18_41_flag endpoint_18_41_sources = some 188253900452004363 := by decide +kernel
private theorem endpoint_18_41_window_0 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 2 188253900452004363 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_window_2 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 2 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 4 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 2 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_window_0 endpoint_18_41_window_2
private theorem endpoint_18_41_window_4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 4 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 6 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 4 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_4 endpoint_18_41_window_4
private theorem endpoint_18_41_window_6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 6 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 8 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 6 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_6 endpoint_18_41_window_6
private theorem endpoint_18_41_window_8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 8 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 10 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 8 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_8 endpoint_18_41_window_8
private theorem endpoint_18_41_window_10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 10 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 12 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 10 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_10 endpoint_18_41_window_10
private theorem endpoint_18_41_window_12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 12 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 14 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 12 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_12 endpoint_18_41_window_12
private theorem endpoint_18_41_window_14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 14 2 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 16 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 14 2 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_14 endpoint_18_41_window_14
private theorem endpoint_18_41_window_16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 16 1 196266932253538919 = some 196266932253538919 := by decide +kernel
private theorem endpoint_18_41_prefix_17 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 17 188253900452004363 = some 196266932253538919 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 16 1 188253900452004363 196266932253538919 196266932253538919 endpoint_18_41_prefix_16 endpoint_18_41_window_16

def endpoint_18_41 : CertifiedEndpoint :=
  ⟨⟨18, 41, 2306⟩, 196266932253538919, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_41_flag endpoint_18_41_sources 17 188253900452004363 196266932253538919 rfl endpoint_18_41_base endpoint_18_41_prefix_17) (by decide)⟩
private def endpoint_18_42_flag : Flag := ⟨18, 42, 2263⟩
private def endpoint_18_42_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_18_42_base : receiptBase endpoint_18_42_flag endpoint_18_42_sources = some 193484322825738278 := by decide +kernel
private theorem endpoint_18_42_window_0 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 2 193484322825738278 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_window_2 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 2 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 4 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 2 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_window_0 endpoint_18_42_window_2
private theorem endpoint_18_42_window_4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 4 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 6 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 4 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_4 endpoint_18_42_window_4
private theorem endpoint_18_42_window_6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 6 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 8 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 6 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_6 endpoint_18_42_window_6
private theorem endpoint_18_42_window_8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 8 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 10 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 8 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_8 endpoint_18_42_window_8
private theorem endpoint_18_42_window_10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 10 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 12 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 10 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_10 endpoint_18_42_window_10
private theorem endpoint_18_42_window_12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 12 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 14 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 12 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_12 endpoint_18_42_window_12
private theorem endpoint_18_42_window_14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 14 2 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 16 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 14 2 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_14 endpoint_18_42_window_14
private theorem endpoint_18_42_window_16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 16 1 193976951229146418 = some 193976951229146418 := by decide +kernel
private theorem endpoint_18_42_prefix_17 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 17 193484322825738278 = some 193976951229146418 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 16 1 193484322825738278 193976951229146418 193976951229146418 endpoint_18_42_prefix_16 endpoint_18_42_window_16

def endpoint_18_42 : CertifiedEndpoint :=
  ⟨⟨18, 42, 2263⟩, 193976951229146418, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_18_42_flag endpoint_18_42_sources 17 193484322825738278 193976951229146418 rfl endpoint_18_42_base endpoint_18_42_prefix_17) (by decide)⟩
private def endpoint_18_43_flag : Flag := ⟨18, 43, 2219⟩
private def endpoint_18_43_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_43_base : receiptBase endpoint_18_43_flag endpoint_18_43_sources = some 194167039346930510 := by decide +kernel
private theorem endpoint_18_43_window_0 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 2 194167039346930510 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_window_2 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 2 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 4 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 2 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_window_0 endpoint_18_43_window_2
private theorem endpoint_18_43_window_4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 4 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 6 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 4 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_4 endpoint_18_43_window_4
private theorem endpoint_18_43_window_6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 6 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 8 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 6 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_6 endpoint_18_43_window_6
private theorem endpoint_18_43_window_8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 8 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 10 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 8 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_8 endpoint_18_43_window_8
private theorem endpoint_18_43_window_10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 10 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 12 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 10 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_10 endpoint_18_43_window_10
private theorem endpoint_18_43_window_12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 12 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 14 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 12 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_12 endpoint_18_43_window_12
private theorem endpoint_18_43_window_14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 14 2 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 16 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 14 2 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_14 endpoint_18_43_window_14
private theorem endpoint_18_43_window_16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 16 1 195667722783421052 = some 195667722783421052 := by decide +kernel
private theorem endpoint_18_43_prefix_17 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 17 194167039346930510 = some 195667722783421052 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 16 1 194167039346930510 195667722783421052 195667722783421052 endpoint_18_43_prefix_16 endpoint_18_43_window_16

def endpoint_18_43 : CertifiedEndpoint :=
  ⟨⟨18, 43, 2219⟩, 195667722783421052, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_43_flag endpoint_18_43_sources 17 194167039346930510 195667722783421052 rfl endpoint_18_43_base endpoint_18_43_prefix_17) (by decide)⟩
private def endpoint_18_44_flag : Flag := ⟨18, 44, 2174⟩
private def endpoint_18_44_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_44_base : receiptBase endpoint_18_44_flag endpoint_18_44_sources = some 194191915802995931 := by decide +kernel
private theorem endpoint_18_44_window_0 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 2 194191915802995931 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_window_2 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 2 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 4 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 2 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_window_0 endpoint_18_44_window_2
private theorem endpoint_18_44_window_4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 4 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 6 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 4 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_4 endpoint_18_44_window_4
private theorem endpoint_18_44_window_6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 6 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 8 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 6 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_6 endpoint_18_44_window_6
private theorem endpoint_18_44_window_8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 8 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 10 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 8 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_8 endpoint_18_44_window_8
private theorem endpoint_18_44_window_10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 10 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 12 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 10 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_10 endpoint_18_44_window_10
private theorem endpoint_18_44_window_12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 12 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 14 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 12 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_12 endpoint_18_44_window_12
private theorem endpoint_18_44_window_14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 14 2 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 16 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 14 2 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_14 endpoint_18_44_window_14
private theorem endpoint_18_44_window_16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 16 1 199396696230332936 = some 199396696230332936 := by decide +kernel
private theorem endpoint_18_44_prefix_17 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 17 194191915802995931 = some 199396696230332936 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 16 1 194191915802995931 199396696230332936 199396696230332936 endpoint_18_44_prefix_16 endpoint_18_44_window_16

def endpoint_18_44 : CertifiedEndpoint :=
  ⟨⟨18, 44, 2174⟩, 199396696230332936, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_44_flag endpoint_18_44_sources 17 194191915802995931 199396696230332936 rfl endpoint_18_44_base endpoint_18_44_prefix_17) (by decide)⟩
private def endpoint_18_45_flag : Flag := ⟨18, 45, 2129⟩
private def endpoint_18_45_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_45_base : receiptBase endpoint_18_45_flag endpoint_18_45_sources = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_window_0 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_window_2 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 2 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 4 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 2 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_window_0 endpoint_18_45_window_2
private theorem endpoint_18_45_window_4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 4 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 6 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 4 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_4 endpoint_18_45_window_4
private theorem endpoint_18_45_window_6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 6 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 8 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 6 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_6 endpoint_18_45_window_6
private theorem endpoint_18_45_window_8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 8 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 10 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 8 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_8 endpoint_18_45_window_8
private theorem endpoint_18_45_window_10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 10 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 12 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 10 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_10 endpoint_18_45_window_10
private theorem endpoint_18_45_window_12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 12 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 14 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 12 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_12 endpoint_18_45_window_12
private theorem endpoint_18_45_window_14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 14 2 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 16 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 14 2 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_14 endpoint_18_45_window_14
private theorem endpoint_18_45_window_16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 16 1 194565658968662774 = some 194565658968662774 := by decide +kernel
private theorem endpoint_18_45_prefix_17 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 17 194565658968662774 = some 194565658968662774 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 16 1 194565658968662774 194565658968662774 194565658968662774 endpoint_18_45_prefix_16 endpoint_18_45_window_16

def endpoint_18_45 : CertifiedEndpoint :=
  ⟨⟨18, 45, 2129⟩, 194565658968662774, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_45_flag endpoint_18_45_sources 17 194565658968662774 194565658968662774 rfl endpoint_18_45_base endpoint_18_45_prefix_17) (by decide)⟩
private def endpoint_18_46_flag : Flag := ⟨18, 46, 2083⟩
private def endpoint_18_46_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_46_base : receiptBase endpoint_18_46_flag endpoint_18_46_sources = some 194157245606936799 := by decide +kernel
private theorem endpoint_18_46_window_0 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 2 194157245606936799 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_window_2 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 2 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 4 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 2 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_window_0 endpoint_18_46_window_2
private theorem endpoint_18_46_window_4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 4 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 6 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 4 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_4 endpoint_18_46_window_4
private theorem endpoint_18_46_window_6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 6 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 8 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 6 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_6 endpoint_18_46_window_6
private theorem endpoint_18_46_window_8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 8 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 10 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 8 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_8 endpoint_18_46_window_8
private theorem endpoint_18_46_window_10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 10 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 12 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 10 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_10 endpoint_18_46_window_10
private theorem endpoint_18_46_window_12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 12 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 14 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 12 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_12 endpoint_18_46_window_12
private theorem endpoint_18_46_window_14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 14 2 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 16 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 14 2 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_14 endpoint_18_46_window_14
private theorem endpoint_18_46_window_16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 16 1 194183176688500146 = some 194183176688500146 := by decide +kernel
private theorem endpoint_18_46_prefix_17 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 17 194157245606936799 = some 194183176688500146 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 16 1 194157245606936799 194183176688500146 194183176688500146 endpoint_18_46_prefix_16 endpoint_18_46_window_16

def endpoint_18_46 : CertifiedEndpoint :=
  ⟨⟨18, 46, 2083⟩, 194183176688500146, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_46_flag endpoint_18_46_sources 17 194157245606936799 194183176688500146 rfl endpoint_18_46_base endpoint_18_46_prefix_17) (by decide)⟩
private def endpoint_18_47_flag : Flag := ⟨18, 47, 2036⟩
private def endpoint_18_47_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_47_base : receiptBase endpoint_18_47_flag endpoint_18_47_sources = some 193498444359013853 := by decide +kernel
private theorem endpoint_18_47_window_0 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 2 193498444359013853 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_window_2 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 2 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 4 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 2 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_window_0 endpoint_18_47_window_2
private theorem endpoint_18_47_window_4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 4 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 6 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 4 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_4 endpoint_18_47_window_4
private theorem endpoint_18_47_window_6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 6 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 8 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 6 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_6 endpoint_18_47_window_6
private theorem endpoint_18_47_window_8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 8 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 10 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 8 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_8 endpoint_18_47_window_8
private theorem endpoint_18_47_window_10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 10 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 12 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 10 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_10 endpoint_18_47_window_10
private theorem endpoint_18_47_window_12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 12 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 14 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 12 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_12 endpoint_18_47_window_12
private theorem endpoint_18_47_window_14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 14 2 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 16 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 14 2 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_14 endpoint_18_47_window_14
private theorem endpoint_18_47_window_16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 16 1 197079412498053211 = some 197079412498053211 := by decide +kernel
private theorem endpoint_18_47_prefix_17 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 17 193498444359013853 = some 197079412498053211 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 16 1 193498444359013853 197079412498053211 197079412498053211 endpoint_18_47_prefix_16 endpoint_18_47_window_16

def endpoint_18_47 : CertifiedEndpoint :=
  ⟨⟨18, 47, 2036⟩, 197079412498053211, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_47_flag endpoint_18_47_sources 17 193498444359013853 197079412498053211 rfl endpoint_18_47_base endpoint_18_47_prefix_17) (by decide)⟩
private def endpoint_18_48_flag : Flag := ⟨18, 48, 1988⟩
private def endpoint_18_48_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_48_base : receiptBase endpoint_18_48_flag endpoint_18_48_sources = some 193278573763268841 := by decide +kernel
private theorem endpoint_18_48_window_0 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 2 193278573763268841 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_window_2 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 2 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 4 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 2 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_window_0 endpoint_18_48_window_2
private theorem endpoint_18_48_window_4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 4 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 6 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 4 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_4 endpoint_18_48_window_4
private theorem endpoint_18_48_window_6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 6 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 8 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 6 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_6 endpoint_18_48_window_6
private theorem endpoint_18_48_window_8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 8 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 10 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 8 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_8 endpoint_18_48_window_8
private theorem endpoint_18_48_window_10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 10 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 12 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 10 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_10 endpoint_18_48_window_10
private theorem endpoint_18_48_window_12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 12 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 14 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 12 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_12 endpoint_18_48_window_12
private theorem endpoint_18_48_window_14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 14 2 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 16 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 14 2 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_14 endpoint_18_48_window_14
private theorem endpoint_18_48_window_16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 16 1 194318399488514664 = some 194318399488514664 := by decide +kernel
private theorem endpoint_18_48_prefix_17 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 17 193278573763268841 = some 194318399488514664 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 16 1 193278573763268841 194318399488514664 194318399488514664 endpoint_18_48_prefix_16 endpoint_18_48_window_16

def endpoint_18_48 : CertifiedEndpoint :=
  ⟨⟨18, 48, 1988⟩, 194318399488514664, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_48_flag endpoint_18_48_sources 17 193278573763268841 194318399488514664 rfl endpoint_18_48_base endpoint_18_48_prefix_17) (by decide)⟩
private def endpoint_18_49_flag : Flag := ⟨18, 49, 1939⟩
private def endpoint_18_49_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_49_base : receiptBase endpoint_18_49_flag endpoint_18_49_sources = some 192091457917178044 := by decide +kernel
private theorem endpoint_18_49_window_0 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 2 192091457917178044 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_window_2 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 2 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 4 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 2 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_window_0 endpoint_18_49_window_2
private theorem endpoint_18_49_window_4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 4 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 6 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 4 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_4 endpoint_18_49_window_4
private theorem endpoint_18_49_window_6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 6 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 8 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 6 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_6 endpoint_18_49_window_6
private theorem endpoint_18_49_window_8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 8 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 10 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 8 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_8 endpoint_18_49_window_8
private theorem endpoint_18_49_window_10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 10 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 12 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 10 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_10 endpoint_18_49_window_10
private theorem endpoint_18_49_window_12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 12 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 14 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 12 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_12 endpoint_18_49_window_12
private theorem endpoint_18_49_window_14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 14 2 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 16 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 14 2 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_14 endpoint_18_49_window_14
private theorem endpoint_18_49_window_16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 16 1 196689888824714966 = some 196689888824714966 := by decide +kernel
private theorem endpoint_18_49_prefix_17 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 17 192091457917178044 = some 196689888824714966 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 16 1 192091457917178044 196689888824714966 196689888824714966 endpoint_18_49_prefix_16 endpoint_18_49_window_16

def endpoint_18_49 : CertifiedEndpoint :=
  ⟨⟨18, 49, 1939⟩, 196689888824714966, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_49_flag endpoint_18_49_sources 17 192091457917178044 196689888824714966 rfl endpoint_18_49_base endpoint_18_49_prefix_17) (by decide)⟩
private def endpoint_18_50_flag : Flag := ⟨18, 50, 1889⟩
private def endpoint_18_50_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_50_base : receiptBase endpoint_18_50_flag endpoint_18_50_sources = some 190635570266391046 := by decide +kernel
private theorem endpoint_18_50_window_0 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 2 190635570266391046 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_window_2 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 2 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 4 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 2 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_window_0 endpoint_18_50_window_2
private theorem endpoint_18_50_window_4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 4 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 6 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 4 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_4 endpoint_18_50_window_4
private theorem endpoint_18_50_window_6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 6 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 8 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 6 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_6 endpoint_18_50_window_6
private theorem endpoint_18_50_window_8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 8 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 10 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 8 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_8 endpoint_18_50_window_8
private theorem endpoint_18_50_window_10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 10 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 12 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 10 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_10 endpoint_18_50_window_10
private theorem endpoint_18_50_window_12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 12 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 14 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 12 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_12 endpoint_18_50_window_12
private theorem endpoint_18_50_window_14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 14 2 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 16 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 14 2 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_14 endpoint_18_50_window_14
private theorem endpoint_18_50_window_16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 16 1 198864217022759078 = some 198864217022759078 := by decide +kernel
private theorem endpoint_18_50_prefix_17 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 17 190635570266391046 = some 198864217022759078 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 16 1 190635570266391046 198864217022759078 198864217022759078 endpoint_18_50_prefix_16 endpoint_18_50_window_16

def endpoint_18_50 : CertifiedEndpoint :=
  ⟨⟨18, 50, 1889⟩, 198864217022759078, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_50_flag endpoint_18_50_sources 17 190635570266391046 198864217022759078 rfl endpoint_18_50_base endpoint_18_50_prefix_17) (by decide)⟩
private def endpoint_18_51_flag : Flag := ⟨18, 51, 1838⟩
private def endpoint_18_51_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_18_51_base : receiptBase endpoint_18_51_flag endpoint_18_51_sources = some 188878863010462373 := by decide +kernel
private theorem endpoint_18_51_window_0 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 2 188878863010462373 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_window_2 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 2 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 4 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 2 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_window_0 endpoint_18_51_window_2
private theorem endpoint_18_51_window_4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 4 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 6 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 4 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_4 endpoint_18_51_window_4
private theorem endpoint_18_51_window_6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 6 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 8 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 6 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_6 endpoint_18_51_window_6
private theorem endpoint_18_51_window_8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 8 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 10 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 8 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_8 endpoint_18_51_window_8
private theorem endpoint_18_51_window_10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 10 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 12 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 10 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_10 endpoint_18_51_window_10
private theorem endpoint_18_51_window_12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 12 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 14 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 12 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_12 endpoint_18_51_window_12
private theorem endpoint_18_51_window_14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 14 2 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 16 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 14 2 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_14 endpoint_18_51_window_14
private theorem endpoint_18_51_window_16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 16 1 200837183499445611 = some 200837183499445611 := by decide +kernel
private theorem endpoint_18_51_prefix_17 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 17 188878863010462373 = some 200837183499445611 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 16 1 188878863010462373 200837183499445611 200837183499445611 endpoint_18_51_prefix_16 endpoint_18_51_window_16

def endpoint_18_51 : CertifiedEndpoint :=
  ⟨⟨18, 51, 1838⟩, 200837183499445611, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_18_51_flag endpoint_18_51_sources 17 188878863010462373 200837183499445611 rfl endpoint_18_51_base endpoint_18_51_prefix_17) (by decide)⟩
private def endpoint_18_52_flag : Flag := ⟨18, 52, 1786⟩
private def endpoint_18_52_sources : Sources := ⟨contact29, contact16, contact12⟩
private theorem endpoint_18_52_base : receiptBase endpoint_18_52_flag endpoint_18_52_sources = some 187297733654062632 := by decide +kernel
private theorem endpoint_18_52_window_0 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 2 187297733654062632 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_window_2 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 2 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 4 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 2 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_window_0 endpoint_18_52_window_2
private theorem endpoint_18_52_window_4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 4 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 6 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 4 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_4 endpoint_18_52_window_4
private theorem endpoint_18_52_window_6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 6 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 8 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 6 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_6 endpoint_18_52_window_6
private theorem endpoint_18_52_window_8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 8 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 10 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 8 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_8 endpoint_18_52_window_8
private theorem endpoint_18_52_window_10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 10 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 12 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 10 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_10 endpoint_18_52_window_10
private theorem endpoint_18_52_window_12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 12 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 14 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 12 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_12 endpoint_18_52_window_12
private theorem endpoint_18_52_window_14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 14 2 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 16 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 14 2 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_14 endpoint_18_52_window_14
private theorem endpoint_18_52_window_16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 16 1 201396469144789896 = some 201396469144789896 := by decide +kernel
private theorem endpoint_18_52_prefix_17 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 17 187297733654062632 = some 201396469144789896 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 16 1 187297733654062632 201396469144789896 201396469144789896 endpoint_18_52_prefix_16 endpoint_18_52_window_16

def endpoint_18_52 : CertifiedEndpoint :=
  ⟨⟨18, 52, 1786⟩, 201396469144789896, .terminal ⟨contact29, contact16, contact12⟩ (finish_receipt_window endpoint_18_52_flag endpoint_18_52_sources 17 187297733654062632 201396469144789896 rfl endpoint_18_52_base endpoint_18_52_prefix_17) (by decide)⟩
private def endpoint_18_53_flag : Flag := ⟨18, 53, 1733⟩
private def endpoint_18_53_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_18_53_base : receiptBase endpoint_18_53_flag endpoint_18_53_sources = some 186428385425818065 := by decide +kernel
private theorem endpoint_18_53_window_0 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 2 186428385425818065 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_window_2 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 2 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 4 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 2 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_window_0 endpoint_18_53_window_2
private theorem endpoint_18_53_window_4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 4 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 6 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 4 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_4 endpoint_18_53_window_4
private theorem endpoint_18_53_window_6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 6 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 8 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 6 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_6 endpoint_18_53_window_6
private theorem endpoint_18_53_window_8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 8 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 10 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 8 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_8 endpoint_18_53_window_8
private theorem endpoint_18_53_window_10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 10 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 12 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 10 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_10 endpoint_18_53_window_10
private theorem endpoint_18_53_window_12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 12 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 14 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 12 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_12 endpoint_18_53_window_12
private theorem endpoint_18_53_window_14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 14 2 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 16 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 14 2 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_14 endpoint_18_53_window_14
private theorem endpoint_18_53_window_16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 16 1 189445216734205323 = some 189445216734205323 := by decide +kernel
private theorem endpoint_18_53_prefix_17 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 17 186428385425818065 = some 189445216734205323 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 16 1 186428385425818065 189445216734205323 189445216734205323 endpoint_18_53_prefix_16 endpoint_18_53_window_16

def endpoint_18_53 : CertifiedEndpoint :=
  ⟨⟨18, 53, 1733⟩, 189445216734205323, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_18_53_flag endpoint_18_53_sources 17 186428385425818065 189445216734205323 rfl endpoint_18_53_base endpoint_18_53_prefix_17) (by decide)⟩
private def endpoint_18_54_flag : Flag := ⟨18, 54, 1678⟩
private def endpoint_18_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_54_base : receiptBase endpoint_18_54_flag endpoint_18_54_sources = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_window_0 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_window_2 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 2 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 4 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 2 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_window_0 endpoint_18_54_window_2
private theorem endpoint_18_54_window_4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 4 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 6 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 4 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_4 endpoint_18_54_window_4
private theorem endpoint_18_54_window_6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 6 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 8 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 6 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_6 endpoint_18_54_window_6
private theorem endpoint_18_54_window_8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 8 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 10 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 8 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_8 endpoint_18_54_window_8
private theorem endpoint_18_54_window_10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 10 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 12 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 10 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_10 endpoint_18_54_window_10
private theorem endpoint_18_54_window_12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 12 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 14 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 12 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_12 endpoint_18_54_window_12
private theorem endpoint_18_54_window_14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 14 2 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 16 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 14 2 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_14 endpoint_18_54_window_14
private theorem endpoint_18_54_window_16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 16 1 185380582774013711 = some 185380582774013711 := by decide +kernel
private theorem endpoint_18_54_prefix_17 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 17 185380582774013711 = some 185380582774013711 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 16 1 185380582774013711 185380582774013711 185380582774013711 endpoint_18_54_prefix_16 endpoint_18_54_window_16

def endpoint_18_54 : CertifiedEndpoint :=
  ⟨⟨18, 54, 1678⟩, 185380582774013711, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_54_flag endpoint_18_54_sources 17 185380582774013711 185380582774013711 rfl endpoint_18_54_base endpoint_18_54_prefix_17) (by decide)⟩
private def endpoint_18_55_flag : Flag := ⟨18, 55, 1623⟩
private def endpoint_18_55_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_55_base : receiptBase endpoint_18_55_flag endpoint_18_55_sources = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_window_0 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_window_2 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 2 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 4 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 2 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_window_0 endpoint_18_55_window_2
private theorem endpoint_18_55_window_4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 4 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 6 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 4 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_4 endpoint_18_55_window_4
private theorem endpoint_18_55_window_6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 6 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 8 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 6 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_6 endpoint_18_55_window_6
private theorem endpoint_18_55_window_8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 8 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 10 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 8 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_8 endpoint_18_55_window_8
private theorem endpoint_18_55_window_10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 10 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 12 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 10 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_10 endpoint_18_55_window_10
private theorem endpoint_18_55_window_12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 12 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 14 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 12 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_12 endpoint_18_55_window_12
private theorem endpoint_18_55_window_14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 14 2 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 16 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 14 2 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_14 endpoint_18_55_window_14
private theorem endpoint_18_55_window_16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 16 1 182271861261916301 = some 182271861261916301 := by decide +kernel
private theorem endpoint_18_55_prefix_17 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 17 182271861261916301 = some 182271861261916301 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 16 1 182271861261916301 182271861261916301 182271861261916301 endpoint_18_55_prefix_16 endpoint_18_55_window_16

def endpoint_18_55 : CertifiedEndpoint :=
  ⟨⟨18, 55, 1623⟩, 182271861261916301, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_55_flag endpoint_18_55_sources 17 182271861261916301 182271861261916301 rfl endpoint_18_55_base endpoint_18_55_prefix_17) (by decide)⟩
private def endpoint_18_56_flag : Flag := ⟨18, 56, 1567⟩
private def endpoint_18_56_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_56_base : receiptBase endpoint_18_56_flag endpoint_18_56_sources = some 177331781823301897 := by decide +kernel
private theorem endpoint_18_56_window_0 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 2 177331781823301897 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_window_2 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 2 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 4 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 2 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_window_0 endpoint_18_56_window_2
private theorem endpoint_18_56_window_4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 4 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 6 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 4 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_4 endpoint_18_56_window_4
private theorem endpoint_18_56_window_6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 6 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 8 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 6 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_6 endpoint_18_56_window_6
private theorem endpoint_18_56_window_8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 8 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 10 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 8 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_8 endpoint_18_56_window_8
private theorem endpoint_18_56_window_10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 10 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 12 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 10 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_10 endpoint_18_56_window_10
private theorem endpoint_18_56_window_12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 12 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 14 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 12 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_12 endpoint_18_56_window_12
private theorem endpoint_18_56_window_14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 14 2 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 16 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 14 2 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_14 endpoint_18_56_window_14
private theorem endpoint_18_56_window_16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 16 1 191732269629708588 = some 191732269629708588 := by decide +kernel
private theorem endpoint_18_56_prefix_17 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 17 177331781823301897 = some 191732269629708588 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 16 1 177331781823301897 191732269629708588 191732269629708588 endpoint_18_56_prefix_16 endpoint_18_56_window_16

def endpoint_18_56 : CertifiedEndpoint :=
  ⟨⟨18, 56, 1567⟩, 191732269629708588, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_56_flag endpoint_18_56_sources 17 177331781823301897 191732269629708588 rfl endpoint_18_56_base endpoint_18_56_prefix_17) (by decide)⟩
private def endpoint_18_57_flag : Flag := ⟨18, 57, 1509⟩
private def endpoint_18_57_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_57_base : receiptBase endpoint_18_57_flag endpoint_18_57_sources = some 173534830682116533 := by decide +kernel
private theorem endpoint_18_57_window_0 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 2 173534830682116533 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_window_2 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 2 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 4 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 2 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_window_0 endpoint_18_57_window_2
private theorem endpoint_18_57_window_4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 4 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 6 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 4 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_4 endpoint_18_57_window_4
private theorem endpoint_18_57_window_6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 6 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 8 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 6 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_6 endpoint_18_57_window_6
private theorem endpoint_18_57_window_8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 8 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 10 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 8 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_8 endpoint_18_57_window_8
private theorem endpoint_18_57_window_10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 10 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 12 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 10 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_10 endpoint_18_57_window_10
private theorem endpoint_18_57_window_12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 12 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 14 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 12 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_12 endpoint_18_57_window_12
private theorem endpoint_18_57_window_14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 14 2 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 16 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 14 2 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_14 endpoint_18_57_window_14
private theorem endpoint_18_57_window_16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 16 1 192001568849225283 = some 192001568849225283 := by decide +kernel
private theorem endpoint_18_57_prefix_17 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 17 173534830682116533 = some 192001568849225283 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 16 1 173534830682116533 192001568849225283 192001568849225283 endpoint_18_57_prefix_16 endpoint_18_57_window_16

def endpoint_18_57 : CertifiedEndpoint :=
  ⟨⟨18, 57, 1509⟩, 192001568849225283, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_57_flag endpoint_18_57_sources 17 173534830682116533 192001568849225283 rfl endpoint_18_57_base endpoint_18_57_prefix_17) (by decide)⟩
private def endpoint_18_58_flag : Flag := ⟨18, 58, 1450⟩
private def endpoint_18_58_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_58_base : receiptBase endpoint_18_58_flag endpoint_18_58_sources = some 170842373735685124 := by decide +kernel
private theorem endpoint_18_58_window_0 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 2 170842373735685124 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_window_2 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 2 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 4 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 2 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_window_0 endpoint_18_58_window_2
private theorem endpoint_18_58_window_4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 4 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 6 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 4 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_4 endpoint_18_58_window_4
private theorem endpoint_18_58_window_6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 6 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 8 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 6 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_6 endpoint_18_58_window_6
private theorem endpoint_18_58_window_8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 8 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 10 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 8 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_8 endpoint_18_58_window_8
private theorem endpoint_18_58_window_10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 10 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 12 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 10 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_10 endpoint_18_58_window_10
private theorem endpoint_18_58_window_12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 12 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 14 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 12 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_12 endpoint_18_58_window_12
private theorem endpoint_18_58_window_14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 14 2 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 16 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 14 2 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_14 endpoint_18_58_window_14
private theorem endpoint_18_58_window_16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 16 1 177687905383503654 = some 177687905383503654 := by decide +kernel
private theorem endpoint_18_58_prefix_17 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 17 170842373735685124 = some 177687905383503654 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 16 1 170842373735685124 177687905383503654 177687905383503654 endpoint_18_58_prefix_16 endpoint_18_58_window_16

def endpoint_18_58 : CertifiedEndpoint :=
  ⟨⟨18, 58, 1450⟩, 177687905383503654, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_58_flag endpoint_18_58_sources 17 170842373735685124 177687905383503654 rfl endpoint_18_58_base endpoint_18_58_prefix_17) (by decide)⟩
private def endpoint_18_59_flag : Flag := ⟨18, 59, 1390⟩
private def endpoint_18_59_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_59_base : receiptBase endpoint_18_59_flag endpoint_18_59_sources = some 166347195018124802 := by decide +kernel
private theorem endpoint_18_59_window_0 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 2 166347195018124802 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_window_2 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 2 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 4 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 2 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_window_0 endpoint_18_59_window_2
private theorem endpoint_18_59_window_4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 4 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 6 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 4 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_4 endpoint_18_59_window_4
private theorem endpoint_18_59_window_6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 6 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 8 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 6 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_6 endpoint_18_59_window_6
private theorem endpoint_18_59_window_8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 8 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 10 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 8 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_8 endpoint_18_59_window_8
private theorem endpoint_18_59_window_10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 10 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 12 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 10 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_10 endpoint_18_59_window_10
private theorem endpoint_18_59_window_12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 12 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 14 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 12 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_12 endpoint_18_59_window_12
private theorem endpoint_18_59_window_14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 14 2 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 16 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 14 2 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_14 endpoint_18_59_window_14
private theorem endpoint_18_59_window_16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 16 1 177188377665661840 = some 177188377665661840 := by decide +kernel
private theorem endpoint_18_59_prefix_17 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 17 166347195018124802 = some 177188377665661840 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 16 1 166347195018124802 177188377665661840 177188377665661840 endpoint_18_59_prefix_16 endpoint_18_59_window_16

def endpoint_18_59 : CertifiedEndpoint :=
  ⟨⟨18, 59, 1390⟩, 177188377665661840, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_59_flag endpoint_18_59_sources 17 166347195018124802 177188377665661840 rfl endpoint_18_59_base endpoint_18_59_prefix_17) (by decide)⟩
private def endpoint_18_60_flag : Flag := ⟨18, 60, 1329⟩
private def endpoint_18_60_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_60_base : receiptBase endpoint_18_60_flag endpoint_18_60_sources = some 161518984524715238 := by decide +kernel
private theorem endpoint_18_60_window_0 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 2 161518984524715238 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_window_2 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 2 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 4 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 2 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_window_0 endpoint_18_60_window_2
private theorem endpoint_18_60_window_4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 4 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 6 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 4 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_4 endpoint_18_60_window_4
private theorem endpoint_18_60_window_6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 6 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 8 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 6 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_6 endpoint_18_60_window_6
private theorem endpoint_18_60_window_8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 8 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 10 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 8 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_8 endpoint_18_60_window_8
private theorem endpoint_18_60_window_10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 10 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 12 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 10 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_10 endpoint_18_60_window_10
private theorem endpoint_18_60_window_12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 12 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 14 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 12 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_12 endpoint_18_60_window_12
private theorem endpoint_18_60_window_14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 14 2 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 16 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 14 2 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_14 endpoint_18_60_window_14
private theorem endpoint_18_60_window_16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 16 1 176446882588849020 = some 176446882588849020 := by decide +kernel
private theorem endpoint_18_60_prefix_17 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 17 161518984524715238 = some 176446882588849020 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 16 1 161518984524715238 176446882588849020 176446882588849020 endpoint_18_60_prefix_16 endpoint_18_60_window_16

def endpoint_18_60 : CertifiedEndpoint :=
  ⟨⟨18, 60, 1329⟩, 176446882588849020, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_60_flag endpoint_18_60_sources 17 161518984524715238 176446882588849020 rfl endpoint_18_60_base endpoint_18_60_prefix_17) (by decide)⟩
private def endpoint_18_61_flag : Flag := ⟨18, 61, 1266⟩
private def endpoint_18_61_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_18_61_base : receiptBase endpoint_18_61_flag endpoint_18_61_sources = some 156558455961371073 := by decide +kernel
private theorem endpoint_18_61_window_0 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 2 156558455961371073 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_window_2 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 2 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 4 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 2 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_window_0 endpoint_18_61_window_2
private theorem endpoint_18_61_window_4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 4 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 6 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 4 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_4 endpoint_18_61_window_4
private theorem endpoint_18_61_window_6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 6 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 8 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 6 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_6 endpoint_18_61_window_6
private theorem endpoint_18_61_window_8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 8 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 10 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 8 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_8 endpoint_18_61_window_8
private theorem endpoint_18_61_window_10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 10 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 12 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 10 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_10 endpoint_18_61_window_10
private theorem endpoint_18_61_window_12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 12 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 14 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 12 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_12 endpoint_18_61_window_12
private theorem endpoint_18_61_window_14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 14 2 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 16 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 14 2 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_14 endpoint_18_61_window_14
private theorem endpoint_18_61_window_16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 16 1 172310449073319963 = some 172310449073319963 := by decide +kernel
private theorem endpoint_18_61_prefix_17 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 17 156558455961371073 = some 172310449073319963 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 16 1 156558455961371073 172310449073319963 172310449073319963 endpoint_18_61_prefix_16 endpoint_18_61_window_16

def endpoint_18_61 : CertifiedEndpoint :=
  ⟨⟨18, 61, 1266⟩, 172310449073319963, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_18_61_flag endpoint_18_61_sources 17 156558455961371073 172310449073319963 rfl endpoint_18_61_base endpoint_18_61_prefix_17) (by decide)⟩
private def endpoint_18_62_flag : Flag := ⟨18, 62, 1202⟩
private def endpoint_18_62_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_18_62_base : receiptBase endpoint_18_62_flag endpoint_18_62_sources = some 152121935162910713 := by decide +kernel
private theorem endpoint_18_62_window_0 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 2 152121935162910713 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_window_2 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 2 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 4 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 2 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_window_0 endpoint_18_62_window_2
private theorem endpoint_18_62_window_4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 4 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 6 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 4 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_4 endpoint_18_62_window_4
private theorem endpoint_18_62_window_6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 6 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 8 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 6 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_6 endpoint_18_62_window_6
private theorem endpoint_18_62_window_8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 8 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 10 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 8 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_8 endpoint_18_62_window_8
private theorem endpoint_18_62_window_10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 10 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 12 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 10 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_10 endpoint_18_62_window_10
private theorem endpoint_18_62_window_12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 12 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 14 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 12 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_12 endpoint_18_62_window_12
private theorem endpoint_18_62_window_14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 14 2 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 16 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 14 2 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_14 endpoint_18_62_window_14
private theorem endpoint_18_62_window_16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 16 1 163617027672232110 = some 163617027672232110 := by decide +kernel
private theorem endpoint_18_62_prefix_17 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 17 152121935162910713 = some 163617027672232110 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 16 1 152121935162910713 163617027672232110 163617027672232110 endpoint_18_62_prefix_16 endpoint_18_62_window_16

def endpoint_18_62 : CertifiedEndpoint :=
  ⟨⟨18, 62, 1202⟩, 163617027672232110, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_18_62_flag endpoint_18_62_sources 17 152121935162910713 163617027672232110 rfl endpoint_18_62_base endpoint_18_62_prefix_17) (by decide)⟩
private def endpoint_18_63_flag : Flag := ⟨18, 63, 1136⟩
private def endpoint_18_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_18_63_base : receiptBase endpoint_18_63_flag endpoint_18_63_sources = some 145928416164506936 := by decide +kernel
private theorem endpoint_18_63_window_0 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 2 145928416164506936 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_window_2 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 2 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 4 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 2 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_window_0 endpoint_18_63_window_2
private theorem endpoint_18_63_window_4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 4 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 6 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 4 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_4 endpoint_18_63_window_4
private theorem endpoint_18_63_window_6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 6 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 8 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 6 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_6 endpoint_18_63_window_6
private theorem endpoint_18_63_window_8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 8 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 10 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 8 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_8 endpoint_18_63_window_8
private theorem endpoint_18_63_window_10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 10 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 12 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 10 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_10 endpoint_18_63_window_10
private theorem endpoint_18_63_window_12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 12 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 14 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 12 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_12 endpoint_18_63_window_12
private theorem endpoint_18_63_window_14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 14 2 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 16 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 14 2 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_14 endpoint_18_63_window_14
private theorem endpoint_18_63_window_16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 16 1 161773622503627680 = some 161773622503627680 := by decide +kernel
private theorem endpoint_18_63_prefix_17 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 17 145928416164506936 = some 161773622503627680 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 16 1 145928416164506936 161773622503627680 161773622503627680 endpoint_18_63_prefix_16 endpoint_18_63_window_16

def endpoint_18_63 : CertifiedEndpoint :=
  ⟨⟨18, 63, 1136⟩, 161773622503627680, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_18_63_flag endpoint_18_63_sources 17 145928416164506936 161773622503627680 rfl endpoint_18_63_base endpoint_18_63_prefix_17) (by decide)⟩
private def endpoint_18_64_flag : Flag := ⟨18, 64, 1069⟩
private def endpoint_18_64_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_64_base : receiptBase endpoint_18_64_flag endpoint_18_64_sources = some 140909194854678090 := by decide +kernel
private theorem endpoint_18_64_window_0 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 2 140909194854678090 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_window_2 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 2 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 4 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 2 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_window_0 endpoint_18_64_window_2
private theorem endpoint_18_64_window_4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 4 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 6 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 4 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_4 endpoint_18_64_window_4
private theorem endpoint_18_64_window_6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 6 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 8 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 6 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_6 endpoint_18_64_window_6
private theorem endpoint_18_64_window_8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 8 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 10 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 8 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_8 endpoint_18_64_window_8
private theorem endpoint_18_64_window_10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 10 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 12 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 10 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_10 endpoint_18_64_window_10
private theorem endpoint_18_64_window_12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 12 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 14 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 12 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_12 endpoint_18_64_window_12
private theorem endpoint_18_64_window_14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 14 2 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 16 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 14 2 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_14 endpoint_18_64_window_14
private theorem endpoint_18_64_window_16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 16 1 150512700153136656 = some 150512700153136656 := by decide +kernel
private theorem endpoint_18_64_prefix_17 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 17 140909194854678090 = some 150512700153136656 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 16 1 140909194854678090 150512700153136656 150512700153136656 endpoint_18_64_prefix_16 endpoint_18_64_window_16

def endpoint_18_64 : CertifiedEndpoint :=
  ⟨⟨18, 64, 1069⟩, 150512700153136656, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_64_flag endpoint_18_64_sources 17 140909194854678090 150512700153136656 rfl endpoint_18_64_base endpoint_18_64_prefix_17) (by decide)⟩
def endpoint_18_65 : CertifiedEndpoint :=
  ⟨⟨18, 65, 1000⟩, 241497284478574729, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_66 : CertifiedEndpoint :=
  ⟨⟨18, 66, 930⟩, 227848799100830106, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_67 : CertifiedEndpoint :=
  ⟨⟨18, 67, 858⟩, 213043581520662827, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_68 : CertifiedEndpoint :=
  ⟨⟨18, 68, 785⟩, 197318857305757467, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_69 : CertifiedEndpoint :=
  ⟨⟨18, 69, 709⟩, 180123362220480574, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_70 : CertifiedEndpoint :=
  ⟨⟨18, 70, 632⟩, 161963176323839540, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_71 : CertifiedEndpoint :=
  ⟨⟨18, 71, 553⟩, 142546853036198518, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_72 : CertifiedEndpoint :=
  ⟨⟨18, 72, 472⟩, 121847281851581872, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_73 : CertifiedEndpoint :=
  ⟨⟨18, 73, 388⟩, 99550424102040725, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_74 : CertifiedEndpoint :=
  ⟨⟨18, 74, 303⟩, 76198507187883317, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_75 : CertifiedEndpoint :=
  ⟨⟨18, 75, 215⟩, 51186045861524924, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_76 : CertifiedEndpoint :=
  ⟨⟨18, 76, 126⟩, 25073341193924210, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_19 : CertifiedEndpoint :=
  ⟨⟨19, 19, 2834⟩, 139325133028860663, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_20 : CertifiedEndpoint :=
  ⟨⟨19, 20, 2801⟩, 142065019797445546, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_21 : CertifiedEndpoint :=
  ⟨⟨19, 21, 2768⟩, 144701154745112783, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_22 : CertifiedEndpoint :=
  ⟨⟨19, 22, 2735⟩, 155927144260852523, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_23 : CertifiedEndpoint :=
  ⟨⟨19, 23, 2701⟩, 166771035374027790, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_24 : CertifiedEndpoint :=
  ⟨⟨19, 24, 2666⟩, 177218499718663010, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_25 : CertifiedEndpoint :=
  ⟨⟨19, 25, 2631⟩, 187326859401876312, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_26 : CertifiedEndpoint :=
  ⟨⟨19, 26, 2596⟩, 197096114423667696, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_27 : CertifiedEndpoint :=
  ⟨⟨19, 27, 2560⟩, 206445062066959743, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_28 : CertifiedEndpoint :=
  ⟨⟨19, 28, 2523⟩, 215359373965776879, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_29 : CertifiedEndpoint :=
  ⟨⟨19, 29, 2486⟩, 223915476715204665, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_30 : CertifiedEndpoint :=
  ⟨⟨19, 30, 2448⟩, 232017839232190108, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_31 : CertifiedEndpoint :=
  ⟨⟨19, 31, 2410⟩, 239752440355802485, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_32 : CertifiedEndpoint :=
  ⟨⟨19, 32, 2371⟩, 247014196759005087, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_19_33_flag : Flag := ⟨19, 33, 2331⟩
private def endpoint_19_33_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_33_base : receiptBase endpoint_19_33_flag endpoint_19_33_sources = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_window_0 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_window_2 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 2 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 4 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 2 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_window_0 endpoint_19_33_window_2
private theorem endpoint_19_33_window_4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 4 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 6 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 4 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_4 endpoint_19_33_window_4
private theorem endpoint_19_33_window_6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 6 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 8 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 6 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_6 endpoint_19_33_window_6
private theorem endpoint_19_33_window_8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 8 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 10 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 8 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_8 endpoint_19_33_window_8
private theorem endpoint_19_33_window_10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 10 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 12 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 10 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_10 endpoint_19_33_window_10
private theorem endpoint_19_33_window_12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 12 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 14 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 12 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_12 endpoint_19_33_window_12
private theorem endpoint_19_33_window_14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 14 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 16 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 14 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_14 endpoint_19_33_window_14
private theorem endpoint_19_33_window_16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 16 2 163609177882920848 = some 163609177882920848 := by decide +kernel
private theorem endpoint_19_33_prefix_18 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 18 163609177882920848 = some 163609177882920848 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 16 2 163609177882920848 163609177882920848 163609177882920848 endpoint_19_33_prefix_16 endpoint_19_33_window_16

def endpoint_19_33 : CertifiedEndpoint :=
  ⟨⟨19, 33, 2331⟩, 163609177882920848, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_33_flag endpoint_19_33_sources 18 163609177882920848 163609177882920848 rfl endpoint_19_33_base endpoint_19_33_prefix_18) (by decide)⟩

def endpointBlock12 : List CertifiedEndpoint := [
  endpoint_17_50, endpoint_17_51, endpoint_17_52, endpoint_17_53, endpoint_17_54, endpoint_17_55,
  endpoint_17_56, endpoint_17_57, endpoint_17_58, endpoint_17_59, endpoint_17_60, endpoint_17_61,
  endpoint_17_62, endpoint_17_63, endpoint_17_64, endpoint_17_65, endpoint_17_66, endpoint_17_67,
  endpoint_17_68, endpoint_17_69, endpoint_17_70, endpoint_17_71, endpoint_17_72, endpoint_17_73,
  endpoint_17_74, endpoint_17_75, endpoint_17_76, endpoint_17_77, endpoint_17_78, endpoint_17_79,
  endpoint_17_80, endpoint_18_18, endpoint_18_19, endpoint_18_20, endpoint_18_21, endpoint_18_22,
  endpoint_18_23, endpoint_18_24, endpoint_18_25, endpoint_18_26, endpoint_18_27, endpoint_18_28,
  endpoint_18_29, endpoint_18_30, endpoint_18_31, endpoint_18_32, endpoint_18_33, endpoint_18_34,
  endpoint_18_35, endpoint_18_36, endpoint_18_37, endpoint_18_38, endpoint_18_39, endpoint_18_40,
  endpoint_18_41, endpoint_18_42, endpoint_18_43, endpoint_18_44, endpoint_18_45, endpoint_18_46,
  endpoint_18_47, endpoint_18_48, endpoint_18_49, endpoint_18_50, endpoint_18_51, endpoint_18_52,
  endpoint_18_53, endpoint_18_54, endpoint_18_55, endpoint_18_56, endpoint_18_57, endpoint_18_58,
  endpoint_18_59, endpoint_18_60, endpoint_18_61, endpoint_18_62, endpoint_18_63, endpoint_18_64,
  endpoint_18_65, endpoint_18_66, endpoint_18_67, endpoint_18_68, endpoint_18_69, endpoint_18_70,
  endpoint_18_71, endpoint_18_72, endpoint_18_73, endpoint_18_74, endpoint_18_75, endpoint_18_76,
  endpoint_19_19, endpoint_19_20, endpoint_19_21, endpoint_19_22, endpoint_19_23, endpoint_19_24,
  endpoint_19_25, endpoint_19_26, endpoint_19_27, endpoint_19_28, endpoint_19_29, endpoint_19_30,
  endpoint_19_31, endpoint_19_32, endpoint_19_33
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
