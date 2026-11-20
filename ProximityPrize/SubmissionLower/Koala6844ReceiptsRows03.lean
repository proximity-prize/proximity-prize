import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


def endpoint_7_44 : CertifiedEndpoint :=
  ⟨⟨7, 44, 3830⟩, 256357847371575606, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_7_45_flag : Flag := ⟨7, 45, 3803⟩
private def endpoint_7_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_45_base : receiptBase endpoint_7_45_flag endpoint_7_45_sources = some 174841091192638986 := by decide +kernel
private theorem endpoint_7_45_window_0 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 2 174841091192638986 = some 174841091192638986 := by decide +kernel
private theorem endpoint_7_45_window_2 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 2 2 174841091192638986 = some 174841091192638986 := by decide +kernel
private theorem endpoint_7_45_prefix_4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 4 174841091192638986 = some 174841091192638986 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 2 2 174841091192638986 174841091192638986 174841091192638986 endpoint_7_45_window_0 endpoint_7_45_window_2
private theorem endpoint_7_45_window_4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 4 2 174841091192638986 = some 174841091192638986 := by decide +kernel
private theorem endpoint_7_45_prefix_6 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 6 174841091192638986 = some 174841091192638986 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 4 2 174841091192638986 174841091192638986 174841091192638986 endpoint_7_45_prefix_4 endpoint_7_45_window_4

def endpoint_7_45 : CertifiedEndpoint :=
  ⟨⟨7, 45, 3803⟩, 174841091192638986, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_45_flag endpoint_7_45_sources 6 174841091192638986 174841091192638986 rfl endpoint_7_45_base endpoint_7_45_prefix_6) (by decide)⟩
private def endpoint_7_46_flag : Flag := ⟨7, 46, 3776⟩
private def endpoint_7_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_46_base : receiptBase endpoint_7_46_flag endpoint_7_46_sources = some 176927205340396251 := by decide +kernel
private theorem endpoint_7_46_window_0 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 2 176927205340396251 = some 176927205340396251 := by decide +kernel
private theorem endpoint_7_46_window_2 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 2 2 176927205340396251 = some 176927205340396251 := by decide +kernel
private theorem endpoint_7_46_prefix_4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 4 176927205340396251 = some 176927205340396251 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 2 2 176927205340396251 176927205340396251 176927205340396251 endpoint_7_46_window_0 endpoint_7_46_window_2
private theorem endpoint_7_46_window_4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 4 2 176927205340396251 = some 176927205340396251 := by decide +kernel
private theorem endpoint_7_46_prefix_6 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 6 176927205340396251 = some 176927205340396251 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 4 2 176927205340396251 176927205340396251 176927205340396251 endpoint_7_46_prefix_4 endpoint_7_46_window_4

def endpoint_7_46 : CertifiedEndpoint :=
  ⟨⟨7, 46, 3776⟩, 176927205340396251, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_46_flag endpoint_7_46_sources 6 176927205340396251 176927205340396251 rfl endpoint_7_46_base endpoint_7_46_prefix_6) (by decide)⟩
private def endpoint_7_47_flag : Flag := ⟨7, 47, 3749⟩
private def endpoint_7_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_47_base : receiptBase endpoint_7_47_flag endpoint_7_47_sources = some 178965796174999075 := by decide +kernel
private theorem endpoint_7_47_window_0 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 2 178965796174999075 = some 178965796174999075 := by decide +kernel
private theorem endpoint_7_47_window_2 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 2 2 178965796174999075 = some 178965796174999075 := by decide +kernel
private theorem endpoint_7_47_prefix_4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 4 178965796174999075 = some 178965796174999075 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 2 2 178965796174999075 178965796174999075 178965796174999075 endpoint_7_47_window_0 endpoint_7_47_window_2
private theorem endpoint_7_47_window_4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 4 2 178965796174999075 = some 178965796174999075 := by decide +kernel
private theorem endpoint_7_47_prefix_6 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 6 178965796174999075 = some 178965796174999075 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 4 2 178965796174999075 178965796174999075 178965796174999075 endpoint_7_47_prefix_4 endpoint_7_47_window_4

def endpoint_7_47 : CertifiedEndpoint :=
  ⟨⟨7, 47, 3749⟩, 178965796174999075, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_47_flag endpoint_7_47_sources 6 178965796174999075 178965796174999075 rfl endpoint_7_47_base endpoint_7_47_prefix_6) (by decide)⟩
private def endpoint_7_48_flag : Flag := ⟨7, 48, 3721⟩
private def endpoint_7_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_48_base : receiptBase endpoint_7_48_flag endpoint_7_48_sources = some 180908972656623170 := by decide +kernel
private theorem endpoint_7_48_window_0 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 2 180908972656623170 = some 180908972656623170 := by decide +kernel
private theorem endpoint_7_48_window_2 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 2 2 180908972656623170 = some 180908972656623170 := by decide +kernel
private theorem endpoint_7_48_prefix_4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 4 180908972656623170 = some 180908972656623170 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 2 2 180908972656623170 180908972656623170 180908972656623170 endpoint_7_48_window_0 endpoint_7_48_window_2
private theorem endpoint_7_48_window_4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 4 2 180908972656623170 = some 180908972656623170 := by decide +kernel
private theorem endpoint_7_48_prefix_6 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 6 180908972656623170 = some 180908972656623170 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 4 2 180908972656623170 180908972656623170 180908972656623170 endpoint_7_48_prefix_4 endpoint_7_48_window_4

def endpoint_7_48 : CertifiedEndpoint :=
  ⟨⟨7, 48, 3721⟩, 180908972656623170, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_48_flag endpoint_7_48_sources 6 180908972656623170 180908972656623170 rfl endpoint_7_48_base endpoint_7_48_prefix_6) (by decide)⟩
private def endpoint_7_49_flag : Flag := ⟨7, 49, 3692⟩
private def endpoint_7_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_49_base : receiptBase endpoint_7_49_flag endpoint_7_49_sources = some 182754142604551023 := by decide +kernel
private theorem endpoint_7_49_window_0 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 2 182754142604551023 = some 182754142604551023 := by decide +kernel
private theorem endpoint_7_49_window_2 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 2 2 182754142604551023 = some 182754142604551023 := by decide +kernel
private theorem endpoint_7_49_prefix_4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 4 182754142604551023 = some 182754142604551023 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 2 2 182754142604551023 182754142604551023 182754142604551023 endpoint_7_49_window_0 endpoint_7_49_window_2
private theorem endpoint_7_49_window_4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 4 2 182754142604551023 = some 182754142604551023 := by decide +kernel
private theorem endpoint_7_49_prefix_6 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 6 182754142604551023 = some 182754142604551023 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 4 2 182754142604551023 182754142604551023 182754142604551023 endpoint_7_49_prefix_4 endpoint_7_49_window_4

def endpoint_7_49 : CertifiedEndpoint :=
  ⟨⟨7, 49, 3692⟩, 182754142604551023, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_49_flag endpoint_7_49_sources 6 182754142604551023 182754142604551023 rfl endpoint_7_49_base endpoint_7_49_prefix_6) (by decide)⟩
private def endpoint_7_50_flag : Flag := ⟨7, 50, 3663⟩
private def endpoint_7_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_50_base : receiptBase endpoint_7_50_flag endpoint_7_50_sources = some 184548332998367748 := by decide +kernel
private theorem endpoint_7_50_window_0 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 2 184548332998367748 = some 184548332998367748 := by decide +kernel
private theorem endpoint_7_50_window_2 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 2 2 184548332998367748 = some 184548332998367748 := by decide +kernel
private theorem endpoint_7_50_prefix_4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 4 184548332998367748 = some 184548332998367748 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 2 2 184548332998367748 184548332998367748 184548332998367748 endpoint_7_50_window_0 endpoint_7_50_window_2
private theorem endpoint_7_50_window_4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 4 2 184548332998367748 = some 184548332998367748 := by decide +kernel
private theorem endpoint_7_50_prefix_6 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 6 184548332998367748 = some 184548332998367748 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 4 2 184548332998367748 184548332998367748 184548332998367748 endpoint_7_50_prefix_4 endpoint_7_50_window_4

def endpoint_7_50 : CertifiedEndpoint :=
  ⟨⟨7, 50, 3663⟩, 184548332998367748, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_50_flag endpoint_7_50_sources 6 184548332998367748 184548332998367748 rfl endpoint_7_50_base endpoint_7_50_prefix_6) (by decide)⟩
private def endpoint_7_51_flag : Flag := ⟨7, 51, 3634⟩
private def endpoint_7_51_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_51_base : receiptBase endpoint_7_51_flag endpoint_7_51_sources = some 186291543838073344 := by decide +kernel
private theorem endpoint_7_51_window_0 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 2 186291543838073344 = some 186291543838073344 := by decide +kernel
private theorem endpoint_7_51_window_2 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 2 2 186291543838073344 = some 186291543838073344 := by decide +kernel
private theorem endpoint_7_51_prefix_4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 4 186291543838073344 = some 186291543838073344 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 2 2 186291543838073344 186291543838073344 186291543838073344 endpoint_7_51_window_0 endpoint_7_51_window_2
private theorem endpoint_7_51_window_4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 4 2 186291543838073344 = some 186291543838073344 := by decide +kernel
private theorem endpoint_7_51_prefix_6 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 6 186291543838073344 = some 186291543838073344 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 4 2 186291543838073344 186291543838073344 186291543838073344 endpoint_7_51_prefix_4 endpoint_7_51_window_4

def endpoint_7_51 : CertifiedEndpoint :=
  ⟨⟨7, 51, 3634⟩, 186291543838073344, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_51_flag endpoint_7_51_sources 6 186291543838073344 186291543838073344 rfl endpoint_7_51_base endpoint_7_51_prefix_6) (by decide)⟩
private def endpoint_7_52_flag : Flag := ⟨7, 52, 3603⟩
private def endpoint_7_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_52_base : receiptBase endpoint_7_52_flag endpoint_7_52_sources = some 189045858774757907 := by decide +kernel
private theorem endpoint_7_52_window_0 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 2 189045858774757907 = some 189045858774757907 := by decide +kernel
private theorem endpoint_7_52_window_2 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 2 2 189045858774757907 = some 189045858774757907 := by decide +kernel
private theorem endpoint_7_52_prefix_4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 4 189045858774757907 = some 189045858774757907 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 2 2 189045858774757907 189045858774757907 189045858774757907 endpoint_7_52_window_0 endpoint_7_52_window_2
private theorem endpoint_7_52_window_4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 4 2 189045858774757907 = some 189045858774757907 := by decide +kernel
private theorem endpoint_7_52_prefix_6 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 6 189045858774757907 = some 189045858774757907 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 4 2 189045858774757907 189045858774757907 189045858774757907 endpoint_7_52_prefix_4 endpoint_7_52_window_4

def endpoint_7_52 : CertifiedEndpoint :=
  ⟨⟨7, 52, 3603⟩, 189045858774757907, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_52_flag endpoint_7_52_sources 6 189045858774757907 189045858774757907 rfl endpoint_7_52_base endpoint_7_52_prefix_6) (by decide)⟩
private def endpoint_7_53_flag : Flag := ⟨7, 53, 3572⟩
private def endpoint_7_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_53_base : receiptBase endpoint_7_53_flag endpoint_7_53_sources = some 190583792505257732 := by decide +kernel
private theorem endpoint_7_53_window_0 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 2 190583792505257732 = some 190583792505257732 := by decide +kernel
private theorem endpoint_7_53_window_2 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 2 2 190583792505257732 = some 190583792505257732 := by decide +kernel
private theorem endpoint_7_53_prefix_4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 4 190583792505257732 = some 190583792505257732 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 2 2 190583792505257732 190583792505257732 190583792505257732 endpoint_7_53_window_0 endpoint_7_53_window_2
private theorem endpoint_7_53_window_4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 4 2 190583792505257732 = some 190583792505257732 := by decide +kernel
private theorem endpoint_7_53_prefix_6 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 6 190583792505257732 = some 190583792505257732 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 4 2 190583792505257732 190583792505257732 190583792505257732 endpoint_7_53_prefix_4 endpoint_7_53_window_4

def endpoint_7_53 : CertifiedEndpoint :=
  ⟨⟨7, 53, 3572⟩, 190583792505257732, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_53_flag endpoint_7_53_sources 6 190583792505257732 190583792505257732 rfl endpoint_7_53_base endpoint_7_53_prefix_6) (by decide)⟩
private def endpoint_7_54_flag : Flag := ⟨7, 54, 3540⟩
private def endpoint_7_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_54_base : receiptBase endpoint_7_54_flag endpoint_7_54_sources = some 192013129228271507 := by decide +kernel
private theorem endpoint_7_54_window_0 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 2 192013129228271507 = some 192013129228271507 := by decide +kernel
private theorem endpoint_7_54_window_2 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 2 2 192013129228271507 = some 192013129228271507 := by decide +kernel
private theorem endpoint_7_54_prefix_4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 4 192013129228271507 = some 192013129228271507 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 2 2 192013129228271507 192013129228271507 192013129228271507 endpoint_7_54_window_0 endpoint_7_54_window_2
private theorem endpoint_7_54_window_4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 4 2 192013129228271507 = some 192013129228271507 := by decide +kernel
private theorem endpoint_7_54_prefix_6 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 6 192013129228271507 = some 192013129228271507 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 4 2 192013129228271507 192013129228271507 192013129228271507 endpoint_7_54_prefix_4 endpoint_7_54_window_4

def endpoint_7_54 : CertifiedEndpoint :=
  ⟨⟨7, 54, 3540⟩, 192013129228271507, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_54_flag endpoint_7_54_sources 6 192013129228271507 192013129228271507 rfl endpoint_7_54_base endpoint_7_54_prefix_6) (by decide)⟩
private def endpoint_7_55_flag : Flag := ⟨7, 55, 3508⟩
private def endpoint_7_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_55_base : receiptBase endpoint_7_55_flag endpoint_7_55_sources = some 193385716889619775 := by decide +kernel
private theorem endpoint_7_55_window_0 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 2 193385716889619775 = some 193385716889619775 := by decide +kernel
private theorem endpoint_7_55_window_2 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 2 2 193385716889619775 = some 193385716889619775 := by decide +kernel
private theorem endpoint_7_55_prefix_4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 4 193385716889619775 = some 193385716889619775 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 2 2 193385716889619775 193385716889619775 193385716889619775 endpoint_7_55_window_0 endpoint_7_55_window_2
private theorem endpoint_7_55_window_4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 4 2 193385716889619775 = some 193385716889619775 := by decide +kernel
private theorem endpoint_7_55_prefix_6 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 6 193385716889619775 = some 193385716889619775 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 4 2 193385716889619775 193385716889619775 193385716889619775 endpoint_7_55_prefix_4 endpoint_7_55_window_4

def endpoint_7_55 : CertifiedEndpoint :=
  ⟨⟨7, 55, 3508⟩, 193385716889619775, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_55_flag endpoint_7_55_sources 6 193385716889619775 193385716889619775 rfl endpoint_7_55_base endpoint_7_55_prefix_6) (by decide)⟩
private def endpoint_7_56_flag : Flag := ⟨7, 56, 3474⟩
private def endpoint_7_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_56_base : receiptBase endpoint_7_56_flag endpoint_7_56_sources = some 194590875097764154 := by decide +kernel
private theorem endpoint_7_56_window_0 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 2 194590875097764154 = some 194590875097764154 := by decide +kernel
private theorem endpoint_7_56_window_2 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 2 2 194590875097764154 = some 194590875097764154 := by decide +kernel
private theorem endpoint_7_56_prefix_4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 4 194590875097764154 = some 194590875097764154 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 2 2 194590875097764154 194590875097764154 194590875097764154 endpoint_7_56_window_0 endpoint_7_56_window_2
private theorem endpoint_7_56_window_4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 4 2 194590875097764154 = some 194590875097764154 := by decide +kernel
private theorem endpoint_7_56_prefix_6 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 6 194590875097764154 = some 194590875097764154 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 4 2 194590875097764154 194590875097764154 194590875097764154 endpoint_7_56_prefix_4 endpoint_7_56_window_4

def endpoint_7_56 : CertifiedEndpoint :=
  ⟨⟨7, 56, 3474⟩, 194590875097764154, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_56_flag endpoint_7_56_sources 6 194590875097764154 194590875097764154 rfl endpoint_7_56_base endpoint_7_56_prefix_6) (by decide)⟩
private def endpoint_7_57_flag : Flag := ⟨7, 57, 3440⟩
private def endpoint_7_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_57_base : receiptBase endpoint_7_57_flag endpoint_7_57_sources = some 195735791994294379 := by decide +kernel
private theorem endpoint_7_57_window_0 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 2 195735791994294379 = some 195735791994294379 := by decide +kernel
private theorem endpoint_7_57_window_2 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 2 2 195735791994294379 = some 195735791994294379 := by decide +kernel
private theorem endpoint_7_57_prefix_4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 4 195735791994294379 = some 195735791994294379 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 2 2 195735791994294379 195735791994294379 195735791994294379 endpoint_7_57_window_0 endpoint_7_57_window_2
private theorem endpoint_7_57_window_4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 4 2 195735791994294379 = some 195735791994294379 := by decide +kernel
private theorem endpoint_7_57_prefix_6 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 6 195735791994294379 = some 195735791994294379 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 4 2 195735791994294379 195735791994294379 195735791994294379 endpoint_7_57_prefix_4 endpoint_7_57_window_4

def endpoint_7_57 : CertifiedEndpoint :=
  ⟨⟨7, 57, 3440⟩, 195735791994294379, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_57_flag endpoint_7_57_sources 6 195735791994294379 195735791994294379 rfl endpoint_7_57_base endpoint_7_57_prefix_6) (by decide)⟩
private def endpoint_7_58_flag : Flag := ⟨7, 58, 3404⟩
private def endpoint_7_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_58_base : receiptBase endpoint_7_58_flag endpoint_7_58_sources = some 197338700951173712 := by decide +kernel
private theorem endpoint_7_58_window_0 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 2 197338700951173712 = some 197338700951173712 := by decide +kernel
private theorem endpoint_7_58_window_2 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 2 2 197338700951173712 = some 197338700951173712 := by decide +kernel
private theorem endpoint_7_58_prefix_4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 4 197338700951173712 = some 197338700951173712 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 2 2 197338700951173712 197338700951173712 197338700951173712 endpoint_7_58_window_0 endpoint_7_58_window_2
private theorem endpoint_7_58_window_4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 4 2 197338700951173712 = some 197338700951173712 := by decide +kernel
private theorem endpoint_7_58_prefix_6 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 6 197338700951173712 = some 197338700951173712 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 4 2 197338700951173712 197338700951173712 197338700951173712 endpoint_7_58_prefix_4 endpoint_7_58_window_4

def endpoint_7_58 : CertifiedEndpoint :=
  ⟨⟨7, 58, 3404⟩, 197338700951173712, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_58_flag endpoint_7_58_sources 6 197338700951173712 197338700951173712 rfl endpoint_7_58_base endpoint_7_58_prefix_6) (by decide)⟩
private def endpoint_7_59_flag : Flag := ⟨7, 59, 3368⟩
private def endpoint_7_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_59_base : receiptBase endpoint_7_59_flag endpoint_7_59_sources = some 198238476268372949 := by decide +kernel
private theorem endpoint_7_59_window_0 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 2 198238476268372949 = some 198238476268372949 := by decide +kernel
private theorem endpoint_7_59_window_2 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 2 2 198238476268372949 = some 198238476268372949 := by decide +kernel
private theorem endpoint_7_59_prefix_4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 4 198238476268372949 = some 198238476268372949 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 2 2 198238476268372949 198238476268372949 198238476268372949 endpoint_7_59_window_0 endpoint_7_59_window_2
private theorem endpoint_7_59_window_4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 4 2 198238476268372949 = some 198238476268372949 := by decide +kernel
private theorem endpoint_7_59_prefix_6 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 6 198238476268372949 = some 198238476268372949 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 4 2 198238476268372949 198238476268372949 198238476268372949 endpoint_7_59_prefix_4 endpoint_7_59_window_4

def endpoint_7_59 : CertifiedEndpoint :=
  ⟨⟨7, 59, 3368⟩, 198238476268372949, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_59_flag endpoint_7_59_sources 6 198238476268372949 198238476268372949 rfl endpoint_7_59_base endpoint_7_59_prefix_6) (by decide)⟩
private def endpoint_7_60_flag : Flag := ⟨7, 60, 3330⟩
private def endpoint_7_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_60_base : receiptBase endpoint_7_60_flag endpoint_7_60_sources = some 198956475106512149 := by decide +kernel
private theorem endpoint_7_60_window_0 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 2 198956475106512149 = some 198956475106512149 := by decide +kernel
private theorem endpoint_7_60_window_2 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 2 2 198956475106512149 = some 198956475106512149 := by decide +kernel
private theorem endpoint_7_60_prefix_4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 4 198956475106512149 = some 198956475106512149 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 2 2 198956475106512149 198956475106512149 198956475106512149 endpoint_7_60_window_0 endpoint_7_60_window_2
private theorem endpoint_7_60_window_4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 4 2 198956475106512149 = some 198956475106512149 := by decide +kernel
private theorem endpoint_7_60_prefix_6 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 6 198956475106512149 = some 198956475106512149 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 4 2 198956475106512149 198956475106512149 198956475106512149 endpoint_7_60_prefix_4 endpoint_7_60_window_4

def endpoint_7_60 : CertifiedEndpoint :=
  ⟨⟨7, 60, 3330⟩, 198956475106512149, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_60_flag endpoint_7_60_sources 6 198956475106512149 198956475106512149 rfl endpoint_7_60_base endpoint_7_60_prefix_6) (by decide)⟩
private def endpoint_7_61_flag : Flag := ⟨7, 61, 3291⟩
private def endpoint_7_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_61_base : receiptBase endpoint_7_61_flag endpoint_7_61_sources = some 199547353611904124 := by decide +kernel
private theorem endpoint_7_61_window_0 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 2 199547353611904124 = some 199547353611904124 := by decide +kernel
private theorem endpoint_7_61_window_2 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 2 2 199547353611904124 = some 199547353611904124 := by decide +kernel
private theorem endpoint_7_61_prefix_4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 4 199547353611904124 = some 199547353611904124 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 2 2 199547353611904124 199547353611904124 199547353611904124 endpoint_7_61_window_0 endpoint_7_61_window_2
private theorem endpoint_7_61_window_4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 4 2 199547353611904124 = some 199547353611904124 := by decide +kernel
private theorem endpoint_7_61_prefix_6 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 6 199547353611904124 = some 199547353611904124 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 4 2 199547353611904124 199547353611904124 199547353611904124 endpoint_7_61_prefix_4 endpoint_7_61_window_4

def endpoint_7_61 : CertifiedEndpoint :=
  ⟨⟨7, 61, 3291⟩, 199547353611904124, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_61_flag endpoint_7_61_sources 6 199547353611904124 199547353611904124 rfl endpoint_7_61_base endpoint_7_61_prefix_6) (by decide)⟩
private def endpoint_7_62_flag : Flag := ⟨7, 62, 3250⟩
private def endpoint_7_62_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_62_base : receiptBase endpoint_7_62_flag endpoint_7_62_sources = some 199947725013364445 := by decide +kernel
private theorem endpoint_7_62_window_0 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 2 199947725013364445 = some 199947725013364445 := by decide +kernel
private theorem endpoint_7_62_window_2 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 2 2 199947725013364445 = some 199947725013364445 := by decide +kernel
private theorem endpoint_7_62_prefix_4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 4 199947725013364445 = some 199947725013364445 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 2 2 199947725013364445 199947725013364445 199947725013364445 endpoint_7_62_window_0 endpoint_7_62_window_2
private theorem endpoint_7_62_window_4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 4 2 199947725013364445 = some 199947725013364445 := by decide +kernel
private theorem endpoint_7_62_prefix_6 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 6 199947725013364445 = some 199947725013364445 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 4 2 199947725013364445 199947725013364445 199947725013364445 endpoint_7_62_prefix_4 endpoint_7_62_window_4

def endpoint_7_62 : CertifiedEndpoint :=
  ⟨⟨7, 62, 3250⟩, 199947725013364445, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_62_flag endpoint_7_62_sources 6 199947725013364445 199947725013364445 rfl endpoint_7_62_base endpoint_7_62_prefix_6) (by decide)⟩
private def endpoint_7_63_flag : Flag := ⟨7, 63, 3208⟩
private def endpoint_7_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_63_base : receiptBase endpoint_7_63_flag endpoint_7_63_sources = some 202294770721687655 := by decide +kernel
private theorem endpoint_7_63_window_0 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 2 202294770721687655 = some 202294770721687655 := by decide +kernel
private theorem endpoint_7_63_window_2 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 2 2 202294770721687655 = some 202294770721687655 := by decide +kernel
private theorem endpoint_7_63_prefix_4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 4 202294770721687655 = some 202294770721687655 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 2 2 202294770721687655 202294770721687655 202294770721687655 endpoint_7_63_window_0 endpoint_7_63_window_2
private theorem endpoint_7_63_window_4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 4 2 202294770721687655 = some 202294770721687655 := by decide +kernel
private theorem endpoint_7_63_prefix_6 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 6 202294770721687655 = some 202294770721687655 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 4 2 202294770721687655 202294770721687655 202294770721687655 endpoint_7_63_prefix_4 endpoint_7_63_window_4

def endpoint_7_63 : CertifiedEndpoint :=
  ⟨⟨7, 63, 3208⟩, 202294770721687655, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_63_flag endpoint_7_63_sources 6 202294770721687655 202294770721687655 rfl endpoint_7_63_base endpoint_7_63_prefix_6) (by decide)⟩
private def endpoint_7_64_flag : Flag := ⟨7, 64, 3164⟩
private def endpoint_7_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_64_base : receiptBase endpoint_7_64_flag endpoint_7_64_sources = some 202344911210269743 := by decide +kernel
private theorem endpoint_7_64_window_0 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 2 202344911210269743 = some 202344911210269743 := by decide +kernel
private theorem endpoint_7_64_window_2 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 2 2 202344911210269743 = some 202344911210269743 := by decide +kernel
private theorem endpoint_7_64_prefix_4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 4 202344911210269743 = some 202344911210269743 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 2 2 202344911210269743 202344911210269743 202344911210269743 endpoint_7_64_window_0 endpoint_7_64_window_2
private theorem endpoint_7_64_window_4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 4 2 202344911210269743 = some 202344911210269743 := by decide +kernel
private theorem endpoint_7_64_prefix_6 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 6 202344911210269743 = some 202344911210269743 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 4 2 202344911210269743 202344911210269743 202344911210269743 endpoint_7_64_prefix_4 endpoint_7_64_window_4

def endpoint_7_64 : CertifiedEndpoint :=
  ⟨⟨7, 64, 3164⟩, 202344911210269743, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_64_flag endpoint_7_64_sources 6 202344911210269743 202344911210269743 rfl endpoint_7_64_base endpoint_7_64_prefix_6) (by decide)⟩
private def endpoint_7_65_flag : Flag := ⟨7, 65, 3118⟩
private def endpoint_7_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_65_base : receiptBase endpoint_7_65_flag endpoint_7_65_sources = some 202188103169912260 := by decide +kernel
private theorem endpoint_7_65_window_0 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 2 202188103169912260 = some 202188103169912260 := by decide +kernel
private theorem endpoint_7_65_window_2 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 2 2 202188103169912260 = some 202188103169912260 := by decide +kernel
private theorem endpoint_7_65_prefix_4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 4 202188103169912260 = some 202188103169912260 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 2 2 202188103169912260 202188103169912260 202188103169912260 endpoint_7_65_window_0 endpoint_7_65_window_2
private theorem endpoint_7_65_window_4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 4 2 202188103169912260 = some 202188103169912260 := by decide +kernel
private theorem endpoint_7_65_prefix_6 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 6 202188103169912260 = some 202188103169912260 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 4 2 202188103169912260 202188103169912260 202188103169912260 endpoint_7_65_prefix_4 endpoint_7_65_window_4

def endpoint_7_65 : CertifiedEndpoint :=
  ⟨⟨7, 65, 3118⟩, 202188103169912260, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_65_flag endpoint_7_65_sources 6 202188103169912260 202188103169912260 rfl endpoint_7_65_base endpoint_7_65_prefix_6) (by decide)⟩
private def endpoint_7_66_flag : Flag := ⟨7, 66, 3069⟩
private def endpoint_7_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_66_base : receiptBase endpoint_7_66_flag endpoint_7_66_sources = some 201753949507386040 := by decide +kernel
private theorem endpoint_7_66_window_0 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 2 201753949507386040 = some 201753949507386040 := by decide +kernel
private theorem endpoint_7_66_window_2 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 2 2 201753949507386040 = some 201753949507386040 := by decide +kernel
private theorem endpoint_7_66_prefix_4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 4 201753949507386040 = some 201753949507386040 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 2 2 201753949507386040 201753949507386040 201753949507386040 endpoint_7_66_window_0 endpoint_7_66_window_2
private theorem endpoint_7_66_window_4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 4 2 201753949507386040 = some 201753949507386040 := by decide +kernel
private theorem endpoint_7_66_prefix_6 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 6 201753949507386040 = some 201753949507386040 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 4 2 201753949507386040 201753949507386040 201753949507386040 endpoint_7_66_prefix_4 endpoint_7_66_window_4

def endpoint_7_66 : CertifiedEndpoint :=
  ⟨⟨7, 66, 3069⟩, 201753949507386040, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_66_flag endpoint_7_66_sources 6 201753949507386040 201753949507386040 rfl endpoint_7_66_base endpoint_7_66_prefix_6) (by decide)⟩
private def endpoint_7_67_flag : Flag := ⟨7, 67, 3018⟩
private def endpoint_7_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_67_base : receiptBase endpoint_7_67_flag endpoint_7_67_sources = some 202549244137004430 := by decide +kernel
private theorem endpoint_7_67_window_0 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 2 202549244137004430 = some 202549244137004430 := by decide +kernel
private theorem endpoint_7_67_window_2 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 2 2 202549244137004430 = some 202549244137004430 := by decide +kernel
private theorem endpoint_7_67_prefix_4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 4 202549244137004430 = some 202549244137004430 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 2 2 202549244137004430 202549244137004430 202549244137004430 endpoint_7_67_window_0 endpoint_7_67_window_2
private theorem endpoint_7_67_window_4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 4 2 202549244137004430 = some 202549244137004430 := by decide +kernel
private theorem endpoint_7_67_prefix_6 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 6 202549244137004430 = some 202549244137004430 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 4 2 202549244137004430 202549244137004430 202549244137004430 endpoint_7_67_prefix_4 endpoint_7_67_window_4

def endpoint_7_67 : CertifiedEndpoint :=
  ⟨⟨7, 67, 3018⟩, 202549244137004430, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_67_flag endpoint_7_67_sources 6 202549244137004430 202549244137004430 rfl endpoint_7_67_base endpoint_7_67_prefix_6) (by decide)⟩
private def endpoint_7_68_flag : Flag := ⟨7, 68, 2964⟩
private def endpoint_7_68_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_68_base : receiptBase endpoint_7_68_flag endpoint_7_68_sources = some 201598867467563292 := by decide +kernel
private theorem endpoint_7_68_window_0 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 2 201598867467563292 = some 201598867467563292 := by decide +kernel
private theorem endpoint_7_68_window_2 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 2 2 201598867467563292 = some 201598867467563292 := by decide +kernel
private theorem endpoint_7_68_prefix_4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 4 201598867467563292 = some 201598867467563292 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 2 2 201598867467563292 201598867467563292 201598867467563292 endpoint_7_68_window_0 endpoint_7_68_window_2
private theorem endpoint_7_68_window_4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 4 2 201598867467563292 = some 201598867467563292 := by decide +kernel
private theorem endpoint_7_68_prefix_6 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 6 201598867467563292 = some 201598867467563292 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 4 2 201598867467563292 201598867467563292 201598867467563292 endpoint_7_68_prefix_4 endpoint_7_68_window_4

def endpoint_7_68 : CertifiedEndpoint :=
  ⟨⟨7, 68, 2964⟩, 201598867467563292, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_68_flag endpoint_7_68_sources 6 201598867467563292 201598867467563292 rfl endpoint_7_68_base endpoint_7_68_prefix_6) (by decide)⟩
private def endpoint_7_69_flag : Flag := ⟨7, 69, 2907⟩
private def endpoint_7_69_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_69_base : receiptBase endpoint_7_69_flag endpoint_7_69_sources = some 200346448330469279 := by decide +kernel
private theorem endpoint_7_69_window_0 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 2 200346448330469279 = some 200346448330469279 := by decide +kernel
private theorem endpoint_7_69_window_2 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 2 2 200346448330469279 = some 200346448330469279 := by decide +kernel
private theorem endpoint_7_69_prefix_4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 4 200346448330469279 = some 200346448330469279 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 2 2 200346448330469279 200346448330469279 200346448330469279 endpoint_7_69_window_0 endpoint_7_69_window_2
private theorem endpoint_7_69_window_4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 4 2 200346448330469279 = some 200346448330469279 := by decide +kernel
private theorem endpoint_7_69_prefix_6 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 6 200346448330469279 = some 200346448330469279 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 4 2 200346448330469279 200346448330469279 200346448330469279 endpoint_7_69_prefix_4 endpoint_7_69_window_4

def endpoint_7_69 : CertifiedEndpoint :=
  ⟨⟨7, 69, 2907⟩, 200346448330469279, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_69_flag endpoint_7_69_sources 6 200346448330469279 200346448330469279 rfl endpoint_7_69_base endpoint_7_69_prefix_6) (by decide)⟩
private def endpoint_7_70_flag : Flag := ⟨7, 70, 2848⟩
private def endpoint_7_70_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_7_70_base : receiptBase endpoint_7_70_flag endpoint_7_70_sources = some 200323182481869805 := by decide +kernel
private theorem endpoint_7_70_window_0 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 2 200323182481869805 = some 200323182481869805 := by decide +kernel
private theorem endpoint_7_70_window_2 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 2 2 200323182481869805 = some 200323182481869805 := by decide +kernel
private theorem endpoint_7_70_prefix_4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 4 200323182481869805 = some 200323182481869805 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 2 2 200323182481869805 200323182481869805 200323182481869805 endpoint_7_70_window_0 endpoint_7_70_window_2
private theorem endpoint_7_70_window_4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 4 2 200323182481869805 = some 200323182481869805 := by decide +kernel
private theorem endpoint_7_70_prefix_6 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 6 200323182481869805 = some 200323182481869805 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 4 2 200323182481869805 200323182481869805 200323182481869805 endpoint_7_70_prefix_4 endpoint_7_70_window_4

def endpoint_7_70 : CertifiedEndpoint :=
  ⟨⟨7, 70, 2848⟩, 200323182481869805, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_7_70_flag endpoint_7_70_sources 6 200323182481869805 200323182481869805 rfl endpoint_7_70_base endpoint_7_70_prefix_6) (by decide)⟩
private def endpoint_7_71_flag : Flag := ⟨7, 71, 2786⟩
private def endpoint_7_71_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_71_base : receiptBase endpoint_7_71_flag endpoint_7_71_sources = some 199996815466296341 := by decide +kernel
private theorem endpoint_7_71_window_0 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 2 199996815466296341 = some 199996815466296341 := by decide +kernel
private theorem endpoint_7_71_window_2 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 2 2 199996815466296341 = some 199996815466296341 := by decide +kernel
private theorem endpoint_7_71_prefix_4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 4 199996815466296341 = some 199996815466296341 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 2 2 199996815466296341 199996815466296341 199996815466296341 endpoint_7_71_window_0 endpoint_7_71_window_2
private theorem endpoint_7_71_window_4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 4 2 199996815466296341 = some 199996815466296341 := by decide +kernel
private theorem endpoint_7_71_prefix_6 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 6 199996815466296341 = some 199996815466296341 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 4 2 199996815466296341 199996815466296341 199996815466296341 endpoint_7_71_prefix_4 endpoint_7_71_window_4

def endpoint_7_71 : CertifiedEndpoint :=
  ⟨⟨7, 71, 2786⟩, 199996815466296341, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_71_flag endpoint_7_71_sources 6 199996815466296341 199996815466296341 rfl endpoint_7_71_base endpoint_7_71_prefix_6) (by decide)⟩
private def endpoint_7_72_flag : Flag := ⟨7, 72, 2721⟩
private def endpoint_7_72_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_72_base : receiptBase endpoint_7_72_flag endpoint_7_72_sources = some 197833090760548831 := by decide +kernel
private theorem endpoint_7_72_window_0 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 2 197833090760548831 = some 197833090760548831 := by decide +kernel
private theorem endpoint_7_72_window_2 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 2 2 197833090760548831 = some 197833090760548831 := by decide +kernel
private theorem endpoint_7_72_prefix_4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 4 197833090760548831 = some 197833090760548831 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 2 2 197833090760548831 197833090760548831 197833090760548831 endpoint_7_72_window_0 endpoint_7_72_window_2
private theorem endpoint_7_72_window_4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 4 2 197833090760548831 = some 197833090760548831 := by decide +kernel
private theorem endpoint_7_72_prefix_6 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 6 197833090760548831 = some 197833090760548831 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 4 2 197833090760548831 197833090760548831 197833090760548831 endpoint_7_72_prefix_4 endpoint_7_72_window_4

def endpoint_7_72 : CertifiedEndpoint :=
  ⟨⟨7, 72, 2721⟩, 197833090760548831, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_72_flag endpoint_7_72_sources 6 197833090760548831 197833090760548831 rfl endpoint_7_72_base endpoint_7_72_prefix_6) (by decide)⟩
private def endpoint_7_73_flag : Flag := ⟨7, 73, 2653⟩
private def endpoint_7_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_73_base : receiptBase endpoint_7_73_flag endpoint_7_73_sources = some 198226489515480906 := by decide +kernel
private theorem endpoint_7_73_window_0 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 2 198226489515480906 = some 198226489515480906 := by decide +kernel
private theorem endpoint_7_73_window_2 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 2 2 198226489515480906 = some 198226489515480906 := by decide +kernel
private theorem endpoint_7_73_prefix_4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 4 198226489515480906 = some 198226489515480906 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 2 2 198226489515480906 198226489515480906 198226489515480906 endpoint_7_73_window_0 endpoint_7_73_window_2
private theorem endpoint_7_73_window_4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 4 2 198226489515480906 = some 198226489515480906 := by decide +kernel
private theorem endpoint_7_73_prefix_6 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 6 198226489515480906 = some 198226489515480906 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 4 2 198226489515480906 198226489515480906 198226489515480906 endpoint_7_73_prefix_4 endpoint_7_73_window_4

def endpoint_7_73 : CertifiedEndpoint :=
  ⟨⟨7, 73, 2653⟩, 198226489515480906, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_73_flag endpoint_7_73_sources 6 198226489515480906 198226489515480906 rfl endpoint_7_73_base endpoint_7_73_prefix_6) (by decide)⟩
private def endpoint_7_74_flag : Flag := ⟨7, 74, 2583⟩
private def endpoint_7_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_74_base : receiptBase endpoint_7_74_flag endpoint_7_74_sources = some 195411604188615395 := by decide +kernel
private theorem endpoint_7_74_window_0 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 2 195411604188615395 = some 195411604188615395 := by decide +kernel
private theorem endpoint_7_74_window_2 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 2 2 195411604188615395 = some 195411604188615395 := by decide +kernel
private theorem endpoint_7_74_prefix_4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 4 195411604188615395 = some 195411604188615395 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 2 2 195411604188615395 195411604188615395 195411604188615395 endpoint_7_74_window_0 endpoint_7_74_window_2
private theorem endpoint_7_74_window_4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 4 2 195411604188615395 = some 195411604188615395 := by decide +kernel
private theorem endpoint_7_74_prefix_6 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 6 195411604188615395 = some 195411604188615395 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 4 2 195411604188615395 195411604188615395 195411604188615395 endpoint_7_74_prefix_4 endpoint_7_74_window_4

def endpoint_7_74 : CertifiedEndpoint :=
  ⟨⟨7, 74, 2583⟩, 195411604188615395, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_74_flag endpoint_7_74_sources 6 195411604188615395 195411604188615395 rfl endpoint_7_74_base endpoint_7_74_prefix_6) (by decide)⟩
private def endpoint_7_75_flag : Flag := ⟨7, 75, 2510⟩
private def endpoint_7_75_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_75_base : receiptBase endpoint_7_75_flag endpoint_7_75_sources = some 192237742802610059 := by decide +kernel
private theorem endpoint_7_75_window_0 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 2 192237742802610059 = some 192237742802610059 := by decide +kernel
private theorem endpoint_7_75_window_2 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 2 2 192237742802610059 = some 192237742802610059 := by decide +kernel
private theorem endpoint_7_75_prefix_4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 4 192237742802610059 = some 192237742802610059 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 2 2 192237742802610059 192237742802610059 192237742802610059 endpoint_7_75_window_0 endpoint_7_75_window_2
private theorem endpoint_7_75_window_4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 4 2 192237742802610059 = some 192237742802610059 := by decide +kernel
private theorem endpoint_7_75_prefix_6 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 6 192237742802610059 = some 192237742802610059 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 4 2 192237742802610059 192237742802610059 192237742802610059 endpoint_7_75_prefix_4 endpoint_7_75_window_4

def endpoint_7_75 : CertifiedEndpoint :=
  ⟨⟨7, 75, 2510⟩, 192237742802610059, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_75_flag endpoint_7_75_sources 6 192237742802610059 192237742802610059 rfl endpoint_7_75_base endpoint_7_75_prefix_6) (by decide)⟩
private def endpoint_7_76_flag : Flag := ⟨7, 76, 2435⟩
private def endpoint_7_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_76_base : receiptBase endpoint_7_76_flag endpoint_7_76_sources = some 192359404350951784 := by decide +kernel
private theorem endpoint_7_76_window_0 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 2 192359404350951784 = some 192359404350951784 := by decide +kernel
private theorem endpoint_7_76_window_2 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 2 2 192359404350951784 = some 192359404350951784 := by decide +kernel
private theorem endpoint_7_76_prefix_4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 4 192359404350951784 = some 192359404350951784 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 2 2 192359404350951784 192359404350951784 192359404350951784 endpoint_7_76_window_0 endpoint_7_76_window_2
private theorem endpoint_7_76_window_4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 4 2 192359404350951784 = some 192359404350951784 := by decide +kernel
private theorem endpoint_7_76_prefix_6 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 6 192359404350951784 = some 192359404350951784 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 4 2 192359404350951784 192359404350951784 192359404350951784 endpoint_7_76_prefix_4 endpoint_7_76_window_4

def endpoint_7_76 : CertifiedEndpoint :=
  ⟨⟨7, 76, 2435⟩, 192359404350951784, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_76_flag endpoint_7_76_sources 6 192359404350951784 192359404350951784 rfl endpoint_7_76_base endpoint_7_76_prefix_6) (by decide)⟩
private def endpoint_7_77_flag : Flag := ⟨7, 77, 2356⟩
private def endpoint_7_77_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_77_base : receiptBase endpoint_7_77_flag endpoint_7_77_sources = some 188411751780923967 := by decide +kernel
private theorem endpoint_7_77_window_0 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 2 188411751780923967 = some 188411751780923967 := by decide +kernel
private theorem endpoint_7_77_window_2 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 2 2 188411751780923967 = some 188411751780923967 := by decide +kernel
private theorem endpoint_7_77_prefix_4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 4 188411751780923967 = some 188411751780923967 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 2 2 188411751780923967 188411751780923967 188411751780923967 endpoint_7_77_window_0 endpoint_7_77_window_2
private theorem endpoint_7_77_window_4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 4 2 188411751780923967 = some 188411751780923967 := by decide +kernel
private theorem endpoint_7_77_prefix_6 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 6 188411751780923967 = some 188411751780923967 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 4 2 188411751780923967 188411751780923967 188411751780923967 endpoint_7_77_prefix_4 endpoint_7_77_window_4

def endpoint_7_77 : CertifiedEndpoint :=
  ⟨⟨7, 77, 2356⟩, 188411751780923967, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_77_flag endpoint_7_77_sources 6 188411751780923967 188411751780923967 rfl endpoint_7_77_base endpoint_7_77_prefix_6) (by decide)⟩
private def endpoint_7_78_flag : Flag := ⟨7, 78, 2275⟩
private def endpoint_7_78_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_78_base : receiptBase endpoint_7_78_flag endpoint_7_78_sources = some 184157053933630242 := by decide +kernel
private theorem endpoint_7_78_window_0 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 2 184157053933630242 = some 184157053933630242 := by decide +kernel
private theorem endpoint_7_78_window_2 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 2 2 184157053933630242 = some 184157053933630242 := by decide +kernel
private theorem endpoint_7_78_prefix_4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 4 184157053933630242 = some 184157053933630242 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 2 2 184157053933630242 184157053933630242 184157053933630242 endpoint_7_78_window_0 endpoint_7_78_window_2
private theorem endpoint_7_78_window_4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 4 2 184157053933630242 = some 184157053933630242 := by decide +kernel
private theorem endpoint_7_78_prefix_6 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 6 184157053933630242 = some 184157053933630242 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 4 2 184157053933630242 184157053933630242 184157053933630242 endpoint_7_78_prefix_4 endpoint_7_78_window_4

def endpoint_7_78 : CertifiedEndpoint :=
  ⟨⟨7, 78, 2275⟩, 184157053933630242, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_78_flag endpoint_7_78_sources 6 184157053933630242 184157053933630242 rfl endpoint_7_78_base endpoint_7_78_prefix_6) (by decide)⟩
private def endpoint_7_79_flag : Flag := ⟨7, 79, 2191⟩
private def endpoint_7_79_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_7_79_base : receiptBase endpoint_7_79_flag endpoint_7_79_sources = some 179466006895002435 := by decide +kernel
private theorem endpoint_7_79_window_0 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 2 179466006895002435 = some 179466006895002435 := by decide +kernel
private theorem endpoint_7_79_window_2 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 2 2 179466006895002435 = some 179466006895002435 := by decide +kernel
private theorem endpoint_7_79_prefix_4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 4 179466006895002435 = some 179466006895002435 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 2 2 179466006895002435 179466006895002435 179466006895002435 endpoint_7_79_window_0 endpoint_7_79_window_2
private theorem endpoint_7_79_window_4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 4 2 179466006895002435 = some 179466006895002435 := by decide +kernel
private theorem endpoint_7_79_prefix_6 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 6 179466006895002435 = some 179466006895002435 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 4 2 179466006895002435 179466006895002435 179466006895002435 endpoint_7_79_prefix_4 endpoint_7_79_window_4

def endpoint_7_79 : CertifiedEndpoint :=
  ⟨⟨7, 79, 2191⟩, 179466006895002435, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_7_79_flag endpoint_7_79_sources 6 179466006895002435 179466006895002435 rfl endpoint_7_79_base endpoint_7_79_prefix_6) (by decide)⟩
private def endpoint_7_80_flag : Flag := ⟨7, 80, 2104⟩
private def endpoint_7_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_80_base : receiptBase endpoint_7_80_flag endpoint_7_80_sources = some 176324088623614646 := by decide +kernel
private theorem endpoint_7_80_window_0 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 2 176324088623614646 = some 176324088623614646 := by decide +kernel
private theorem endpoint_7_80_window_2 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 2 2 176324088623614646 = some 176324088623614646 := by decide +kernel
private theorem endpoint_7_80_prefix_4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 4 176324088623614646 = some 176324088623614646 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 2 2 176324088623614646 176324088623614646 176324088623614646 endpoint_7_80_window_0 endpoint_7_80_window_2
private theorem endpoint_7_80_window_4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 4 2 176324088623614646 = some 176324088623614646 := by decide +kernel
private theorem endpoint_7_80_prefix_6 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 6 176324088623614646 = some 176324088623614646 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 4 2 176324088623614646 176324088623614646 176324088623614646 endpoint_7_80_prefix_4 endpoint_7_80_window_4

def endpoint_7_80 : CertifiedEndpoint :=
  ⟨⟨7, 80, 2104⟩, 176324088623614646, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_80_flag endpoint_7_80_sources 6 176324088623614646 176324088623614646 rfl endpoint_7_80_base endpoint_7_80_prefix_6) (by decide)⟩
def endpoint_7_81 : CertifiedEndpoint :=
  ⟨⟨7, 81, 2015⟩, 255740309272870496, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_82 : CertifiedEndpoint :=
  ⟨⟨7, 82, 1923⟩, 246912877019094207, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_83 : CertifiedEndpoint :=
  ⟨⟨7, 83, 1828⟩, 237374910179889099, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_84 : CertifiedEndpoint :=
  ⟨⟨7, 84, 1730⟩, 227111255724887666, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_85 : CertifiedEndpoint :=
  ⟨⟨7, 85, 1630⟩, 216243146506428913, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_86 : CertifiedEndpoint :=
  ⟨⟨7, 86, 1527⟩, 204622410951520491, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_87 : CertifiedEndpoint :=
  ⟨⟨7, 87, 1421⟩, 192233896029794894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_88 : CertifiedEndpoint :=
  ⟨⟨7, 88, 1313⟩, 179203885603713629, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_89 : CertifiedEndpoint :=
  ⟨⟨7, 89, 1201⟩, 165236036527291998, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_90 : CertifiedEndpoint :=
  ⟨⟨7, 90, 1087⟩, 150599753225861355, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_91 : CertifiedEndpoint :=
  ⟨⟨7, 91, 970⟩, 135138445776225181, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_92 : CertifiedEndpoint :=
  ⟨⟨7, 92, 850⟩, 118836961148015970, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_93 : CertifiedEndpoint :=
  ⟨⟨7, 93, 728⟩, 101830001553899399, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_94 : CertifiedEndpoint :=
  ⟨⟨7, 94, 603⟩, 83955926060556447, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_95 : CertifiedEndpoint :=
  ⟨⟨7, 95, 475⟩, 65199581637619608, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_96 : CertifiedEndpoint :=
  ⟨⟨7, 96, 344⟩, 45545815254721376, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_97 : CertifiedEndpoint :=
  ⟨⟨7, 97, 211⟩, 25136063804690764, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_8 : CertifiedEndpoint :=
  ⟨⟨8, 8, 4513⟩, 42506316724450241, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_9 : CertifiedEndpoint :=
  ⟨⟨8, 9, 4495⟩, 45149000708753534, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_10 : CertifiedEndpoint :=
  ⟨⟨8, 10, 4477⟩, 47769109762199375, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_11 : CertifiedEndpoint :=
  ⟨⟨8, 11, 4459⟩, 56212962564981892, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_12 : CertifiedEndpoint :=
  ⟨⟨8, 12, 4441⟩, 64584984516071227, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_13 : CertifiedEndpoint :=
  ⟨⟨8, 13, 4423⟩, 72885175615467380, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_14 : CertifiedEndpoint :=
  ⟨⟨8, 14, 4404⟩, 81095084194437504, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_15 : CertifiedEndpoint :=
  ⟨⟨8, 15, 4385⟩, 89229279172974274, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_16 : CertifiedEndpoint :=
  ⟨⟨8, 16, 4367⟩, 97310094968550709, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_17 : CertifiedEndpoint :=
  ⟨⟨8, 17, 4347⟩, 105270528328747752, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_18 : CertifiedEndpoint :=
  ⟨⟨8, 18, 4328⟩, 113177582505984460, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_19 : CertifiedEndpoint :=
  ⟨⟨8, 19, 4309⟩, 121008923082787814, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_20 : CertifiedEndpoint :=
  ⟨⟨8, 20, 4289⟩, 128734450144204451, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_21 : CertifiedEndpoint :=
  ⟨⟨8, 21, 4270⟩, 136412422145771011, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_22 : CertifiedEndpoint :=
  ⟨⟨8, 22, 4250⟩, 143980697883210682, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_23 : CertifiedEndpoint :=
  ⟨⟨8, 23, 4229⟩, 151433453233413206, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_24 : CertifiedEndpoint :=
  ⟨⟨8, 24, 4209⟩, 158840594898135739, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_25 : CertifiedEndpoint :=
  ⟨⟨8, 25, 4188⟩, 166128333426880953, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_26 : CertifiedEndpoint :=
  ⟨⟨8, 26, 4168⟩, 173374341018886348, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_27 : CertifiedEndpoint :=
  ⟨⟨8, 27, 4147⟩, 180497062726174252, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_28 : CertifiedEndpoint :=
  ⟨⟨8, 28, 4125⟩, 187490674425634407, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_29 : CertifiedEndpoint :=
  ⟨⟨8, 29, 4104⟩, 194444496562724829, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_30 : CertifiedEndpoint :=
  ⟨⟨8, 30, 4082⟩, 201265325943247330, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_31 : CertifiedEndpoint :=
  ⟨⟨8, 31, 4060⟩, 207998793477115961, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_32 : CertifiedEndpoint :=
  ⟨⟨8, 32, 4038⟩, 214644899164330722, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_33 : CertifiedEndpoint :=
  ⟨⟨8, 33, 4015⟩, 221148305223127132, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_34 : CertifiedEndpoint :=
  ⟨⟨8, 34, 3992⟩, 227560466686529500, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_35 : CertifiedEndpoint :=
  ⟨⟨8, 35, 3969⟩, 233881383554537826, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_36 : CertifiedEndpoint :=
  ⟨⟨8, 36, 3946⟩, 240111055827152110, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_37 : CertifiedEndpoint :=
  ⟨⟨8, 37, 3922⟩, 246186380225127527, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_38 : CertifiedEndpoint :=
  ⟨⟨8, 38, 3898⟩, 252166577278968730, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_8_39_flag : Flag := ⟨8, 39, 3873⟩
private def endpoint_8_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_39_base : receiptBase endpoint_8_39_flag endpoint_8_39_sources = some 171235044474167951 := by decide +kernel
private theorem endpoint_8_39_window_0 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 2 171235044474167951 = some 171235044474167951 := by decide +kernel
private theorem endpoint_8_39_window_2 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 2 2 171235044474167951 = some 171235044474167951 := by decide +kernel
private theorem endpoint_8_39_prefix_4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 4 171235044474167951 = some 171235044474167951 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 2 2 171235044474167951 171235044474167951 171235044474167951 endpoint_8_39_window_0 endpoint_8_39_window_2
private theorem endpoint_8_39_window_4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 4 2 171235044474167951 = some 171235044474167951 := by decide +kernel
private theorem endpoint_8_39_prefix_6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 6 171235044474167951 = some 171235044474167951 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 4 2 171235044474167951 171235044474167951 171235044474167951 endpoint_8_39_prefix_4 endpoint_8_39_window_4
private theorem endpoint_8_39_window_6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 6 1 171235044474167951 = some 171235044474167951 := by decide +kernel
private theorem endpoint_8_39_prefix_7 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 7 171235044474167951 = some 171235044474167951 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 6 1 171235044474167951 171235044474167951 171235044474167951 endpoint_8_39_prefix_6 endpoint_8_39_window_6

def endpoint_8_39 : CertifiedEndpoint :=
  ⟨⟨8, 39, 3873⟩, 171235044474167951, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_39_flag endpoint_8_39_sources 7 171235044474167951 171235044474167951 rfl endpoint_8_39_base endpoint_8_39_prefix_7) (by decide)⟩
private def endpoint_8_40_flag : Flag := ⟨8, 40, 3848⟩
private def endpoint_8_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_40_base : receiptBase endpoint_8_40_flag endpoint_8_40_sources = some 173797674961219720 := by decide +kernel
private theorem endpoint_8_40_window_0 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 2 173797674961219720 = some 173797674961219720 := by decide +kernel
private theorem endpoint_8_40_window_2 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 2 2 173797674961219720 = some 173797674961219720 := by decide +kernel
private theorem endpoint_8_40_prefix_4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 4 173797674961219720 = some 173797674961219720 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 2 2 173797674961219720 173797674961219720 173797674961219720 endpoint_8_40_window_0 endpoint_8_40_window_2
private theorem endpoint_8_40_window_4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 4 2 173797674961219720 = some 173797674961219720 := by decide +kernel
private theorem endpoint_8_40_prefix_6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 6 173797674961219720 = some 173797674961219720 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 4 2 173797674961219720 173797674961219720 173797674961219720 endpoint_8_40_prefix_4 endpoint_8_40_window_4
private theorem endpoint_8_40_window_6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 6 1 173797674961219720 = some 173797674961219720 := by decide +kernel
private theorem endpoint_8_40_prefix_7 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 7 173797674961219720 = some 173797674961219720 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 6 1 173797674961219720 173797674961219720 173797674961219720 endpoint_8_40_prefix_6 endpoint_8_40_window_6

def endpoint_8_40 : CertifiedEndpoint :=
  ⟨⟨8, 40, 3848⟩, 173797674961219720, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_40_flag endpoint_8_40_sources 7 173797674961219720 173797674961219720 rfl endpoint_8_40_base endpoint_8_40_prefix_7) (by decide)⟩
private def endpoint_8_41_flag : Flag := ⟨8, 41, 3823⟩
private def endpoint_8_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_41_base : receiptBase endpoint_8_41_flag endpoint_8_41_sources = some 176312733629282822 := by decide +kernel
private theorem endpoint_8_41_window_0 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 2 176312733629282822 = some 176312733629282822 := by decide +kernel
private theorem endpoint_8_41_window_2 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 2 2 176312733629282822 = some 176312733629282822 := by decide +kernel
private theorem endpoint_8_41_prefix_4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 4 176312733629282822 = some 176312733629282822 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 2 2 176312733629282822 176312733629282822 176312733629282822 endpoint_8_41_window_0 endpoint_8_41_window_2
private theorem endpoint_8_41_window_4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 4 2 176312733629282822 = some 176312733629282822 := by decide +kernel
private theorem endpoint_8_41_prefix_6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 6 176312733629282822 = some 176312733629282822 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 4 2 176312733629282822 176312733629282822 176312733629282822 endpoint_8_41_prefix_4 endpoint_8_41_window_4
private theorem endpoint_8_41_window_6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 6 1 176312733629282822 = some 176312733629282822 := by decide +kernel
private theorem endpoint_8_41_prefix_7 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 7 176312733629282822 = some 176312733629282822 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 6 1 176312733629282822 176312733629282822 176312733629282822 endpoint_8_41_prefix_6 endpoint_8_41_window_6

def endpoint_8_41 : CertifiedEndpoint :=
  ⟨⟨8, 41, 3823⟩, 176312733629282822, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_41_flag endpoint_8_41_sources 7 176312733629282822 176312733629282822 rfl endpoint_8_41_base endpoint_8_41_prefix_7) (by decide)⟩
private def endpoint_8_42_flag : Flag := ⟨8, 42, 3798⟩
private def endpoint_8_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_42_base : receiptBase endpoint_8_42_flag endpoint_8_42_sources = some 178780220478357257 := by decide +kernel
private theorem endpoint_8_42_window_0 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 2 178780220478357257 = some 178780220478357257 := by decide +kernel
private theorem endpoint_8_42_window_2 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 2 2 178780220478357257 = some 178780220478357257 := by decide +kernel
private theorem endpoint_8_42_prefix_4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 4 178780220478357257 = some 178780220478357257 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 2 2 178780220478357257 178780220478357257 178780220478357257 endpoint_8_42_window_0 endpoint_8_42_window_2
private theorem endpoint_8_42_window_4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 4 2 178780220478357257 = some 178780220478357257 := by decide +kernel
private theorem endpoint_8_42_prefix_6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 6 178780220478357257 = some 178780220478357257 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 4 2 178780220478357257 178780220478357257 178780220478357257 endpoint_8_42_prefix_4 endpoint_8_42_window_4
private theorem endpoint_8_42_window_6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 6 1 178780220478357257 = some 178780220478357257 := by decide +kernel
private theorem endpoint_8_42_prefix_7 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 7 178780220478357257 = some 178780220478357257 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 6 1 178780220478357257 178780220478357257 178780220478357257 endpoint_8_42_prefix_6 endpoint_8_42_window_6

def endpoint_8_42 : CertifiedEndpoint :=
  ⟨⟨8, 42, 3798⟩, 178780220478357257, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_42_flag endpoint_8_42_sources 7 178780220478357257 178780220478357257 rfl endpoint_8_42_base endpoint_8_42_prefix_7) (by decide)⟩
private def endpoint_8_43_flag : Flag := ⟨8, 43, 3772⟩
private def endpoint_8_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_43_base : receiptBase endpoint_8_43_flag endpoint_8_43_sources = some 181152863443496130 := by decide +kernel
private theorem endpoint_8_43_window_0 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 2 181152863443496130 = some 181152863443496130 := by decide +kernel
private theorem endpoint_8_43_window_2 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 2 2 181152863443496130 = some 181152863443496130 := by decide +kernel
private theorem endpoint_8_43_prefix_4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 4 181152863443496130 = some 181152863443496130 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 2 2 181152863443496130 181152863443496130 181152863443496130 endpoint_8_43_window_0 endpoint_8_43_window_2
private theorem endpoint_8_43_window_4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 4 2 181152863443496130 = some 181152863443496130 := by decide +kernel
private theorem endpoint_8_43_prefix_6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 6 181152863443496130 = some 181152863443496130 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 4 2 181152863443496130 181152863443496130 181152863443496130 endpoint_8_43_prefix_4 endpoint_8_43_window_4
private theorem endpoint_8_43_window_6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 6 1 181152863443496130 = some 181152863443496130 := by decide +kernel
private theorem endpoint_8_43_prefix_7 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 7 181152863443496130 = some 181152863443496130 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 6 1 181152863443496130 181152863443496130 181152863443496130 endpoint_8_43_prefix_6 endpoint_8_43_window_6

def endpoint_8_43 : CertifiedEndpoint :=
  ⟨⟨8, 43, 3772⟩, 181152863443496130, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_43_flag endpoint_8_43_sources 7 181152863443496130 181152863443496130 rfl endpoint_8_43_base endpoint_8_43_prefix_7) (by decide)⟩
private def endpoint_8_44_flag : Flag := ⟨8, 44, 3745⟩
private def endpoint_8_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_44_base : receiptBase endpoint_8_44_flag endpoint_8_44_sources = some 183427864182405992 := by decide +kernel
private theorem endpoint_8_44_window_0 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 2 183427864182405992 = some 183427864182405992 := by decide +kernel
private theorem endpoint_8_44_window_2 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 2 2 183427864182405992 = some 183427864182405992 := by decide +kernel
private theorem endpoint_8_44_prefix_4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 4 183427864182405992 = some 183427864182405992 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 2 2 183427864182405992 183427864182405992 183427864182405992 endpoint_8_44_window_0 endpoint_8_44_window_2
private theorem endpoint_8_44_window_4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 4 2 183427864182405992 = some 183427864182405992 := by decide +kernel
private theorem endpoint_8_44_prefix_6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 6 183427864182405992 = some 183427864182405992 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 4 2 183427864182405992 183427864182405992 183427864182405992 endpoint_8_44_prefix_4 endpoint_8_44_window_4
private theorem endpoint_8_44_window_6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 6 1 183427864182405992 = some 183427864182405992 := by decide +kernel
private theorem endpoint_8_44_prefix_7 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 7 183427864182405992 = some 183427864182405992 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 6 1 183427864182405992 183427864182405992 183427864182405992 endpoint_8_44_prefix_6 endpoint_8_44_window_6

def endpoint_8_44 : CertifiedEndpoint :=
  ⟨⟨8, 44, 3745⟩, 183427864182405992, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_44_flag endpoint_8_44_sources 7 183427864182405992 183427864182405992 rfl endpoint_8_44_base endpoint_8_44_prefix_7) (by decide)⟩
private def endpoint_8_45_flag : Flag := ⟨8, 45, 3718⟩
private def endpoint_8_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_45_base : receiptBase endpoint_8_45_flag endpoint_8_45_sources = some 185651561979269252 := by decide +kernel
private theorem endpoint_8_45_window_0 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 2 185651561979269252 = some 185651561979269252 := by decide +kernel
private theorem endpoint_8_45_window_2 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 2 2 185651561979269252 = some 185651561979269252 := by decide +kernel
private theorem endpoint_8_45_prefix_4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 4 185651561979269252 = some 185651561979269252 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 2 2 185651561979269252 185651561979269252 185651561979269252 endpoint_8_45_window_0 endpoint_8_45_window_2
private theorem endpoint_8_45_window_4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 4 2 185651561979269252 = some 185651561979269252 := by decide +kernel
private theorem endpoint_8_45_prefix_6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 6 185651561979269252 = some 185651561979269252 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 4 2 185651561979269252 185651561979269252 185651561979269252 endpoint_8_45_prefix_4 endpoint_8_45_window_4
private theorem endpoint_8_45_window_6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 6 1 185651561979269252 = some 185651561979269252 := by decide +kernel
private theorem endpoint_8_45_prefix_7 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 7 185651561979269252 = some 185651561979269252 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 6 1 185651561979269252 185651561979269252 185651561979269252 endpoint_8_45_prefix_6 endpoint_8_45_window_6

def endpoint_8_45 : CertifiedEndpoint :=
  ⟨⟨8, 45, 3718⟩, 185651561979269252, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_45_flag endpoint_8_45_sources 7 185651561979269252 185651561979269252 rfl endpoint_8_45_base endpoint_8_45_prefix_7) (by decide)⟩
private def endpoint_8_46_flag : Flag := ⟨8, 46, 3691⟩
private def endpoint_8_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_46_base : receiptBase endpoint_8_46_flag endpoint_8_46_sources = some 187823956834085910 := by decide +kernel
private theorem endpoint_8_46_window_0 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 2 187823956834085910 = some 187823956834085910 := by decide +kernel
private theorem endpoint_8_46_window_2 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 2 2 187823956834085910 = some 187823956834085910 := by decide +kernel
private theorem endpoint_8_46_prefix_4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 4 187823956834085910 = some 187823956834085910 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 2 2 187823956834085910 187823956834085910 187823956834085910 endpoint_8_46_window_0 endpoint_8_46_window_2
private theorem endpoint_8_46_window_4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 4 2 187823956834085910 = some 187823956834085910 := by decide +kernel
private theorem endpoint_8_46_prefix_6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 6 187823956834085910 = some 187823956834085910 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 4 2 187823956834085910 187823956834085910 187823956834085910 endpoint_8_46_prefix_4 endpoint_8_46_window_4
private theorem endpoint_8_46_window_6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 6 1 187823956834085910 = some 187823956834085910 := by decide +kernel
private theorem endpoint_8_46_prefix_7 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 7 187823956834085910 = some 187823956834085910 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 6 1 187823956834085910 187823956834085910 187823956834085910 endpoint_8_46_prefix_6 endpoint_8_46_window_6

def endpoint_8_46 : CertifiedEndpoint :=
  ⟨⟨8, 46, 3691⟩, 187823956834085910, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_46_flag endpoint_8_46_sources 7 187823956834085910 187823956834085910 rfl endpoint_8_46_base endpoint_8_46_prefix_7) (by decide)⟩
private def endpoint_8_47_flag : Flag := ⟨8, 47, 3663⟩
private def endpoint_8_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_47_base : receiptBase endpoint_8_47_flag endpoint_8_47_sources = some 189894045558851138 := by decide +kernel
private theorem endpoint_8_47_window_0 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 2 189894045558851138 = some 189894045558851138 := by decide +kernel
private theorem endpoint_8_47_window_2 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 2 2 189894045558851138 = some 189894045558851138 := by decide +kernel
private theorem endpoint_8_47_prefix_4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 4 189894045558851138 = some 189894045558851138 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 2 2 189894045558851138 189894045558851138 189894045558851138 endpoint_8_47_window_0 endpoint_8_47_window_2
private theorem endpoint_8_47_window_4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 4 2 189894045558851138 = some 189894045558851138 := by decide +kernel
private theorem endpoint_8_47_prefix_6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 6 189894045558851138 = some 189894045558851138 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 4 2 189894045558851138 189894045558851138 189894045558851138 endpoint_8_47_prefix_4 endpoint_8_47_window_4
private theorem endpoint_8_47_window_6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 6 1 189894045558851138 = some 189894045558851138 := by decide +kernel
private theorem endpoint_8_47_prefix_7 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 7 189894045558851138 = some 189894045558851138 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 6 1 189894045558851138 189894045558851138 189894045558851138 endpoint_8_47_prefix_6 endpoint_8_47_window_6

def endpoint_8_47 : CertifiedEndpoint :=
  ⟨⟨8, 47, 3663⟩, 189894045558851138, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_47_flag endpoint_8_47_sources 7 189894045558851138 189894045558851138 rfl endpoint_8_47_base endpoint_8_47_prefix_7) (by decide)⟩
private def endpoint_8_48_flag : Flag := ⟨8, 48, 3634⟩
private def endpoint_8_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_48_base : receiptBase endpoint_8_48_flag endpoint_8_48_sources = some 191859029811271484 := by decide +kernel
private theorem endpoint_8_48_window_0 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 2 191859029811271484 = some 191859029811271484 := by decide +kernel
private theorem endpoint_8_48_window_2 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 2 2 191859029811271484 = some 191859029811271484 := by decide +kernel
private theorem endpoint_8_48_prefix_4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 4 191859029811271484 = some 191859029811271484 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 2 2 191859029811271484 191859029811271484 191859029811271484 endpoint_8_48_window_0 endpoint_8_48_window_2
private theorem endpoint_8_48_window_4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 4 2 191859029811271484 = some 191859029811271484 := by decide +kernel
private theorem endpoint_8_48_prefix_6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 6 191859029811271484 = some 191859029811271484 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 4 2 191859029811271484 191859029811271484 191859029811271484 endpoint_8_48_prefix_4 endpoint_8_48_window_4
private theorem endpoint_8_48_window_6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 6 1 191859029811271484 = some 191859029811271484 := by decide +kernel
private theorem endpoint_8_48_prefix_7 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 7 191859029811271484 = some 191859029811271484 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 6 1 191859029811271484 191859029811271484 191859029811271484 endpoint_8_48_prefix_6 endpoint_8_48_window_6

def endpoint_8_48 : CertifiedEndpoint :=
  ⟨⟨8, 48, 3634⟩, 191859029811271484, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_48_flag endpoint_8_48_sources 7 191859029811271484 191859029811271484 rfl endpoint_8_48_base endpoint_8_48_prefix_7) (by decide)⟩
private def endpoint_8_49_flag : Flag := ⟨8, 49, 3605⟩
private def endpoint_8_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_49_base : receiptBase endpoint_8_49_flag endpoint_8_49_sources = some 193768979998587293 := by decide +kernel
private theorem endpoint_8_49_window_0 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 2 193768979998587293 = some 193768979998587293 := by decide +kernel
private theorem endpoint_8_49_window_2 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 2 2 193768979998587293 = some 193768979998587293 := by decide +kernel
private theorem endpoint_8_49_prefix_4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 4 193768979998587293 = some 193768979998587293 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 2 2 193768979998587293 193768979998587293 193768979998587293 endpoint_8_49_window_0 endpoint_8_49_window_2
private theorem endpoint_8_49_window_4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 4 2 193768979998587293 = some 193768979998587293 := by decide +kernel
private theorem endpoint_8_49_prefix_6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 6 193768979998587293 = some 193768979998587293 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 4 2 193768979998587293 193768979998587293 193768979998587293 endpoint_8_49_prefix_4 endpoint_8_49_window_4
private theorem endpoint_8_49_window_6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 6 1 193768979998587293 = some 193768979998587293 := by decide +kernel
private theorem endpoint_8_49_prefix_7 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 7 193768979998587293 = some 193768979998587293 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 6 1 193768979998587293 193768979998587293 193768979998587293 endpoint_8_49_prefix_6 endpoint_8_49_window_6

def endpoint_8_49 : CertifiedEndpoint :=
  ⟨⟨8, 49, 3605⟩, 193768979998587293, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_49_flag endpoint_8_49_sources 7 193768979998587293 193768979998587293 rfl endpoint_8_49_base endpoint_8_49_prefix_7) (by decide)⟩
private def endpoint_8_50_flag : Flag := ⟨8, 50, 3575⟩
private def endpoint_8_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_50_base : receiptBase endpoint_8_50_flag endpoint_8_50_sources = some 195570094590500287 := by decide +kernel
private theorem endpoint_8_50_window_0 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 2 195570094590500287 = some 195570094590500287 := by decide +kernel
private theorem endpoint_8_50_window_2 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 2 2 195570094590500287 = some 195570094590500287 := by decide +kernel
private theorem endpoint_8_50_prefix_4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 4 195570094590500287 = some 195570094590500287 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 2 2 195570094590500287 195570094590500287 195570094590500287 endpoint_8_50_window_0 endpoint_8_50_window_2
private theorem endpoint_8_50_window_4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 4 2 195570094590500287 = some 195570094590500287 := by decide +kernel
private theorem endpoint_8_50_prefix_6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 6 195570094590500287 = some 195570094590500287 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 4 2 195570094590500287 195570094590500287 195570094590500287 endpoint_8_50_prefix_4 endpoint_8_50_window_4
private theorem endpoint_8_50_window_6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 6 1 195570094590500287 = some 195570094590500287 := by decide +kernel
private theorem endpoint_8_50_prefix_7 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 7 195570094590500287 = some 195570094590500287 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 6 1 195570094590500287 195570094590500287 195570094590500287 endpoint_8_50_prefix_6 endpoint_8_50_window_6

def endpoint_8_50 : CertifiedEndpoint :=
  ⟨⟨8, 50, 3575⟩, 195570094590500287, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_50_flag endpoint_8_50_sources 7 195570094590500287 195570094590500287 rfl endpoint_8_50_base endpoint_8_50_prefix_7) (by decide)⟩
private def endpoint_8_51_flag : Flag := ⟨8, 51, 3545⟩
private def endpoint_8_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_51_base : receiptBase endpoint_8_51_flag endpoint_8_51_sources = some 198373957214410005 := by decide +kernel
private theorem endpoint_8_51_window_0 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 2 198373957214410005 = some 198373957214410005 := by decide +kernel
private theorem endpoint_8_51_window_2 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 2 2 198373957214410005 = some 198373957214410005 := by decide +kernel
private theorem endpoint_8_51_prefix_4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 4 198373957214410005 = some 198373957214410005 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 2 2 198373957214410005 198373957214410005 198373957214410005 endpoint_8_51_window_0 endpoint_8_51_window_2
private theorem endpoint_8_51_window_4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 4 2 198373957214410005 = some 198373957214410005 := by decide +kernel
private theorem endpoint_8_51_prefix_6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 6 198373957214410005 = some 198373957214410005 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 4 2 198373957214410005 198373957214410005 198373957214410005 endpoint_8_51_prefix_4 endpoint_8_51_window_4
private theorem endpoint_8_51_window_6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 6 1 198373957214410005 = some 198373957214410005 := by decide +kernel
private theorem endpoint_8_51_prefix_7 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 7 198373957214410005 = some 198373957214410005 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 6 1 198373957214410005 198373957214410005 198373957214410005 endpoint_8_51_prefix_6 endpoint_8_51_window_6

def endpoint_8_51 : CertifiedEndpoint :=
  ⟨⟨8, 51, 3545⟩, 198373957214410005, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_51_flag endpoint_8_51_sources 7 198373957214410005 198373957214410005 rfl endpoint_8_51_base endpoint_8_51_prefix_7) (by decide)⟩
private def endpoint_8_52_flag : Flag := ⟨8, 52, 3514⟩
private def endpoint_8_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_52_base : receiptBase endpoint_8_52_flag endpoint_8_52_sources = some 200006011156585521 := by decide +kernel
private theorem endpoint_8_52_window_0 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 2 200006011156585521 = some 200006011156585521 := by decide +kernel
private theorem endpoint_8_52_window_2 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 2 2 200006011156585521 = some 200006011156585521 := by decide +kernel
private theorem endpoint_8_52_prefix_4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 4 200006011156585521 = some 200006011156585521 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 2 2 200006011156585521 200006011156585521 200006011156585521 endpoint_8_52_window_0 endpoint_8_52_window_2
private theorem endpoint_8_52_window_4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 4 2 200006011156585521 = some 200006011156585521 := by decide +kernel
private theorem endpoint_8_52_prefix_6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 6 200006011156585521 = some 200006011156585521 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 4 2 200006011156585521 200006011156585521 200006011156585521 endpoint_8_52_prefix_4 endpoint_8_52_window_4
private theorem endpoint_8_52_window_6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 6 1 200006011156585521 = some 200006011156585521 := by decide +kernel
private theorem endpoint_8_52_prefix_7 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 7 200006011156585521 = some 200006011156585521 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 6 1 200006011156585521 200006011156585521 200006011156585521 endpoint_8_52_prefix_6 endpoint_8_52_window_6

def endpoint_8_52 : CertifiedEndpoint :=
  ⟨⟨8, 52, 3514⟩, 200006011156585521, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_52_flag endpoint_8_52_sources 7 200006011156585521 200006011156585521 rfl endpoint_8_52_base endpoint_8_52_prefix_7) (by decide)⟩
private def endpoint_8_53_flag : Flag := ⟨8, 53, 3482⟩
private def endpoint_8_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_53_base : receiptBase endpoint_8_53_flag endpoint_8_53_sources = some 201521616475131445 := by decide +kernel
private theorem endpoint_8_53_window_0 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 2 201521616475131445 = some 201521616475131445 := by decide +kernel
private theorem endpoint_8_53_window_2 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 2 2 201521616475131445 = some 201521616475131445 := by decide +kernel
private theorem endpoint_8_53_prefix_4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 4 201521616475131445 = some 201521616475131445 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 2 2 201521616475131445 201521616475131445 201521616475131445 endpoint_8_53_window_0 endpoint_8_53_window_2
private theorem endpoint_8_53_window_4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 4 2 201521616475131445 = some 201521616475131445 := by decide +kernel
private theorem endpoint_8_53_prefix_6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 6 201521616475131445 = some 201521616475131445 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 4 2 201521616475131445 201521616475131445 201521616475131445 endpoint_8_53_prefix_4 endpoint_8_53_window_4
private theorem endpoint_8_53_window_6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 6 1 201521616475131445 = some 201521616475131445 := by decide +kernel
private theorem endpoint_8_53_prefix_7 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 7 201521616475131445 = some 201521616475131445 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 6 1 201521616475131445 201521616475131445 201521616475131445 endpoint_8_53_prefix_6 endpoint_8_53_window_6

def endpoint_8_53 : CertifiedEndpoint :=
  ⟨⟨8, 53, 3482⟩, 201521616475131445, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_53_flag endpoint_8_53_sources 7 201521616475131445 201521616475131445 rfl endpoint_8_53_base endpoint_8_53_prefix_7) (by decide)⟩
private def endpoint_8_54_flag : Flag := ⟨8, 54, 3450⟩
private def endpoint_8_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_54_base : receiptBase endpoint_8_54_flag endpoint_8_54_sources = some 202976005897866584 := by decide +kernel
private theorem endpoint_8_54_window_0 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 2 202976005897866584 = some 202976005897866584 := by decide +kernel
private theorem endpoint_8_54_window_2 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 2 2 202976005897866584 = some 202976005897866584 := by decide +kernel
private theorem endpoint_8_54_prefix_4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 4 202976005897866584 = some 202976005897866584 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 2 2 202976005897866584 202976005897866584 202976005897866584 endpoint_8_54_window_0 endpoint_8_54_window_2
private theorem endpoint_8_54_window_4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 4 2 202976005897866584 = some 202976005897866584 := by decide +kernel
private theorem endpoint_8_54_prefix_6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 6 202976005897866584 = some 202976005897866584 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 4 2 202976005897866584 202976005897866584 202976005897866584 endpoint_8_54_prefix_4 endpoint_8_54_window_4
private theorem endpoint_8_54_window_6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 6 1 202976005897866584 = some 202976005897866584 := by decide +kernel
private theorem endpoint_8_54_prefix_7 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 7 202976005897866584 = some 202976005897866584 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 6 1 202976005897866584 202976005897866584 202976005897866584 endpoint_8_54_prefix_6 endpoint_8_54_window_6

def endpoint_8_54 : CertifiedEndpoint :=
  ⟨⟨8, 54, 3450⟩, 202976005897866584, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_54_flag endpoint_8_54_sources 7 202976005897866584 202976005897866584 rfl endpoint_8_54_base endpoint_8_54_prefix_7) (by decide)⟩
private def endpoint_8_55_flag : Flag := ⟨8, 55, 3416⟩
private def endpoint_8_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_55_base : receiptBase endpoint_8_55_flag endpoint_8_55_sources = some 204251179705053535 := by decide +kernel
private theorem endpoint_8_55_window_0 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 2 204251179705053535 = some 204251179705053535 := by decide +kernel
private theorem endpoint_8_55_window_2 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 2 2 204251179705053535 = some 204251179705053535 := by decide +kernel
private theorem endpoint_8_55_prefix_4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 4 204251179705053535 = some 204251179705053535 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 2 2 204251179705053535 204251179705053535 204251179705053535 endpoint_8_55_window_0 endpoint_8_55_window_2
private theorem endpoint_8_55_window_4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 4 2 204251179705053535 = some 204251179705053535 := by decide +kernel
private theorem endpoint_8_55_prefix_6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 6 204251179705053535 = some 204251179705053535 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 4 2 204251179705053535 204251179705053535 204251179705053535 endpoint_8_55_prefix_4 endpoint_8_55_window_4
private theorem endpoint_8_55_window_6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 6 1 204251179705053535 = some 204251179705053535 := by decide +kernel
private theorem endpoint_8_55_prefix_7 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 7 204251179705053535 = some 204251179705053535 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 6 1 204251179705053535 204251179705053535 204251179705053535 endpoint_8_55_prefix_6 endpoint_8_55_window_6

def endpoint_8_55 : CertifiedEndpoint :=
  ⟨⟨8, 55, 3416⟩, 204251179705053535, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_55_flag endpoint_8_55_sources 7 204251179705053535 204251179705053535 rfl endpoint_8_55_base endpoint_8_55_prefix_7) (by decide)⟩
private def endpoint_8_56_flag : Flag := ⟨8, 56, 3382⟩
private def endpoint_8_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_56_base : receiptBase endpoint_8_56_flag endpoint_8_56_sources = some 206179802330281185 := by decide +kernel
private theorem endpoint_8_56_window_0 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 2 206179802330281185 = some 206179802330281185 := by decide +kernel
private theorem endpoint_8_56_window_2 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 2 2 206179802330281185 = some 206179802330281185 := by decide +kernel
private theorem endpoint_8_56_prefix_4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 4 206179802330281185 = some 206179802330281185 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 2 2 206179802330281185 206179802330281185 206179802330281185 endpoint_8_56_window_0 endpoint_8_56_window_2
private theorem endpoint_8_56_window_4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 4 2 206179802330281185 = some 206179802330281185 := by decide +kernel
private theorem endpoint_8_56_prefix_6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 6 206179802330281185 = some 206179802330281185 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 4 2 206179802330281185 206179802330281185 206179802330281185 endpoint_8_56_prefix_4 endpoint_8_56_window_4
private theorem endpoint_8_56_window_6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 6 1 206179802330281185 = some 206179802330281185 := by decide +kernel
private theorem endpoint_8_56_prefix_7 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 7 206179802330281185 = some 206179802330281185 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 6 1 206179802330281185 206179802330281185 206179802330281185 endpoint_8_56_prefix_6 endpoint_8_56_window_6

def endpoint_8_56 : CertifiedEndpoint :=
  ⟨⟨8, 56, 3382⟩, 206179802330281185, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_56_flag endpoint_8_56_sources 7 206179802330281185 206179802330281185 rfl endpoint_8_56_base endpoint_8_56_prefix_7) (by decide)⟩
private def endpoint_8_57_flag : Flag := ⟨8, 57, 3347⟩
private def endpoint_8_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_57_base : receiptBase endpoint_8_57_flag endpoint_8_57_sources = some 207256349435863915 := by decide +kernel
private theorem endpoint_8_57_window_0 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 2 207256349435863915 = some 207256349435863915 := by decide +kernel
private theorem endpoint_8_57_window_2 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 2 2 207256349435863915 = some 207256349435863915 := by decide +kernel
private theorem endpoint_8_57_prefix_4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 4 207256349435863915 = some 207256349435863915 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 2 2 207256349435863915 207256349435863915 207256349435863915 endpoint_8_57_window_0 endpoint_8_57_window_2
private theorem endpoint_8_57_window_4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 4 2 207256349435863915 = some 207256349435863915 := by decide +kernel
private theorem endpoint_8_57_prefix_6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 6 207256349435863915 = some 207256349435863915 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 4 2 207256349435863915 207256349435863915 207256349435863915 endpoint_8_57_prefix_4 endpoint_8_57_window_4
private theorem endpoint_8_57_window_6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 6 1 207256349435863915 = some 207256349435863915 := by decide +kernel
private theorem endpoint_8_57_prefix_7 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 7 207256349435863915 = some 207256349435863915 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 6 1 207256349435863915 207256349435863915 207256349435863915 endpoint_8_57_prefix_6 endpoint_8_57_window_6

def endpoint_8_57 : CertifiedEndpoint :=
  ⟨⟨8, 57, 3347⟩, 207256349435863915, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_57_flag endpoint_8_57_sources 7 207256349435863915 207256349435863915 rfl endpoint_8_57_base endpoint_8_57_prefix_7) (by decide)⟩

def endpointBlock03 : List CertifiedEndpoint := [
  endpoint_7_44, endpoint_7_45, endpoint_7_46, endpoint_7_47, endpoint_7_48, endpoint_7_49,
  endpoint_7_50, endpoint_7_51, endpoint_7_52, endpoint_7_53, endpoint_7_54, endpoint_7_55,
  endpoint_7_56, endpoint_7_57, endpoint_7_58, endpoint_7_59, endpoint_7_60, endpoint_7_61,
  endpoint_7_62, endpoint_7_63, endpoint_7_64, endpoint_7_65, endpoint_7_66, endpoint_7_67,
  endpoint_7_68, endpoint_7_69, endpoint_7_70, endpoint_7_71, endpoint_7_72, endpoint_7_73,
  endpoint_7_74, endpoint_7_75, endpoint_7_76, endpoint_7_77, endpoint_7_78, endpoint_7_79,
  endpoint_7_80, endpoint_7_81, endpoint_7_82, endpoint_7_83, endpoint_7_84, endpoint_7_85,
  endpoint_7_86, endpoint_7_87, endpoint_7_88, endpoint_7_89, endpoint_7_90, endpoint_7_91,
  endpoint_7_92, endpoint_7_93, endpoint_7_94, endpoint_7_95, endpoint_7_96, endpoint_7_97,
  endpoint_8_8, endpoint_8_9, endpoint_8_10, endpoint_8_11, endpoint_8_12, endpoint_8_13,
  endpoint_8_14, endpoint_8_15, endpoint_8_16, endpoint_8_17, endpoint_8_18, endpoint_8_19,
  endpoint_8_20, endpoint_8_21, endpoint_8_22, endpoint_8_23, endpoint_8_24, endpoint_8_25,
  endpoint_8_26, endpoint_8_27, endpoint_8_28, endpoint_8_29, endpoint_8_30, endpoint_8_31,
  endpoint_8_32, endpoint_8_33, endpoint_8_34, endpoint_8_35, endpoint_8_36, endpoint_8_37,
  endpoint_8_38, endpoint_8_39, endpoint_8_40, endpoint_8_41, endpoint_8_42, endpoint_8_43,
  endpoint_8_44, endpoint_8_45, endpoint_8_46, endpoint_8_47, endpoint_8_48, endpoint_8_49,
  endpoint_8_50, endpoint_8_51, endpoint_8_52, endpoint_8_53, endpoint_8_54, endpoint_8_55,
  endpoint_8_56, endpoint_8_57
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
