import ProximityPrize.SubmissionBinaryLower.B6401IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part0
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part2
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part3
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part4
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part5
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part6
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part7
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part8
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3Part9

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401CertsT3

open B6401IntFarkas B6401IntSmallCerts

def T3_CAP_BOUND : Nat := 10000000000000000000

def checkT3Entry (c : T3Cert) : Bool :=
  checkT3Cert c && (c.m == 0 || c.cap.c1Bkt * 3850 + c.cap.c0Bkt ≤ T3_CAP_BOUND)

def checkT3_2BEntry (c : T3_2BCert) : Bool :=
  checkT3_2BCert c && (c.m == 0 || c.cap.c1Bkt * 3850 + c.cap.c0Bkt ≤ T3_CAP_BOUND)

def certsT3_2B : List T3_2BCert := [
  ⟨11534323,1048575,502267341,44739200,14,2,0,0,0,0,122,0,0,38,66,10000,8,17,4148332,489217,1000000000,⟨false,0,0,0,0,0,0,0,2142393714491,342825972934605⟩⟩,
  ⟨502267341,44739200,24793721,2164800,14,2,0,0,0,0,122,26,66,0,66,10000,8,17,4148292,183609,200000000,⟨false,0,0,0,0,0,0,0,1154413364577,184946322686048⟩⟩,
]

theorem certsT3_2B_ok : certsT3_2B.all checkT3_2BEntry = true := by decide

def certsT3All : List T3Cert :=
  B6401CertsT3Part0.certsT3_0 ++ B6401CertsT3Part1.certsT3_1 ++ B6401CertsT3Part2.certsT3_2 ++ B6401CertsT3Part3.certsT3_3 ++ B6401CertsT3Part4.certsT3_4 ++ B6401CertsT3Part5.certsT3_5 ++ B6401CertsT3Part6.certsT3_6 ++ B6401CertsT3Part7.certsT3_7 ++ B6401CertsT3Part8.certsT3_8 ++ B6401CertsT3Part9.certsT3_9

theorem certsT3All_ok : ∀ c ∈ certsT3All, checkT3Entry c = true := by
  intro c hc
  simp only [certsT3All, List.mem_append] at hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  rcases hc with hc | hc
  · exact List.all_eq_true.mp B6401CertsT3Part0.certsT3_0_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part1.certsT3_1_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part2.certsT3_2_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part3.certsT3_3_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part4.certsT3_4_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part5.certsT3_5_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part6.certsT3_6_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part7.certsT3_7_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part8.certsT3_8_ok c hc
  · exact List.all_eq_true.mp B6401CertsT3Part9.certsT3_9_ok c hc

end B6401CertsT3
end ProximityPrize.SubmissionBinaryLower
