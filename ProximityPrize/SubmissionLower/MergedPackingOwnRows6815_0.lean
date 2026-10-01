import ProximityPrize.SubmissionLower.MergedInfra6815_53
import ProximityPrize.SubmissionLower.MergedInfra6815_49
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok1 (v : ℕ) : Bool := if 181<v then true else rowCheck 1 v
private theorem g1_0 : SingletonCertificate6815.allN (fun j => ok1 (64*0+j)) 64=true := by decide +kernel
private theorem g1_1 : SingletonCertificate6815.allN (fun j => ok1 (64*1+j)) 64=true := by decide +kernel
private theorem g1_2 : SingletonCertificate6815.allN (fun j => ok1 (64*2+j)) 64=true := by decide +kernel
theorem checked1 (v : ℕ) (hv : v≤181) : rowCheck 1 v=true := by
  have h : ok1 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok1 64 0 g1_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok1 64 1 g1_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok1 64 2 g1_2 v (by omega) (by omega)
  simpa only [ok1,if_neg (show ¬181<v by omega)] using h
private def ok2 (v : ℕ) : Bool := if 180<v then true else rowCheck 2 v
private theorem g2_0 : SingletonCertificate6815.allN (fun j => ok2 (64*0+j)) 64=true := by decide +kernel
private theorem g2_1 : SingletonCertificate6815.allN (fun j => ok2 (64*1+j)) 64=true := by decide +kernel
private theorem g2_2 : SingletonCertificate6815.allN (fun j => ok2 (64*2+j)) 64=true := by decide +kernel
theorem checked2 (v : ℕ) (hv : v≤180) : rowCheck 2 v=true := by
  have h : ok2 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok2 64 0 g2_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok2 64 1 g2_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok2 64 2 g2_2 v (by omega) (by omega)
  simpa only [ok2,if_neg (show ¬180<v by omega)] using h
private def ok3 (v : ℕ) : Bool := if 179<v then true else rowCheck 3 v
private theorem g3_0 : SingletonCertificate6815.allN (fun j => ok3 (64*0+j)) 64=true := by decide +kernel
private theorem g3_1 : SingletonCertificate6815.allN (fun j => ok3 (64*1+j)) 64=true := by decide +kernel
private theorem g3_2 : SingletonCertificate6815.allN (fun j => ok3 (64*2+j)) 64=true := by decide +kernel
theorem checked3 (v : ℕ) (hv : v≤179) : rowCheck 3 v=true := by
  have h : ok3 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok3 64 0 g3_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok3 64 1 g3_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok3 64 2 g3_2 v (by omega) (by omega)
  simpa only [ok3,if_neg (show ¬179<v by omega)] using h
private def ok4 (v : ℕ) : Bool := if 178<v then true else rowCheck 4 v
private theorem g4_0 : SingletonCertificate6815.allN (fun j => ok4 (64*0+j)) 64=true := by decide +kernel
private theorem g4_1 : SingletonCertificate6815.allN (fun j => ok4 (64*1+j)) 64=true := by decide +kernel
private theorem g4_2 : SingletonCertificate6815.allN (fun j => ok4 (64*2+j)) 64=true := by decide +kernel
theorem checked4 (v : ℕ) (hv : v≤178) : rowCheck 4 v=true := by
  have h : ok4 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok4 64 0 g4_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok4 64 1 g4_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok4 64 2 g4_2 v (by omega) (by omega)
  simpa only [ok4,if_neg (show ¬178<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok5 (v : ℕ) : Bool := if 177<v then true else rowCheck 5 v
private theorem g5_0 : SingletonCertificate6815.allN (fun j => ok5 (64*0+j)) 64=true := by decide +kernel
private theorem g5_1 : SingletonCertificate6815.allN (fun j => ok5 (64*1+j)) 64=true := by decide +kernel
private theorem g5_2 : SingletonCertificate6815.allN (fun j => ok5 (64*2+j)) 64=true := by decide +kernel
theorem checked5 (v : ℕ) (hv : v≤177) : rowCheck 5 v=true := by
  have h : ok5 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok5 64 0 g5_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok5 64 1 g5_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok5 64 2 g5_2 v (by omega) (by omega)
  simpa only [ok5,if_neg (show ¬177<v by omega)] using h
private def ok6 (v : ℕ) : Bool := if 176<v then true else rowCheck 6 v
private theorem g6_0 : SingletonCertificate6815.allN (fun j => ok6 (64*0+j)) 64=true := by decide +kernel
private theorem g6_1 : SingletonCertificate6815.allN (fun j => ok6 (64*1+j)) 64=true := by decide +kernel
private theorem g6_2 : SingletonCertificate6815.allN (fun j => ok6 (64*2+j)) 64=true := by decide +kernel
theorem checked6 (v : ℕ) (hv : v≤176) : rowCheck 6 v=true := by
  have h : ok6 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok6 64 0 g6_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok6 64 1 g6_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok6 64 2 g6_2 v (by omega) (by omega)
  simpa only [ok6,if_neg (show ¬176<v by omega)] using h
private def ok7 (v : ℕ) : Bool := if 175<v then true else rowCheck 7 v
private theorem g7_0 : SingletonCertificate6815.allN (fun j => ok7 (64*0+j)) 64=true := by decide +kernel
private theorem g7_1 : SingletonCertificate6815.allN (fun j => ok7 (64*1+j)) 64=true := by decide +kernel
private theorem g7_2 : SingletonCertificate6815.allN (fun j => ok7 (64*2+j)) 64=true := by decide +kernel
theorem checked7 (v : ℕ) (hv : v≤175) : rowCheck 7 v=true := by
  have h : ok7 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok7 64 0 g7_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok7 64 1 g7_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok7 64 2 g7_2 v (by omega) (by omega)
  simpa only [ok7,if_neg (show ¬175<v by omega)] using h
private def ok8 (v : ℕ) : Bool := if 174<v then true else rowCheck 8 v
private theorem g8_0 : SingletonCertificate6815.allN (fun j => ok8 (64*0+j)) 64=true := by decide +kernel
private theorem g8_1 : SingletonCertificate6815.allN (fun j => ok8 (64*1+j)) 64=true := by decide +kernel
private theorem g8_2 : SingletonCertificate6815.allN (fun j => ok8 (64*2+j)) 64=true := by decide +kernel
theorem checked8 (v : ℕ) (hv : v≤174) : rowCheck 8 v=true := by
  have h : ok8 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok8 64 0 g8_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok8 64 1 g8_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok8 64 2 g8_2 v (by omega) (by omega)
  simpa only [ok8,if_neg (show ¬174<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok9 (v : ℕ) : Bool := if 173<v then true else rowCheck 9 v
private theorem g9_0 : SingletonCertificate6815.allN (fun j => ok9 (64*0+j)) 64=true := by decide +kernel
private theorem g9_1 : SingletonCertificate6815.allN (fun j => ok9 (64*1+j)) 64=true := by decide +kernel
private theorem g9_2 : SingletonCertificate6815.allN (fun j => ok9 (64*2+j)) 64=true := by decide +kernel
theorem checked9 (v : ℕ) (hv : v≤173) : rowCheck 9 v=true := by
  have h : ok9 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok9 64 0 g9_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok9 64 1 g9_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok9 64 2 g9_2 v (by omega) (by omega)
  simpa only [ok9,if_neg (show ¬173<v by omega)] using h
private def ok10 (v : ℕ) : Bool := if 172<v then true else rowCheck 10 v
private theorem g10_0 : SingletonCertificate6815.allN (fun j => ok10 (64*0+j)) 64=true := by decide +kernel
private theorem g10_1 : SingletonCertificate6815.allN (fun j => ok10 (64*1+j)) 64=true := by decide +kernel
private theorem g10_2 : SingletonCertificate6815.allN (fun j => ok10 (64*2+j)) 64=true := by decide +kernel
theorem checked10 (v : ℕ) (hv : v≤172) : rowCheck 10 v=true := by
  have h : ok10 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok10 64 0 g10_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok10 64 1 g10_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok10 64 2 g10_2 v (by omega) (by omega)
  simpa only [ok10,if_neg (show ¬172<v by omega)] using h
private def ok11 (v : ℕ) : Bool := if 171<v then true else rowCheck 11 v
private theorem g11_0 : SingletonCertificate6815.allN (fun j => ok11 (64*0+j)) 64=true := by decide +kernel
private theorem g11_1 : SingletonCertificate6815.allN (fun j => ok11 (64*1+j)) 64=true := by decide +kernel
private theorem g11_2 : SingletonCertificate6815.allN (fun j => ok11 (64*2+j)) 64=true := by decide +kernel
theorem checked11 (v : ℕ) (hv : v≤171) : rowCheck 11 v=true := by
  have h : ok11 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok11 64 0 g11_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok11 64 1 g11_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok11 64 2 g11_2 v (by omega) (by omega)
  simpa only [ok11,if_neg (show ¬171<v by omega)] using h
private def ok12 (v : ℕ) : Bool := if 170<v then true else rowCheck 12 v
private theorem g12_0 : SingletonCertificate6815.allN (fun j => ok12 (64*0+j)) 64=true := by decide +kernel
private theorem g12_1 : SingletonCertificate6815.allN (fun j => ok12 (64*1+j)) 64=true := by decide +kernel
private theorem g12_2 : SingletonCertificate6815.allN (fun j => ok12 (64*2+j)) 64=true := by decide +kernel
theorem checked12 (v : ℕ) (hv : v≤170) : rowCheck 12 v=true := by
  have h : ok12 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok12 64 0 g12_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok12 64 1 g12_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok12 64 2 g12_2 v (by omega) (by omega)
  simpa only [ok12,if_neg (show ¬170<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok13 (v : ℕ) : Bool := if 169<v then true else rowCheck 13 v
private theorem g13_0 : SingletonCertificate6815.allN (fun j => ok13 (64*0+j)) 64=true := by decide +kernel
private theorem g13_1 : SingletonCertificate6815.allN (fun j => ok13 (64*1+j)) 64=true := by decide +kernel
private theorem g13_2 : SingletonCertificate6815.allN (fun j => ok13 (64*2+j)) 64=true := by decide +kernel
theorem checked13 (v : ℕ) (hv : v≤169) : rowCheck 13 v=true := by
  have h : ok13 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok13 64 0 g13_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok13 64 1 g13_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok13 64 2 g13_2 v (by omega) (by omega)
  simpa only [ok13,if_neg (show ¬169<v by omega)] using h
private def ok14 (v : ℕ) : Bool := if 168<v then true else rowCheck 14 v
private theorem g14_0 : SingletonCertificate6815.allN (fun j => ok14 (64*0+j)) 64=true := by decide +kernel
private theorem g14_1 : SingletonCertificate6815.allN (fun j => ok14 (64*1+j)) 64=true := by decide +kernel
private theorem g14_2 : SingletonCertificate6815.allN (fun j => ok14 (64*2+j)) 64=true := by decide +kernel
theorem checked14 (v : ℕ) (hv : v≤168) : rowCheck 14 v=true := by
  have h : ok14 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok14 64 0 g14_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok14 64 1 g14_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok14 64 2 g14_2 v (by omega) (by omega)
  simpa only [ok14,if_neg (show ¬168<v by omega)] using h
private def ok15 (v : ℕ) : Bool := if 167<v then true else rowCheck 15 v
private theorem g15_0 : SingletonCertificate6815.allN (fun j => ok15 (64*0+j)) 64=true := by decide +kernel
private theorem g15_1 : SingletonCertificate6815.allN (fun j => ok15 (64*1+j)) 64=true := by decide +kernel
private theorem g15_2 : SingletonCertificate6815.allN (fun j => ok15 (64*2+j)) 64=true := by decide +kernel
theorem checked15 (v : ℕ) (hv : v≤167) : rowCheck 15 v=true := by
  have h : ok15 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok15 64 0 g15_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok15 64 1 g15_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok15 64 2 g15_2 v (by omega) (by omega)
  simpa only [ok15,if_neg (show ¬167<v by omega)] using h
private def ok16 (v : ℕ) : Bool := if 166<v then true else rowCheck 16 v
private theorem g16_0 : SingletonCertificate6815.allN (fun j => ok16 (64*0+j)) 64=true := by decide +kernel
private theorem g16_1 : SingletonCertificate6815.allN (fun j => ok16 (64*1+j)) 64=true := by decide +kernel
private theorem g16_2 : SingletonCertificate6815.allN (fun j => ok16 (64*2+j)) 64=true := by decide +kernel
theorem checked16 (v : ℕ) (hv : v≤166) : rowCheck 16 v=true := by
  have h : ok16 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok16 64 0 g16_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok16 64 1 g16_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok16 64 2 g16_2 v (by omega) (by omega)
  simpa only [ok16,if_neg (show ¬166<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok17 (v : ℕ) : Bool := if 165<v then true else rowCheck 17 v
private theorem g17_0 : SingletonCertificate6815.allN (fun j => ok17 (64*0+j)) 64=true := by decide +kernel
private theorem g17_1 : SingletonCertificate6815.allN (fun j => ok17 (64*1+j)) 64=true := by decide +kernel
private theorem g17_2 : SingletonCertificate6815.allN (fun j => ok17 (64*2+j)) 64=true := by decide +kernel
theorem checked17 (v : ℕ) (hv : v≤165) : rowCheck 17 v=true := by
  have h : ok17 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok17 64 0 g17_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok17 64 1 g17_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok17 64 2 g17_2 v (by omega) (by omega)
  simpa only [ok17,if_neg (show ¬165<v by omega)] using h
private def ok18 (v : ℕ) : Bool := if 164<v then true else rowCheck 18 v
private theorem g18_0 : SingletonCertificate6815.allN (fun j => ok18 (64*0+j)) 64=true := by decide +kernel
private theorem g18_1 : SingletonCertificate6815.allN (fun j => ok18 (64*1+j)) 64=true := by decide +kernel
private theorem g18_2 : SingletonCertificate6815.allN (fun j => ok18 (64*2+j)) 64=true := by decide +kernel
theorem checked18 (v : ℕ) (hv : v≤164) : rowCheck 18 v=true := by
  have h : ok18 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok18 64 0 g18_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok18 64 1 g18_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok18 64 2 g18_2 v (by omega) (by omega)
  simpa only [ok18,if_neg (show ¬164<v by omega)] using h
private def ok19 (v : ℕ) : Bool := if 163<v then true else rowCheck 19 v
private theorem g19_0 : SingletonCertificate6815.allN (fun j => ok19 (64*0+j)) 64=true := by decide +kernel
private theorem g19_1 : SingletonCertificate6815.allN (fun j => ok19 (64*1+j)) 64=true := by decide +kernel
private theorem g19_2 : SingletonCertificate6815.allN (fun j => ok19 (64*2+j)) 64=true := by decide +kernel
theorem checked19 (v : ℕ) (hv : v≤163) : rowCheck 19 v=true := by
  have h : ok19 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok19 64 0 g19_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok19 64 1 g19_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok19 64 2 g19_2 v (by omega) (by omega)
  simpa only [ok19,if_neg (show ¬163<v by omega)] using h
private def ok20 (v : ℕ) : Bool := if 162<v then true else rowCheck 20 v
private theorem g20_0 : SingletonCertificate6815.allN (fun j => ok20 (64*0+j)) 64=true := by decide +kernel
private theorem g20_1 : SingletonCertificate6815.allN (fun j => ok20 (64*1+j)) 64=true := by decide +kernel
private theorem g20_2 : SingletonCertificate6815.allN (fun j => ok20 (64*2+j)) 64=true := by decide +kernel
theorem checked20 (v : ℕ) (hv : v≤162) : rowCheck 20 v=true := by
  have h : ok20 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok20 64 0 g20_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok20 64 1 g20_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok20 64 2 g20_2 v (by omega) (by omega)
  simpa only [ok20,if_neg (show ¬162<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
end MergedPart4
