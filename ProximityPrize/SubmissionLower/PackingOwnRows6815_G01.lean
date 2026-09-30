import ProximityPrize.SubmissionLower.PackingOwnRows6815_G00
import ProximityPrize.SubmissionLower.CompactAllN6815
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
