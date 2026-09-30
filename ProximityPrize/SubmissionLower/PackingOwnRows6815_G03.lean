import ProximityPrize.SubmissionLower.PackingOwnRows6815_G02
import ProximityPrize.SubmissionLower.CompactAllN6815
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
