import ProximityPrize.SubmissionLower.PackingOwnRows6815_G05
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok25 (v : ℕ) : Bool := if 157<v then true else rowCheck 25 v
private theorem g25_0 : SingletonCertificate6815.allN (fun j => ok25 (64*0+j)) 64=true := by decide +kernel
private theorem g25_1 : SingletonCertificate6815.allN (fun j => ok25 (64*1+j)) 64=true := by decide +kernel
private theorem g25_2 : SingletonCertificate6815.allN (fun j => ok25 (64*2+j)) 64=true := by decide +kernel
theorem checked25 (v : ℕ) (hv : v≤157) : rowCheck 25 v=true := by
  have h : ok25 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok25 64 0 g25_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok25 64 1 g25_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok25 64 2 g25_2 v (by omega) (by omega)
  simpa only [ok25,if_neg (show ¬157<v by omega)] using h
private def ok26 (v : ℕ) : Bool := if 156<v then true else rowCheck 26 v
private theorem g26_0 : SingletonCertificate6815.allN (fun j => ok26 (64*0+j)) 64=true := by decide +kernel
private theorem g26_1 : SingletonCertificate6815.allN (fun j => ok26 (64*1+j)) 64=true := by decide +kernel
private theorem g26_2 : SingletonCertificate6815.allN (fun j => ok26 (64*2+j)) 64=true := by decide +kernel
theorem checked26 (v : ℕ) (hv : v≤156) : rowCheck 26 v=true := by
  have h : ok26 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok26 64 0 g26_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok26 64 1 g26_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok26 64 2 g26_2 v (by omega) (by omega)
  simpa only [ok26,if_neg (show ¬156<v by omega)] using h
private def ok27 (v : ℕ) : Bool := if 155<v then true else rowCheck 27 v
private theorem g27_0 : SingletonCertificate6815.allN (fun j => ok27 (64*0+j)) 64=true := by decide +kernel
private theorem g27_1 : SingletonCertificate6815.allN (fun j => ok27 (64*1+j)) 64=true := by decide +kernel
private theorem g27_2 : SingletonCertificate6815.allN (fun j => ok27 (64*2+j)) 64=true := by decide +kernel
theorem checked27 (v : ℕ) (hv : v≤155) : rowCheck 27 v=true := by
  have h : ok27 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok27 64 0 g27_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok27 64 1 g27_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok27 64 2 g27_2 v (by omega) (by omega)
  simpa only [ok27,if_neg (show ¬155<v by omega)] using h
private def ok28 (v : ℕ) : Bool := if 154<v then true else rowCheck 28 v
private theorem g28_0 : SingletonCertificate6815.allN (fun j => ok28 (64*0+j)) 64=true := by decide +kernel
private theorem g28_1 : SingletonCertificate6815.allN (fun j => ok28 (64*1+j)) 64=true := by decide +kernel
private theorem g28_2 : SingletonCertificate6815.allN (fun j => ok28 (64*2+j)) 64=true := by decide +kernel
theorem checked28 (v : ℕ) (hv : v≤154) : rowCheck 28 v=true := by
  have h : ok28 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok28 64 0 g28_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok28 64 1 g28_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok28 64 2 g28_2 v (by omega) (by omega)
  simpa only [ok28,if_neg (show ¬154<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
