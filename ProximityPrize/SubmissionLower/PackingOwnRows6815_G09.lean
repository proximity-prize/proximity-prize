import ProximityPrize.SubmissionLower.PackingOwnRows6815_G08
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok37 (v : ℕ) : Bool := if 145<v then true else rowCheck 37 v
private theorem g37_0 : SingletonCertificate6815.allN (fun j => ok37 (64*0+j)) 64=true := by decide +kernel
private theorem g37_1 : SingletonCertificate6815.allN (fun j => ok37 (64*1+j)) 64=true := by decide +kernel
private theorem g37_2 : SingletonCertificate6815.allN (fun j => ok37 (64*2+j)) 64=true := by decide +kernel
theorem checked37 (v : ℕ) (hv : v≤145) : rowCheck 37 v=true := by
  have h : ok37 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok37 64 0 g37_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok37 64 1 g37_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok37 64 2 g37_2 v (by omega) (by omega)
  simpa only [ok37,if_neg (show ¬145<v by omega)] using h
private def ok38 (v : ℕ) : Bool := if 144<v then true else rowCheck 38 v
private theorem g38_0 : SingletonCertificate6815.allN (fun j => ok38 (64*0+j)) 64=true := by decide +kernel
private theorem g38_1 : SingletonCertificate6815.allN (fun j => ok38 (64*1+j)) 64=true := by decide +kernel
private theorem g38_2 : SingletonCertificate6815.allN (fun j => ok38 (64*2+j)) 64=true := by decide +kernel
theorem checked38 (v : ℕ) (hv : v≤144) : rowCheck 38 v=true := by
  have h : ok38 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok38 64 0 g38_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok38 64 1 g38_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok38 64 2 g38_2 v (by omega) (by omega)
  simpa only [ok38,if_neg (show ¬144<v by omega)] using h
private def ok39 (v : ℕ) : Bool := if 143<v then true else rowCheck 39 v
private theorem g39_0 : SingletonCertificate6815.allN (fun j => ok39 (64*0+j)) 64=true := by decide +kernel
private theorem g39_1 : SingletonCertificate6815.allN (fun j => ok39 (64*1+j)) 64=true := by decide +kernel
private theorem g39_2 : SingletonCertificate6815.allN (fun j => ok39 (64*2+j)) 64=true := by decide +kernel
theorem checked39 (v : ℕ) (hv : v≤143) : rowCheck 39 v=true := by
  have h : ok39 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok39 64 0 g39_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok39 64 1 g39_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok39 64 2 g39_2 v (by omega) (by omega)
  simpa only [ok39,if_neg (show ¬143<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
