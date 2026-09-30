import ProximityPrize.SubmissionLower.PackingOwnRows6815_G06
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok29 (v : ℕ) : Bool := if 153<v then true else rowCheck 29 v
private theorem g29_0 : SingletonCertificate6815.allN (fun j => ok29 (64*0+j)) 64=true := by decide +kernel
private theorem g29_1 : SingletonCertificate6815.allN (fun j => ok29 (64*1+j)) 64=true := by decide +kernel
private theorem g29_2 : SingletonCertificate6815.allN (fun j => ok29 (64*2+j)) 64=true := by decide +kernel
theorem checked29 (v : ℕ) (hv : v≤153) : rowCheck 29 v=true := by
  have h : ok29 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok29 64 0 g29_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok29 64 1 g29_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok29 64 2 g29_2 v (by omega) (by omega)
  simpa only [ok29,if_neg (show ¬153<v by omega)] using h
private def ok30 (v : ℕ) : Bool := if 152<v then true else rowCheck 30 v
private theorem g30_0 : SingletonCertificate6815.allN (fun j => ok30 (64*0+j)) 64=true := by decide +kernel
private theorem g30_1 : SingletonCertificate6815.allN (fun j => ok30 (64*1+j)) 64=true := by decide +kernel
private theorem g30_2 : SingletonCertificate6815.allN (fun j => ok30 (64*2+j)) 64=true := by decide +kernel
theorem checked30 (v : ℕ) (hv : v≤152) : rowCheck 30 v=true := by
  have h : ok30 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok30 64 0 g30_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok30 64 1 g30_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok30 64 2 g30_2 v (by omega) (by omega)
  simpa only [ok30,if_neg (show ¬152<v by omega)] using h
private def ok31 (v : ℕ) : Bool := if 151<v then true else rowCheck 31 v
private theorem g31_0 : SingletonCertificate6815.allN (fun j => ok31 (64*0+j)) 64=true := by decide +kernel
private theorem g31_1 : SingletonCertificate6815.allN (fun j => ok31 (64*1+j)) 64=true := by decide +kernel
private theorem g31_2 : SingletonCertificate6815.allN (fun j => ok31 (64*2+j)) 64=true := by decide +kernel
theorem checked31 (v : ℕ) (hv : v≤151) : rowCheck 31 v=true := by
  have h : ok31 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok31 64 0 g31_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok31 64 1 g31_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok31 64 2 g31_2 v (by omega) (by omega)
  simpa only [ok31,if_neg (show ¬151<v by omega)] using h
private def ok32 (v : ℕ) : Bool := if 150<v then true else rowCheck 32 v
private theorem g32_0 : SingletonCertificate6815.allN (fun j => ok32 (64*0+j)) 64=true := by decide +kernel
private theorem g32_1 : SingletonCertificate6815.allN (fun j => ok32 (64*1+j)) 64=true := by decide +kernel
private theorem g32_2 : SingletonCertificate6815.allN (fun j => ok32 (64*2+j)) 64=true := by decide +kernel
theorem checked32 (v : ℕ) (hv : v≤150) : rowCheck 32 v=true := by
  have h : ok32 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok32 64 0 g32_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok32 64 1 g32_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok32 64 2 g32_2 v (by omega) (by omega)
  simpa only [ok32,if_neg (show ¬150<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
