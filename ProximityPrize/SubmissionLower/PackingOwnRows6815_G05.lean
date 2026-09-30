import ProximityPrize.SubmissionLower.PackingOwnRows6815_G04
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok21 (v : ℕ) : Bool := if 161<v then true else rowCheck 21 v
private theorem g21_0 : SingletonCertificate6815.allN (fun j => ok21 (64*0+j)) 64=true := by decide +kernel
private theorem g21_1 : SingletonCertificate6815.allN (fun j => ok21 (64*1+j)) 64=true := by decide +kernel
private theorem g21_2 : SingletonCertificate6815.allN (fun j => ok21 (64*2+j)) 64=true := by decide +kernel
theorem checked21 (v : ℕ) (hv : v≤161) : rowCheck 21 v=true := by
  have h : ok21 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok21 64 0 g21_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok21 64 1 g21_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok21 64 2 g21_2 v (by omega) (by omega)
  simpa only [ok21,if_neg (show ¬161<v by omega)] using h
private def ok22 (v : ℕ) : Bool := if 160<v then true else rowCheck 22 v
private theorem g22_0 : SingletonCertificate6815.allN (fun j => ok22 (64*0+j)) 64=true := by decide +kernel
private theorem g22_1 : SingletonCertificate6815.allN (fun j => ok22 (64*1+j)) 64=true := by decide +kernel
private theorem g22_2 : SingletonCertificate6815.allN (fun j => ok22 (64*2+j)) 64=true := by decide +kernel
theorem checked22 (v : ℕ) (hv : v≤160) : rowCheck 22 v=true := by
  have h : ok22 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok22 64 0 g22_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok22 64 1 g22_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok22 64 2 g22_2 v (by omega) (by omega)
  simpa only [ok22,if_neg (show ¬160<v by omega)] using h
private def ok23 (v : ℕ) : Bool := if 159<v then true else rowCheck 23 v
private theorem g23_0 : SingletonCertificate6815.allN (fun j => ok23 (64*0+j)) 64=true := by decide +kernel
private theorem g23_1 : SingletonCertificate6815.allN (fun j => ok23 (64*1+j)) 64=true := by decide +kernel
private theorem g23_2 : SingletonCertificate6815.allN (fun j => ok23 (64*2+j)) 64=true := by decide +kernel
theorem checked23 (v : ℕ) (hv : v≤159) : rowCheck 23 v=true := by
  have h : ok23 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok23 64 0 g23_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok23 64 1 g23_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok23 64 2 g23_2 v (by omega) (by omega)
  simpa only [ok23,if_neg (show ¬159<v by omega)] using h
private def ok24 (v : ℕ) : Bool := if 158<v then true else rowCheck 24 v
private theorem g24_0 : SingletonCertificate6815.allN (fun j => ok24 (64*0+j)) 64=true := by decide +kernel
private theorem g24_1 : SingletonCertificate6815.allN (fun j => ok24 (64*1+j)) 64=true := by decide +kernel
private theorem g24_2 : SingletonCertificate6815.allN (fun j => ok24 (64*2+j)) 64=true := by decide +kernel
theorem checked24 (v : ℕ) (hv : v≤158) : rowCheck 24 v=true := by
  have h : ok24 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok24 64 0 g24_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok24 64 1 g24_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok24 64 2 g24_2 v (by omega) (by omega)
  simpa only [ok24,if_neg (show ¬158<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
