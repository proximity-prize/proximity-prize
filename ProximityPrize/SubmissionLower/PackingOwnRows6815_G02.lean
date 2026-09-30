import ProximityPrize.SubmissionLower.PackingOwnRows6815_G01
import ProximityPrize.SubmissionLower.CompactAllN6815
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
