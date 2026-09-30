import ProximityPrize.SubmissionLower.PackingOwnCheck6815
import ProximityPrize.SubmissionLower.CompactAllN6815
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
