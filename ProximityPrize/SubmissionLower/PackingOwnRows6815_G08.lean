import ProximityPrize.SubmissionLower.PackingOwnRows6815_G07
import ProximityPrize.SubmissionLower.CompactAllN6815
namespace ProximityPrize.SubmissionLower.PackingOwnRows6815
open PackingOwnCheck6815
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
private def ok33 (v : ℕ) : Bool := if 149<v then true else rowCheck 33 v
private theorem g33_0 : SingletonCertificate6815.allN (fun j => ok33 (64*0+j)) 64=true := by decide +kernel
private theorem g33_1 : SingletonCertificate6815.allN (fun j => ok33 (64*1+j)) 64=true := by decide +kernel
private theorem g33_2 : SingletonCertificate6815.allN (fun j => ok33 (64*2+j)) 64=true := by decide +kernel
theorem checked33 (v : ℕ) (hv : v≤149) : rowCheck 33 v=true := by
  have h : ok33 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok33 64 0 g33_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok33 64 1 g33_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok33 64 2 g33_2 v (by omega) (by omega)
  simpa only [ok33,if_neg (show ¬149<v by omega)] using h
private def ok34 (v : ℕ) : Bool := if 148<v then true else rowCheck 34 v
private theorem g34_0 : SingletonCertificate6815.allN (fun j => ok34 (64*0+j)) 64=true := by decide +kernel
private theorem g34_1 : SingletonCertificate6815.allN (fun j => ok34 (64*1+j)) 64=true := by decide +kernel
private theorem g34_2 : SingletonCertificate6815.allN (fun j => ok34 (64*2+j)) 64=true := by decide +kernel
theorem checked34 (v : ℕ) (hv : v≤148) : rowCheck 34 v=true := by
  have h : ok34 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok34 64 0 g34_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok34 64 1 g34_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok34 64 2 g34_2 v (by omega) (by omega)
  simpa only [ok34,if_neg (show ¬148<v by omega)] using h
private def ok35 (v : ℕ) : Bool := if 147<v then true else rowCheck 35 v
private theorem g35_0 : SingletonCertificate6815.allN (fun j => ok35 (64*0+j)) 64=true := by decide +kernel
private theorem g35_1 : SingletonCertificate6815.allN (fun j => ok35 (64*1+j)) 64=true := by decide +kernel
private theorem g35_2 : SingletonCertificate6815.allN (fun j => ok35 (64*2+j)) 64=true := by decide +kernel
theorem checked35 (v : ℕ) (hv : v≤147) : rowCheck 35 v=true := by
  have h : ok35 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok35 64 0 g35_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok35 64 1 g35_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok35 64 2 g35_2 v (by omega) (by omega)
  simpa only [ok35,if_neg (show ¬147<v by omega)] using h
private def ok36 (v : ℕ) : Bool := if 146<v then true else rowCheck 36 v
private theorem g36_0 : SingletonCertificate6815.allN (fun j => ok36 (64*0+j)) 64=true := by decide +kernel
private theorem g36_1 : SingletonCertificate6815.allN (fun j => ok36 (64*1+j)) 64=true := by decide +kernel
private theorem g36_2 : SingletonCertificate6815.allN (fun j => ok36 (64*2+j)) 64=true := by decide +kernel
theorem checked36 (v : ℕ) (hv : v≤146) : rowCheck 36 v=true := by
  have h : ok36 v=true := by
    rcases (show (0≤v ∧ v<64) ∨ (64≤v ∧ v<128) ∨ (128≤v ∧ v<192) by omega) with h0 | h1 | h2
    · exact CompactAllN6815.allN_blockN ok36 64 0 g36_0 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok36 64 1 g36_1 v (by omega) (by omega)
    · exact CompactAllN6815.allN_blockN ok36 64 2 g36_2 v (by omega) (by omega)
  simpa only [ok36,if_neg (show ¬146<v by omega)] using h
end ProximityPrize.SubmissionLower.PackingOwnRows6815
