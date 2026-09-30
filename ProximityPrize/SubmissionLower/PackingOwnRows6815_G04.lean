import ProximityPrize.SubmissionLower.PackingOwnRows6815_G03
import ProximityPrize.SubmissionLower.CompactAllN6815
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
