import ProximityPrize.SubmissionLower.MergedPackingOwnRows6815_0
import ProximityPrize.SubmissionLower.MergedInfra6815_49
set_option Elab.async false
section MergedPart0
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
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
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
end MergedPart3
section MergedPart4
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
end MergedPart4
