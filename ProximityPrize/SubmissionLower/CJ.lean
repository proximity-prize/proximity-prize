import ProximityPrize.SubmissionLower.CK
set_option Elab.async false
set_option autoImplicit true
section
namespace abF
open xE GI
open scoped BigOperators
structure af where
 first:ℕ
 count:ℕ
 packed :ℕ
 deriving Inhabited
private def unpack (packed :ℕ) :kJ :=
 ⟨packed % 512,packed/512 % 512,packed/262144 % 1024⟩
private def Xy (s :ℕ) :ℕ→ℕ→ℕ→ℕ
 | 0,_,_=>0
 | n+1,j,packed =>
     afm s j (unpack packed)+Xy s n (j+1) (packed/268435456)
private def aph (s :ℕ) (r :af) :ℕ :=
 if 2008≤ s∧s<3012∧322≤ r.first∧r.first+r.count≤1063 ∧
  3000≤ s+r.first∧s+r.first+r.count≤3420
 then Xy s r.count r.first r.packed else 0
def fD:ℕ→List af→ℕ
 | _,[]=>0
 | s,r :: rs=>aph s r+fD (s+1) rs
end abF
end
