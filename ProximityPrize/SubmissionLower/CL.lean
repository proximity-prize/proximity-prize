import ProximityPrize.SubmissionLower.CM
set_option Elab.async false
set_option autoImplicit true
section
namespace acY
open xE GI
open scoped BigOperators
private def decode (code :ℕ) :kJ :=
 ⟨code % 2048,code/2048 % 1024,code/2097152 % 1024⟩
private def E0 (code :ℕ) :ℕ:=code/2147483648+1
private def agf :List ℕ→ℕ
 | []=>0
 | code :: tail=>E0 code+agf tail
private def Eu (f :ℕ→ℕ) (j:ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>Eu f j n+f (j+n)
private def IK (s j code :ℕ) :ℕ :=
 if code % 2147483648=0 then 0
 else Eu (fun u=>Zr s u (decode code)) j (E0 code)
private def Sk (s j:ℕ) :List ℕ→ℕ
 | []=>0
 | code :: tail=>IK s j code+Sk s (j+E0 code) tail
private def rowStart (s :ℕ) :ℕ:=max 23 (3333 - s)
def value (s :ℕ) :List (List ℕ)→ℕ
 | []=>0
 | row :: tail=>Sk s (rowStart s) row+value (s+1) tail
def fits (s :ℕ) :List (List ℕ)→Bool
  | []=>true
  | row :: tail =>
    decide (rowStart s+agf row≤409∧s+rowStart s+agf row≤3797)
      && fits (s+1) tail
theorem a9s (s :ℕ) (a b:List (List ℕ)) :
   value s (a ++ b)=value s a+value (s+a.length) b:= by
 induction a generalizing s with
 | nil=>simp [value]
 | cons row tail ih =>
   simp only [List.cons_append,value,List.length_cons,ih,add_assoc,Nat.add_comm 1 tail.length]
theorem aUX (s :ℕ) (a b:List (List ℕ)) :
   fits s (a ++ b)=(fits s a && fits (s+a.length) b) := by
 induction a generalizing s with
 | nil=>simp [fits]
 | cons row tail ih =>
   simp only [List.cons_append,fits,List.length_cons,ih,Bool.and_assoc]
   rw [show s+1+tail.length=s+(tail.length+1) by omega]
end acY
end
