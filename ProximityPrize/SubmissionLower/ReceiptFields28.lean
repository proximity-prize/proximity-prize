namespace ReceiptFields28

private def widen (a b c : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, data =>
    let grade := data % a
    let index := data / a % b
    let top := data / (a*b) % c
    let rest := data / (a*b*c)
    grade + (index <<< 9) + (top <<< 18) + (widen a b c n rest <<< 28)

/-- Expand columns in a receipt to their original 9-, 9-, and 10-bit fields. -/
def expand (count gradeWidth indexWidth topWidth data : Nat) : Nat :=
  widen (1 <<< gradeWidth) (1 <<< indexWidth) (1 <<< topWidth) count data

end ReceiptFields28
