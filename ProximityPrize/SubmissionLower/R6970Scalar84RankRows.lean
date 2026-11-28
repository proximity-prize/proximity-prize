import ProximityPrize.SubmissionLower.R6970Scalar84RankDefs

namespace R6970Scalar84Rank.CompactRows

def z (n : Nat) : List Nat := List.replicate n 0

def u (before after : Nat) : List Nat :=
  List.replicate before 0 ++ (1 :: List.replicate after 0)

def r (n : Nat) (row : List Nat) : List (List Nat) := List.replicate n row

private def digit (c : UInt8) : Nat :=
  let v := c.toNat
  if v = 99 then 57 else v - 35

private def words : List UInt8 → Nat → Nat → List Nat
  | [], _, _ => []
  | c :: cs, w, scale =>
    let w' := w + digit c * scale
    let next := 64 * scale
    if next < 2147483648 then
      words cs w' next
    else
      (w' % 2147483648) :: words cs (w' / 2147483648) (next / 2147483648)

def a (text : String) : List Nat := words text.toByteArray.data.toList 0 1

end R6970Scalar84Rank.CompactRows
