
namespace ProximityPrize.SubmissionLower.PackingDecode6815

def seriesWAux (m : Nat) (n : Nat) : Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih prev older code =>
      let z := Nat.mod code m
      let pred := Nat.sub (Nat.mul 2 prev) older
      let value := cond (Nat.beq (Nat.mod z 2) 0) (Nat.add pred (Nat.div z 2)) (Nat.sub pred (Nat.div z 2))
      value :: ih value prev (Nat.div code m)) n

def seriesW (n w code : Nat) : Array Nat := (seriesWAux (2^w) n 0 0 code).toArray

end ProximityPrize.SubmissionLower.PackingDecode6815
