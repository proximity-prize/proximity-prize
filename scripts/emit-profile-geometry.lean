/-
Emit the code geometry each Lean profile actually has, as JSON.

`scripts/check-profile-geometry.py` compares this against the numbers
`benchmark_profiles.py` publishes in every score artifact, so the released
metadata cannot describe a geometry the formalisation does not have.

Run with `lake env lean --run scripts/emit-profile-geometry.lean`.
-/
import ProximityPrize

open ProximityPrize.Benchmark

private def entry (selector field domainKind : String)
    (totalDimension interleaving baseDimension domainSize repetitions : Nat) :
    String :=
  "  \"" ++ selector ++ "\": {" ++
    "\"field\": \"" ++ field ++ "\", " ++
    "\"totalDimension\": " ++ toString totalDimension ++ ", " ++
    "\"interleaving\": " ++ toString interleaving ++ ", " ++
    "\"baseDimension\": " ++ toString baseDimension ++ ", " ++
    "\"domainSize\": " ++ toString domainSize ++ ", " ++
    "\"repetitions\": " ++ toString repetitions ++ ", " ++
    "\"domainKind\": \"" ++ domainKind ++ "\"}"

def main : IO Unit := do
  IO.println "{"
  IO.println <| entry "lower" "KoalaBear^6" "multiplicative-NTT"
    IRSProfile.totalDimension IRSProfile.interleaving IRSProfile.baseDimension
    IRSProfile.domainSize IRSProfile.repetitions ++ ","
  IO.println <| entry "binary-lower" "BF64.Ext3" "additive-polynomial-basis"
    BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving
    BinaryIRSProfile.baseDimension BinaryIRSProfile.domainSize
    BinaryIRSProfile.repetitions
  IO.println "}"
