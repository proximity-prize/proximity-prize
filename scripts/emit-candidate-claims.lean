/-
Emit the numerals each track's `candidate` actually proves.

`scripts/check-candidate-claims.py` compares these against the committed
`score.txt` and radius/unsafe-index files, so a mismatch is caught locally
rather than at the next benchmark run. The benchmark path binds them already:
the trusted statement Comparator checks is rendered from those same files.

Run with `lake env lean scripts/emit-candidate-claims.lean`.
-/
import ProximityPrize.SubmissionLower.Solution
import ProximityPrize.SubmissionUpper.Solution
import ProximityPrize.SubmissionBinaryLower.Solution
import ProximityPrize.SubmissionBinaryUpper.Solution

open Lean Elab Command Meta

/-- The Nat arguments of `candidate`'s declared type, in order. For the lower
tracks that is `centiBits`, `radiusNumerator`, `radiusDenominator`; for the
upper tracks `centiBits`, `unsafeIndex`. -/
private def claimNumerals (n : Name) : TermElabM (Array String) := do
  let info ← getConstInfo n
  let args := (← instantiateMVars info.type).getAppArgs
  let mut nums : Array String := #[]
  for a in args do
    match ← (Meta.evalNat a).run with
    | some v => nums := nums.push (toString v)
    | none => pure ()
  return nums

run_cmd liftTermElabM do
  let targets : List (String × Name) :=
    [("lower", ``ProximityPrize.Benchmark.candidate),
     ("upper", ``ProximityPrize.Benchmark.Upper.candidate),
     ("binary-lower", ``ProximityPrize.Benchmark.Binary.candidate),
     ("binary-upper", ``ProximityPrize.Benchmark.Binary.Upper.candidate)]
  for (label, n) in targets do
    let nums ← claimNumerals n
    IO.println s!"{label} {String.intercalate " " nums.toList}"
