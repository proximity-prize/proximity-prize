/- Transitive axiom audit of the four editable seed certificates. -/
import ProximityPrize.SubmissionLower.Solution
import ProximityPrize.SubmissionUpper.Solution
import ProximityPrize.SubmissionBinaryLower.Solution
import ProximityPrize.SubmissionBinaryUpper.Solution

open Lean Lean.Meta

open Elab.Command in
run_cmd liftTermElabM do
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let seeds : List Name :=
    [``ProximityPrize.Benchmark.candidate,
     ``ProximityPrize.Benchmark.Upper.candidate,
     ``ProximityPrize.Benchmark.Binary.candidate,
     ``ProximityPrize.Benchmark.Binary.Upper.candidate]
  for seed in seeds do
    let axioms ← collectAxioms seed
    let unexpected := axioms.toList.filter (fun a => !whitelist.contains a)
    unless unexpected.isEmpty do
      throwError "seed {seed} depends on forbidden axioms: {unexpected}"
    IO.println s!"ok: {seed} uses only propext/Classical.choice/Quot.sound"
