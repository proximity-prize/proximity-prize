/-
Environment and axiom audit for the protected IRS benchmark contract.

Run after building all four protected benchmark targets:
`lake env lean scripts/check-axioms.lean`.
-/
import ProximityPrize

open Lean Lean.Meta

-- Every top-level module prefix admitted into the environment. Two are easy to
-- mistake for dead entries, so record where they come from: `ToMathlib` is
-- VCVio's staging library for declarations bound for Mathlib, and `ToCslib` is
-- PolyFun's equivalent for declarations bound for Cslib -- it ships in
-- `PolyFun/ToCslib/`, not in a package of its own.
def trustedModulePrefixes : List String :=
  ["Init", "Lean", "Lake", "Std", "Batteries", "Aesop", "Qq", "Plausible", "Cslib",
   "ProofWidgets", "ImportGraph", "LeanSearchClient", "Mathlib", "ArkLib",
   "VCVio", "CompPoly", "PolyFun", "Loom", "ToMathlib", "ToCslib", "ProximityPrize"]

open Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut badMods : Array Name := #[]
  for m in mods do
    let top := (m.components.head?.getD m).toString
    unless trustedModulePrefixes.contains top do
      badMods := badMods.push m
  unless badMods.isEmpty do
    for m in badMods do
      IO.eprintln s!"::error::module `{m}` has an unreviewed top-level prefix"
    throwError "unreviewed modules in environment ({badMods.size})"

  let mut bad : Array (Name × Name) := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := mods[idx.toNat]!
      if (`ProximityPrize).isPrefixOf modName && ci.isAxiom then
        bad := bad.push (name, modName)
  unless bad.isEmpty do
    for (n, m) in bad do
      IO.eprintln s!"::error::axiom declaration `{n}` in module `{m}`"
    throwError "axiom declarations found in ProximityPrize modules ({bad.size})"
  IO.println "ok — reviewed module prefixes; no local axiom declarations"

open Elab.Command in
run_cmd liftTermElabM do
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let trustedDecls : List Name :=
    [``ProximityPrize.Benchmark.IRSProfile.encoder_injective,
     ``ProximityPrize.Benchmark.IRSProfile.encoder_range,
     ``ProximityPrize.Benchmark.IRSProfile.dimension,
     ``ProximityPrize.Benchmark.IRSProfile.alphabetRate,
     ``ProximityPrize.Benchmark.IRSProfile.minDistance,
     ``ProximityPrize.Benchmark.IRSProfile.base_minRelativeDistance,
     ``ProximityPrize.Benchmark.claimedRadius,
     ``ProximityPrize.Benchmark.claimedError,
     ``ProximityPrize.Benchmark.reductionTarget,
     ``ProximityPrize.Benchmark.ProtocolClaim,
     ``ProximityPrize.Benchmark.Upper.epsilonStar,
     ``ProximityPrize.Benchmark.Upper.claimedUnsafeRadius,
     ``ProximityPrize.Benchmark.Upper.ProtocolClaimUpper]
  let trustedDecls := trustedDecls ++
    [``ProximityPrize.Benchmark.BinarySampling.baseSampleableType,
     ``ProximityPrize.Benchmark.BinarySampling.sampleableType,
     ``ProximityPrize.Benchmark.BinarySampling.evalDist_sample,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.domain,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.encoder_injective,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.encoder_range,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.dimension,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.alphabetRate,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.minDistance,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.base_minRelativeDistance,
     ``ProximityPrize.Benchmark.BinaryIRSProfile.minRelativeDistance_eq,
     ``ProximityPrize.Benchmark.Binary.claimedRadius,
     ``ProximityPrize.Benchmark.Binary.claimedError,
     ``ProximityPrize.Benchmark.Binary.reductionTarget,
     ``ProximityPrize.Benchmark.Binary.ProtocolClaim,
     ``ProximityPrize.Benchmark.Binary.Upper.epsilonStar,
     ``ProximityPrize.Benchmark.Binary.Upper.claimedUnsafeRadius,
     ``ProximityPrize.Benchmark.Binary.Upper.ProtocolClaimUpper]
  for decl in trustedDecls do
    let axioms ← collectAxioms decl
    let offending := axioms.toList.filter (fun a => !whitelist.contains a)
    unless offending.isEmpty do
      for ax in offending do
        IO.eprintln s!"::error::trusted declaration `{decl}` depends on `{ax}`"
      throwError "protected IRS path has non-whitelisted axioms"
  IO.println "ok — protected IRS path uses only propext/Classical.choice/Quot.sound"
