import Lean

def identityType : Lean.Expr :=
  .forallE `P (.sort .zero)
    (.forallE `h (.bvar 0) (.bvar 1) .default) .default

def identityProof : Lean.Expr :=
  .lam `P (.sort .zero) (.lam `h (.bvar 0) (.bvar 0) .default) .default

def check (proof : Lean.Expr) : IO Unit := do
  let ci : Lean.ConstantInfo := .thmInfo {
    name := `replayRegression
    levelParams := []
    type := identityType
    value := proof
  }
  let constants := ({} : Std.HashMap Lean.Name Lean.ConstantInfo).insert ci.name ci
  let env ← Lean.Environment.replay constants (← Lean.mkEmptyEnvironment)
  unless env.toKernelEnv.find? ci.name |>.isSome do
    throw <| IO.userError "Replay omitted the theorem"

def main : IO Unit := do
  check identityProof
  IO.println "PASS: valid closed proof accepted by fresh replay"
  let rejected ← try
    check (.sort .zero)
    pure false
  catch _ => pure true
  unless rejected do
    throw <| IO.userError "Invalid proof was accepted"
  IO.println "PASS: invalid closed proof rejected by fresh replay"
