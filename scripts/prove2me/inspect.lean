import Lean
open Lean

/-- Stable structural types across separate native/platform environments. Binder
names and metadata are irrelevant; constants and universe positions are not. -/
private def mappedName (renames : Array (String × String)) (n : Name) : String := Id.run do
  let value := ((privateToUserName? n).getD n).toString
  for (generated, original) in renames do
    let generated := ((privateToUserName? generated.toName).getD generated.toName).toString
    let original := ((privateToUserName? original.toName).getD original.toName).toString
    if value == generated then return original
    if value.startsWith (generated ++ ".") then return original ++ (value.drop generated.length).toString
  return value

private partial def levelJson (params : List Name) : Level → Json
  | .zero => toJson ("zero" : String)
  | .succ u => Json.arr #[toJson "succ", levelJson params u]
  | .max a b => Json.arr #[toJson "max", levelJson params a, levelJson params b]
  | .imax a b => Json.arr #[toJson "imax", levelJson params a, levelJson params b]
  | .param n => Json.arr #[toJson "param", toJson (params.idxOf n)]
  | .mvar _ => toJson "UNRESOLVED_UNIVERSE"

private partial def exprJson (params : List Name) (renames : Array (String × String)) (e : Expr) : Json :=
  let go := exprJson params renames
  match e with
  | .bvar i => Json.arr #[toJson "bound", toJson i]
  | .fvar _ | .mvar _ => toJson "UNRESOLVED_TERM"
  | .sort u => Json.arr #[toJson "sort", levelJson params u]
  | .const n us => Json.arr #[toJson "const", toJson (mappedName renames n), toJson (us.map (levelJson params))]
  | .app f a => Json.arr #[toJson "app", go f, go a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (reprStr bi), go t, go b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (reprStr bi), go t, go b]
  | .letE _ t v b _ => Json.arr #[toJson "let", go t, go v, go b]
  | .lit (.natVal n) => Json.arr #[toJson "nat", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "string", toJson s]
  | .mdata _ e => go e
  | .proj s i e => Json.arr #[toJson "proj", toJson (mappedName renames s), toJson i, go e]

private def constantValue : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- Skip only explicitly named platform statement stubs. Every other reachable
axiom, including a direct or hidden sorry, remains visible to the caller. -/
private def axioms (env : Environment) (root : Name) (allowed : Array String) : Array String := Id.run do
  let mut pending := [root]
  let mut seen : Std.HashSet Name := {}
  let mut result : Array String := #[]
  while h : pending ≠ [] do
    let n := pending.head h
    pending := pending.tail
    if seen.contains n || allowed.contains n.toString then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      if ci.isUnsafe || ci.isPartial then result := result.push s!"unsafe:{n}"
      match ci with
      | .axiomInfo _ => result := result.push n.toString
      | _ => pure ()
      pending := (ci.type.getUsedConstants ++ ((constantValue ci).map Expr.getUsedConstants |>.getD #[])).toList ++ pending
  return result.qsort (· < ·)

unsafe def main (args : List String) : IO UInt32 := do
  let some configFile := args[0]? | throw <| IO.userError "Expected inspection config"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (System.FilePath.mk configFile))
  let moduleName ← IO.ofExcept <| config.getObjValAs? String "module"
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "names"
  let renames ← IO.ofExcept <| config.getObjValAs? (Array (String × String)) "renames"
  let allowed ← IO.ofExcept <| config.getObjValAs? (Array String) "allowedStubs"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {} 0
  for name in names do
    let some ci := env.find? name.toName | throw <| IO.userError s!"Missing declaration {name}"
    let body := match ci with
      | .defnInfo d => exprJson ci.levelParams renames d.value
      | .opaqueInfo o => exprJson ci.levelParams renames o.value
      | _ => Json.null
    let shape := match ci with
      | .inductInfo d => Json.arr ((d.ctors.toArray).map fun ctor =>
          match env.find? ctor with
          | some c => exprJson c.levelParams renames c.type
          | none => toJson "MISSING_CONSTRUCTOR")
      | _ => Json.null
    IO.println (Json.mkObj [("name", toJson name), ("levels", toJson ci.levelParams.length), ("body", body), ("shape", shape),
      ("type", exprJson ci.levelParams renames ci.type), ("modules", toJson (env.header.moduleNames.map Name.toString)), ("axioms", toJson (axioms env name.toName allowed))]).compress
  return 0
