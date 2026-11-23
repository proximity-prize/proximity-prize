import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Data.Int.Interval
set_option Elab.async false
set_option autoImplicit true
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
open ReedSolomon.HiddenDerivative PolynomialDifferential
abbrev Jet := (s : Fin 65) × (e2 : Fin (min s.val 10 + 1)) ×
  Fin (min (s.val - e2.val) (21 - 2 * e2.val) + 1)
def e1 (j : Jet) : ℕ := j.2.2.val
def e2 (j : Jet) : ℕ := j.2.1.val
def e0 (j : Jet) : ℕ := j.1.val - e2 j - e1 j
def width (j : Jet) : ℕ := 48 * 180265 - 131072 * j.1.val + e1 j + 2 * e2 j
abbrev SourceIndex := (j : Jet) × Fin (width j)
def columns (i : SourceIndex) : SourceColumn 2 where
  x := i.2.val
  y₀ := e0 i.1
  higher := ![e1 i.1, e2 i.1]
end Sol1.C42
end
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
def rowCount (s : ℕ) (g : ℤ) : ℕ :=
  let L : ℤ := 48 - g - s
  let lo : ℤ := max 0 (-g)
  let hi : ℤ := min 21 (47 - g)
  if 0 < L ∧ lo ≤ hi then
    ∑ b ∈ Finset.range (min s ((L - 1) / 2).toNat + 1),
      (((min ((s : ℤ) - b - 1) (L - 1 - 2 * b)) - max 0 (lo - s + b) + 1).toNat +
        if 2 * (b : ℤ) + ((s : ℤ) - b) < L ∧
          2 * ((lo + 1) / 2) ≤ min hi (2 * ((s : ℤ) - b)) then 1 else 0)
  else 0
end Sol1.C42
end
section
namespace Sol1.C42
open ReedSolomon.HiddenDerivative
end Sol1.C42
end
