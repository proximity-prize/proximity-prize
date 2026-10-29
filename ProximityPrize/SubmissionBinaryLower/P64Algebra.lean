import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity

/-!
The generic algebra layer stays independent of the concrete benchmark. Its
explicit imports avoid loading unrelated Mathlib and protocol developments
for each component check.
-/
