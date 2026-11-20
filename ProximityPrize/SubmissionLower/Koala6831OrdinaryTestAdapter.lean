import ProximityPrize.SubmissionLower.Koala6831OrdinaryFactorCount
import Mathlib.FieldTheory.Finite.Basic
import ProximityPrize.SubmissionLower.LowerFoundation
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import ProximityPrize.SubmissionLower.Koala6831BivariateSeeds
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import ProximityPrize.SubmissionLower.Koala6831OrdinaryCarrierLift
import ProximityPrize.SubmissionLower.Koala6831OrdinaryFullTest
import ProximityPrize.SubmissionLower.Koala6831OrdinaryTests


namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open Koala6831Intrinsic (implicitRegularity graphSpecialize)
open ProximityPrize.Benchmark
open RCN136 RCN137 MvPolynomial
open scoped Classical Polynomial BigOperators

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000

variable {K E Ω I : Type} [Field K] [Field E] [Field Ω]

private theorem ordinarySurface_rename (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ F = MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (surfaceMap φ F) := rfl


theorem ordinarySurface_implicitRegularity (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ (implicitRegularity F) = MvPolynomial.pderiv (1 : Fin 3) (ordinarySurface φ F) := by
  rw [ordinarySurface_rename, ordinarySurface_rename, implicitRegularity]
  have hswap : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  have h := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 3) 1).injective 0 (surfaceMap φ F)
  rw [hswap, RCN267.surfaceMap_pderiv] at h
  exact h.symm






end

end ProximityPrize.SubmissionLower.Koala6831Ordinary

