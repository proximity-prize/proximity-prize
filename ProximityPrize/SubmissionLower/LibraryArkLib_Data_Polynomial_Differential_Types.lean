import ProximityPrize.Benchmark.TargetLower
set_option Elab.async false
/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/




/-!
# Finite-jet polynomial relations

This file defines the variables and polynomial type for relations in an independent coordinate
and a finite Hasse jet. The representation is shared by polynomial interpolation and differential
root-finding arguments.

The definitions are adapted, with permission, from `kz99/rs-ld-mca`.
-/

section

namespace PolynomialDifferential

/-- Variables `X, Y₀, ..., Y_d`. `none` denotes `X`; `some j` denotes `Y_j`. -/
abbrev JetVariable (d : ℕ) := Option (Fin (d + 1))

/-- A polynomial in `X, Y₀, ..., Y_d` over `F`. -/
abbrev DifferentialPolynomial (F : Type*) [CommSemiring F] (d : ℕ) :=
  MvPolynomial (JetVariable d) F

end PolynomialDifferential
