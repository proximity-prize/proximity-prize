/-
Copyright (c) 2026 Xavier Généreux, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.RingTheory.Adjoin.Polynomial.Bivariate.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: d36e620393387e3539e2f29ec51ad926d9de0738a08a8e386f7cb4464a05c448.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .







 -/

noncomputable section

namespace Polynomial.Bivariate

open Polynomial Bivariate Algebra Transcendental

variable {R A : Type*} [CommRing R]

section Ring

variable [Ring A] [Algebra R A] {x : A}

/-- . -/
def Transcendental.algEquivAdjoin (hx : Transcendental R x) :
    R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X] :=
  mapAlgEquiv (algEquivOfTranscendental _ x hx)

theorem Transcendental.algEquivAdjoin_apply (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin p = mapAlgHom (aeval ⟨x, self_mem_adjoin_singleton R x⟩) p :=
  rfl

attribute [local instance] algebra in
theorem Transcendental.algEquivAdjoin_swap_eq_aeval (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin (swap p) = aeval (C ⟨x, self_mem_adjoin_singleton R x⟩) p := by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

end Ring

section CommRing

variable [CommRing A] [Algebra R A]

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

attribute [local instance] Polynomial.algebra in
theorem aeval_aeval_eq_aeval_algEquivAdjoin {x : A} (y : B)
    (hx : Transcendental R x) (p : R[X][Y]) :
    aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_singleton R y⟩ :
      adjoin R {y})) p) = aeval y (hx.algEquivAdjoin p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]

theorem _root_.IsAlgebraic.adjoin_singleton {x : A} {y : B} (hx : Transcendental R x)
    (hy : Transcendental R y) (h : IsAlgebraic (adjoin R {x}) y) :
    IsAlgebraic (adjoin R {y}) (algebraMap A B x) := by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy, aeval_aeval_eq_aeval_algEquivAdjoin y hx]

end CommRing

end Polynomial.Bivariate

end
