/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.RingTheory.Finiteness.Quotient.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: cf4626228125398ee2095b10fd10e442fdef29380c21ac1d74ec8cce4a9a2f7b.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .

 -/

section ProximityFlatProofPort

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (P : Ideal B) (p : Ideal A) [P.LiesOver p]

/-- . -/
instance module_finite_of_liesOver [Module.Finite A B] : Module.Finite (A ⧸ p) (B ⧸ P) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

/-- . -/
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B] :
    Algebra.FiniteType (A ⧸ p) (B ⧸ P) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

/-- . -/
instance isNoetherian_of_liesOver [IsNoetherian A B] : IsNoetherian (A ⧸ p) (B ⧸ P) :=
  isNoetherian_of_tower A inferInstance

instance QuotientMapQuotient.isNoetherian [IsNoetherian A B] :
    IsNoetherian (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
  isNoetherian_of_tower A <|
    isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
