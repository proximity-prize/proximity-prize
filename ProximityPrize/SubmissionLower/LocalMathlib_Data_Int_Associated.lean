/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.Data.Int.Associated.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 1a04fceaa7b52d91e882fd28f7750bbab178d069ebe9dcceb3070c7e24f1e231.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/
/-!
# Associated elements and the integers

This file contains some results on equality up to units in the integers.

## Main results

* `Int.natAbs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/

section ProximityFlatProofPort


theorem Int.natAbs_eq_iff_associated {a b : ℤ} : a.natAbs = b.natAbs ↔ Associated a b := by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
