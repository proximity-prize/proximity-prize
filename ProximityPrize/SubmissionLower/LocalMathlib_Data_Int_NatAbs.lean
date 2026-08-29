/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Jeremy Tan
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.Data.Int.NatAbs.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 4cc46e92ddae85345f19a2a2d6bbacc2681d8d3ce5c6af6ca6cb97cbe248beef.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-!
# Lemmas about `Int.natAbs`

This file contains some results on `Int.natAbs`, the absolute value of an integer as a
natural number.

## Main results

* `Int.natAbsHom`: `Int.natAbs` bundled as a `MonoidWithZeroHom`.
-/

section ProximityFlatProofPort

namespace Int

/-- `Int.natAbs` as a bundled `MonoidWithZeroHom`. -/
@[simps]
def natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero

lemma natAbs_natCast_sub_natCast_of_ge {a b : ℕ} (h : b ≤ a) : Int.natAbs (↑a - ↑b) = a - b := by
  lia

lemma natAbs_natCast_sub_natCast_of_le {a b : ℕ} (h : a ≤ b) : Int.natAbs (↑a - ↑b) = b - a := by
  lia

end Int
