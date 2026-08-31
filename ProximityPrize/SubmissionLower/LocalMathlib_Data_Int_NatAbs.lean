/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Anne Baanen,Jeremy Tan
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
namespace Int
@[simps]
def natAbsHom:ℤ →*₀ ℕ where
  toFun:=Int.natAbs
  map_mul':=Int.natAbs_mul
  map_one':=Int.natAbs_one
  map_zero':=Int.natAbs_zero
lemma natAbs_natCast_sub_natCast_of_ge {a b:ℕ} (h:b ≤ a):Int.natAbs (↑a-↑b)=a-b:=by
  lia
lemma natAbs_natCast_sub_natCast_of_le {a b:ℕ} (h:a ≤ b):Int.natAbs (↑a-↑b)=b-a:=by
  lia
end Int
