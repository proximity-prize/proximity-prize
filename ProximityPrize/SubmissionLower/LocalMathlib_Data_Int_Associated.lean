/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Anne Baanen
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
theorem Int.natAbs_eq_iff_associated {a b:ℤ}:a.natAbs=b.natAbs ↔ Associated a b:=by
  refine Int.natAbs_eq_natAbs_iff.trans ?_
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1,by simp⟩
  · rintro ⟨u,rfl⟩
    obtain rfl | rfl:=Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
