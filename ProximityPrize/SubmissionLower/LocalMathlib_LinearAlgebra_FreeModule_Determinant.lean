/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Anne Baanen,Alex J. Best
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
@[simp high]
theorem LinearMap.det_zero'' {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Nontrivial M]:LinearMap.det (0:M →ₗ[R] M)=0:=by
  letI:Nonempty (Module.Free.ChooseBasisIndex R M):=(Module.Free.chooseBasis R M).index_nonempty
  nontriviality R
  exact LinearMap.det_zero' (Module.Free.chooseBasis R M)
