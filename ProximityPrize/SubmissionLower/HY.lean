import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
@[simp high]
theorem LinearMap.det_zero'' {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
   [Module.Free R M] [Module.Finite R M] [Nontrivial M]:LinearMap.det (0:M →ₗ[R] M)=0:=by
 letI:Nonempty (Module.Free.ChooseBasisIndex R M):=(Module.Free.chooseBasis R M).index_nonempty
 nontriviality R
 exact LinearMap.det_zero' (Module.Free.chooseBasis R M)
