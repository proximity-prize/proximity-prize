import ProximityPrize.SubmissionLower.Koala6844Assembly
import ProximityPrize.SubmissionLower.Koala6844Primitive

namespace ProximityPrize.SubmissionLower.Koala6844Assembly

theorem protocolClaim_of_retained_geometry
    (hGeometry : Koala6844BenchmarkGeometry.RemainingGeometrySeedBound) :
    ProximityPrize.Benchmark.ProtocolClaim 6844 332546047 1073741824 :=
  protocolClaim_of_scalar_seed_bound
    (Koala6844BenchmarkCases.seed_bound_of_rank_one
      (Koala6844BenchmarkGeometry.rank_one_bound_of_geometry hGeometry))

end ProximityPrize.SubmissionLower.Koala6844Assembly

