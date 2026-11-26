import ProximityPrize.SubmissionBinaryLower.B6402LinearSplit
import ProximityPrize.SubmissionBinaryLower.B6402ScalarCases

namespace ProximityPrize.SubmissionBinaryLower.B6402HardReduction
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary

theorem protocol (line : B6402LinearSplit.HardLinear) (list : B6402ScalarCases.HardList) :
    ProtocolClaim 6402 78643482 268435456 :=
  B6402FactorAssembly.protocol_from_factor_and_scalar
    (B6402FactorCases.positive (B6402LinearSplit.linear_of_hard line) B6402QuadraticCase.quadratic)
    (B6402ScalarCases.scalar_of_hard list)

#print axioms protocol
end ProximityPrize.SubmissionBinaryLower.B6402HardReduction
