import ProximityPrize.SubmissionLower.LowerGeometry
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain
open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]

variable {Iota : Type}

end
end ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain

namespace ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]

variable {I : Type}

end
end ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget

namespace ProximityPrize.SubmissionLower.BoundaryTailChainHelper
open AsymmetricHelper
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 RCN294 LocatorDerivativeChain BoundaryTailSharedDegreeBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K I : Type} [Field K]

end
end ProximityPrize.SubmissionLower.BoundaryTailChainHelper

namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811

namespace ProximityPrize.SubmissionLower.Lower80811.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811 BoundaryTailChainHelper AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

end
end ProximityPrize.SubmissionLower.Lower80811.Counting

namespace ProximityPrize.SubmissionLower.Lower80811.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end
end ProximityPrize.SubmissionLower.Lower80811.Budgets
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.FoldChain6813
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052 RCN264 RCN007 RCN004 RCN072 LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}

section Components

variable (K)

end Components

end
end ProximityPrize.SubmissionLower.FoldChain6813
end MergedPart1
