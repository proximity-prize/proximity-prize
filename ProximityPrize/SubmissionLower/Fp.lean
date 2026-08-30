import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.B
namespace ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
open ContactGenericSurface ContactRegularFactorGate
open ContactIdentityResidualIterationResearch
open ContactFlagBezout6543Research
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
theorem residualStage_pderiv_one_ne_zero
   (S:ResidualStage phi Gamma x p e flag d):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
end
end ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
