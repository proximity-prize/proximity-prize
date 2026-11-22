import ProximityPrize.SubmissionLower.RungSplit
import ProximityPrize.SubmissionLower.Numeric6Defs
import ProximityPrize.SubmissionLower.FrontBranch12

set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Protocol82180
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
abbrev I := P3.I
abbrev K := P3.K
abbrev Words := P3.Words
abbrev node := P3.node
abbrev k := P3.k
open scoped NNReal

abbrev agreement : ℕ := 179964
abbrev listCap : ℕ := 7936304360743194
end
end Protocol82180
