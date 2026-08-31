import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y2
namespace ProximityPrize.SubmissionLower.RCN168
open RCN051
def implicitWeightedCap:ℕ:=(2*slopeCap-1)*weightedCap
def implicitYCap:ℕ:=(implicitWeightedCap-1)/w
def liftedSurface:DegreeVector:=⟨implicitYCap,1,algebraicCap⟩
def implicitCut:DegreeVector:=⟨implicitYCap,0,algebraicCap⟩
def liftedLastTail:DegreeVector:=
 ⟨1+2*implicitWeightedCap*implicitYCap,
   implicitWeightedCap,2*implicitWeightedCap*algebraicCap⟩
def liftedAgreement:DegreeVector:=
 ⟨1+2*w*implicitYCap,w,2*w*algebraicCap+1⟩
def liftedSingularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
   mixed liftedSurface implicitCut liftedLastTail+
   (errors+1)*mixed liftedSurface implicitCut unitZ)+
 (n-w)*mixed liftedSurface implicitCut liftedAgreement
def liftedTotalNumerator:ℕ:=regularNumerator+gap*liftedSingularNumerator
theorem lifted_parameter_values:
   implicitWeightedCap=29924640∧implicitYCap=228∧
   liftedLastTail=⟨13645635841,29924640,94801259520⟩∧
   liftedAgreement=⟨59768377,131071,415232929⟩:=by
 norm_num [implicitWeightedCap,implicitYCap,liftedLastTail,liftedAgreement,
   algebraicCap,weightedCap,RCN051.multiplicity,agreements,
   w,slopeCap,seedTotalCap]
theorem lifted_projection_values:
   mixed liftedSurface implicitCut unitY=1584∧
   mixed liftedSurface implicitCut unitR=722304∧
   mixed liftedSurface implicitCut unitZ=228:=by
 norm_num [mixed,liftedSurface,implicitCut,implicitYCap,implicitWeightedCap,
   unitY,unitR,unitZ,algebraicCap,weightedCap,
   RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem lifted_projection_characteristic_gates:
   implicitWeightedCap < prime∧
   mixed liftedSurface implicitCut unitY < prime∧
   mixed liftedSurface implicitCut unitR < prime∧
   mixed liftedSurface implicitCut unitZ < prime:=by
 rcases lifted_projection_values with ⟨hY,hR,hZ⟩
 rw [hY,hR,hZ,lifted_parameter_values.1]
 norm_num [prime]
theorem lifted_singular_numerator_exact:
   liftedSingularNumerator=3516047537415780312:=by
 norm_num [liftedSingularNumerator,mixed,liftedSurface,implicitCut,liftedLastTail,
   liftedAgreement,implicitYCap,implicitWeightedCap,unitZ,algebraicCap,
   weightedCap,RCN051.multiplicity,agreements,w,gap,
   errors,n,slopeCap,seedTotalCap]
theorem lifted_total_numerator_exact:
   liftedTotalNumerator=143697127886496891242366373:=by
 rw [liftedTotalNumerator,lifted_singular_numerator_exact]
 norm_num [regularNumerator,cutNumerator,wholeNumerator,mixed,
   firstTail,lastTail,tailVector,agreementVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,
   w,gap,errors,n,slopeCap,seedTotalCap]
theorem lifted_division_certificate:
   liftedTotalNumerator=49925776167317549*gap^2+2316504024∧
   2316504024 < gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num
theorem lifted_ceiling_exact:
   49925776167317549*gap^2 < liftedTotalNumerator∧
     liftedTotalNumerator ≤ 49925776167317550*gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num
theorem lifted_strict_budget:
   liftedTotalNumerator < alignmentBudget*gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num [alignmentBudget]
end ProximityPrize.SubmissionLower.RCN168
