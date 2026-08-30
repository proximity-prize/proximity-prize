import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y2
namespace ProximityPrize.SubmissionLower.RCN242
open RCN051
def surfaceVector:DegreeVector:=⟨yCap,slopeCap,seedTotalCap⟩
theorem first_cut_projection_values:
   mixed surfaceVector firstTail unitY=438304768∧
   mixed surfaceVector firstTail unitR=2283798704∧
   mixed surfaceVector firstTail unitZ=61603845:=by
 norm_num [mixed,surfaceVector,firstTail,tailVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem agreement_cut_projection_values:
   mixed surfaceVector agreementVector unitY=438301429∧
   mixed surfaceVector agreementVector unitR=2283781305∧
   mixed surfaceVector agreementVector unitZ=61603375:=by
 norm_num [mixed,surfaceVector,agreementVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem non_R_projection_caps_below_characteristic:
   mixed surfaceVector firstTail unitY < prime∧
   mixed surfaceVector firstTail unitZ < prime∧
   mixed surfaceVector agreementVector unitY < prime∧
   mixed surfaceVector agreementVector unitZ < prime:=by
 rcases first_cut_projection_values with ⟨h1,h2,h3⟩
 rcases agreement_cut_projection_values with ⟨h4,h5,h6⟩
 rw [h1,h3,h4,h6]
 norm_num [prime]
end ProximityPrize.SubmissionLower.RCN242
