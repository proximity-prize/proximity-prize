import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxis
import ProximityPrize.SubmissionLower.R6960MarkedWordResidues

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open RetainedSurfaceClass RetainedRestrictionTorus ChartSections
open RetainedTwistedRestriction MarkedEvaluation

variable {E : Type} [Field E] [Algebra ChartField E]

local instance sectionAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

/-- The actual global abscissa function is a unit on the common axis. -/
def axisX (z:L) : (Axis E true z)ˣ :=
  Units.map (Ideal.Quotient.mk (axisIdeal E true z)).toMonoidHom (varUnit E false)

/-- A matching pair of regular original chart values is a section in the
literal interface used by the marked principal-parts construction. -/
theorem fibreSection_of_chart_pair (a:ℕ) (z:L) (v:Axis E true z)
    (finite : v∈chartImage E true z false)
    (infinity : ((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v∈chartImage E true z true) :
    FibreSection (E:=E) a z v := by
  intro b
  cases b
  · obtain ⟨u,reg,val⟩ := finite
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true false)=1 := by
      apply Subtype.ext
      change algebraMap ChartField E (localFrame (reference true false) false)=1
      rw [show localFrame (reference true false) false=1 from rfl,map_one]
    rw [eq,one_pow,one_mul]
    exact val
  · obtain ⟨u,reg,val⟩ := infinity
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true true)=(varUnit E false:Tor E) := rfl
    rw [eq]
    change Ideal.Quotient.mk (axisIdeal E true z) (((varUnit E false:Tor E)^a)*u)=v
    rw [map_mul,map_pow]
    have q : Ideal.Quotient.mk (axisIdeal E true z) (varUnit E false:Tor E)=
        (axisX (E:=E) z:Axis E true z) := rfl
    rw [q,show Ideal.Quotient.mk (axisIdeal E true z) u=((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v from val,
      ←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]

#print axioms fibreSection_of_chart_pair
end
end Lower6960.CollisionMarked
