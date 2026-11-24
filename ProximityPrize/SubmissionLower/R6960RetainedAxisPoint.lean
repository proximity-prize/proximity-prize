import ProximityPrize.SubmissionLower.R6960RetainedAxisFree
import ProximityPrize.SubmissionLower.R6960RetainedLineEvaluation
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus MonicChartProbes
open Module Submodule Algebra Polynomial
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (toCross toCross_kernel finiteX_val finiteZ_val)
open Lower6960.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]

def atCoord (j:Bool) (x z:L) := if j then z else x
def nodeMap (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₗ[L] Crossing E x z :=
  match j with | false=>crossingX E x z | true=>crossingZ E x z
theorem through (j:Bool) (x z:L) (v:Tor E) :
    nodeMap E j x z (red E j (atCoord j x z) v)=Ideal.Quotient.mk _ v := by cases j <;> rfl

theorem onto_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) :
    Function.Surjective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false).subtype) := by
  intro w
  obtain ⟨u,hu⟩ := cross_surjective E x z nx nz w
  have s : reference j false=(false,false) := by cases j <;> rfl
  refine ⟨⟨red E j (atCoord j x z) (fromFinite E u),⟨fromFinite E u,?_,rfl⟩⟩,?_⟩
  · change IsIntegral (baseChart (reference j false)) u.val
    rw [s]; exact u.property
  · exact (through E j x z (fromFinite E u)).trans hu

theorem cut_running (j:Bool) (c:L) :
    along E j false (Polynomial.X-C c)=cut E (!j) c := by
  apply Subtype.ext
  rw [map_sub]
  change ((along E j false Polynomial.X):E)-((along E j false (C c)):E)=_
  rw [show along E j false Polynomial.X=
    (⟨algebraMap ChartField E (coordinate (!j)),isIntegral_algebraMap (x:=(⟨_,torus_coordinate (!j) false⟩:torus))⟩:Tor E)
    from eval₂_X _ _,show along E j false (C c)=algebraMap L (Tor E) c from eval₂_C _ _]
  exact (map_sub (algebraMap ChartField E) _ _).symm

private theorem coordinate_ideal (x z:L) (nx:x≠0) (nz:z≠0) (u:finiteOrder E)
    (zero : Lower6960.RetainedSurfaceClass.toCross E x z u=0) :
    ∃ a b:finiteOrder E, fromFinite E u=cut E false x*fromFinite E a+cut E true z*fromFinite E b := by
  have mem : u∈RingHom.ker (Lower6960.RetainedSurfaceClass.toCross E x z).toRingHom := RingHom.mem_ker.mpr zero
  rw [Lower6960.RetainedSurfaceClass.toCross_kernel E x z nx nz,point_kernel,Ideal.map_sup,
    Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton] at mem
  obtain ⟨_,hu,_,hv,eq⟩:=Submodule.mem_sup.mp mem
  obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp hv
  have fx : fromFinite E (algebraMap Base (finiteOrder E) (finiteX x))=cut E false x :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteX_val x))
  have fz : fromFinite E (algebraMap Base (finiteOrder E) (finiteZ z))=cut E true z :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteZ_val z))
  exact ⟨a,b,by rw [←eq,map_add,map_mul,map_mul,fx,fz]⟩

/-- The kernel of evaluation on the actual finite line chart consists of multiples
of its crossing coordinate. This identifies the point fibre even at the two chart boundaries. -/
theorem kernel_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:chartImage E j (atCoord j x z) false) :
    nodeMap E j x z u=0 ↔ ∃ v:chartImage E j (atCoord j x z) false,
      (u:Axis E j (atCoord j x z))=polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z))*v.val := by
  let R:=axisIdeal E j (atCoord j x z)
  let π:=Ideal.Quotient.mk R
  have fixed : π (cut E j (atCoord j x z))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have variableCut : polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z)) =
      π (cut E (!j) (atCoord (!j) x z)) := congrArg π (cut_running E j _)
  have origin : reference j false=(false,false) := by cases j <;> rfl
  have image (y : finiteOrder E) : π (fromFinite E y)∈chartImage E j (atCoord j x z) false := by
    refine ⟨fromFinite E y,?_,rfl⟩
    change IsIntegral (baseChart (reference j false)) y.val; rw [origin]; exact y.property
  constructor
  · intro hz
    obtain ⟨w,hw,ew⟩:=u.property
    change IsIntegral (baseChart (reference j false)) (w:E) at hw
    rw [origin] at hw
    let W:finiteOrder E:=⟨w,hw⟩
    have fw : fromFinite E W=w := rfl
    rw [←ew,through] at hz
    have zero : Lower6960.RetainedSurfaceClass.toCross E x z W=0 := hz
    obtain ⟨a,b,eq⟩:=coordinate_ideal E x z nx nz W zero
    have ed:=congrArg π eq
    rw [map_add,map_mul,map_mul,fw] at ed
    change π w=u.val at ew
    rw [ew] at ed
    cases j
    · refine ⟨⟨_,image b⟩,?_⟩
      change π (cut E false x)=0 at fixed
      rw [fixed,zero_mul,zero_add] at ed
      rw [variableCut]; exact ed
    · refine ⟨⟨_,image a⟩,?_⟩
      change π (cut E true z)=0 at fixed
      rw [fixed,zero_mul,add_zero] at ed
      rw [variableCut]; exact ed
  · rintro ⟨v,hv⟩
    obtain ⟨w,_,ew⟩:=v.property
    rw [hv,variableCut,←ew]
    change nodeMap E j x z (π (cut E (!j) (atCoord (!j) x z))*π w)=0
    rw [←map_mul]
    change nodeMap E j x z (red E j (atCoord j x z) _)=0
    rw [through E j x z, map_mul]
    have member : cut E (!j) (atCoord (!j) x z)∈axisIdeal E false x⊔axisIdeal E true z := by
      cases j
      · exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
      · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr member,zero_mul]

#print axioms onto_at_node
#print axioms kernel_at_node
end Lower6960.RetainedSurfaceClass
