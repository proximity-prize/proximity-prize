import ProximityPrize.SubmissionLower.R6961MarkedPrincipalParts
import ProximityPrize.SubmissionLower.R6961RetainedAxisTransition

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent RetainedRestrictionTorus
open RetainedSurfaceClass RetainedTwistedRestriction ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass Lower6961.MarkedEvaluation
open Lower6961.RetainedTwistedRestriction (regular_on_overlap)
open Lower6961.RetainedSurfaceClass (congr_of_eq)
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def torFrame (E:Type) [Field E] [Algebra ChartField E] (s:Chart) : Tor E :=
  ⟨fr s,isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).1⟩:torus))⟩

/-- A section on the actual specialized abscissa line, with its degree represented
in the infinity frame. The two tested images are the original surface orders. -/
def FibreSection (i:ℕ) (z:L) (v:Axis E true z) : Prop :=
  ∀ b:Bool, ∃u:Tor E, IsIntegral (baseChart (reference true b)) (u:E) ∧
    red E true z ((torFrame E (reference true b))^i*u)=v

private theorem equal_residues (j c) (u v:Tor E) (h:Congruent j c (u:E) (v:E)) :
    red E j c u=red E j c v := by
  obtain ⟨r,ir,eq⟩:=h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨⟨r,ir⟩,Subtype.ext eq⟩)

/-- Actual affine representatives for a marked fibre section on all four charts.
Dividing these representatives by the scalar parameter gives compatible principal
parts on the normalized surface. -/
theorem word_principal_parts [FiniteDimensional ChartField E]
    (i:ℕ) (z:L) (nz:z≠0) (v:Axis E true z) (sectionOnLine:FibreSection i z v) :
    ∃ w:Chart→Tor E, (∀s,Regular s i (w s:E)) ∧ (∀s, red E true z (w s)=v) ∧
      ∀s t,Over s t i ((w s:E)/ι (divisor true z)-(w t:E)/ι (divisor true z)) := by
  classical
  have atChart (s:Chart):∃w:Tor E,Regular s i (w:E) ∧ red E true z w=v := by
    let t:=reference true s.1
    obtain ⟨a,ia,eq⟩:=sectionOnLine s.1
    have parallel:axisBit s (!true)=axisBit t (!true):=rfl
    obtain ⟨q,iq,matchValue⟩:=line_representative true z nz s t parallel (a:E) (order_mono (chart_cover s t) ia)
    let Q:Tor E:=⟨q,order_mono (base_torus s) iq⟩
    have frameEq:torFrame E t=torFrame E s := rfl
    have eqQ:=equal_residues true z a Q matchValue
    let w:=torFrame E s^i*Q
    refine ⟨w,?_,?_⟩
    · change IsIntegral _ ((fr s)⁻¹^i*(fr s^i*q))
      have nzf : (fr s:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)
      rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ nzf,one_pow,one_mul]
      exact iq
    · change Ideal.Quotient.mk _ ((torFrame E s)^i*Q)=v
      change Ideal.Quotient.mk _ a=Ideal.Quotient.mk _ Q at eqQ
      rw [map_mul,←eqQ,←map_mul,←frameEq];exact eq
  choose w regular value using atChart
  refine ⟨w,regular,value,fun s t=>?_⟩
  let D:=ι (divisor true z)
  let V:=(fr s)⁻¹^i*((w s:E)/D-(w t:E)/D)
  have dn:D≠0:=(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne _ _)
  have zn:zcut s z≠0:=by
    intro zero
    exact (div_ne_zero (divisor_ne true z) (localFrame_ne s true))
      ((zcut_value s z).symm.trans (congrArg (fun a:baseChart s=>(a:ChartField)) zero))
  have : UniqueFactorizationMonoid (baseChart s) := (MonicChartProbes.planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  apply cancel_equation s t (zcut s z) zn (IsRelPrime.mul_right_iff.mp (boundary_rel s 1 z one_ne_zero nz)).2.symm V
  · have lhs:=order_mono (into_cleared _ (edge s t)) (regular s)
    have rhs:=Lower6961.RetainedTwistedRestriction.regular_on_overlap s t i _ (regular t)
    have base:(localFrame s true)⁻¹∈baseChart s := by
      have h:chartCoordinate s.2 scalarCoordinate∈baseChart s:=Subring.subset_closure (Or.inr (Or.inr rfl))
      by_cases ht:s.2=true <;> simp [localFrame,axisBit,coordinate,ht,chartCoordinate] at * <;> assumption
    have inv:IsIntegral (baseChart s) (ι ((localFrame s true)⁻¹):E) := isIntegral_algebraMap (x:=(⟨_,base⟩:baseChart s))
    have reg:= (order_mono (into_cleared _ (edge s t)) inv).mul (lhs.sub rhs)
    change IsIntegral _ (ι (zcut s z:ChartField)*V)
    rw [zcut_value,map_div₀]
    have eq : (D/ι (localFrame s true))*V = ι ((localFrame s true)⁻¹)*((fr s)⁻¹^i*(w s:E)-(fr s)⁻¹^i*(w t:E)) := by
      dsimp only [V];rw [map_inv₀];field_simp [dn,(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s true)]
      <;> ring
    rw [eq];exact reg
  · obtain ⟨r,ir,rr⟩:=Lower6961.RetainedSurfaceClass.congr_of_eq E true z (w s) (w t) ((value s).trans (value t).symm)
    have inv : IsIntegral torus (fr s:E)⁻¹ := by rw [fr,←map_inv₀];exact isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).2⟩:torus))
    change IsIntegral torus ((fr s)⁻¹^i*((w s:E)/D-(w t:E)/D))
    rw [←sub_div,rr,show ι (divisor true z)=D from rfl,mul_div_cancel_left₀ _ dn]
    exact (inv.pow _).mul ir

#print axioms word_principal_parts
end Lower6961.MarkedEvaluation
