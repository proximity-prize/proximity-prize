import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960RetainedGoodCrossing

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests MonicChartLaurent
open Polynomial
open private Lower6960.RetainedRestrictionTorus.linear from ProximityPrize.SubmissionLower.R6960RetainedRestrictionTorus
open scoped Polynomial

def coordinate (zAxis : Bool) : ChartField := if zAxis then scalarCoordinate else RatFunc.X
def axisBit (s : Chart) (zAxis : Bool) : Bool := if zAxis then s.2 else s.1
def localFrame (s : Chart) (zAxis : Bool) : ChartField :=
  if axisBit s zAxis then coordinate zAxis else 1
def divisor (zAxis : Bool) (c:L) : ChartField := coordinate zAxis-constants c

theorem coord_ne (j : Bool) : coordinate j≠0 := by cases j <;> simp [coordinate,scalar_ne,RatFunc.X_ne_zero]
theorem localFrame_ne (s : Chart) (j : Bool) : localFrame s j≠0 := by
  unfold localFrame; split <;> first | exact one_ne_zero | exact coord_ne _

theorem divisor_ne (j : Bool) (c:L) : divisor j c≠0 := by
  have nz:RetainedLineRestriction.lines c c≠0 := by
    have := MonicChartProbes.planeMap_injective (false,false)
    let a:PlaneConstants.Plane L:=Polynomial.X-C (C c)
    let b:PlaneConstants.Plane L:=C (Polynomial.X-C c)
    have h:= (map_ne_zero_iff _ this).mpr (mul_ne_zero (X_sub_C_ne_zero (C c))
      (C_ne_zero.mpr (X_sub_C_ne_zero c)))
    simpa [RetainedLineRestriction.lines,chartCoordinate] using h
  cases j
  · exact left_ne_zero_of_mul nz
  · exact right_ne_zero_of_mul nz

theorem xcut_value (s : Chart) (c:L) : (xcut s c : ChartField) = divisor false c/localFrame s false := by
  change planeMap s ((Lower6960.RetainedRestrictionTorus.linear s.1 c).map C)=_
  unfold Lower6960.RetainedRestrictionTorus.linear
  by_cases h:s.1=true <;> simp [h,map_sub,map_mul,divisor,localFrame,coordinate,axisBit,
    chartCoordinate,sub_mul,RatFunc.X_ne_zero,div_eq_mul_inv]
theorem zcut_value (s : Chart) (c:L) : (zcut s c : ChartField) = divisor true c/localFrame s true := by
  change planeMap s (C (Lower6960.RetainedRestrictionTorus.linear s.2 c))=_
  unfold Lower6960.RetainedRestrictionTorus.linear
  by_cases h:s.2=true <;> simp [h,map_sub,map_mul,divisor,localFrame,coordinate,axisBit,
    chartCoordinate,sub_mul,scalar_ne,div_eq_mul_inv]

theorem base_torus (s : Chart) : baseChart s≤torus :=
  (into_cleared _ (edge s s)).trans (to_torus s s)
theorem torus_coordinate (j : Bool) (b : Bool) : chartCoordinate b (coordinate j)∈torus := by
  apply base_torus (b,b)
  cases j <;> apply Subring.subset_closure <;> simp [coordinate]
theorem torus_frame (s : Chart) (j : Bool) : localFrame s j∈torus ∧ (localFrame s j)⁻¹∈torus := by
  unfold localFrame
  split
  · exact ⟨torus_coordinate j false,torus_coordinate j true⟩
  · simp
theorem chart_constant (s : Chart) (c:L) : constants c∈baseChart s :=
  Subring.subset_closure (Or.inl ⟨c,rfl⟩)

variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def Congruent (j : Bool) (c : L) (u v : E) : Prop :=
  ∃ r : E, IsIntegral torus r ∧ u-v=ι (divisor j c)*r

theorem Congruent.refl (j : Bool) (c : L) (u : E) : Congruent j c u u := ⟨0,isIntegral_zero,by simp⟩
theorem Congruent.symm {j c} {u v:E} (h : Congruent j c u v) : Congruent j c v u := by
  obtain ⟨r,hr,eq⟩:=h; exact ⟨-r,hr.neg,by rw [mul_neg,←eq,neg_sub]⟩
theorem Congruent.trans {j c} {u v w:E} (h : Congruent j c u v) (h' : Congruent j c v w) :
    Congruent j c u w := by
  obtain ⟨a,ia,eq⟩:=h; obtain ⟨b,ib,eq'⟩:=h'
  exact ⟨a+b,ia.add ib,by rw [mul_add,←eq,←eq']; abel⟩
theorem Congruent.sub {j c} {u v w h:E} (a : Congruent j c u v) (b : Congruent j c w h) :
    Congruent j c (u-w) (v-h) := by
  obtain ⟨r,ir,ea⟩:=a; obtain ⟨q,iq,eb⟩:=b
  exact ⟨r-q,ir.sub iq,by rw [mul_sub,←ea,←eb]; abel⟩

private theorem local_int {s : Chart} {a : ChartField} (ha:a∈baseChart s) : IsIntegral (baseChart s) (ι a : E) :=
  isIntegral_algebraMap (x:=(⟨a,ha⟩:baseChart s))
private theorem torus_int {a : ChartField} (ha:a∈torus) : IsIntegral torus (ι a : E) :=
  isIntegral_algebraMap (x:=(⟨a,ha⟩:torus))

/-- A transition regular on an overlap that inverts only the transverse coordinate
has a regular representative on the original chart after taking the line residue. -/
theorem line_representative (j : Bool) (c : L) (nc : c≠0) (s t : Chart)
    (parallel : axisBit s (!j)=axisBit t (!j)) (y : E) (regular : IsIntegral (overlapRing s t) y) :
    ∃ v:E,IsIntegral (baseChart s) v ∧ Congruent j c y v := by
  let A:=baseChart s
  let g:=edge s t
  let val : L:=if axisBit s j=axisBit t j then 1 else if axisBit s j then c⁻¹ else c
  have vn : val≠0 := by dsimp only [val]; split <;> first | exact one_ne_zero | split <;> simp [nc]
  have valMem:=chart_constant s val
  let cv:A:=⟨constants val,valMem⟩
  obtain ⟨n,cleared⟩:=localize_integral A _ g (edge_ne s t) le_rfl y regular
  obtain ⟨q,factor⟩: g-cv∣g^n-cv^n := sub_dvd_pow_sub_pow _ _ _
  have unitval : ι (constants val)≠(0:E) :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr ((map_ne_zero_iff _ constants.injective).mpr vn)
  have step : ∃ r : ChartField,r∈torus ∧ boundary s t-constants val=divisor j c*r := by
    by_cases same : axisBit s j=axisBit t j
    · refine ⟨0,torus.zero_mem,?_⟩
      cases j <;> simp_all [boundary,axisBit,val]
    · have eq : boundary s t=chartCoordinate (axisBit s j) (coordinate j) := by
        cases j <;> simp_all [axisBit,boundary,coordinate]
      rw [eq]
      have vv : val = if axisBit s j then c⁻¹ else c := by simp only [val,same,ite_false]
      rw [vv]
      by_cases neg : axisBit s j=true
      · refine ⟨-(coordinate j)⁻¹*constants c⁻¹,torus.mul_mem (torus.neg_mem (torus_coordinate j true))
          (base_torus s (chart_constant s c⁻¹)),?_⟩
        simp only [neg,ite_true,chartCoordinate,map_inv₀,divisor]
        field_simp [coord_ne j, (map_ne_zero_iff _ constants.injective).mpr nc]
        <;> ring
      · exact ⟨1,torus.one_mem,by simp [neg,chartCoordinate,divisor]⟩
  obtain ⟨r,ir,eq⟩:=step
  let b:=ι (constants val)
  let G:=ι (boundary s t)
  have inv : IsIntegral A (b⁻¹) := by
    have h : IsIntegral A (ι (constants val⁻¹)):=local_int (chart_constant s val⁻¹)
    simpa [b] using h
  refine ⟨b⁻¹^n*(G^n*y),(inv.pow n).mul cleared,?_⟩
  have it:= order_mono (to_torus s t) regular
  have iq : IsIntegral torus (ι (q:ChartField)) := torus_int (base_torus s q.property)
  refine ⟨-(b⁻¹^n*(ι r*ι (q:ChartField))*y),
    (((order_mono (base_torus s) (inv.pow n)).mul ((torus_int ir).mul iq)).mul it).neg,?_⟩
  have eq' : G-b=ι (divisor j c)*ι r := by simpa only [map_sub,map_mul,G,b] using congrArg ι eq
  have powers : G^n-b^n=(G-b)*ι (q:ChartField) := by
    have mapped:=congrArg (fun v:A=>ι (v:ChartField)) factor
    change ι ((boundary s t)^n-(constants val)^n) = ι ((boundary s t-constants val)*(q:ChartField)) at mapped
    simpa only [map_pow,map_sub,map_mul,G,b] using mapped
  have cancel : b⁻¹^n*b^n=1 := by rw [←mul_pow,inv_mul_cancel₀ unitval,one_pow]
  calc y-b⁻¹^n*(G^n*y) = -(b⁻¹^n*((G^n-b^n)*y)) := by linear_combination -y*cancel
       _ = _ := by rw [powers,eq']; ring

#print axioms line_representative
end Lower6960.RetainedRestrictionTorus
