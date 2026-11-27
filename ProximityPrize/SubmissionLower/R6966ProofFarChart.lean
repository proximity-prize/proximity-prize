import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Union
import ProximityPrize.SubmissionLower.R6960MonicChartFrobenius
import ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant

set_option Elab.async false

-- merged module R6960MonicFourChartDescent
section Merged_R6960MonicFourChartDescent

-- merged module R6960ChartSections
section Merged_R6960ChartSections
namespace Lower6960.ChartSections
abbrev Exponent := ℤ×ℤ
abbrev Chart := Bool×Bool
def fits (d : ℕ) (s : Bool) (i : ℤ) : Prop :=
  if s then i ≤ -(d:ℤ) else 0 ≤ i
def allowed (a b : ℕ) (s : Chart) (m : Exponent) : Prop :=
  fits a s.1 m.1 ∧ fits b s.2 m.2
def overlap (a b : ℕ) (s t : Chart) (m : Exponent) : Prop :=
  (s.1=t.1 → fits a s.1 m.1) ∧ (s.2=t.2 → fits b s.2 m.2)
private def opposite (i : ℤ) : Bool := decide (0 ≤ i)
private theorem excluded (d : ℕ) (hd : 0<d) (i : ℤ) : ¬fits d (opposite i) i := by
  by_cases hi : 0 ≤ i
  · simp [opposite,hi,fits]; omega
  · simp [opposite,hi,fits]
theorem negative_correction {k : Type*} [AddCommGroup k] (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (p : Chart→Exponent→₀k)
    (compatible : ∀ s t m,¬overlap a b s t m → (p s) m=(p t) m) :
    ∃ c : Exponent→₀k, ∀ s m,¬allowed a b s m → (p s-c) m=0 := by
  classical
  let coeff (m : Exponent) := p (opposite m.1,opposite m.2) m
  let support := Finset.univ.biUnion fun s : Chart=>(p s).support
  let c : Exponent→₀k := Finsupp.onFinset support coeff (fun m hm=>
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hm⟩)
  refine ⟨c,?_⟩
  rintro ⟨s,t⟩ ⟨i,j⟩ bad
  change ¬(fits a s i ∧ fits b t j) at bad
  change p (s,t) (i,j)-p (opposite i,opposite j) (i,j)=0
  apply sub_eq_zero.mpr
  by_cases bx : fits a s i
  · have bz : ¬fits b t j := fun z=>bad ⟨bx,z⟩
    calc p (s,t) (i,j) = p (opposite i,t) (i,j) := compatible (s,t) (opposite i,t) (i,j) (fun h=>bz (h.2 rfl))
         _ = _ := compatible (opposite i,t) (opposite i,opposite j) (i,j) (fun h=>excluded a ha i (h.1 rfl))
  · calc p (s,t) (i,j) = p (s,opposite j) (i,j) := compatible (s,t) (s,opposite j) (i,j) (fun h=>bx (h.1 rfl))
         _ = _ := compatible (s,opposite j) (opposite i,opposite j) (i,j) (fun h=>excluded b hb j (h.2 rfl))






section
variable {k ι J : Type*} [CommRing k] [Fintype ι]































end
end Lower6960.ChartSections

end Merged_R6960ChartSections

-- merged module R6960MonicFourChartDescent
section Merged_R6960MonicFourChartDescent
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicFourChartDescent
noncomputable section
open Polynomial
open K1_14 (L)
open MonicChart (ChartField Scalar Infinity)
open ChartSections (Chart)
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
def constants : L →+* ChartField := RatFunc.C.comp ((algebraMap (Polynomial L) Scalar).comp C)
def scalarCoordinate : ChartField := RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))
def chartCoordinate (infinity : Bool) (x : ChartField) : ChartField :=
  if infinity then x⁻¹ else x
def baseChart (s : Chart) : Subring ChartField :=
  Subring.closure (Set.range constants ∪
    {chartCoordinate s.1 RatFunc.X, chartCoordinate s.2 scalarCoordinate})
def frame (a b : ℕ) (s : Chart) : ChartField :=
  (if s.1 then RatFunc.X else 1)^a * (if s.2 then scalarCoordinate else 1)^b
theorem frame_scale (a b n : ℕ) (s : Chart) :
    frame (a*n) (b*n) s=(frame a b s)^n := by
  simp only [frame,pow_mul,mul_pow]
variable {E : Type*} [Field E] [Algebra ChartField E]
def Correction (a b : ℕ) (u : Chart → E) (c : E) : Prop :=
  ∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*(u s-c))
theorem finite_inclusion :
    baseChart (false,false) ≤ (algebraMap (Polynomial Scalar) ChartField).range := by
  apply Subring.closure_le.mpr
  intro x hx
  simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with ⟨c,rfl⟩ | rfl | rfl
  · exact ⟨C (algebraMap (Polynomial L) Scalar (C c)),RatFunc.algebraMap_C _⟩
  · exact ⟨Polynomial.X,RatFunc.algebraMap_X⟩
  · exact ⟨C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L))),RatFunc.algebraMap_C _⟩
theorem infinity_inclusion [DecidableEq ChartField] :
    baseChart (true,false) ≤ (algebraMap (Infinity Scalar) ChartField).range := by
  apply Subring.closure_le.mpr
  intro x hx
  simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with ⟨c,rfl⟩ | rfl | rfl
  · exact ⟨MonicChart.inftyRingEval Scalar (C (algebraMap (Polynomial L) Scalar (C c))),aeval_C _ _⟩
  · exact ⟨MonicChart.inftyRingEval Scalar Polynomial.X,MonicChart.mapped_X_infty⟩
  · exact ⟨MonicChart.inftyRingEval Scalar (C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))),
      aeval_C _ _⟩
theorem integral_of_inclusion (s : Chart) {R : Type*} [CommRing R] [Algebra R ChartField]
    [Algebra R E] [IsScalarTower R ChartField E] (inj : Function.Injective (algebraMap R ChartField))
    (fit : baseChart s ≤ (algebraMap R ChartField).range) {q : E}
    (integral : IsIntegral (baseChart s) q) : IsIntegral R q := by
  let j := algebraMap R ChartField
  let equiv : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b eq=>inj (congrArg Subtype.val eq),j.rangeRestrict_surjective⟩
  let lift : baseChart s →+* R := equiv.symm.toRingHom.comp (Subring.inclusion fit)
  have commute (x : baseChart s) : j (lift x)=(x:ChartField) :=
    congrArg Subtype.val (equiv.apply_symm_apply (Subring.inclusion fit x))
  let : Algebra (baseChart s) R := lift.toAlgebra
  let : IsScalarTower (baseChart s) R E := IsScalarTower.of_algebraMap_eq fun x=>by
    change algebraMap ChartField E (x:ChartField) = algebraMap R E (lift x)
    rw [IsScalarTower.algebraMap_apply R ChartField E,commute]
  exact integral.tower_top





















































































end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

-- merged module R6966ProofFarChart
section Merged_R6966ProofFarChart

section Merged_R6960MonicChartActual

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap abscissa_coeff_height)
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)





























































































end
end Lower6960.MonicChart

end Merged_R6960MonicChartActual

section Merged_R6960MonicChartFrobenius
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open RetainedCompression (Curve ordinate view view_y height heightCap)
open scoped Polynomial Lower6960.MonicChart
variable {E : Type*} [Field E]
    [Algebra ChartField E] [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) ChartField E]
variable [DecidableEq ChartField] [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) ChartField E]






















































end
end Lower6960.MonicChart

end Merged_R6960MonicChartFrobenius

section Merged_R6960MonicFourChartDescent
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicFourChartDescent
noncomputable section
open Polynomial
open K1_14 (L)
open MonicChart (ChartField Scalar Infinity)
open ChartSections (Chart)
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]






















































































end
end Lower6960.MonicFourChartDescent

end Merged_R6960MonicFourChartDescent

end Merged_R6966ProofFarChart
