import ProximityPrize.SubmissionLower.R6960RetainedChartGluing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedLineRestriction
open MonicFourChartDescent ChartSections MonicChart RetainedChartGluing
open ChartGlobalTests (frame_ne)
open MonicChartLaurent (overlapRing)
open MonicChartProbes (planeMap planeMap_injective)
open RetainedCompression (Curve ordinate view height heightCap wordDegree)
open Polynomial
open K1_14 (L)

/-- Global equation of one abscissa fibre and one scalar fibre. -/
def lines (x z : L) : ChartField :=
  (RatFunc.X-constants x)*(scalarCoordinate-constants z)

private theorem lines_ne (x z : L) : lines x z≠0 := by
  let m := planeMap (false,false)
  have a : (Polynomial.X (R:=(Polynomial L)))-C (C x)≠0 := X_sub_C_ne_zero _
  have b : (C (Polynomial.X (R:=L)) : (Polynomial (Polynomial L)))-C (C z)≠0 := by
    rw [←map_sub]; exact C_ne_zero.mpr (X_sub_C_ne_zero _)
  have good := (map_ne_zero_iff m (planeMap_injective _)).mpr (mul_ne_zero a b)
  simpa only [m,map_mul,map_sub,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_scalar,
    MonicChartProbes.planeMap_abscissa,chartCoordinate,Bool.false_eq_true,ite_false,lines] using good

private theorem linear_factor (A : Subring ChartField) (b : Bool) (v c : ChartField) (nz : v≠0)
    (var : chartCoordinate b v∈A) (constant : c∈A) :
    (v-c)/(if b then v else 1)∈A := by
  cases b with
  | false => simpa [chartCoordinate] using A.sub_mem var constant
  | true =>
    change (v-c)/v∈A
    rw [sub_div,div_self nz,div_eq_mul_inv]
    exact A.sub_mem A.one_mem (A.mul_mem constant var)

theorem local_equation (x z : L) (s : Chart) : lines x z / frame 1 1 s∈baseChart s := by
  have constants_mem (c : L) : constants c∈baseChart s := Subring.subset_closure (Or.inl ⟨c,rfl⟩)
  have Xmem : chartCoordinate s.1 RatFunc.X∈baseChart s := Subring.subset_closure (Or.inr (Or.inl rfl))
  have Zmem : chartCoordinate s.2 scalarCoordinate∈baseChart s := Subring.subset_closure (Or.inr (Or.inr rfl))
  rw [lines,frame,pow_one,pow_one,←div_mul_div_comm]
  exact (baseChart s).mul_mem (linear_factor _ _ _ _ RatFunc.X_ne_zero Xmem (constants_mem x))
    (linear_factor _ _ _ _ ChartOverlapTests.scalar_ne Zmem (constants_mem z))

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- If an untwisted transition class splits modulo the equation of the two fibres, it
already splits on the normalized surface. Divisibility takes place in the actual
normalized overlaps. The representatives on each chart may be chosen independently. -/
theorem split_of_split_on_lines (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (g : Chart→Chart→E) (add : ∀ s t r, g s t+g t r=g s r)
    (v : Chart→E) (localV : ∀ s, IsIntegral (baseChart s) (v s))
    (restricted : ∀ s t, ∃ r : E, IsIntegral (overlapRing s t) r ∧
      g s t-(v s-v t)=algebraMap ChartField E (lines x z / frame 1 1 s)*r) :
    ∃ w : Chart→E, (∀ s,IsIntegral (baseChart s) (w s)) ∧ ∀ s t,g s t=w s-w t := by
  let ι:=algebraMap ChartField E
  let P:=ι (lines x z)
  have pn : P≠0 := (map_ne_zero_iff ι ι.injective).mpr (lines_ne x z)
  let h (s t:Chart):=(g s t-(v s-v t))/P
  have coc (s t r) : h s t+h t r=h s r := by
    dsimp [h]
    rw [←add_div]
    congr 1
    linear_combination add s t r
  have twist (s t) : IsIntegral (overlapRing s t) (ι (frame 1 1 s)*h s t) := by
    obtain ⟨r,hr,eq⟩:=restricted s t
    have nz := (map_ne_zero_iff ι ι.injective).mpr (frame_ne 1 1 s)
    have recover : ι (frame 1 1 s)*h s t=r := by
      dsimp only [h]; rw [eq,map_div₀]
      change ι (frame 1 1 s)*(P/ι (frame 1 1 s)*r/P)=r
      field_simp
    rwa [recover]
  obtain ⟨w,localW,diff⟩:=split_cocycle f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
  refine ⟨fun s=>v s+P*w s,fun s=>(localV s).add ?_,fun s t=>?_⟩
  · have integral : IsIntegral (baseChart s) (ι (lines x z/frame 1 1 s)) :=
      isIntegral_algebraMap (x:=(⟨_, local_equation x z s⟩ : baseChart s))
    have eq : ι (lines x z / frame 1 1 s)*(ι (frame 1 1 s)*w s)=P*w s := by
      rw [map_div₀,←mul_assoc,div_mul_cancel₀ _ ((map_ne_zero_iff ι ι.injective).mpr (frame_ne _ _ _))]
    exact eq ▸ integral.mul (localW s)
  · have eq := (div_eq_iff pn).mp (diff s t)
    linear_combination eq

#print axioms split_of_split_on_lines
end Lower6960.RetainedLineRestriction
