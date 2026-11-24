import ProximityPrize.SubmissionLower.R6960CollisionMarkedPlaneOverlap
import ProximityPrize.SubmissionLower.R6960CollisionMarkedLineTrace
import ProximityPrize.SubmissionLower.R6960CollisionMarkedGlobalSum
set_option synthInstance.maxHeartbeats 200000

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus LineEuler CollisionTame
open Polynomial LaurentPolynomial Module Algebra Matrix Finset
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial Matrix

private theorem laurent_nat_coeff {k:Type} [CommRing k] (P:(Polynomial k)) (n:ℕ) :
    P.toLaurent.coeff (n:ℤ)=P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ _

/-- The abscissa overlap unit has scalar degree zero. Reflecting its
coefficient sequence therefore cannot increase the seed degree. -/
theorem plane_overlap_height_le {k:Type} [Field k] (A B:(Polynomial (Polynomial k))) (an:A≠0)
    (u:k) (un:u≠0) (m:ℤ)
    (glue : A.toLaurent=LaurentPolynomial.C (Polynomial.C u)*T m*invert B.toLaurent) :
    CurvatureSquares.height B≤CurvatureSquares.height A := by
  obtain ⟨_,bd⟩ := plane_overlap_degree_caps A B an u un m glue
  have cdeg (n:ℕ) : (B.coeff n).natDegree≤CurvatureSquares.height A := by
    by_cases h : (n:ℤ)≤m
    · let j := (m-(n:ℤ)).toNat
      have js : (j:ℤ)=m-(n:ℤ) := Int.toNat_of_nonneg (sub_nonneg.mpr h)
      have r := congrArg (fun P:LaurentPolynomial (Polynomial k)=>P.coeff (j:ℤ)) glue
      rw [laurent_nat_coeff,←single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff ((j:ℤ)-m) (by intro v _; omega),
        invert_apply,show -((j:ℤ)-m)=(n:ℤ) by omega,laurent_nat_coeff] at r
      have eq := congrArg Polynomial.natDegree r
      rw [natDegree_C_mul_of_isUnit (IsUnit.mk0 u un)] at eq
      exact eq ▸ CurvatureSquares.coeff_height A j
    · have s : B.natDegree<n := by omega
      rw [coeff_eq_zero_of_natDegree_lt s,natDegree_zero]
      exact Nat.zero_le _
  change (Bivariate.swap B).natDegree≤CurvatureSquares.height A
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n high
  apply Polynomial.ext
  intro i
  rw [CurvatureSquares.coeff_swap,coeff_eq_zero_of_natDegree_lt ((cdeg i).trans_lt high),coeff_zero]

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

local instance measuredCrossRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

theorem line_principal_discriminant (j b:Bool) :
    ∃ δ:Plane L, δ≠0 ∧ lineDiscriminant (E:=E) j b=Ideal.span {δ} := by
  let A := Plane L
  let F := FractionRing A
  let : Algebra A E := linePlaneAlgebra j b
  let : Algebra F E := lineFractionAlgebra j b
  let : SMul A F := (inferInstance : Algebra A F).toSMul
  let : IsScalarTower A F E := linePlaneTower j b
  let : FiniteDimensional F E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable F E := lineFraction_separable j b
  have hn := normalizationDiscriminant_ne_bot (A:=A) (E:=E) (F:=F)
  obtain ⟨δ,hδ⟩ := plane_discriminant_principal (k:=L) (E:=E)
  refine ⟨δ,?_,hδ⟩
  intro zero
  apply hn
  rw [hδ,zero]
  change Ideal.span ({0}:Set A)=⊥
  exact Ideal.span_singleton_zero

/-- Read the degree of each original plane generator in one direction
from the actual reduced crossing and the very transition measured in
the native surface budget. -/
theorem original_line_degree_cap (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) true))
    (s:ℕ) (measure:(transition E j (atCoord j x z) (by cases j <;> assumption) bf bi).det.degree=
      ((-(s:ℤ):ℤ):WithBot ℤ))
    (δf δi:Plane L) (nf:δf≠0)
    (df:lineDiscriminant (E:=E) j false=Ideal.span {δf})
    (di:lineDiscriminant (E:=E) j true=Ideal.span {δi}) :
    (CurvatureSquares.height δf≤2*s ∧ CurvatureSquares.height δi≤2*s) ∧
    ∃ u:L,u≠0 ∧ (Bivariate.swap δf).toLaurent=
      LaurentPolynomial.C (Polynomial.C u)*T (2*(s:ℤ))*invert (Bivariate.swap δi).toLaurent := by
  let c := atCoord j x z
  have nc : c≠0 := by cases j <;> assumption
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j false c) := lineChartAlgebra j false c nc
  let : Algebra (Polynomial L) (lineChartRing (E:=E) j true c) := lineChartAlgebra j true c nc
  let f := (traceMatrix (Polynomial L) (bf.map (lineChartLinearEquiv (E:=E) j false c nc))).det
  let i := (traceMatrix (Polynomial L) (bi.map (lineChartLinearEquiv (E:=E) j true c nc))).det
  let A := Bivariate.swap δf
  let B := Bivariate.swap δi
  have an : A≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have af' : Associated f (δf.eval (Polynomial.C c)) :=
    selected_line_trace_associated j false c nc bf δf (by intro _; exact df)
  have ai' : Associated i (δi.eval (Polynomial.C c)) :=
    selected_line_trace_associated j true c nc bi δi (by intro _; exact di)
  have hswap (δ:Plane L) : δ.eval (Polynomial.C c)=(Bivariate.swap δ).map (evalRingHom c) := by
    simpa only [Bivariate.swap_swap_apply] using RetainedCompression.eval_swap (Bivariate.swap δ) c
  have af : Associated f (A.map (evalRingHom c)) := hswap δf ▸ af'
  have ai : Associated i (B.map (evalRingHom c)) := hswap δi ▸ ai'
  have fn : f≠0 := selected_line_trace_nonzero j x z nx nz p small bf
  have good : A.map (evalRingHom c)≠0 := fun z=>fn (zero_dvd_iff.mp (z ▸ af.dvd'))
  obtain ⟨u,m,un,glue⟩ := line_overlap_unit j δf δi df di
  let G := (transition E j c nc bf bi).det
  have unit : IsUnit G := (Matrix.isUnit_iff_isUnit_det _).mp
    (freeTransition_unit bf bi (nativeMap E j c false) (nativeMap E j c true)
      (native_localization E j c nc false) (native_localization E j c nc true))
  have trace : invert i.toLaurent=G^2*f.toLaurent := selected_line_trace_transition j c nc bf bi
  have caps := plane_degree_from_line_transition A B an u un m glue c good f i af ai G unit trace s measure
  obtain ⟨d,dd,eq⟩ := overlap_transition_exponent A B u un m glue (evalRingHom c)
    good f i af ai G unit trace
  have de := WithBot.coe_injective (dd.symm.trans measure)
  have mx : m=2*(s:ℤ) := by omega
  exact ⟨caps,u,un,mx ▸ glue⟩

/-- The two selected deficits bound the actual finite discriminant's
bidegree and the one reciprocal exceptional-seed polynomial. -/
theorem actual_measured_discriminants (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p)
    {m n:ℕ} (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false))
    (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false))
    (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true))
    (s t:ℕ)
    (ds:(transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ))
    (dt:(transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ)) :
    ∃ δf δi:Plane L, δf≠0 ∧ δi≠0 ∧
      axisDiscriminant (E:=E) false=Ideal.span {δf} ∧
      axisDiscriminant (E:=E) true=Ideal.span {δi} ∧
      CurvatureSquares.height δf≤2*s ∧ δf.natDegree≤2*t ∧
      ((Bivariate.swap δi).trailingCoeff).natDegree≤2*t := by
  classical
  obtain ⟨δf,nf,df⟩ := line_principal_discriminant (E:=E) true false
  obtain ⟨δi,ni,di⟩ := line_principal_discriminant (E:=E) true true
  obtain ⟨δt,_,dti⟩ := line_principal_discriminant (E:=E) false true
  have swap : lineDiscriminant (E:=E) false false=Ideal.span {Bivariate.swap δf} := by
    rw [←line_discriminant_swap,df,Ideal.map_span,Set.image_singleton]
    rfl
  have xcap := (original_line_degree_cap true x z nx nz p small zf zi s ds δf δi nf df di).1.1
  have nzswap : Bivariate.swap δf≠0 :=
    (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have zcap := (original_line_degree_cap false x z nx nz p small xf xi t dt _ δt nzswap swap dti).1.1
  change (Bivariate.swap (Bivariate.swap δf)).natDegree≤2*t at zcap
  rw [Bivariate.swap_swap_apply] at zcap
  obtain ⟨u,l,un,glue⟩ := line_overlap_unit true δf δi df di
  have zi_le := plane_overlap_height_le _ _ nzswap u un l glue
  change (Bivariate.swap (Bivariate.swap δi)).natDegree≤(Bivariate.swap (Bivariate.swap δf)).natDegree at zi_le
  rw [Bivariate.swap_swap_apply,Bivariate.swap_swap_apply] at zi_le
  have cap := (boundary_seed_polynomial δi ni).2.1
  exact ⟨δf,δi,nf,ni,(line_discriminant_axis false).symm.trans df,
    (line_discriminant_axis true).symm.trans di,xcap,zcap,(cap.trans zi_le).trans zcap⟩

#print axioms actual_measured_discriminants
end
end Lower6960.CollisionMarked
