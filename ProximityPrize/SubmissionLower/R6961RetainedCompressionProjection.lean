import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import ProximityPrize.SubmissionLower.KoalaRectQuotient
import Mathlib.RingTheory.Localization.Integer

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

namespace Lower6961.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation Seeds seedEmbedding graphEval atX)
open CurvatureSquares (Ordinate zView ordEval)
open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Polynomial nonZeroDivisors

abbrev RationalOrdinate := Polynomial (Polynomial FX)

abbrev incl := algebraMap (Polynomial L) FX

private def graph : Seeds →+* (Polynomial FX) := (K1_14.frobeniusGraph (F := FX) p).toRingHom

/-- The graph map is applied to the original rational coefficients. -/
def project (f : Equation) : RationalOrdinate := f.map graph

def intoFraction (P : Ordinate) : RationalOrdinate :=
  P.map ((mapRingHom incl).comp Bivariate.swap.toRingHom)

private theorem incl_inj : Function.Injective incl := IsFractionRing.injective (Polynomial L) FX

private theorem coeff_into (P : Ordinate) (i j : ℕ) :
    ((intoFraction P).coeff i).coeff j = incl ((Bivariate.swap (P.coeff i)).coeff j) := by
  simp [intoFraction]

private theorem into_degree (P : Ordinate) : (intoFraction P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective ((Polynomial.map_injective incl incl_inj).comp Bivariate.swap.injective) P

private theorem degree_project (f : Equation) (small : axisDegree f 0<p) :
    (project f).natDegree=f.natDegree := by
  by_cases nz : f=0
  · simp [nz,project]
  apply natDegree_map_of_leadingCoeff_ne_zero graph
  exact K1_14.frobeniusGraph_ne_zero p (by decide) f.leadingCoeff
    (leadingCoeff_ne_zero.mpr nz) (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)

private theorem projected_coeff (f : Equation) (i : ℕ) :
    ((project f).coeff i).natDegree≤axisDegree f 0+p*axisDegree f 1 := by
  rw [project, coeff_map]
  exact K1_14.frobeniusGraph_degree p _ _ (f.coeff i)
    ((axisDegree_le_iff f 0 _).mp le_rfl i) ((axisDegree_le_iff f 1 _).mp le_rfl i)

private theorem graph_eval (z : K) :
    (evalRingHom (seedEmbedding z)).comp graph=graphEval z := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [graph, K1_14.frobeniusGraph, graphEval]
  · intro i
    fin_cases i <;> simp [graph, K1_14.frobeniusGraph, graphEval]

theorem specialize_project (f : Equation) (z : K) :
    (project f).map (evalRingHom (seedEmbedding z))=f.map (graphEval z) := by
  rw [project, Polynomial.map_map, graph_eval]

/-- Clear denominators in the abscissa without increasing either the ordinate
or scalar degree. The identity holds over the original fraction field. -/
theorem clear_abscissa (G : RationalOrdinate) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ intoFraction P=C (C (incl d))*G := by
  classical
  let S := G.support.sigma (fun i => (G.coeff i).support)
  let coeffs (x : Σ _ : ℕ, ℕ) : FX := (G.coeff x.1).coeff x.2
  let den := IsLocalization.commonDenom (nonZeroDivisors (Polynomial L)) S coeffs
  let ints := IsLocalization.integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs
  let value (i j : ℕ) : (Polynomial L) := if h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S then ints ⟨⟨i,j⟩,h⟩ else 0
  let raw : Ordinate :=
    ∑ i∈G.support, monomial i (∑ j∈(G.coeff i).support, monomial j (value i j))
  let P := raw.map Bivariate.swap.toRingHom
  have degree (i j : ℕ) : (raw.coeff i).coeff j = value i j := by
    by_cases hi : i∈G.support
    · by_cases hj : j∈(G.coeff i).support
      · simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj]
      · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hj (Finset.mem_sigma.mp m).2
        simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj, value, hnot]
    · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hi (Finset.mem_sigma.mp m).1
      simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
        hi, value, hnot]
  refine ⟨den,P,nonZeroDivisors.coe_ne_zero den,?_⟩
  ext i j
  rw [coeff_into,show P.coeff i=Bivariate.swap (raw.coeff i) from coeff_map ..,
    Bivariate.swap_swap_apply, degree, coeff_C_mul, coeff_C_mul]
  by_cases h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S
  · have prop := IsLocalization.map_integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs ⟨⟨i,j⟩,h⟩
    change incl (ints ⟨⟨i,j⟩,h⟩)=(den : (Polynomial L)) • (G.coeff i).coeff j at prop
    rw [Algebra.smul_def] at prop
    simpa only [value, dite_eq_left h] using prop
  · have zero : (G.coeff i).coeff j=0 := by
      by_contra ne
      have hj := mem_support_iff.mpr ne
      exact h (Finset.mem_sigma.mpr ⟨mem_support_iff.mpr (fun z => by simpa [z] using ne),hj⟩)
    simp [value, h,zero]

/-- A scalar specialization of a cleared ordinate polynomial, with the
abscissa polynomial kept as its coefficient ring. -/
def specialize (P : Ordinate) (z : L) : Polynomial (Polynomial L) :=
  P.map (mapRingHom (evalRingHom z))

theorem eval_swap {F : Type*} [Field F] (Q : Polynomial (Polynomial F)) (z : F) :
    (Bivariate.swap Q).eval (C z) = Q.map (evalRingHom z) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ, Polynomial.map_add]
  | monomial n a =>
    rw [Bivariate.swap_monomial, eval_mul, eval_C, eval_map_apply, map_monomial,
      coe_evalRingHom, C_mul_X_pow_eq_monomial]

theorem specialize_into (P : Ordinate) (z : L) :
    (intoFraction P).map (evalRingHom (incl (C z)))=(specialize P z).map incl := by
  ext i
  simp only [intoFraction, specialize, coeff_map, RingHom.comp_apply, coe_mapRingHom,
    coe_evalRingHom, eval_map]
  change (Bivariate.swap (P.coeff i)).eval₂ incl (incl (C z)) =
    incl ((P.coeff i).map (evalRingHom z))
  have mapped := Polynomial.hom_eval₂ (p := Bivariate.swap (P.coeff i))
    (f := RingHom.id (Polynomial L)) (g := incl) (C z)
  rw [RingHom.comp_id] at mapped
  rw [← mapped]
  exact congrArg incl (eval_swap (P.coeff i) z)

private theorem z_coeff (P : Ordinate) (i j : ℕ) :
    ((zView P).coeff j).coeff i = (Bivariate.swap (P.coeff i)).coeff j := by
  change ((Bivariate.swap (P.map Bivariate.swap.toRingHom)).coeff j).coeff i =
    (Bivariate.swap (P.coeff i)).coeff j
  rw [CurvatureSquares.coeff_swap, coeff_map]
  rfl

/-- An integral projected polynomial carries the terminal equation's exact
ordinate degree and the shared scalar-degree cap. -/
theorem integral_project (f : Equation) (nz : f≠0) (small : axisDegree f 0<p) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ z : K, (specialize P (algebraMap K L z)).map incl = C (incl d)*f.map (graphEval z) := by
  obtain ⟨d,P,hd,eq⟩ := clear_abscissa (project f)
  have dn : incl d≠0 := (map_ne_zero_iff incl incl_inj).mpr hd
  have pn : project f≠0 := by
    intro z
    have hl := degree_project f small
    unfold project at z
    have killed := congrArg (fun V : RationalOrdinate => V.coeff f.natDegree) z
    have hp : graph f.leadingCoeff≠0 :=
      K1_14.frobeniusGraph_ne_zero p (by decide) _ (leadingCoeff_ne_zero.mpr nz)
        (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)
    exact hp (by simpa only [coeff_map,coeff_natDegree,coeff_zero] using killed)
  refine ⟨d,P,hd,fun h => ?_,?_,?_,?_⟩
  · rw [h,intoFraction,Polynomial.map_zero] at eq
    exact (mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr dn)) pn) eq.symm
  · rw [← into_degree P,eq,natDegree_C_mul (C_ne_zero.mpr dn),degree_project f small]
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [z_coeff,coeff_zero]
    apply incl_inj
    rw [← coeff_into,eq,coeff_C_mul,coeff_C_mul,coeff_eq_zero_of_natDegree_lt
      ((projected_coeff f i).trans_lt hj),mul_zero,map_zero]
  · intro z
    have label : incl (C (algebraMap K L z))=seedEmbedding z := rfl
    rw [← specialize_into, label, eq, Polynomial.map_mul, Polynomial.map_C, specialize_project]
    simp only [coe_evalRingHom, eval_C]

#print axioms integral_project
end
end Lower6961.RetainedCompression
