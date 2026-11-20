/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833TwistedRows
namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Moving (affineDenominator)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open K6969Global (RetainedComparison)
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive (Received SelectionMap badNodes agreementSet eval_eq_of_mem_agreementSet)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [Fintype I]

def solves (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (T : K[X]) :=
  ∀ j, N.d₁ * (N.A j).map σ * T.map σ - N.d₀.map σ * N.B j * T = offset σ N j

private theorem unique_value (A : Fin 2 → K[X]) (cp : IsCoprime (A 0) (A 1)) (x a b : K)
    (val : ∀ j, a * (A j).eval x = b * (A j).eval x) : a=b := by
  obtain ⟨u,v,bez⟩ := cp
  have bz := congrArg (Polynomial.eval x) bez
  simp only [eval_add,eval_mul,eval_one] at bz
  by_contra ne
  have zero (j) : (A j).eval x = 0 := (mul_eq_zero.mp
    (show (a-b)*(A j).eval x=0 by linear_combination val j)).resolve_left (sub_ne_zero.mpr ne)
  simp only [zero,mul_zero,add_zero] at bz
  exact zero_ne_one bz

/-- Both receiver coefficients constrain each normalized polynomial, even when the
specialized equation for the chosen seed alone would lose one of them. -/
theorem retained_solutions (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (short : primitiveExcess 131071 q ≤ 12136) :
    ∃ S ⊆ E, E.card ≤ S.card+(Fintype.card I+1+(prime+1)*primitiveExcess 131071 q) ∧
      ∃ (T : K → K[X]) (v : I → K), ∀ g∈S,
        (T g).natDegree ≤ 131071+primitiveExcess 131071 q ∧
        N.d₀*P g + affineDenominator (N.C 0) (N.C 1) g =
          affineDenominator (N.A 0) (N.A 1) g * T g ∧
        (∀ i∈agreementSet x U P g, (T g).eval (x i)=v i) ∧ solves σ N (T g) := by
  classical
  let δ := primitiveExcess 131071 q
  let nodes := univ \ badNodes x σ U q
  have good (i) (hi:i∈nodes) : q.atNode (MvPolynomial.C (x i))
      (Koala6831SeparationFactors.affine 0 (U 0 i) (U 1 i))
      (Koala6831SeparationFactors.affine 1 (σ (U 0 i)) (σ (U 1 i)))=0 := by
    have orig := Koala6831BenchmarkResidual.good_node_identity (mem_sdiff.mp hi).2
    simpa only [Koala6831SeparationFactors.affine,mul_comm] using orig
  obtain ⟨S,sub,card,v,T,hv,props⟩ := Koala6831Moving.normalForm_exists_retained_normalized_words
    N σ prime (by unfold prime; omega) nodes x (U 0) (U 1) good E P h.selection.degree_le
    (fun g hg => (h.good g hg).1)
  have cn := card_le_card (Finset.subset_univ nodes)
  rw [card_univ] at cn
  refine ⟨S,sub,by omega,T,v,?_⟩
  intro g hg
  let support := agreementSet x U P g
  have inc (i) (hi:i∈support) : i∈nodes := mem_sdiff.mpr ⟨mem_univ _,
    fun bad => disjoint_left.mp (h.good g (sub hg)).2 hi bad⟩
  have fits (i) (hi:i∈support) := (props g hg).2.2 i (inc i hi)
    (eval_eq_of_mem_agreementSet (x:=x) (received:=U) (selected:=P) (g:=g) hi)
  refine ⟨(props g hg).1,(props g hg).2.1,fits,?_⟩
  intro j
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i:support => x i.val)
    (x.injective.comp Subtype.val_injective)
  · intro i
    obtain ⟨t,left,eq⟩ := node_equations σ N (x i.val) (fixed i.val) (fun j=>U j i.val) (good _ (inc _ i.property))
    have vv : ∀ k, t*(N.A k).eval (x i.val) = v i.val * (N.A k).eval (x i.val) := by
      intro k
      rw [←left k,mul_comm (v i.val)]
      fin_cases k
      · exact (hv _ (inc _ i.property)).1
      · exact (hv _ (inc _ i.property)).2
    have same := unique_value _ N.A_coprime (x i.val) t (v i.val) vv
    have mp := eval_map_apply (p:=T g) σ (x i.val)
    rw [fixed, fits _ i.property] at mp
    simp only [eval_sub,eval_mul,mp,fits _ i.property,←same]
    exact eq j
  · rw [Fintype.card_coe]
    have sz : 179740≤support.card := h.selection.agreement g (sub hg)
    have da : (N.A j).natDegree ≤ pairDegree N.A := by fin_cases j <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have db : (N.B j).natDegree ≤ pairDegree N.B := by fin_cases j <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have dc : (N.C j).natDegree ≤ pairDegree N.C := by fin_cases j <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have dd : (N.D j).natDegree ≤ pairDegree N.D := by fin_cases j <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have d0 := N.first_degree
    have d1 := N.second_degree
    have c := N.left_degree
    have d := N.right_degree
    have dt := (props g hg).1
    unfold offset
    have l₁ := @natDegree_mul_le _ _ N.d₁ ((N.A j).map σ)
    have l₂ := @natDegree_mul_le _ _ (N.d₁*(N.A j).map σ) ((T g).map σ)
    have r₁ := @natDegree_mul_le _ _ (N.d₀.map σ) (N.B j)
    have r₂ := @natDegree_mul_le _ _ (N.d₀.map σ*N.B j) (T g)
    have m₁ := natDegree_map_le (p:=N.A j) (f:=σ)
    have m₂ := natDegree_map_le (p:=N.d₀) (f:=σ)
    have m₃ := natDegree_map_le (p:=T g) (f:=σ)
    have ms := natDegree_sub_le (N.d₁*(N.A j).map σ*(T g).map σ) (N.d₀.map σ*N.B j*T g)
    have os := natDegree_add_le (N.d₁*(N.C j).map σ) (N.d₀.map σ*N.D j)
    have ol := @natDegree_mul_le _ _ N.d₁ ((N.C j).map σ)
    have orr := @natDegree_mul_le _ _ (N.d₀.map σ) (N.D j)
    have mc := natDegree_map_le (p:=N.C j) (f:=σ)
    omega

theorem homogeneous_difference (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) {T R : K[X]} (ht : solves σ N T) (hr : solves σ N R) (j : Fin 2) :
    (N.d₁*(N.A j).map σ)*(T-R).map σ=(N.d₀.map σ*N.B j)*(T-R) := by
  rw [Polynomial.map_sub]
  linear_combination ht j - hr j

#print axioms retained_solutions
#print axioms homogeneous_difference
end
end Frontier6969.GenuineMoving
