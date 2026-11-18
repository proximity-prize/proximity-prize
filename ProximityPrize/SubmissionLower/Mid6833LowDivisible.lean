/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The normalization and affine leading-degree cleanup are due to
the credited 68.32 release and 69.69 project. Recovery uses both actual words. -/
import ProximityPrize.SubmissionLower.Mid6833FixedPoles
import ProximityPrize.SubmissionLower.Mid6833InfinityBounds
import ProximityPrize.SubmissionLower.Mid6833FiniteDivisor
namespace ProximityPrize.SubmissionLower.Genuine6969
open Koala6831Comparison K6969Global Koala6831Separation Koala6831Moving Koala6831BenchmarkPrimitive
open Koala6831BenchmarkField (prime)
open Frontier6969.GenuineMoving Polynomial Finset
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K I : Type} [Field K] [Fintype I]

theorem nonzero_at_agreement (x : I ↪ K) (s : K →+* K) (fixed : ∀i,s (x i)=x i)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x s U E P q) (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (ker : CommonKernel s N) (g : K) (hg : g∈E) (i : I) (hi : i∈agreementSet x U P g) :
    N.d₀.eval (x i)≠0 := by
  intro pole
  have other := (fixed_pole_equiv s N ker (x i) (fixed i)).mp pole
  have ok := Koala6831BenchmarkResidual.good_node_identity
    (fun z => Finset.disjoint_left.mp (h.good g hg).2 hi z)
  have ne := primitive_active_at_good_node q h.primitive (x i) _ _ ok
  rw [←map_eval_regroup,←map_eval_regroup,N.first_eq,N.second_eq] at ne
  simpa only [map_mul,map_neg,MvPolynomial.map_C,Polynomial.coe_evalRingHom,pole,other,
    MvPolynomial.C_0,zero_mul,neg_zero,ne_self_iff_false,or_self] using ne

/-- With a divisible determinant, normalized low-degree entries reconstruct
both true coordinates on the complete agreement set. Thus a genuinely bad
family lies in the explicitly bounded normalization/leading/pole discards. -/
theorem low_divisible (x : I ↪ K) (s : K →+* K) (fixed : ∀i,s (x i)=x i)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x s U E P q) (bad : Bad x U E P)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (ker : CommonKernel s N)
    (short : primitiveExcess 131071 q≤12136)
    (det : N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0)
    (small : (N.A 0*N.C 1-N.A 1*N.C 0).natDegree≤131071+N.d₀.natDegree+pairDegree N.A) :
    E.card ≤ Fintype.card I+2+(prime+2)*primitiveExcess 131071 q := by
  classical
  let δ := primitiveExcess 131071 q
  let nodes := univ \ badNodes x s U q
  have good (i) (hi:i∈nodes) := Koala6831BenchmarkResidual.good_node_identity (mem_sdiff.mp hi).2
  have gd (i) (hi:i∈nodes) : q.atNode (MvPolynomial.C (x i))
      (Koala6831SeparationFactors.affine 0 (U 0 i) (U 1 i))
      (Koala6831SeparationFactors.affine 1 (s (U 0 i)) (s (U 1 i)))=0 := by
    simpa only [Koala6831SeparationFactors.affine,mul_comm] using good i hi
  obtain ⟨S,sub,sz,v,T,values,props⟩ := normalForm_exists_retained_normalized_words N s prime
    (by unfold prime; omega) nodes x (U 0) (U 1) gd E P h.selection.degree_le (fun g hg => (h.good g hg).1)
  obtain ⟨R,ss,sz2,leading⟩ := Frontier6969.Moving.leading_regular S N.A N.A_coprime
  have smallR : R.card≤N.d₀.natDegree := by
    apply fixed_divisor_exceptions _ N.d₀_ne _ N.A_coprime
    intro g hg reg
    have hs := ss hg
    have he := sub hs
    obtain ⟨_,row,matchAt⟩ := props g hs
    apply bad g he
    apply quotient_reconstructs x U (agreementSet x U P g) N.d₀ N.d₀_ne (T g) N.A N.C 131071
      (nonzero_at_agreement x s fixed U E P q h N ker g he) _ (separate_divisors _ _ _ _ _ g reg det row)
      (infinity_small N g (P g) (T g) (h.selection.degree_le g he) (leading g hg).1 (leading g hg).2 row small)
    intro i hi j
    have inside : i∈nodes := mem_sdiff.mpr ⟨mem_univ _,fun z => disjoint_left.mp (h.good g he).2 hi z⟩
    rw [matchAt i inside (eval_eq_of_mem_agreementSet hi)]
    fin_cases j
    · exact (values i inside).1
    · exact (values i inside).2
  have dd := N.first_degree
  have nn := (card_le_card (subset_univ nodes)).trans_eq card_univ
  dsimp [δ] at *
  unfold prime at *
  omega

#print axioms nonzero_at_agreement
#print axioms low_divisible
end
end ProximityPrize.SubmissionLower.Genuine6969
