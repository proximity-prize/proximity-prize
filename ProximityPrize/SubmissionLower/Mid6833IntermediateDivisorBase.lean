/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Derived from the genuine-seed common-divisor proof and the earlier high-degree list bridge.
Bome2017's benchmark proof credits Lucieno and BitWonka. This module keeps the stronger physical agreement. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineResidual
namespace ProximityPrize.SubmissionLower.Genuine6969.IntermediateDivisor
open Koala6831Comparison K6969Global Koala6831Separation Koala6831Moving
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes)
open Koala6831BenchmarkField (prime)
open Frontier6969.GenuineMoving Polynomial Finset ReedSolomon ProximityPrize.Benchmark
open scoped Polynomial Classical
noncomputable section
local instance mid6833Local_IntermediateDivisorBase_11  : DecidableEq KoalaBear.Ext6 := Classical.decEq _
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

def ScalarAt (d A C : ℕ) : Prop := ∀ (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6),
  (closePolynomialSet x u (d+1) A).ncard ≤ C

private theorem high_cap {d A C : ℕ} (ha : d+1≤A) (cap : ScalarAt d A C)
    (x : Fin 262144 ↪ KoalaBear.Ext6) (E : Finset KoalaBear.Ext6)
    (S : KoalaBear.Ext6 → Finset (Fin 262144)) (ha' : ∀g∈E, A≤(S g).card)
    (T : E ↪ KoalaBear.Ext6[X]) (word : Fin 262144 → KoalaBear.Ext6)
    (fits : ∀ g : E, (T g).natDegree≤d ∧ ∀i∈S g,(T g).eval (x i)=word i) : E.card≤C := by
  classical
  let L := closePolynomialSet x word (d+1) A
  have hf : L.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x word ha).1
  have sub : (univ.map T) ⊆ hf.toFinset := by
    intro z hz
    obtain ⟨g,_,rfl⟩ := mem_map.mp hz
    apply hf.mem_toFinset.mpr
    refine ⟨(Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (fits g).1)),(ha' _ g.property).trans (card_le_card ?_)⟩
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(fits g).2 i hi⟩
  have bound := cap x word
  change L.ncard ≤ C at bound
  rw [Set.ncard_eq_toFinset_card _ hf] at bound
  simpa using (card_le_card sub).trans bound

theorem effective_at {A C B k : ℕ} (ha : 131071+k+1≤A) (cap : ScalarAt (131071+k) A C)
    (allowance : C+431289073806690≤B)
    (U : Received F IRSProfile.Index) (E : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (SeedRing F)) (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (difficulty : Difficult U E P q N) (agree : ∀g∈E,A≤(agreementSet Dmn U P g).card)
    (G : F[X]) (ng : G≠0) (divD : G∣N.d₀) (divM : G∣det N)
    (height : N.d₀.natDegree≤pairDegree N.A+G.natDegree+k) :
    E.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤B := by
  have short : primitiveExcess 131071 q ≤ 12136 := Nat.le_of_lt_succ difficulty.short
  have ker := difficulty.kernel
  have nondiv := difficulty.finiteFailure
  have small := difficulty.low
  have h := difficulty.actual
  classical
  let x := Dmn
  let fixed := Koala6831BenchmarkField.domain_fixed
  obtain ⟨S,sub,c1,T,v,fit⟩ := retained_solutions x σ fixed U E P q h N short
  obtain ⟨R,rs,c2,lead⟩ := Frontier6969.Moving.leading_regular S N.A N.A_coprime
  let regularSeeds := R.filter (fun g => IsCoprime G (affineDenominator (N.A 0) (N.A 1) g))
  have zr : regularSeeds⊆R := filter_subset _ _
  have reg (g) (hg:g∈regularSeeds) : IsCoprime G (affineDenominator (N.A 0) (N.A 1) g) := (mem_filter.mp hg).2
  have exc : (R\regularSeeds).card≤G.natDegree := by
    apply fixed_divisor_exceptions G ng N.A N.A_coprime
    intro g hg yes
    exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,yes⟩)
  have parts := card_sdiff_add_card_eq_card zr
  have bound : regularSeeds.card≤C := by
    by_cases z : regularSeeds.Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp z]
    obtain ⟨r,hr⟩ := z
    have es (g) (hg:g∈regularSeeds) := rs (zr hg)
    have ok (g) (hg:g∈regularSeeds) := (fit g (es g hg)).2.1
    have low (g) (hg:g∈regularSeeds) := infinity_small N g (P g) (T g) (h.selection.degree_le g (sub (es g hg)))
      (lead g (zr hg)).1 (lead g (zr hg)).2 (ok g hg) small
    have src (g : regularSeeds) := difference_divisor N G ng divD divM g r (P g) (P r) (T g) (T r)
      (reg g g.property) (reg r hr) (ok g g.property) (ok r hr) (low g g.property) (low r hr)
    choose V eq deg using src
    have tinj := Frontier6969.Moving.injective regularSeeds N.d₀ (N.A 0) (N.A 1) (N.C 0) (N.C 1) P T nondiv ok
    have inj : Function.Injective V := by
      intro g k he
      apply tinj
      have same : T g-T r=T k-T r := by rw [eq g,eq k,he]
      exact sub_left_inj.mp same
    apply high_cap ha cap x regularSeeds (agreementSet x U P)
      (fun g hg => agree g (sub (es g hg))) ⟨V,inj⟩
      (fun i => (v i-(T r).eval (x i))/G.eval (x i))
    intro g
    refine ⟨(deg g).trans (by omega),?_⟩
    intro i hi
    have noD := nonzero_at_agreement x σ fixed U E P q h N ker g (sub (es g g.property)) i hi
    obtain ⟨d,de⟩ := divD
    have noG : G.eval (x i)≠0 := by intro zero;apply noD;rw [de,eval_mul,zero,zero_mul]
    apply (eq_div_iff noG).mpr
    have val := congrArg (Polynomial.eval (x i)) (eq g)
    simp only [eval_sub,eval_mul,(fit g (es _ g.property)).2.2.1 i hi] at val
    linear_combination -val
  rw [IRSProfile.card_index] at c1
  have gd := Polynomial.natDegree_le_of_dvd divD N.d₀_ne
  have dd := N.first_degree
  unfold prime at *
  omega
#print axioms effective_at
end
end ProximityPrize.SubmissionLower.Genuine6969.IntermediateDivisor
