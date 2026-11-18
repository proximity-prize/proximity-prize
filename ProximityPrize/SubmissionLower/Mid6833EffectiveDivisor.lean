/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LowDivisible
import ProximityPrize.SubmissionLower.Mid6833RationalSlope
namespace ProximityPrize.SubmissionLower.Genuine6969
open Koala6831Comparison K6969Global Koala6831Separation Koala6831Moving
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes)
open Koala6831BenchmarkField (prime)
open Frontier6969.GenuineMoving Polynomial Finset ProximityPrize.Benchmark
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K : Type} [Field K]

/-- All normalized differences carry the same fixed divisor. The remaining height
is controlled by the original code degree and the uncancelled denominator. -/
theorem difference_divisor {q : SymbolicRow (Seeds K)} {w δ : ℕ} (N : NormalForm q w δ)
    (G : K[X]) (ng : G≠0) (divD : G∣N.d₀) (divM : G∣N.A 0*N.C 1-N.A 1*N.C 0)
    (g h : K) (Pg Ph Tg Th : K[X])
    (regG : IsCoprime G (affineDenominator (N.A 0) (N.A 1) g))
    (regH : IsCoprime G (affineDenominator (N.A 0) (N.A 1) h))
    (rg : N.d₀*Pg+affineDenominator (N.C 0) (N.C 1) g=affineDenominator (N.A 0) (N.A 1) g*Tg)
    (rh : N.d₀*Ph+affineDenominator (N.C 0) (N.C 1) h=affineDenominator (N.A 0) (N.A 1) h*Th)
    (lowG : ∀j,(N.A j*Tg-N.C j).natDegree≤w+N.d₀.natDegree)
    (lowH : ∀j,(N.A j*Th-N.C j).natDegree≤w+N.d₀.natDegree) :
    ∃V : K[X], Tg-Th=G*V ∧ V.natDegree≤w+N.d₀.natDegree-pairDegree N.A-G.natDegree := by
  obtain ⟨d,hd⟩ := divD
  have dg := separate_divisors G (d*Pg) Tg N.A N.C g regG divM (by simpa only [hd,mul_assoc] using rg)
  have dh := separate_divisors G (d*Ph) Th N.A N.C h regH divM (by simpa only [hd,mul_assoc] using rh)
  have dv (j) : G∣N.A j*(Tg-Th) := by
    convert dvd_sub (dg j) (dh j) using 1
    ring
  obtain ⟨u,v,bez⟩ := N.A_coprime
  have divides : G∣Tg-Th := by
    convert dvd_add (dvd_mul_of_dvd_right (dv 0) u) (dvd_mul_of_dvd_right (dv 1) v) using 1
    linear_combination -(Tg-Th)*bez
  obtain ⟨V,eq⟩ := divides
  refine ⟨V,eq,?_⟩
  by_cases zero : V=0
  · simp [zero]
  have height (j) : (N.A j*(G*V)).natDegree≤w+N.d₀.natDegree := by
    rw [←eq,show N.A j*(Tg-Th)=(N.A j*Tg-N.C j)-(N.A j*Th-N.C j) by ring]
    exact (natDegree_sub_le ..).trans (max_le (lowG j) (lowH j))
  have aux (j) (nz : N.A j≠0) : (N.A j).natDegree+G.natDegree+V.natDegree≤w+N.d₀.natDegree := by
    have H := height j
    rw [natDegree_mul nz (mul_ne_zero ng zero),natDegree_mul ng zero] at H
    omega
  by_cases n0 : N.A 0=0
  · have n1 : N.A 1≠0 := by intro z; simp [n0,z] at bez
    have := aux 1 n1
    simp only [pairDegree,n0,natDegree_zero,zero_le,max_eq_right] at *
    omega
  by_cases n1 : N.A 1=0
  · have := aux 0 n0
    simp only [pairDegree,n1,natDegree_zero,Nat.zero_le,max_eq_left] at *
    omega
  have := aux 0 n0
  have := aux 1 n1
  unfold pairDegree
  omega

theorem effective_count (U : Received F IRSProfile.Index) (E : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (ker : CommonKernel σ N)
    (short : primitiveExcess 131071 q≤12136)
    (nondiv : ¬N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0)
    (small : (N.A 0*N.C 1-N.A 1*N.C 0).natDegree≤131071+N.d₀.natDegree+pairDegree N.A)
    (G : F[X]) (ng : G≠0) (divD : G∣N.d₀) (divM : G∣N.A 0*N.C 1-N.A 1*N.C 0)
    (height : N.d₀.natDegree≤pairDegree N.A+G.natDegree+472) :
    E.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget := by
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
  have bound : regularSeeds.card≤214887237245589756 := by
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
    apply Frontier.LinearKernel.high_cap x regularSeeds (agreementSet x U P)
      (fun g hg => h.selection.agreement g (sub (es g hg))) ⟨V,inj⟩
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
  unfold budget prime at *
  omega
#print axioms difference_divisor
#print axioms effective_count
end
end ProximityPrize.SubmissionLower.Genuine6969
