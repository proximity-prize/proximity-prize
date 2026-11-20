/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833MobiusIncidence
import ProximityPrize.SubmissionLower.Mid6833EffectiveDivisor
import ProximityPrize.SubmissionLower.Mid6833PoleCount
namespace ProximityPrize.SubmissionLower.Genuine6969
open Koala6831Comparison K6969Global Koala6831Separation Koala6831Moving
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open Koala6831BenchmarkField (prime)
open Frontier6969.GenuineMoving Polynomial Finset ProximityPrize.Benchmark
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K : Type} [Field K]

theorem reduced_conjugate_poles {L : Type} [Field L] (c : F →+* L) (τ : L →+* L)
    (comm : τ.comp c=c.comp σ) (power : ∀ b, τ b=b^prime) (U : Received F IRSProfile.Index) (E : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (short : primitiveExcess 131071 q≤12136)
    (small : (N.A 0*N.C 1-N.A 1*N.C 0).natDegree≤131071+N.d₀.natDegree+pairDegree N.A)
    (G d M : F[X]) (ng : G≠0) (dd : N.d₀=G*d) (dm : N.A 0*N.C 1-N.A 1*N.C 0=G*M)
    (α : L) (pole : d.eval₂ c α=0) (conj : d.eval₂ c (τ α)=0)
    (visible : M.eval₂ c α≠0) (visible' : M.eval₂ c (τ α)≠0) :
    E.card ≤ prime+1 + (262144+2+(prime+2)*primitiveExcess 131071 q) := by
  classical
  obtain ⟨S,se,c1,T,_,fit⟩ := retained_solutions Dmn σ Koala6831BenchmarkField.domain_fixed U E P q h N short
  obtain ⟨R,rs,c2,lead⟩ := Frontier6969.Moving.leading_regular S N.A N.A_coprime
  let A := affineDenominator (N.A 0) (N.A 1)
  let goodSeeds := R.filter (fun g => IsCoprime G (A g))
  have gr : goodSeeds⊆R := filter_subset _ _
  have regs (g) (hg:g∈goodSeeds) : IsCoprime G (A g) := (mem_filter.mp hg).2
  have exc : (R\goodSeeds).card≤G.natDegree := by
    apply fixed_divisor_exceptions G ng N.A N.A_coprime
    intro g hg yes
    exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,yes⟩)
  have parts := card_sdiff_add_card_eq_card gr
  have cnt : goodSeeds.card≤prime+1 := by
    by_cases few : goodSeeds.card≤1
    · exact few.trans (by omega)
    obtain ⟨r,hr,s,hs,rsne⟩ := Finset.one_lt_card.mp (by omega : 1<goodSeeds.card)
    have gs (g) (hg:g∈goodSeeds) := rs (gr hg)
    have ok (g) (hg:g∈goodSeeds) := (fit g (gs g hg)).2.1
    have low (g) (hg:g∈goodSeeds) := infinity_small N g (P g) (T g) (h.selection.degree_le g (se (gs g hg)))
      (lead g (gr hg)).1 (lead g (gr hg)).2 (ok g hg) small
    have fct (g : goodSeeds) := difference_divisor N G ng ⟨d,dd⟩ ⟨M,dm⟩ g r (P g) (P r) (T g) (T r)
      (regs g g.property) (regs r hr) (ok g g.property) (ok r hr) (low g g.property) (low r hr)
    choose Q eq _ using fct
    let a (z : L) (g : F) := (N.A 0).eval₂ c z + c g*(N.A 1).eval₂ c z
    have localEq (g : goodSeeds) (z : L) (zero : d.eval₂ c z=0) :
        a z g * a z r * (Q g).eval₂ c z = (c g-c r)*M.eval₂ c z := by
      have full : A g*A r*(T g-T r)=N.d₀*(A r*P g-A g*P r)+C ((g:F)-r)*(N.A 0*N.C 1-N.A 1*N.C 0) := by
        have ge := ok g g.property
        have re := ok r hr
        dsimp only [A,affineDenominator] at ge re ⊢
        rw [C_sub]
        linear_combination -(N.A 0+C r*N.A 1)*ge+(N.A 0+C (g:F)*N.A 1)*re
      rw [eq g,dd,dm] at full
      have divided : A g*A r*Q g=d*(A r*P g-A g*P r)+C ((g:F)-r)*M := by
        apply mul_left_cancel₀ ng
        linear_combination full
      have ev := congrArg (Polynomial.eval₂ c z) divided
      simpa only [a,A,affineDenominator,eval₂_mul,eval₂_sub,eval₂_add,eval₂_C,map_sub,zero,zero_mul,zero_add] using ev
    have active : ∃j, N.A j≠0 := by
      by_contra! z
      obtain ⟨u,v,b⟩ := N.A_coprime
      simp only [z,mul_zero,zero_add] at b
      exact zero_ne_one b
    obtain ⟨j,nj⟩ := active

    let lc := N.d₁*(N.A j).map σ*G.map σ
    let rc := N.d₀.map σ*N.B j*G
    have ln : lc≠0 := mul_ne_zero (mul_ne_zero N.d₁_ne (Polynomial.map_ne_zero nj)) (Polynomial.map_ne_zero ng)
    have row (g : goodSeeds) : lc*(Q g).map σ=rc*Q g := by
      have hom := homogeneous_difference σ N (fit g (gs g g.property)).2.2.2 (fit r (gs r hr)).2.2.2 j
      rw [eq g,Polynomial.map_mul] at hom
      dsimp only [lc,rc]
      linear_combination hom
    let s' : goodSeeds := ⟨s,hs⟩
    have ratio (g : goodSeeds) : τ ((Q g).eval₂ c α)*(Q s').eval₂ c (τ α) =
        τ ((Q s').eval₂ c α)*(Q g).eval₂ c (τ α) := by
      have cross : (Q g).map σ*Q s'=(Q s').map σ*Q g := by
        apply mul_left_cancel₀ ln
        linear_combination Q s' * row g - Q g * row s'
      have atβ := congrArg (Polynomial.eval₂ c (τ α)) cross
      have conjEval (P : F[X]) : (P.map σ).eval₂ c (τ α)=τ (P.eval₂ c α) := by
        rw [Polynomial.eval₂_map,Polynomial.hom_eval₂,comm]
      simpa only [eval₂_mul,conjEval] using atβ
    have base : (c s-c r)*M.eval₂ c α≠0 := mul_ne_zero (sub_ne_zero.mpr (c.injective.ne rsne.symm)) visible
    have qa : (Q s').eval₂ c α≠0 := by
      intro bad
      have h := localEq s' α pole
      rw [bad,mul_zero] at h
      exact base h.symm
    have ar : a α r≠0 := by
      intro bad
      have h := localEq s' α pole
      rw [bad,mul_zero,zero_mul] at h
      exact base h.symm
    let c₀ := a (τ α) r*(Q s').eval₂ c (τ α)*τ (M.eval₂ c α)
    let c₁ := M.eval₂ c (τ α)*τ (a α r)*τ ((Q s').eval₂ c α)
    have cn : c₁≠0 := mul_ne_zero (mul_ne_zero visible' ((map_ne_zero τ).mpr ar)) ((map_ne_zero τ).mpr qa)
    apply mobius_count c prime (by decide) goodSeeds r hr
      ((N.A 0).eval₂ c α) ((N.A 1).eval₂ c α) ((N.A 0).eval₂ c (τ α)) ((N.A 1).eval₂ c (τ α)) c₀ c₁ ar cn
    intro g hg
    let gg : goodSeeds := ⟨g,hg⟩
    change c₀*a (τ α) g*(c g-c r)^prime=c₁*(c g-c r)*(a α g)^prime
    rw [←power,←power]
    have ea := congrArg τ (localEq gg α pole)
    simp only [map_mul] at ea
    have eb := localEq gg (τ α) conj
    have rat := ratio gg
    change τ (a α g)*τ (a α r)*τ ((Q gg).eval₂ c α)=τ (c g-c r)*τ (M.eval₂ c α) at ea
    change a (τ α) g*a (τ α) r*(Q gg).eval₂ c (τ α)=(c g-c r)*M.eval₂ c (τ α) at eb
    dsimp only [c₀,c₁]
    linear_combination -(a (τ α) r)*(Q s').eval₂ c (τ α)*(a (τ α) g)*ea
      + τ (a α r)*τ ((Q s').eval₂ c α)*τ (a α g)*eb
      + a (τ α) r*a (τ α) g*τ (a α r)*τ (a α g)*rat
  rw [IRSProfile.card_index] at c1
  have gd := Polynomial.natDegree_le_of_dvd (show G∣N.d₀ from ⟨d,dd⟩) N.d₀_ne
  have dd' := N.first_degree
  unfold prime at *
  omega
#print axioms reduced_conjugate_poles
end
end ProximityPrize.SubmissionLower.Genuine6969
