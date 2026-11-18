/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
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

/-- At a fixed point all values of a homogeneous semilinear polynomial family
lie on one line over the fixed field, including after cancellation of a polynomial divisor. -/
theorem evaluated_homogeneous_count (s : K →+* K) (p : ℕ) (hp : 1<p)
    (pow : ∀g,s g=g^p) (α : K) (hx : s α=α) (S : Finset K) (Q : S → K[X])
    (L R : K[X]) (nz : L≠0) (row : ∀g,L*(Q g).map s=R*Q g)
    (inj : Function.Injective (fun g:S => (Q g).eval α)) : S.card≤p := by
  classical
  let f (g : S) := (Q g).eval α
  let vals := univ.image f
  have finj : Function.Injective f := inj
  have card : vals.card=S.card := by rw [show vals=univ.image f from rfl,card_image_of_injective _ finj,card_univ,Fintype.card_coe]
  by_cases nonzero : ∃ h:S,f h≠0
  · obtain ⟨h,nh⟩ := nonzero
    rw [←card]
    apply Frontier6969.Projection.prime_line s p hp pow vals 1 (f h) one_ne_zero nh
    intro t ht
    obtain ⟨g,_,rfl⟩ := mem_image.mp ht
    have cross : (Q g).map s * Q h = (Q h).map s * Q g := by
      apply mul_left_cancel₀ nz
      linear_combination (Q h)*(row g) - (Q g)*(row h)
    have ev := congrArg (Polynomial.eval α) cross
    have ma (P : K[X]) : (P.map s).eval α=s (P.eval α) := by simpa only [hx] using eval_map_apply (p:=P) s α
    simp only [eval_mul,ma] at ev
    simp only [f,mul_one]
    linear_combination -ev
  · have hi : vals⊆{0} := by
      intro t ht
      obtain ⟨g,_,rfl⟩ := mem_image.mp ht
      exact mem_singleton.mpr (by_contra (fun ne => nonzero ⟨g,ne⟩))
    rw [←card]
    exact (card_le_card hi).trans (by simpa using hp.le)

/-- The residue after dividing a common part of the two polynomials detects
a seed even when both original evaluations at the pole are zero. -/
theorem repeated_pole_count (U : Received F IRSProfile.Index) (E : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (short : primitiveExcess 131071 q≤12136)
    (small : (N.A 0*N.C 1-N.A 1*N.C 0).natDegree≤131071+N.d₀.natDegree+pairDegree N.A)
    (G d M : F[X]) (ng : G≠0) (dd : N.d₀=G*d) (dm : N.A 0*N.C 1-N.A 1*N.C 0=G*M)
    (α : F) (fixed : σ α=α) (pole : d.eval α=0) (visible : M.eval α≠0) :
    E.card ≤ prime + (262144+2+(prime+2)*primitiveExcess 131071 q) := by
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
  have cnt : goodSeeds.card≤prime := by
    by_cases nonempty : goodSeeds.Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    obtain ⟨r,hr⟩ := nonempty
    have gs (g) (hg:g∈goodSeeds) := rs (gr hg)
    have ok (g) (hg:g∈goodSeeds) := (fit g (gs g hg)).2.1
    have low (g) (hg:g∈goodSeeds) := infinity_small N g (P g) (T g) (h.selection.degree_le g (se (gs g hg)))
      (lead g (gr hg)).1 (lead g (gr hg)).2 (ok g hg) small
    have fct (g : goodSeeds) := difference_divisor N G ng ⟨d,dd⟩ ⟨M,dm⟩ g r (P g) (P r) (T g) (T r)
      (regs g g.property) (regs r hr) (ok g g.property) (ok r hr) (low g g.property) (low r hr)
    choose Q eq _ using fct
    have localEq (g:goodSeeds) : (A g).eval α * (A r).eval α * (Q g).eval α = ((g:F)-r)*M.eval α := by
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
      have ev := congrArg (Polynomial.eval α) divided
      simpa only [eval_mul,eval_sub,eval_add,eval_C,pole,zero_mul,zero_add] using ev
    have inj : Function.Injective (fun g:goodSeeds => (Q g).eval α) := by
      intro g k agree
      apply Subtype.ext
      have ge := localEq g
      have ke := localEq k
      change (Q g).eval α=(Q k).eval α at agree
      rw [agree] at ge
      by_cases ar : (A r).eval α=0
      · rw [ar,mul_zero,zero_mul] at ge ke
        have e₁ := (mul_eq_zero.mp ge.symm).resolve_right visible
        have e₂ := (mul_eq_zero.mp ke.symm).resolve_right visible
        exact (sub_eq_zero.mp e₁).trans (sub_eq_zero.mp e₂).symm
      have out : (((g:F)-(k:F))*M.eval α)*(A r).eval α = 0 := by
        simp only [A,affineDenominator,eval_add,eval_mul,eval_C] at ge ke ⊢
        linear_combination -((N.A 0).eval α+(k:F)*(N.A 1).eval α)*ge +
          ((N.A 0).eval α+(g:F)*(N.A 1).eval α)*ke
      exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp out).resolve_right ar)).resolve_right visible)
    have active : ∃j, N.A j≠0 := by
      by_contra! z
      obtain ⟨u,v,b⟩ := N.A_coprime
      simp only [z,mul_zero,zero_add] at b
      exact zero_ne_one b
    obtain ⟨j,nj⟩ := active
    apply evaluated_homogeneous_count σ prime (by decide) Koala6831BenchmarkField.frobenius_apply α fixed goodSeeds Q
      (N.d₁*(N.A j).map σ*G.map σ) (N.d₀.map σ*N.B j*G)
      (mul_ne_zero (mul_ne_zero N.d₁_ne (Polynomial.map_ne_zero nj)) (Polynomial.map_ne_zero ng)) _ inj
    intro g
    have hom := homogeneous_difference σ N (fit g (gs g g.property)).2.2.2 (fit r (gs r hr)).2.2.2 j
    rw [eq g,Polynomial.map_mul] at hom
    linear_combination hom
  rw [IRSProfile.card_index] at c1
  have gd := Polynomial.natDegree_le_of_dvd (show G∣N.d₀ from ⟨d,dd⟩) N.d₀_ne
  have dd' := N.first_degree
  unfold prime at *
  omega
#print axioms evaluated_homogeneous_count
#print axioms repeated_pole_count
end
end ProximityPrize.SubmissionLower.Genuine6969
