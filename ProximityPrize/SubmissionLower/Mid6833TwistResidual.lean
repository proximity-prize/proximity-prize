/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833NormalizedTwist
namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower ProximityPrize.Benchmark
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Moving (affineDenominator)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open K6969Global (RetainedComparison budget combinedDegree)
open Koala6831BenchmarkField (prime frobenius)
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K I : Type} [Field K] [Fintype I]

def CommonKernel (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) : Prop :=
  ∃ R : K[X], R≠0 ∧ ∀ j, N.d₁*(N.A j).map σ*R.map σ=N.d₀.map σ*N.B j*R

theorem kernel_or_small (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (short : primitiveExcess 131071 q ≤ 12136) :
    CommonKernel σ N ∨ E.card≤82405+(Fintype.card I+1+(prime+1)*primitiveExcess 131071 q) := by
  classical
  obtain ⟨S,inc,card,T,v,fit⟩ := retained_solutions x σ fixed U E P q h N short
  by_cases variation : ∃ g ∈ S, ∃ h ∈ S, T g ≠ T h
  · obtain ⟨g,hg,f,hf,ne⟩ := variation
    exact Or.inl ⟨T g - T f,sub_ne_zero.mpr ne, homogeneous_difference σ N
      (fit g hg).2.2.2 (fit f hf).2.2.2⟩
  · right
    suffices S.card ≤ 82405 by omega
    by_cases nonempty : S.Nonempty
    · obtain ⟨r,hr⟩ := nonempty
      apply Koala6831Cramer.card_le_of_common_denominator S P N.d₀
        (N.A 0*T r-N.C 0) (N.A 1*T r-N.C 1) N.d₀_ne 131071 82404
        (fun g hg => h.selection.degree_le g (inc hg))
      · intro g hg
        have same : T g = T r := by_contra fun ne => variation ⟨g,hg,r,hr,ne⟩
        have row := (fit g hg).2.1
        simp only [affineDenominator,same] at row
        linear_combination row
      · intro p₀ p₁ dp₀ dp₁
        apply (card_le_card ?_).trans (h.selection.pencil p₀ p₁ dp₀ dp₁)
        intro g hg
        obtain ⟨hs,eq⟩ := mem_filter.mp hg
        exact mem_filter.mpr ⟨inc hs,eq⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

/-- The only remaining actual benchmark rows have conjugate-proportional directions
and admit a simultaneous nonzero polynomial eigenfunction in the two channels. -/
def CompatibleResidual : Prop :=
  ∀ (U : Received IRSProfile.Field IRSProfile.Index) (S : Finset IRSProfile.Field)
    (P : SelectionMap IRSProfile.Field) (q : SymbolicRow (Seeds IRSProfile.Field)),
    RetainedComparison IRSProfile.domain frobenius.toRingHom U S P q →
    primitiveExcess 131071 q < 12137 →
    (∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0) →
    ∀ N : NormalForm q 131071 (primitiveExcess 131071 q),
    combinedDegree q ≤ 2 →
    (pairDegree N.A+pairDegree N.B+472<primitiveExcess 131071 q ∨
      (N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0 ∧ N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0 ∧ IsCoprime N.d₀ N.d₁)) →
    twist frobenius.toRingHom N.A N.B = 0 → CommonKernel frobenius.toRingHom N →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget

theorem protocol_of_compatible (remaining : CompatibleResidual) :
    ProtocolClaim 6969 337530879 1073741824 := by
  apply K6969Global.protocol_reduction
  intro U S P q h hs rank N dc div
  by_cases transverse : twist frobenius.toRingHom N.A N.B=0
  · rcases kernel_or_small IRSProfile.domain frobenius.toRingHom Koala6831BenchmarkField.domain_fixed
      U S P q h N (by omega) with kernel | small
    · exact remaining U S P q h hs rank N dc div transverse kernel
    · rw [IRSProfile.card_index] at small
      unfold budget prime at *
      omega
  · have bound := transverse_count IRSProfile.domain frobenius.toRingHom Koala6831BenchmarkField.domain_fixed
      U S P q h N (by omega) transverse
    unfold budget prime
    omega

#print axioms kernel_or_small
#print axioms protocol_of_compatible
end
end Frontier6969.GenuineMoving
