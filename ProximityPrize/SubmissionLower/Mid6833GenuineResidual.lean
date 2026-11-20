/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Exact remaining obligation at score 6969. See RESULTS.md. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineProtocol
import ProximityPrize.SubmissionLower.Mid6833LinearCut
import ProximityPrize.SubmissionLower.Mid6833RepeatedPole
import ProximityPrize.SubmissionLower.Mid6833InfinityCount
import ProximityPrize.SubmissionLower.Mid6833ReducedPoles
import ProximityPrize.SubmissionLower.Mid6833MixedPoleCount

namespace ProximityPrize.SubmissionLower.Genuine6969
open ProximityPrize.Benchmark K6969Global Koala6831Separation Koala6831Comparison
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open Koala6831BenchmarkField (prime frobenius)
open Frontier6969.GenuineMoving Polynomial
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

abbrev det {q : SymbolicRow (Seeds F)} {δ : ℕ} (N : NormalForm q 131071 δ) :=
  N.A 0*N.C 1-N.A 1*N.C 0

def VisibleAdjacent {q : SymbolicRow (Seeds F)} {δ : ℕ} (N : NormalForm q 131071 δ) : Prop :=
  ∃ (L : Type) (_ : Field L) (c : F →+* L) (τ : L →+* L), τ.comp c=c.comp σ ∧
    (∀t,τ t=t^prime) ∧ ∃ (G d M : F[X]) (α : L), G≠0 ∧ N.d₀=G*d ∧ det N=G*M ∧
      d.eval₂ c α=0 ∧ d.eval₂ c (τ α)=0 ∧ M.eval₂ c α≠0 ∧ M.eval₂ c (τ α)≠0

/-- No family of visible poles has residue-field degrees with joint gcd one
with the sextic extension degree. Different poles can use different fields. -/
def NoMixedPoles {q : SymbolicRow (Seeds F)} {δ : ℕ} (N : NormalForm q 131071 δ) : Prop :=
  ∀ {J : Type} [Fintype J] (L Ω : J → Type) [∀j,Field (L j)] [∀j,Field (Ω j)] [∀j,Fintype (L j)]
    (ι : ∀j,F→+*Ω j) (l : ∀j,L j→+*Ω j) (b : ∀j,KoalaBear.Field→+*L j)
    (_comm : ∀j,(ι j).comp (algebraMap KoalaBear.Field F)=(l j).comp (b j))
    (α : ∀j,L j) (m : J → ℕ) (_sizes : ∀j,Fintype.card (L j)=prime^(m j)),
    (∀j,N.d₀.eval₂ (ι j) (l j (α j))=0) → (∀j,(det N).eval₂ (ι j) (l j (α j))≠0) →
    Nat.gcd 6 (Finset.univ.gcd m)≠1

def VisibleFixed {q : SymbolicRow (Seeds F)} {δ : ℕ} (N : NormalForm q 131071 δ) : Prop :=
  ∃ (G d M : F[X]) (α : F), G≠0 ∧ N.d₀=G*d ∧ det N=G*M ∧
    σ α=α ∧ d.eval α=0 ∧ M.eval α≠0

/-- Every field is a necessary condition on a still-unpriced family. -/
structure Difficult (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (Seeds F)) (N : NormalForm q 131071 (primitiveExcess 131071 q)) : Prop where
  actual : RetainedComparison Dmn σ U S P q
  genuinelyBad : Bad Dmn U S P
  short : primitiveExcess 131071 q<12137
  singular : ∀keys,(Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0
  combined : combinedDegree q≤2
  gap : pairDegree N.A+pairDegree N.B+472<primitiveExcess 131071 q
  aligned : twist σ N.A N.B=0
  kernel : CommonKernel σ N
  low : (det N).natDegree≤131071+N.d₀.natDegree+pairDegree N.A
  finiteFailure : ¬ N.d₀∣det N
  degreeLeft : ∀G : F[X],G≠0 → G∣N.d₀ → G∣det N → pairDegree N.A+G.natDegree+472<N.d₀.natDegree
  fixed : ¬ VisibleFixed N
  adjacent : ¬ VisibleAdjacent N
  mixed : NoMixedPoles N
  linear : combinedDegree q≤1 → HardLinear U S P (primitiveExcess 131071 q)

def Remaining : Prop :=
  ∀ (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (Seeds F)) (N : NormalForm q 131071 (primitiveExcess 131071 q)),
    Difficult U S P q N → S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget

/-- Each exclusion is integrated into the official protocol type. The sole
unproved obligation is named Remaining and appears in the theorem statement. -/
theorem protocol_of_remaining (remaining : Remaining) : ProtocolClaim 6969 337530879 1073741824 := by
  classical
  apply protocol_of_bad_residual
  intro U S P q h bad short rank N dc old
  let fixed := Koala6831BenchmarkField.domain_fixed
  let pow := Koala6831BenchmarkField.frobenius_apply
  let δ := primitiveExcess 131071 q
  change S.card+(33735-δ+1)*6*(prime+1)≤budget
  have hs : δ≤12136 := by dsimp [δ];omega
  by_cases aligned : twist σ N.A N.B=0
  swap
  · have n := transverse_count Dmn σ fixed U S P q h N hs aligned
    unfold budget prime
    omega
  rcases kernel_or_small Dmn σ fixed U S P q h N hs with ker|tiny
  swap
  · rw [IRSProfile.card_index] at tiny
    change S.card≤82405+(262144+1+(prime+1)*δ) at tiny
    unfold budget prime at *
    omega
  by_cases low : (det N).natDegree≤131071+N.d₀.natDegree+pairDegree N.A
  swap
  · have n := infinity_large Dmn σ fixed pow U S P q h N hs (lt_of_not_ge low)
    rw [IRSProfile.card_index] at n
    change S.card≤prime+(262144+2+(prime+1)*δ) at n
    unfold budget prime at *
    omega
  by_cases yes : N.d₀∣det N
  · have n := low_divisible Dmn σ fixed U S P q h bad N ker hs yes low
    rw [IRSProfile.card_index] at n
    change S.card≤262144+2+(prime+2)*δ at n
    unfold budget prime at *
    omega
  have gap : pairDegree N.A+pairDegree N.B+472<δ := old.resolve_right (fun alt => yes alt.1)
  by_cases eff : ∀G : F[X],G≠0 → G∣N.d₀ → G∣det N → pairDegree N.A+G.natDegree+472<N.d₀.natDegree
  swap
  · push Not at eff
    obtain ⟨G,nG,divD,divM,save⟩ := eff
    exact effective_count U S P q h N ker hs yes low G nG divD divM save
  by_cases vis : VisibleFixed N
  · obtain ⟨G,d,M,α,nG,dd,dm,fx,root,nz⟩ := vis
    have n := repeated_pole_count U S P q h N hs low G d M nG dd dm α fx root nz
    change S.card≤prime+(262144+2+(prime+2)*δ) at n
    unfold budget prime at *
    omega
  by_cases pair : VisibleAdjacent N
  · obtain ⟨L,inst,c,τ,comm,power,G,d,M,α,nG,dd,dm,root,other,m₀,m₁⟩ := pair
    letI := inst
    have n := reduced_conjugate_poles c τ comm power U S P q h N hs low G d M nG dd dm α root other m₀ m₁
    change S.card≤prime+1+(262144+2+(prime+2)*δ) at n
    unfold budget prime at *
    omega
  by_cases priced : S.card+(33735-δ+1)*6*(prime+1)≤budget
  · exact priced
  have mix : NoMixedPoles N := by
    intro J _ L Ω iL iΩ fL ι l b commute α m sizes poles visible cop
    exact priced (mixed_pole_price U S P q h N hs L Ω ι l b commute α m sizes cop poles visible)
  by_cases lin : combinedDegree q≤1 → HardLinear U S P δ
  · exact remaining U S P q N ⟨h,bad,short,rank,dc,gap,aligned,ker,low,yes,eff,vis,pair,mix,lin⟩
  push Not at lin
  have n := (linear_or_small U S P q h bad lin.1).resolve_left lin.2
  unfold budget prime
  omega

#print axioms protocol_of_remaining
end
end ProximityPrize.SubmissionLower.Genuine6969
