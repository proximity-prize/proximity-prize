/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. This reduction retains the actual physical support of every seed.
It extends the comparison method of Bome2017, Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Mid6833IntermediateBridge
import ProximityPrize.SubmissionLower.Mid6833IntermediateSemilinear
namespace ProximityPrize.SubmissionLower.Intermediate
open ProximityPrize.Benchmark K6969Global Koala6831Separation Koala6831Comparison Genuine6969 Genuine6969.IntermediateDivisor
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Koala6831BenchmarkField (prime)
open scoped Classical
noncomputable section
local instance mid6833Local_OpenRange_11  : DecidableEq IRSProfile.Field := Classical.decEq _
local instance mid6833Local_OpenRange_12  : DecidableEq IRSProfile.Index := Classical.decEq _

theorem can_of_excess {q : SymbolicRow (SeedRing F)} {δ k : ℕ} (N : NormalForm q 131071 δ)
    (h : δ≤k) : CanNormalize N k := by
  have nz : N.A 0 ≠ 0 ∨ N.A 1 ≠ 0 := by
    by_contra! z
    obtain ⟨a,b,eq⟩ := N.A_coprime
    simp [z.1,z.2] at eq
  have existsj : ∃ j, N.A j ≠ 0 := nz.elim (fun e => ⟨0,e⟩) (fun e => ⟨1,e⟩)
  obtain ⟨j,hj⟩ := existsj
  refine ⟨1,j,0,one_ne_zero,one_dvd _,one_dvd _,hj,fun _ _ _ => Nat.zero_le _,?_⟩
  have d := N.first_degree
  omega

def OpenAt (A B k hi : ℕ) : Prop :=
  ∀ (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F) (q : SymbolicRow (SeedRing F))
    (N : NormalForm q 131071 (primitiveExcess 131071 q)), Difficult U S P q N →
    (∀ g∈S, A≤(agreementSet Dmn U P g).card) →
    (∀ V W : Polynomial F, V.natDegree≤131071 → W.natDegree≤131071 →
      (RCN050.pencilSeeds S P V W).card≤262144-A+1) →
    k<primitiveExcess 131071 q → primitiveExcess 131071 q<hi → ¬CanNormalize N k →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤B
#print axioms can_of_excess
end
end ProximityPrize.SubmissionLower.Intermediate
