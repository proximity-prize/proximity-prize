import ProximityPrize.SubmissionLower.Koala6831BenchmarkPrimitive

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention

open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive Koala6831Comparison Koala6831Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000

variable {K I : Type} [Field K] [Fintype I]

def commonDiscardBudget : ℕ := 330770866814160
def retainedSeedBudget : ℕ := 274430098954830993

structure RetainedComparison (x : I ↪ K) (σ : K →+* K)
    (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) : Prop where
  selection : Selection x received retained selected
  first_ne : q.first ≠ 0
  second_ne : q.second ≠ 0
  primitive : IsPrimitiveRow q
  xDegree : q.beta.natDegree ≤ 181083 ∧ q.first.natDegree ≤ 50012 ∧ q.second.natDegree ≤ 50012
  seedDegree : ∀ j, ((q.beta.coeff j).degreeOf 0 ≤ 5 ∧ (q.beta.coeff j).degreeOf 1 ≤ 5) ∧
    ((q.first.coeff j).degreeOf 0 ≤ 4 ∧ (q.first.coeff j).degreeOf 1 ≤ 5) ∧
    ((q.second.coeff j).degreeOf 0 ≤ 5 ∧ (q.second.coeff j).degreeOf 1 ≤ 4)
  excess_bad : primitiveExcess 131071 q + (badNodes x σ received q).card ≤ 31357
  good : ∀ g ∈ retained, primitiveSelected σ prime q selected g = 0 ∧
    Disjoint (agreementSet x received selected g) (badNodes x σ received q)

def RetainedTwoSidedSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ received retained selected q → retained.card ≤ retainedSeedBudget

private theorem selection_of_subset {x : I ↪ K} {received : Received K I}
    {seeds retained : Finset K} {selected : SelectionMap K}
    (support : Selection x received seeds selected) (hsub : retained ⊆ seeds) :
    Selection x received retained selected := by
  refine ⟨fun g hg => support.degree_le g (hsub hg), fun g hg => support.agreement g (hsub hg), ?_⟩
  intro p₀ p₁ hp₀ hp₁
  refine (Finset.card_le_card (t := RCN050.pencilSeeds seeds selected p₀ p₁) ?_).trans
    (support.pencil p₀ p₁ hp₀ hp₁)
  intro g hg
  obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hsub hmem, heq⟩

theorem primitive_bound_of_retained
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hRetained : RetainedTwoSidedSeedBound x σ) :
    TwoSidedPrimitiveSeedBound x σ := by
  intro received seeds selected support row q m hfirst hsecond hm hprimitive hfactor hcap
  obtain ⟨retained, hsub, hseedCount, hrow⟩ := retain_primitive_rows
    (A := 181084) (a := 50013) (w := 131071) (p := prime)
    x σ hfixed hpow (by decide) received (by decide) (by decide) row q m hm
    (Or.inl hfirst) hfactor seeds (agreementSet x received selected) selected
    support.degree_le support.agreement (fun _ _ _ hi => eval_eq_of_mem_agreementSet hi)
  have hX := primitive_x_degree_caps row.1 q m hm hfactor
  have hB := primitive_seed_degree_caps row.1 q m hm hfactor
  have hretained := hRetained received retained selected q
    ⟨selection_of_subset support hsub, hfirst, hsecond, hprimitive, hX, hB, by omega, hrow⟩
  have hbad : (badNodes x σ received q).card + 1 ≤ 31048 := by omega
  have hdiscard : ((badNodes x σ received q).card + 1) * (5 * (prime + 1)) ≤ commonDiscardBudget :=
    (Nat.mul_le_mul_right (5 * (prime + 1)) hbad).trans_eq (by decide +kernel)
  have hsum : retainedSeedBudget + commonDiscardBudget = mcaBudget := by decide +kernel
  calc
    seeds.card ≤ retained.card + ((badNodes x σ received q).card + 1) * (5 * (prime + 1)) := hseedCount
    _ ≤ retainedSeedBudget + commonDiscardBudget := Nat.add_le_add hretained hdiscard
    _ = mcaBudget := hsum

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/
