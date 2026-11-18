import ProximityPrize.SubmissionLower.Koala6831BenchmarkField
import ProximityPrize.SubmissionLower.Koala6831Protocol
import ProximityPrize.SubmissionLower.Koala6831OneSided
import ProximityPrize.SubmissionLower.Koala6831PrimitiveDimension
import ProximityPrize.SubmissionLower.Koala6831PrimitiveDiscard

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkPrimitive

open Koala6831BenchmarkField (prime)
open Koala6831Comparison Koala6831Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000

variable {K I : Type} [Field K] [Fintype I]

abbrev Received (K I : Type) := Fin 2 → I → K
abbrev SelectionMap (K : Type) [Semiring K] := K → Polynomial K

abbrev Rows (x : I ↪ K) (σ : K →+* K) (received : Received K I) (d : ℕ) :=
  ComparisonSpace 181078 50007 d x
    (fun j i => if j = 0 then received 0 i else σ (received 0 i))
    (fun j i => if j = 0 then received 1 i else σ (received 1 i))

def agreementSet (x : I ↪ K) (received : Received K I) (selected : SelectionMap K)
    (g : K) : Finset I :=
  @Finset.filter _ (fun i => (selected g).eval (x i) =
    received 0 i + g * received 1 i) (fun _ => Classical.propDecidable _) Finset.univ

theorem eval_eq_of_mem_agreementSet
    {x : I ↪ K} {received : Received K I} {selected : SelectionMap K} {g : K} {i : I}
    (hi : i ∈ agreementSet x received selected g) :
    (selected g).eval (x i) = received 0 i + g * received 1 i := by
  unfold agreementSet at hi
  exact (Finset.mem_filter.mp hi).2

structure Selection (x : I ↪ K) (received : Received K I) (seeds : Finset K)
    (selected : SelectionMap K) : Prop where
  degree_le : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071
  agreement : ∀ g ∈ seeds, 181078 ≤ (agreementSet x received selected g).card
  pencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ 131071 → p₁.natDegree ≤ 131071 →
    (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ 81067

abbrev badNodes (x : I ↪ K) (σ : K →+* K) (received : Received K I)
    (q : SymbolicRow (SeedRing K)) :=
  primitiveBadNodes x (conjugateWord σ (received 0)) (conjugateWord σ (received 1)) q

def coefficientDeterminant {A a d₀ d₁ : ℕ} (first : RowIndex A a d₀ → K)
    (second : RowIndex A a d₁ → K) : SeedCoefficients K :=
  (symbolicRow first).first * (symbolicRow second).second -
    (symbolicRow first).second * (symbolicRow second).first

def TwoSidedPrimitiveSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (seeds : Finset K) (selected : SelectionMap K),
    Selection x received seeds selected →
    ∀ (row : Rows x σ received 4)
      (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q →
      RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (badNodes x σ received q).card ≤ 31059 →
      seeds.card ≤ mcaBudget

private theorem one_sided_rows_le_seed_budget
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (received : Received K I) (row : Rows x σ received 4)
    (hone : let q := symbolicRow row.1
      (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0))
    (seeds : Finset K) (selected : SelectionMap K)
    (support : Selection x received seeds selected) : seeds.card ≤ mcaBudget := by
  have bound := Koala6831OneSided.one_sided_comparison_card_le
    (p := prime) (w := 131071) (e := 81066) (A := 181078) (a := 50007)
    (by decide) (by decide) x received σ hfixed hpow (by decide) (by decide)
    (by rw [hcard]; decide) row hone seeds selected support.degree_le support.agreement support.pencil
  rw [hcard, Koala6831OneSided.koala_one_sided_budget] at bound
  exact bound.trans (by decide +kernel)

def MixedRowsSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (row : Rows x σ received 4) (other : Rows x σ received 62150),
    coefficientDeterminant row.1 other.1 ≠ 0 →
    ∀ (seeds : Finset K) (selected : SelectionMap K),
      Selection x received seeds selected → seeds.card ≤ mcaBudget

private theorem cross_eq_of_symbolic_det_zero {A a d₀ d₁ : ℕ}
    (first : RowIndex A a d₀ → K) (second : RowIndex A a d₁ → K)
    (hzero : coefficientDeterminant first second = 0) :
    (rankRow first).first * (rankRow second).second =
      (rankRow second).first * (rankRow first).second := by
  unfold coefficientDeterminant at hzero
  simpa only [rankRow, mul_comm (symbolicRow first).second (symbolicRow second).first]
    using sub_eq_zero.mp hzero

private theorem comparison_one_sided_of_factor {A a d : ℕ}
    (row : RowIndex A a d → K) (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (hfactor : RowFactors q (rankRow row) m)
    (hone : (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0)) :
    let r := symbolicRow row
    (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0) := by
  have hr := Koala6831OneSided.one_sided_of_nonzero_multiplier hm hone
  rw [← hfactor.first, ← hfactor.second] at hr
  simpa only [rankRow] using hr

def RankOneSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (seeds : Finset K) (selected : SelectionMap K),
    Selection x received seeds selected →
    ∀ row : Rows x σ received 4, row.1 ≠ 0 →
      (∀ other : Rows x σ received 62150, coefficientDeterminant row.1 other.1 = 0) →
      seeds.card ≤ mcaBudget

private theorem seed_bound_of_rank_cases
    (x : I ↪ K) (σ : K →+* K) (hcard : Fintype.card I = 262144)
    (hMixed : MixedRowsSeedBound x σ) (hRankOne : RankOneSeedBound x σ) :
    RCN050.SelectedNoLargePencilBound x 131071 errors mcaBudget := by
  intro received seeds A selected hdegree hnear hvalue hpencil
  have hthreshold : Fintype.card I - errors = 181078 := by rw [hcard]; decide
  have hagreement : ∀ g ∈ seeds, 181078 ≤ (agreementSet x received selected g).card := by
    intro g hg
    have hn := hnear g hg
    rw [hthreshold] at hn
    refine hn.trans (Finset.card_le_card ?_)
    intro i hi
    unfold agreementSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalue g hg i hi⟩
  have hselection : Selection x received seeds selected := ⟨hdegree, hagreement, hpencil⟩
  let u (j : Fin 2) (i : I) := if j = 0 then received 0 i else σ (received 0 i)
  let v (j : Fin 2) (i : I) := if j = 0 then received 1 i else σ (received 1 i)
  obtain ⟨row, hrow⟩ := (exists_koalabear_comparison_rows x u v hcard).1
  by_cases hdet : ∃ other : Rows x σ received 62150, coefficientDeterminant row.1 other.1 ≠ 0
  · obtain ⟨other, hother⟩ := hdet
    exact hMixed received row other hother seeds selected hselection
  exact hRankOne received seeds selected hselection row hrow
    (fun other => not_ne_iff.mp (fun h => hdet ⟨other, h⟩))

private theorem card_le_from_primitive_cases
    (x : I ↪ K) (u v : Fin 2 → I → K) (hcard : Fintype.card I = 262144)
    (row : ComparisonSpace 181078 50007 4 x u v) (hrow : row.1 ≠ 0)
    (hdet : ∀ other : ComparisonSpace 181078 50007 62150 x u v,
      coefficientDeterminant row.1 other.1 = 0)
    (seedCount : ℕ)
    (honeCase : (let r := symbolicRow row.1
      (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0)) → seedCount ≤ mcaBudget)
    (hbothCase : ∀ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q → RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 31059 → seedCount ≤ mcaBudget) :
    seedCount ≤ mcaBudget := by
  obtain ⟨q, m, hm, hactive, hprimitive, hfactor, hlarge⟩ :=
    exists_primitive_comparison_generator x u v row hrow (by rw [hcard]; decide)
      (fun other => cross_eq_of_symbolic_det_zero row.1 other.1 (hdet other))
  by_cases hone : (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0)
  · exact honeCase (comparison_one_sided_of_factor row.1 q m hm hfactor hone)
  have hboth : q.first ≠ 0 ∧ q.second ≠ 0 := by
    rcases hactive with hf | hs
    · exact ⟨hf, fun hz => hone (Or.inl ⟨hf, hz⟩)⟩
    · exact ⟨fun hz => hone (Or.inr ⟨hz, hs⟩), hs⟩
  have hcap := primitive_excess_add_badCard_le_31059 x u v q hboth.1 hboth.2 hcard hlarge
  exact hbothCase q m hboth.1 hboth.2 hm hprimitive hfactor hcap

private theorem rank_one_bound_of_primitive
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (hPrimitive : TwoSidedPrimitiveSeedBound x σ) : RankOneSeedBound x σ := by
  intro received seeds selected hselection row hrow hcross
  exact card_le_from_primitive_cases x (conjugateWord σ (received 0))
    (conjugateWord σ (received 1)) hcard row hrow hcross seeds.card
    (fun hone => one_sided_rows_le_seed_budget x σ hfixed hpow hcard received row hone
      seeds selected hselection)
    (hPrimitive received seeds selected hselection row)

theorem seed_bound_of_two_sided_primitive
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (hMixed : MixedRowsSeedBound x σ) (hPrimitive : TwoSidedPrimitiveSeedBound x σ) :
    RCN050.SelectedNoLargePencilBound x 131071 errors mcaBudget :=
  seed_bound_of_rank_cases x σ hcard hMixed
    (rank_one_bound_of_primitive x σ hfixed hpow hcard hPrimitive)

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkPrimitive

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
