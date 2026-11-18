/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the credited Bome2017 68.32 release of Lucieno's comparison construction.
This file instantiates a larger secondary row and the separate row-height pricing. -/
import ProximityPrize.SubmissionLower.Mid6833MixedRank
import ProximityPrize.SubmissionLower.Mid6833OneSided
import ProximityPrize.SubmissionLower.Mid6833Discard
import ProximityPrize.SubmissionLower.Mid6833OrdinaryLarge
import ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual
import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Ordinary
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes coefficientDeterminant)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
variable {K I : Type} [Field K] [Fintype I]
abbrev Selection (x : I ↪ K) (U : Received K I) (S : Finset K) (P : SelectionMap K) := K6969OrdinaryLarge.Support x U S P
abbrev budget := 216076807731363018
abbrev Rows (x : I ↪ K) (σ : K →+* K) (received : Received K I) (d : ℕ) :=
  ComparisonSpace 179740 48669 d x
    (fun j i => if j = 0 then received 0 i else σ (received 0 i))
    (fun j i => if j = 0 then received 1 i else σ (received 1 i))

private theorem one_sided_price :
    max ((262144-131071:ℕ)*(7*(prime+1))/(179740-131071))
      ((131071+1)*(6*(prime+1))+(82404+1)) = 1675655722385893 := by decide +kernel
theorem primitive_excess_add_badCard_le_33735
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) (hcard : Fintype.card I = 262144)
    (h : ∀ θ : ComparisonSpace 179740 48669 67471 x u v, ∃ m, RowFactors q (rankRow θ.1) m) :
    primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 33735 := by
  have hlo := comparisonSpace_finrank_lower_bound 179740 48669 67471 82404 x u v hcard
  have hhi := comparisonSpace_finrank_le_primitiveBox x u v q h₀ h₁ (by decide)
    (w := 131071) (by decide) h
  have hbound := hlo.trans hhi
  norm_num at hbound
  omega
def TwoSidedPrimitiveSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (seeds : Finset K) (selected : SelectionMap K),
    Selection x received seeds selected →
    ∀ (row : Rows x σ received 5)
      (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q →
      RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (badNodes x σ received q).card ≤ 33735 →
      seeds.card ≤ budget

private theorem one_sided_rows_le_seed_budget
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (received : Received K I) (row : Rows x σ received 5)
    (hone : let q := symbolicRow row.1
      (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0))
    (seeds : Finset K) (selected : SelectionMap K)
    (support : Selection x received seeds selected) : seeds.card ≤ budget := by
  have bound := K6969OneSided.one_sided_comparison_card_le
    (p := prime) (w := 131071) (e := 82404) (A := 179740) (a := 48669)
    (by decide) (by decide) x received σ hfixed hpow (by decide) (by decide)
    (by rw [hcard]; decide) row hone seeds selected support.degree_le support.agreement support.pencil
  rw [hcard, one_sided_price] at bound
  exact bound.trans (by decide +kernel)

def MixedRowsSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (row : Rows x σ received 5) (other : Rows x σ received 67471),
    coefficientDeterminant row.1 other.1 ≠ 0 →
    ∀ (seeds : Finset K) (selected : SelectionMap K),
      Selection x received seeds selected → seeds.card ≤ budget

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
    ∀ row : Rows x σ received 5, row.1 ≠ 0 →
      (∀ other : Rows x σ received 67471, coefficientDeterminant row.1 other.1 = 0) →
      seeds.card ≤ budget

private theorem seed_bound_of_rank_cases
    (x : I ↪ K) (σ : K →+* K) (hcard : Fintype.card I = 262144)
    (hMixed : MixedRowsSeedBound x σ) (hRankOne : RankOneSeedBound x σ) :
    RCN050.SelectedNoLargePencilBound x 131071 82404 budget := by
  intro received seeds A selected hdegree hnear hvalue hpencil
  have hthreshold : Fintype.card I - 82404 = 179740 := by rw [hcard]
  have hagreement : ∀ g ∈ seeds, 179740 ≤ (agreementSet x received selected g).card := by
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
  obtain ⟨row, hrow⟩ := exists_nonzero_comparison_row 179740 48669 5 82404 x u v hcard (by decide +kernel)
  by_cases hdet : ∃ other : Rows x σ received 67471, coefficientDeterminant row.1 other.1 ≠ 0
  · obtain ⟨other, hother⟩ := hdet
    exact hMixed received row other hother seeds selected hselection
  exact hRankOne received seeds selected hselection row hrow
    (fun other => not_ne_iff.mp (fun h => hdet ⟨other, h⟩))

private theorem card_le_from_primitive_cases
    (x : I ↪ K) (u v : Fin 2 → I → K) (hcard : Fintype.card I = 262144)
    (row : ComparisonSpace 179740 48669 5 x u v) (hrow : row.1 ≠ 0)
    (hdet : ∀ other : ComparisonSpace 179740 48669 67471 x u v,
      coefficientDeterminant row.1 other.1 = 0)
    (seedCount : ℕ)
    (honeCase : (let r := symbolicRow row.1
      (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0)) → seedCount ≤ budget)
    (hbothCase : ∀ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q → RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 33735 → seedCount ≤ budget) :
    seedCount ≤ budget := by
  obtain ⟨q, m, hm, hactive, hprimitive, hfactor, hlarge⟩ :=
    exists_primitive_comparison_generator x u v row hrow (by rw [hcard]; decide)
      (fun other => cross_eq_of_symbolic_det_zero row.1 other.1 (hdet other))
  by_cases hone : (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0)
  · exact honeCase (comparison_one_sided_of_factor row.1 q m hm hfactor hone)
  have hboth : q.first ≠ 0 ∧ q.second ≠ 0 := by
    rcases hactive with hf | hs
    · exact ⟨hf, fun hz => hone (Or.inl ⟨hf, hz⟩)⟩
    · exact ⟨fun hz => hone (Or.inr ⟨hz, hs⟩), hs⟩
  have hcap := primitive_excess_add_badCard_le_33735 x u v q hboth.1 hboth.2 hcard hlarge
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
    RCN050.SelectedNoLargePencilBound x 131071 82404 budget :=
  seed_bound_of_rank_cases x σ hcard hMixed
    (rank_one_bound_of_primitive x σ hfixed hpow hcard hPrimitive)
theorem symbolic_mixed
    {A a d₀ d₁ D p w e : ℕ} (hp : 0 < p) (hwidth : 2*D + 2 ≤ p)
    (hle₀ : d₀ ≤ D) (hle₁ : d₁ ≤ D)
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (haPos : 0 < a) (ha : a + w = A) (han : A ≤ Fintype.card I)
    (θ : ComparisonSpace A a d₀ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (η : ComparisonSpace A a d₁ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (hdet : coefficientDeterminant θ.1 η.1 ≠ 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (Finset.univ.filter (fun i => (selected g).eval (x i) = U 0 i + g * U 1 i)).card)
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((Fintype.card I - JointIdentity.splitPoint w A) * ((d₀+d₁ + 2) * (p + 1)) / (A - JointIdentity.splitPoint w A))
      (Fintype.card I * ((d₀+d₁ + 1) * (p + 1)) / (JointIdentity.tolerance w A + 1) + (e + 1)) := by
  exact Frontier6969Mixed.actual_rows hp hwidth hle₀ hle₁ x U σ hfixed hσ haPos ha han θ η hdet seeds selected hdegree hagreement hpencil
theorem mixed (x : I ↪ K) (σ : K →+* K) (hx : ∀ i, σ (x i)=x i)
    (hs : ∀ z, σ z=z^prime) (hcard : Fintype.card I=262144) : MixedRowsSeedBound x σ := by
  classical
  intro U row other hdet seeds P h
  have out := symbolic_mixed (A:=179740) (a:=48669) (d₀:=5) (d₁:=67471)
    (D:=67471) (p:=prime) (w:=131071) (e:=82404) (by decide) (by decide) (by decide) (by decide)
    x U σ hx hs (by decide) (by decide) (by rw [hcard];decide) row other hdet seeds P h.degree_le h.agreement h.pencil
  rw [hcard] at out
  exact out.trans (by decide +kernel)
structure RetainedComparison (x : I ↪ K) (σ : K →+* K)
    (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) : Prop where
  selection : Selection x received retained selected
  first_ne : q.first ≠ 0
  second_ne : q.second ≠ 0
  primitive : IsPrimitiveRow q
  xDegree : q.beta.natDegree ≤ 179739 ∧ q.first.natDegree ≤ 48668 ∧ q.second.natDegree ≤ 48668
  seedDegree : ∀ j, ((q.beta.coeff j).degreeOf 0 ≤ 6 ∧ (q.beta.coeff j).degreeOf 1 ≤ 6) ∧
    ((q.first.coeff j).degreeOf 0 ≤ 5 ∧ (q.first.coeff j).degreeOf 1 ≤ 6) ∧
    ((q.second.coeff j).degreeOf 0 ≤ 6 ∧ (q.second.coeff j).degreeOf 1 ≤ 5)
  excess_bad : primitiveExcess 131071 q + (badNodes x σ received q).card ≤ 33735
  good : ∀ g ∈ retained, primitiveSelected σ prime q selected g = 0 ∧
    Disjoint (agreementSet x received selected g) (badNodes x σ received q)

abbrev combinedDegree (q : SymbolicRow (SeedRing K)) : ℕ :=
  weightDegree totalWeights (primitiveRowLift q)

theorem combined_degree_le_twelve
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (h : RetainedComparison x σ received retained selected q) :
    combinedDegree q ≤ 12 := by
  have hβ := liftedCoefficient_total_weight_le q.beta 6 6
    (fun j => (h.seedDegree j).1.1) (fun j => (h.seedDegree j).1.2)
  have ha := liftedCoefficient_total_weight_le q.first 5 6
    (fun j => (h.seedDegree j).2.1.1) (fun j => (h.seedDegree j).2.1.2)
  have hb := liftedCoefficient_total_weight_le q.second 6 5
    (fun j => (h.seedDegree j).2.2.1) (fun j => (h.seedDegree j).2.2.2)
  have ha' : weightDegree totalWeights
      (retainCarrier (carrierOfSeedCoefficients q.first) * MvPolynomial.X 1) ≤ (5 + 6) + 1 :=
    (weight_mul_le _ _ _).trans (by
      rw [weight_X]
      exact Nat.add_le_add ha (show totalWeights 1 ≤ 1 by decide))
  have hb' : weightDegree totalWeights
      (retainCarrier (carrierOfSeedCoefficients q.second) * MvPolynomial.X 2) ≤ (6 + 5) + 1 :=
    (weight_mul_le _ _ _).trans (by
      rw [weight_X]
      exact Nat.add_le_add hb (show totalWeights 2 ≤ 1 by decide))
  change weightDegree totalWeights (primitiveRowLift q) ≤ 12
  rw [primitiveRowLift_weight_max]
  exact max_le (max_le hβ ha') hb'

def RetainedTwoSidedSeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (U : Received K I) (S : Finset K) (P : SelectionMap K) (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ U S P q →
    S.card + (33735 - primitiveExcess 131071 q+1)*6*(prime+1) ≤ budget
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
  obtain ⟨retained, hsub, hseedCount, hrow⟩ := K6969Discard.retain_primitive_rows
    (A := 179740) (a := 48669) (w := 131071) (p := prime)
    x σ hfixed hpow (by decide) received (by decide) (by decide) row q m hm
    (Or.inl hfirst) hfactor seeds (agreementSet x received selected) selected
    support.degree_le support.agreement (fun _ _ _ hi => eval_eq_of_mem_agreementSet hi)
  have hX := primitive_x_degree_caps row.1 q m hm hfactor
  have hB := primitive_seed_degree_caps row.1 q m hm hfactor
  have hretained := hRetained received retained selected q
    ⟨selection_of_subset support hsub, hfirst, hsecond, hprimitive, hX, hB, by omega, hrow⟩
  have hbad : (badNodes x σ received q).card ≤ 33735 - primitiveExcess 131071 q := by omega
  calc
    seeds.card ≤ retained.card + ((badNodes x σ received q).card + 1)*(6*(prime+1)) := hseedCount
    _ ≤ retained.card + (33735-primitiveExcess 131071 q+1)*6*(prime+1) := by
      apply Nat.add_le_add_left
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hbad 1)
    _ ≤ budget := hretained
theorem selected_of_retained (x : I ↪ K) (σ : K →+* K) (hx : ∀ i, σ (x i)=x i)
    (hs : ∀ z, σ z=z^prime) (hcard : Fintype.card I=262144) (h : RetainedTwoSidedSeedBound x σ) :
    RCN050.SelectedNoLargePencilBound x 131071 82404 budget :=
  seed_bound_of_two_sided_primitive x σ hx hs hcard (mixed x σ hx hs hcard) (primitive_bound_of_retained x σ hx hs h)
#print axioms mixed
#print axioms combined_degree_le_twelve
#print axioms selected_of_retained
end
end ProximityPrize.SubmissionLower.K6969Global
